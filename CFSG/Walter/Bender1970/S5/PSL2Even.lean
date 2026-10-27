module

public import CFSG.Walter.Bender1970.S2.AutEven
public import CFSG.Walter.Bender1970.S38.Component

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

section PSL2

variable {f : ℕ}

theorem psl2_even_eq_one_of_smul_eq (hf : 2 ≤ f) {P P' : Sylow 2 PSL(2, GaloisField 2 f)}
    (h : P ≠ P') {x : PSL(2, GaloisField 2 f)} (hx : x ∈ (P : Subgroup PSL(2, GaloisField 2 f)))
    (hxP' : x • P' = P') : x = 1 := by
  have h1 : x ∈ Subgroup.normalizer ((P' : Subgroup PSL(2, GaloisField 2 f)) :
      Set PSL(2, GaloisField 2 f)) ⊓ P := ⟨Sylow.smul_eq_iff_mem_normalizer.mp hxP', hx⟩
  rw [psl2_even_normalizer_inf_eq_bot hf (Ne.symm h)] at h1
  exact Subgroup.mem_bot.mp h1

theorem psl2_even_card_sylow_ne (hf : 2 ≤ f) (P : Sylow 2 PSL(2, GaloisField 2 f)) :
    Nat.card {Q : Sylow 2 PSL(2, GaloisField 2 f) // Q ≠ P} = 2 ^ f := by
  classical
  have h1 := psl2_even_card_sylow (show f ≠ 0 by omega)
  have : Fintype (Sylow 2 PSL(2, GaloisField 2 f)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h1 ⊢
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, h1]
  simp

theorem psl2_even_exists_smul_eq (hf : 2 ≤ f) (P : Sylow 2 PSL(2, GaloisField 2 f))
    {P₁ P₂ : Sylow 2 PSL(2, GaloisField 2 f)} (h₁ : P₁ ≠ P) (h₂ : P₂ ≠ P) :
    ∃ x ∈ (P : Subgroup PSL(2, GaloisField 2 f)), x • P₁ = P₂ := by
  classical
  set L := PSL(2, GaloisField 2 f) with hLdef
  have hf0 : f ≠ 0 := by omega
  have hne : ∀ s ∈ (P : Subgroup L), s • P₁ ≠ P := by
    intro s hs h
    apply h₁
    have h1 : s⁻¹ • P = P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ((P : Subgroup L).inv_mem hs))
    calc P₁ = s⁻¹ • (s • P₁) := (inv_smul_smul s P₁).symm
      _ = s⁻¹ • P := by rw [h]
      _ = P := h1
  let g : ↥(P : Subgroup L) → {Q : Sylow 2 L // Q ≠ P} := fun s => ⟨(s : L) • P₁, hne s s.2⟩
  have hg : Function.Injective g := by
    intro s s' hss'
    have h1 : (s : L) • P₁ = (s' : L) • P₁ := congrArg Subtype.val hss'
    have h2 : ((s' : L)⁻¹ * s) • P₁ = P₁ := by rw [mul_smul, h1, inv_smul_smul]
    have h3 := psl2_even_eq_one_of_smul_eq hf (Ne.symm h₁)
      ((P : Subgroup L).mul_mem ((P : Subgroup L).inv_mem s'.2) s.2) h2
    rw [inv_mul_eq_one] at h3
    exact Subtype.ext h3.symm
  have hcardP : Nat.card (P : Subgroup L) = 2 ^ f := (psl2_even_sylow_two hf P).2
  have hcard : Nat.card {Q : Sylow 2 L // Q ≠ P} = 2 ^ f := psl2_even_card_sylow_ne hf P
  have hbij : Function.Bijective g := hg.bijective_of_nat_card_le (by rw [hcardP, hcard])
  obtain ⟨s, hs⟩ := hbij.2 ⟨P₂, h₂⟩
  exact ⟨s, s.2, congrArg Subtype.val hs⟩

theorem psl2_even_eq_top_of_normalizer_le (hf : 2 ≤ f) (P : Sylow 2 PSL(2, GaloisField 2 f))
    {Y : Subgroup PSL(2, GaloisField 2 f)}
    (hNY : Subgroup.normalizer ((P : Subgroup PSL(2, GaloisField 2 f)) :
      Set PSL(2, GaloisField 2 f)) ≤ Y)
    {y : PSL(2, GaloisField 2 f)} (hyY : y ∈ Y) (hy : y • P ≠ P) : Y = ⊤ := by
  classical
  have hf0 : f ≠ 0 := by omega
  have hPY : (P : Subgroup PSL(2, GaloisField 2 f)) ≤ Y := Subgroup.le_normalizer.trans hNY
  have htrans : ∀ Q : Sylow 2 PSL(2, GaloisField 2 f), ∃ z ∈ Y, z • P = Q := by
    intro Q
    by_cases hQ : Q = y • P
    · exact ⟨y, hyY, hQ.symm⟩
    · have hyP : (y • P : Sylow 2 PSL(2, GaloisField 2 f)) ≤ Y := by
        intro x hx
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          MulAut.smul_def, MulAut.conj_inv_apply] at hx
        have := Y.mul_mem (Y.mul_mem hyY (hPY hx)) (Y.inv_mem hyY)
        simpa [mul_assoc] using this
      obtain ⟨x, hx, hxQ⟩ := psl2_even_exists_smul_eq hf (y • P) (Ne.symm hy) hQ
      exact ⟨x, hyP hx, hxQ⟩
  have : MulAction.IsPretransitive Y (Sylow 2 PSL(2, GaloisField 2 f)) := by
    refine ⟨fun Q₁ Q₂ => ?_⟩
    obtain ⟨z₁, hz₁, hz₁Q⟩ := htrans Q₁
    obtain ⟨z₂, hz₂, hz₂Q⟩ := htrans Q₂
    refine ⟨⟨z₂, hz₂⟩ * ⟨z₁, hz₁⟩⁻¹, ?_⟩
    rw [mul_smul, Subgroup.smul_def, Subgroup.smul_def]
    change (z₂ : PSL(2, GaloisField 2 f)) • ((z₁ : PSL(2, GaloisField 2 f))⁻¹ • Q₁) = Q₂
    rw [← hz₁Q, inv_smul_smul, hz₂Q]
  have hidx := MulAction.index_stabilizer_of_transitive Y P
  have hstab : Nat.card (MulAction.stabilizer Y P) =
      Nat.card (Subgroup.normalizer ((P : Subgroup PSL(2, GaloisField 2 f)) :
        Set PSL(2, GaloisField 2 f))) := by
    refine Nat.card_congr ⟨fun x => ⟨(x : PSL(2, GaloisField 2 f)), ?_⟩,
      fun x => ⟨⟨x, hNY x.2⟩, ?_⟩,
      fun x => rfl, fun x => rfl⟩
    · exact Sylow.smul_eq_iff_mem_normalizer.mp x.2
    · exact Sylow.smul_eq_iff_mem_normalizer.mpr x.2
  have hcardY := (MulAction.stabilizer Y P).card_mul_index
  rw [hstab, hidx, psl2_even_card_normalizer_sylow_two hf0, psl2_even_card_sylow hf0] at hcardY
  apply Subgroup.eq_top_of_card_eq
  rw [← hcardY, psl2_even_card hf0]
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [← Nat.sq_sub_sq, one_pow]
  rw [this]
  ring

theorem psl2_even_torus (hf : 2 ≤ f) {P P' : Sylow 2 PSL(2, GaloisField 2 f)} (h : P ≠ P') :
    Odd (Nat.card (Subgroup.normalizer ((P : Subgroup PSL(2, GaloisField 2 f)) :
        Set PSL(2, GaloisField 2 f)) ⊓ Subgroup.normalizer
        ((P' : Subgroup PSL(2, GaloisField 2 f)) : Set PSL(2, GaloisField 2 f)) :
        Subgroup PSL(2, GaloisField 2 f))) ∧
      (∀ u ∈ (P : Subgroup PSL(2, GaloisField 2 f)), u ≠ 1 →
        ∀ v ∈ (P : Subgroup PSL(2, GaloisField 2 f)), v ≠ 1 →
        ∃ r ∈ Subgroup.normalizer ((P : Subgroup PSL(2, GaloisField 2 f)) :
            Set PSL(2, GaloisField 2 f)) ⊓ Subgroup.normalizer
            ((P' : Subgroup PSL(2, GaloisField 2 f)) : Set PSL(2, GaloisField 2 f)),
          r * u * r⁻¹ = v) ∧
      (∃ w ∈ Subgroup.normalizer (((Subgroup.normalizer ((P : Subgroup PSL(2, GaloisField 2 f)) :
            Set PSL(2, GaloisField 2 f)) ⊓ Subgroup.normalizer
            ((P' : Subgroup PSL(2, GaloisField 2 f)) : Set PSL(2, GaloisField 2 f)) :
            Subgroup PSL(2, GaloisField 2 f))) : Set PSL(2, GaloisField 2 f)),
          w • P ≠ P) ∧
      ∀ ℓ : PSL(2, GaloisField 2 f), orderOf ℓ = 2 →
        ¬ Subgroup.normalizer ((P : Subgroup PSL(2, GaloisField 2 f)) :
            Set PSL(2, GaloisField 2 f)) ⊓ Subgroup.normalizer
            ((P' : Subgroup PSL(2, GaloisField 2 f)) : Set PSL(2, GaloisField 2 f)) ≤
          Subgroup.centralizer ({ℓ} : Set PSL(2, GaloisField 2 f)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := PSL(2, GaloisField 2 f) with hLdef
  have hf0 : f ≠ 0 := by omega
  set NP := Subgroup.normalizer ((P : Subgroup L) : Set L) with hNP
  set NP' := Subgroup.normalizer ((P' : Subgroup L) : Set L) with hNP'
  set R := NP ⊓ NP' with hR
  have hRP : R ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hx'⟩, hxP⟩
    have h1 : x ∈ NP' ⊓ P := ⟨hx', hxP⟩
    rwa [hNP', psl2_even_normalizer_inf_eq_bot hf (Ne.symm h)] at h1
  have hRcard : Nat.card R = 2 ^ f - 1 := by
    have horb : MulAction.orbit NP P' = {Q : Sylow 2 L | Q ≠ P} := by
      ext Q
      constructor
      · rintro ⟨n, rfl⟩ hnP
        have hnP' : (n : L) • P' = P := hnP
        have h1 : (n : L) • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr n.2
        exact h (MulAction.injective (n : L) (h1.trans hnP'.symm))
      · intro hQ
        obtain ⟨x, hx, hxQ⟩ := psl2_even_exists_smul_eq hf P (Ne.symm h) hQ
        exact ⟨⟨x, Subgroup.le_normalizer hx⟩, hxQ⟩
    have hidx := MulAction.index_stabilizer NP P'
    rw [horb] at hidx
    have hcardQ : ({Q : Sylow 2 L | Q ≠ P} : Set (Sylow 2 L)).ncard = 2 ^ f := by
      rw [← Nat.card_coe_set_eq]
      exact psl2_even_card_sylow_ne hf P
    rw [hcardQ] at hidx
    have hstab : Nat.card (MulAction.stabilizer NP P') = Nat.card R := by
      refine Nat.card_congr ⟨fun x => ⟨(x : L), x.1.2, ?_⟩, fun x => ⟨⟨x, x.2.1⟩, ?_⟩,
        fun x => rfl, fun x => rfl⟩
      · exact Sylow.smul_eq_iff_mem_normalizer.mp x.2
      · exact Sylow.smul_eq_iff_mem_normalizer.mpr x.2.2
    have h1 := (MulAction.stabilizer NP P').card_mul_index
    rw [hstab, hidx, psl2_even_card_normalizer_sylow_two hf0] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans (mul_comm _ _))
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hRcard]
    exact Nat.Even.sub_odd (by omega) (even_iff_two_dvd.mpr (dvd_pow_self 2 hf0)) odd_one
  ·
    intro u hu hu1
    have hCu := psl2_even_centralizer_involution hf P hu hu1
    have hfree : ∀ r ∈ R, r * u * r⁻¹ = u → r = 1 := by
      intro r hr hru
      have hrC : r ∈ Subgroup.centralizer ({u} : Set L) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc r * u = r * u * r⁻¹ * r := by group
          _ = u * r := by rw [hru]
      rw [hCu] at hrC
      have : r ∈ R ⊓ P := ⟨hr, hrC⟩
      rwa [hRP, Subgroup.mem_bot] at this
    set T : Set L := {v | v ∈ (P : Subgroup L) ∧ v ≠ 1} with hT
    have hTcard : Nat.card T = 2 ^ f - 1 := by
      have : T = ((P : Subgroup L) : Set L) \ {1} := Set.ext fun v => Iff.rfl
      rw [Nat.card_coe_set_eq, this, Set.ncard_sdiff_singleton_of_mem ((P : Subgroup L).one_mem),
        ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, (psl2_even_sylow_two hf P).2]
    let φ : R → T := fun r => ⟨(r : L) * u * (r : L)⁻¹,
      (Subgroup.mem_normalizer_iff.mp r.2.1 u).mp hu, fun h1 => hu1 (by
        calc u = (r : L)⁻¹ * ((r : L) * u * (r : L)⁻¹) * r := by group
          _ = 1 := by rw [h1]; group)⟩
    have hφ : Function.Injective φ := by
      intro r₁ r₂ h12
      have h' : (r₁ : L) * u * (r₁ : L)⁻¹ = r₂ * u * (r₂ : L)⁻¹ := congrArg Subtype.val h12
      have h1 := hfree ((r₂ : L)⁻¹ * r₁) (R.mul_mem (R.inv_mem r₂.2) r₁.2) (by
        calc (r₂ : L)⁻¹ * r₁ * u * ((r₂ : L)⁻¹ * r₁)⁻¹
            = (r₂ : L)⁻¹ * ((r₁ : L) * u * (r₁ : L)⁻¹) * r₂ := by group
          _ = u := by rw [h']; group)
      rw [inv_mul_eq_one] at h1
      exact Subtype.ext h1.symm
    have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hRcard, hTcard])
    intro v hv hv1
    obtain ⟨r, hr⟩ := hbij.2 ⟨v, hv, hv1⟩
    exact ⟨r, r.2, congrArg Subtype.val hr⟩
  ·
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P P'
    have hgP' : g • P' ≠ P' := by
      intro h1
      apply h
      calc P = g⁻¹ • (g • P) := (inv_smul_smul g P).symm
        _ = g⁻¹ • (g • P') := by rw [hg, h1]
        _ = P' := inv_smul_smul g P'
    obtain ⟨x, hx, hxP⟩ := psl2_even_exists_smul_eq hf P' hgP' (Ne.symm h).symm
    set w := x * g with hw
    have hwP : w • P = P' := by
      rw [hw, mul_smul, hg]
      exact Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hx)
    have hwP' : w • P' = P := by rw [hw, mul_smul, hxP]
    have hconjN : ∀ {Q : Sylow 2 L} {n : L}, n ∈ Subgroup.normalizer ((Q : Subgroup L) : Set L) →
        w * n * w⁻¹ ∈ Subgroup.normalizer (((w • Q : Sylow 2 L) : Subgroup L) : Set L) := by
      intro Q n hn
      have hn' : n • Q = Q := Sylow.smul_eq_iff_mem_normalizer.mpr hn
      apply Sylow.smul_eq_iff_mem_normalizer.mp
      rw [mul_smul, mul_smul, inv_smul_smul, hn']
    refine ⟨w, mem_normalizer_of_conj_mem' fun r hr => ⟨?_, ?_⟩, ?_⟩
    · have := hconjN hr.2
      rwa [hwP'] at this
    · have := hconjN hr.1
      rwa [hwP] at this
    · rw [hwP]
      exact Ne.symm h
  ·
    intro ℓ hℓ hRℓ
    have hℓp : IsPGroup 2 (Subgroup.zpowers ℓ) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hℓ, pow_one])
    obtain ⟨Q, hQ⟩ := hℓp.exists_le_sylow
    have hℓ1 : ℓ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hℓ
      omega
    rw [psl2_even_centralizer_involution hf Q (hQ (Subgroup.mem_zpowers ℓ)) hℓ1] at hRℓ
    have hdvd : Nat.card R ∣ 2 ^ f := (psl2_even_sylow_two hf Q).2 ▸ Subgroup.card_dvd_of_le hRℓ
    rw [hRcard] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero] at hk
      omega
    · have h2 : 2 ∣ 2 ^ f - 1 := hk ▸ dvd_pow_self 2 hk0.ne'
      have h3 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
      omega

end PSL2

section Lift

variable {K : Type} [Group K] [Finite K] {f : ℕ} {φ : K →* PSL(2, GaloisField 2 f)}

theorem mem_of_map_mem_of_ker_eq_center (hZ : Odd (Nat.card (Subgroup.center K)))
    (hker : φ.ker = Subgroup.center K) {P : Subgroup K} (hP : IsPGroup 2 P) {s : K} {kS : ℕ}
    (hs : s ^ 2 ^ kS = 1) (hsP : φ s ∈ P.map φ) : s ∈ P := by
  obtain ⟨kP, hkP⟩ := exists_pow_eq_one_of_isPGroup hP
  obtain ⟨p, hp, hps⟩ := hsP
  set z := p⁻¹ * s with hz
  have hzZ : z ∈ Subgroup.center K := by
    rw [← hker, MonoidHom.mem_ker, hz, map_mul, map_inv, hps, inv_mul_cancel]
  have hcomm : Commute p⁻¹ s := by
    have h1 : s = p * z := by rw [hz, mul_inv_cancel_left]
    rw [h1]
    exact (Commute.inv_left (Commute.refl p)).mul_right (Subgroup.mem_center_iff.mp hzZ p⁻¹)
  have hs' : s ^ 2 ^ (kS + kP) = 1 := by rw [pow_add, pow_mul, hs, one_pow]
  have hp' : p ^ 2 ^ (kS + kP) = 1 := by rw [pow_add, mul_comm, pow_mul, hkP p hp, one_pow]
  have hzk : z ^ 2 ^ (kS + kP) = 1 := by
    rw [hz, hcomm.mul_pow, inv_pow, hp', hs', inv_one, one_mul]
  have hz1 := eq_one_of_mem_center_of_pow hZ hzZ hzk
  rw [hz, inv_mul_eq_one] at hz1
  rw [← hz1]
  exact hp

theorem eq_of_map_eq_of_ker_eq_center (hZ : Odd (Nat.card (Subgroup.center K)))
    (hker : φ.ker = Subgroup.center K) {P : Subgroup K} (hP : IsPGroup 2 P) {x y : K}
    (hx : x ∈ P) (hy : y ∈ P) (h : φ x = φ y) : x = y := by
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hP
  have h1 : x⁻¹ * y ∈ Subgroup.center K := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h2 := eq_one_of_mem_center_of_pow hZ h1 (hk _ (P.mul_mem (P.inv_mem hx) hy))
  rw [inv_mul_eq_one] at h2
  exact h2

theorem mem_normalizer_of_map_mem_normalizer (hZ : Odd (Nat.card (Subgroup.center K)))
    (hker : φ.ker = Subgroup.center K) (P : Sylow 2 K) {x : K}
    (hx : φ x ∈ Subgroup.normalizer (((P : Subgroup K).map φ : Subgroup _) :
      Set PSL(2, GaloisField 2 f))) : x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) := by
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup P.isPGroup'
  refine mem_normalizer_of_conj_mem' fun y hy => ?_
  refine mem_of_map_mem_of_ker_eq_center hZ hker P.isPGroup' (kS := k) ?_ ?_
  · rw [conj_pow, hk y hy, mul_one, mul_inv_cancel]
  · rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx (φ y)).mp ⟨y, hy, rfl⟩

theorem exists_torus_of_surjective (hf : 2 ≤ f) (hK : commutator K = ⊤)
    (hZ : Odd (Nat.card (Subgroup.center K))) (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center K) (P : Sylow 2 K) :
    ∃ R : Subgroup K, R ≤ Subgroup.normalizer ((P : Subgroup K) : Set K) ∧ Odd (Nat.card R) ∧
      (∀ u ∈ (P : Subgroup K), u ≠ 1 → ∀ v ∈ (P : Subgroup K), v ≠ 1 →
        ∃ r ∈ R, r * u * r⁻¹ = v) ∧
      (∀ ℓ : K, orderOf ℓ = 2 → ¬ R ≤ Subgroup.centralizer ({ℓ} : Set K)) ∧
      ∀ Y : Subgroup K, Subgroup.normalizer ((P : Subgroup K) : Set K) ≤ Y →
        Subgroup.normalizer (R : Set K) ≤ Y → Y = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf0 : f ≠ 0 := by omega
  set Pb : Sylow 2 PSL(2, GaloisField 2 f) := P.mapSurjective hφ with hPbdef
  have hPb : (Pb : Subgroup PSL(2, GaloisField 2 f)) = (P : Subgroup K).map φ :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨P', hP'⟩ : ∃ P' : Sylow 2 PSL(2, GaloisField 2 f), Pb ≠ P' := by
    have : Nontrivial (Sylow 2 PSL(2, GaloisField 2 f)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, psl2_even_card_sylow hf0]
      have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    obtain ⟨P', hP'⟩ := exists_ne Pb
    exact ⟨P', Ne.symm hP'⟩
  obtain ⟨hRodd, hRtr, ⟨w, hwN, hwP⟩, hRinv⟩ := psl2_even_torus hf hP'
  set Rb := Subgroup.normalizer ((Pb : Subgroup PSL(2, GaloisField 2 f)) :
    Set PSL(2, GaloisField 2 f)) ⊓ Subgroup.normalizer ((P' : Subgroup PSL(2, GaloisField 2 f)) :
    Set PSL(2, GaloisField 2 f)) with hRbdef
  set R := Rb.comap φ with hRdef
  have hφP : ∀ {x : K}, φ x ∈ Subgroup.normalizer ((Pb : Subgroup PSL(2, GaloisField 2 f)) :
      Set PSL(2, GaloisField 2 f)) → x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) :=
    fun hx => mem_normalizer_of_map_mem_normalizer hZ hker P (hPb ▸ hx)
  have hRN : R ≤ Subgroup.normalizer ((P : Subgroup K) : Set K) := fun r hr => hφP hr.1
  have hZ1 : ∀ z ∈ Subgroup.center K, z ^ 2 = 1 → z = 1 := fun z hz hz2 =>
    eq_one_of_mem_center_of_pow hZ hz (m := 1) (by rw [pow_one]; exact hz2)
  have hφne : ∀ x : K, x ^ 2 = 1 → x ≠ 1 → φ x ≠ 1 := fun x hx2 hx1 hφx =>
    hx1 (hZ1 x (by rw [← hker]; exact hφx) hx2)
  refine ⟨R, hRN, ?_, ?_, ?_, ?_⟩
  ·
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 (even_iff_two_dvd.mp hodd)
    have hr2 : (r : K) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hr, pow_orderOf_eq_one, Subgroup.coe_one]
    have hr1 : (r : K) ≠ 1 := by
      intro h
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at hr
      omega
    have h1 : orderOf (⟨φ r, r.2⟩ : Rb) ∣ 2 := orderOf_dvd_of_pow_eq_one
      (Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hr2, map_one]; rfl))
    have h2 : orderOf (⟨φ r, r.2⟩ : Rb) ∣ Nat.card Rb := orderOf_dvd_natCard _
    have h3 : orderOf (⟨φ r, r.2⟩ : Rb) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hRodd) h1 h2
    rw [orderOf_eq_one_iff] at h3
    exact hφne r hr2 hr1 (congrArg Subtype.val h3)
  ·
    obtain ⟨kP, hkP⟩ := exists_pow_eq_one_of_isPGroup P.isPGroup'
    have hφ1 : ∀ u ∈ (P : Subgroup K), u ≠ 1 → φ u ≠ 1 := by
      intro u hu hu1 h
      apply hu1
      have h1 : u ∈ Subgroup.center K := by rw [← hker]; exact h
      exact eq_one_of_mem_center_of_pow hZ h1 (hkP u hu)
    intro u hu hu1 v hv hv1
    obtain ⟨rb, hrb, hrbuv⟩ := hRtr (φ u) (hPb ▸ ⟨u, hu, rfl⟩) (hφ1 u hu hu1) (φ v)
      (hPb ▸ ⟨v, hv, rfl⟩) (hφ1 v hv hv1)
    obtain ⟨r, rfl⟩ := hφ rb
    refine ⟨r, hrb, eq_of_map_eq_of_ker_eq_center hZ hker P.isPGroup'
      ((Subgroup.mem_normalizer_iff.mp (hRN hrb) u).mp hu) hv ?_⟩
    rw [map_mul, map_mul, map_inv, hrbuv]
  ·
    intro ℓ hℓ hRℓ
    have hℓ2 : ℓ ^ 2 = 1 := by rw [← hℓ, pow_orderOf_eq_one]
    have hℓ1 : ℓ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hℓ
      omega
    have hφℓ : orderOf (φ ℓ) = 2 :=
      orderOf_eq_prime (by rw [← map_pow, hℓ2, map_one]) (hφne ℓ hℓ2 hℓ1)
    apply hRinv (φ ℓ) hφℓ
    intro rb hrb
    obtain ⟨r, rfl⟩ := hφ rb
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hRℓ (show r ∈ R from hrb))
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h1]
  ·
    intro Y hNY hNRY
    have hNY' : Subgroup.normalizer ((Pb : Subgroup PSL(2, GaloisField 2 f)) :
        Set PSL(2, GaloisField 2 f)) ≤ Y.map φ := by
      intro xb hxb
      obtain ⟨x, rfl⟩ := hφ xb
      exact ⟨x, hNY (hφP hxb), rfl⟩
    obtain ⟨w₀, rfl⟩ := hφ w
    have hw₀ : w₀ ∈ Subgroup.normalizer (R : Set K) := by
      refine mem_normalizer_of_conj_mem' fun r hr => ?_
      show φ (w₀ * r * w₀⁻¹) ∈ Rb
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hwN (φ r)).mp hr
    have hYtop := psl2_even_eq_top_of_normalizer_le hf Pb hNY' ⟨w₀, hNRY hw₀, rfl⟩ hwP
    apply eq_top_of_sup_center_eq_top hK
    rw [eq_top_iff]
    intro k _
    obtain ⟨y, hy, hyk⟩ := (hYtop ▸ Subgroup.mem_top (φ k) : φ k ∈ Y.map φ)
    have hz : y⁻¹ * k ∈ Subgroup.center K := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyk, inv_mul_cancel]
    have : k = y * (y⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hy hz

end Lift

end CFSG.Walter
