module

public import CFSG.Quasithin.H13.NQCatC2Syl
public import CFSG.Quasithin.H13.NQCatT513L24
public import CFSG.Quasithin.H13.NQCatC2Gen

public section

namespace CFSG.Quasithin.H13.NQCat.C2

open CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCat.T513

variable {A : Type} [Group A] [Finite A]

theorem l24_facts {R S : Subgroup A} (hR : CFSG.Blueprint.LieModel (ModO2 R) .PSL 2 2 2)
    (hSR : IsSylowTwoOf (S ⊓ R) R) :
    (∃ w ∈ R ⊓ Subgroup.normalizer ((S ⊓ R : Subgroup A) : Set A), orderOf w = 3) ∧
    ∀ X : Subgroup A, X ≤ R ⊓ Subgroup.normalizer ((S ⊓ R : Subgroup A) : Set A) →
      Odd (Nat.card X) → Nat.card X ∣ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₄⟩ := exists_l24_of_lieModel hR
  let π : ↥R →* ModO2 R := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkerπ : π.ker = CFSG.pCore 2 ↥R := QuotientGroup.ker_mk' _
  obtain ⟨-, hSR2, hSRi⟩ := hSR
  set P : Subgroup ↥R := (S ⊓ R).subgroupOf R with hP
  have hP2 : IsPGroup 2 P := hSR2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  let PS : Sylow 2 ↥R := hP2.toSylow hSRi
  have hcore : CFSG.pCore 2 ↥R ≤ P :=
    (CFSG.pCore_isPGroup (G := ↥R) (p := 2)).le_sylow_of_normal PS
  have hPb2 : IsPGroup 2 (P.map π) := hP2.map π
  have hPbi : ¬ 2 ∣ (P.map π).index := fun h2 => hSRi (h2.trans (P.index_map_dvd hπ))
  let PbS : Sylow 2 (ModO2 R) := hPb2.toSylow hPbi
  refine ⟨?_, fun X hX hXo => ?_⟩
  ·
    obtain ⟨ybar, hybar, hy3⟩ :=
      CFSG.Walter.JT.exists_orderOf_three_mem_normalizer_of_psl24 e₄ PbS
    obtain ⟨y, rfl⟩ := hπ ybar
    have hyN : (y : A) ∈ R ⊓ Subgroup.normalizer ((S ⊓ R : Subgroup A) : Set A) := by
      refine ⟨y.2, ?_⟩
      have hyP : y ∈ Subgroup.normalizer (P : Set ↥R) := by
        apply mem_normalizer_of_conj_mem
        intro s hs
        have h1 : π (y * s * y⁻¹) ∈ P.map π := by
          rw [map_mul, map_mul, map_inv]
          exact (Subgroup.mem_normalizer_iff.mp hybar _).mp ⟨s, hs, rfl⟩
        obtain ⟨s', hs', hs'e⟩ := h1
        have h2 : s'⁻¹ * (y * s * y⁻¹) ∈ P := by
          apply hcore
          rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hs'e, inv_mul_cancel]
        have := P.mul_mem hs' h2
        rwa [mul_inv_cancel_left] at this
      apply mem_normalizer_of_conj_mem
      intro s hs
      exact (Subgroup.mem_normalizer_iff.mp hyP ⟨s, hs.2⟩).mp
        (show (⟨s, hs.2⟩ : ↥R) ∈ P from hs)
    have h3 : 3 ∣ orderOf (y : A) := by
      have h1 : orderOf (π y) ∣ orderOf y := orderOf_map_dvd π y
      rwa [hy3, ← Subgroup.orderOf_coe] at h1
    exact ⟨(y : A) ^ (orderOf (y : A) / 3), Subgroup.pow_mem _ hyN _,
      orderOf_pow_orderOf_div (orderOf_pos _).ne' h3⟩
  ·
    have hXR : X ≤ R := hX.trans inf_le_left
    let fX : ↥(X.subgroupOf R) →* ModO2 R := π.comp (X.subgroupOf R).subtype
    have hfX : Function.Injective fX := by
      rw [injective_iff_map_eq_one]
      intro b hb
      have hb' : ((b : ↥R) : ↥R) ∈ CFSG.pCore 2 ↥R := by
        rw [← hkerπ]
        exact hb
      obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (G := ↥R) (p := 2))
        ⟨(b : ↥R), hb'⟩
      have hodd : Odd (orderOf (b : ↥R)) := by
        have h1 : orderOf ((b : ↥R) : A) ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X b.2
        rw [Subgroup.orderOf_coe] at h1
        exact Odd.of_dvd_nat hXo h1
      rw [Subgroup.orderOf_mk] at hn
      rw [hn] at hodd
      have hn0 : n = 0 := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · exact h0
        · exact absurd (Nat.even_pow.mpr ⟨even_two, h0.ne'⟩) (Nat.not_even_iff_odd.mpr hodd)
      rw [hn0, pow_zero] at hn
      exact Subtype.ext (orderOf_eq_one_iff.mp hn)
    have hrange : fX.range ≤
        Subgroup.normalizer (((PbS : Subgroup (ModO2 R))) : Set (ModO2 R)) := by
      rintro _ ⟨b, rfl⟩
      have hbN : ((b : ↥R) : A) ∈ Subgroup.normalizer ((S ⊓ R : Subgroup A) : Set A) :=
        (hX (b.2 : ((b : ↥R) : A) ∈ X)).2
      apply mem_normalizer_of_conj_mem
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨(b : ↥R) * s * (b : ↥R)⁻¹, ?_, by simp [fX]⟩
      have hs' : (s : A) ∈ S ⊓ R := hs
      show (((b : ↥R) * s * (b : ↥R)⁻¹ : ↥R) : A) ∈ S ⊓ R
      exact (Subgroup.mem_normalizer_iff.mp hbN _).mp hs'
    have hXdvd : Nat.card X ∣ 12 := by
      have h1 : Nat.card fX.range ∣ 12 :=
        (Subgroup.card_dvd_of_le hrange).trans (card_normalizer_dvd_twelve e₄ PbS)
      rwa [Nat.card_congr (MonoidHom.ofInjective hfX).toEquiv.symm,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXR).toEquiv] at h1
    have hpos : 0 < Nat.card X := Nat.card_pos
    have hle : Nat.card X ≤ 12 := Nat.le_of_dvd (by norm_num) hXdvd
    obtain ⟨m, hm⟩ := hXo
    interval_cases hc : Nat.card X <;> omega

omit [Finite A] in
theorem mem_map_conj_iff {R : Subgroup A} {s y : A} :
    y ∈ R.map (MulAut.conj s).toMonoidHom ↔ s⁻¹ * y * s ∈ R := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_inf_normalizer {R₁ R₂ S : Subgroup A} {s : A} (hs : s ∈ S)
    (hR₂ : R₂ = R₁.map (MulAut.conj s).toMonoidHom) {y : A}
    (hy : y ∈ R₁ ⊓ Subgroup.normalizer ((S ⊓ R₁ : Subgroup A) : Set A)) :
    s * y * s⁻¹ ∈ R₂ ⊓ Subgroup.normalizer ((S ⊓ R₂ : Subgroup A) : Set A) := by
  subst hR₂
  refine Subgroup.mem_inf.mpr ⟨mem_map_conj_iff.mpr
    (by rw [show s⁻¹ * (s * y * s⁻¹) * s = y by group]; exact hy.1),
    mem_normalizer_of_conj_mem fun t ht => ?_⟩
  have ht' : s⁻¹ * t * s ∈ S ⊓ R₁ := Subgroup.mem_inf.mpr
    ⟨mul_mem (mul_mem (inv_mem hs) ht.1) hs, mem_map_conj_iff.mp ht.2⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hy.2 _).mp ht'
  have e : s * y * s⁻¹ * t * (s * y * s⁻¹)⁻¹ = s * (y * (s⁻¹ * t * s) * y⁻¹) * s⁻¹ := by group
  rw [e]
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hs h1.1) (inv_mem hs), mem_map_conj_iff.mpr ?_⟩
  rw [show s⁻¹ * (s * (y * (s⁻¹ * t * s) * y⁻¹) * s⁻¹) * s = y * (s⁻¹ * t * s) * y⁻¹ by group]
  exact h1.2

theorem conj_inv_mem_inf_normalizer {R₁ R₂ S : Subgroup A} {s : A} (hs : s ∈ S)
    (hR₂ : R₂ = R₁.map (MulAut.conj s).toMonoidHom) {y : A}
    (hy : y ∈ R₂ ⊓ Subgroup.normalizer ((S ⊓ R₂ : Subgroup A) : Set A)) :
    s⁻¹ * y * s ∈ R₁ ⊓ Subgroup.normalizer ((S ⊓ R₁ : Subgroup A) : Set A) := by
  subst hR₂
  refine Subgroup.mem_inf.mpr ⟨mem_map_conj_iff.mp hy.1,
    mem_normalizer_of_conj_mem fun t ht => ?_⟩
  have ht' : s * t * s⁻¹ ∈ S ⊓ R₁.map (MulAut.conj s).toMonoidHom := Subgroup.mem_inf.mpr
    ⟨mul_mem (mul_mem hs ht.1) (inv_mem hs),
      mem_map_conj_iff.mpr (by rw [show s⁻¹ * (s * t * s⁻¹) * s = t by group]; exact ht.2)⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hy.2 _).mp ht'
  have e : s⁻¹ * y * s * t * (s⁻¹ * y * s)⁻¹ = s⁻¹ * (y * (s * t * s⁻¹) * y⁻¹) * s := by group
  rw [e]
  exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hs) h1.1) hs, mem_map_conj_iff.mp h1.2⟩

variable {Q₁ Q₂ : Subgroup A}

theorem b_facts (h : CommPair Q₁ Q₂) {R₁ R₂ S B : Subgroup A} {s : A} (hs : s ∈ S)
    (hR₂ : R₂ = R₁.map (MulAut.conj s).toMonoidHom) (hR₁Q : R₁ ≤ Q₁) (hR₂Q : R₂ ≤ Q₂)
    (hL : CFSG.Blueprint.LieModel (ModO2 R₁) .PSL 2 2 2)
    (hSR : IsSylowTwoOf (S ⊓ (R₁ ⊔ R₂)) (R₁ ⊔ R₂))
    (hB : Lin2.IsHallTwoPrimeOf B
      ((R₁ ⊔ R₂) ⊓ Subgroup.normalizer ((S ⊓ (R₁ ⊔ R₂) : Subgroup A) : Set A))) :
    h.img₁ B ≤ R₁ ⊓ Subgroup.normalizer ((S ⊓ R₁ : Subgroup A) : Set A) ∧
    h.img₂ B ≤ R₂ ⊓ Subgroup.normalizer ((S ⊓ R₂ : Subgroup A) : Set A) ∧
    Nat.card B = 9 ∧ Nat.card (h.img₁ B) = 3 ∧ Nat.card (h.img₂ B) = 3 := by
  have hRQ : R₁ ⊔ R₂ ≤ Q₁ ⊔ Q₂ := sup_le_sup hR₁Q hR₂Q
  have e₁ : S ⊓ (R₁ ⊔ R₂) ⊓ R₁ = S ⊓ R₁ := by
    rw [inf_assoc, inf_eq_right.mpr (le_sup_left : R₁ ≤ R₁ ⊔ R₂)]
  have e₂ : S ⊓ (R₁ ⊔ R₂) ⊓ R₂ = S ⊓ R₂ := by
    rw [inf_assoc, inf_eq_right.mpr (le_sup_right : R₂ ≤ R₁ ⊔ R₂)]
  have hSR₁ : IsSylowTwoOf (S ⊓ R₁) R₁ := e₁ ▸ h.isSylowTwoOf_inf₁ hR₁Q hR₂Q hSR
  have hi₁ : h.img₁ (S ⊓ (R₁ ⊔ R₂)) = S ⊓ R₁ := by rw [h.img₁_eq_of_sylow hR₁Q hR₂Q hSR, e₁]
  have hi₂ : h.img₂ (S ⊓ (R₁ ⊔ R₂)) = S ⊓ R₂ := by rw [h.img₂_eq_of_sylow hR₁Q hR₂Q hSR, e₂]
  have hSRe : S ⊓ (R₁ ⊔ R₂) = (S ⊓ R₁) ⊔ (S ⊓ R₂) := by
    rw [← e₁, ← e₂]
    exact h.eq_sup_of_sylow hR₁Q hR₂Q hSR
  obtain ⟨hBM, hBo, k, hk⟩ := hB
  have hBR : B ≤ R₁ ⊔ R₂ := hBM.trans inf_le_left
  have hP₁ : h.img₁ B ≤ R₁ ⊓ Subgroup.normalizer ((S ⊓ R₁ : Subgroup A) : Set A) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := h.exists_of_mem_img₁ ha
    refine ⟨h.img₁_le_of_le hR₁Q hR₂Q hBR ha, ?_⟩
    rw [← hi₁]
    exact h.mem_normalizer_img₁ (h.img₁_le B ha) hb (hBM hab).2
  have hP₂ : h.img₂ B ≤ R₂ ⊓ Subgroup.normalizer ((S ⊓ R₂ : Subgroup A) : Set A) := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := h.exists_of_mem_img₂ hb
    refine ⟨h.img₂_le_of_le hR₁Q hR₂Q hBR hb, ?_⟩
    rw [← hi₂]
    exact h.mem_normalizer_img₂ ha (h.img₂_le B hb) (hBM hab).2
  obtain ⟨⟨w, hw, hw3⟩, hodd₁⟩ := l24_facts hL hSR₁
  have hd₁ : Nat.card (h.img₁ B) ∣ 3 :=
    hodd₁ _ hP₁ (Odd.of_dvd_nat hBo (h.card_img₁_dvd (hBR.trans hRQ)))
  have hd₂ : Nat.card (h.img₂ B) ∣ 3 := by
    have hX : (h.img₂ B).map (MulAut.conj s⁻¹).toMonoidHom ≤
        R₁ ⊓ Subgroup.normalizer ((S ⊓ R₁ : Subgroup A) : Set A) := by
      rintro _ ⟨y, hy, rfl⟩
      have := conj_inv_mem_inf_normalizer hs hR₂ (hP₂ hy)
      simpa [MulAut.conj_apply] using this
    have hXc : Nat.card ((h.img₂ B).map (MulAut.conj s⁻¹).toMonoidHom) = Nat.card (h.img₂ B) :=
      Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective
    rw [← hXc]
    exact hodd₁ _ hX (hXc ▸ Odd.of_dvd_nat hBo (h.card_img₂_dvd (hBR.trans hRQ)))
  have hw₂ := conj_mem_inf_normalizer hs hR₂ hw
  have hN : ∀ {y : A} {i : Subgroup A} {j : Subgroup A}, y ∈ i ⊓
      Subgroup.normalizer ((S ⊓ i : Subgroup A) : Set A) →
      (∀ a ∈ S ⊓ j, a * y = y * a) → (S ⊓ i) ⊔ (S ⊓ j) = S ⊓ (R₁ ⊔ R₂) →
      y ∈ Subgroup.normalizer ((S ⊓ (R₁ ⊔ R₂) : Subgroup A) : Set A) := by
    intro y i j hy hc he
    rw [← he]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hy.2, le_normalizer_of_forall_comm (Y := Subgroup.zpowers y)
        (fun a ha b hb => by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact (Commute.zpow_right (hc a ha) n).eq) (Subgroup.mem_zpowers y)⟩
  have hwN := hN hw (fun a ha => (h.comm w (hR₁Q hw.1) a (hR₂Q ha.2)).symm) hSRe.symm
  have hw₂N := hN hw₂ (fun a ha => h.comm a (hR₁Q ha.2) _ (hR₂Q hw₂.1))
    ((sup_comm (S ⊓ R₂) (S ⊓ R₁)).trans hSRe.symm)
  have hW : CommPair (Subgroup.zpowers w) (Subgroup.zpowers (s * w * s⁻¹)) :=
    h.mono (Subgroup.zpowers_le.mpr (hR₁Q hw.1)) (Subgroup.zpowers_le.mpr (hR₂Q hw₂.1))
  have hW9 : Nat.card ↥(Subgroup.zpowers w ⊔ Subgroup.zpowers (s * w * s⁻¹)) = 9 := by
    rw [hW.card_sup, Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hw3]
  have hWM : Subgroup.zpowers w ⊔ Subgroup.zpowers (s * w * s⁻¹) ≤
      (R₁ ⊔ R₂) ⊓ Subgroup.normalizer ((S ⊓ (R₁ ⊔ R₂) : Subgroup A) : Set A) :=
    sup_le (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_left hw.1, hwN⟩)
      (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_right hw₂.1, hw₂N⟩)
  have hM : Nat.card ↥((R₁ ⊔ R₂) ⊓ Subgroup.normalizer ((S ⊓ (R₁ ⊔ R₂) : Subgroup A) : Set A)) =
      2 ^ k * Nat.card B := by
    rw [← hk, ← Subgroup.relIndex_mul_card B _, inf_eq_left.mpr hBM]
  have h9 : 9 ∣ Nat.card B := by
    have := Subgroup.card_dvd_of_le hWM
    rw [hW9, hM] at this
    exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_left this
  have hle := h.card_le_mul (hBR.trans hRQ)
  have h1 : Nat.card (h.img₁ B) ≤ 3 := Nat.le_of_dvd (by norm_num) hd₁
  have h2 : Nat.card (h.img₂ B) ≤ 3 := Nat.le_of_dvd (by norm_num) hd₂
  have hB9 : Nat.card B = 9 := by
    have : Nat.card B ≤ 9 := hle.trans (by nlinarith)
    have hpos : 0 < Nat.card B := Nat.card_pos
    obtain ⟨c, hc⟩ := h9
    have : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · omega
    omega
  refine ⟨hP₁, hP₂, hB9, ?_, ?_⟩
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd₁ with h0 | h0
    · rw [hB9, h0] at hle
      omega
    · exact h0
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd₂ with h0 | h0
    · rw [hB9, h0] at hle
      omega
    · exact h0

theorem le_inf_normalizer_of_img (h : CommPair Q₁ Q₂) {R₁ R₂ S X : Subgroup A} (hR₁Q : R₁ ≤ Q₁)
    (hR₂Q : R₂ ≤ Q₂) (hSR : IsSylowTwoOf (S ⊓ (R₁ ⊔ R₂)) (R₁ ⊔ R₂)) (hXQ : X ≤ Q₁ ⊔ Q₂)
    (h₁ : h.img₁ X ≤ R₁ ⊓ Subgroup.normalizer ((S ⊓ R₁ : Subgroup A) : Set A))
    (h₂ : h.img₂ X ≤ R₂ ⊓ Subgroup.normalizer ((S ⊓ R₂ : Subgroup A) : Set A)) :
    X ≤ (R₁ ⊔ R₂) ⊓ Subgroup.normalizer ((S ⊓ (R₁ ⊔ R₂) : Subgroup A) : Set A) := by
  have e₁ : S ⊓ (R₁ ⊔ R₂) ⊓ R₁ = S ⊓ R₁ := by
    rw [inf_assoc, inf_eq_right.mpr (le_sup_left : R₁ ≤ R₁ ⊔ R₂)]
  have e₂ : S ⊓ (R₁ ⊔ R₂) ⊓ R₂ = S ⊓ R₂ := by
    rw [inf_assoc, inf_eq_right.mpr (le_sup_right : R₂ ≤ R₁ ⊔ R₂)]
  have hSRe : S ⊓ (R₁ ⊔ R₂) = (S ⊓ R₁) ⊔ (S ⊓ R₂) := by
    rw [← e₁, ← e₂]
    exact h.eq_sup_of_sylow hR₁Q hR₂Q hSR
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_img hXQ hx
  have ha' := Subgroup.mem_inf.mp (h₁ ha)
  have hb' := Subgroup.mem_inf.mp (h₂ hb)
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem_sup ha'.1 hb'.1, ?_⟩
  rw [hSRe]
  refine mul_mem (Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨ha'.2, ?_⟩)
    (Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, hb'.2⟩)
  · exact le_normalizer_of_forall_comm (X := S ⊓ R₂) (Y := Q₁)
      (fun u hu v hv => (h.comm v hv u (hR₂Q (Subgroup.mem_inf.mp hu).2)).symm) (h.img₁_le X ha)
  · exact le_normalizer_of_forall_comm (X := S ⊓ R₁) (Y := Q₂)
      (fun u hu v hv => h.comm u (hR₁Q (Subgroup.mem_inf.mp hu).2) v hv) (h.img₂_le X hb)

end CFSG.Quasithin.H13.NQCat.C2
