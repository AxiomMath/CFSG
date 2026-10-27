module

public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftBasic
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLift

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace E2.BorelLift

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem eq_of_two_pow_mul_eq {k m c d : ℕ} (hc : Odd c) (hd : Odd d) (h : 2 ^ k * c = 2 ^ m * d) :
    c = d := by
  have h1 : c ∣ d := by
    have : c ∣ 2 ^ m * d := ⟨2 ^ k, by rw [← h, mul_comm]⟩
    exact (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hc)).dvd_of_dvd_mul_left this
  have h2 : d ∣ c := by
    have : d ∣ 2 ^ k * c := ⟨2 ^ m, by rw [h, mul_comm]⟩
    exact (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hd)).dvd_of_dvd_mul_left this
  exact Nat.dvd_antisymm h1 h2

omit [Finite Γ] in
theorem exists_eq_two_pow_of_dvd {a b : ℕ} (h : a ∣ 2 ^ b) : ∃ k : ℕ, a = 2 ^ k := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact ⟨k, hk⟩

theorem lift_of_borel {H T M R₀ P₂ Y₀ : Subgroup Γ} {w₀ : Γ} {n : ℕ}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hMH : M ≤ H)
    (hHR : H ≤ Subgroup.normalizer (R₀ : Set Γ)) (hRH : R₀ ≤ H) (hHRT : H ≤ R₀ ⊔ T)
    (hMS : M ≤ Subgroup.normalizer ((T ⊓ R₀ : Subgroup Γ) : Set Γ))
    (hcomm : ∀ a ∈ M ⊓ R₀, ∀ b ∈ M ⊓ R₀, a * b * a⁻¹ * b⁻¹ ∈ T ⊓ R₀)
    (hn : 1 ≤ n) (hY₀ : Y₀ ≤ M ⊓ R₀) (hYc : IsCyclic ↥Y₀) (hYcard : Nat.card Y₀ = 2 ^ n - 1)
    (hP₂M : P₂ ≤ M) (hP₂ : IsPGroup 2 ↥P₂) (hYP : Y₀ ≤ Subgroup.normalizer (P₂ : Set Γ))
    (hw₀H : w₀ ∈ H) (hw₀M : w₀ ∉ M)
    (hw₀ : ∀ A : Subgroup Γ, A ≤ Y₀ → ∀ a ∈ A, w₀ * a * w₀⁻¹ ∈ A ⊔ P₂) :
    E22BorelLift H T M n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup Γ := T ⊓ R₀ with hSdef
  set P : Subgroup Γ := M ⊓ R₀ with hPdef
  have hT2 : IsPGroup 2 T := hT.2.1
  have hS2 : IsPGroup 2 S := hT2.to_le inf_le_left
  have hSP : S ≤ P := le_inf (inf_le_left.trans hTM) inf_le_right
  have hPM : P ≤ M := inf_le_left
  have hMP : M ≤ Subgroup.normalizer (P : Set Γ) := by
    intro m hm
    have hmR := hHR (hMH hm)
    rw [Subgroup.mem_normalizer_iff] at hmR ⊢
    intro x
    constructor
    · rintro ⟨hxM, hxR⟩
      exact ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), (hmR x).mp hxR⟩
    · rintro ⟨hxM, hxR⟩
      refine ⟨?_, (hmR x).mpr hxR⟩
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm
      simpa [mul_assoc] using this
  have hPS : P ≤ Subgroup.normalizer (S : Set Γ) := hPM.trans hMS
  have hTMs : IsSylowTwoOf T M := A4.isSylowTwoOf_mono hT hTM hMH
  have hSsyl : IsSylowTwoOf S P := by
    have h := A4.isSylowTwoOf_inf_normal hTMs hPM hMP
    have he : T ⊓ P = S := by
      rw [hPdef, hSdef, ← inf_assoc, inf_eq_left.mpr hTM]
    rwa [he] at h
  have hSodd : Odd (S.relIndex P) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hSsyl.2.2
  have hTN : T ≤ Subgroup.normalizer (R₀ : Set Γ) := (hT.1).trans hHR
  have hMPT : M ≤ T ⊔ P := by
    intro m hm
    have hmRT : m ∈ ((R₀ ⊔ T : Subgroup Γ) : Set Γ) := hHRT (hMH hm)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R₀ T hTN] at hmRT
    obtain ⟨r, hr, t, ht, rfl⟩ := hmRT
    have hrM : r ∈ M := by
      have := M.mul_mem hm (M.inv_mem (hTM ht))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hrM, hr⟩) (Subgroup.mem_sup_left ht)
  have hMeq : T ⊔ P = M := le_antisymm (sup_le hTM hPM) hMPT
  have hTP : T ≤ Subgroup.normalizer (P : Set Γ) := hTM.trans hMP
  obtain ⟨a, ha⟩ : ∃ a : ℕ, P.relIndex M = 2 ^ a := by
    have h1 := A4.relIndex_sup_eq_of_le_normalizer' hTP
    rw [hMeq] at h1
    rw [h1]
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    exact exists_eq_two_pow_of_dvd (hk ▸ Subgroup.relIndex_dvd_card P T)
  obtain ⟨b, hb⟩ := hS2.exists_card_eq
  have hcP : Nat.card P = S.relIndex P * 2 ^ b := by
    have h := Subgroup.relIndex_mul_card S P
    rw [inf_eq_left.mpr hSP, hb] at h
    exact h.symm
  have hcM : Nat.card M = 2 ^ a * (S.relIndex P * 2 ^ b) := by
    have h := Subgroup.relIndex_mul_card P M
    rw [inf_eq_left.mpr hPM, ha, hcP] at h
    exact h.symm
  have hO2 : oTwoUpper H ≤ R₀ := by
    obtain ⟨c, hc⟩ : ∃ c : ℕ, R₀.relIndex H = 2 ^ c := by
      have hHeq : T ⊔ R₀ = H := le_antisymm (sup_le hT.1 hRH) (by rwa [sup_comm] at hHRT)
      have h1 := A4.relIndex_sup_eq_of_le_normalizer' hTN
      rw [hHeq] at h1
      rw [h1]
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      exact exists_eq_two_pow_of_dvd (hk ▸ Subgroup.relIndex_dvd_card R₀ T)
    refine (Subgroup.closure_le R₀).mpr fun x ⟨hxH, hxo⟩ => ?_
    have hle := le_of_odd hRH hHR hc ((Subgroup.zpowers_le).mpr hxH)
      (by rw [Nat.card_zpowers]; exact hxo)
    exact hle (Subgroup.mem_zpowers x)
  have hPsolv : Group.IsSolvable P := by
    set N : Subgroup P := S.subgroupOf P with hN
    have hNn : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPS
    have hN2 : IsPGroup 2 N := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSP).symm
    have hNs : Group.IsSolvable N := by
      have := hN2.isNilpotent
      infer_instance
    have hQs : Group.IsSolvable (↥P ⧸ N) := by
      refine Group.isSolvable_of_comm fun x y => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N y
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ N := hcomm x x.2 y y.2
      rw [← QuotientGroup.eq_one_iff] at h1
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
      simp only [QuotientGroup.mk'_apply]
      calc (x : ↥P ⧸ N) * y = ((x : ↥P ⧸ N) * y * (x : ↥P ⧸ N)⁻¹ * (y : ↥P ⧸ N)⁻¹) * (y * x) := by
            group
        _ = y * x := by rw [h1, one_mul]
    exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', N.range_subtype])
  have hMsolv : Group.IsSolvable M := by
    set N : Subgroup M := P.subgroupOf M with hN
    have hNn : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hMP
    have hNs : Group.IsSolvable N :=
      Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hPM).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPM).injective
    have hQ2 : IsPGroup 2 (↥M ⧸ N) := IsPGroup.of_card (n := a) (by
      rw [← Subgroup.index_eq_card]
      exact ha)
    have hQs : Group.IsSolvable (↥M ⧸ N) := by
      have := hQ2.isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', N.range_subtype])
  refine ⟨hMsolv, S, inf_le_left, hS2, hMS, ?_, ?_⟩
  ·
    obtain ⟨C₀, hC₀P, hC₀card, -⟩ := exists_complement hSP hPS hS2 hSodd
    refine ⟨C₀, hC₀P.trans hPM, hC₀card ▸ hSodd, a + b, ?_⟩
    have h1 := Subgroup.relIndex_mul_card C₀ M
    rw [inf_eq_left.mpr (hC₀P.trans hPM), hcM, hC₀card] at h1
    have hpos : 0 < S.relIndex P := hSodd.pos
    rw [pow_add]
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  intro C hCM hCodd ⟨k, hk⟩
  have hCP : C ≤ P := le_of_odd hPM hMP ha hCM hCodd
  have hcC : Nat.card C = S.relIndex P := by
    have h1 := Subgroup.relIndex_mul_card C M
    rw [inf_eq_left.mpr hCM, hk, hcM] at h1
    exact eq_of_two_pow_mul_eq (m := a + b) hCodd hSodd (by rw [h1, pow_add]; ring)
  have hCS0 : C ⊓ S = ⊥ := inf_eq_bot_of_odd hCodd hS2
  have hCN : C ≤ Subgroup.normalizer (S : Set Γ) := hCP.trans hPS
  have hCSP : C ⊔ S = P := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hCP hSP) ?_
    have h1 := card_sup_mul_card_inf hCN
    rw [hCS0, Subgroup.card_bot, mul_one, hcC, hb] at h1
    rw [h1, hcP]
  refine ⟨hCSP ▸ hMP, ?_, ?_, ?_⟩
  · rw [hCSP]
    exact le_inf inf_le_left (inf_le_right.trans hO2)
  ·
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have h1 : (x : Γ) * y * (x : Γ)⁻¹ * (y : Γ)⁻¹ ∈ C ⊓ S :=
      ⟨C.mul_mem (C.mul_mem (C.mul_mem x.2 y.2) (C.inv_mem x.2)) (C.inv_mem y.2),
        hcomm _ (hCP x.2) _ (hCP y.2)⟩
    rw [hCS0, Subgroup.mem_bot] at h1
    simp only [Subgroup.coe_mul]
    calc (x : Γ) * y = ((x : Γ) * y * (x : Γ)⁻¹ * (y : Γ)⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  ·
    have hY₀odd : Odd (Nat.card Y₀) := by rw [hYcard]; exact odd_two_pow_sub_one hn
    have hY₀S : Y₀ ≤ Subgroup.normalizer (S : Set Γ) := (hY₀.trans hPM).trans hMS
    set F : Subgroup Γ := Y₀ ⊔ S with hF
    have hY₀S0 : Y₀ ⊓ S = ⊥ := inf_eq_bot_of_odd hY₀odd hS2
    have hcF : Nat.card F = Nat.card Y₀ * Nat.card S := by
      have h1 := card_sup_mul_card_inf hY₀S
      rwa [hY₀S0, Subgroup.card_bot, mul_one] at h1
    set C' : Subgroup Γ := C ⊓ F with hC'
    have hC'S : C' ⊔ S = F := by
      refine le_antisymm (sup_le inf_le_right le_sup_right) ?_
      intro x hx
      have hxP : x ∈ ((C ⊔ S : Subgroup Γ) : Set Γ) := by
        rw [hCSP]
        exact sup_le hY₀ hSP hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right C S hCN] at hxP
      obtain ⟨c, hc, s, hs, rfl⟩ := hxP
      have hcF : c ∈ F := by
        have := F.mul_mem hx (F.inv_mem ((le_sup_right : S ≤ Y₀ ⊔ S) hs))
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hc, hcF⟩) (Subgroup.mem_sup_right hs)
    have hC'N : C' ≤ Subgroup.normalizer (S : Set Γ) := inf_le_left.trans hCN
    have hcC' : Nat.card C' = Nat.card Y₀ := by
      have h1 := card_sup_mul_card_inf hC'N
      have hC'S0 : C' ⊓ S = ⊥ := le_bot_iff.mp (hCS0 ▸ inf_le_inf_right S inf_le_left)
      rw [hC'S0, Subgroup.card_bot, mul_one, hC'S, hcF] at h1
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1.symm
    obtain ⟨s, hs, hC'eq⟩ := exists_conj_of_card_eq hS2 hY₀odd hY₀S
      (inf_le_right : C' ≤ F) hcC'
    have hC'eq' : C' = Y₀.map (MulAut.conj s⁻¹).toMonoidHom := hC'eq
    refine ⟨C', inf_le_left, ?_, hcC'.trans hYcard, ?_⟩
    · rw [hC'eq']
      exact isCyclic_of_injective
        (Subgroup.equivMapOfInjective Y₀ (MulAut.conj s⁻¹).toMonoidHom
          (MulAut.conj s⁻¹).injective).symm.toMonoidHom
        (Subgroup.equivMapOfInjective Y₀ (MulAut.conj s⁻¹).toMonoidHom
          (MulAut.conj s⁻¹).injective).symm.injective
    · intro A hAC' hA1 hle
      have hsM : s ∈ M := hTM hs.1
      set A₀ : Subgroup Γ := A.map (MulAut.conj s).toMonoidHom with hA₀
      have hA₀Y : A₀ ≤ Y₀ := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' := hAC' hx
        rw [hC'eq'] at hx'
        obtain ⟨y, hy, rfl⟩ := hx'
        simpa [MulAut.conj_apply, mul_assoc] using hy
      have hcA₀ : Nat.card A₀ = Nat.card A :=
        Subgroup.card_map_of_injective (MulAut.conj s).injective
      have hA₀odd : Odd (Nat.card A₀) :=
        hY₀odd.of_dvd_nat (Subgroup.card_dvd_of_le hA₀Y)
      set A₁ : Subgroup Γ := A₀.map (MulAut.conj w₀).toMonoidHom with hA₁
      have hA₁le : A₁ ≤ A₀ ⊔ P₂ := by
        rintro _ ⟨x, hx, rfl⟩
        exact hw₀ A₀ hA₀Y x hx
      have hcA₁ : Nat.card A₁ = Nat.card A₀ :=
        Subgroup.card_map_of_injective (MulAut.conj w₀).injective
      obtain ⟨q, hq, hA₁eq⟩ := exists_conj_of_card_eq hP₂ hA₀odd (hA₀Y.trans hYP) hA₁le hcA₁
      have hgN : q * w₀ ∈ Subgroup.normalizer (A₀ : Set Γ) := by
        refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
        have h1 : w₀ * x * w₀⁻¹ ∈ A₁ := ⟨x, hx, rfl⟩
        rw [hA₁eq] at h1
        obtain ⟨y, hy, hyx⟩ := h1
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hyx
        have : q * w₀ * x * (q * w₀)⁻¹ = y := by
          calc q * w₀ * x * (q * w₀)⁻¹ = q * (w₀ * x * w₀⁻¹) * q⁻¹ := by group
            _ = q * (q⁻¹ * y * q) * q⁻¹ := by rw [hyx]
            _ = y := by group
        rw [this]
        exact hy
      have hg'N : s⁻¹ * (q * w₀) * s ∈ Subgroup.normalizer (A : Set Γ) := by
        refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
        have h1 : s * x * s⁻¹ ∈ A₀ := ⟨x, hx, rfl⟩
        have h2 := (Subgroup.mem_normalizer_iff.mp hgN _).mp h1
        obtain ⟨z, hz, hzx⟩ := h2
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzx
        have : s⁻¹ * (q * w₀) * s * x * (s⁻¹ * (q * w₀) * s)⁻¹ = z := by
          calc s⁻¹ * (q * w₀) * s * x * (s⁻¹ * (q * w₀) * s)⁻¹
              = s⁻¹ * ((q * w₀) * (s * x * s⁻¹) * (q * w₀)⁻¹) * s := by group
            _ = s⁻¹ * (s * z * s⁻¹) * s := by rw [hzx]
            _ = z := by group
        rw [this]
        exact hz
      have hg'H : s⁻¹ * (q * w₀) * s ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem (hMH hsM)) (H.mul_mem (hMH (hP₂M hq)) hw₀H)) (hMH hsM)
      have hg'M := hle ⟨hg'H, hg'N⟩
      apply hw₀M
      have h1 : q * w₀ ∈ M := by
        have := M.mul_mem (M.mul_mem hsM hg'M) (M.inv_mem hsM)
        simpa [mul_assoc] using this
      have := M.mul_mem (M.inv_mem (hP₂M hq)) h1
      simpa using this

end E2.BorelLift

end CFSG.Quasithin
