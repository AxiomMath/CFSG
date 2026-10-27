module

public import CFSG.Quasithin.Background.HSL3One

public section

namespace CFSG.Quasithin

namespace H

namespace SL3One

open CFSG.Open CFSG.Assembly.LowTwoRank SL3Pair

theorem four_le_card_sup_zpowers {W : Type*} [CommGroup W] [Finite (MulAut W)]
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian2 E) {x y : MulAut W} (hxE : x ∈ E)
    (hyE : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    4 ≤ Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  have hxx : x * x = 1 := by
    rw [← sq]
    exact hE.2 x hxE
  have hF : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.mpr hxE) (Subgroup.zpowers_le.mpr hyE)
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    (E3.isPGroup_of_isElemAbelian2 hE).to_le hF
  have hlt : Subgroup.zpowers x < Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hy : y ∈ Subgroup.zpowers x := h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · apply hy1
      rw [← hk, ← two_mul, zpow_mul, zpow_two, hxx, one_zpow]
    · apply hxy
      rw [← hk, zpow_add, zpow_mul, zpow_two, hxx, one_zpow, one_mul, zpow_one]
  have h2 := Subgroup.card_lt_of_lt hlt
  rw [card_zpowers_eq_two hxx hx1, card_eq_two_pow_of_isPGroup hpg] at h2
  rw [card_eq_two_pow_of_isPGroup hpg]
  have hk : 2 ≤ rk ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
    by_contra h
    push Not at h
    have h1 : 2 ^ rk ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_one] at h1
    omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hk

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_sup_ge_of_sub (hK : Nat.card K = 2) {E : Subgroup (MulAut (PairMod K))}
    (hEN : E ≤ pairNorm K) (hE2 : IsElemAbelian2 E) (hsub : E ≤ pairSub K)
    {x y : MulAut (PairMod K)} (hxE : x ∈ E) (hyE : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x ≠ y) :
    2 ^ 5 ≤ Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y)) := by
  have hxx : x * x = 1 := by
    rw [← sq]
    exact hE2.2 x hxE
  have hyy : y * y = 1 := by
    rw [← sq]
    exact hE2.2 y hyE
  set F := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hFdef
  have hFE : F ≤ E := sup_le (Subgroup.zpowers_le.mpr hxE) (Subgroup.zpowers_le.mpr hyE)
  have hF2 : IsElemAbelian2 F :=
    ⟨fun a ha b hb => hE2.1 a (hFE ha) b (hFE hb), fun a ha => hE2.2 a (hFE ha)⟩
  have hF4 : 4 ≤ Nat.card F := four_le_card_sup_zpowers hE2 hxE hyE hx1 hy1 hxy
  have h8 := card_fixV_le_eight_of_sub hK (hFE.trans hEN) hF2 hF4 (hFE.trans hsub)
  have hinf : fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y) ≤ fixV F := by
    intro v hv
    have hS : F ≤ MulAction.stabilizer (MulAut (PairMod K)) v := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact H.mem_fixV_zpowers_iff.mp hv.1
      · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact H.mem_fixV_zpowers_iff.mp hv.2
    rw [mem_fixV]
    intro f hf
    have h := hS hf
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h
  have hle8 : Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers y)) ≤ 8 :=
    (Subgroup.card_le_of_le hinf).trans h8
  have hfx := sixteen_le_card_fixV hK (hsub hxE) hxx
  have hfy := sixteen_le_card_fixV hK (hsub hyE) hyy
  have hprod := card_mul_le_card_inf_mul_card_sup (fixV (Subgroup.zpowers x))
    (fixV (Subgroup.zpowers y))
  have key : 16 * 16 ≤ 8 * Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y)) :=
    calc 16 * 16 ≤ Nat.card ↥(fixV (Subgroup.zpowers x)) *
          Nat.card ↥(fixV (Subgroup.zpowers y)) := Nat.mul_le_mul hfx hfy
      _ ≤ _ := hprod
      _ ≤ _ := Nat.mul_le_mul_right _ hle8
  have e : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [e]
  omega

theorem H4_SL3One_inner {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL H V₁ ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) {E : Subgroup (MulAut V)}
    (hEH : E ≤ H) (hE2 : IsElemAbelian2 E) (hE4 : Nat.card E = 4) :
    (∀ x ∈ E, ∀ y ∈ E, ∀ v : V, y (x v * v⁻¹) = x v * v⁻¹) ∧
      ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧
        2 ^ 5 ≤ Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y)) := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod K) := Finite.of_equiv V e.toEquiv
  have hmem : ∀ z ∈ H, congrHom e z ∈ pairSL K := fun z hz => by
    rw [← he]
    exact ⟨z, hz, rfl⟩
  have hNS : ∀ z ∈ E, congrHom e z ∈ pairNorm K ∧ congrHom e z ∈ pairSub K := by
    intro z hz
    refine ⟨pairSL_le_pairNorm (hmem z (hEH hz)), ?_⟩
    obtain ⟨γ, -, hγz⟩ := hmem z (hEH hz)
    rw [← hγz, pairHom_apply]
    exact pairAut_mem_pairSub _ _
  have hsq : ∀ z ∈ E, z * z = 1 := fun z hz => by
    rw [← sq]
    exact hE2.2 z hz
  have hsq' : ∀ z ∈ E, congrHom e z * congrHom e z = 1 := fun z hz => by
    rw [← map_mul, hsq z hz, map_one]
  refine ⟨fun x hx y hy v => ?_, ?_⟩
  ·
    obtain ⟨hxN, hxS⟩ := hNS x hx
    obtain ⟨hyN, hyS⟩ := hNS y hy
    have hxy : congrHom e x * congrHom e y = congrHom e y * congrHom e x := by
      rw [← map_mul, ← map_mul, hE2.1 x hx y hy]
    have h := fix_comm_of_sub hK2 hxN hyN hxS hyS (hsq' x hx) (hsq' y hy) hxy (e v)
    have e1 : congrHom e x (e v) = e (x v) := by
      rw [congrHom_apply, MulEquiv.symm_apply_apply]
    have e2 : e (x v * v⁻¹) = e (x v) * (e v)⁻¹ := by
      rw [map_mul, map_inv]
    rw [e1, ← e2, congrHom_apply, MulEquiv.symm_apply_apply] at h
    exact e.injective h
  ·
    obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
      rw [hbot, Subgroup.card_bot] at hE4
      omega
    obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers x := by
      by_contra h
      push Not at h
      have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers x from h)
      rw [hE4, card_zpowers_eq_two (hsq x hxE) hx1] at hle
      omega
    have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
    have hxy : x ≠ y := fun h => hyx (h ▸ Subgroup.mem_zpowers x)
    refine ⟨x, hxE, y, hyE, hx1, hy1, ?_⟩
    have hE'N : E.map (congrHom e) ≤ pairNorm K := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hNS z hz).1
    have hE'S : E.map (congrHom e) ≤ pairSub K := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hNS z hz).2
    have hE'2 : IsElemAbelian2 (E.map (congrHom e)) := (isElemAbelian2_map_congrHom e).mpr hE2
    have hx1' : congrHom e x ≠ 1 := fun h =>
      hx1 (congrHom_injective e (h.trans (map_one _).symm))
    have hy1' : congrHom e y ≠ 1 := fun h =>
      hy1 (congrHom_injective e (h.trans (map_one _).symm))
    have hxy' : congrHom e x ≠ congrHom e y := fun h => hxy (congrHom_injective e h)
    have h := card_sup_ge_of_sub hK2 hE'N hE'2 hE'S ⟨x, hxE, rfl⟩ ⟨y, hyE, rfl⟩ hx1' hy1' hxy'
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, fixV_map_congrHom,
      fixV_map_congrHom, ← Subgroup.map_sup,
      Subgroup.card_map_of_injective (e.injective : Function.Injective e.toMonoidHom)] at h
    exact h

end SL3One

end H

end CFSG.Quasithin
