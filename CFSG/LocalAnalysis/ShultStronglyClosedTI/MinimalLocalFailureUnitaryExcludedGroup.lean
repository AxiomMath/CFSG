module

public import Mathlib.GroupTheory.Sylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_of_isPGroup_of_le_sup [Finite G] {T M X : Subgroup G} (hT : IsPGroup 2 T)
    (hM : M ≤ Subgroup.normalizer (T : Set G)) (hModd : Odd (Nat.card M)) (hX : IsPGroup 2 X)
    (hXle : X ≤ T ⊔ M) : X ≤ T := by
  have hN : T ⊔ M ≤ Subgroup.normalizer (T : Set G) := sup_le Subgroup.le_normalizer hM
  have hXT : IsPGroup 2 (X ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hX hT (hXle.trans hN)
  intro x hx
  have hxTM : x ∈ ((T ⊔ M : Subgroup G) : Set G) := hXle hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left T M hM] at hxTM
  obtain ⟨τ, hτ, m, hm, rfl⟩ := hxTM
  have hmXT : m ∈ X ⊔ T := by
    have h := (X ⊔ T).mul_mem ((X ⊔ T).inv_mem (Subgroup.mem_sup_right hτ))
      (Subgroup.mem_sup_left hx)
    rwa [inv_mul_cancel_left] at h
  obtain ⟨k, hk⟩ := hXT ⟨m, hmXT⟩
  have hk' : m ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hodd : Odd (orderOf m) := by
    have hdvd : orderOf m ∣ Nat.card M := by
      rw [← Subgroup.orderOf_mk m hm]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hModd hdvd
  have hdvd2 : orderOf m ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf m) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have h1 : m = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd2)
  subst h1
  simpa using hτ

theorem card_sup_mul_card_inf [Finite G] {T W : Subgroup G}
    (hW : W ≤ Subgroup.normalizer (T : Set G)) :
    Nat.card (T ⊔ W : Subgroup G) * Nat.card (T ⊓ W : Subgroup G) = Nat.card T * Nat.card W := by
  set N : Subgroup G := Subgroup.normalizer (T : Set G)
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hTWN : T ⊔ W ≤ N := sup_le hTN hW
  have : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr le_rfl
  have hrel : T.relIndex (T ⊔ W) = (T ⊓ W).relIndex W := by
    rw [← Subgroup.relIndex_subgroupOf hTWN, Subgroup.subgroupOf_sup hTN hW,
      Subgroup.relIndex_sup_left, Subgroup.relIndex_subgroupOf hW, Subgroup.inf_relIndex_right]
  have h1 := Subgroup.relIndex_mul_card T (T ⊔ W)
  rw [inf_of_le_left le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (T ⊓ W) W
  rw [inf_of_le_left inf_le_right] at h2
  rw [← h1, ← h2, hrel]
  ring

theorem mem_normalizer_of_le_isCyclic [Finite G] {A A₀ : Subgroup G} (hA : A ≤ A₀)
    (hcyc : IsCyclic A₀) {g : G} (hg : g ∈ Subgroup.normalizer (A₀ : Set G)) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  set A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom
  have hA'A₀ : A' ≤ A₀ := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp (hA ha)
  have hcard : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hsub : A'.subgroupOf A₀ = A.subgroupOf A₀ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'A₀).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hcard]
  have hA'eq : A' = A := by
    have h := Subgroup.subgroupOf_inj.mp hsub
    rwa [inf_of_le_left hA'A₀, inf_of_le_left hA] at h
  refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [← hA'eq]
    exact ⟨a, ha, rfl⟩
  · rw [← hA'eq] at ha
    obtain ⟨b, hb, hba⟩ := ha
    have : b = a := by
      have h := hba
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      exact mul_left_cancel (mul_right_cancel h)
    rwa [← this]

theorem mem_normalizer_centralizer {S : Set G} {g : G} (hg : g ∈ Subgroup.normalizer S) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer S : Set G) := by
  have key : ∀ {h : G}, h ∈ Subgroup.normalizer S → ∀ c ∈ Subgroup.centralizer S,
      h * c * h⁻¹ ∈ Subgroup.centralizer S := by
    intro h hh c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : h⁻¹ * s * h ∈ S := (Subgroup.mem_set_normalizer_iff''.mp hh s).mp hs
    have hc' := Subgroup.mem_centralizer_iff.mp hc _ hs'
    calc s * (h * c * h⁻¹) = h * ((h⁻¹ * s * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * s * h)) * h⁻¹ := by rw [hc']
      _ = h * c * h⁻¹ * s := by group
  refine Subgroup.mem_set_normalizer_iff.mpr fun c => ⟨key hg c, fun hc => ?_⟩
  have h := key (inv_mem hg) _ hc
  rwa [inv_inv, show g⁻¹ * (g * c * g⁻¹) * g = c by group] at h

theorem mem_normalizer_commutator {C A : Subgroup G} {g : G}
    (hC : g ∈ Subgroup.normalizer (C : Set G)) (hA : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (⁅C, A⁆ : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hC hA ⊢
  rw [Subgroup.map_commutator, hC, hA]

theorem exists_conj_le_of_not_two_dvd_index [Finite G] {N X Y : Subgroup G} (hXN : X ≤ N)
    (hX : IsPGroup 2 X) (hXodd : ¬ 2 ∣ X.index) (hYN : Y ≤ N) (hY : IsPGroup 2 Y) :
    ∃ g ∈ N, Y.map (MulAut.conj g).toMonoidHom ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXrel : ¬ 2 ∣ (X.subgroupOf N).index := by
    intro h
    apply hXodd
    rw [← Subgroup.relIndex_mul_index hXN]
    exact Dvd.dvd.mul_right h _
  have hXp : IsPGroup 2 (X.subgroupOf N) :=
    hX.comap_of_injective N.subtype N.subtype_injective
  set PX : Sylow 2 N := hXp.toSylow hXrel
  have hYp : IsPGroup 2 (Y.subgroupOf N) :=
    hY.comap_of_injective N.subtype N.subtype_injective
  obtain ⟨PY, hPY⟩ := hYp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N PY PX
  refine ⟨n, n.2, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hyN : (⟨y, hYN hy⟩ : N) ∈ PY := hPY hy
  have hmem : n * ⟨y, hYN hy⟩ * n⁻¹ ∈ (PX : Subgroup N) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact ⟨_, hyN, rfl⟩
  rw [IsPGroup.toSylow_coe] at hmem
  exact hmem

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
