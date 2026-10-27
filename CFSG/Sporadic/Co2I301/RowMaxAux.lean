module

public import CFSG.Sporadic.Co2I301.SpecSix
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Max

public noncomputable section

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremA.H301

private theorem wordVal_mem_of {M : Type*} [Group M] (H : Subgroup M) {g : List M}
    (hg : ∀ x ∈ g, x ∈ H) (w : List ℕ) : wordVal g w ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [List.getD_eq_getElem?_getD]
  cases h : g[i]? with
  | none => exact H.one_mem
  | some y => exact hg y (List.mem_of_getElem? h)

private theorem mem_locC_of_conj_mem
    {x : Equiv.Perm (Fin 2300)} (hx : x ∈ co2P) (h : ∀ q ∈ locQ, x * q * x⁻¹ ∈ locQ)
    (h' : ∀ q ∈ locQ, x⁻¹ * q * x ∈ locQ) : x ∈ locC := by
  have hz := locZ_mem_centerIn_Q
  have hc : x * locZ * x⁻¹ ∈ CFSG.centerIn locQ := by
    refine Subgroup.mem_inf.2 ⟨h _ (Subgroup.mem_inf.1 hz).1,
      Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 _ (h' q hq)
    calc q * (x * locZ * x⁻¹) = x * (x⁻¹ * q * x * locZ) * x⁻¹ := by group
      _ = x * (locZ * (x⁻¹ * q * x)) * x⁻¹ := by rw [h1]
      _ = x * locZ * x⁻¹ * q := by group
  have hne : x * locZ * x⁻¹ ≠ 1 := by
    intro h0
    apply locZ_ne_one
    calc locZ = x⁻¹ * (x * locZ * x⁻¹) * x := by group
      _ = 1 := by rw [h0]; group
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : CFSG.centerIn locQ)).1 card_centerIn_Q
  have e1 := huniq ⟨_, hc⟩ fun h0 => hne (congrArg Subtype.val h0)
  have e2 := huniq ⟨_, hz⟩ fun h0 => locZ_ne_one (congrArg Subtype.val h0)
  have heq : x * locZ * x⁻¹ = locZ := congrArg Subtype.val (e1.trans e2.symm)
  rw [locC_eq_centralizer]
  refine Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc x * locZ = x * locZ * x⁻¹ * x := by group
    _ = locZ * x := by rw [heq]

private theorem exists_mem_locC_of_not_le
    {R : Subgroup co2P} (hR : IsPGroup 2 R) (hQR : locQ.subgroupOf co2P ≤ R)
    (hne : ¬ R ≤ locQ.subgroupOf co2P) :
    ∃ x : co2P, x ∈ R ∧ (x : Equiv.Perm (Fin 2300)) ∈ locC ∧
      (x : Equiv.Perm (Fin 2300)) ∉ locQ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR.isNilpotent
  set Q' : Subgroup R := (locQ.subgroupOf co2P).subgroupOf R
  have hlt : Q' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun r hr => ?_
    have h1 : (⟨r, hr⟩ : R) ∈ Q' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hlt)
  have hconj : ∀ u : R, u ∈ Subgroup.normalizer (Q' : Set R) → ∀ q ∈ locQ,
      ((u : co2P) : Equiv.Perm (Fin 2300)) * q * ((u : co2P) : Equiv.Perm (Fin 2300))⁻¹ ∈
        locQ := by
    intro u hu q hq
    have hqP : q ∈ co2P := locC_le_P (locQ_le_C hq)
    have hqR : (⟨q, hqP⟩ : co2P) ∈ R := hQR (Subgroup.mem_subgroupOf.2 hq)
    have h1 := (Subgroup.mem_normalizer_iff.1 hu ⟨⟨q, hqP⟩, hqR⟩).1
      (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hq))
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 h1)
  refine ⟨y, y.2, mem_locC_of_conj_mem (y : co2P).2 (hconj y hyN) fun q hq => ?_,
    fun h => hyQ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 h))⟩
  have h1 := hconj y⁻¹ (Subgroup.inv_mem _ hyN) q hq
  simpa only [InvMemClass.coe_inv, inv_inv] using h1

private theorem toPerm63_sixAction_mem
    (c : locC) :
    toPerm63 (sixAction c) ∈ Subgroup.closure {π | ∃ i < 2, sixPi i = π} := by
  have h : sixAction c ∈ sixAction.range := ⟨c, rfl⟩
  rw [sixAction_range] at h
  have h2 := Subgroup.mem_map_of_mem toPerm63 h
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  exact ⟨i, hi, (toPerm63_sixAction_cGen hi).symm⟩

theorem eq_locQ_of_invariant
    (R : Subgroup co2P) (hR : IsPGroup 2 R)
    (hKB : K0.subgroupOf co2P ⊔ B1.subgroupOf co2P ≤ Subgroup.normalizer (R : Set co2P))
    (hQR : locQ.subgroupOf co2P ≤ R) : R = locQ.subgroupOf co2P := by
  refine le_antisymm ?_ hQR
  by_contra hne
  obtain ⟨x, hxR, hxC, hxQ⟩ := exists_mem_locC_of_not_le hR hQR hne
  let φ : locC →* Equiv.Perm (Fin 63) := toPerm63.comp sixAction
  let TC : Subgroup locC := R.comap (Subgroup.inclusion locC_le_P)
  let S : Subgroup (Equiv.Perm (Fin 63)) := TC.map φ
  have hS2 : IsPGroup 2 S :=
    (hR.comap_of_injective _ (Subgroup.inclusion_injective locC_le_P)).map φ
  have hSne : S ≠ ⊥ := by
    intro hS
    have hmem : φ ⟨x, hxC⟩ ∈ S := Subgroup.mem_map_of_mem φ (show
      Subgroup.inclusion locC_le_P ⟨x, hxC⟩ ∈ R from hxR)
    rw [hS, Subgroup.mem_bot] at hmem
    have h1 : sixAction ⟨x, hxC⟩ = 1 := toPerm63_injective (hmem.trans (map_one _).symm)
    have h2 : (⟨x, hxC⟩ : locC) ∈ locQ.subgroupOf locC := by
      rw [← sixAction_ker]
      exact MonoidHom.mem_ker.2 h1
    exact hxQ (Subgroup.mem_subgroupOf.1 h2)
  obtain ⟨X, hXS, hX1, hX2, hXc⟩ := exists_central_involution hS2 hSne
  have hnorm : ∀ c : locC, Subgroup.inclusion locC_le_P c ∈ K0.subgroupOf co2P ⊔
      B1.subgroupOf co2P → φ c ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 63))) :=
    fun c hc => Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ
      (Subgroup.le_normalizer_comap (Subgroup.inclusion locC_le_P) (hKB hc)))
  have hg := gens_mem_locC
  have hk1 : k1P ∈ K0 := show k1P ∈ Subgroup.closure {k1P, k2P} from
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hk2 : k2P ∈ K0 := show k2P ∈ Subgroup.closure {k1P, k2P} from
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hd : dP ∈ B1 := show dP ∈ Subgroup.closure {dP, b2P, b3P} from
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h1 : φ ⟨k1P, hg.2.2.2.2.1⟩ ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 63))) :=
    hnorm ⟨k1P, hg.2.2.2.2.1⟩ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hk1))
  have h2 : φ ⟨k2P, hg.2.2.2.2.2⟩ ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 63))) :=
    hnorm ⟨k2P, hg.2.2.2.2.2⟩ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hk2))
  have h3 : φ ⟨dP, hg.1⟩ ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 63))) :=
    hnorm ⟨dP, hg.1⟩ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hd))
  obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hXS
  obtain ⟨w, -, hw⟩ := six_facts ⟨k1P, hg.2.2.2.2.1⟩ ⟨k2P, hg.2.2.2.2.2⟩ ⟨dP, hg.1⟩ rfl rfl rfl
    (φ t) (toPerm63_sixAction_mem t) hX2 hX1
  have hW := wordVal_mem_of (Subgroup.normalizer (S : Set (Equiv.Perm (Fin 63))))
    (g := [φ ⟨k1P, hg.2.2.2.2.1⟩, φ ⟨k2P, hg.2.2.2.2.2⟩, φ ⟨dP, hg.1⟩])
    (by
      intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl
      exacts [h1, h2, h3]) w
  exact hw (hXc _ ((Subgroup.mem_normalizer_iff.1 hW _).1 hXS))

end CFSG.Sporadic.Co2I301
