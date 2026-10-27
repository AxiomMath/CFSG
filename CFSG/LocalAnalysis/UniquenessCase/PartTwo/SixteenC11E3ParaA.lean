module

public import CFSG.Quasithin.H13.A6S1372L76N3b
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4AThetaLin
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Quasithin.H13.A6.A6L76Of CFSG.Quasithin.H13.A6.A6L76N3
open CFSG.Quasithin.Stellmacher.L3YC

noncomputable section

@[expose] def s1611e3_fixSub {K : Type} [Field K]
    (P : Subgroup ↥(StatedSL 3 K)) : Subgroup (Multiplicative (Fin 3 → K)) where
  carrier := {m | ∀ γ ∈ P, natHom γ m = m}
  one_mem' := by intro γ _; rw [map_one]
  mul_mem' := by intro a b ha hb γ hγ; rw [map_mul, ha γ hγ, hb γ hγ]
  inv_mem' := by intro a ha γ hγ; rw [map_inv, ha γ hγ]

@[expose] def s1611e3_stabSL {K : Type} [Field K]
    (m : Multiplicative (Fin 3 → K)) : Subgroup ↥(StatedSL 3 K) where
  carrier := {γ | natHom γ m = m}
  one_mem' := by
    change natHom (1 : ↥(StatedSL 3 K)) m = m
    rw [map_one, MulAut.one_apply]
  mul_mem' := by
    intro a b ha hb
    change natHom a m = m at ha
    change natHom b m = m at hb
    change natHom (a * b) m = m
    rw [map_mul, MulAut.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change natHom a m = m at ha
    apply (natHom a).injective
    change natHom a (natHom a⁻¹ m) = natHom a m
    rw [map_inv, MulAut.apply_inv_self, ha]

private theorem card_comap_top_subtype {G : Type} [Group G] (H : Subgroup G) :
    Nat.card ↥(H.comap (⊤ : Subgroup G).subtype) = Nat.card ↥H := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun γ : ↥(H.comap (⊤ : Subgroup G).subtype) =>
      (⟨(γ.1 : G), by simpa using Subgroup.mem_comap.mp γ.2⟩ : ↥H)) ⟨?_, ?_⟩)
  · intro a b hab
    have h : (a.1.1 : G) = b.1.1 := congrArg (fun x : ↥H => (x.1 : G)) hab
    exact Subtype.ext (Subtype.ext h)
  · intro h
    refine ⟨⟨⟨(h.1 : G), Subgroup.mem_top _⟩, Subgroup.mem_comap.mpr h.2⟩, rfl⟩

theorem s1611e3_fixSub_card {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {P : Subgroup ↥(StatedSL 3 K)} (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) :
    Nat.card ↥(s1611e3_fixSub P) = 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hKf2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  letI : MulAction ↥P (Multiplicative (Fin 3 → K)) :=
    { smul := fun p m => natHom (p : ↥(StatedSL 3 K)) m
      one_smul := by
        intro m
        show natHom ((1 : ↥P) : ↥(StatedSL 3 K)) m = m
        rw [Subgroup.coe_one, map_one, MulAut.one_apply]
      mul_smul := by
        intro a b m
        show natHom (((a * b : ↥P) : ↥(StatedSL 3 K))) m =
          natHom (a : ↥(StatedSL 3 K)) (natHom (b : ↥(StatedSL 3 K)) m)
        rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply] }
  have huniq : ∀ m ∈ s1611e3_fixSub P, m ≠ 1 →
      ∀ m' ∈ s1611e3_fixSub P, m' ≠ 1 → m = m' := by
    intro m hm hm1 m' hm' hm1'
    exact eq_of_fix_sylow (F := K) hK hP hodd hm1 hm1' hm hm'
  have hfixP : ∀ m, m ∈ s1611e3_fixSub P ↔
      m ∈ MulAction.fixedPoints ↥P (Multiplicative (Fin 3 → K)) := by
    intro m
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hm p; exact hm (p : ↥(StatedSL 3 K)) p.2
    · intro hm γ hγ; exact hm ⟨γ, hγ⟩
  have hcard8 : Nat.card (Multiplicative (Fin 3 → K)) = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
      Fintype.card_fin, hKf2]
    norm_num
  obtain ⟨m₀, hm₀fix, hm₀ne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (Multiplicative (Fin 3 → K))
      (show 2 ∣ Nat.card (Multiplicative (Fin 3 → K)) by rw [hcard8]; norm_num)
      (show (1 : Multiplicative (Fin 3 → K)) ∈ MulAction.fixedPoints ↥P _ by
        rw [MulAction.mem_fixedPoints]
        intro p
        change natHom (p : ↥(StatedSL 3 K)) 1 = 1
        rw [map_one])
  have hm₀ : m₀ ∈ s1611e3_fixSub P := (hfixP m₀).2 hm₀fix
  have hset : (s1611e3_fixSub P : Set (Multiplicative (Fin 3 → K))) = {1, m₀} := by
    ext m
    simp only [s1611e3_fixSub, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hm
      rcases eq_or_ne m 1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (huniq m hm h1 m₀ hm₀ (Ne.symm hm₀ne))
    · intro hm
      rcases hm with h1 | h1
      · rw [h1]; exact (s1611e3_fixSub P).one_mem
      · rw [h1]; exact hm₀
  change Nat.card (s1611e3_fixSub P : Set (Multiplicative (Fin 3 → K))) = 2
  rw [Nat.card_coe_set_eq, hset, Set.ncard_pair hm₀ne]

theorem s1611e3_stabSL_card {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {m : Multiplicative (Fin 3 → K)} (hm : m ≠ 1) :
    Nat.card ↥(s1611e3_stabSL m) = 24 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hKf2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hSLtop : StatedSL 3 K = ⊤ := CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK 3
  have hstab : s1611e3_stabSL m =
      (stabAct (Multiplicative.toAdd m)).comap (StatedSL 3 K).subtype := by
    ext γ
    rw [Subgroup.mem_comap, mem_stabAct]
    change natHom γ m = m ↔
      glAct (γ : GL (Fin 3) K) (Multiplicative.toAdd m) = Multiplicative.toAdd m
    constructor
    · intro h; exact congrArg Multiplicative.toAdd h
    · intro h; exact Multiplicative.toAdd.injective h
  have hw : Multiplicative.toAdd m ≠ 0 := by
    intro h0
    exact hm (Multiplicative.toAdd.injective (by simpa using h0))
  rw [hstab, hSLtop, card_comap_top_subtype]
  exact card_stabAct hKf2 hw

end
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
