module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedTensor
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedLemma11
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedLower

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin CFSG.Quasithin.B45Sz
  CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.GF2n.Tim81.Sec2.SzTensor

section Invariants

variable {G : Type} [Group G] {V : Type} [AddCommGroup V]

theorem fixedSub_eq_invariants {k : Type} [Field k] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) :
    fixedSub ρ H = Representation.invariants (ρ.comp H.subtype) := by
  ext v
  simp only [mem_fixedSub, Representation.mem_invariants, MonoidHom.comp_apply,
    Subgroup.coe_subtype]
  exact ⟨fun h s => h s s.2, fun h s hs => h ⟨s, hs⟩⟩

theorem invariants_le_invariants_comp {k : Type} [Field k] [Module k V]
    (ρ : Representation k G V) (S : Subgroup G) :
    Representation.invariants ρ ≤ Representation.invariants (ρ.comp S.subtype) := by
  intro v hv
  rw [Representation.mem_invariants] at hv ⊢
  intro s
  exact hv (s : G)

theorem invariants_quotientToInvariants_eq {k : Type} [Field k] [Module k V]
    (ρ : Representation k G V) (S : Subgroup G) [S.Normal] :
    Representation.invariants (Representation.quotientToInvariants ρ S) =
      (Representation.invariants ρ).comap
        (Representation.invariants (ρ.comp S.subtype)).subtype := by
  ext v
  rw [Submodule.mem_comap]
  constructor
  · intro hv
    rw [Representation.mem_invariants] at hv
    intro g
    have h := hv (QuotientGroup.mk g)
    rw [Representation.ofQuotient_coe_apply] at h
    simpa using congrArg Subtype.val h
  · intro hv
    rw [Representation.mem_invariants]
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [Representation.ofQuotient_coe_apply]
      refine Subtype.ext ?_
      exact (Representation.mem_invariants ρ (v := (v : V))).mp hv g

theorem finrank_invariants_quotientToInvariants {k : Type} [Field k] [Module k V]
    [Module.Finite k V] (ρ : Representation k G V) (S : Subgroup G) [S.Normal] :
    Module.finrank k ↥(Representation.invariants (Representation.quotientToInvariants ρ S)) =
      Module.finrank k ↥(Representation.invariants ρ) := by
  rw [invariants_quotientToInvariants_eq ρ S]
  have hmap : ((Representation.invariants ρ).comap
        (Representation.invariants (ρ.comp S.subtype)).subtype).map
        (Representation.invariants (ρ.comp S.subtype)).subtype =
      Representation.invariants ρ := by
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr (invariants_le_invariants_comp ρ S)
  have hfr : Module.finrank k ↥(((Representation.invariants ρ).comap
        (Representation.invariants (ρ.comp S.subtype)).subtype).map
        (Representation.invariants (ρ.comp S.subtype)).subtype) =
      Module.finrank k ↥((Representation.invariants ρ).comap
        (Representation.invariants (ρ.comp S.subtype)).subtype) :=
    Submodule.finrank_map_subtype_eq _ _
  rw [hmap] at hfr
  exact hfr.symm

end Invariants

section Steinberg

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
variable (k : Type) [Field k] [Algebra K k] [CharP k 2]

theorem finrank_fixedSub_szOmega_le
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Module.finrank k (fixedSub (matRep (szT k hK (szOmega a))) (szZ a K)) ≤ 2 ^ (2 * a + 1) := by
  classical
  haveI hN : ((szZ a K).subgroupOf (szUp a K)).Normal := szZ_normal_in_szUp hK
  let ρΩ : Representation k ↥(szUp a K) ((↥(szOmega a) → Fin 4) → k) :=
    (matRep (szT k hK (szOmega a))).comp (szUp a K).subtype
  have hsub : Representation.invariants ((matRep (szT k hK (szOmega a))).comp (szZ a K).subtype) =
      Representation.invariants (ρΩ.comp ((szZ a K).subgroupOf (szUp a K)).subtype) := by
    ext v
    simp only [Representation.mem_invariants, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_subgroupOf]
    constructor
    · intro h s
      exact h ⟨(s : ↥(szUp a K)), s.2⟩
    · intro h z
      exact h ⟨⟨(z : ↥(suzukiGroup a K)), szZ_le_szUp z.2⟩, z.2⟩
  have hident : Module.finrank k (fixedSub (matRep (szT k hK (szOmega a))) (szZ a K)) =
      Module.finrank k ↥(Representation.invariants
        (ρΩ.comp ((szZ a K).subgroupOf (szUp a K)).subtype)) := by
    rw [fixedSub_eq_invariants, hsub]
  rw [hident]
  have h1 := finrank_le_two_pow_mul_finrank_invariants (m := 2 * a + 1)
    (ρ := Representation.quotientToInvariants ρΩ ((szZ a K).subgroupOf (szUp a K)))
    (szUp_quot_szZ_mul_self hK) (card_szUp_quot_szZ hK)
  rw [finrank_invariants_quotientToInvariants] at h1
  have h2 : Module.finrank k ↥(Representation.invariants ρΩ) = 1 := by
    rw [← fixedSub_eq_invariants]
    rw [(szT_fixed_irreducible k hK (A := szOmega a) le_rfl).1]
    exact finrank_span_singleton (hwS_ne_zero k (szOmega a))
  rw [h2, mul_one] at h1
  exact h1

end Steinberg

section TensorStep

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {k : Type} [Field k] [Algebra K k] [CharP k 2]

theorem extractLM_sum_kronFun {Ω : Finset ℕ} {B : Finset ℕ} (hB : B ⊆ Ω)
    (g : ↥(Ω \ B) → Fin 4) {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι × κ → k) (u : ι → (B → Fin 4) → k) (v : κ → (↥(Ω \ B) → Fin 4) → k) :
    extractLM hB (evalLM g)
        (∑ p : ι × κ, c p • kronFun hB (u p.1) (v p.2)) =
      ∑ i, (∑ j, c (i, j) * v j g) • u i := by
  rw [map_sum]
  have h1 : ∀ p : ι × κ,
      extractLM hB (evalLM g) (c p • kronFun hB (u p.1) (v p.2)) =
        (c p * v p.2 g) • u p.1 := by
    intro p
    rw [map_smul, extractLM_kronFun, evalLM_apply, smul_smul]
  simp only [h1]
  rw [Fintype.sum_prod_type]
  dsimp only
  exact Finset.sum_congr rfl (fun i _ => (Finset.sum_smul).symm)

theorem linearIndependent_kronFun {Ω : Finset ℕ} {B : Finset ℕ} (hB : B ⊆ Ω)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : ι → (B → Fin 4) → k) (v : κ → (↥(Ω \ B) → Fin 4) → k)
    (hu : LinearIndependent k u) (hv : LinearIndependent k v) :
    LinearIndependent k (fun p : ι × κ => kronFun hB (u p.1) (v p.2)) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro c c' h
  rintro ⟨i, j⟩
  have hcoef : ∀ (g : ↥(Ω \ B) → Fin 4) (i' : ι),
      (∑ j', c (i', j') * v j' g) = ∑ j', c' (i', j') * v j' g := by
    intro g i'
    refine LinearIndependent.eq_coords_of_eq
      (f := fun i' => ∑ j', c (i', j') * v j' g)
      (g := fun i' => ∑ j', c' (i', j') * v j' g) hu ?_ i'
    have h1 := congrArg (extractLM hB (evalLM g)) h
    rw [extractLM_sum_kronFun hB g c u v, extractLM_sum_kronFun hB g c' u v] at h1
    exact h1
  have hfun : (∑ j', c (i, j') • v j') = ∑ j', c' (i, j') • v j' := by
    funext g
    rw [Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hcoef g i
  exact LinearIndependent.eq_coords_of_eq hv hfun j

theorem linearIndependent_kronFun_subtype
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {Ω : Finset ℕ} {B : Finset ℕ} (hB : B ⊆ Ω)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : ι → (B → Fin 4) → k) (v : κ → (↥(Ω \ B) → Fin 4) → k)
    (hu : LinearIndependent k u) (hv : LinearIndependent k v)
    (hmem : ∀ (i : ι) (j : κ), kronFun hB (u i) (v j) ∈
      fixedSub (matRep (szT k hK Ω)) (szZ a K)) :
    LinearIndependent k (fun p : ι × κ =>
      (⟨kronFun hB (u p.1) (v p.2), hmem p.1 p.2⟩ :
        ↥(fixedSub (matRep (szT k hK Ω)) (szZ a K)))) := by
  have hamb := linearIndependent_kronFun hB u v hu hv
  rw [Fintype.linearIndependent_iffₛ] at hamb ⊢
  intro c c' hcc'
  refine hamb c c' ?_
  have h2 := congrArg (fun w : ↥(fixedSub (matRep (szT k hK Ω)) (szZ a K)) =>
    (w : (Ω → Fin 4) → k)) hcc'
  simpa using h2

theorem finrank_fixed_mul_le
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {Ω : Finset ℕ} (B : Finset ℕ) (hB : B ⊆ Ω) :
    Module.finrank k (fixedSub (matRep (szT k hK B)) (szZ a K)) *
      Module.finrank k (fixedSub (matRep (szT k hK (Ω \ B))) (szZ a K)) ≤
    Module.finrank k (fixedSub (matRep (szT k hK Ω)) (szZ a K)) := by
  classical
  let bB := Module.finBasis k ↥(fixedSub (matRep (szT k hK B)) (szZ a K))
  let bC := Module.finBasis k ↥(fixedSub (matRep (szT k hK (Ω \ B))) (szZ a K))
  have hli := linearIndependent_kronFun_subtype (k := k) (K := K) (a := a) hK (Ω := Ω) (B := B) hB
    (fun i => (bB i : (B → Fin 4) → k))
    (fun j => (bC j : (↥(Ω \ B) → Fin 4) → k))
    (bB.linearIndependent.map' (fixedSub (matRep (szT k hK B)) (szZ a K)).subtype
      (Submodule.ker_subtype _))
    (bC.linearIndependent.map' (fixedSub (matRep (szT k hK (Ω \ B))) (szZ a K)).subtype
      (Submodule.ker_subtype _))
    (fun i j => kronFun_mem_fixedSub hK B hB (bB i).2 (bC j).2)
  have hcard := hli.fintype_card_le_finrank
  simpa using hcard

end TensorStep

section Equality

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
variable (k : Type) [Field k] [Algebra K k] [CharP k 2]

theorem finrank_fixedSub_szZ
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {B : Finset ℕ} (hB : B ⊆ szOmega a) :
    Module.finrank k (fixedSub (matRep (szT k hK B)) (szZ a K)) = 2 ^ B.card := by
  refine le_antisymm ?_ (two_pow_card_le_finrank_fixed_szZ k hK hB)
  have hBcard : B.card ≤ 2 * a + 1 := by
    rw [← card_szOmega]
    exact Finset.card_le_card hB
  have hBC : B.card + (szOmega a \ B).card = 2 * a + 1 := by
    rw [Finset.card_sdiff_of_subset hB, card_szOmega]
    omega
  have hle : Module.finrank k (fixedSub (matRep (szT k hK B)) (szZ a K)) *
      2 ^ (szOmega a \ B).card ≤ 2 ^ (2 * a + 1) := by
    calc Module.finrank k (fixedSub (matRep (szT k hK B)) (szZ a K)) *
          2 ^ (szOmega a \ B).card
        ≤ Module.finrank k (fixedSub (matRep (szT k hK B)) (szZ a K)) *
          Module.finrank k (fixedSub (matRep (szT k hK (szOmega a \ B))) (szZ a K)) :=
          Nat.mul_le_mul_left _ (two_pow_card_le_finrank_fixed_szZ k hK Finset.sdiff_subset)
      _ ≤ Module.finrank k (fixedSub (matRep (szT k hK (szOmega a))) (szZ a K)) :=
          finrank_fixed_mul_le hK B hB
      _ ≤ 2 ^ (2 * a + 1) := finrank_fixedSub_szOmega_le k hK
  rw [show 2 ^ (2 * a + 1) = 2 ^ B.card * 2 ^ (szOmega a \ B).card by
    rw [← hBC, pow_add]] at hle
  exact Nat.le_of_mul_le_mul_right hle (by positivity)

end Equality

end CFSG.RankThree.GF2n.Tim81.Sec2
