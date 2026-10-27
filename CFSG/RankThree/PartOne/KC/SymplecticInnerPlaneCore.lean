module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneDefs
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicOrbits
public import CFSG.RankThree.PartOne.KC.OrthogonalProjectiveCore
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Model

variable {r : ℕ} {K : Type} [Field K]

theorem spProj_facts {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) :
    IsSimpleGroup (StatedProj (StatedSp r K)) ∧
      Subgroup.center (StatedProj (StatedSp r K)) = ⊥ ∧
      Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K))) := by
  have hq2 : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
      (Nat.card K = 2 ∧ 3 ≤ r) := by
    rw [hK]
    rcases Nat.lt_or_ge (ℓ ^ f) 4 with h4 | h4
    · rcases (show ℓ ^ f = 2 ∨ ℓ ^ f = 3 by omega) with h | h
      · have : r ≠ 2 := fun hr2 => hrq ⟨hr2, h⟩
        exact Or.inr (Or.inr ⟨h, by omega⟩)
      · exact Or.inr (Or.inl ⟨h, hr⟩)
    · exact Or.inl (Or.inr h4)
  have hsimple := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r
    (by omega) hq
  obtain ⟨-, -, a, b, hab⟩ := CFSG.LieType.Universal.Symplectic.isQuasisimple r K (by omega) hq
  let e := CFSG.LieType.Universal.Symplectic.centerQuotientEquiv r K
  have hcenter : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSp r K))) with h | h
    · exact h
    · exfalso
      have hv : e b ∈ Subgroup.center (StatedProj (StatedSp r K)) := h ▸ Subgroup.mem_top _
      exact hab (e.injective (by rw [map_mul, map_mul]; exact (Subgroup.mem_center_iff.mp hv
        (e a))))
  exact ⟨hsimple, hcenter, KCOrthogonal.conj_injective_of_center_eq_bot hcenter⟩

end Model

section Listed

variable {r : ℕ} {K : Type} [Field K]

theorem not_le_ker_proj_of_isQuasisimple {P : Subgroup (StatedSp r K)}
    (hq : CFSG.IsQuasisimple ↥P) : ¬ P ≤ (proj r K).ker := by
  intro hle
  have hker : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  refine Subtype.ext ?_
  have := Subgroup.mem_center_iff.mp (hker (hle a.2)) (b : StatedSp r K)
  exact this.symm

theorem normal_subgroupOf_map {S T : Type*} [Group S] [Group T] (ρ : S →* T) {M P : Subgroup S}
    (hnorm : ∀ m ∈ M, ∀ g ∈ P, m * g * m⁻¹ ∈ P) :
    ((P.map ρ).subgroupOf (M.map ρ)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : T) ∈ P.map ρ := hn
  obtain ⟨j, hj, hjn⟩ := hn'
  obtain ⟨m, hm, hmg⟩ := g.2
  show (g : T) * (n : T) * (g : T)⁻¹ ∈ P.map ρ
  refine ⟨m * j * m⁻¹, hnorm m hm j hj, ?_⟩
  rw [map_mul, map_mul, map_inv, hjn, hmg]

variable [Finite K]

theorem spListed_facts {p : ℕ} (hp : p.Prime)
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))))
    {a : StatedProj (StatedSp r K)} {x : StatedSp r K}
    (hcent : Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))) =
      (Subgroup.centralizer ({x} : Set (StatedSp r K))).map (proj r K))
    {P : Subgroup (StatedSp r K)} (hP : P ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)))
    (hnorm : ∀ m ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ g ∈ P, m * g * m⁻¹ ∈ P)
    (hq : CFSG.IsQuasisimple ↥P) :
    P.map (proj r K) ≤ Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))) ∧
      CFSG.IsQuasisimple ↥(P.map (proj r K)) ∧
      ((P.map (proj r K)).subgroupOf
        (Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))))).Normal ∧
      CFSG.IsComponent (((P.map (proj r K)).map (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K)))).subgroupOf
          (B ⊓ Subgroup.centralizer ({MulAut.conj a} :
            Set (MulAut (StatedProj (StatedSp r K)))))) ∧
      ∀ s ∈ spLocalCore p B a, ∀ j ∈ P.map (proj r K),
        s * MulAut.conj j = MulAut.conj j * s := by
  have : Finite (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp r K
  have hle : P.map (proj r K) ≤ Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))) := by
    rw [hcent]
    exact Subgroup.map_mono hP
  have hqm : CFSG.IsQuasisimple ↥(P.map (proj r K)) :=
    CFSG.LocalCores.isQuasisimple_map hq (proj r K) (not_le_ker_proj_of_isQuasisimple hq)
  have hN : ((P.map (proj r K)).subgroupOf
      (Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K))))).Normal := by
    rw [hcent]
    exact normal_subgroupOf_map (proj r K) hnorm
  refine ⟨hle, hqm, hN, KCOrthogonal.isComponent_conj_subgroupOf hB a hinj hle hN hqm, ?_⟩
  have hcore := KCOrthogonal.commutator_core_map_conj_eq_bot hp hB a hinj hle hN hqm
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcore
  intro s hs j hj
  have := Subgroup.mem_centralizer_iff.mp (hcen hs) (MulAut.conj j) (Subgroup.mem_map_of_mem _ hj)
  exact this.symm

end Listed

section Pull

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spPull (x : StatedSp r K) (h : K[X]) : Subgroup (StatedSp r K) :=
  (specialBlock (spForm r K) (spLin r K x) h).comap (spLin r K)

theorem spBlockImage_eq (x : StatedSp r K) (h : K[X]) :
    spBlockImage x h = (spPull x h).map (proj r K) := rfl

theorem spLin_mem_sesq_of_mem_specialBlock {x : StatedSp r K} {h : K[X]}
    {g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)}
    (hg : g ∈ specialBlock (spForm r K) (spLin r K x) h) : g ∈ sesqUnitaryGroup (spForm r K) :=
  (mem_unitaryCentralizer.mp (specialBlock_le_unitaryCentralizer hg)).1

theorem spPull_le_centralizer (x : StatedSp r K) (h : K[X]) :
    spPull x h ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)) := by
  intro g hg
  have h1 : spLin r K g ∈ unitaryCentralizer (spForm r K) (spLin r K x) :=
    specialBlock_le_unitaryCentralizer hg
  rw [unitaryCentralizer_spForm_eq_map] at h1
  obtain ⟨g₀, hg₀, hgg⟩ := h1
  rwa [← spLin_injective hgg]

theorem spPull_normalized (x : StatedSp r K) (h : K[X]) :
    ∀ m ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ g ∈ spPull x h,
      m * g * m⁻¹ ∈ spPull x h := by
  intro m hm g hg
  have hm' : spLin r K m ∈ unitaryCentralizer (spForm r K) (spLin r K x) := by
    rw [unitaryCentralizer_spForm_eq_map]
    exact Subgroup.mem_map_of_mem _ hm
  have := conj_mem_specialBlock hm' hg
  change spLin r K (m * g * m⁻¹) ∈ specialBlock (spForm r K) (spLin r K x) h
  rwa [map_mul, map_mul, map_inv]

theorem spPull_isQuasisimple {x : StatedSp r K} {h : primaryFactors (spEnd x)}
    (facts : SpBlockFacts (spForm r K) (spLin r K x) h)
    (hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])) :
    CFSG.IsQuasisimple ↥(spPull x (h : K[X])) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (comapSpLinEquiv _ (fun _ hg => spLin_mem_sesq_of_mem_specialBlock hg)).symm
    (facts.quasisimple hm)

end Pull

end CFSG.RankThree.PartOne
