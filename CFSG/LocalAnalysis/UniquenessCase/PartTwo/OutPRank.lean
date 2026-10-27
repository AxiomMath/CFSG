module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centOverO2_eq_ker_map {X M : Subgroup G} (hMN : M ≤ normalizer (X : Set G)) :
    F08.CentOverO2 M X =
      (MonoidHom.ker ((rhoL X).comp (Subgroup.inclusion hMN))).map M.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxM, hxc⟩ := mem_centOverO2_iff.mp hx
    refine Subgroup.mem_map.2 ⟨⟨x, hxM⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    ext z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    show rhoL X ⟨x, hMN hxM⟩ (QuotientGroup.mk y) = QuotientGroup.mk y
    exact (rhoL_fix_iff X ⟨x, hMN hxM⟩ y).2 (hxc (y : G) y.2)
  · rintro hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hx
    rw [mem_centOverO2_iff]
    refine ⟨m.2, ?_⟩
    intro l hl
    rw [MonoidHom.mem_ker] at hm
    have h1 : rhoL X ⟨(m : G), hMN m.2⟩ (QuotientGroup.mk (⟨l, hl⟩ : ↥X)) =
        QuotientGroup.mk (⟨l, hl⟩ : ↥X) := by
      have h2 : rhoL X (Subgroup.inclusion hMN m) (QuotientGroup.mk (⟨l, hl⟩ : ↥X)) =
          QuotientGroup.mk (⟨l, hl⟩ : ↥X) := by
        simpa using congrArg (fun f : MulAut (Bar2 X) =>
          f (QuotientGroup.mk (⟨l, hl⟩ : ↥X))) hm
      exact h2
    exact (rhoL_fix_iff X ⟨(m : G), hMN m.2⟩ ⟨l, hl⟩).1 h1

omit [Finite G] in
theorem map_rhoL_le_inner_of_isCyclic_outer {X M : Subgroup G}
    (hMN : M ≤ normalizer (X : Set G)) (hOut : IsCyclic (Outer (Bar2 X)))
    {p : ℕ} (hp : p.Prime) (hOp : UC22.F10.OpRes p M = M)
    {A : Subgroup G} (hAM : A ≤ M) (hAel : IsElemAbelian p A) :
    (A.subgroupOf M).map ((rhoL X).comp (Subgroup.inclusion hMN)) ≤ inner (Bar2 X) := by
  let ρ : ↥M →* MulAut (Bar2 X) := (rhoL X).comp (Subgroup.inclusion hMN)
  have hgen : Subgroup.closure {y | y ∈ (M.subgroupOf M).map ρ ∧ ¬ p ∣ orderOf y} =
      (M.subgroupOf M).map ρ :=
    closure_pPrime_map ρ (M.subgroupOf M)
      (closure_pPrime_subgroupOf (le_refl M) (p := p) hOp)
  intro y hy
  obtain ⟨a, ha, rfl⟩ := hy
  have haA : (a : G) ∈ A := ha
  have hap : ρ a ^ (p ^ 1) = 1 := by
    rw [← map_pow]
    have h1 : a ^ (p ^ 1) = 1 := by
      apply Subtype.ext
      simpa using hAel.2 (a : G) haA
    rw [h1, map_one]
  exact mem_inner_of_pPow (inner (Bar2 X)) (inner (Bar2 X)) ((M.subgroupOf M).map ρ)
    hOut (fun φ hφ => (inner (Bar2 X)).pow_mem hφ 3) hp (Or.inr le_rfl) hgen
    (Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 (hAM haA))) hap

theorem dvd_card_centOverO2_of_pRank_lt {X M : Subgroup G}
    (hMN : M ≤ normalizer (X : Set G))
    (hZ : Subgroup.center (Bar2 X) = ⊥)
    (hOut : IsCyclic (Outer (Bar2 X)))
    {p : ℕ} (hp : p.Prime) (hOp : UC22.F10.OpRes p M = M)
    (hrank : Open.pRank p (⊤ : Subgroup (Bar2 X)) < Open.pRank p M) :
    p ∣ Nat.card (F08.CentOverO2 M X) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let ρ : ↥M →* MulAut (Bar2 X) := (rhoL X).comp (Subgroup.inclusion hMN)
  obtain ⟨A₀, hA₀M, hA₀el, hA₀card⟩ :=
    exists_elemAbelian_card_of_le_pRank (M := M) hp (k := Open.pRank p M) le_rfl
  let A₀M : Subgroup ↥M := A₀.subgroupOf M
  have hA₀Mcard : Nat.card A₀M = p ^ Open.pRank p M := by
    rw [← hA₀card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv
  have hA₀Mel : IsElemAbelian p A₀M := hA₀el.subgroupOf M
  have hAinner : A₀M.map ρ ≤ inner (Bar2 X) :=
    map_rhoL_le_inner_of_isCyclic_outer hMN hOut hp hOp hA₀M hA₀el
  have hKne : A₀M ⊓ ρ.ker ≠ ⊥ := by
    intro hbot
    have hdisj : Disjoint A₀M ρ.ker := by
      rw [disjoint_iff]
      exact hbot
    have hAcard : Nat.card (A₀M.map ρ) = p ^ Open.pRank p M := by
      rw [UC6S846.card_map_of_disjoint_ker ρ A₀M hdisj, hA₀Mcard]
    have hAel : IsElemAbelian p (A₀M.map ρ) := hA₀Mel.map ρ
    have hconj : Function.Injective (MulAut.conj : Bar2 X →* MulAut (Bar2 X)) :=
      CFSG.HardMathSupport.Lang.Triality.conj_injective_of_center_eq_bot hZ
    let A' : Subgroup (Bar2 X) := (A₀M.map ρ).comap (MulAut.conj : Bar2 X →* MulAut (Bar2 X))
    have hA'el : IsElemAbelian p A' :=
      CFSG.LieType.SeitzGeneration.isElemAbelian_comap_conj hconj hAel
    have hA'map : A'.map (MulAut.conj : Bar2 X →* MulAut (Bar2 X)) = A₀M.map ρ :=
      Subgroup.map_comap_eq_self hAinner
    have hA'card : Nat.card A' = p ^ Open.pRank p M := by
      calc Nat.card A' = Nat.card (A'.map (MulAut.conj : Bar2 X →* MulAut (Bar2 X))) :=
            (Subgroup.card_map_of_injective hconj).symm
        _ = Nat.card (A₀M.map ρ) := by rw [hA'map]
        _ = p ^ Open.pRank p M := hAcard
    have hle : Open.pRank p M ≤ Open.pRank p (⊤ : Subgroup (Bar2 X)) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_top hA'el hA'card
    exact (not_le.mpr hrank) hle
  have hKp : IsPGroup p ↥(A₀M ⊓ ρ.ker) := hA₀Mel.isPGroup.to_inf_left
  have hKdvd : p ∣ Nat.card ↥(A₀M ⊓ ρ.ker) := by
    rcases hKp.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hKne
    · exact h1
  have hKle : (A₀M ⊓ ρ.ker).map M.subtype ≤ F08.CentOverO2 M X := by
    rw [centOverO2_eq_ker_map hMN]
    exact Subgroup.map_mono inf_le_right
  have hKmapdvd : p ∣ Nat.card ((A₀M ⊓ ρ.ker).map M.subtype) := by
    rwa [Subgroup.card_map_of_injective M.subtype_injective]
  exact hKmapdvd.trans (Subgroup.card_dvd_of_le hKle)

theorem exists_isPGroup_le_centralizer_centOverO2 {X M R : Subgroup G}
    (hXM : X ≤ M) (hMN : M ≤ normalizer (X : Set G))
    (hZ : Subgroup.center (Bar2 X) = ⊥)
    (hOut : IsCyclic (Outer (Bar2 X)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hOp : UC22.F10.OpRes p M = M)
    (hrank : Open.pRank p (⊤ : Subgroup (Bar2 X)) < Open.pRank p M)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hRX : R ≤ X) (hRp : IsPGroup r R) :
    ∃ S : Subgroup G, S ≤ F08.CentOverO2 M X ∧ IsPGroup p S ∧ S ≠ ⊥ ∧
      S ≤ Subgroup.centralizer (R : Set G) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup G := F08.CentOverO2 M X with hZdef
  have hpZ : p ∣ Nat.card Z :=
    dvd_card_centOverO2_of_pRank_lt hMN hZ hOut hp hOp hrank
  have hMZ : M ≤ normalizer (Z : Set G) := by
    rw [hZdef, centOverO2_eq_ker_map hMN]
    exact CFSG.GroupTheory.FT63ChII.le_normalizer_map_subtype
      (R := M) ((rhoL X).comp (Subgroup.inclusion hMN)).ker
  have hRM : R ≤ M := hRX.trans hXM
  have hRZ : R ≤ normalizer (Z : Set G) := hRM.trans hMZ
  have hRO : R ≤ normalizer (pCoreOf 2 X : Set G) :=
    hRX.trans (le_normalizer.trans (normalizer_le_normalizer_pCoreOf X))
  have hRN : R ≤ normalizer ((Z ⊓ pCoreOf 2 X : Subgroup G) : Set G) :=
    (le_inf hRZ hRO).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcomm : ⁅Z, R⁆ ≤ Z ⊓ pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro z hz r hr'
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : r * z⁻¹ * r⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hRZ hr') z⁻¹).mp (Z.inv_mem hz)
      simpa [mul_assoc] using Z.mul_mem hz h1
    · exact (mem_centOverO2_iff.mp hz).2 r (hRX hr')
  have hO2r : ¬ r ∣ Nat.card (pCoreOf 2 X) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (isPGroup_pCoreOf X) hr hr2
  have hO2p : ¬ p ∣ Nat.card (pCoreOf 2 X) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (isPGroup_pCoreOf X) hp hp2
  have hNr : ¬ r ∣ Nat.card ↥(Z ⊓ pCoreOf 2 X) := fun hd =>
    hO2r (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hNp : ¬ p ∣ Nat.card ↥(Z ⊓ pCoreOf 2 X) := fun hd =>
    hO2p (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  obtain ⟨S, hSyl, hSc⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := r) (q := p) (X := Z) (N := Z ⊓ pCoreOf 2 X) (R := R)
      inf_le_left hRZ hRN hRp hNr hcomm hNp
  refine ⟨S, hSyl.le, hSyl.isPGroup, ?_, hSc⟩
  · intro hbot
    have hcard := hSyl.card_eq
    have hpos : 0 < (Nat.card Z).factorization p :=
      hp.factorization_pos_of_dvd Nat.card_pos.ne' hpZ
    have hle : p ≤ Nat.card S := by
      rw [hcard]
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (Nat.card Z).factorization p := Nat.pow_le_pow_right hp.pos hpos
    rw [hbot] at hle
    rw [Subgroup.card_bot] at hle
    have hpge : 2 ≤ p := hp.two_le
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
