module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.LinearAlgebra.SteinbergBQAutomizerPermutation
public import CFSG.RankThree.PartOne.S12.Sec159Fin
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.Sec159Defs
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] noncomputable def fullMatrixPreimage {d : ℕ} {K : Type} [Field K]
    (U : Subgroup (GL (Fin d) K)) {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj U) (A : Subgroup (MulAut L')) :
    Subgroup (Subgroup.normalizer (U : Set (GL (Fin d) K))) :=
  (TypeA.inducedSub ψ A).comap (TableB.projConj U)

@[expose] def coverPullback {d : ℕ} {K : Type} [Field K]
    (U : Subgroup (GL (Fin d) K)) {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj U) (A : Subgroup (MulAut L')) : Subgroup (L' × ↥U) :=
  CFSG.LieType.Steinberg.pullback ψ (LargeEvenProjMk U) ⊓
    ((Subgroup.normalizer (A : Set (MulAut L'))).comap
      (MulAut.conj : L' →* MulAut L')).prod ⊤

theorem mem_coverPullback {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')} {p : L' × ↥U} :
    p ∈ coverPullback U ψ A ↔
      ψ p.1 = LargeEvenProjMk U p.2 ∧
        MulAut.conj p.1 ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  simp [coverPullback, CFSG.LieType.Steinberg.mem_pullback, Subgroup.mem_prod]

theorem TableB.projConj_of_eq {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {u : ↥U} {l : L'}
    (h : LargeEvenProjMk U u = ψ l) (l₀ : L') :
    TableB.projConj U ⟨(u : GL (Fin d) K), Subgroup.le_normalizer u.2⟩ (ψ l₀) =
      ψ (l * l₀ * l⁻¹) := by
  obtain ⟨u₀, hψ⟩ := QuotientGroup.mk_surjective (ψ l₀)
  rw [← hψ, TableB.projConj_mk]
  let c : ↥U := u * u₀ * u⁻¹
  have hval : (U.normalizerMonoidHom
      ⟨(u : GL (Fin d) K), Subgroup.le_normalizer u.2⟩) u₀ = c := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  rw [hval]
  change (LargeEvenProjMk U) (u * u₀ * u⁻¹) = ψ (l * l₀ * l⁻¹)
  rw [map_mul, map_mul, map_inv, h]
  rw [show (LargeEvenProjMk U) u₀ = ψ l₀ from hψ]
  rw [map_mul, map_mul, map_inv]

theorem TableB.projConj_normalizes_inducedSub {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')} {u : ↥U} {l : L'}
    (hl : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hπ : LargeEvenProjMk U u = ψ l) :
    ∀ φ ∈ TypeA.inducedSub ψ A,
      TableB.projConj U ⟨(u : GL (Fin d) K), Subgroup.le_normalizer u.2⟩ * φ *
        (TableB.projConj U ⟨(u : GL (Fin d) K), Subgroup.le_normalizer u.2⟩)⁻¹ ∈
          TypeA.inducedSub ψ A := by
  intro φ hφ
  obtain ⟨a, ha, hφa⟩ := TypeA.mem_inducedSub.mp hφ
  have hconjA : MulAut.conj l * a * (MulAut.conj l)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hl a).mp ha
  refine TypeA.mem_inducedSub.mpr ⟨MulAut.conj l * a * (MulAut.conj l)⁻¹, hconjA, ?_⟩
  intro l₀
  set ρ : MulAut (LargeEvenProj U) :=
    TableB.projConj U ⟨(u : GL (Fin d) K), Subgroup.le_normalizer u.2⟩ with hρ
  have hρ_mul : ρ (ψ (l⁻¹ * l₀ * l)) = ψ l₀ := by
    rw [hρ, TableB.projConj_of_eq hπ]
    congr 1
    group
  have hρ_inv : ρ⁻¹ (ψ l₀) = ψ (l⁻¹ * l₀ * l) := by
    rw [← hρ_mul]
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  calc
    (ρ * φ * ρ⁻¹) (ψ l₀) = ρ (φ (ρ⁻¹ (ψ l₀))) := by rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = ρ (φ (ψ (l⁻¹ * l₀ * l))) := by rw [hρ_inv]
    _ = ρ (ψ (a (l⁻¹ * l₀ * l))) := by rw [hφa]
    _ = ψ (l * (a (l⁻¹ * l₀ * l)) * l⁻¹) := by rw [hρ, TableB.projConj_of_eq hπ]
    _ = ψ ((MulAut.conj l * a * (MulAut.conj l)⁻¹) l₀) := by
      congr 1

@[expose] noncomputable def fullMatrixPreimageGL {d : ℕ} {K : Type} [Field K]
    (U : Subgroup (GL (Fin d) K)) {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj U) (A : Subgroup (MulAut L')) : Subgroup (GL (Fin d) K) :=
  (fullMatrixPreimage U ψ A).map
    (Subgroup.subtype (Subgroup.normalizer (U : Set (GL (Fin d) K))))

theorem conj_mem_fullMatrixPreimageGL {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')} {u : ↥U} {l : L'}
    (hl : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hπ : LargeEvenProjMk U u = ψ l) :
    ∀ b ∈ fullMatrixPreimageGL U ψ A,
      (u : GL (Fin d) K) * b * (u : GL (Fin d) K)⁻¹ ∈ fullMatrixPreimageGL U ψ A := by
  intro b hb
  obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
  let uN : Subgroup.normalizer (U : Set (GL (Fin d) K)) :=
    ⟨(u : GL (Fin d) K), Subgroup.le_normalizer u.2⟩
  let c : Subgroup.normalizer (U : Set (GL (Fin d) K)) := uN * b₀ * uN⁻¹
  have hbB : TableB.projConj U b₀ ∈ TypeA.inducedSub ψ A := by
    simpa [fullMatrixPreimage] using hb₀
  have hcB : c ∈ fullMatrixPreimage U ψ A := by
    rw [fullMatrixPreimage, Subgroup.mem_comap]
    change TableB.projConj U (uN * b₀ * uN⁻¹) ∈ TypeA.inducedSub ψ A
    rw [map_mul, map_mul, map_inv]
    exact TableB.projConj_normalizes_inducedSub hl hπ _ hbB
  refine Subgroup.mem_map.mpr ⟨c, hcB, ?_⟩
  change (c : GL (Fin d) K) = (u : GL (Fin d) K) * (b₀ : GL (Fin d) K) * (u : GL (Fin d) K)⁻¹
  simp [c, uN]

@[expose] def coverPullbackToNormalizer {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')} :
    coverPullback U ψ A →* Subgroup.normalizer (A : Set (MulAut L')) where
  toFun p := ⟨MulAut.conj (p : L' × ↥U).1, (mem_coverPullback.mp p.2).2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)

theorem mem_normalizer_fullMatrixPreimageGL {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')} {u : ↥U} {l : L'}
    (hl : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hπ : LargeEvenProjMk U u = ψ l) :
    (u : GL (Fin d) K) ∈
      Subgroup.normalizer (fullMatrixPreimageGL U ψ A : Set (GL (Fin d) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact conj_mem_fullMatrixPreimageGL hl hπ b hb
  · intro hb
    have hπinv : LargeEvenProjMk U u⁻¹ = ψ l⁻¹ := by
      rw [map_inv, map_inv, hπ]
    have hlinv : MulAut.conj l⁻¹ ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
      simpa only [map_inv] using Subgroup.inv_mem _ hl
    have h := conj_mem_fullMatrixPreimageGL hlinv hπinv
      ((u : GL (Fin d) K) * b * (u : GL (Fin d) K)⁻¹) hb
    have h' : (u : GL (Fin d) K)⁻¹ * ((u : GL (Fin d) K) * b * (u : GL (Fin d) K)⁻¹) *
        ((u : GL (Fin d) K)⁻¹)⁻¹ ∈ fullMatrixPreimageGL U ψ A := by
      simpa only [Subgroup.coe_inv, inv_inv] using h
    have heq : (u : GL (Fin d) K)⁻¹ * ((u : GL (Fin d) K) * b * (u : GL (Fin d) K)⁻¹) *
        ((u : GL (Fin d) K)⁻¹)⁻¹ = b := by group
    rwa [heq] at h'

@[expose] noncomputable def coverPullbackToGLNormalizer {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')} :
    coverPullback U ψ A →*
      Subgroup.normalizer (fullMatrixPreimageGL U ψ A : Set (GL (Fin d) K)) where
  toFun p :=
    ⟨((p : L' × ↥U).2 : GL (Fin d) K),
      mem_normalizer_fullMatrixPreimageGL (mem_coverPullback.mp p.2).2
        (mem_coverPullback.mp p.2).1.symm⟩
  map_one' := Subtype.ext rfl
  map_mul' := fun _ _ => Subtype.ext rfl


@[expose] noncomputable def coverPullbackAutomizer {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')} :
    coverPullback U ψ A →* MulAut A :=
  (Subgroup.normalizerMonoidHom A).comp
    (coverPullbackToNormalizer (ψ := ψ) (A := A))

theorem range_coverPullbackAutomizer {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')} :
    (coverPullbackAutomizer (U := U) (ψ := ψ) (A := A)).range =
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
  rw [ggAutomizer_eq]
  ext φ
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨MulAut.conj (p : L' × ↥U).1, ⟨(p : L' × ↥U).1, rfl⟩,
      (mem_coverPullback.mp p.2).2, fun a => ?_⟩
    change ((Subgroup.normalizerMonoidHom A
      ⟨MulAut.conj (p : L' × ↥U).1, (mem_coverPullback.mp p.2).2⟩) a : MulAut L') =
        MulAut.conj (p : L' × ↥U).1 * (a : MulAut L') * (MulAut.conj (p : L' × ↥U).1)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  · rintro ⟨g, ⟨l, rfl⟩, hgN, hgφ⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (ψ l)
    have hp : (l, u) ∈ coverPullback U ψ A := by
      rw [mem_coverPullback]
      exact ⟨hu.symm, hgN⟩
    refine ⟨⟨(l, u), hp⟩, ?_⟩
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change ((Subgroup.normalizerMonoidHom A ⟨MulAut.conj l, hgN⟩) a : MulAut L') =
      (φ a : MulAut L')
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (hgφ a).symm

theorem coverPullbackAutomizer_eq_one_of_centralizer {d : ℕ} {K : Type} [Field K]
    {U : Subgroup (GL (Fin d) K)} {L' : Type} [Group L']
    {ψ : L' →* LargeEvenProj U} {A : Subgroup (MulAut L')}
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hMB : ∀ a ∈ A, ∃ M ∈ fullMatrixPreimage U ψ A,
      ∀ l : L', TableB.projConj U M (ψ l) = ψ (a l))
    {p : coverPullback U ψ A}
    (hp : ((p : L' × ↥U).2 : GL (Fin d) K) ∈
      Subgroup.centralizer (fullMatrixPreimageGL U ψ A : Set (GL (Fin d) K))) :
    coverPullbackAutomizer p = 1 := by
  let l : L' := (p : L' × ↥U).1
  let u : ↥U := (p : L' × ↥U).2
  have hπ : LargeEvenProjMk U u = ψ l := (mem_coverPullback.mp p.2).1.symm
  have hl : MulAut.conj l ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    (mem_coverPullback.mp p.2).2
  let uN : Subgroup.normalizer (U : Set (GL (Fin d) K)) :=
    ⟨(u : GL (Fin d) K), Subgroup.le_normalizer u.2⟩
  let ρu : MulAut (LargeEvenProj U) := TableB.projConj U uN
  have hρu_apply : ∀ x : L', ρu (ψ x) = ψ ((MulAut.conj l) x) := by
    intro x
    change TableB.projConj U uN (ψ x) = ψ ((MulAut.conj l) x)
    rw [TableB.projConj_of_eq hπ]
    rfl
  apply MulEquiv.ext
  intro a₀
  apply Subtype.ext
  apply TypeA.mulAut_eq_of_forall ψ hker hperf
  intro x
  obtain ⟨M, hMB, hMφ⟩ := hMB a₀ a₀.2
  let ρM : MulAut (LargeEvenProj U) := TableB.projConj U M
  have hMgl_mem : ((M : Subgroup.normalizer (U : Set (GL (Fin d) K))) : GL (Fin d) K) ∈
      fullMatrixPreimageGL U ψ A :=
    Subgroup.mem_map.mpr ⟨M, hMB, rfl⟩
  have hcommGL : (u : GL (Fin d) K) *
      ((M : Subgroup.normalizer (U : Set (GL (Fin d) K))) : GL (Fin d) K) =
      ((M : Subgroup.normalizer (U : Set (GL (Fin d) K))) : GL (Fin d) K) *
        (u : GL (Fin d) K) := by
    have h := (Subgroup.mem_centralizer_iff.mp hp)
      ((M : Subgroup.normalizer (U : Set (GL (Fin d) K))) : GL (Fin d) K) hMgl_mem
    simpa using h.symm
  have hcommN : uN * M = M * uN := Subtype.ext (by simpa [uN] using hcommGL)
  have hρcomm : ρu * ρM = ρM * ρu := by
    rw [← map_mul, ← map_mul, hcommN]
  have hρconj : ρu * ρM * ρu⁻¹ = ρM := by
    rw [hρcomm]
    group
  have hρu_inv : ρu⁻¹ (ψ x) = ψ ((MulAut.conj l)⁻¹ x) := by
    have h1 : ρu (ψ ((MulAut.conj l)⁻¹ x)) = ψ x := by
      rw [hρu_apply]
      congr 1
      simp only [MulAut.conj_apply, MulAut.conj_inv_apply]
      group
    rw [← h1, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hFval : (((coverPullbackAutomizer p) a₀ : A) : MulAut L') =
      MulAut.conj l * (a₀ : MulAut L') * (MulAut.conj l)⁻¹ := by
    change (((Subgroup.normalizerMonoidHom A
      ⟨MulAut.conj l, hl⟩) a₀ : A) : MulAut L') =
        MulAut.conj l * (a₀ : MulAut L') * (MulAut.conj l)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  change ψ ((((coverPullbackAutomizer p) a₀ : A) : MulAut L') x) =
    ψ (((a₀ : A) : MulAut L') x)
  rw [hFval]
  calc
    ψ ((MulAut.conj l * (a₀ : MulAut L') * (MulAut.conj l)⁻¹) x)
        = ψ ((MulAut.conj l) ((a₀ : MulAut L') ((MulAut.conj l)⁻¹ x))) := by
          rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = ρu (ψ ((a₀ : MulAut L') ((MulAut.conj l)⁻¹ x))) := by rw [hρu_apply]
    _ = ρu (ρM (ψ ((MulAut.conj l)⁻¹ x))) := by rw [hMφ]
    _ = ρu (ρM (ρu⁻¹ (ψ x))) := by rw [hρu_inv]
    _ = (ρu * ρM * ρu⁻¹) (ψ x) := by rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = ρM (ψ x) := by rw [hρconj]
    _ = ψ (((a₀ : A) : MulAut L') x) := hMφ x

theorem odd_card_fullMatrixPreimage_of_elemAbelian {d : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (U : Subgroup (GL (Fin d) K)) {L' : Type} [Group L']
    [Finite L'] (ψ : L' →* LargeEvenProj U) (hψ : Function.Surjective ψ)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ M : Subgroup.normalizer (U : Set (GL (Fin d) K)),
      ∀ l : L', TableB.projConj U M (ψ l) = ψ (a l))
    (hscal : (TableB.projConj U).ker ≤
      (LargeEvenScalars (Fin d) K).subgroupOf
        (Subgroup.normalizer (U : Set (GL (Fin d) K)))) :
    Odd (Nat.card (fullMatrixPreimage U ψ A)) := by
  classical
  let X : Subgroup (MulAut (LargeEvenProj U)) := TypeA.inducedSub ψ A
  let N : Subgroup (GL (Fin d) K) := Subgroup.normalizer (U : Set (GL (Fin d) K))
  have hXle : X ≤ (TableB.projConj U).range := by
    intro φ hφ
    obtain ⟨a, ha, hφa⟩ := TypeA.mem_inducedSub.mp hφ
    obtain ⟨M, hMφ⟩ := hAI a ha
    exact ⟨M, (TypeA.induced_unique ψ hψ (a := (a : MulAut L')) hφa hMφ).symm⟩
  have hXP : IsPGroup 3 X :=
    CFSG.Open.IsElemAbelian.isPGroup (TypeA.isElemAbelian_inducedSub hψ hA)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXP
  have hXodd : Odd (Nat.card X) := by
    rw [hk]
    exact Odd.pow (n := k) (show Odd (3 : ℕ) by norm_num)
  have hEven : Even (Nat.card K) := by
    let hF : Fintype K := Fintype.ofFinite K
    have h2 : Fintype.card K % 2 = 0 :=
      @FiniteField.even_card_of_char_two K _ hF (by rw [ringChar.eq K 2])
    rw [show Nat.card K = Fintype.card K from @Nat.card_eq_fintype_card K hF, Nat.even_iff]
    exact h2
  have hKunits : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact Nat.Even.sub_odd Nat.card_pos hEven (by decide)
  have hScalLe : LargeEvenScalars (Fin d) K ≤ N := fun z hz =>
    TableB.scalar_mem_normalizer U hz
  have hScalSubOdd : Odd (Nat.card ((LargeEvenScalars (Fin d) K).subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hScalLe).toEquiv]
    exact Odd.of_dvd_nat hKunits (by
      rw [largeEvenScalars_def]
      exact Subgroup.card_range_dvd (Matrix.GeneralLinearGroup.scalar (Fin d) : Kˣ →* GL (Fin d) K))
  let ρB : fullMatrixPreimage U ψ A →* MulAut (LargeEvenProj U) :=
    (TableB.projConj U).comp (fullMatrixPreimage U ψ A).subtype
  have hρB_range : ρB.range = X := by
    have h1 : ρB.range = (TableB.projConj U).range ⊓ X := by
      rw [show ρB = (TableB.projConj U).comp (fullMatrixPreimage U ψ A).subtype from rfl,
        MonoidHom.range_comp, Subgroup.range_subtype]
      rw [fullMatrixPreimage, Subgroup.map_comap_eq]
    rw [h1, inf_eq_right.mpr hXle]
  have hkerLe : ρB.ker.map (fullMatrixPreimage U ψ A).subtype ≤
      (LargeEvenScalars (Fin d) K).subgroupOf N := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    exact hscal (by simpa [ρB] using hb)
  have hkerOdd : Odd (Nat.card ρB.ker) := by
    have hcard : Nat.card (ρB.ker.map (fullMatrixPreimage U ψ A).subtype) =
        Nat.card ρB.ker :=
      Subgroup.card_map_of_injective (fullMatrixPreimage U ψ A).subtype_injective
    have hdvd : Nat.card (ρB.ker.map (fullMatrixPreimage U ψ A).subtype) ∣
        Nat.card ((LargeEvenScalars (Fin d) K).subgroupOf N) :=
      Subgroup.card_dvd_of_le hkerLe
    rw [hcard] at hdvd
    exact Odd.of_dvd_nat hScalSubOdd hdvd
  have hcard := Subgroup.card_ker_mul_card_range ρB
  rw [hρB_range] at hcard
  rw [← hcard]
  exact hkerOdd.mul hXodd

theorem card_ggAutomizer_dvd_factorial {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    [CharP K 2] (U : Subgroup (GL (Fin d) K)) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj U)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ M : Subgroup.normalizer (U : Set (GL (Fin d) K)),
      ∀ l : L', TableB.projConj U M (ψ l) = ψ (a l))
    (hBcomm : ∀ b ∈ fullMatrixPreimage U ψ A,
      ∀ c ∈ fullMatrixPreimage U ψ A, b * c = c * b)
    (hBodd : Odd (Nat.card (fullMatrixPreimage U ψ A))) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ Nat.factorial d := by
  classical
  let Bmat : Subgroup (GL (Fin d) K) := fullMatrixPreimageGL U ψ A
  let Nmat : Subgroup (GL (Fin d) K) := Subgroup.normalizer (Bmat : Set (GL (Fin d) K))
  have hBmat_comm : ∀ a ∈ Bmat, ∀ b ∈ Bmat, a * b = b * a := by
    rintro a ⟨a₀, ha₀, rfl⟩ b ⟨b₀, hb₀, rfl⟩
    exact congrArg (Subgroup.subtype (Subgroup.normalizer (U : Set (GL (Fin d) K))))
      (hBcomm a₀ ha₀ b₀ hb₀)
  have hBmat_odd : Odd (Nat.card Bmat) := by
    change Odd (Nat.card (fullMatrixPreimageGL U ψ A))
    rw [fullMatrixPreimageGL, Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (Subgroup.normalizer (U : Set (GL (Fin d) K))))]
    exact hBodd
  let eGL : GL (Fin d) K ≃* LinearMap.GeneralLinearGroup K (Fin d → K) :=
    Matrix.GeneralLinearGroup.toLin
  let Blin : Subgroup (LinearMap.GeneralLinearGroup K (Fin d → K)) :=
    Bmat.map eGL.toMonoidHom
  letI : Finite (GL (Fin d) K) := by
    unfold Matrix.GeneralLinearGroup
    infer_instance
  letI : Finite ↥Bmat := Subtype.finite
  letI : Finite ↥Blin :=
    Finite.of_equiv ↥Bmat
      (Subgroup.equivMapOfInjective Bmat eGL.toMonoidHom eGL.injective).toEquiv
  have hBlin_comm : ∀ a ∈ Blin, ∀ b ∈ Blin, a * b = b * a := by
    rintro a ⟨a₀, ha₀, rfl⟩ b ⟨b₀, hb₀, rfl⟩
    simpa only [map_mul] using congrArg eGL.toMonoidHom (hBmat_comm a₀ ha₀ b₀ hb₀)
  have hBlin_odd : Odd (Nat.card Blin) := by
    change Odd (Nat.card (Bmat.map eGL.toMonoidHom))
    exact hBmat_odd.of_dvd_nat (Subgroup.card_map_dvd Bmat eGL.toMonoidHom)
  have hBlin_cop : Nat.Coprime (Nat.card Blin) 2 :=
    Nat.coprime_two_right.mpr hBlin_odd
  obtain ⟨r, hr1, hrle, femb, hfemb, -⟩ :=
    CFSG.LinearAlgebra.abelian_coprime_matrix_automizer_permutation_embedding
      (k := K) (V := Fin d → K) (p := 2)
      (by simpa [Module.finrank_fintype_fun_eq_card] using hd) Blin hBlin_comm hBlin_cop
  let Nlin : Subgroup (LinearMap.GeneralLinearGroup K (Fin d → K)) :=
    Subgroup.normalizer (Blin : Set (LinearMap.GeneralLinearGroup K (Fin d → K)))
  let Clin : Subgroup Nlin :=
    (Subgroup.centralizer (Blin : Set (LinearMap.GeneralLinearGroup K (Fin d → K)))).subgroupOf
      Nlin
  let NmatToNlin : Nmat →* Nlin :=
    { toFun := fun n => ⟨eGL (n : GL (Fin d) K), by
        change eGL (n : GL (Fin d) K) ∈
          Subgroup.normalizer ((Bmat.map eGL.toMonoidHom :
            Subgroup (LinearMap.GeneralLinearGroup K (Fin d → K))) :
              Set (LinearMap.GeneralLinearGroup K (Fin d → K)))
        rw [← Subgroup.map_equiv_normalizer_eq Bmat eGL]
        exact Subgroup.mem_map.mpr ⟨n, n.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one eGL)
      map_mul' := fun a b => Subtype.ext (map_mul eGL (a : GL (Fin d) K) (b : GL (Fin d) K)) }
  let pNlin : coverPullback U ψ A →* Nlin :=
    NmatToNlin.comp (coverPullbackToGLNormalizer (ψ := ψ) (A := A))
  let f : coverPullback U ψ A →* Equiv.Perm (Fin r) :=
    femb.comp ((QuotientGroup.mk' Clin).comp pNlin)
  have hMB : ∀ a ∈ A, ∃ M ∈ fullMatrixPreimage U ψ A,
      ∀ l : L', TableB.projConj U M (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨M, hMφ⟩ := hAI a ha
    exact ⟨M, Subgroup.mem_comap.mpr (TypeA.mem_inducedSub.mpr ⟨a, ha, hMφ⟩), hMφ⟩
  have hker : f.ker ≤ (coverPullbackAutomizer (U := U) (ψ := ψ) (A := A)).ker := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    have hq : (QuotientGroup.mk (pNlin p) : Nlin ⧸ Clin) = 1 := by
      apply hfemb
      simpa [f] using hp
    have hpC : pNlin p ∈ Clin :=
      (QuotientGroup.eq_one_iff (N := Clin) (pNlin p)).mp hq
    have hpcentL : (pNlin p : LinearMap.GeneralLinearGroup K (Fin d → K)) ∈
        Subgroup.centralizer
          (Blin : Set (LinearMap.GeneralLinearGroup K (Fin d → K))) :=
      Subgroup.mem_subgroupOf.mp hpC
    have hpcentMat : ((p : L' × ↥U).2 : GL (Fin d) K) ∈
        Subgroup.centralizer (Bmat : Set (GL (Fin d) K)) := by
      have hmem : eGL ((p : L' × ↥U).2 : GL (Fin d) K) ∈
          (Subgroup.centralizer (Bmat : Set (GL (Fin d) K))).map eGL.toMonoidHom := by
        rw [CFSG.RankThree.Asc83Table.map_equiv_centralizer_eq eGL Bmat]
        change (pNlin p : LinearMap.GeneralLinearGroup K (Fin d → K)) ∈
          Subgroup.centralizer (Blin : Set (LinearMap.GeneralLinearGroup K (Fin d → K)))
        exact hpcentL
      obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
      have hxval : x = ((p : L' × ↥U).2 : GL (Fin d) K) := eGL.injective hxeq
      simpa [hxval] using hx
    exact coverPullbackAutomizer_eq_one_of_centralizer hker hperf hMB hpcentMat
  have hdiv : Nat.card (coverPullbackAutomizer (U := U) (ψ := ψ) (A := A)).range ∣
      Nat.card f.range :=
    CFSG.RankThree.PartOne.Sec159Cfg.card_range_dvd_of_ker_le f
      (coverPullbackAutomizer (U := U) (ψ := ψ) (A := A)) hker
  have hf_fact : Nat.card f.range ∣ Nat.factorial r := by
    have h := Subgroup.card_subgroup_dvd_card f.range
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using h
  have hrle' : r ≤ d := by
    simpa [Module.finrank_fintype_fun_eq_card] using hrle
  have hfact : Nat.factorial r ∣ Nat.factorial d := Nat.factorial_dvd_factorial hrle'
  have haut : Nat.card (coverPullbackAutomizer (U := U) (ψ := ψ) (A := A)).range ∣
      Nat.factorial d := hdiv.trans (hf_fact.trans hfact)
  rwa [range_coverPullbackAutomizer] at haut

theorem card_ggAutomizer_dvd_factorial_of_induced {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K]
    [Finite K] [CharP K 2] (U : Subgroup (GL (Fin d) K)) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj U)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} {I : Set (MulAut (LargeEvenProj U))}
    (hI : I ⊆ Set.range (TableB.projConj U))
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (hBcomm : ∀ b ∈ fullMatrixPreimage U ψ A,
      ∀ c ∈ fullMatrixPreimage U ψ A, b * c = c * b)
    (hBodd : Odd (Nat.card (fullMatrixPreimage U ψ A))) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ Nat.factorial d := by
  refine card_ggAutomizer_dvd_factorial hd U ψ hker hperf ?_ hBcomm hBodd
  intro a ha
  obtain ⟨φ, hφI, hφ⟩ := hAI a ha
  obtain ⟨M, hM⟩ := hI hφI
  exact ⟨M, by simpa [hM] using hφ⟩

theorem card_ggAutomizer_dvd_factorial_of_matConjImage {d : ℕ} (hd : 1 ≤ d) {K : Type}
    [Field K] [Finite K] [CharP K 2] (U : Subgroup (GL (Fin d) K)) {L' : Type} [Group L']
    [Finite L'] (ψ : L' →* LargeEvenProj U)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} {S : Set (GL (Fin d) K)}
    (hS : S ⊆ Subgroup.normalizer (U : Set (GL (Fin d) K)))
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk U) S,
      ∀ l : L', φ (ψ l) = ψ (a l))
    (hBcomm : ∀ b ∈ fullMatrixPreimage U ψ A,
      ∀ c ∈ fullMatrixPreimage U ψ A, b * c = c * b)
    (hBodd : Odd (Nat.card (fullMatrixPreimage U ψ A))) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ Nat.factorial d := by
  refine card_ggAutomizer_dvd_factorial_of_induced hd U ψ hker hperf ?_ hAI hBcomm hBodd
  intro φ hφ
  obtain ⟨M, hM, hMeq⟩ := TableB.exists_eq_projConj hS hφ
  exact ⟨⟨M, hS hM⟩, hMeq.symm⟩

theorem card_ggAutomizer_dvd_factorial_of_induced_elemAbelian {d : ℕ} (hd : 1 ≤ d) {K : Type}
    [Field K] [Finite K] [CharP K 2] (U : Subgroup (GL (Fin d) K)) {L' : Type} [Group L']
    [Finite L'] (ψ : L' →* LargeEvenProj U) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} {I : Set (MulAut (LargeEvenProj U))}
    (hA : IsElemAbelian 3 A)
    (hscal : (TableB.projConj U).ker ≤
      (LargeEvenScalars (Fin d) K).subgroupOf
        (Subgroup.normalizer (U : Set (GL (Fin d) K))))
    (hI : I ⊆ Set.range (TableB.projConj U))
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (hBcomm : ∀ b ∈ fullMatrixPreimage U ψ A,
      ∀ c ∈ fullMatrixPreimage U ψ A, b * c = c * b) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ Nat.factorial d := by
  refine card_ggAutomizer_dvd_factorial_of_induced hd U ψ hker hperf hI hAI hBcomm ?_
  refine odd_card_fullMatrixPreimage_of_elemAbelian U ψ hψ hA ?_ hscal
  intro a ha
  obtain ⟨φ, hφI, hφ⟩ := hAI a ha
  obtain ⟨M, hM⟩ := hI hφI
  exact ⟨M, by simpa [hM] using hφ⟩

theorem card_ggAutomizer_dvd_factorial_of_matConjImage_elemAbelian {d : ℕ} (hd : 1 ≤ d)
    {K : Type} [Field K] [Finite K] [CharP K 2] (U : Subgroup (GL (Fin d) K)) {L' : Type}
    [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj U) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} {S : Set (GL (Fin d) K)} (hA : IsElemAbelian 3 A)
    (hscal : (TableB.projConj U).ker ≤
      (LargeEvenScalars (Fin d) K).subgroupOf
        (Subgroup.normalizer (U : Set (GL (Fin d) K))))
    (hS : S ⊆ Subgroup.normalizer (U : Set (GL (Fin d) K)))
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk U) S,
      ∀ l : L', φ (ψ l) = ψ (a l))
    (hBcomm : ∀ b ∈ fullMatrixPreimage U ψ A,
      ∀ c ∈ fullMatrixPreimage U ψ A, b * c = c * b) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ Nat.factorial d := by
  refine card_ggAutomizer_dvd_factorial_of_matConjImage hd U ψ hker hperf hS hAI hBcomm ?_
  apply odd_card_fullMatrixPreimage_of_elemAbelian U ψ hψ hA _ hscal
  intro a ha
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  obtain ⟨M, hM, hMeq⟩ := TableB.exists_eq_projConj hS hφ
  exact ⟨⟨M, hS hM⟩, by simpa [hMeq] using hφa⟩

end CFSG.StandardType
