module

public import CFSG.RankThree.PartOne.KE8F.E8Frame
public import CFSG.RankThree.PartOne.KE8F.E8Kernel
public import CFSG.RankThree.PartOne.KE8F.PairA1
public import CFSG.RankThree.PartOne.KE8F.FamBruhat

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def cls (α : Fin Tag.E8.rank → ℤ) : Set (Fin Tag.E8.rank → ℤ) :=
  {α, -α} ∪ {e8P4V *ᵥ α, -(e8P4V *ᵥ α)}

theorem mem_cls_iff {α γ : Fin Tag.E8.rank → ℤ} :
    γ ∈ cls α ↔ γ = α ∨ γ = -α ∨ γ = e8P4V *ᵥ α ∨ γ = -(e8P4V *ᵥ α) := by
  simp only [cls, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem e8P4V_mulVec_mulVec (α : Fin Tag.E8.rank → ℤ) : e8P4V *ᵥ (e8P4V *ᵥ α) = -α := by
  rw [Matrix.mulVec_mulVec, e8P4V_sq, Matrix.neg_mulVec, Matrix.one_mulVec]

section Orth

theorem e8P4_orth_list : ∀ l ∈ Tag.E8.artifactRoots,
    toVec Tag.E8.rank l ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ
      toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList l)) = 0 := by
  decide +kernel

theorem e8P4_orth {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) :
    α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ (e8P4V *ᵥ α)) = 0 := by
  have h := e8P4_orth_list _ (isRoot_iff_mem_artifactRoots.1 hα)
  rw [toVec_ofFn', toVec_V_ofFn] at h
  exact h

end Orth

section Frobenius

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]

theorem baseChangeGL_frob_fixed {τ : Tag} (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) w) =
      baseChangeGL (algebraMap K L) w := by
  have : Fintype K := Fintype.ofFinite K
  have hcomp : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun c => by
    change Fr (algebraMap K L c) = algebraMap K L c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have e : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) w) =
      baseChangeGL Fr (baseChangeGL (algebraMap K L) w) := Units.ext rfl
  rw [e, baseChangeGL_baseChangeGL, hcomp]

end Frobenius

section FrameLevel

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] {ℓ f p : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

@[expose] def psiC (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K) :
    adjointGroup .E8 K →* ModGL .E8 L :=
  (MulAut.conj F.g0⁻¹).toMonoidHom.comp ((adjEmb .E8 K L).comp (MulAut.conj c).toMonoidHom)

theorem psiC_apply (F : E8P4Frame0 K L ℓ f) (c d : adjointGroup .E8 K) :
    psiC F c d = F.g0⁻¹ * adjEmb .E8 K L (c * d * c⁻¹) * F.g0 := by
  simp [psiC, MulAut.conj_apply]

theorem psiC_injective (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K) :
    Function.Injective (psiC F c) := by
  intro a b h
  rw [psiC_apply, psiC_apply] at h
  have h1 := mul_left_cancel (mul_right_cancel h)
  have h2 := adjEmb_injective h1
  have := congrArg (fun z => c⁻¹ * z * c) h2
  simpa [mul_assoc] using this

theorem psiC_mem_adjoint (F : E8P4Frame0 K L ℓ f) (c d : adjointGroup .E8 K) :
    psiC F c d ∈ adjointGroup .E8 L := by
  rw [psiC_apply]
  exact mul_mem (mul_mem (inv_mem F.hg0C) (adjEmb_mem _)) F.hg0C

theorem psiC_fixed (F : E8P4Frame0 K L ℓ f) (hK : Nat.card K = ℓ ^ f)
    (c d : adjointGroup .E8 K) :
    F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (psiC F c d) * F.n⁻¹ =
      psiC F c d := by
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]
    exact iterateFrobenius_def ℓ f x
  have hfix := baseChangeGL_frob_fixed (τ := .E8) (iterateFrobenius L ℓ f) hFr
    ((c * d * c⁻¹ : adjointGroup .E8 K) : ModGL .E8 K)
  rw [psiC_apply, map_mul, map_mul, map_inv, F.hg0, adjEmb_apply, hfix]
  group

theorem e8P4_weyl_class (F : E8P4Frame0 K L ℓ f) {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) :
    IsRoot .E8 (e8P4V *ᵥ α) ∧
      weylQuotientHom .E8 L ⟨F.n, F.hnm⟩ • α = e8P4V *ᵥ α ∧
      weylQuotientHom .E8 L ⟨F.n, F.hnm⟩ • (e8P4V *ᵥ α) = -α := by
  refine ⟨?_, ?_, ?_⟩
  · have := IsRoot.smul hα ((coxeterSystem .E8).wordProd e8P4WW)
    rwa [e8P4_weylImage] at this
  · rw [F.hnW]
    exact e8P4_weylImage α
  · rw [F.hnW, e8P4_weylImage, e8P4V_mulVec_mulVec]

theorem e8P4_pair_family [IsAlgClosed L] (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f)
    {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) :
    ∃ P : Unit → Subgroup (ModGL .E8 L),
      IsSigmaFamily F.n (iterateFrobenius L ℓ f) (cls α) P := by
  obtain ⟨hv, hw₁, hw₂⟩ := e8P4_weyl_class F hα
  exact pair_A1_family hf F.hnm hα hv hw₁ hw₂ (e8P4_orth hα)

theorem exists_pair_family_C [IsAlgClosed L] (F : E8P4Frame0 K L ℓ f)
    (hf : 1 ≤ f) (c : adjointGroup .E8 K)
    {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) {Y : Subgroup (adjointGroup .E8 K)}
    (hYQ : ∀ y ∈ Y, psiC F c y ∈
      Subgroup.centralizer (rootSpan .E8 L (cls α) : Set (ModGL .E8 L))) :
    ∃ P : Unit → Subgroup (ModGL .E8 L),
      IsSigmaFamily F.n (iterateFrobenius L ℓ f) (cls α) P ∧
        ∀ u ∈ P (), ∃ d ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)),
          psiC F c d = u := by
  classical
  obtain ⟨P, hP⟩ := e8P4_pair_family F hf hα
  refine ⟨P, hP, fun u hu => ?_⟩
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, -, -⟩ := hP
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom (iterateFrobenius L ℓ f)) with hΦ
  set P' : Subgroup (ModGL .E8 L) := (P ()).map (MulAut.conj F.g0).toMonoidHom with hP'
  have hP'adj : P' ≤ adjointGroup .E8 L := by
    rintro _ ⟨v, hv, rfl⟩
    exact mul_mem (mul_mem F.hg0C (hPadj () hv)) (inv_mem F.hg0C)
  have hP'fix : ∀ w ∈ P', Φ w = w := by
    rintro _ ⟨v, hv, rfl⟩
    have hvR : F.n * Φ v * F.n⁻¹ = v := hPR () hv
    change Φ (F.g0 * v * F.g0⁻¹) = F.g0 * v * F.g0⁻¹
    rw [map_mul, map_mul, map_inv, F.hg0]
    calc F.g0 * F.n * Φ v * (F.g0 * F.n)⁻¹ = F.g0 * (F.n * Φ v * F.n⁻¹) * F.g0⁻¹ := by group
      _ = F.g0 * v * F.g0⁻¹ := by rw [hvR]
  have hPperf : ⁅P (), P ()⁆ = P () := Subgroup.isPerfect_iff.1 (hPq ()).1
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [hP', ← Subgroup.map_commutator, hPperf]
  have hP'fin : Finite P' := by
    have := hPfin ()
    exact Finite.of_surjective ((MulAut.conj F.g0).toMonoidHom.subgroupMap (P ()))
      ((MulAut.conj F.g0).toMonoidHom.subgroupMap_surjective (P ()))
  have hmem : F.g0 * u * F.g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hu
  obtain ⟨y', hy'⟩ := F.hperf P' hP'fin hP'adj hP'fix hP'perf hmem
  refine ⟨c⁻¹ * y' * c, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hu1 : u * psiC F c y = psiC F c y * u :=
      Subgroup.mem_centralizer_iff.1 (hYQ y hy) u (hPQ () hu)
    have hι : adjEmb .E8 K L (y' * (c * y * c⁻¹)) = adjEmb .E8 K L ((c * y * c⁻¹) * y') := by
      have e : adjEmb .E8 K L (c * y * c⁻¹) = F.g0 * psiC F c y * F.g0⁻¹ := by
        rw [psiC_apply]
        group
      rw [map_mul (adjEmb .E8 K L) y' (c * y * c⁻¹), map_mul (adjEmb .E8 K L) (c * y * c⁻¹) y', hy', e]
      calc F.g0 * u * F.g0⁻¹ * (F.g0 * psiC F c y * F.g0⁻¹)
          = F.g0 * (u * psiC F c y) * F.g0⁻¹ := by group
        _ = F.g0 * (psiC F c y * u) * F.g0⁻¹ := by rw [hu1]
        _ = F.g0 * psiC F c y * F.g0⁻¹ * (F.g0 * u * F.g0⁻¹) := by group
    have hcomm' : y' * (c * y * c⁻¹) = (c * y * c⁻¹) * y' := adjEmb_injective hι
    calc y * (c⁻¹ * y' * c) = c⁻¹ * ((c * y * c⁻¹) * y') * c := by group
      _ = c⁻¹ * (y' * (c * y * c⁻¹)) * c := by rw [hcomm']
      _ = c⁻¹ * y' * c * y := by group
  · rw [psiC_apply]
    rw [show c * (c⁻¹ * y' * c) * c⁻¹ = y' by group, hy']
    group

end FrameLevel

section Base

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

omit [Algebra K L] [IsAlgClosed L] [CharP L ℓ] in
theorem not_dvd_char (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hpf : p ∣ Nat.card K * Nat.card K + 1) : ¬ ℓ ∣ p := by
  intro h
  have hℓ : ℓ.Prime := Fact.out
  have hpl : ℓ = p := ((Nat.dvd_prime hp).1 h).resolve_left hℓ.one_lt.ne'
  have hq : p ∣ Nat.card K := by
    rw [hK, ← hpl]
    exact dvd_pow_self ℓ (by omega)
  have h1 : p ∣ Nat.card K * Nat.card K := Dvd.dvd.mul_right hq _
  have := (Nat.dvd_add_right h1).1 hpf
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

@[expose] def tupleGroup (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K)
    (Y : Subgroup (adjointGroup .E8 K)) : Subgroup (Fin Tag.E8.rank → Lˣ) :=
  (Y.map (psiC F c)).comap (rootDiagUnitHom .E8 L)

theorem mem_tupleGroup {F : E8P4Frame0 K L ℓ f} {c : adjointGroup .E8 K}
    {Y : Subgroup (adjointGroup .E8 K)} {b : Fin Tag.E8.rank → Lˣ} :
    b ∈ tupleGroup F c Y ↔ rootDiagUnit .E8 b ∈ Y.map (psiC F c) := Iff.rfl

theorem tupleGroup_le_T0tors (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K)
    {Y : Subgroup (adjointGroup .E8 K)}
    (hYT : ∀ y ∈ Y, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hYp : ∀ y ∈ Y, y ^ p = 1) :
    tupleGroup F c Y ≤ T0tors (iterateFrobenius L ℓ f) p := by
  intro b hb
  obtain ⟨y, hy, hyb⟩ := hb
  have hT := hYT y hy
  rw [F.hT] at hT
  obtain ⟨b', hb', hbb'⟩ := hT
  have hbb : b' = b := rootDiagUnit_injective (hbb'.trans hyb)
  rw [hbb] at hb'
  refine Subgroup.mem_inf.2 ⟨hb', fun i => ?_⟩
  have h1 : rootDiagUnit .E8 b ^ p = 1 := by
    have hyb' : psiC F c y = rootDiagUnit .E8 b := hyb
    rw [← hyb', ← map_pow, hYp y hy, map_one]
  have h2 : b ^ p = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← rootDiagUnit_pow, h1, rootDiagUnit_one]
  exact congrFun h2 i

theorem card_tupleGroup (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K)
    {Y : Subgroup (adjointGroup .E8 K)}
    (hYT : ∀ y ∈ Y, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Nat.card (tupleGroup F c Y) = Nat.card Y := by
  have hinj : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hle : Y.map (psiC F c) ≤ (rootDiagUnitHom .E8 L).range := by
    rintro _ ⟨y, hy, rfl⟩
    have hT := hYT y hy
    rw [F.hT] at hT
    obtain ⟨b, -, hb⟩ := hT
    exact ⟨b, hb⟩
  have hmap : (tupleGroup F c Y).map (rootDiagUnitHom .E8 L) = Y.map (psiC F c) := by
    rw [tupleGroup, Subgroup.map_comap_eq, inf_of_le_right hle]
  rw [← Subgroup.card_map_of_injective hinj, hmap,
    Subgroup.card_map_of_injective (psiC_injective F c)]

end Base

section BaseMain

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_tuple_of_mem (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K)
    {Y : Subgroup (adjointGroup .E8 K)}
    (hYT : ∀ y ∈ Y, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {y : adjointGroup .E8 K} (hy : y ∈ Y) :
    ∃ b ∈ tupleGroup F c Y, rootDiagUnit .E8 b = psiC F c y := by
  have hT := hYT y hy
  rw [F.hT] at hT
  obtain ⟨b, -, hb⟩ := hT
  exact ⟨b, ⟨y, hy, hb.symm⟩, hb⟩

theorem famKernel_neg' {F : Set (Fin Tag.E8.rank → Lˣ)} {α : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ famKernel F) : -α ∈ famKernel F :=
  ⟨IsRoot.neg hα.1, fun a ha => by rw [rootChar_neg', hα.2 a ha, inv_one]⟩

theorem famKernel_v {Fr : L →+* L} {F : Set (Fin Tag.E8.rank → Lˣ)}
    (hF : ∀ a ∈ F, a ∈ fixedCharTuples e8P4V Fr) {α : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ famKernel F) : e8P4V *ᵥ α ∈ famKernel F := by
  refine ⟨?_, fun a ha => ?_⟩
  · have := IsRoot.smul hα.1 ((coxeterSystem .E8).wordProd e8P4WW)
    rwa [e8P4_weylImage] at this
  · rw [mem_fixedCharTuples_iff.1 (hF a ha) α, hα.2 a ha, map_one]

theorem famKernel_cls (F : E8P4Frame0 K L ℓ f) (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : 2 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (c : adjointGroup .E8 K) {Y : Subgroup (adjointGroup .E8 K)}
    (hYT : ∀ y ∈ Y, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hYp : ∀ y ∈ Y, y ^ p = 1) (hYcard : p ^ 3 ≤ Nat.card Y)
    {α₀ : Fin Tag.E8.rank → ℤ}
    (hα₀ : α₀ ∈ famKernel ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
      Set (Fin Tag.E8.rank → Lˣ))) :
    famKernel ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
      Set (Fin Tag.E8.rank → Lˣ)) = cls α₀ := by
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]
    exact iterateFrobenius_def ℓ f x
  have hpℓ : ¬ ℓ ∣ p := not_dvd_char hf hK hp hpf
  have hYdT := tupleGroup_le_T0tors F c hYT hYp
  have hYdcard : p ^ 3 ≤ Nat.card (tupleGroup F c Y) := by
    rw [card_tupleGroup F c hYT]
    exact hYcard
  ext γ
  constructor
  · intro hγ
    exact mem_cls_iff.2 (eq_cls_of_trivial hFr hp hp2 hpf hpℓ hYdT hYdcard hα₀.1
      hγ.1 (fun y hy => hα₀.2 y hy) (fun y hy => hγ.2 y hy))
  · intro hγ
    have hfix : ∀ a ∈ ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
        Set (Fin Tag.E8.rank → Lˣ)), a ∈ fixedCharTuples e8P4V (iterateFrobenius L ℓ f) :=
      fun a ha => (hYdT ha).1
    rcases mem_cls_iff.1 hγ with rfl | rfl | rfl | rfl
    · exact hα₀
    · exact famKernel_neg' hα₀
    · exact famKernel_v hfix hα₀
    · exact famKernel_neg' (famKernel_v hfix hα₀)

theorem exists_family_kernel (F : E8P4Frame0 K L ℓ f) (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : 2 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (c : adjointGroup .E8 K) {Y : Subgroup (adjointGroup .E8 K)}
    (hYT : ∀ y ∈ Y, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hYp : ∀ y ∈ Y, y ^ p = 1) (hYcard : p ^ 3 ≤ Nat.card Y) :
    ∃ (ι' : Type) (P : ι' → Subgroup (ModGL .E8 L)),
      IsSigmaFamily F.n (iterateFrobenius L ℓ f)
        (famKernel ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
          Set (Fin Tag.E8.rank → Lˣ))) P ∧
      ∀ i, ∀ u ∈ P i, ∃ d ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)),
        psiC F c d = u := by
  classical
  by_cases hex : ∃ α, α ∈ famKernel ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
      Set (Fin Tag.E8.rank → Lˣ))
  · obtain ⟨α₀, hα₀⟩ := hex
    have hSeq := famKernel_cls F hK hf hp hp2 hpf c hYT hYp hYcard hα₀
    have hYQ : ∀ y ∈ Y, psiC F c y ∈
        Subgroup.centralizer (rootSpan .E8 L (cls α₀) : Set (ModGL .E8 L)) := by
      intro y hy
      obtain ⟨b, hb, hby⟩ := exists_tuple_of_mem F c hYT hy
      rw [← hby, Subgroup.mem_centralizer_iff]
      intro g hg
      have hle := rootSpan_le_centralizer (K := L) b (S := cls α₀)
        (fun γ hγ => by
          have : γ ∈ famKernel ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
            Set (Fin Tag.E8.rank → Lˣ)) := hSeq ▸ hγ
          exact ⟨this.1, this.2 b hb⟩)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    obtain ⟨P, hP, hrat⟩ := exists_pair_family_C F hf c hα₀.1 hYQ
    rw [← hSeq] at hP
    exact ⟨Unit, P, hP, fun _ => hrat⟩
  · push Not at hex
    have hSe : famKernel ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
        Set (Fin Tag.E8.rank → Lˣ)) = ∅ := Set.eq_empty_of_forall_notMem hex
    refine ⟨Empty, fun e => e.elim, ⟨fun e => e.elim, fun e => e.elim, fun e => e.elim,
      fun e => e.elim, fun e => e.elim, fun e => e.elim, fun y hy hyR _ => ?_⟩,
      fun e => e.elim⟩
    rw [hSe] at hy ⊢
    have h0 : rootSpan .E8 L (∅ : Set (Fin Tag.E8.rank → ℤ)) = ⊥ := by simp [rootSpan]
    rw [h0, sup_bot_eq] at hy
    refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have : g = 1 := by
      rw [h0] at hg
      exact hg
    rw [this, one_mul, mul_one]

@[expose] def StabGen (L : Type) [Field L] (Fr : L →+* L) (p : ℕ) : Prop :=
  ∀ Y : Subgroup (Fin Tag.E8.rank → Lˣ), Y ≤ T0tors Fr p → p ^ 3 ≤ Nat.card Y →
    famStabilizer (Y : Set (Fin Tag.E8.rank → Lˣ)) ⊆
      (Subgroup.closure {s | ∃ α ∈ famKernel (Y : Set (Fin Tag.E8.rank → Lˣ)),
        s = rootReflection α} : Set (WeylGroup .E8))

theorem stabGen_of_not_dvd_weyl {Fr : L →+* L} (hp : p.Prime) (hp10 : 10 < p)
    (hpℓ : ¬ ℓ ∣ p) : StabGen L Fr p := by
  classical
  intro Y hY hcard
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf (L := L) hp hpℓ
  have hord : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp (by omega) (Or.inr (Or.inr rfl))
  have hYfin : Finite Y := Nat.finite_of_card_ne_zero (by
    have : 0 < p ^ 3 := pow_pos hp.pos 3
    omega)
  exact famStabilizer_subset_closure (L := L) (τ := .E8) hp hord hζ
    (Y : Set (Fin Tag.E8.rank → Lˣ)) (fun a ha i => (hY ha).2 i)

theorem centralizer_psiC_le_sup (F : E8P4Frame0 K L ℓ f)
    (hgen : StabGen L (iterateFrobenius L ℓ f) p) (c : adjointGroup .E8 K)
    {Y : Subgroup (adjointGroup .E8 K)}
    (hYT : ∀ y ∈ Y, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hYp : ∀ y ∈ Y, y ^ p = 1) (hYcard : p ^ 3 ≤ Nat.card Y)
    {d : adjointGroup .E8 K} (hd : d ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 K))) :
    psiC F c d ∈ torusGroup .E8 L ⊔ rootSpan .E8 L
      (famKernel ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
        Set (Fin Tag.E8.rank → Lˣ))) := by
  classical
  have hYdT := tupleGroup_le_T0tors F c hYT hYp
  have hstab := hgen _ hYdT (by
    rw [card_tupleGroup F c hYT]
    exact hYcard)
  have hcomm : ∀ a ∈ ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) :
      Set (Fin Tag.E8.rank → Lˣ)),
      psiC F c d * rootDiagUnit .E8 a = rootDiagUnit .E8 a * psiC F c d := by
    intro a ha
    obtain ⟨y, hy, hya⟩ := ha
    have hya' : psiC F c y = rootDiagUnit .E8 a := hya
    rw [← hya', ← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_centralizer_iff.1 hd y hy).symm
  obtain ⟨t, ht, q, hq, h⟩ := mem_torus_mul_rootSpan_of_commute_fam
    ((tupleGroup F c Y : Subgroup (Fin Tag.E8.rank → Lˣ)) : Set (Fin Tag.E8.rank → Lˣ)) hstab
    (fun α hα => hα.1) (fun α hα => famKernel_neg' hα) subset_rfl (psiC_mem_adjoint F c d) hcomm
  rw [← h]
  exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hq)

theorem embed_normal_le_torus (F : E8P4Frame0 K L ℓ f) (hK : Nat.card K = ℓ ^ f)
    (c : adjointGroup .E8 K) {Y : Subgroup (adjointGroup .E8 K)}
    {S : Set (Fin Tag.E8.rank → ℤ)} {ι' : Type} {P : ι' → Subgroup (ModGL .E8 L)}
    (hP : IsSigmaFamily F.n (iterateFrobenius L ℓ f) S P)
    (hrat : ∀ i, ∀ u ∈ P i,
      ∃ d ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)), psiC F c d = u)
    (hHQ : ∀ d ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)),
      psiC F c d ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S)
    {V : Subgroup (adjointGroup .E8 K)}
    (hVD : V ≤ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)))
    (hVn : ∀ d ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)), ∀ v ∈ V, d * v * d⁻¹ ∈ V)
    (hVs : Group.IsSolvable V) :
    ∀ v ∈ V, psiC F c v ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  classical
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hP
  let ψ : Subgroup.centralizer (Y : Set (adjointGroup .E8 K)) →* ModGL .E8 L :=
    (psiC F c).comp (Subgroup.centralizer (Y : Set (adjointGroup .E8 K))).subtype
  have hψinj : Function.Injective ψ :=
    (psiC_injective F c).comp (Subgroup.subtype_injective _)
  have hPψ : ∀ i, P i ≤ ψ.range := fun i u hu => by
    obtain ⟨d, hd, rfl⟩ := hrat i u hu
    exact ⟨⟨d, hd⟩, rfl⟩
  have hfix : ∀ d : Subgroup.centralizer (Y : Set (adjointGroup .E8 K)),
      ψ d ∈ twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
    fun d => mem_twistedFixedPoints.2 (psiC_fixed F hK c d)
  have hnorm : ∀ i, ∀ d : Subgroup.centralizer (Y : Set (adjointGroup .E8 K)), ∀ u ∈ P i,
      ψ d * u * (ψ d)⁻¹ ∈ P i := fun i d u hu => hPnorm i (ψ d) (hHQ d d.2) (hfix d) u hu
  have hcent : ∀ d : Subgroup.centralizer (Y : Set (adjointGroup .E8 K)),
      (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈
        subtorusSigma F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) S :=
    fun d hd => hPcent (ψ d) (hHQ d d.2) (hfix d) hd
  have hV'n : (V.subgroupOf (Subgroup.centralizer (Y : Set (adjointGroup .E8 K)))).Normal :=
    ⟨fun v hv d => by
      rw [Subgroup.mem_subgroupOf] at hv ⊢
      exact hVn d d.2 v hv⟩
  have hV's : Group.IsSolvable
      (V.subgroupOf (Subgroup.centralizer (Y : Set (adjointGroup .E8 K)))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hVD).toMonoidHom) (MulEquiv.injective _)
  have hle := solvable_normal_le_of_embedding_family ψ hψinj P
    (subtorusSigma F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) S) hPψ hPq hnorm hcent
    (V.subgroupOf (Subgroup.centralizer (Y : Set (adjointGroup .E8 K))))
  intro v hv
  have hv' : (⟨v, hVD hv⟩ : Subgroup.centralizer (Y : Set (adjointGroup .E8 K))) ∈
      V.subgroupOf (Subgroup.centralizer (Y : Set (adjointGroup .E8 K))) :=
    Subgroup.mem_subgroupOf.2 hv
  have key := hle hv'
  rw [Subgroup.mem_comap] at key
  have key2 := subtorusSigma_le_twistedTorusOf _ _ S key
  have e : ψ ⟨v, hVD hv⟩ = psiC F c v := rfl
  rw [e] at key2
  exact key2

theorem base_case_gen (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp2 : 2 < p) (hgen : StabGen L (iterateFrobenius L ℓ f) p)
    (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (c : adjointGroup .E8 K) {Y : Subgroup (adjointGroup .E8 K)}
    (hYT : ∀ y ∈ Y, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hYp : ∀ y ∈ Y, y ^ p = 1) (hYcard : p ^ 3 ≤ Nat.card Y)
    {V : Subgroup (adjointGroup .E8 K)}
    (hVD : V ≤ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)))
    (hVn : ∀ d ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)), ∀ v ∈ V, d * v * d⁻¹ ∈ V)
    (hVs : Group.IsSolvable V) :
    ∀ v ∈ V, psiC F c v ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  obtain ⟨ι', P, hP, hrat⟩ := exists_family_kernel F hK hf hp hp2 hpf c hYT hYp hYcard
  exact embed_normal_le_torus F hK c hP hrat
    (fun d hd => centralizer_psiC_le_sup F hgen c hYT hYp hYcard hd) hVD hVn hVs

theorem base_case (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp10 : 10 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (c : adjointGroup .E8 K) {Y : Subgroup (adjointGroup .E8 K)}
    (hYT : ∀ y ∈ Y, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hYp : ∀ y ∈ Y, y ^ p = 1) (hYcard : p ^ 3 ≤ Nat.card Y)
    {V : Subgroup (adjointGroup .E8 K)}
    (hVD : V ≤ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)))
    (hVn : ∀ d ∈ Subgroup.centralizer (Y : Set (adjointGroup .E8 K)), ∀ v ∈ V, d * v * d⁻¹ ∈ V)
    (hVs : Group.IsSolvable V) :
    ∀ v ∈ V, psiC F c v ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
  base_case_gen F hf hK hp (by omega)
    (stabGen_of_not_dvd_weyl hp hp10 (not_dvd_char hf hK hp hpf)) hpf c hYT hYp hYcard hVD hVn hVs

end BaseMain

end CFSG.RankThree.PartOne.KE8F
