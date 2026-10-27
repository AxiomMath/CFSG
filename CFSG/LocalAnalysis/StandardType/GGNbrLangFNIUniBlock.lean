module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniPsu
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniMark
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.HardMathSupport.Dickson.Bal207.Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniBlocks

public section

namespace CFSG.StandardType

open Polynomial Module CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ComponentClassification.Burgoyne.U
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks
  (toLinSU exists_good_block_of_component primaryData_toLin')

section Blocks

variable {n d : ℕ} {K : Type} [Field K]

theorem fniUni_good_block (hn : 1 ≤ n) (hd : 3 ≤ d) (h : UnitaryFieldData 2 n K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (A : GL (Fin d) K) (hA : A ∈ primeFormUnitary h (idGram K d))
    {c : Kˣ} (hAc : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c)
    (u : MulAut (StatedProj (StatedSU d (2 ^ n) K)))
    (hu : ∀ g g' : ↥(StatedSU d (2 ^ n) K),
      (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
        u (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K)))
    (hJP : CFSG.Open.IsComponentOf JP (fixSubgroup u)) :
    ∃ (H : UnitaryPrimaryData h.bar (idForm h d) (Matrix.GeneralLinearGroup.toLin A))
      (a : {a : primaryFactors ((Matrix.GeneralLinearGroup.toLin A :
          LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) //
        IsGoodBlock h (Matrix.GeneralLinearGroup.toLin A) a}),
      ∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ JP ↔
        ∃ g : GL (Fin d) K, Matrix.GeneralLinearGroup.toLin g ∈
          specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X]) ∧
          ∃ hg : g ∈ StatedSU d (2 ^ n) K,
            LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨g, hg⟩ = z := by
  classical
  haveI := h.finite
  have hd1 : 1 ≤ d := by omega
  have hq : 2 ≤ 2 ^ n := by
    have := Nat.one_lt_pow (by omega : n ≠ 0) Nat.one_lt_two
    omega
  set A' : primeFormUnitary h (idGram K d) := ⟨A, hA⟩ with hA'
  have hu' : u = uConjAut h hd1 A' := by
    ext r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective r
    have h1 := hu g ⟨A * (g : GL (Fin d) K) * A⁻¹, uConjSU_mem h A' g⟩ rfl
    exact h1.trans (uConjAut_proj h hd1 A' g).symm
  have hcompat : ∀ r : StatedProj (StatedSU d (2 ^ n) K),
      uTransport h hd1 (u r) = primeFormConjHom h (idGram K d) A' (uTransport h hd1 r) := by
    intro r
    rw [hu']
    have : uConjAut h hd1 A' = (MulAut.congr (uTransport h hd1)).symm
        (primeFormConjHom h (idGram K d) A') := rfl
    rw [this]
    simp [MulAut.congr_apply]
  have hfix : (fixSubgroup u).map (uTransport h hd1).toMonoidHom =
      fixSubgroup (primeFormConjHom h (idGram K d) A') := by
    ext y
    obtain ⟨r, rfl⟩ := (uTransport h hd1).surjective y
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_fixSubgroup, mem_fixSubgroup,
      ← hcompat]
    exact (uTransport h hd1).injective.eq_iff.symm
  have hcomp : CFSG.Open.IsComponentOf (JP.map (uTransport h hd1).toMonoidHom)
      (fixSubgroup (primeFormConjHom h (idGram K d) A')) := by
    have := CFSG.isComponentOf_map_mulEquiv (uTransport h hd1) hJP
    rwa [hfix] at this
  have H := primaryData_toLin' h hA hp hp2 hAc
  obtain ⟨a, hLeq⟩ := exists_good_block_of_component hq A' rfl H _ hcomp
  refine ⟨H, a, ?_⟩
  exact l154_JP_iff hd1 h JP _
    ((specialBlock (idForm h d) (Matrix.GeneralLinearGroup.toLin A) (a.1 : K[X])).comap
      (Matrix.GeneralLinearGroup.toLin :
        GL (Fin d) K ≃* LinearMap.GeneralLinearGroup K (Fin d → K)).toMonoidHom)
    (fun g => Iff.rfl) hLeq

theorem fniUni_block_data (hn : 1 ≤ n) (hd : 3 ≤ d) (h : UnitaryFieldData 2 n K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (A : GL (Fin d) K) (hA : A ∈ primeFormUnitary h (idGram K d))
    {c : Kˣ} (hAc : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c)
    (u : MulAut (StatedProj (StatedSU d (2 ^ n) K)))
    (hu : ∀ g g' : ↥(StatedSU d (2 ^ n) K),
      (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
        u (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    (JP : Subgroup (StatedProj (StatedSU d (2 ^ n) K)))
    (hJP : CFSG.Open.IsComponentOf JP (fixSubgroup u)) :
    L154BlockSU n d K h JP ∨ L154BlockSL n d K h JP ∨ L154BlockSL2 n d K h JP := by
  obtain ⟨H, a, hz⟩ := fniUni_good_block hn hd h hp hp2 A hA hAc u hu JP hJP
  by_cases hself : dualPoly h.bar (a.1 : K[X]) = a.1
  · by_cases hm3 : 3 ≤ primaryMultiplicity
        (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin d → K)) (a.1 : K[X])
    · exact Or.inl (l154_uni_block_su hn h A JP H a hz hself hm3)
    · exact Or.inr (Or.inr (l154_uni_block_sl2 hn h A JP H a hz hself hm3))
  · exact Or.inr (Or.inl (l154_uni_block_sl hn h A JP H a hz hself))

end Blocks

theorem fniUni_centerQuot_equiv {R G₁ R₁ : Type} [Group R] [Group G₁] [Group R₁]
    {J₀ : Subgroup R} (Ψ : G₁ →* R) (q₁ : G₁ →* R₁) (hq₁s : Function.Surjective q₁)
    (hq₁k : q₁.ker ≤ Subgroup.center G₁) (hR₁ : Subgroup.center R₁ = ⊥)
    (hker : ∀ m, Ψ m = 1 → q₁ m = 1) (hJ : ∀ z : R, z ∈ J₀ ↔ ∃ m, Ψ m = z) :
    ∃ e₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* R₁,
      ∀ (m : G₁) (hm : Ψ m ∈ J₀), e₀ (QuotientGroup.mk ⟨Ψ m, hm⟩) = q₁ m := by
  classical
  obtain ⟨Θ, hΘ⟩ := l154_exists_hom_lift J₀.subtype Ψ q₁
    (fun j => (hJ (j : R)).1 j.2) hker
  have hΘsurj : Function.Surjective Θ := by
    intro r
    obtain ⟨m, rfl⟩ := hq₁s r
    have hm : Ψ m ∈ J₀ := (hJ (Ψ m)).2 ⟨m, rfl⟩
    refine ⟨⟨Ψ m, hm⟩, ?_⟩
    obtain ⟨m', hm'⟩ := (hJ (Ψ m)).1 hm
    have hq : q₁ m = q₁ m' := by
      have h1 : q₁ (m⁻¹ * m') = 1 := by
        apply hker
        rw [map_mul, map_inv, hm', inv_mul_cancel]
      rw [map_mul, map_inv] at h1
      exact inv_mul_eq_one.1 h1
    rw [hΘ _ _ hm', hq]
  have hker_le : Θ.ker ≤ Subgroup.center ↥J₀ := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    obtain ⟨m, hm⟩ := (hJ (j : R)).1 j.2
    have hq1 : q₁ m = 1 := by
      rw [← hΘ j m hm]
      exact hj
    have hmc : m ∈ Subgroup.center G₁ := hq₁k (MonoidHom.mem_ker.2 hq1)
    rw [Subgroup.mem_center_iff]
    intro j'
    obtain ⟨m', hm'⟩ := (hJ (j' : R)).1 j'.2
    apply Subtype.ext
    show (j' : R) * (j : R) = (j : R) * (j' : R)
    rw [← hm, ← hm', ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hmc m']
  have hcenter_le : Subgroup.center ↥J₀ ≤ Θ.ker := by
    intro j hj
    rw [MonoidHom.mem_ker]
    have hzj : Θ j ∈ Subgroup.center R₁ := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨j', rfl⟩ := hΘsurj r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hj j']
    rw [hR₁] at hzj
    simpa using hzj
  have hker_eq : Θ.ker = Subgroup.center ↥J₀ := le_antisymm hker_le hcenter_le
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Θ hΘsurj), ?_⟩
  intro m hm
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  exact hΘ _ m rfl

variable {n d : ℕ} {K : Type} [Field K]

theorem fniUni_exists_moved (h : UnitaryFieldData 2 n K) (σ : K ≃+* K)
    (hσmem : ∀ g ∈ StatedSU d (2 ^ n) K, glMap σ g ∈ StatedSU d (2 ^ n) K)
    {f : MulAut (StatedProj (StatedSU d (2 ^ n) K))}
    (hf : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = glMap σ (g : GL (Fin d) K) →
      f (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hord : orderOf f = p) :
    ∃ c : K, h.bar c = c ∧ σ c ≠ c := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hcomm : ∀ c, σ (h.bar c) = h.bar (σ c) := by
    intro c
    rw [h.bar_apply, h.bar_apply, map_pow]
  have hroot : ∀ c, σ c = c ∨ σ c = h.bar c := by
    intro c
    have hs : h.bar (c + h.bar c) = c + h.bar c := by rw [map_add, h.bar_bar, add_comm]
    have hn : h.bar (c * h.bar c) = c * h.bar c := by rw [map_mul, h.bar_bar, mul_comm]
    have hs' := hcon _ hs
    have hn' := hcon _ hn
    rw [map_add, hcomm] at hs'
    rw [map_mul, hcomm] at hn'
    have h0 : (σ c - c) * (σ c - h.bar c) = 0 := by
      have e : (σ c - c) * (σ c - h.bar c) =
          σ c * σ c - (c + h.bar c) * σ c + c * h.bar c := by ring
      rw [e, ← hs', ← hn']
      ring
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hσ2 : σ ^ 2 = 1 := by
    rcases eq_or_ne σ 1 with h1 | h1
    · rw [h1]
      ext c
      simp
    · have hall : ∀ c, σ c = h.bar c := by
        by_contra hne
        push Not at hne
        obtain ⟨c1, hc1⟩ := hne
        obtain ⟨c0, hc0⟩ : ∃ c0, σ c0 ≠ c0 := by
          by_contra hh
          simp only [not_exists, not_not] at hh
          exact h1 (RingEquiv.ext hh)
        have hc0b : σ c0 = h.bar c0 := (hroot c0).resolve_left hc0
        have hc1' : σ c1 = c1 := (hroot c1).resolve_right hc1
        rcases hroot (c1 + c0) with h | h
        · rw [map_add, hc1', hc0b] at h
          exact hc0 (hc0b.trans (add_left_cancel h))
        · rw [map_add, hc1', hc0b, map_add] at h
          exact hc1 (hc1'.trans (add_right_cancel h))
      ext c
      rw [pow_two]
      show σ (σ c) = c
      rw [hall c, hall (h.bar c)]
      exact h.bar_bar c
  have hff : f * f = 1 := by
    ext r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective r
    change f (f (LargeEvenProjMk (StatedSU d (2 ^ n) K) g)) =
      LargeEvenProjMk (StatedSU d (2 ^ n) K) g
    have hgl0 : glMap σ (glMap σ (g : GL (Fin d) K)) = (g : GL (Fin d) K) := by
      have h1 : glMap (σ ^ 2) (g : GL (Fin d) K) =
          glMap σ (glMap σ (g : GL (Fin d) K)) := by
        simpa using glMap_pow_succ σ 1 (g : GL (Fin d) K)
      rw [← h1, hσ2, glMap_one]
    have hgl : (g : GL (Fin d) K) = glMap σ (glMap σ (g : GL (Fin d) K)) := hgl0.symm
    rw [hf g ⟨glMap σ (g : GL (Fin d) K), hσmem (g : GL (Fin d) K) g.2⟩ rfl]
    rw [hf ⟨glMap σ (g : GL (Fin d) K), hσmem (g : GL (Fin d) K) g.2⟩ g hgl]
  have hdvd : p ∣ 2 := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hff
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)

theorem fniUni_not_mem_of_line {m : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 2 n K)
    (σ : K ≃+* K) (hσmem : ∀ g ∈ StatedSU d (2 ^ n) K, glMap σ g ∈ StatedSU d (2 ^ n) K)
    {f : MulAut (StatedProj (StatedSU d (2 ^ n) K))}
    (hf : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = glMap σ (g : GL (Fin d) K) →
      f (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    {J₀ : Subgroup (StatedProj (StatedSU d (2 ^ n) K))} (f' : MulAut ↥J₀)
    (hf' : ∀ j : ↥J₀, (f' j : StatedProj (StatedSU d (2 ^ n) K)) = f j)
    {M : Subgroup (GL (Fin m) E)} (hperf : commutator ↥M = ⊤) (ι : GL (Fin m) E →* GL (Fin d) K)
    (hmem : ∀ t ∈ M, ι t ∈ StatedSU d (2 ^ n) K)
    (hJ : ∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ J₀ ↔ ∃ t ∈ M,
      ∃ ht : ι t ∈ StatedSU d (2 ^ n) K, LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, ht⟩ = z)
    (e₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj M)
    (he₀ : ∀ (t : ↥M)
      (ht : LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, hmem t t.2⟩ ∈ J₀),
      e₀ (QuotientGroup.mk ⟨_, ht⟩) = LargeEvenProjMk M t)
    (S₀ : Set (GL (Fin m) E)) (hnorm : ∀ P ∈ S₀, ∀ t ∈ M, P * t * P⁻¹ ∈ M)
    (N : Matrix (Fin d) (Fin d) K) (hN : N ≠ 0) {c₁ : K} (hc₁ : h.bar c₁ = c₁)
    (hσc : σ c₁ ≠ c₁)
    (hline : ∀ c : K, h.bar c = c →
      ∃ t ∈ M, ((ι t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N)
    {φ : MulAut (LargeEvenProj M)} (hφ : LargeEvenInduces e₀ (fun j k : ↥J₀ => k = f' j) φ) :
    φ ∉ LargeEvenMatConjImage (LargeEvenProjMk M) S₀ := by
  classical
  have hcongr : MulAut.congr (MulEquiv.refl (LargeEvenProj M)) φ = φ := by
    ext f
    simp [MulAut.congr, MulEquiv.trans_apply]
  have hnot : MulAut.congr (MulEquiv.refl (LargeEvenProj M)) φ ∉
      LargeEvenMatConjImage (LargeEvenProjMk M) S₀ := by
    refine l154_notInner_of_line ι hperf σ 1 S₀ hnorm (MulEquiv.refl (LargeEvenProj M)) φ ?_
      N hN {c : K | h.bar c = c} (map_one h.bar) hc₁ hσc (fun c hc => hline c hc)
    intro t
    set g : ↥(StatedSU d (2 ^ n) K) := ⟨ι (t : GL (Fin m) E), hmem t t.2⟩ with hg
    have hjg : LargeEvenProjMk (StatedSU d (2 ^ n) K) g ∈ J₀ :=
      (hJ _).2 ⟨t, t.2, hmem t t.2, rfl⟩
    set j : ↥J₀ := ⟨LargeEvenProjMk (StatedSU d (2 ^ n) K) g, hjg⟩ with hj
    obtain ⟨t', ht', ht'SU, hJp⟩ :=
      (hJ (f' j : StatedProj (StatedSU d (2 ^ n) K))).1 (f' j).2
    have he0t : e₀ (QuotientGroup.mk j) = LargeEvenProjMk M t := he₀ t hjg
    have hfj : e₀ (QuotientGroup.mk (f' j)) = LargeEvenProjMk M ⟨t', ht'⟩ := by
      have harg : (⟨LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t', ht'SU⟩,
          (hJ _).2 ⟨t', ht', ht'SU, rfl⟩⟩ : ↥J₀) = f' j := by
        apply Subtype.ext
        exact hJp
      rw [← harg]
      exact he₀ ⟨t', ht'⟩ _
    have hJp' : LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t', ht'SU⟩ =
        LargeEvenProjMk (StatedSU d (2 ^ n) K)
          ⟨glMap σ (ι (t : GL (Fin m) E)), hσmem _ (hmem t t.2)⟩ := by
      have h1 : (f' j : StatedProj (StatedSU d (2 ^ n) K)) =
          LargeEvenProjMk (StatedSU d (2 ^ n) K)
            ⟨glMap σ (ι (t : GL (Fin m) E)), hσmem _ (hmem t t.2)⟩ := by
        rw [hf' j]
        exact hf g ⟨glMap σ (ι (t : GL (Fin m) E)), hσmem _ (hmem t t.2)⟩ rfl
      exact hJp.trans h1
    obtain ⟨z0, hz0⟩ :=
      (l154_projMk_eq_iff (StatedSU d (2 ^ n) K) ⟨ι t', ht'SU⟩
        ⟨glMap σ (ι (t : GL (Fin m) E)), hσmem _ (hmem t t.2)⟩).1 hJp'
    refine ⟨⟨t', ht'⟩, z0⁻¹, ?_, ?_⟩
    · rw [hcongr]
      calc φ (LargeEvenProjMk M t) = φ (e₀ (QuotientGroup.mk j)) := by rw [he0t]
        _ = e₀ (QuotientGroup.mk (f' j)) := hφ j (f' j) rfl
        _ = LargeEvenProjMk M ⟨t', ht'⟩ := hfj
    · have hmain : ι t' = Matrix.GeneralLinearGroup.scalar (Fin d) z0⁻¹ *
          glMap σ (ι (t : GL (Fin m) E)) := by
        have h1 : ι t' * Matrix.GeneralLinearGroup.scalar (Fin d) z0 =
            glMap σ (ι (t : GL (Fin m) E)) := by
          rw [hz0]
          group
        rw [← h1, ← mul_assoc, scalar_mul_comm, mul_assoc, ← map_mul, inv_mul_cancel,
          map_one, mul_one]
      simpa using hmain
  rw [hcongr] at hnot
  exact hnot

theorem fniUni_not_mem_sl2 {F : Type} [Field F] [Finite F] (hF2 : (2 : F) = 0)
    (h : UnitaryFieldData 2 n K) (σ : K ≃+* K)
    (hσmem : ∀ g ∈ StatedSU d (2 ^ n) K, glMap σ g ∈ StatedSU d (2 ^ n) K)
    {f : MulAut (StatedProj (StatedSU d (2 ^ n) K))}
    (hf : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = glMap σ (g : GL (Fin d) K) →
      f (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    {J₀ : Subgroup (StatedProj (StatedSU d (2 ^ n) K))} (f' : MulAut ↥J₀)
    (hf' : ∀ j : ↥J₀, (f' j : StatedProj (StatedSU d (2 ^ n) K)) = f j)
    (hperf : commutator ↥(StatedSL 2 F) = ⊤) (ι : ↥(StatedSL 2 F) →* GL (Fin d) K)
    (hmem : ∀ t, ι t ∈ StatedSU d (2 ^ n) K)
    (hJ : ∀ z : StatedProj (StatedSU d (2 ^ n) K), z ∈ J₀ ↔ ∃ t : ↥(StatedSL 2 F),
      ∃ ht : ι t ∈ StatedSU d (2 ^ n) K, LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, ht⟩ = z)
    (e₀ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (StatedSL 2 F))
    (he₀ : ∀ (t : ↥(StatedSL 2 F))
      (ht : LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, hmem t⟩ ∈ J₀),
      e₀ (QuotientGroup.mk ⟨_, ht⟩) = LargeEvenProjMk (StatedSL 2 F) t)
    (N : Matrix (Fin d) (Fin d) K) (hN : N ≠ 0) {c₁ : K} (hc₁ : h.bar c₁ = c₁)
    (hσc : σ c₁ ≠ c₁)
    (hline : ∀ c : K, h.bar c = c →
      ∃ t : ↥(StatedSL 2 F), ((ι t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N)
    {φ : MulAut (LargeEvenProj (StatedSL 2 F))}
    (hφ : LargeEvenInduces e₀ (fun j k : ↥J₀ => k = f' j) φ) :
    φ ∉ LargeEvenMatConjImage (LargeEvenProjMk (StatedSL 2 F)) Set.univ := by
  classical
  have hcongr : MulAut.congr (MulEquiv.refl (LargeEvenProj (StatedSL 2 F))) φ = φ := by
    ext f
    simp [MulAut.congr, MulEquiv.trans_apply]
  have hnot : MulAut.congr (MulEquiv.refl (LargeEvenProj (StatedSL 2 F))) φ ∉
      LargeEvenMatConjImage (LargeEvenProjMk (StatedSL 2 F)) Set.univ := by
    refine l154_notInner_sl2 hF2 ι hperf σ 1 (MulEquiv.refl (LargeEvenProj (StatedSL 2 F))) φ ?_
      N hN {c : K | h.bar c = c} (map_one h.bar) hc₁ hσc (fun c hc => hline c hc)
    intro t
    set g : ↥(StatedSU d (2 ^ n) K) := ⟨ι t, hmem t⟩ with hg
    have hjg : LargeEvenProjMk (StatedSU d (2 ^ n) K) g ∈ J₀ :=
      (hJ _).2 ⟨t, hmem t, rfl⟩
    set j : ↥J₀ := ⟨LargeEvenProjMk (StatedSU d (2 ^ n) K) g, hjg⟩ with hj
    obtain ⟨t', ht'SU, hJp⟩ :=
      (hJ (f' j : StatedProj (StatedSU d (2 ^ n) K))).1 (f' j).2
    have he0t : e₀ (QuotientGroup.mk j) = LargeEvenProjMk (StatedSL 2 F) t := he₀ t hjg
    have hfj : e₀ (QuotientGroup.mk (f' j)) = LargeEvenProjMk (StatedSL 2 F) t' := by
      have harg : (⟨LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t', ht'SU⟩,
          (hJ _).2 ⟨t', ht'SU, rfl⟩⟩ : ↥J₀) = f' j := by
        apply Subtype.ext
        exact hJp
      rw [← harg]
      exact he₀ t' _
    have hJp' : LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t', ht'SU⟩ =
        LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨glMap σ (ι t), hσmem _ (hmem t)⟩ := by
      have h1 : (f' j : StatedProj (StatedSU d (2 ^ n) K)) =
          LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨glMap σ (ι t), hσmem _ (hmem t)⟩ := by
        rw [hf' j]
        exact hf g ⟨glMap σ (ι t), hσmem _ (hmem t)⟩ rfl
      exact hJp.trans h1
    obtain ⟨z0, hz0⟩ :=
      (l154_projMk_eq_iff (StatedSU d (2 ^ n) K) ⟨ι t', ht'SU⟩
        ⟨glMap σ (ι t), hσmem _ (hmem t)⟩).1 hJp'
    refine ⟨t', z0⁻¹, ?_, ?_⟩
    · rw [hcongr]
      calc φ (LargeEvenProjMk (StatedSL 2 F) t) =
            φ (e₀ (QuotientGroup.mk j)) := by rw [he0t]
        _ = e₀ (QuotientGroup.mk (f' j)) := hφ j (f' j) rfl
        _ = LargeEvenProjMk (StatedSL 2 F) t' := hfj
    · have hmain : ι t' = Matrix.GeneralLinearGroup.scalar (Fin d) z0⁻¹ * glMap σ (ι t) := by
        have h1 : ι t' * Matrix.GeneralLinearGroup.scalar (Fin d) z0 = glMap σ (ι t) := by
          rw [hz0]
          group
        rw [← h1, ← mul_assoc, scalar_mul_comm, mul_assoc, ← map_mul, inv_mul_cancel,
          map_one, mul_one]
      simpa using hmain
  rw [hcongr] at hnot
  exact hnot

theorem fniUni_neg_su [Finite K] (h : UnitaryFieldData 2 n K) (σ : K ≃+* K)
    (hσmem : ∀ g ∈ StatedSU d (2 ^ n) K, glMap σ g ∈ StatedSU d (2 ^ n) K)
    {f : MulAut (StatedProj (StatedSU d (2 ^ n) K))}
    (hf : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = glMap σ (g : GL (Fin d) K) →
      f (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    {J₀ : Subgroup (StatedProj (StatedSU d (2 ^ n) K))} (hJ₀ : commutator ↥J₀ = ⊤)
    (f' : MulAut ↥J₀) (hf' : ∀ j : ↥J₀, (f' j : StatedProj (StatedSU d (2 ^ n) K)) = f j)
    {c₁ : K} (hc₁ : h.bar c₁ = c₁) (hσc : σ c₁ ≠ c₁) (hblock : L154BlockSU n d K h J₀) :
    LargeEvenMarking ↥J₀ fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : ↥J₀ => k = f' j) φ := by
  classical
  obtain ⟨m, E, instE, finE, k, ι, N, hm3, hk1, hk2, hcardE, hN, hline, hmem, hscal,
    hJPiff⟩ := hblock
  have hnq : (m, 2 ^ k) ≠ (3, 2) := by
    intro hc
    have h1 : m = 3 := congrArg Prod.fst hc
    have h2 : 2 ^ k = 2 := congrArg Prod.snd hc
    have := hk2 h1
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hperfM : commutator ↥(StatedSU m (2 ^ k) E) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcardE hm3 hnq)
  have hsimple : IsSimpleGroup (LargeEvenProj (StatedSU m (2 ^ k) E)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU E 2 k hcardE m hm3 hnq
  let ι' : ↥(StatedSU m (2 ^ k) E) →* GL (Fin d) K := ι.comp (StatedSU m (2 ^ k) E).subtype
  let Ψ : ↥(StatedSU m (2 ^ k) E) →* StatedProj (StatedSU d (2 ^ n) K) :=
    (LargeEvenProjMk (StatedSU d (2 ^ n) K)).comp
      (ι'.codRestrict (StatedSU d (2 ^ n) K) (fun t => hmem t.1 t.2))
  have hΨ : ∀ t : ↥(StatedSU m (2 ^ k) E),
      Ψ t = LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t.1, hmem t.1 t.2⟩ := fun t => rfl
  have hJ : ∀ z : StatedProj (StatedSU d (2 ^ n) K),
      z ∈ J₀ ↔ ∃ t : ↥(StatedSU m (2 ^ k) E), Ψ t = z := by
    intro z
    rw [hJPiff z]
    constructor
    · rintro ⟨t, ht, htSU, hz⟩
      exact ⟨⟨t, ht⟩, (hΨ ⟨t, ht⟩).trans hz⟩
    · rintro ⟨t, hz⟩
      exact ⟨t.1, t.2, hmem t.1 t.2, (hΨ t).symm.trans hz⟩
  haveI : IsSimpleGroup (LargeEvenProj (StatedSU m (2 ^ k) E)) := hsimple
  haveI : Group.IsPerfect ↥(StatedSU m (2 ^ k) E) := Group.isPerfect_def.mpr hperfM
  haveI : Group.IsPerfect (LargeEvenProj (StatedSU m (2 ^ k) E)) :=
    Group.IsPerfect.ofSurjective (f := LargeEvenProjMk _) (QuotientGroup.mk'_surjective _)
  have hna : ∃ a b : LargeEvenProj (StatedSU m (2 ^ k) E), a * b ≠ b * a := by
    have hnc := Group.IsPerfect.not_isMulCommutative (G := LargeEvenProj (StatedSU m (2 ^ k) E))
    rw [isMulCommutative_iff] at hnc
    push Not at hnc
    exact hnc
  have hcenter : Subgroup.center (LargeEvenProj (StatedSU m (2 ^ k) E)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (LargeEvenProj (StatedSU m (2 ^ k) E))) with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm
  have hker : ∀ t : ↥(StatedSU m (2 ^ k) E), Ψ t = 1 →
      LargeEvenProjMk (StatedSU m (2 ^ k) E) t = 1 := by
    intro t ht
    have h1 : LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t.1, hmem t.1 t.2⟩ =
        LargeEvenProjMk (StatedSU d (2 ^ n) K) 1 := by
      rw [← hΨ t, ht, map_one]
    obtain ⟨z, hz⟩ := (projMk_eq_iff_uni (StatedSU d (2 ^ n) K)
      ⟨ι t.1, hmem t.1 t.2⟩ 1).1 h1
    have hz' : ι (t : GL (Fin m) E) = Matrix.GeneralLinearGroup.scalar (Fin d) z⁻¹ := by
      have e1 : Matrix.GeneralLinearGroup.scalar (Fin d) z⁻¹ =
          (Matrix.GeneralLinearGroup.scalar (Fin d) z)⁻¹ := map_inv _ z
      rw [e1, hz]
      simp
    obtain ⟨c, hc⟩ := hscal (t : GL (Fin m) E) z⁻¹ hz'
    refine (projMk_eq_iff_uni (StatedSU m (2 ^ k) E) t 1).2 ⟨c⁻¹, ?_⟩
    rw [hc]
    simpa using (map_inv (Matrix.GeneralLinearGroup.scalar (Fin m)) c).symm
  obtain ⟨e₀, he₀⟩ := fniUni_centerQuot_equiv Ψ (LargeEvenProjMk (StatedSU m (2 ^ k) E))
    (QuotientGroup.mk'_surjective _) (ker_projMk_uni_le_center _) hcenter hker hJ
  have hnorm : ∀ P ∈ LargeEvenGUSet (Fin m) E (2 ^ k),
      ∀ t ∈ StatedSU m (2 ^ k) E, P * t * P⁻¹ ∈ StatedSU m (2 ^ k) E := by
    intro P hP t ht
    obtain ⟨τ', hτ'm, hτ'⟩ := exists_frob_equiv hcardE
    obtain ⟨A', hA', hAeq⟩ := exists_heldGU_of_GUSet hτ'm hcardE hτ' P hP
    have := conj_mem_statedSU hτ' hτ'm hA' ht
    rwa [hAeq] at this
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  refine ⟨hJ₀, ⟨.twA, r, k⟩, ?_, ?_⟩
  · change 1 ≤ k ∧ 2 ≤ r ∧ (r = 2 → 2 ≤ k)
    exact ⟨hk1, by omega, fun hr2 => hk2 (by omega)⟩
  · refine ⟨E, instE, finE, hcardE, hsimple, hna, e₀, ?_⟩
    rintro ⟨φ, hφcl, hind⟩
    have hq : ¬(r + 1 = 3 ∧ 2 ^ k = 2) := fun hc => hnq (Prod.ext hc.1 hc.2)
    have hE : UnitaryFieldData 2 k E := unitaryFieldData_of_card hk1 hcardE
    have hI := RecipeFieldSU.ggRawInnField_unitary hE hcardE (by omega : 3 ≤ r + 1) hq
      (p := 3) (by norm_num)
    obtain ⟨hmul, hinv, hconj, -⟩ := hI hsimple hna
    let H' : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) E (2 ^ k)))) :=
      { carrier := LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) E (2 ^ k)))
          (LargeEvenGUSet (Fin (r + 1)) E (2 ^ k))
        one_mem' := by simpa using hconj 1
        mul_mem' := fun ha hb => hmul _ ha _ hb
        inv_mem' := fun ha => hinv _ ha }
    have hclosure : Subgroup.closure
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) E (2 ^ k)))
          (LargeEvenGUSet (Fin (r + 1)) E (2 ^ k))) ≤ H' := by
      rw [Subgroup.closure_le]
      exact fun x hx => by simpa [H'] using hx
    have hφI : φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) E (2 ^ k)))
        (LargeEvenGUSet (Fin (r + 1)) E (2 ^ k)) := by
      simpa [H'] using hclosure hφcl
    exact (fniUni_not_mem_of_line (J₀ := J₀) h σ hσmem hf f' hf' hperfM ι
      hmem hJPiff e₀ he₀ (LargeEvenGUSet (Fin (r + 1)) E (2 ^ k)) hnorm
      N hN hc₁ hσc hline hind) hφI

theorem fniUni_neg_sl [Finite K] (h : UnitaryFieldData 2 n K) (σ : K ≃+* K)
    (hσmem : ∀ g ∈ StatedSU d (2 ^ n) K, glMap σ g ∈ StatedSU d (2 ^ n) K)
    {f : MulAut (StatedProj (StatedSU d (2 ^ n) K))}
    (hf : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = glMap σ (g : GL (Fin d) K) →
      f (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    {J₀ : Subgroup (StatedProj (StatedSU d (2 ^ n) K))} (hJ₀ : commutator ↥J₀ = ⊤)
    (f' : MulAut ↥J₀) (hf' : ∀ j : ↥J₀, (f' j : StatedProj (StatedSU d (2 ^ n) K)) = f j)
    {c₁ : K} (hc₁ : h.bar c₁ = c₁) (hσc : σ c₁ ≠ c₁) (hblock : L154BlockSL n d K h J₀) :
    LargeEvenMarking ↥J₀ fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : ↥J₀ => k = f' j) φ := by
  classical
  obtain ⟨m, E, instE, finE, k, ι, N, hm2, hk2, hcardE, hN, hline, hmem, hscal,
    hJPiff⟩ := hblock
  rw [← largeEvenSLGroup_eq_statedSL (K := E) m] at hline hmem hJPiff
  have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have h22 : m ≠ 2 ∨ Nat.card E ≠ 2 := Or.inr (by rw [hcardE]; omega)
  have h23 : m ≠ 2 ∨ Nat.card E ≠ 3 := Or.inr (by rw [hcardE]; omega)
  have hperfM : commutator ↥(LargeEvenSLGroup (Fin m) E) = ⊤ := by
    rw [largeEvenSLGroup_eq_statedSL (K := E) m]
    exact Group.isPerfect_def.mp
      (CFSG.LieType.SemisimpleCentralizers.Held.hct_isPerfect_statedSL E hm2 h22 h23)
  have hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin m) E)) := by
    rw [largeEvenSLGroup_eq_statedSL (K := E) m]
    exact CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL E hm2 h22 h23
  have h4E : 4 ≤ Nat.card E := by
    rw [hcardE]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  let ι' : ↥(LargeEvenSLGroup (Fin m) E) →* GL (Fin d) K :=
    ι.comp (LargeEvenSLGroup (Fin m) E).subtype
  let Ψ : ↥(LargeEvenSLGroup (Fin m) E) →* StatedProj (StatedSU d (2 ^ n) K) :=
    (LargeEvenProjMk (StatedSU d (2 ^ n) K)).comp
      (ι'.codRestrict (StatedSU d (2 ^ n) K) (fun t => hmem t t.2))
  have hΨ : ∀ t : ↥(LargeEvenSLGroup (Fin m) E),
      Ψ t = LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι (t : GL (Fin m) E), hmem t t.2⟩ :=
    fun t => rfl
  have hJ : ∀ z : StatedProj (StatedSU d (2 ^ n) K),
      z ∈ J₀ ↔ ∃ t : ↥(LargeEvenSLGroup (Fin m) E), Ψ t = z := by
    intro z
    rw [hJPiff z]
    constructor
    · rintro ⟨t, ht, htSU, hz⟩
      exact ⟨⟨t, ht⟩, (hΨ ⟨t, ht⟩).trans hz⟩
    · rintro ⟨t, hz⟩
      exact ⟨t.1, t.2, hmem t.1 t.2, (hΨ t).symm.trans hz⟩
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin m) E)) := hsimple
  haveI : Group.IsPerfect ↥(LargeEvenSLGroup (Fin m) E) := Group.isPerfect_def.mpr hperfM
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSLGroup (Fin m) E)) :=
    Group.IsPerfect.ofSurjective (f := LargeEvenProjMk _) (QuotientGroup.mk'_surjective _)
  have hna : ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin m) E), a * b ≠ b * a := by
    have hnc := Group.IsPerfect.not_isMulCommutative
      (G := LargeEvenProj (LargeEvenSLGroup (Fin m) E))
    rw [isMulCommutative_iff] at hnc
    push Not at hnc
    exact hnc
  have hcenter : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin m) E)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin m) E))) with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm
  have hker : ∀ t : ↥(LargeEvenSLGroup (Fin m) E), Ψ t = 1 →
      LargeEvenProjMk (LargeEvenSLGroup (Fin m) E) t = 1 := by
    intro t ht
    have h1 : LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t.1, hmem t.1 t.2⟩ =
        LargeEvenProjMk (StatedSU d (2 ^ n) K) 1 := by
      rw [← hΨ t, ht, map_one]
    obtain ⟨z, hz⟩ := (projMk_eq_iff_uni (StatedSU d (2 ^ n) K)
      ⟨ι t.1, hmem t.1 t.2⟩ 1).1 h1
    have hz' : ι (t : GL (Fin m) E) = Matrix.GeneralLinearGroup.scalar (Fin d) z⁻¹ := by
      have e1 : Matrix.GeneralLinearGroup.scalar (Fin d) z⁻¹ =
          (Matrix.GeneralLinearGroup.scalar (Fin d) z)⁻¹ := map_inv _ z
      rw [e1, hz]
      simp
    obtain ⟨c, hc⟩ := hscal (t : GL (Fin m) E) z⁻¹ hz'
    refine (projMk_eq_iff_uni (LargeEvenSLGroup (Fin m) E) t 1).2 ⟨c⁻¹, ?_⟩
    rw [hc]
    simpa using (map_inv (Matrix.GeneralLinearGroup.scalar (Fin m)) c).symm
  obtain ⟨e₀, he₀⟩ := fniUni_centerQuot_equiv Ψ
    (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E))
    (QuotientGroup.mk'_surjective _) (ker_projMk_uni_le_center _) hcenter hker hJ
  haveI : (LargeEvenSLGroup (Fin m) E).Normal := by
    rw [largeEvenSLGroup_eq_statedSL (K := E) m]
    infer_instance
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  refine ⟨hJ₀, ⟨.A, r, k⟩, ?_, ?_⟩
  · change 1 ≤ k ∧ 1 ≤ r ∧ (r = 1 → 2 ≤ k)
    exact ⟨by omega, by omega, fun _ => hk2⟩
  · refine ⟨E, instE, finE, hcardE, hsimple, hna, e₀, ?_⟩
    rintro ⟨φ, hφcl, hind⟩
    have hI := RecipeFieldLinear.ggRawInnField_linear (K := E) (d := r + 1) (by omega)
      (Or.inr h4E) (p := 3) (by norm_num)
    obtain ⟨hmul, hinv, hconj, -⟩ := hI hsimple hna
    let H' : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) E))) :=
      { carrier := LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) E)) Set.univ
        one_mem' := by simpa using hconj 1
        mul_mem' := fun ha hb => hmul _ ha _ hb
        inv_mem' := fun ha => hinv _ ha }
    have hclosure : Subgroup.closure
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) E))
          Set.univ) ≤ H' := by
      rw [Subgroup.closure_le]
      exact fun x hx => by simpa [H'] using hx
    have hφI : φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) E)) Set.univ := by
      simpa [H'] using hclosure hφcl
    exact (fniUni_not_mem_of_line (J₀ := J₀) h σ hσmem hf f' hf' hperfM ι hmem hJPiff
      e₀ he₀ Set.univ
      (fun P _ t ht => (inferInstance : (LargeEvenSLGroup (Fin (r + 1)) E).Normal).conj_mem
        t ht P)
      N hN hc₁ hσc hline hind) hφI

theorem fniUni_neg_sl2 [Finite K] (h : UnitaryFieldData 2 n K) (σ : K ≃+* K)
    (hσmem : ∀ g ∈ StatedSU d (2 ^ n) K, glMap σ g ∈ StatedSU d (2 ^ n) K)
    {f : MulAut (StatedProj (StatedSU d (2 ^ n) K))}
    (hf : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = glMap σ (g : GL (Fin d) K) →
      f (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    {J₀ : Subgroup (StatedProj (StatedSU d (2 ^ n) K))} (hJ₀ : commutator ↥J₀ = ⊤)
    (f' : MulAut ↥J₀) (hf' : ∀ j : ↥J₀, (f' j : StatedProj (StatedSU d (2 ^ n) K)) = f j)
    {c₁ : K} (hc₁ : h.bar c₁ = c₁) (hσc : σ c₁ ≠ c₁) (hblock : L154BlockSL2 n d K h J₀) :
    LargeEvenMarking ↥J₀ fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : ↥J₀ => k = f' j) φ := by
  classical
  obtain ⟨F, instF, finF, k, ι, N, hk2, hcardF, hN, hinj, hline, hmem, hcen,
    hJPiff⟩ := hblock
  have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := k)
    (by rw [← Nat.card_eq_fintype_card]; exact hcardF)
  have hF2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h22 : (2 : ℕ) ≠ 2 ∨ Nat.card F ≠ 2 := Or.inr (by rw [hcardF]; omega)
  have h23 : (2 : ℕ) ≠ 2 ∨ Nat.card F ≠ 3 := Or.inr (by rw [hcardF]; omega)
  have hperfM : commutator ↥(StatedSL 2 F) = ⊤ :=
    Group.isPerfect_def.mp
      (CFSG.LieType.SemisimpleCentralizers.Held.hct_isPerfect_statedSL F le_rfl h22 h23)
  have hsimple : IsSimpleGroup (LargeEvenProj (StatedSL 2 F)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F le_rfl h22 h23
  let Ψ : ↥(StatedSL 2 F) →* StatedProj (StatedSU d (2 ^ n) K) :=
    (LargeEvenProjMk (StatedSU d (2 ^ n) K)).comp
      (ι.codRestrict (StatedSU d (2 ^ n) K) hmem)
  have hΨ : ∀ t : ↥(StatedSL 2 F),
      Ψ t = LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, hmem t⟩ := fun t => rfl
  have hJ : ∀ z : StatedProj (StatedSU d (2 ^ n) K),
      z ∈ J₀ ↔ ∃ t : ↥(StatedSL 2 F), Ψ t = z := by
    intro z
    rw [hJPiff z]
    constructor
    · rintro ⟨t, ht, hz⟩
      exact ⟨t, (hΨ t).trans hz⟩
    · rintro ⟨t, hz⟩
      exact ⟨t, hmem t, (hΨ t).symm.trans hz⟩
  haveI : IsSimpleGroup (LargeEvenProj (StatedSL 2 F)) := hsimple
  haveI : Group.IsPerfect ↥(StatedSL 2 F) := Group.isPerfect_def.mpr hperfM
  haveI : Group.IsPerfect (LargeEvenProj (StatedSL 2 F)) :=
    Group.IsPerfect.ofSurjective (f := LargeEvenProjMk _) (QuotientGroup.mk'_surjective _)
  have hna : ∃ a b : LargeEvenProj (StatedSL 2 F), a * b ≠ b * a := by
    have hnc := Group.IsPerfect.not_isMulCommutative (G := LargeEvenProj (StatedSL 2 F))
    rw [isMulCommutative_iff] at hnc
    push Not at hnc
    exact hnc
  have hcenter : Subgroup.center (LargeEvenProj (StatedSL 2 F)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (LargeEvenProj (StatedSL 2 F))) with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm
  have hker : ∀ t : ↥(StatedSL 2 F), Ψ t = 1 →
      LargeEvenProjMk (StatedSL 2 F) t = 1 := by
    intro t ht
    have h1 : LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨ι t, hmem t⟩ =
        LargeEvenProjMk (StatedSU d (2 ^ n) K) 1 := by
      rw [← hΨ t, ht, map_one]
    obtain ⟨z, hz⟩ := (projMk_eq_iff_uni (StatedSU d (2 ^ n) K) ⟨ι t, hmem t⟩ 1).1 h1
    have hz' : ι t = Matrix.GeneralLinearGroup.scalar (Fin d) z⁻¹ := by
      have e1 : Matrix.GeneralLinearGroup.scalar (Fin d) z⁻¹ =
          (Matrix.GeneralLinearGroup.scalar (Fin d) z)⁻¹ := map_inv _ z
      rw [e1, hz]
      simp
    have htcen := hcen t ⟨z⁻¹, hz'⟩
    rw [CFSG.GH74.L5U5.center_statedSL_eq (F := F) 2] at htcen
    exact (QuotientGroup.eq_one_iff t).2 htcen
  obtain ⟨e₀, he₀⟩ := fniUni_centerQuot_equiv Ψ (LargeEvenProjMk (StatedSL 2 F))
    (QuotientGroup.mk'_surjective _) (ker_projMk_uni_le_center _) hcenter hker hJ
  let f'q : MulAut (↥J₀ ⧸ Subgroup.center ↥J₀) :=
    QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥J₀) f'
      (Subgroup.characteristic_iff_map_eq.mp Subgroup.centerCharacteristic f')
  have hf'q : ∀ j : ↥J₀, f'q (QuotientGroup.mk j) = QuotientGroup.mk (f' j) :=
    fun j => QuotientGroup.congr_mk _ _ _ _ j
  have hφ0 : LargeEvenInduces e₀ (fun j k : ↥J₀ => k = f' j) (MulAut.congr e₀ f'q) := by
    intro j k hk
    subst hk
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hf'q]
  have hnot0 : MulAut.congr e₀ f'q ∉
      LargeEvenMatConjImage (LargeEvenProjMk (StatedSL 2 F)) Set.univ :=
    fniUni_not_mem_sl2 (J₀ := J₀) hF2 h σ hσmem hf f' hf' hperfM ι hmem hJPiff
      e₀ he₀ N hN hc₁ hσc hline hφ0
  obtain ⟨e, hnot⟩ := exists_notInner_of_eq (H := LargeEvenSLGroup (Fin 2) F)
    (largeEvenSLGroup_eq_statedSL (K := F) 2) f'q ⟨e₀, hnot0⟩
  have hperfL : commutator ↥(LargeEvenSLGroup (Fin 2) F) = ⊤ := by
    rw [largeEvenSLGroup_eq_statedSL (K := F) 2]
    exact hperfM
  have hsimpleL : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) := by
    rw [largeEvenSLGroup_eq_statedSL (K := F) 2]
    exact hsimple
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) := hsimpleL
  haveI : Group.IsPerfect ↥(LargeEvenSLGroup (Fin 2) F) := Group.isPerfect_def.mpr hperfL
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) :=
    Group.IsPerfect.ofSurjective (f := LargeEvenProjMk _) (QuotientGroup.mk'_surjective _)
  have hnaL : ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin 2) F), a * b ≠ b * a := by
    have hnc := Group.IsPerfect.not_isMulCommutative
      (G := LargeEvenProj (LargeEvenSLGroup (Fin 2) F))
    rw [isMulCommutative_iff] at hnc
    push Not at hnc
    exact hnc
  have h4F : 4 ≤ Nat.card F := by
    rw [hcardF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hI0 := RecipeFieldLinear.ggRawInnField_linear (K := F) (d := 2) le_rfl (Or.inr h4F)
    (p := 3) (by norm_num)
  refine ⟨hJ₀, ⟨.A, 1, k⟩, ?_, ?_⟩
  · change 1 ≤ k ∧ 1 ≤ 1 ∧ (1 = 1 → 2 ≤ k)
    exact ⟨by omega, le_rfl, fun _ => hk2⟩
  · refine ⟨F, instF, finF, hcardF, hsimpleL, hnaL, e, ?_⟩
    rintro ⟨φ, hφcl, hind⟩
    obtain ⟨hmul, hinv, hconj, -⟩ := hI0 hsimpleL hnaL
    let H' : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) F))) :=
      { carrier := LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) Set.univ
        one_mem' := by simpa using hconj 1
        mul_mem' := fun ha hb => hmul _ ha _ hb
        inv_mem' := fun ha => hinv _ ha }
    have hclosure : Subgroup.closure
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) Set.univ) ≤ H' := by
      rw [Subgroup.closure_le]
      exact fun x hx => by simpa [H'] using hx
    have hφI : φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) F)) Set.univ := by
      simpa [H'] using hclosure hφcl
    have hφeq : φ = MulAut.congr e f'q := by
      ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J₀) y
      change φ (e (QuotientGroup.mk j)) =
        (MulAut.congr e f'q) (e (QuotientGroup.mk j))
      have h1 : φ (e (QuotientGroup.mk j)) = e (QuotientGroup.mk (f' j)) :=
        hind j (f' j) rfl
      have h2 : MulAut.congr e f'q (e (QuotientGroup.mk j)) =
          e (QuotientGroup.mk (f' j)) := by
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hf'q]
      rw [h1, h2]
    rw [hφeq] at hφI
    exact hnot hφI

end CFSG.StandardType
