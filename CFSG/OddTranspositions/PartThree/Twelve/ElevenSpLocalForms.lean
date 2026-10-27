module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpLocal
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpArith
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpLocalIso
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpPencil
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelChart
import CFSG.OddTranspositions.PartThree.Twelve.SevenForm
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import CFSG.RankThree.PartOne.AUTSL.TraceASApply

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.AUTSL
open QuadraticMap

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D} {B : SpBranch hC}
  {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

private theorem exists_sq_add_sq_eq_of_mem_artinSchreier_range {K : Type} [Field K] [Fintype K]
    [CharP K 2] {A₀ : K} (hA₀ : A₀ ∈ (artinSchreierHom (K := K)).range) :
    ∃ s₀ : K, s₀ ^ 2 + s₀ = A₀ ^ 2 := by
  obtain ⟨s₀, hs₀⟩ := AddMonoidHom.mem_range.mp ((sq_mem_range_artinSchreier_iff A₀).mpr hA₀)
  exact ⟨s₀, by rw [← hs₀, artinSchreierHom_apply, pow_two]⟩

omit [Finite G] [Fintype F] [DecidableEq F] in
private theorem commute_of_spCoord_root {c : SpChart hC B.hα k F}
    {e : ↥(Halpha D hC.alpha) ≃* (↥(StatedSp k F) × Multiplicative (ZMod 2))}
    (he1 : ∀ h, (e h).1 = c.ρ h) {v : G} (hv : v ∈ commSet D hC.d) {s : F}
    {h r : ↥(Halpha D hC.alpha)}
    (hh : e h = (spTransvection (c.vec v) s, Multiplicative.ofAdd 1))
    (hr : Commute (r : G) v) : Commute h r := by
  have hρ : spEnd (c.ρ r) (c.vec v) = c.vec v := by
    have h1 := (SpChart.vec_conj c r hv).2
    rw [hr.eq, mul_assoc, mul_inv_cancel, mul_one] at h1
    exact h1.symm
  have hT : c.ρ r * spTransvection (c.vec v) s * (c.ρ r)⁻¹ =
      spTransvection (c.vec v) s := by
    rw [CFSG.RankThree.PartOne.CTP.spTransvection_conj, hρ]
  have hcomm : Commute (c.ρ r) (spTransvection (c.vec v) s) := by
    have h2 : c.ρ r * spTransvection (c.vec v) s =
        spTransvection (c.vec v) s * c.ρ r := by
      calc c.ρ r * spTransvection (c.vec v) s
          = (c.ρ r * spTransvection (c.vec v) s * (c.ρ r)⁻¹) * c.ρ r := by group
        _ = spTransvection (c.vec v) s * c.ρ r := by rw [hT]
    exact h2
  have hpair : Commute (e h) (e r) := by
    rw [hh]
    show (spTransvection (c.vec v) s, (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))) *
        e r = e r * (spTransvection (c.vec v) s, Multiplicative.ofAdd 1)
    apply Prod.ext
    · show spTransvection (c.vec v) s * (e r).1 =
        (e r).1 * spTransvection (c.vec v) s
      rw [he1 r]
      exact hcomm.symm
    · exact mul_comm _ _
  exact Commute.of_map e.injective hpair

omit [Fintype F] [DecidableEq F] in
private theorem mStabForm_conj_root {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {w : MSpace k F} {τ : MGroup Q₀}
    {a_v : Fin k ⊕ Fin k → F} {s : F}
    (hτ : τ ∈ Subgroup.centralizer ({mRefl Q₀ mU} : Set (MGroup Q₀)))
    (hβw : w.1.2 ≠ 0)
    (hτlin : ∀ x, ((τ : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2 =
      spEnd (spTransvection a_v s) x)
    (hy : mStabForm Q₀ w a_v = 1) :
    ∀ a, mStabForm Q₀ ((τ : MSpace k F ≃ₗ[F] MSpace k F) w) a =
      mStabForm Q₀ w a + (s ^ 2 + s) * spForm k F a a_v ^ 2 := by
  intro a
  have hτfix : (τ : MSpace k F ≃ₗ[F] MSpace k F) mU = mU :=
    (mem_centralizer_mRefl_mU_iff hQ₀ τ).mp hτ
  have hβY : ((τ : MSpace k F ≃ₗ[F] MSpace k F) w).1.2 ≠ 0 := by
    have hpol : ((τ : MSpace k F ≃ₗ[F] MSpace k F) w).1.2 =
        polar (mForm Q₀) mU ((τ : MSpace k F ≃ₗ[F] MSpace k F) w) :=
      (polar_mU_eq_snd _).symm
    rw [hpol, ← hτfix]
    rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup τ.2]
    rw [polar_mForm hQ₀]
    simpa [mU] using hβw
  have h1 := mStabForm_apply_eq_of_mem_centralizer hQ₀ hβw hτ
    (spEnd (spTransvection a_v s) a)
  rw [hτlin] at h1
  have hlin : spForm k F (a + (s * spForm k F a a_v) • a_v) a_v = spForm k F a a_v := by
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, mul_zero, add_zero]
  have hT2 : spEnd (spTransvection a_v s) (spEnd (spTransvection a_v s) a) = a := by
    rw [spEnd_spTransvection, spEnd_spTransvection, hlin, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  rw [hT2] at h1
  rw [h1, mStabForm_spEnd_spTransvection hQ₀ s hy a]


omit [DecidableEq F] in
private lemma exists_root_element (c : SpChart hC B.hα k F) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    {A₀ : F} (hA₀mem : A₀ ∈ (artinSchreierHom (K := F)).range) :
    ∃ (s₀ : F) (τ : MGroup Q₀),
      s₀ ^ 2 + s₀ = A₀ ^ 2 ∧
      τ ∈ Subgroup.centralizer ({mRefl Q₀ mU} : Set (MGroup Q₀)) ∧
      (∀ x, ((τ : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2 =
        spEnd (spTransvection (c.vec (hC.conj g).d) s₀) x) ∧
      Commute τ (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))) ∧
      ∀ r : ↥(Halpha D hC.alpha), Commute (r : G) (hC.conj g).d →
        Commute τ (θ r : MGroup Q₀) := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_sq_add_sq_eq_of_mem_artinSchreier_range hA₀mem
  obtain ⟨hu', e, he1, he2, he3⟩ := exists_spCoord (B := B) c
  let a_v : Fin k ⊕ Fin k → F := c.vec (hC.conj g).d
  let hτ : ↥(Halpha D hC.alpha) :=
    e.symm (spTransvection a_v s₀, Multiplicative.ofAdd 1)
  have hehτ : e hτ = (spTransvection a_v s₀, Multiplicative.ofAdd 1) := by
    simp [hτ]
  have hρhτ : c.ρ hτ = spTransvection a_v s₀ := by
    have h := congrArg Prod.fst hehτ
    simpa [he1 hτ] using h
  let θhτ : ↥(Subgroup.centralizer {mRefl Q₀ mU}) := θ hτ
  let τ : MGroup Q₀ := θhτ
  have hτU : τ ∈ Subgroup.centralizer ({mRefl Q₀ mU} : Set (MGroup Q₀)) := θhτ.2
  have hτcomm : ∀ r : ↥(Halpha D hC.alpha), Commute (r : G) (hC.conj g).d →
      Commute τ (θ r : MGroup Q₀) := by
    intro r hrv
    have h1 : Commute hτ r := commute_of_spCoord_root (B := B) (c := c) he1 hv hehτ hrv
    have h2 : Commute (θ hτ) (θ r) := h1.map θ.toMonoidHom
    exact congrArg Subtype.val h2
  have hτlin : ∀ x, ((τ : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2 =
      spEnd (spTransvection a_v s₀) x := by
    intro x
    rw [← hθ.1 hτ x, hρhτ]
  have hvH : (hC.conj g).d ∈ Halpha D hC.alpha :=
    mem_Halpha_of_mem_commSet hC B.hα hv
  have hcommV : Commute τ (mRefl Q₀ (mLift Q₀ a_v)) := by
    have h1 := hτcomm ⟨(hC.conj g).d, hvH⟩ (Commute.refl _)
    rw [hθ.2.2 _ hv] at h1
    simpa [a_v] using h1
  exact ⟨s₀, τ, hs₀, hτU, hτlin, hcommV, hτcomm⟩

omit [DecidableEq F] in
private lemma local_iso_form_vector (c : SpChart hC B.hα k F) (g : G)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)} {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)} {τ : MGroup Q₀}
    {ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    {ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hψ : ∀ h, (ψ h : MGroup Q₀) = τ * (ψ₁ h : MGroup Q₀) * τ⁻¹)
    (hψz : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) =
        mRefl Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z))))) :
    ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      mForm Q₀ ((τ : MSpace k F ≃ₗ[F] MSpace k F)
          (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z))))) = 1 ∧
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) =
        mRefl Q₀ ((τ : MSpace k F ≃ₗ[F] MSpace k F)
          (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z))))) := by
  intro z hz
  let w : MSpace k F := γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z)))
  have hwψ : (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
      MGroup Q₀) = mRefl Q₀ w := hψz z hz
  have hYψ : (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
      MGroup Q₀) = mRefl Q₀ ((τ : MSpace k F ≃ₗ[F] MSpace k F) w) := by
    rw [hψ, hwψ]
    apply Subtype.ext
    change (τ : MSpace k F ≃ₗ[F] MSpace k F) * reflect (mForm Q₀) w *
        (τ : MSpace k F ≃ₗ[F] MSpace k F)⁻¹ =
      reflect (mForm Q₀) ((τ : MSpace k F ≃ₗ[F] MSpace k F) w)
    exact reflect_conj τ.2 w
  have hYform : mForm Q₀ ((τ : MSpace k F ≃ₗ[F] MSpace k F) w) = 1 := by
    have h1 : mForm Q₀ ((τ : MSpace k F ≃ₗ[F] MSpace k F) w) = mForm Q₀ w :=
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup τ.2 w
    rw [h1]
    show mForm Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z)))) = 1
    rw [hγ]
    exact mForm_mLift (Q₀ := Q₀) (A ((SpChart.conj (B := B) c g).vec z))
  exact ⟨hYform, hYψ⟩

omit [DecidableEq F] in
private theorem second_eq_spForm {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {γ : MSpace k F ≃ₗ[F] MSpace k F} (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    {y' : Fin k ⊕ Fin k → F} (hγy' : γ (mLift Q₀ y') = mU)
    (a : Fin k ⊕ Fin k → F) :
    (γ (mLift Q₀ a)).1.2 = spForm k F y' a := by
  have hpol : (γ (mLift Q₀ a)).1.2 = polar (mForm Q₀) mU (γ (mLift Q₀ a)) :=
    (polar_mU_eq_snd _).symm
  rw [hpol, ← hγy']
  rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hγ)]
  rw [polar_mForm hQ₀]
  simp [mLift]

omit [DecidableEq F] in
private lemma mStabForm_eq_formOfLine (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    {σ : F ≃+* F} {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {y' : Fin k ⊕ Fin k → F}
    (hAform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z))
    (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hγy' : γ (mLift Q₀ y') = mU) (hAy : A (cv.vec hC.d) = y')
    {A₀ : F} (hA₀form : ∀ x ∈ commSet D (hC.conj g).d, ¬ Commute x hC.d →
      ∀ Q, IsFormOfLine c Q x → ∀ a,
        Q a = mStabForm Q₀ (γ (mLift Q₀ (A (cv.vec x)))) a +
          (A₀ * spForm k F (c.vec (hC.conj g).d) a) ^ 2)
    {s₀ : F} (hs₀ : s₀ ^ 2 + s₀ = A₀ ^ 2) {τ : MGroup Q₀}
    (hτU : τ ∈ Subgroup.centralizer ({mRefl Q₀ mU} : Set (MGroup Q₀)))
    (hτlin : ∀ x, ((τ : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2 =
      spEnd (spTransvection (c.vec (hC.conj g).d) s₀) x) :
    ∀ z, z ∈ commSet D (hC.conj g).d → ¬ Commute z hC.d →
      ∀ Q, IsFormOfLine c Q z → ∀ a,
        Q a = mStabForm Q₀ ((τ : MSpace k F ≃ₗ[F] MSpace k F)
          (γ (mLift Q₀ (A (cv.vec z))))) a := by
  intro z hz hzd Q hQ
  obtain ⟨hQpol, hQline⟩ := hQ
  let w : MSpace k F := γ (mLift Q₀ (A (cv.vec z)))
  have hvz : (hC.conj g).d ∈ commSet D z := ⟨hv.1, hz.2.1.symm, hz.2.2.symm⟩
  have hQav : Q (c.vec (hC.conj g).d) = 1 := (hQline _ hv).mp hvz
  have hd_in : hC.d ∈ commSet D (hC.conj g).d := ⟨hC.hd, hv.2.1.symm, hv.2.2.symm⟩
  have hsp : spForm k F (cv.vec hC.d) (cv.vec z) ≠ 0 := by
    intro h0
    exact hzd ((cv.commute_iff hC.d hd_in z hz).mpr h0).symm
  have hsp' : spForm k F y' (A (cv.vec z)) ≠ 0 := by
    rw [← hAy, hAform]
    exact fun h0 => hsp (σ.injective (by rw [h0, map_zero]))
  have hβw : w.1.2 ≠ 0 := by
    rw [second_eq_spForm hQ₀ hγ hγy']
    exact hsp'
  have hSw : mStabForm Q₀ w (c.vec (hC.conj g).d) = 1 := by
    have h0 := hA₀form z hz hzd Q ⟨hQpol, hQline⟩ (c.vec (hC.conj g).d)
    rw [hQav, spForm_isAlt.self_eq_zero] at h0
    simpa using h0.symm
  have hstab := mStabForm_conj_root (Q₀ := Q₀) hQ₀ hτU hβw hτlin hSw
  have hsymm : ∀ a, spForm k F a (c.vec (hC.conj g).d) =
      spForm k F (c.vec (hC.conj g).d) a := by
    intro a
    have h := (spForm_isAlt (r := k) (K := F)).neg_eq a (c.vec (hC.conj g).d)
    rwa [CharTwo.neg_eq] at h
  intro a
  rw [hA₀form z hz hzd Q ⟨hQpol, hQline⟩ a, hstab a, hsymm a, hs₀]
  ring

private theorem exists_psi_eq_of_mem_commSet_mRefl (c : SpChart hC B.hα k F) {g : G}
    (hk : 2 ≤ k) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {ψ₁ ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    {τ : MGroup Q₀}
    (hψ : ∀ h, (ψ h : MGroup Q₀) = τ * (ψ₁ h : MGroup Q₀) * τ⁻¹)
    (hcommV : Commute τ (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))))
    (hψonto : ∀ m ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))),
      ∃ z, ∃ hz : z ∈ commSet D (hC.conj g).d,
        (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) = m) :
    ∀ m ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))),
      ∃ z, ∃ hz : z ∈ commSet D (hC.conj g).d,
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) = m := by
  intro m hm
  have hm' : τ⁻¹ * m * τ ∈
      commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))) := by
    have h := conj_mem_commSet_of_commute (D := mClass Q₀)
      (x := mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))) (g := τ⁻¹)
      (setup_mClass hQ₀ hk).normal hcommV.inv_left hm
    simpa [inv_inv] using h
  obtain ⟨z, hz, hψz'⟩ := hψonto (τ⁻¹ * m * τ) hm'
  refine ⟨z, hz, ?_⟩
  rw [hψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩, hψz']
  group

omit [DecidableEq F] in
private theorem exists_mRefl_and_mStabForm_eq (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    {σ : F ≃+* F} {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {y' : Fin k ⊕ Fin k → F}
    {ψ₁ ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    {τ : MGroup Q₀}
    (hψ : ∀ h, (ψ h : MGroup Q₀) = τ * (ψ₁ h : MGroup Q₀) * τ⁻¹)
    (hψz : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) =
        mRefl Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z)))))
    (hAform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z))
    (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hγy' : γ (mLift Q₀ y') = mU) (hAy : A ((SpChart.conj (B := B) c g).vec hC.d) = y')
    {A₀ : F} (hA₀form : ∀ x ∈ commSet D (hC.conj g).d, ¬ Commute x hC.d →
      ∀ Q, IsFormOfLine c Q x → ∀ a,
        Q a = mStabForm Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec x)))) a +
          (A₀ * spForm k F (c.vec (hC.conj g).d) a) ^ 2)
    {s₀ : F} (hs₀ : s₀ ^ 2 + s₀ = A₀ ^ 2)
    (hτU : τ ∈ Subgroup.centralizer ({mRefl Q₀ mU} : Set (MGroup Q₀)))
    (hτlin : ∀ x, ((τ : MSpace k F ≃ₗ[F] MSpace k F) ((0, 0), x)).2 =
      spEnd (spTransvection (c.vec (hC.conj g).d) s₀) x) :
    ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d, ∃ Y : MSpace k F,
      mForm Q₀ Y = 1 ∧
      (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
        MGroup Q₀) = mRefl Q₀ Y ∧
      (¬ Commute z hC.d → ∀ z', z' ∈ commSet D hC.d →
        (z' ∈ commSet D z ↔ mStabForm Q₀ Y (c.vec z') = 1)) := by
  intro z hz
  obtain ⟨hYform, hYψ⟩ :=
    local_iso_form_vector (B := B) c g hγ hψ hψz z hz
  refine ⟨(τ : MSpace k F ≃ₗ[F] MSpace k F)
    (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z)))), hYform, hYψ, ?_⟩
  intro hzd z' hz'
  obtain ⟨Q, hQpol, hQline, -⟩ :=
    exists_quadraticForm_commSet_inter B.hIH hC B.hMZ B.hα B.hs B.hn B.hf B.hSp c hnk hF
      hv hz.1 hzd hz.2.1
  have hQY := mStabForm_eq_formOfLine (B := B) c hQ₀ g hv
    (SpChart.conj (B := B) c g) hAform hγ hγy' hAy hA₀form hs₀ hτU hτlin z hz hzd Q
    ⟨hQpol, hQline⟩
  rw [hQline z' hz', hQY (c.vec z')]

theorem exists_local_iso_forms_eq (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (hQ₀ty : ∃ w₀ : G, w₀ ∈ D ∧ (lineMem D hC.d w₀).ncard = 2 ^ B.f - 1 ∧
      IsFormOfLine c Q₀ w₀) :
    ∃ ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
        ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}),
      (∀ (r : ↥(Halpha D hC.alpha)), ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
        (ψ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀)) ∧
      (∀ m ∈ commSet (mClass Q₀) (mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))),
        ∃ z, ∃ hz : z ∈ commSet D (hC.conj g).d,
          (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) = m) ∧
      ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d, ∃ Y : MSpace k F,
        mForm Q₀ Y = 1 ∧
        (ψ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
          MGroup Q₀) = mRefl Q₀ Y ∧
        (¬ Commute z hC.d → ∀ z', z' ∈ commSet D hC.d →
          (z' ∈ commSet D z ↔ mStabForm Q₀ Y (c.vec z') = 1)) := by
  obtain ⟨σ, A, γ, y', ψ₁, _, hAadd, hAsmul, hAform, hγ, hγU, _, hγy', hAy, hψθ, hψz,
      hψonto⟩ :=
    exists_semilinear_localIso c hnk hF hQ₀ hθ g hv
  obtain ⟨A₀, hA₀mem, hA₀form⟩ :=
    exists_formOfLine_eq_mStabForm_add_sq c hnk hF hQ₀ hθ g hv hQ₀ty
      hAadd hAsmul hAform hγ hγU hψθ hψz
  obtain ⟨s₀, τ, hs₀, hτU, hτlin, hcommV, hτcomm⟩ :=
    exists_root_element (B := B) c g hv hθ hA₀mem
  have hτV₀ : τ ∈ Subgroup.centralizer
      ({mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))} : Set (MGroup Q₀)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcommV.eq
  let ψ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))}) :=
    ψ₁.trans (MulAut.conj ⟨τ, hτV₀⟩)
  have hψ : ∀ h, (ψ h : MGroup Q₀) = τ * (ψ₁ h : MGroup Q₀) * τ⁻¹ := fun _ => rfl
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro r hr
    have hrv : Commute (r : G) (hC.conj g).d :=
      commute_d_of_mem_Halpha (hC.conj g) (B.conj g).hα ⟨r, hr⟩
    have hcomm := hτcomm r hrv
    rw [hψ ⟨r, hr⟩, hψθ r hr, hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  · exact exists_psi_eq_of_mem_commSet_mRefl (B := B) c (B.two_le_rank hnk) hQ₀ hψ hcommV
      hψonto
  · exact exists_mRefl_and_mStabForm_eq (B := B) c hnk hF hQ₀ hv hψ hψz hAform hγ
      hγy' hAy hA₀form hs₀ hτU hτlin

end CFSG.OddTranspositions.PartThree.ElevenSp

end
