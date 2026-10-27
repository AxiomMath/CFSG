module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP8Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly

theorem P8a_jTag_inLambda2 {j : LargeEvenLabel} (hj : GGFrameJTag j) : LargeEvenInLambda2 j := by
  rcases hj with rfl | rfl | rfl | rfl <;> simp [LargeEvenInLambda2]

theorem P8a_jTag_rigid {j lab : LargeEvenLabel} (hj : GGFrameJTag j) (h : GGLabelIso lab j) :
    lab = j := by
  rcases lab with ⟨t, r, n⟩
  rcases hj with rfl | rfl | rfl | rfl <;>
    unfold GGLabelIso at h <;>
    simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false, false_or,
      and_true, true_and] at h ⊢ <;>
    simp_all

theorem P8b_fieldOne_marking (hTCJ : GGTCJKnown) (hRigid : GGLabelRigidInput)
    {K : Type} [Group K] [Finite K] (α : MulAut K) (hα : α ^ 3 = 1) (J : Subgroup K)
    (hJ : IsComponentOf J (ggFixSub α))
    (hJlab : ∃ j, GGFrameJTag j ∧ GGHasLabel j (J ⧸ Subgroup.center J))
    (P : LargeEvenMarkProp K)
    (hM : LargeEvenMarking K fun lab R _ I F θ => P lab R I F θ ∧ GGFrameInd I θ α) :
    LargeEvenMarking K fun lab R _ I F θ => P lab R I F θ ∧ GGFrameInd I θ α ∧ lab.n = 1 := by
  have hKperf : commutator K = ⊤ := hM.1
  have hM' := ggMarking_and_labelAll_dep
    (P' := fun lab => fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J' : Subgroup L', IsComponentOf J' (ggFixSub e) →
            ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
              GGHasLabel labJ (J' ⧸ Subgroup.center J'))
    (fun lab hlab => hTCJ 3 Nat.prime_three (by norm_num) lab hlab) hM
  refine largeEvenMarking_mono ?_ hM'
  intro lab R _ I F θ h
  obtain ⟨⟨hP, hInd⟩, hTC⟩ := h
  refine ⟨hP, hInd, ?_⟩
  let ψ : K →* R := (θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center K := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : K ⧸ Subgroup.center K) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hInd' : ∃ φ ∈ I, ∀ l : K, φ (ψ l) = ψ (α l) := by
    obtain ⟨φ, hφI, hφ⟩ := hInd
    exact ⟨φ, hφI, fun l => hφ l⟩
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ := hTC K ψ hψsurj hψker hKperf α hα hInd' J hJ
  obtain ⟨j, hj, hhasj⟩ := hJlab
  have hjeq : labJ = j :=
    P8a_jTag_rigid hj
      (hRigid labJ j (J ⧸ Subgroup.center J) hlabJ (P8a_jTag_inLambda2 hj) hhasJ hhasj)
  have hjn : j.n = 1 := by rcases hj with rfl | rfl | rfl | rfl <;> rfl
  have hdvd1 : lab.n ∣ 1 := by
    rw [← hjn, ← hjeq]
    exact hdvd
  exact Nat.dvd_one.mp hdvd1

theorem P8c_innerDiag_fieldOne (hTCJ : GGTCJKnown) (hRigid : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop} {Bs K J₁ : Subgroup G}
    {x : G} (hxBs : x ∈ Bs) (hx3 : x ^ 3 = 1) (hK : GGInnerDiagOnLabel S 3 Bs K)
    (hJK : J₁ ≤ K) (hJ₁ : IsComponentOf J₁ (K ⊓ Subgroup.centralizer ({x} : Set G)))
    (hJlab : ∃ j, GGFrameJTag j ∧ GGHasLabel j (J₁ ⧸ Subgroup.center J₁)) :
    GGInnerDiagOnLabel (fun p lab => S p lab ∧ lab.n = 1) 3 Bs K := by
  obtain ⟨_, _, _, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨_, hBsN, _⟩ := hP
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBsN hxBs
  have hα : K.normalizerMonoidHom ⟨x, hxN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [h1, map_one]
  obtain ⟨j, hj, hhasj⟩ := hJlab
  have hJlab' : ∃ j, GGFrameJTag j ∧
      GGHasLabel j ((J₁.subgroupOf K) ⧸ Subgroup.center (J₁.subgroupOf K)) :=
    ⟨j, hj, ggHasLabel_of_mulEquiv
      (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
        (Subgroup.map_center_eq _)).symm hhasj⟩
  let P : LargeEvenMarkProp ↥K := fun lab R _ I F θ =>
    S 3 lab ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
  have hM : LargeEvenMarking ↥K fun lab R _ I F θ => P lab R I F θ ∧
      GGFrameInd I θ (K.normalizerMonoidHom ⟨x, hxN⟩) := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP, ?_⟩) hK
    obtain ⟨φ, hφI, hφ⟩ := hP.2.2 x⁻¹ (Bs.inv_mem hxBs)
    refine ⟨φ, hφI, fun k => hφ k (K.normalizerMonoidHom ⟨x, hxN⟩ k) ?_⟩
    show ((K.normalizerMonoidHom ⟨x, hxN⟩ k : ↥K) : G) = (x⁻¹)⁻¹ * ((k : ↥K) : G) * x⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hM1 := P8b_fieldOne_marking hTCJ hRigid (K.normalizerMonoidHom ⟨x, hxN⟩) hα
    (J₁.subgroupOf K) (ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hJ₁) hJlab' P hM
  refine largeEvenMarking_mono (fun lab R _ I F θ h => ?_) hM1
  exact ⟨⟨h.1.1, h.2.2⟩, h.1.2.1, h.1.2.2⟩

end CFSG.StandardType.FrameRoute
