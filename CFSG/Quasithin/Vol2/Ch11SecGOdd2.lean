module

public import CFSG.Quasithin.Vol2.Ch11SecGEven

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G]

theorem mQuot_conjSub (x : G) (A B : Subgroup G) :
    E3.mQuot (conjSub x A) (conjSub x B) = E3.mQuot A B := by
  rw [conjSub_eq_conjSubgroup, conjSub_eq_conjSubgroup, E3.mQuot_conjSubgroup]

theorem mQuot_inf_left (A Y : Subgroup G) : E3.mQuot A (A ⊓ Y) = E3.mQuot A Y := by
  unfold E3.mQuot
  rw [Subgroup.inf_relIndex_left]

variable [Finite G]

theorem mQuot_le_of_le {A B Y : Subgroup G} (hAB : A ≤ B) (hB : IsPGroup 2 B) :
    E3.mQuot A Y ≤ E3.mQuot B Y := by
  have h1 := E3.relIndex_eq_two_pow (hB.to_le hAB) Y
  have h2 := E3.relIndex_eq_two_pow hB Y
  have h3 := Subgroup.relIndex_le_of_le_right hAB (E3.relIndex_ne_zero' B Y)
  rw [h1, h2] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

variable {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem mQuot_le_one_of_conjSub {V₁ H₁ : Subgroup G}
    (hsix : ∀ A : Subgroup G, A ≤ ROf T L V₁ → IsElemAbelian 2 A →
      E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≤ 1)
    {A : Subgroup G} {x : G} (hA : IsElemAbelian 2 A) (hAR : A ≤ conjSub x (ROf T L V₁)) :
    E3.mQuot A (A ⊓ conjSub x (pCoreOf 2 H₁)) ≤ 1 := by
  have hA' : conjSub x⁻¹ A ≤ ROf T L V₁ := by
    rw [conjSub_le_iff, inv_inv]
    exact hAR
  have h1 := hsix _ hA' (F7.isElemAbelian_conjSub hA)
  have h2 := mQuot_conjSub x (conjSub x⁻¹ A) (conjSub x⁻¹ A ⊓ pCoreOf 2 H₁)
  rw [conjSub_inf, conjSub_inv_conjSub] at h2
  rw [h2]
  exact h1

theorem le_centralizer_D (hCor : R1CorankFact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1122 : Stmt11_2_2) (h1141 : Stmt11_4_1) (h1151 : Stmt11_5_1) (h1155 : Stmt11_5_5)
    (h1157 : Stmt11_5_7) (h : Hyp11 G T L I n) {V₁ V₃ H₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃) (hinH : InH (LOf L V₁ ⊔ T) H₁)
    (hHM : ¬ H₁ ≤ Subgroup.normalizer (L : Set G))
    (hHN : H₁ ≤ Subgroup.normalizer (V₁ : Set G))
    (hsix : ∀ A : Subgroup G, A ≤ ROf T L V₁ → IsElemAbelian 2 A →
      E3.mQuot A (A ⊓ pCoreOf 2 H₁) ≤ 1)
    {g : G} (hbot : V₁ ⊓ conjSub g V₁ = ⊥)
    (hUg : ∃ k ∈ H₁, conjSub g (conjClosure (fsuV T I) H₁) ≤ conjSub k (ROf T L V₁))
    (hU : ∃ k ∈ H₁, conjClosure (fsuV T I) H₁ ≤ conjSub (g * k) (ROf T L V₁)) :
    conjSub g (conjClosure V₃ H₁) ⊓ pCoreOf 2 H₁ ≤ Subgroup.centralizer (fsuV T I : Set G) ∧
      E3.mQuot (conjSub g (conjClosure V₃ H₁))
        (conjSub g (conjClosure V₃ H₁) ⊓ pCoreOf 2 H₁) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := fsuV T I with hVdef
  set Q := pCoreOf 2 H₁ with hQdef
  set U := conjClosure V H₁ with hUdef
  set UH := conjClosure V₃ H₁ with hUHdef
  set D := conjSub g UH ⊓ Q with hDdef
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  have hkind := h1151 G T L I n h
  have hV₃V := SecA.IsVi.le_fsuV hV₃
  have hVel := SecA.isElemAbelian_fsuV h
  have hUel := isElemAbelian_U_of_le h1157 h hV₁ hHN
  have hU2 := F7.isPGroup_of_isElemAbelian hUel
  have hUHU : UH ≤ U := conjClosure_mono hV₃V le_rfl
  have hVU : V ≤ U := le_conjClosure _ _
  have hV₃U : V₃ ≤ U := hV₃V.trans hVU
  have hQR := pCoreOf_le_ROf_of_le h hinH.1
  have hQx : ∀ x ∈ H₁, conjSub x Q = Q := fun x hx =>
    F7.conjSub_eq_of_mem_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx)
  have hcomm : ⁅UH, Q⁆ ≤ V₁ := (h1155 G T L I n V₁ V₃ H₁ h hV₁ hV₃ hinH hHM hHN).2.1
  have hgQ : ⁅conjSub g Q, conjSub g UH⁆ ≤ conjSub g V₁ := by
    rw [conjSub_commutator, Subgroup.commutator_comm]
    exact conjSub_mono g hcomm
  obtain ⟨k, hk, hk'⟩ := hUg
  have hidx₂ : E3.mQuot (conjSub g UH) D ≤ 1 := by
    have h1 := mQuot_le_one_of_conjSub hsix
      (F7.isElemAbelian_conjSub (F7.isElemAbelian_mono hUel hUHU))
      ((conjSub_mono g hUHU).trans hk')
    rwa [hQx k hk] at h1
  obtain ⟨k₁, hk₁, hUk₁⟩ := hU
  have hidx₁ : E3.mQuot U (U ⊓ conjSub g Q) ≤ 1 := by
    have h1 := mQuot_le_one_of_conjSub hsix hUel hUk₁
    rwa [conjSub_mul, hQx k₁ hk₁] at h1
  set X₀ := U ⊓ conjSub g Q ⊓ UH with hX₀def
  have hX₀D : ⁅X₀, D⁆ = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    refine le_inf ((Subgroup.commutator_mono inf_le_right inf_le_right).trans hcomm) ?_
    exact (Subgroup.commutator_mono (inf_le_left.trans inf_le_right) inf_le_left).trans hgQ
  have hDX₀ : D ≤ Subgroup.centralizer (X₀ : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hX₀D)
  set B₃ := V₃ ⊓ conjSub g Q with hB₃def
  have hB₃X : B₃ ≤ X₀ :=
    le_inf (le_inf (inf_le_left.trans hV₃U) inf_le_right) (inf_le_left.trans (le_conjClosure _ _))
  have hB₃idx : E3.mQuot V₃ B₃ ≤ 1 := by
    rw [mQuot_inf_left]
    calc E3.mQuot V₃ (conjSub g Q) ≤ E3.mQuot U (conjSub g Q) := mQuot_le_of_le hV₃U hU2
      _ = E3.mQuot U (U ⊓ conjSub g Q) := (mQuot_inf_left U _).symm
      _ ≤ 1 := hidx₁
  have hVD : ⁅V, D⁆ ≤ V₁ := hCor G T L I n V₁ V₃ hset hkind hV₁ hV₃ D B₃
    (inf_le_right.trans hQR) inf_le_left hB₃idx (hDX₀.trans (Subgroup.centralizer_le hB₃X))
  set B := V ⊓ conjSub g Q with hBdef
  have hBD : ⁅B, D⁆ = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    refine le_inf ((Subgroup.commutator_mono inf_le_left le_rfl).trans hVD) ?_
    exact (Subgroup.commutator_mono inf_le_right inf_le_left).trans hgQ
  have hDB : D ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBD)
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  have hn := h.one_lt
  have hs : 1 < E3.sParam hVel := by
    by_cases hG2 : KindG2 L V n
    · have h1 := (h1122 G T L I n (2 * n) V₁ V₂ h hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)).2.2.2.1 hVel
      omega
    · have h1 := (h1122 G T L I n n V₁ V₂ h hV₁ hV₂ (Or.inr ⟨hG2, rfl⟩)).2.2.2.1 hVel
      omega
  have hBidx : E3.mQuot V B < E3.sParam hVel := by
    rw [mQuot_inf_left]
    have h1 : E3.mQuot V (conjSub g Q) ≤ E3.mQuot U (conjSub g Q) := mQuot_le_of_le hVU hU2
    rw [← mQuot_inf_left U] at h1
    omega
  have hD2 : IsPGroup 2 D := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₁).to_le inf_le_right
  have he36 := (E3.e3_6 hVel (A := V) (B := B) (E := D) inf_le_left le_rfl hBidx hD2).2
  refine ⟨?_, hidx₂⟩
  calc D ≤ D ⊓ Subgroup.centralizer (B : Set G) := le_inf le_rfl hDB
    _ = D ⊓ Subgroup.centralizer (V : Set G) := he36
    _ ≤ Subgroup.centralizer (V : Set G) := inf_le_right

end CFSG.Quasithin.Vol2.Ch11.SecG
