module

public import CFSG.RankThree.PartOne.K1214.XNorm
public import CFSG.RankThree.PartOne.K1214.Gen
public import CFSG.RankThree.PartOne.K1214.Trans
public import CFSG.RankThree.PartOne.K1214.HSyl
public import CFSG.RankThree.PartOne.K1214.CycCtx

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

theorem kf1214_normalizer_cyc (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes)
    (hU5 : KF1214U5) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
        Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
        (∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f) →
        P ≤ Subgroup.normalizer (E : Set G) ∧
          IsCyclic ↥(Subgroup.centralizer (I : Set G) ⊓ P) := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hgen
  obtain ⟨r, e, hr, he2, hEcard, ⟨φ⟩⟩ :=
    R_equiv hRig h112 ctx hL hC hF (hKR G p A c L E ctx b K I X P Q hL hC hF)
  have hn12 : ¬ RowModel p L 12 := hU5 G p A c L E ctx
  have hnH := not_dvd_torusImage ctx hn12
  have hQE := QE_of_gen ctx hF hC hgen
  have hPp := P_isPGroup hC
  have hFrame : ∀ U : Subgroup G, U ≤ Q ⊓ E →
      (∀ m ∈ Subgroup.normalizer ((P ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G),
        ∀ u ∈ U, m * u * m⁻¹ ∈ U) → U = ⊥ ∨ U = Q ⊓ E := by
    intro U hU hinv
    rw [hQE] at hU ⊢
    refine frame_inv_of_le ctx hnH hC.X_sylow.1 (T := P ⊓ Subgroup.normalizer (E : Set G))
      ?_ ?_ ?_ hU hinv
    · exact hPp.to_le inf_le_left
    · intro x hx
      obtain ⟨hyN, -⟩ := mem_xPreimage_iff.1 (hC.X_sylow.1.1 hx)
      exact ⟨hC.P_sylow.2 hx, hyN⟩
    · exact inf_le_right
  have h := cycBase_of_ctx h112 ctx hL hC hF hgen hr he2 hEcard φ
  exact ⟨h.le_normalizer hFrame, h.isCyclic_Z hFrame⟩

theorem kf1214Cyc_holds (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes)
    (hU5 : KF1214U5) : KF1214Cyc :=
  fun G _ _ p A c L E ctx b K I X P Q hL hC hF hgen =>
    (kf1214_normalizer_cyc h112 hRig hKR hU5 G p A c L E ctx b K I X P Q hL hC hF hgen).2

theorem kf1214Struct_holds (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes)
    (hU5 : KF1214U5) : KF1214Struct :=
  kf1214Struct_of_parts (kf1214Gen_of_h112 h112) (kf1214Cyc_holds h112 hRig hKR hU5)
      (kf1214Omega_of h112 hRig hKR) (kf1214Center_of_u5 hU5) (kf1214Trans_of_u5 hU5)
      (kf1214HSyl_of_u5 hU5)

end CFSG.RankThree.PartOne.K1214
