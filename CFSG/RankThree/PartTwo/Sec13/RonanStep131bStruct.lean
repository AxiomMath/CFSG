module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem struct_holds : PieceStruct := by
  unfold PieceStruct
  intro G _ _ A c L E h
  obtain ⟨hD, hSL2, -, hEle, hEe, hE27, hEC, hEL, -⟩ := h
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : Item131bProof.HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨hcE, -, -, hsup⟩ :=
    Item131bProof.e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hAL : A ⊓ L ≤ Subgroup.zpowers c := Res2Proof.inf_le_zpowers_of_isSLThreePiTwo hD hSL2
  have hAN : A ≤ Subgroup.normalizer (E : Set G) :=
    Item131bProof.le_normalizer_of_heis hD hAL (hEle.trans inf_le_right) hcE hsup
  refine ⟨hcE, ?_, hAN⟩
  have hAC := Item131bProof.inf_thetaQuotCentralizer_eq hD
  have hEW : E ≤ Subgroup.normalizer (A : Set G) := hEle.trans inf_le_right
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcE' : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.mpr hcE
  intro a ha
  have haL : a ∈ Subgroup.normalizer (L : Set G) := hD.le_normalizer ha
  have hcomm_mem : ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ A := fun e he => by
    have h1 : e * a⁻¹ * e⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hEW he) _).mp (inv_mem ha)
    have h2 : a * e * a⁻¹ * e⁻¹ = a * (e * a⁻¹ * e⁻¹) := by group
    rw [h2]
    exact mul_mem ha h1
  have hgenC : ∀ d ∈ E ⊓ Sec4.thetaQuotCentralizer L, a * d * a⁻¹ * d⁻¹ ∈ Subgroup.zpowers c := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Subgroup.mem_inf.mp hd
    have hx : a * d * a⁻¹ * d⁻¹ ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
      Subgroup.mem_inf.mpr ⟨hcomm_mem d hd1,
        mul_mem (Sec12.conj_mem_thetaQuotCentralizer haL hd2) (inv_mem hd2)⟩
    rwa [hAC] at hx
  have hgenL : ∀ l ∈ E ⊓ L, a * l * a⁻¹ * l⁻¹ ∈ Subgroup.zpowers c := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := Subgroup.mem_inf.mp hl
    have hlL : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL l).mp hl2
    have hx : a * l * a⁻¹ * l⁻¹ ∈ A ⊓ L :=
      Subgroup.mem_inf.mpr ⟨hcomm_mem l hl1, mul_mem hlL (inv_mem hl2)⟩
    exact hAL hx
  have hac : a * c = c * a := by
    have := hD.commute ha hD.mem_A
    exact this
  have hcc : ∀ e ∈ E, ∀ k : ℤ, e * c ^ k * e⁻¹ = c ^ k := fun e he k => by
    have h : Commute e c := hEcomm e he c hcE
    have h2 := (h.zpow_right k).eq
    calc e * c ^ k * e⁻¹ = c ^ k * e * e⁻¹ := by rw [h2]
      _ = c ^ k := by group
  let S : Subgroup G :=
    { carrier := {e | e ∈ E ∧ a * e * a⁻¹ * e⁻¹ ∈ Subgroup.zpowers c}
      mul_mem' := by
        rintro e₁ e₂ ⟨he₁, h₁⟩ ⟨he₂, h₂⟩
        refine ⟨mul_mem he₁ he₂, ?_⟩
        obtain ⟨k₂, hk₂⟩ := Subgroup.mem_zpowers_iff.mp h₂
        have h3 : a * (e₁ * e₂) * a⁻¹ * (e₁ * e₂)⁻¹ =
            (a * e₁ * a⁻¹ * e₁⁻¹) * (e₁ * (a * e₂ * a⁻¹ * e₂⁻¹) * e₁⁻¹) := by group
        rw [h3, ← hk₂, hcc e₁ he₁ k₂]
        exact mul_mem h₁ (Subgroup.zpow_mem_zpowers c k₂)
      one_mem' := ⟨one_mem E, by simp⟩
      inv_mem' := by
        rintro e ⟨he, h⟩
        refine ⟨inv_mem he, ?_⟩
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
        have h3 : a * e⁻¹ * a⁻¹ * (e⁻¹)⁻¹ = e⁻¹ * (a * e * a⁻¹ * e⁻¹)⁻¹ * e := by group
        rw [h3, ← hk, ← zpow_neg]
        have h4 := hcc e⁻¹ (inv_mem he) (-k)
        rw [inv_inv] at h4
        rw [h4]
        exact Subgroup.zpow_mem_zpowers c _ }
  have hP : E ≤ S := by
    rw [← hsup]
    exact sup_le (fun d hd => ⟨hd.1, hgenC d hd⟩) (fun l hl => ⟨hl.1, hgenL l hl⟩)
  intro e he
  exact (hP he).2

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
