module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCfg
public import CFSG.Open.GeneralizedFittingSelfCentralizing
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFive
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWN2
import CFSG.GH74.Uniqueness.Section4Lemma45

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {Q : Type} [Group Q] [Finite Q] {T A B R L₀ : Subgroup Q}

theorem Cfg813.fitting_odd (h : Cfg813 T A B R L₀) : Odd (Nat.card (genFittingFitting Q)) := by
  classical
  set F := genFittingFitting Q with hF
  by_contra hodd
  have heven : Even (Nat.card F) := Nat.not_odd_iff_even.mp hodd
  have h2dvd : 2 ∣ Nat.card F := even_iff_two_dvd.mp heven
  have hFnil : Group.IsNilpotent F := by
    rw [hF]
    change Group.IsNilpotent ↥(CFSG.fittingSubgroup Q)
    infer_instance
  haveI : Group.IsNilpotent F := hFnil
  let P : Sylow 2 ↥F := Classical.arbitrary _
  have hPne : (P : Subgroup ↥F) ≠ ⊥ := P.ne_bot_of_dvd_card h2dvd
  have hPchar : (P : Subgroup ↥F).Characteristic :=
    P.characteristic_of_normal (inferInstance : P.Normal)
  haveI : (P : Subgroup ↥F).Characteristic := hPchar
  have hFnormal : F.Normal := by
    rw [hF]
    change (CFSG.fittingSubgroup Q).Normal
    infer_instance
  haveI : F.Normal := hFnormal
  have hmapNormal : ((P : Subgroup ↥F).map F.subtype).Normal := inferInstance
  have hmapNe : ((P : Subgroup ↥F).map F.subtype) ≠ ⊥ := by
    intro hbot
    exact hPne ((Subgroup.map_eq_bot_iff_of_injective (P : Subgroup ↥F)
      (f := F.subtype) F.subtype_injective).mp hbot)
  exact hmapNe (h.no_normal_two _ hmapNormal (P.isPGroup'.map F.subtype))

theorem Cfg813.fitting_commute (h : Cfg813 T A B R L₀) :
    ∀ a ∈ A, ∀ y ∈ genFittingFitting Q, a * y = y * a := by
  classical
  set F := genFittingFitting Q with hF
  have hFodd : Odd (Nat.card F) := by
    rw [hF]
    exact h.fitting_odd
  have hFnormal : F.Normal := by
    rw [hF]
    change (CFSG.fittingSubgroup Q).Normal
    infer_instance
  have hFA : A ≤ Subgroup.normalizer (F : Set Q) := Subgroup.le_normalizer_of_normal
  obtain ⟨p, hpA, hp1, v, hvA, hv1, hpv⟩ := Five.exists_two_ne_one h.A_card
  have hp2 : p * p = 1 := by simpa [pow_two] using h.A_elem.2 p hpA
  have hv2 : v * v = 1 := by simpa [pow_two] using h.A_elem.2 v hvA
  have hcommpv : p * v = v * p :=
    congrArg Subtype.val (h.A_elem.1.is_comm.comm ⟨p, hpA⟩ ⟨v, hvA⟩)
  have hcover : F ≤ (F ⊓ Subgroup.centralizer ({p} : Set Q)) ⊔
      (F ⊓ Subgroup.centralizer ({v} : Set Q)) ⊔
      (F ⊓ Subgroup.centralizer ({p * v} : Set Q)) :=
    CFSG.ComponentClassification.GrSLit.FW.le_sup_inf_centralizer_of_four hFodd hp2 hv2
      hcommpv hp1 hv1 hpv (hFA hpA) (hFA hvA)
  have hpv1 : p * v ≠ 1 := by
    intro hcon
    apply hpv
    have h2 : p * v * v = 1 * v := by rw [hcon]
    rwa [mul_assoc, hv2, mul_one, one_mul] at h2
  have hgen : ∀ b ∈ A, ∀ c ∈ A, c ≠ 1 →
      F ⊓ Subgroup.centralizer ({c} : Set Q) ≤ Subgroup.centralizer ({b} : Set Q) := by
    intro b hbA c hcA hc1
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    obtain ⟨hyF, hyC⟩ := Subgroup.mem_inf.mp hy
    let W : Subgroup Q := Subgroup.closure
      {γ : Q | ∃ x ∈ (⊤ : Subgroup Q) ⊓ Subgroup.centralizer ({c} : Set Q),
        γ = x * b * x⁻¹}
    have hW : IsElemAbelian 2 W := h.K1 b hbA c hcA hc1
    have hbW : b ∈ W := Subgroup.subset_closure ⟨1, by simp, by group⟩
    have hzW : y * b * y⁻¹ ∈ W :=
      Subgroup.subset_closure ⟨y, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top y, hyC⟩, rfl⟩
    have hbz : b * (y * b * y⁻¹) = (y * b * y⁻¹) * b :=
      congrArg Subtype.val (hW.1.is_comm.comm ⟨b, hbW⟩ ⟨y * b * y⁻¹, hzW⟩)
    have hb2 : b * b = 1 := by simpa [pow_two] using h.A_elem.2 b hbA
    have hz2 : (y * b * y⁻¹) * (y * b * y⁻¹) = 1 := by
      simpa [pow_two] using hW.2 (y * b * y⁻¹) hzW
    have hu2 : (b * (y * b * y⁻¹)) * (b * (y * b * y⁻¹)) = 1 := by
      calc (b * (y * b * y⁻¹)) * (b * (y * b * y⁻¹))
          = b * ((y * b * y⁻¹) * b) * (y * b * y⁻¹) := by group
        _ = b * (b * (y * b * y⁻¹)) * (y * b * y⁻¹) := by rw [hbz]
        _ = (b * b) * ((y * b * y⁻¹) * (y * b * y⁻¹)) := by group
        _ = 1 := by rw [hb2, hz2, one_mul]
    have hbyF : b * y * b⁻¹ ∈ F := hFnormal.conj_mem y hyF b
    have hb3 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have huF : b * (y * b * y⁻¹) ∈ F := by
      have hmem : (b * y * b⁻¹) * y⁻¹ ∈ F := F.mul_mem hbyF (F.inv_mem hyF)
      convert hmem using 1
      rw [hb3]
      group
    have hu1 : b * (y * b * y⁻¹) = 1 :=
      CFSG.GH74.Uniqueness.eq_one_of_mem_of_sq_eq_one hFodd huF hu2
    have hyb : b * y * b = y := by
      have := congrArg (· * y) hu1
      simpa [mul_assoc] using this
    have h3 : (b * y * b) * b = b * y := by
      rw [mul_assoc, hb2, mul_one]
    rw [← h3, hyb]
  have hcentral : ∀ b ∈ A, F ≤ Subgroup.centralizer ({b} : Set Q) := by
    intro b hbA
    refine hcover.trans ?_
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hgen b hbA p hpA hp1
    · exact hgen b hbA v hvA hv1
    · exact hgen b hbA (p * v) (A.mul_mem hpA hvA) hpv1
  intro b hbA y hyF
  exact Subgroup.mem_centralizer_iff.mp (hcentral b hbA hyF) b (Set.mem_singleton b)

theorem Cfg813.inf_centralizer_layer (h : Cfg813 T A B R L₀) :
    A ⊓ centralizer (genFittingLayer Q : Set Q) = ⊥ := by
  classical
  refine le_bot_iff.mp ?_
  intro a ha
  rw [Subgroup.mem_bot]
  obtain ⟨haA, haE⟩ := Subgroup.mem_inf.mp ha
  set F := genFittingFitting Q with hF
  set E := genFittingLayer Q with hE
  set Fstar := genFittingFStar Q with hFs
  have hFodd : Odd (Nat.card F) := by
    rw [hF]
    exact h.fitting_odd
  have hFa : F ≤ Subgroup.centralizer ({a} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h.fitting_commute a haA y (by rwa [hF] at hy)).symm
  have hEa : E ≤ Subgroup.centralizer ({a} : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp haE x (by rwa [hE] at hx)
  have hFstara : a ∈ Subgroup.centralizer (Fstar : Set Q) := by
    have hsup : F ⊔ E ≤ Subgroup.centralizer ({a} : Set Q) := sup_le hFa hEa
    have hmem : a ∈ Subgroup.centralizer ((F ⊔ E : Subgroup Q) : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hx)
    simpa [hFs, genFittingFStar.eq_sup, hF, hE] using hmem
  have haFstar : a ∈ Fstar := by
    have hmem := CFSG.Open.Open.generalized_fitting_self_centralizing Q hFstara
    simpa [hFs] using hmem
  let Z : Subgroup Q := (Subgroup.center ↥Fstar).map Fstar.subtype
  have haZ : a ∈ Z := by
    refine Subgroup.mem_map.mpr ⟨⟨a, haFstar⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    have hcomm := Subgroup.mem_centralizer_iff.mp hFstara (z : Q) z.2
    exact Subtype.ext hcomm
  have hFstarNormal : Fstar.Normal := by
    have hFnormal : F.Normal := by
      rw [hF]
      change (CFSG.fittingSubgroup Q).Normal
      infer_instance
    have hEnormal : E.Normal := by
      rw [hE]
      change (CFSG.ComponentClassification.Layer.subgroup Q).Normal
      exact CFSG.ComponentClassification.Layer.normal Q
    have hsup : (F ⊔ E).Normal := inferInstance
    simpa [hFs, hF, hE, genFittingFStar.eq_sup] using hsup
  have hZnormal : Z.Normal := by
    dsimp [Z]
    haveI : Fstar.Normal := hFstarNormal
    haveI : (Subgroup.center ↥Fstar).Characteristic := Subgroup.centerCharacteristic
    infer_instance
  have hZnil : Group.IsNilpotent ↥Z := by
    dsimp [Z]
    let e := Subgroup.equivMapOfInjective (Subgroup.center ↥Fstar) Fstar.subtype
      Fstar.subtype_injective
    exact Group.nilpotent_of_mulEquiv e
  have hZleF : Z ≤ F := by
    rw [hF, genFittingFitting.eq_sSup]
    exact le_sSup ⟨hZnormal, hZnil⟩
  have haF : a ∈ F := hZleF haZ
  have ha2 : a * a = 1 := by simpa [pow_two] using h.A_elem.2 a haA
  exact CFSG.GH74.Uniqueness.eq_one_of_mem_of_sq_eq_one hFodd haF ha2

theorem Cfg813.exists_component (h : Cfg813 T A B R L₀) :
    ∃ J : Subgroup Q, IsComponentOf J ⊤ ∧ ¬ A ≤ centralizer (J : Set Q) := by
  classical
  by_contra hcon
  push Not at hcon
  have hAcent : A ≤ Subgroup.centralizer (genFittingLayer Q : Set Q) := by
    intro a haA
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : genFittingLayer Q ≤ Subgroup.centralizer ({a} : Set Q) := by
      rw [genFittingLayer.eq_sSup]
      refine sSup_le fun J hJ => ?_
      intro y hyJ
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp ((hcon J hJ) haA) y hyJ
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hAleBot : A ≤ ⊥ := by
    have hsub : A ≤ A ⊓ Subgroup.centralizer (genFittingLayer Q : Set Q) := by
      intro a ha
      exact Subgroup.mem_inf.mpr ⟨ha, hAcent ha⟩
    rwa [h.inf_centralizer_layer] at hsub
  have hAbot : A = ⊥ := le_bot_iff.mp hAleBot
  have hcard := h.A_card
  rw [hAbot] at hcard
  simp at hcard

end CFSG.LocalAnalysis.WeakClosure81

end
