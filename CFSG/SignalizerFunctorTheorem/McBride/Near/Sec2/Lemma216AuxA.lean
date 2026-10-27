module

public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216AuxCoord
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216AuxLocal
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.PermutationAction

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

namespace Lemma216

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G S : Subgroup Γ}

theorem le_normalizer_sectionCentralizer {B X Y : Subgroup Γ}
    (hX : B ≤ Subgroup.normalizer (X : Set Γ)) (hY : B ≤ Subgroup.normalizer (Y : Set Γ)) :
    B ≤ Subgroup.normalizer ((sectionCentralizer X Y : Subgroup Γ) : Set Γ) := by
  refine le_normalizer_of_conj_mem fun b hb x hx => ?_
  obtain ⟨hxX, hxY, hxc⟩ := hx
  refine ⟨mul_mem (mul_mem (hX hb) hxX) (inv_mem (hX hb)),
    mul_mem (mul_mem (hY hb) hxY) (inv_mem (hY hb)), fun y hy => ?_⟩
  have hy' : b⁻¹ * y * b ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (hY (inv_mem hb)) y).mp hy
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.mp (hX hb) _).mp (hxc _ hy')
  have e : ⁅b * x * b⁻¹, y⁆ = b * ⁅x, b⁻¹ * y * b⁆ * b⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h1

theorem normalizer_of_mem_khat {X : Subgroup Γ} (hX : sol X = ⊥) {w : Γ} (hw : w ∈ khat X) :
    ∀ J ∈ lcal X, w ∈ Subgroup.normalizer (J : Set Γ) := by
  intro J hJ
  have hs : ¬ Group.IsSolvable X := fun hs => by
    have : Group.IsSolvable ↥X := hs
    exact not_isSolvable_of_mem_lcal hJ
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (lcal_le hJ)))
  have hJl : J ∈ ltilde X := Or.inr ⟨hs, (mcal_eq_lcal_of_sol_eq_bot hX).symm ▸ hJ⟩
  unfold khat at hw
  have := (Subgroup.mem_inf.mp hw).2
  simp only [Subgroup.mem_iInf] at this
  exact this J hJl

theorem mem_khat_of_forall_normalizer {X : Subgroup Γ} (hX : sol X = ⊥) {w : Γ} (hwX : w ∈ X)
    (h : ∀ J ∈ lcal X, w ∈ Subgroup.normalizer (J : Set Γ)) : w ∈ khat X := by
  by_cases hs : Group.IsSolvable X
  · rw [khat_eq_of_isSolvable hs]
    exact hwX
  · have hl : ltilde X = lcal X := by
      rw [← mcal_eq_lcal_of_sol_eq_bot hX]
      ext M
      simp [ltilde, hs]
    unfold khat
    rw [hl]
    refine Subgroup.mem_inf.mpr ⟨hwX, ?_⟩
    simp only [Subgroup.mem_iInf]
    exact fun J hJ => h J hJ

theorem mem_d2_iff {d : Γ} :
    d ∈ d2 A G S ↔ d ∈ d0 A G S ∧ ∀ e ∈ d0 A G S, ⁅d, e⁆ ∈ d1 A G S := by
  constructor
  · intro hd
    obtain ⟨hd0, hsc⟩ := Subgroup.mem_inf.mp hd
    exact ⟨hd0, (mem_sectionCentralizer_iff.mp hsc).2.2⟩
  · rintro ⟨hd0, hc⟩
    refine Subgroup.mem_inf.mpr ⟨hd0, ?_⟩
    exact (mem_sectionCentralizer_iff_of_le (Subgroup.map_subtype_le _)).mpr
      ⟨le_normalizer_fittingSubgroupOf _ hd0, hc⟩

theorem mem_s2_iff {x : Γ} :
    x ∈ s2 G S ↔ x ∈ s0 G S ∧ ∀ y ∈ s0 G S, ⁅x, y⁆ ∈ s1 G S := by
  constructor
  · intro hx
    obtain ⟨hx0, hsc⟩ := Subgroup.mem_inf.mp hx
    exact ⟨hx0, (mem_sectionCentralizer_iff.mp hsc).2.2⟩
  · rintro ⟨hx0, hc⟩
    refine Subgroup.mem_inf.mpr ⟨hx0, ?_⟩
    exact (mem_sectionCentralizer_iff_of_le (Subgroup.map_subtype_le _)).mpr
      ⟨le_normalizer_fittingSubgroupOf _ hx0, hc⟩

theorem d0_le_s0 : d0 A G S ≤ s0 G S := inf_le_right

theorem d2_le_d0 : d2 A G S ≤ d0 A G S := inf_le_left

theorem s0_le_kOf : s0 G S ≤ kOf G := inf_le_right

theorem s1_le_s2 : s1 G S ≤ s2 G S := by
  intro s hs
  have hs0 : s ∈ s0 G S := Subgroup.map_subtype_le _ hs
  refine mem_s2_iff.mpr ⟨hs0, fun y hy => ?_⟩
  have h1 : ⁅s, y⁆ = s * (y * s⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  have hyN : y ∈ Subgroup.normalizer (s1 G S : Set Γ) :=
    le_normalizer_fittingSubgroupOf (s0 G S) hy
  exact mul_mem hs ((Subgroup.mem_normalizer_iff.mp hyN s⁻¹).mp (inv_mem hs))

namespace Hyp

variable [Finite Γ] (H : Hyp p A G S)

include H

theorem d2_le_s2 :
    d2 A G S ≤ s2 G S := by
  intro d hd
  have hK := H.semisimpleAction
  have hP := hK.isDirectProduct_lcal
  obtain ⟨hd0, hc⟩ := mem_d2_iff.mp hd
  have hd0K : d ∈ cenIn (kOf G) A := by rw [← H.d0_eq]; exact hd0
  have hdK : d ∈ kOf G := (mem_cenIn_iff.mp hd0K).1
  have hdc : ∀ e ∈ cenIn (kOf G) A, ⁅d, e⁆ ∈ CFSG.fittingSubgroupOf (cenIn (kOf G) A) := by
    intro e he
    have := hc e (by rw [H.d0_eq]; exact he)
    rwa [H.d1_eq] at this
  refine mem_s2_iff.mpr ⟨d0_le_s0 hd0, fun y hy => ?_⟩
  have hyK : y ∈ kOf G := s0_le_kOf hy
  have hyP : y ∈ kProd A (kOf G) := by rw [← H.s0_eq_kProd]; exact hy
  obtain ⟨_, hycoord⟩ := hK.mem_kProd_iff.mp hyP
  rw [H.s1_eq, hK.mem_fProd_iff]
  have hdN : d ∈ Subgroup.normalizer (kOf G : Set Γ) := Subgroup.le_normalizer hdK
  refine ⟨commutator_mem_of_mem_normalizer hdN hyK, fun J hJ => ?_⟩
  have hdJ : d ∈ Subgroup.normalizer (J : Set Γ) := hP.le_normalizer hJ hdK
  have hyJ : ((hP.coord hJ ⟨y, hyK⟩ : J) : Γ) ∈ J := (hP.coord hJ _).2
  rw [hK.coord_commutator hJ hdN hdJ hyK, hP.commutator_eq_coord hJ hdK hyJ]
  have hdJ' : ((hP.coord hJ ⟨d, hdK⟩ : J) : Γ) ∈ cenIn J (norIn A J) := by
    rw [← hK.projIn_cenIn hJ]
    exact (hP.mem_projIn_iff hJ).mpr ⟨⟨d, hdK⟩, hd0K, rfl⟩
  exact hK.commutator_mem_fitting_kJ hJ
    (le_normalizer_fittingSubgroupOf (kJ A J) (hK.cenIn_norIn_le_kJ hJ hdJ'))
    (hK.coord_commutator_mem_fitting_kJ hJ hdK hdc) (hycoord J hJ)

theorem sup_le_s2 :
    d2 A G S ⊔ s1 G S ≤ s2 G S :=
  sup_le H.d2_le_s2 s1_le_s2

theorem s0_le_W
    : s0 G S ≤ G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S) := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨kOf_le G (s0_le_kOf hx), ?_⟩
  refine (mem_sectionCentralizer_iff_of_le le_sup_right).mpr
    ⟨le_normalizer_fittingSubgroupOf _ hx, fun y hy => ?_⟩
  have h1 := (mem_s2_iff.mp (H.sup_le_s2 hy)).2 x hx
  rw [← commutatorElement_inv]
  exact inv_mem h1

theorem exists_orbit
    {w : Γ} (hw : w ∈ G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S))
    {J : Subgroup Γ} (hJ : J ∈ lcal (kOf G)) :
    ∃ a ∈ A, J.map (MulAut.conj w).toMonoidHom = J.map (MulAut.conj a).toMonoidHom := by
  by_contra hne
  push Not at hne
  obtain ⟨hwG, hwSC⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨hwN1, -, hwc⟩ := hwSC
  have hK := H.semisimpleAction
  have hP := hK.isDirectProduct_lcal
  obtain ⟨v, hvC, hvF, hvc⟩ := hK.exists_core1 hJ
  obtain ⟨d, hdK, hdsm, hdv⟩ := hK.exists_smear_coord hJ hvC
  have hd2 : d ∈ d2 A G S := by
    rw [mem_d2_iff]
    have hd0 : d ∈ d0 A G S := by
      rw [H.d0_eq]
      exact hK.smear_le_cenIn hJ hdsm
    refine ⟨hd0, fun e he => ?_⟩
    rw [H.d1_eq]
    rw [H.d0_eq] at he
    refine hK.commutator_mem_fitting_of_smear hJ hdK hdsm (fun c hc => ?_) he
    rw [hdv]
    exact hvc c hc
  have hwd : ⁅w, d⁆ ∈ s1 G S := hwc d (Subgroup.mem_sup_left hd2)
  have hwN : w ∈ Subgroup.normalizer (kOf G : Set Γ) := Nonsolv.le_normalizer_kOf G hwG
  have ha : ∀ J'' ∈ lcal (kOf G), J''.map (MulAut.conj w).toMonoidHom ∈ lcal (kOf G) :=
    fun J'' hJ'' => map_conj_mem_lcal hJ'' hwN
  have hJ' : J.map (MulAut.conj w).toMonoidHom ∈ lcal (kOf G) := ha J hJ
  have hd1 : d ∈ sSup (lcal (kOf G) \ {J.map (MulAut.conj w).toMonoidHom}) := by
    have hle : orbitClosure J A ≤ sSup (lcal (kOf G) \ {J.map (MulAut.conj w).toMonoidHom}) := by
      refine orbitClosure_le fun a ha' => le_sSup ⟨hK.permutes_lcal a ha' J hJ, fun hEq => ?_⟩
      exact hne a ha' (Set.mem_singleton_iff.mp hEq).symm
    exact hle (smear_le_orbitClosure J A hdsm)
  have hd1' : ((hP.coord hJ' ⟨d, hdK⟩ : J.map (MulAut.conj w).toMonoidHom) : Γ) = 1 :=
    congrArg Subtype.val ((hP.coord_eq_one_iff hJ' ⟨d, hdK⟩).mpr hd1)
  have hwdK : ⁅w, d⁆ ∈ kOf G := commutator_mem_of_mem_normalizer hwN hdK
  have hcomm : ((hP.coord hJ' ⟨⁅w, d⁆, hwdK⟩ : J.map (MulAut.conj w).toMonoidHom) : Γ) =
      w * v * w⁻¹ := by
    have e1 : (⟨⁅w, d⁆, hwdK⟩ : ↥(kOf G)) =
        ⟨w * d * w⁻¹, hP.conj_mem ha hdK⟩ * ⟨d, hdK⟩⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e1, map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv, hd1']
    have e2 := hP.coord_conj ha hJ hdK
    rw [e2, hdv]
    simp
  have hS1 : ⁅w, d⁆ ∈ fProd A (kOf G) := by rw [← H.s1_eq]; exact hwd
  obtain ⟨_, hcc⟩ := hK.mem_fProd_iff.mp hS1
  have h1 := hcc _ hJ'
  rw [hcomm] at h1
  have h2 : w * v * w⁻¹ ∈ s1 G S := by
    have hle : CFSG.fittingSubgroupOf (kJ A (J.map (MulAut.conj w).toMonoidHom)) ≤
        fProd A (kOf G) := le_sSup ⟨_, hJ', rfl⟩
    rw [H.s1_eq]
    exact hle h1
  have h3 : v ∈ s1 G S := (Subgroup.mem_normalizer_iff.mp hwN1 v).mpr h2
  have h4 : v ∈ fProd A (kOf G) ⊓ J :=
    Subgroup.mem_inf.mpr ⟨by rw [← H.s1_eq]; exact h3, (mem_cenIn_iff.mp hvC).1⟩
  rw [hK.fProd_inf hJ] at h4
  exact hvF h4

theorem W_le_khat
    : G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S) ≤ khat G := by
  have hK := H.semisimpleAction
  have hS1 : A ≤ Subgroup.normalizer (s1 G S : Set Γ) := by
    rw [H.s1_eq]
    exact hK.admits_fProd
  have hd2c : d2 A G S ≤ Subgroup.centralizer (A : Set Γ) :=
    d2_le_d0.trans (H.d0_eq.le.trans inf_le_right)
  have hAd2 : A ≤ Subgroup.normalizer (d2 A G S : Set Γ) := le_normalizer_of_le_centralizer hd2c
  have hAY : A ≤ Subgroup.normalizer ((d2 A G S ⊔ s1 G S : Subgroup Γ) : Set Γ) :=
    fun a ha => mem_normalizer_sup (hAd2 ha) (hS1 ha)
  have hAW : A ≤ Subgroup.normalizer
      ((G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S) : Subgroup Γ) : Set Γ) :=
    fun a ha => mem_normalizer_inf (H.near.admits ha)
      (le_normalizer_sectionCentralizer hS1 hAY ha)
  have hcop : Nat.Coprime p
      (Nat.card ↥(G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      H.near.nearPSolvable.1
  have hA : IsPGroup p A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A H.near.elemAbelian
  intro w hw
  refine mem_khat_of_forall_normalizer H.sol_eq (Subgroup.mem_inf.mp hw).1 fun J hJ => ?_
  rw [← H.lcal_kOf] at hJ
  let Ω : Set (Subgroup Γ) := {X | ∃ a ∈ A, X = J.map (MulAut.conj a).toMonoidHom}
  have hΩ : ∀ g ∈ (G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S)) ⊔ A, ∀ X ∈ Ω,
      X.map (MulAut.conj g).toMonoidHom ∈ Ω := by
    intro g hg X hX
    obtain ⟨b, hb, rfl⟩ := hX
    have hg' : g ∈ (((G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S)) ⊔ A : Subgroup Γ) :
        Set Γ) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ A hAW] at hg'
    obtain ⟨w', hw', a, ha, rfl⟩ := hg'
    have hJ₁ : J.map (MulAut.conj (a * b)).toMonoidHom ∈ lcal (kOf G) :=
      hK.permutes_lcal (a * b) (mul_mem ha hb) J hJ
    obtain ⟨c, hc, hcw⟩ := H.exists_orbit hw' hJ₁
    refine ⟨c * (a * b), mul_mem hc (mul_mem ha hb), ?_⟩
    calc (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj (w' * a)).toMonoidHom
        = J.map (MulAut.conj (w' * a * b)).toMonoidHom := map_conj_map_conj J b _
      _ = J.map (MulAut.conj (w' * (a * b))).toMonoidHom := by rw [mul_assoc]
      _ = (J.map (MulAut.conj (a * b)).toMonoidHom).map (MulAut.conj w').toMonoidHom :=
        (map_conj_map_conj J (a * b) w').symm
      _ = (J.map (MulAut.conj (a * b)).toMonoidHom).map (MulAut.conj c).toMonoidHom := hcw
      _ = J.map (MulAut.conj (c * (a * b))).toMonoidHom := map_conj_map_conj J (a * b) c
  have htrans : ∀ X ∈ Ω, ∀ Y ∈ Ω, ∃ a ∈ A, Y = X.map (MulAut.conj a).toMonoidHom := by
    rintro X ⟨b, hb, rfl⟩ Y ⟨c, hc, rfl⟩
    refine ⟨c * b⁻¹, mul_mem hc (inv_mem hb), ?_⟩
    rw [map_conj_map_conj, inv_mul_cancel_right]
  exact normalizes_of_isPGroup_transitive_conj H.near.prime hA hcop hAW hΩ htrans w hw J
    ⟨1, one_mem A, (map_conj_one J).symm⟩

end Hyp

end Lemma216

end CFSG.SignalizerFunctorTheorem.McBride.Near
