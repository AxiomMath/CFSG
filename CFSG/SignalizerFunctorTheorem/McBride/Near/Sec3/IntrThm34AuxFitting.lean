module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm34

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem isGreatest_scalJoin
    (h : NearAsolvAction p A G) :
    IsGreatest {Z : Subgroup Γ | Z ≤ G ∧ Admits (cenIn G (A : Set Γ) ⊔ A) Z ∧
      Group.IsSolvable ↥Z} (scalJoin G A (cenIn G (A : Set Γ))) := by
  have hD : cenIn G (A : Set Γ) ≤ G := inf_le_left
  have hGadm : Admits (cenIn G (A : Set Γ) ⊔ A) G :=
    sup_le (hD.trans Subgroup.le_normalizer) h.admits
  have hGD : G ⊓ cenIn G (A : Set Γ) = cenIn G (A : Set Γ) := inf_eq_right.mpr hD
  refine ⟨⟨Thm211.scalJoin_le_left G A _, ?_, (thm211b h le_rfl hGadm).2⟩, ?_⟩
  · unfold scalJoin
    refine Admits.iSup fun S => Admits.iSup fun hS => ?_
    have := hS.2.1
    rwa [hGD] at this
  · rintro Z ⟨hZG, hZadm, hZs⟩
    exact Thm211.le_scalJoin ⟨hZG, by rwa [hGD], hZs⟩

theorem semisimpleAction_kOf (h : NearAsolvAction p A G) (hsol : sol G = ⊥) (hG1 : G ≠ ⊥) :
    SemisimpleAction p A (kOf G) where
  prime := h.prime
  odd := h.odd
  elemAbelian := h.elemAbelian
  admits := h.admits.trans (Thm211.normalizer_le_normalizer_kOf G)
  nearPSolvable := signalizerNearPSolvable_of_le (kOf_le G) h.nearPSolvable
  solvable_cen := Thm211.isSolvable_of_le (inf_le_inf_right _ (kOf_le G)) h.solvable_cen
  semisimple := isSemisimple_kOf hsol
  ne_bot := Thm211.kOf_ne_bot hsol hG1

omit [Finite Γ] in
theorem mem_normalizer_fittingSubgroupOf {H : Subgroup Γ} {a : Γ}
    (ha : a ∈ Subgroup.normalizer (H : Set Γ)) :
    a ∈ Subgroup.normalizer ((CFSG.fittingSubgroupOf H : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => Thm210.fittingSubgroupOf_conj_mem_of_mem_normalizer ha hx, fun hx => ?_⟩
  have := Thm210.fittingSubgroupOf_conj_mem_of_mem_normalizer (inv_mem ha) hx
  simpa [mul_assoc] using this

theorem admits_cenIn_kOf (G A : Subgroup Γ) :
    Admits (cenIn G (A : Set Γ) ⊔ A) (cenIn (kOf G) (A : Set Γ)) := by
  refine sup_le (fun d hd => ?_) (Thm210.le_normalizer_of_conj_mem fun a ha x hx => ?_)
  · obtain ⟨hdG, hdc⟩ := Thm210.mem_cenIn_iff.mp hd
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Thm211.normalizer_le_normalizer_kOf G (Subgroup.le_normalizer hdG),
        Thm32.le_normalizer_centralizer (Subgroup.centralizer_le_normalizer _) hdc⟩
  · have h1 := Subgroup.mem_centralizer_iff.mp (Thm210.mem_cenIn_iff.mp hx).2 a ha
    have : a * x * a⁻¹ = x := by rw [h1]; group
    rw [this]
    exact hx

variable (h : NearAsolvAction p A G) (hsol : sol G = ⊥) (hG1 : G ≠ ⊥)

include h hsol hG1

theorem fittingSubgroupOf_cenIn_le_kOf :
    CFSG.fittingSubgroupOf (cenIn G (A : Set Γ)) ≤ kOf G := by
  have hS := isGreatest_scalJoin h
  set S := scalJoin G A (cenIn G (A : Set Γ))
  have h216 := lemma216b h hsol hG1 hS
  have hK : SemisimpleAction p A (kOf G) := semisimpleAction_kOf h hsol hG1
  set D := cenIn G (A : Set Γ)
  have hDG : D ≤ G := inf_le_left
  have hDN : D ≤ Subgroup.normalizer (kOf G : Set Γ) :=
    hDG.trans ((Subgroup.le_normalizer).trans (Thm211.normalizer_le_normalizer_kOf G))
  have hDS : D ≤ Subgroup.normalizer (S : Set Γ) := fun d hd =>
    hS.1.2.1 (Subgroup.mem_sup_left hd)
  have hDs0 : D ≤ Subgroup.normalizer ((s0 G S : Subgroup Γ) : Set Γ) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hDS hd, hDN hd⟩
  have hDs1 : D ≤ Subgroup.normalizer ((s1 G S : Subgroup Γ) : Set Γ) := fun d hd =>
    mem_normalizer_fittingSubgroupOf (hDs0 hd)
  have hDd0 : D ≤ Subgroup.normalizer ((d0 A G S : Subgroup Γ) : Set Γ) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hd, hDs0 hd⟩
  have hd0D : d0 A G S ≤ D := inf_le_left
  have hCK : cenIn (kOf G) (A : Set Γ) ≤ s0 G S := by
    refine le_inf (hS.2 ⟨(inf_le_left).trans (kOf_le G), admits_cenIn_kOf G A, ?_⟩) inf_le_left
    exact Thm211.isSolvable_of_le (inf_le_inf_right _ (kOf_le G)) h.solvable_cen
  have hs0sol : Group.IsSolvable ↥(s0 G S) :=
    Thm211.isSolvable_of_le inf_le_left hS.1.2.2
  have hFs1 : s1 G S = s0 G S ⊓ fProd A (kOf G) :=
    hK.fittingSubgroupOf_eq_inf_fProd inf_le_right hCK hs0sol
  intro x hx
  have hxD : x ∈ D := Subgroup.map_subtype_le _ hx
  have hxG : x ∈ G := hDG hxD
  have hN₀ : (CFSG.fittingSubgroupOf D ⊓ d0 A G S) ≤ fProd A (kOf G) := by
    have hle : (CFSG.fittingSubgroupOf D ⊓ d0 A G S) ≤ CFSG.fittingSubgroupOf D := inf_le_left
    have := Thm210.isNilpotent_fittingSubgroupOf D
    refine hK.le_fProd_of_nilpotent (Y := CFSG.fittingSubgroupOf D ⊓ d0 A G S)
      (inf_le_right.trans (inf_le_right.trans inf_le_right))
      (Thm210.isNilpotent_of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)) fun d hd y hy => ?_
    have hdD : d ∈ D := (inf_le_inf_right _ (kOf_le G) : cenIn (kOf G) (A : Set Γ) ≤ D) hd
    exact Subgroup.mem_inf.mpr
      ⟨Thm210.fittingSubgroupOf_conj_mem hdD hy.1,
        (Subgroup.mem_normalizer_iff.mp (hDd0 hdD) y).mp hy.2⟩
  have hx2 : x ∈ s2 G S := by
    rw [h216]
    refine Subgroup.mem_inf.mpr ⟨hxG, mem_sectionCentralizer_iff.mpr ⟨hDs1 hxD, ?_, ?_⟩⟩
    · exact Thm210.mem_normalizer_sup (hDd0 hxD) (hDs1 hxD)
    · intro y hy
      obtain ⟨d, hdd, s, hss, rfl⟩ := (Thm32.mem_sup_iff_mul'
        (fun d hd => hDs1 (hd0D hd))).mp hy
      have hdD : d ∈ D := hd0D hdd
      have h1 : ⁅x, d⁆ ∈ CFSG.fittingSubgroupOf D := by
        have := mul_mem hx (Thm210.fittingSubgroupOf_conj_mem hdD (inv_mem hx))
        simpa [commutatorElement_def, mul_assoc] using this
      have h2 : ⁅x, d⁆ ∈ d0 A G S := by
        have := mul_mem ((Subgroup.mem_normalizer_iff.mp (hDd0 hxD) d).mp hdd) (inv_mem hdd)
        rw [commutatorElement_def]
        exact this
      have hxd : ⁅x, d⁆ ∈ s1 G S := by
        rw [hFs1]
        exact Subgroup.mem_inf.mpr ⟨(inf_le_right : d0 A G S ≤ s0 G S) h2, hN₀ ⟨h1, h2⟩⟩
      have hxs : x * s * x⁻¹ * s⁻¹ ∈ s1 G S :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (hDs1 hxD) s).mp hss) (inv_mem hss)
      have hcomm : ⁅x, d * s⁆ = ⁅x, d⁆ * (d * (x * s * x⁻¹ * s⁻¹) * d⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [hcomm]
      exact mul_mem hxd ((Subgroup.mem_normalizer_iff.mp (hDs1 hdD) _).mp hxs)
  exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx2).1).2

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm34
