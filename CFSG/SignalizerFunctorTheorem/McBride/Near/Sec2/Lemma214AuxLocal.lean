module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma213Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma214Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210gAux3

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma214

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A X W : Subgroup Γ} {a : Γ}

structure Hyp (p : ℕ) (A X W : Subgroup Γ) (a : Γ) : Prop where
  near : NearAction p A X
  semisimple : IsSemisimple X
  ne_bot : X ≠ ⊥
  mem : a ∈ A
  ne_one : a ≠ 1
  solvable : Group.IsSolvable ↥(cenIn X ({a} : Set Γ))
  le : W ≤ cenIn X ({a} : Set Γ)
  admits : Admits (A ⊔ cenIn X ({a} : Set Γ)) W
  cen_bot : cenIn W (A : Set Γ) = ⊥

namespace Hyp

variable (H : Hyp p A X W a)

include H

omit [Finite Γ] in
theorem admits_A : Admits A W := le_sup_left.trans H.admits

omit [Finite Γ] in
theorem conj_mem_W {c : Γ} (hc : c ∈ cenIn X ({a} : Set Γ)) {w : Γ} (hw : w ∈ W) :
    c * w * c⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.1 (H.admits (Subgroup.mem_sup_right hc)) w).1 hw

omit [Finite Γ] in
theorem semisimpleAction : SemisimpleAction p A X where
  prime := H.near.prime
  odd := H.near.odd
  elemAbelian := H.near.elemAbelian
  admits := H.near.admits
  nearPSolvable := H.near.nearPSolvable
  solvable_cen := by
    have : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ({a} : Set Γ)) := H.solvable
    refine Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (inf_le_inf_left X (Subgroup.centralizer_le (Set.singleton_subset_iff.2 H.mem)) :
        cenIn X (A : Set Γ) ≤ cenIn X ({a} : Set Γ)))
  semisimple := H.semisimple
  ne_bot := H.ne_bot

theorem hX : IsDirectProduct (lcal X) X := H.semisimple.isDirectProduct_lcal

omit [Finite Γ] in
theorem perm {b : Γ} (hb : b ∈ A) {J : Subgroup Γ} (hJ : J ∈ lcal X) :
    J.map (MulAut.conj b).toMonoidHom ∈ lcal X :=
  map_conj_mem_lcal hJ (H.near.admits hb)

theorem mem_normalizer {J : Subgroup Γ} (hJ : J ∈ lcal X) :
    a ∈ Subgroup.normalizer (J : Set Γ) := by
  by_contra han
  have hperm : ∀ b ∈ Subgroup.zpowers a, ∀ J' ∈ lcal X,
      J'.map (MulAut.conj b).toMonoidHom ∈ lcal X := fun b hb J' hJ' =>
    H.perm (Subgroup.zpowers_le.2 H.mem hb) hJ'
  have hproj := projIn_centralizer_eq H.hX hperm hJ
  have hinf : Subgroup.zpowers a ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbz, hbN⟩ := Subgroup.mem_inf.1 hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    exact han ((Subgroup.zpowers_le.2 hbN) (mem_zpowers_of_mem_zpowers H.near.prime
      (H.near.elemAbelian.2 a H.mem) H.ne_one hbz hb1))
  have hcen : X ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup Γ) : Set Γ) =
      cenIn X ({a} : Set Γ) := by
    unfold cenIn
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hinf, hcen, Lemma213.centralizer_bot, inf_top_eq] at hproj
  have hsol : Group.IsSolvable ↥(projIn (lcal X) J (cenIn X ({a} : Set Γ))) :=
    Thm210.isSolvable_projIn H.hX hJ inf_le_left H.solvable
  rw [hproj] at hsol
  exact not_isSolvable_of_mem_lcal hJ hsol

theorem mem_norIn {J : Subgroup Γ} (hJ : J ∈ lcal X) : a ∈ norIn A J :=
  Subgroup.mem_inf.2 ⟨H.mem, H.mem_normalizer hJ⟩

theorem cenIn_le {J : Subgroup Γ} (hJ : J ∈ lcal X) :
    cenIn J ({a} : Set Γ) ≤ cenIn J ((norIn A J : Subgroup Γ) : Set Γ) := by
  have hSA := H.semisimpleAction
  obtain ⟨a₀, f, ha₀, hf, hord, hpow, hfix⟩ := hSA.exists_frame hJ
  obtain ⟨k, hk⟩ := hpow a (H.mem_norIn hJ)
  have hpk : ¬ p ∣ k := by
    intro hpk
    have hf1 : f ^ k = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hord]
      exact hpk
    apply not_isSolvable_of_mem_lcal hJ
    have hJa : J ≤ cenIn X ({a} : Set Γ) := by
      refine le_inf (lcal_le hJ) fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hk ⟨x, hx⟩
      rw [hf1, MulAut.one_apply] at h1
      have h2 : a * x * a⁻¹ = x := h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have := H.solvable
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJa)
  intro x hx
  obtain ⟨hxJ, hxa⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hxJ, Subgroup.mem_centralizer_iff.2 fun n hn => ?_⟩
  obtain ⟨m, hm⟩ := hpow n hn
  have hax : a * x * a⁻¹ = x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxa).symm
  have h1 : (f ^ k) ⟨x, hxJ⟩ = ⟨x, hxJ⟩ := Subtype.ext ((hk ⟨x, hxJ⟩).symm.trans hax)
  have h2 : f ⟨x, hxJ⟩ = ⟨x, hxJ⟩ := apply_eq_of_pow_apply_eq H.near.prime hord hpk h1
  have h3 : (f ^ m) ⟨x, hxJ⟩ = ⟨x, hxJ⟩ := pow_apply_eq_of_apply_eq h2 m
  have h4 := hm ⟨x, hxJ⟩
  rw [h3] at h4
  have h5 : n * x * n⁻¹ = x := h4
  rw [mul_inv_eq_iff_eq_mul] at h5
  exact h5

theorem projIn_le_cenIn {J : Subgroup Γ} (hJ : J ∈ lcal X) :
    projIn (lcal X) J W ≤ cenIn J ((norIn A J : Subgroup Γ) : Set Γ) := by
  intro t ht
  obtain ⟨u, huW, hut⟩ := (H.hX.mem_projIn_iff hJ).1 ht
  have hperm : ∀ K ∈ lcal X, K.map (MulAut.conj a).toMonoidHom ∈ lcal X := fun K hK =>
    H.perm H.mem hK
  have hua : a * (u : Γ) * a⁻¹ = u := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (H.le huW)).2
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have h1 := Thm210g.coord_conj_of_normalizer H.hX hperm hJ (H.mem_normalizer hJ) u
  have e : (⟨a * (u : Γ) * a⁻¹, H.hX.conj_mem hperm u.2⟩ : ↥X) = u := Subtype.ext hua
  rw [e, hut] at h1
  refine H.cenIn_le hJ (Subgroup.mem_inf.2 ⟨projIn_le J W ht, ?_⟩)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc t * a = (a * t * a⁻¹) * a := by rw [← h1]
    _ = a * t := by group

theorem le_normalizer_projIn {J : Subgroup Γ} (hJ : J ∈ lcal X) :
    cenIn J ((norIn A J : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer ((projIn (lcal X) J W : Subgroup Γ) : Set Γ) := by
  have hSA := H.semisimpleAction
  have hsub : cenIn J ((norIn A J : Subgroup Γ) : Set Γ) ≤
      projIn (lcal X) J (cenIn X ({a} : Set Γ)) := by
    rw [← hSA.projIn_cenIn hJ]
    exact Thm210.projIn_mono J (inf_le_inf_left X
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 H.mem)))
  have hconj := Thm210.projIn_conj_mem H.hX hJ (Y := cenIn X ({a} : Set Γ)) (X := W)
    fun y hy w hw => H.conj_mem_W hy hw
  exact Thm210.le_normalizer_of_conj_mem fun c hc z hz => hconj c (hsub hc) z hz

theorem fitting_le_projIn
    {J : Subgroup Γ} (hJ : J ∈ lcal X)
    (hne : projIn (lcal X) J W ≠ ⊥) :
    CFSG.fittingSubgroupOf (cenIn J ((norIn A J : Subgroup Γ) : Set Γ)) ≤
      projIn (lcal X) J W :=
  H.semisimpleAction.fittingSubgroupOf_cenIn_le_of_normal hJ (H.projIn_le_cenIn hJ)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (H.projIn_le_cenIn hJ)).2
      (H.le_normalizer_projIn hJ)) hne

theorem fitting_le_commutator
    {J : Subgroup Γ} (hJ : J ∈ lcal X) :
    CFSG.fittingSubgroupOf (cenIn J ((norIn A J : Subgroup Γ) : Set Γ)) ≤
      ⁅CFSG.fittingSubgroupOf (cenIn J ((norIn A J : Subgroup Γ) : Set Γ)),
        cenIn J ((norIn A J : Subgroup Γ) : Set Γ)⁆ := by
  have hSA := H.semisimpleAction
  set C := cenIn J ((norIn A J : Subgroup Γ) : Set Γ) with hC
  set F := CFSG.fittingSubgroupOf C with hF
  have hFC : F ≤ C := Subgroup.map_subtype_le _
  have hNF : ⁅F, C⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro x hx c hc
    rw [commutatorElement_def]
    have : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [this]
    exact mul_mem hx (Thm210.fittingSubgroupOf_conj_mem hc (inv_mem hx))
  have hnorm : C ≤ Subgroup.normalizer ((⁅F, C⁆ : Subgroup Γ) : Set Γ) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
    have h1 : q ∈ Subgroup.normalizer (F : Set Γ) := Thm210.le_normalizer_fittingSubgroupOf C hq
    have h2 : q ∈ Subgroup.normalizer (C : Set Γ) := Subgroup.le_normalizer hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2
    rw [h1, h2]
  have hne : ⁅F, C⁆ ≠ ⊥ := by
    obtain ⟨x, hx, c, hc, hxc⟩ := hSA.exists_noncomm_cenIn hJ
    intro hbot
    have hmem : ⁅x, c⁆ ∈ ⁅F, C⁆ := Subgroup.commutator_mem_commutator hx hc
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : x * c * x⁻¹ * c⁻¹ = 1 := by
      rw [← commutatorElement_def]
      exact hmem
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    apply hxc
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  exact hSA.fittingSubgroupOf_cenIn_le_of_normal hJ (hNF.trans hFC)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (hNF.trans hFC)).2 hnorm) hne

theorem fitting_le_W
    {J : Subgroup Γ} (hJ : J ∈ lcal X) (hne : projIn (lcal X) J W ≠ ⊥) :
    CFSG.fittingSubgroupOf (cenIn J ((norIn A J : Subgroup Γ) : Set Γ)) ≤ W := by
  have hFZ := H.fitting_le_projIn hJ hne
  set C := cenIn J ((norIn A J : Subgroup Γ) : Set Γ) with hC
  set F := CFSG.fittingSubgroupOf C with hF
  have hFC : F ≤ C := Subgroup.map_subtype_le _
  have hcomm : ⁅F, C⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro x hx c hc
    obtain ⟨u, huW, hux⟩ := (H.hX.mem_projIn_iff hJ).1 (hFZ hx)
    have hxJ : x ∈ J := (hFC hx).1
    have hcJ : c ∈ J := hc.1
    have hxX : x⁻¹ ∈ X := inv_mem (H.hX.le hJ hxJ)
    have hl : x⁻¹ * (u : Γ) ∈ sSup (lcal X \ {J}) := by
      refine (H.hX.coord_eq_one_iff hJ ⟨x⁻¹ * (u : Γ), mul_mem hxX u.2⟩).1 ?_
      have e : (⟨x⁻¹ * (u : Γ), mul_mem hxX u.2⟩ : ↥X) = ⟨x⁻¹, hxX⟩ * u := rfl
      rw [e, map_mul]
      have h1 : H.hX.coord hJ ⟨x⁻¹, hxX⟩ = (⟨x, hxJ⟩ : J)⁻¹ :=
        Subtype.ext (H.hX.coord_of_mem hJ (inv_mem hxJ))
      have h2 : H.hX.coord hJ u = ⟨x, hxJ⟩ := Subtype.ext hux
      rw [h1, h2, inv_mul_cancel]
    have hlc : c * (x⁻¹ * (u : Γ)) = (x⁻¹ * (u : Γ)) * c :=
      (H.hX.commute_sSup_diff hJ c hcJ _ hl).eq
    have hcX : c ∈ cenIn X ({a} : Set Γ) := by
      refine Subgroup.mem_inf.2 ⟨H.hX.le hJ hcJ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hc.2 a (H.mem_norIn hJ)).symm
    have hlcl : (x⁻¹ * (u : Γ)) * c * (x⁻¹ * (u : Γ))⁻¹ = c := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hlc.symm
    have hxc : x * c * x⁻¹ * c⁻¹ = (u : Γ) * (c * (u : Γ)⁻¹ * c⁻¹) := by
      have hu : (u : Γ) = x * (x⁻¹ * (u : Γ)) := by group
      calc x * c * x⁻¹ * c⁻¹
          = x * ((x⁻¹ * (u : Γ)) * c * (x⁻¹ * (u : Γ))⁻¹) * x⁻¹ * c⁻¹ := by rw [hlcl]
        _ = (x * (x⁻¹ * (u : Γ))) * (c * (x * (x⁻¹ * (u : Γ)))⁻¹ * c⁻¹) := by group
        _ = (u : Γ) * (c * (u : Γ)⁻¹ * c⁻¹) := by rw [← hu]
    rw [commutatorElement_def, hxc]
    exact mul_mem huW (H.conj_mem_W hcX (inv_mem huW))
  exact (H.fitting_le_commutator hJ).trans hcomm

theorem projIn_eq_bot
    {J : Subgroup Γ} (hJ : J ∈ lcal X) : projIn (lcal X) J W = ⊥ := by
  by_contra hne
  have hFW := H.fitting_le_W hJ hne
  obtain ⟨⟨x, hx⟩, hx1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (H.semisimpleAction.fittingSubgroupOf_cenIn_ne_bot hJ)
  have hxW : x ∈ W := hFW hx
  have hxC : x ∈ cenIn J ((norIn A J : Subgroup Γ) : Set Γ) := Subgroup.map_subtype_le _ hx
  obtain ⟨y, hyC, hyx, hyM⟩ := exists_coord_eq H.hX (fun b hb K hK => H.perm hb hK) hJ hxC.1 hxC.2
  have hyW : (y : Γ) ∈ W :=
    hyM W fun b hb => (Subgroup.mem_normalizer_iff.1 (H.admits_A hb) x).1 hxW
  have hy1 : (y : Γ) = 1 := by
    have hmem : (y : Γ) ∈ cenIn W (A : Set Γ) := Subgroup.mem_inf.2 ⟨hyW, hyC⟩
    rw [H.cen_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hy1' : y = 1 := Subtype.ext hy1
  apply hx1
  apply Subtype.ext
  show x = 1
  calc x = ((H.hX.coord hJ y : J) : Γ) := hyx.symm
    _ = 1 := by rw [hy1', map_one]; rfl

theorem eq_bot : W = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hwX : w ∈ X := (Subgroup.mem_inf.1 (H.le hw)).1
  have h1 : (⟨w, hwX⟩ : ↥X) = 1 := by
    refine H.hX.ext_coord fun J hJ => ?_
    rw [map_one]
    have hmem : ((H.hX.coord hJ ⟨w, hwX⟩ : J) : Γ) ∈ projIn (lcal X) J W :=
      (H.hX.mem_projIn_iff hJ).2 ⟨⟨w, hwX⟩, hw, rfl⟩
    rw [H.projIn_eq_bot hJ, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

end Hyp

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma214
