module

public import CFSG.Timmesfeld.Bridge.RootStructWTILines

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem conj_mem_nCore_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d x : G}
    (hx : x ∈ nCore D d) (g : G) : g * x * g⁻¹ ∈ nCore D (g * d * g⁻¹) := by
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [nCore, MonoidHom.map_closure] at h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨y, ⟨hyD, hyQ⟩, rfl⟩
  exact ⟨conj_mem_of_isClass hclass g hyD, Moufang.mem_twoCore_conj hyQ g⟩

theorem commute_of_mem_nCore_of_mem_rootGroup {d x s : G} (hx : x ∈ nCore D d)
    (hs : s ∈ rootGroup D d) : Commute x s := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    exact (commute_of_mem_rootGroup_of_commute hs hy.1
      (Moufang.commute_of_mem_twoCore hy.2).symm).symm
  | one => exact Commute.one_left s
  | mul y z _ _ ihy ihz => exact ihy.mul_left ihz
  | inv y _ ih => exact ih.inv_left

namespace LineSetting

variable (hL : LineSetting G D) {a : G} (ha : a ∈ D)
include hL ha

theorem sup_rootGroup_le_nCore {d : G} (hd : d ∈ D) (had : Commute a d) :
    rootGroup D a ⊔ rootGroup D d ≤ nCore D a := by
  have := hL.hyp.finite
  refine sup_le ?_ ?_
  · rw [rootGroup, Subgroup.closure_le]
    intro x hx
    exact mem_nCore_of_mem_twoCore hx.1
      (rootSet_subset_twoCore_self hL.hyp.isClass hL.hyp.root hL.closure ha x hx).2
  · exact (rootGroup_le_closure_commute ha hd had (right_mem_line hd)).trans
      (hL.closure_commute_le_nCore ha)

theorem commute_of_mem_nCore_of_commute {d : G} (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {k : G} (hk : k ∈ nCore D d) (hka : Commute k a)
    {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d) : Commute k t := by
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have hTd : rootGroup D a ⊔ rootGroup D d ≤ nCore D d := by
    rw [sup_comm]
    exact hL.sup_rootGroup_le_nCore hd ha had.symm
  have haT : a ∉ rootSet D d := fun h' => hdT (mem_rootSet_comm hd h')
  refine commute_of_mul_inv_mem hL.hyp hL.closure hL.special ha hd had hadD hdT (p := d) (q := a)
    (right_mem_line hd) (hD.ne_one hd) (left_mem_line ha) (hD.ne_one ha) haT
    (fun s hs => commute_of_mem_nCore_of_mem_rootGroup hk hs)
    (fun t ht => nCoreCommutatorInRoot_of_hyp hL.hyp hL.closure d hd k hk t (hTd ht))
    (fun s hs => ?_) ht
  have h1 : (rootGroup D a).map (MulAut.conj k).toMonoidHom = rootGroup D a := by
    rw [← rootGroup_conj hclass, hka.eq, mul_inv_cancel_right]
  rw [← h1]
  exact ⟨s, hs, rfl⟩

theorem mem_nCore_of_map_conj_eq {d : G} (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) {b : G} (hb : b ∈ D) (hab : Commute a b) (habD : a * b ∈ D)
    (hbL : b ∉ rootGroup D a ⊔ rootGroup D d) {k : G} (hk : k ∈ nCore D d) (hka : Commute k a)
    (hkL : (rootGroup D a ⊔ rootGroup D b).map (MulAut.conj k).toMonoidHom =
      rootGroup D a ⊔ rootGroup D b) : k ∈ nCore D a := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  have hTI := hL.lineTI ha hd had hadD hdT
  have hbT : b ∉ rootSet D a := fun h' =>
    hbL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  have hkT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute k t :=
    fun t ht => hL.commute_of_mem_nCore_of_commute ha hd had hadD hdT hk hka ht
  have hdb : orderOf (d * b) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line hD hL.lineCentralizerEq ha hd had hadD hdT hTI hb
      hab hbL
  obtain ⟨y, hy, hdy, hdyD, hay⟩ := exists_special_of_not_mem_line hL.hyp hL.closure hL.special
    hL.lineCentralizerEq ha hd had hadD hdT hTI hb hab habD hbT hbL
  obtain ⟨hyb, hoddb⟩ := opposite_of_not_mem_line hclass hD hL.closure hL.special hL.commLambda
    hL.lineCentralizerEq ha hd had hadD hdT hTI hy hdy hdyD hay hb hab habD hbL
  obtain ⟨b', hb', h3⟩ := exists_orderOf_mul_eq_three_of_oneOpposite hL.hyp hL.closure hL.special
    hL.commLambda hb hy hyb hoddb
    ⟨a, ha, hab.symm, by rw [← hab.eq]; exact habD, by rw [orderOf_mul_comm_eq]; exact hay⟩
  obtain ⟨hμa, -⟩ := map_conj_weyl_eq hclass hD hL.closure hL.special hL.commLambda ha hd had hadD
    hy hdy hdyD hay hb hab habD hdb (mem_rootSet_self hy) hb' h3
  have hb'D := hb'.1
  have hab' : Commute a b' := ((hb'.2 a ha).2 hab.symm).symm
  have hdb' : ¬ Commute d b' := fun h' =>
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hb) hdb
      ((hb'.2 d hd).1 h'.symm).symm
  have hMa : rootGroup D a ⊔ rootGroup D d ≤ nCore D a := hL.sup_rootGroup_le_nCore ha hd had
  have hb'M : b' ∈ nCore D a :=
    hL.closure_commute_le_nCore ha (Subgroup.subset_closure ⟨hb'D, hab'⟩)
  have hNb : ∀ β ∈ rootGroup D b, β * d * β⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
    intro β hβ
    rcases (mem_rootGroup_iff_of_rootClosure hD hL.closure hb).1 hβ with rfl | hβT
    · rw [one_mul, inv_one, mul_one]
      exact right_mem_line hd
    · have := normalizesLine_of_special hD hL.special hL.commLambda hd ha had.symm
        (by rw [← had.eq]; exact hadD) hb hab habD hdb hβT d (left_mem_line hd)
      rwa [sup_comm] at this
  have hα : k * b' * k⁻¹ * b'⁻¹ ∈ rootGroup D a := by
    have hkb : k * b' * k⁻¹ ∈ rootGroup D a ⊔ rootGroup D b := by
      rw [← hkL]
      exact ⟨b', Subgroup.mem_sup_right (rootSet_subset_rootGroup D b hb'), rfl⟩
    obtain ⟨α, hα, β, hβ, hαβ⟩ := exists_mul_eq_of_mem_line hb hab hkb
    have hb'A := rootSet_subset_rootGroup D b hb'
    have e1 : (k * b' * k⁻¹) * d * (k * b' * k⁻¹)⁻¹ = b' * d * b'⁻¹ := by
      have e : (k * b' * k⁻¹) * d * (k * b' * k⁻¹)⁻¹ =
          k * (b' * (k⁻¹ * d * k) * b'⁻¹) * k⁻¹ := by group
      rw [e, show k⁻¹ * d * k = d by
          rw [(hkT d (right_mem_line hd)).inv_left.eq, inv_mul_cancel_right],
        (hkT _ (hNb b' hb'A)).eq, mul_inv_cancel_right]
    have e2 : (α * β) * d * (α * β)⁻¹ = β * d * β⁻¹ := by
      have hc := commute_of_mem_sup_rootGroup ha hd had (Subgroup.mem_sup_left hα) (hNb β hβ)
      rw [show α * β * d * (α * β)⁻¹ = α * (β * d * β⁻¹) * α⁻¹ by group, hc.eq,
        mul_inv_cancel_right]
    rw [hαβ, e2] at e1
    have hcomm : Commute (b'⁻¹ * β) d := by
      have e3 : (b'⁻¹ * β) * d * (b'⁻¹ * β)⁻¹ = d := by
        rw [show b'⁻¹ * β * d * (b'⁻¹ * β)⁻¹ = b'⁻¹ * (β * d * β⁻¹) * b' by group, e1]
        group
      rw [mul_inv_eq_iff_eq_mul] at e3
      exact e3
    have hββ : b'⁻¹ * β = 1 := by
      by_contra hne
      have hT' := mem_rootSet_of_mem_rootGroup_of_ne_one hD hL.closure hb
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb'A) hβ) hne
      exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hb)
        hdb ((hT'.2 d hd).1 hcomm).symm
    rw [hαβ, ← inv_mul_eq_one.1 hββ, mul_inv_cancel_right]
    exact hα
  have hyM : y ∈ nCore D d :=
    hL.closure_commute_le_nCore hd (Subgroup.subset_closure ⟨hy, hdy⟩)
  have hδ := nCoreCommutatorInRoot_of_hyp hL.hyp hL.closure d hd k hk y hyM
  have hNy := normalizesLine_of_special hD hL.special hL.commLambda ha hd had hadD hy hdy hdyD hay
    (mem_rootSet_self hy)
  obtain ⟨μ, hμ⟩ : ∃ μ : G, μ = b' * y * b' := ⟨_, rfl⟩
  rw [← hμ] at hμa
  have hμD : μ ∈ D := by
    have := conj_mem_of_isClass hclass b' hy
    rwa [hD.inv_eq hb'D, ← hμ] at this
  have hμd : μ * d * μ⁻¹ ∈ rootSet D a := by
    have h1 := map_conj_symm_of_mul_self_eq_one (hD.mul_self_eq_one hμD) hμa
    refine mem_rootSet_of_mem_rootGroup hclass ha (conj_mem_of_isClass hclass μ hd) ?_
    rw [← h1]
    exact ⟨d, rootSet_subset_rootGroup D d (mem_rootSet_self hd), rfl⟩
  have h1 : k * μ * k⁻¹ * μ⁻¹ ∈ nCore D a := by
    have e : k * μ * k⁻¹ * μ⁻¹ = (k * b' * k⁻¹ * b'⁻¹) * b' * (k * y * k⁻¹ * y⁻¹) *
        (y * (k * b' * k⁻¹ * b'⁻¹) * y⁻¹) * b'⁻¹ := by rw [hμ]; group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hMa (Subgroup.mem_sup_left hα)) hb'M) (hMa (Subgroup.mem_sup_right hδ)))
      (hMa (hNy _ (Subgroup.mem_sup_left hα)))) (Subgroup.inv_mem _ hb'M)
  have h2 : μ * k * μ⁻¹ ∈ nCore D a := by
    rw [← nCore_eq_of_mem_rootSet hclass hD ha hμd]
    exact conj_mem_nCore_conj hclass hk μ
  have e : k = (k * μ * k⁻¹ * μ⁻¹) * (μ * k * μ⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 h2

end LineSetting

theorem rootLinesRegularStep : RootLinesRegularStep := by
  intro G _ D hL a ha d hd had hadD hdT b hb hab habD hbL c hcD hac hacD hcL
  refine ⟨hL.exists_mem_nCore_conj_line_eq ha hd had hadD hdT hb hab habD hbL hcD hac hacD hcL,
    ?_⟩
  rintro k ⟨hk, hka⟩ hkL
  exact hL.mem_nCore_of_map_conj_eq ha hd had hadD hdT hb hab habD hbL hk
    (Subgroup.mem_centralizer_singleton_iff.1 hka) hkL

end CFSG.Timmesfeld.Bridge
