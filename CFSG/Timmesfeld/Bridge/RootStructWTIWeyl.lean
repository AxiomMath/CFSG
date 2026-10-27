module

public import CFSG.Timmesfeld.Bridge.RootStructR2Defs
public import CFSG.Timmesfeld.Bridge.RootStructThmB

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem map_conj_symm_of_mul_self_eq_one {μ : G} (hμ : μ * μ = 1) {H K : Subgroup G}
    (h : H.map (MulAut.conj μ).toMonoidHom = K) : K.map (MulAut.conj μ).toMonoidHom = H := by
  have hinv : μ⁻¹ = μ := inv_eq_of_mul_eq_one_right hμ
  have hid : (MulAut.conj μ).toMonoidHom.comp (MulAut.conj μ).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply, hinv]
    calc μ * (μ * x * μ) * μ = μ * μ * x * (μ * μ) := by group
      _ = x := by rw [hμ, one_mul, mul_one]
  rw [← h, Subgroup.map_map, hid, Subgroup.map_id]

section Line

variable {a d : G}

theorem normalizesLine_of_special (hD : IsRootInvolutionSet D) (hs : SpecialClosure D)
    (hQ : Moufang.CommLambda D) (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    {y y' : G} (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D) (hay : orderOf (a * y) = 4)
    (hy' : y' ∈ rootSet D y) : NormalizesLine D a d y' := by
  have hz : (a * y) ^ 2 ∈ rootSet D d :=
    hQ d hd a ha y hy had.symm (by rw [← had.eq]; exact hadD) hdy hdyD hay
  have hle : (rootGroup D a ⊔ rootGroup D d).map (MulAut.conj y').toMonoidHom ≤
      rootGroup D a ⊔ rootGroup D d := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap, rootGroup, Subgroup.closure_le]
      intro a' ha'
      simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, SetLike.mem_coe]
      have hw : (a' * y') ^ 2 ∈ rootSet D d := by
        have := hs.mul_sq_mem_rootSet hD ha hy hay ha' hy'
        rwa [rootSet_eq_of_mem hz] at this
      have heq : y' * a' * y'⁻¹ = a' * (a' * y') ^ 2 := by
        rw [hD.inv_eq hy'.1, sq]
        calc y' * a' * y' = a' * a' * y' * a' * y' := by rw [hD.mul_self_eq_one ha'.1, one_mul]
          _ = a' * (a' * y' * (a' * y')) := by simp only [mul_assoc]
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a ha'))
        (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d hw))
    · rw [Subgroup.map_le_iff_le_comap, rootGroup, Subgroup.closure_le]
      intro d' hd'
      simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, SetLike.mem_coe]
      rw [(commute_of_mem_rootSet_of_commute hd hy' hd' hdy.symm).eq, mul_inv_cancel_right]
      exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D d hd')
  intro u hu
  have := hle (Subgroup.mem_map_of_mem _ hu)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem mem_rootGroup_of_mem_line_of_commute (hD : IsRootInvolutionSet D) (hc : RootClosure D)
    (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) {y' : G} (hy' : y' ∈ D) (hdy : Commute d y')
    (hay : ¬ Commute a y') {t : G} (ht : t ∈ rootGroup D a ⊔ rootGroup D d)
    (hty : Commute t y') : t ∈ rootGroup D d := by
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_eq_of_mem_sup
    (fun u hu v hv => commute_of_mem_rootGroup_of_commute' hd hu hv had) ht
  have hvy : Commute v y' := commute_of_mem_rootGroup_of_commute hv hy' hdy
  have huy : Commute u y' := by
    have := hty.mul_left hvy.inv_left
    rwa [mul_inv_cancel_right] at this
  by_cases hu1 : u = 1
  · rw [hu1, one_mul]
    exact hv
  · exact absurd (((mem_rootSet_of_mem_rootGroup_of_ne_one hD hc ha hu hu1).2 y' hy').1 huy) hay

end Line

theorem eq_of_odd_orderOf_of_commute (hD : IsRootInvolutionSet D) {a b d : G} (ha : a ∈ D)
    (hb : b ∈ D) (hd : d ∈ D) (hab : Commute a b) (had : Commute a d) (hadD : a * d ∈ D)
    (hodd : Odd (orderOf (b * d))) : b = d := by
  have hco : Nat.Coprime (orderOf a) (orderOf (b * d)) := by
    rw [hD.1 a ha]
    exact Nat.coprime_two_left.2 hodd
  have hord : orderOf (b * (a * d)) = 2 * orderOf (b * d) := by
    rw [show b * (a * d) = a * (b * d) by rw [← mul_assoc, ← hab.eq, mul_assoc],
      (hab.mul_right had).orderOf_mul_eq_mul_orderOf_of_coprime hco, hD.1 a ha]
  rcases hD.orderOf_mul hb hadD with h | h | h
  · have hm : orderOf (b * d) = 1 := by omega
    rw [orderOf_eq_one_iff] at hm
    calc b = b * (d * d) := by rw [hD.mul_self_eq_one hd, mul_one]
      _ = d := by rw [← mul_assoc, hm, one_mul]
  · have hm : orderOf (b * d) = 2 := by omega
    rw [hm] at hodd
    exact absurd hodd (by decide)
  · rw [hord] at h
    exact absurd h (Nat.not_odd_iff_even.2 (even_two_mul _))

section Line

variable {a d : G}

theorem orderOf_mul_eq_four_of_not_mem_line (hD : IsRootInvolutionSet D)
    (hCE : LineCentralizerEq D) (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (hTI : LineTI D a d) {b : G} (hb : b ∈ D) (hab : Commute a b)
    (hbL : b ∉ rootGroup D a ⊔ rootGroup D d) : orderOf (b * d) = 4 := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hb hd with h | h | ⟨h, -⟩
  · exact absurd (hCE a ha d hd had hadD hdT hTI b hb hab.symm h) hbL
  · exact h
  · have hbd := eq_of_odd_orderOf_of_commute hD ha hb hd hab had hadD h
    rw [hbd] at hbL
    exact (hbL (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d (mem_rootSet_self hd)))).elim

theorem orderOf_mul_eq_four_of_not_mem_line' (hD : IsRootInvolutionSet D)
    (hCE : LineCentralizerEq D) (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (hTI : LineTI D a d) {b : G} (hb : b ∈ D) (hdb : Commute d b)
    (hbL : b ∉ rootGroup D a ⊔ rootGroup D d) : orderOf (b * a) = 4 := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hb ha with h | h | ⟨h, -⟩
  · exact absurd (hCE a ha d hd had hadD hdT hTI b hb h hdb.symm) hbL
  · exact h
  · have hba := eq_of_odd_orderOf_of_commute hD hd hb ha hdb had.symm
      (by rw [← had.eq]; exact hadD) h
    rw [hba] at hbL
    exact (hbL (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a (mem_rootSet_self ha)))).elim

theorem opposite_of_not_mem_line [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hQ : Moufang.CommLambda D) (hCE : LineCentralizerEq D) (ha : a ∈ D) (hd : d ∈ D)
    (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hTI : LineTI D a d)
    {y b : G} (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D) (hay : orderOf (a * y) = 4)
    (hb : b ∈ D) (hab : Commute a b) (habD : a * b ∈ D)
    (hbL : b ∉ rootGroup D a ⊔ rootGroup D d) : ¬ Commute y b ∧ Odd (orderOf (y * b)) := by
  have hdb : orderOf (d * b) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_not_mem_line hD hCE ha hd had hadD hdT hTI hb hab hbL
  have hyN := normalizesLine_of_special hD hs hQ ha hd had hadD hy hdy hdyD hay
    (mem_rootSet_self hy)
  have hbN : NormalizesLine D a d b := by
    have := normalizesLine_of_special hD hs hQ hd ha had.symm (by rw [← had.eq]; exact hadD) hb
      hab habD hdb (mem_rootSet_self hb)
    intro u hu
    rw [sup_comm] at hu ⊢
    exact this u hu
  have hya : ¬ Commute a y :=
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hy) hay
  have hdb' : ¬ Commute d b :=
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hb) hdb
  have hyC : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute t y → t ∈ rootGroup D d :=
    fun t ht => mem_rootGroup_of_mem_line_of_commute hD hc ha hd had hy hdy hya ht
  have hbC : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute t b → t ∈ rootGroup D a := by
    intro t ht htb
    rw [sup_comm] at ht
    exact mem_rootGroup_of_mem_line_of_commute hD hc hd ha had.symm hb hab hdb' ht htb
  have haL : a ∈ rootGroup D a ⊔ rootGroup D d :=
    Subgroup.mem_sup_left (rootSet_subset_rootGroup D a (mem_rootSet_self ha))
  have hdL : d ∈ rootGroup D a ⊔ rootGroup D d :=
    Subgroup.mem_sup_right (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
  have hcomm : ∀ {e g : G}, e ∈ D → g ∈ D → g * e * g⁻¹ ∈ rootGroup D e → Commute e g :=
    fun he hg hge => commute_of_conj_mem_rootSet hclass hD he hg
      (mem_rootSet_of_mem_rootGroup hclass he (conj_mem_of_isClass hclass _ he) hge)
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hy hb with h | h | h
  ·
    refine absurd (hcomm ha hy (hbC _ (hyN a haL) ?_)) hya
    have := (Commute.conj_iff y).2 hab
    rwa [h.eq, mul_inv_cancel_right] at this
  · obtain ⟨hzD, hyz, hbz, -⟩ := sq_mem_of_orderOf_eq_four hD hy hb h
    have hzN : NormalizesLine D a d ((y * b) ^ 2) := by
      intro t ht
      have e : (y * b) ^ 2 * t * ((y * b) ^ 2)⁻¹ =
          y * (b * (y * (b * t * b⁻¹) * y⁻¹) * b⁻¹) * y⁻¹ := by rw [sq]; group
      rw [e]
      exact hyN _ (hbN _ (hyN _ (hbN _ ht)))
    have hza : Commute a ((y * b) ^ 2) := by
      refine hcomm ha hzD (hbC _ (hzN a haL) ?_)
      have := (Commute.conj_iff ((y * b) ^ 2)).2 hab
      rwa [← hbz.eq, mul_inv_cancel_right] at this
    have hzd : Commute d ((y * b) ^ 2) := by
      refine hcomm hd hzD (hyC _ (hzN d hdL) ?_)
      have := (Commute.conj_iff ((y * b) ^ 2)).2 hdy
      rwa [← hyz.eq, mul_inv_cancel_right] at this
    have hzL := hCE a ha d hd had hadD hdT hTI _ hzD hza.symm hzd.symm
    have hz1 : (y * b) ^ 2 ∈ rootGroup D a ⊓ rootGroup D d :=
      ⟨hbC _ hzL hbz.symm, hyC _ hzL hyz.symm⟩
    rw [rootGroup_inf_eq_bot_of_rootClosure hD hc ha hd
      (fun e => hdT (by rw [e]; exact mem_rootSet_self hd)), Subgroup.mem_bot] at hz1
    exact absurd hz1 (hD.ne_one hzD)
  · exact ⟨h.2, h.1⟩

theorem map_conj_weyl_eq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hQ : Moufang.CommLambda D) (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    {y b y' b' : G} (hy : y ∈ D) (hdy : Commute d y) (hdyD : d * y ∈ D)
    (hay : orderOf (a * y) = 4) (hb : b ∈ D) (hab : Commute a b) (habD : a * b ∈ D)
    (hdb : orderOf (d * b) = 4) (hy' : y' ∈ rootSet D y) (hb' : b' ∈ rootSet D b)
    (h3 : orderOf (y' * b') = 3) :
    (rootGroup D a).map (MulAut.conj (b' * y' * b')).toMonoidHom = rootGroup D d ∧
      (rootGroup D b).map (MulAut.conj (b' * y' * b')).toMonoidHom = rootGroup D y := by
  have hb'D := hb'.1
  have hy'D := hy'.1
  have hb'2 := hD.mul_self_eq_one hb'D
  have hy2 := hD.mul_self_eq_one hy'D
  have hab' : Commute a b' := ((hb'.2 a ha).2 hab.symm).symm
  have hdb' : ¬ Commute d b' := fun h' =>
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hb) hdb
      ((hb'.2 d hd).1 h'.symm).symm
  have hdy' : Commute d y' := ((hy'.2 d hd).2 hdy.symm).symm
  have hya : ¬ Commute a y' := fun h' =>
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hy) hay
      ((hy'.2 a ha).1 h'.symm).symm
  obtain ⟨μ, hμ⟩ : ∃ μ : G, μ = b' * y' * b' := ⟨_, rfl⟩
  rw [← hμ]
  have hμD : μ ∈ D := by
    have := conj_mem_of_isClass hclass b' hy'D
    rwa [hD.inv_eq hb'D, ← hμ] at this
  have hμinv : μ⁻¹ = μ := hD.inv_eq hμD
  have hbb : ∀ X : G, b' * (b' * X) = X := fun X => by rw [← mul_assoc, hb'2, one_mul]
  have hyy : ∀ X : G, y' * (y' * X) = X := fun X => by rw [← mul_assoc, hy2, one_mul]
  have hyb3 : y' * (b' * (y' * (b' * (y' * b')))) = 1 := by
    rw [← pow_orderOf_eq_one (y' * b'), h3]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hbraid : μ * b' * μ⁻¹ = y' := by
    rw [hμinv, hμ]
    simp only [mul_assoc, hbb]
    calc b' * (y' * (b' * (y' * b'))) = y' * (y' * (b' * (y' * (b' * (y' * b'))))) :=
          (hyy _).symm
      _ = y' := by rw [hyb3, mul_one]
  have hb'N : NormalizesLine D a d b' := by
    have := normalizesLine_of_special hD hs hQ hd ha had.symm (by rw [← had.eq]; exact hadD) hb
      hab habD hdb hb'
    intro u hu
    rw [sup_comm] at hu ⊢
    exact this u hu
  have hyN := normalizesLine_of_special hD hs hQ ha hd had hadD hy hdy hdyD hay hy'
  have hμN : NormalizesLine D a d μ := by
    intro u hu
    have e : μ * u * μ⁻¹ = b' * (y' * (b' * u * b'⁻¹) * y'⁻¹) * b'⁻¹ := by rw [hμ]; group
    rw [e]
    exact hb'N _ (hyN _ (hb'N _ hu))
  have hyC : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute t y' → t ∈ rootGroup D d :=
    fun t ht => mem_rootGroup_of_mem_line_of_commute hD hc ha hd had hy'D hdy' hya ht
  have hb'C : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute t b' → t ∈ rootGroup D a := by
    intro t ht htb
    rw [sup_comm] at ht
    exact mem_rootGroup_of_mem_line_of_commute hD hc hd ha had.symm hb'D hab' hdb' ht htb
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine hyC _ (hμN u (Subgroup.mem_sup_left hu)) ?_
    have := (Commute.conj_iff μ).2 (commute_of_mem_rootGroup_of_commute hu hb'D hab')
    rwa [hbraid] at this
  · intro v hv
    refine ⟨μ * v * μ⁻¹, hb'C _ (hμN v (Subgroup.mem_sup_right hv)) ?_, ?_⟩
    · have hyb' : μ * y' * μ⁻¹ = b' := by
        rw [← hbraid, hμinv]
        calc μ * (μ * b' * μ) * μ = μ * μ * b' * (μ * μ) := by group
          _ = b' := by rw [hD.mul_self_eq_one hμD, one_mul, mul_one]
      have := (Commute.conj_iff μ).2 (commute_of_mem_rootGroup_of_commute hv hy'D hdy')
      rwa [hyb'] at this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hμinv]
      calc μ * (μ * v * μ) * μ = μ * μ * v * (μ * μ) := by group
        _ = v := by rw [hD.mul_self_eq_one hμD, one_mul, mul_one]
  · rw [← rootGroup_eq_of_mem hb', ← rootGroup_conj hclass, hbraid, rootGroup_eq_of_mem hy']

end Line

end CFSG.Timmesfeld.Bridge
