module

public import CFSG.Timmesfeld.Bridge.RootStructR2Line
public import CFSG.Timmesfeld.Bridge.RootStructThmC

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

section Thin

variable {a d : G} (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem exists_conj_eq_mul_of_mem_rootSet (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {β γ : G} (hβ : β ∈ rootSet D a)
    (hγ : γ ∈ rootSet D d) : ∃ τ ∈ D, Commute τ a ∧ β * γ = τ * γ * τ⁻¹ := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hdQ : d ∈ Moufang.twoCore a :=
    mem_twoCore_of_collinear hclass hD ha hd had.symm (by rw [← had.eq]; exact hadD)
  obtain ⟨t, ht, htQ, h4⟩ :=
    exists_special_of_mem_twoCore hclass hD (oppositeDetermines_of_hyp h) ha hd hdQ hdT
  have hw := sq_mem_rootSet_of_mem_twoCore hD hc (nCoreCommutatorInRoot_of_hyp h hc) ha hd ht
    hdQ htQ h4
  obtain ⟨-, h2, -⟩ := special_pair_rootSet h hc hs hd ht h4
  rw [rootSet_eq_of_mem hw] at h2
  obtain ⟨τ, hτ, hγτ⟩ := h2 γ hγ β hβ
  have hτQ : τ ∈ Moufang.twoCore a := mem_twoCore_of_mem_rootSet hclass hD ha ht htQ hτ
  refine ⟨τ, hτ.1, Moufang.commute_of_mem_twoCore hτQ, ?_⟩
  have hγ2 := hD.mul_self_eq_one hγ.1
  have hβγ : Commute β γ := commute_of_mem_rootGroup_of_commute' hd
    (rootSet_subset_rootGroup D a hβ) (rootSet_subset_rootGroup D d hγ) had
  rw [hβγ.eq, ← hγτ, hD.inv_eq hτ.1, sq]
  calc γ * (γ * τ * (γ * τ)) = (γ * γ) * τ * γ * τ := by simp only [mul_assoc]
    _ = τ * γ * τ := by rw [hγ2, one_mul]

theorem lineTI_of_normalizesLine (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    (h₁ : ∀ y ∈ D, Commute y a → NormalizesLine D a d y)
    (h₂ : ∀ y ∈ D, Commute y d → NormalizesLine D a d y) : LineTI D a d := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hpt : ∀ {e y : G}, e ∈ D → e ∈ rootGroup D a ⊔ rootGroup D d → y ∈ D → Commute y e →
      NormalizesLine D a d y := by
    intro e y he heL hy hye
    obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_line hd had heL
    by_cases hγ1 : γ = 1
    · subst hγ1
      rw [mul_one] at he hye
      have hβT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc ha hβ (hD.ne_one he)
      exact h₁ y hy ((hβT.2 y hy).1 hye.symm).symm
    by_cases hβ1 : β = 1
    · subst hβ1
      rw [one_mul] at he hye
      have hγT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hd hγ (hD.ne_one he)
      exact h₂ y hy ((hγT.2 y hy).1 hye.symm).symm
    have hβT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc ha hβ hβ1
    have hγT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hd hγ hγ1
    obtain ⟨τ, hτ, hτa, hconj⟩ :=
      exists_conj_eq_mul_of_mem_rootSet h hc hs ha hd had hadD hdT hβT hγT
    rw [hconj] at hye
    have hτ2 := hD.mul_self_eq_one hτ
    have hy' : τ⁻¹ * y * τ ∈ D := by simpa using conj_mem_of_isClass hclass τ⁻¹ hy
    have hy'γ : Commute (τ⁻¹ * y * τ) γ := by
      have := (Commute.conj_iff τ⁻¹).2 hye
      simpa [mul_assoc] using this
    have hNy' := h₂ _ hy' ((hγT.2 _ hy').1 hy'γ.symm).symm
    have hNτ := h₁ τ hτ hτa
    intro u hu
    have heq : y * u * y⁻¹ = τ * ((τ⁻¹ * y * τ) * (τ⁻¹ * u * τ) * (τ⁻¹ * y * τ)⁻¹) * τ⁻¹ := by
      group
    rw [heq]
    refine hNτ _ (hNy' _ ?_)
    have := hNτ u hu
    rw [hD.inv_eq hτ] at this ⊢
    exact this
  intro g hg u hu huL hguL v hv hvL
  by_cases hgu : Commute g u
  · exact hpt hu huL hg hgu v hvL
  have hD2 := hD.mul_self_eq_one hg
  have hne : u * (g * u * g⁻¹) ≠ 1 := by
    intro h1
    apply hgu
    have h2 : g * u * g⁻¹ = u := (eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq hu)
    calc g * u = g * u * g⁻¹ * g := by group
      _ = u * g := by rw [h2]
  have heL := Subgroup.mul_mem _ huL hguL
  have heD := mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT heL hne
  have hcomm := commute_of_mem_sup_rootGroup ha hd had huL hguL
  have hge : Commute g (u * (g * u * g⁻¹)) := by
    rw [hD.inv_eq hg] at hcomm ⊢
    show g * (u * (g * u * g)) = u * (g * u * g) * g
    calc g * (u * (g * u * g)) = (g * u * g) * u * g := by simp only [mul_assoc]
      _ = u * (g * u * g) * g := by rw [← hcomm.eq]
  exact hpt heD heL hg hge v hvL

theorem normalizesLine_of_thin (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    (hthin : ∀ c' ∈ D, Commute a c' → a * c' ∈ D → Commute d c' → d * c' ∈ D →
      c' ∈ rootGroup D a ⊔ rootGroup D d) {y : G} (hy : y ∈ D) (hya : Commute y a) :
    NormalizesLine D a d y := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hdQ : d ∈ Moufang.twoCore a :=
    mem_twoCore_of_collinear hclass hD ha hd had.symm (by rw [← had.eq]; exact hadD)
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hd hy with hdy | h4 | hodd
  · intro u hu
    rw [(commute_of_mem_line hy hya hdy.symm hu).eq, mul_inv_cancel_right]
    exact hu
  · obtain ⟨hzD, hdz, -, hydy⟩ := sq_mem_of_orderOf_eq_four hD hd hy h4
    have hd' : y * d * y⁻¹ = d * (d * y) ^ 2 := by rw [hD.inv_eq hy, hydy]
    have hd'D : y * d * y⁻¹ ∈ D := conj_mem_of_isClass hclass y hd
    have had' : Commute a (y * d * y⁻¹) := by
      have := (Commute.conj_iff y).2 had
      rwa [hya.eq, mul_inv_cancel_right] at this
    have had'D : a * (y * d * y⁻¹) ∈ D := by
      have := conj_mem_of_isClass hclass y hadD
      rwa [show y * (a * d) * y⁻¹ = (y * a * y⁻¹) * (y * d * y⁻¹) by group, hya.eq,
        mul_inv_cancel_right] at this
    have hdd' : Commute d (y * d * y⁻¹) := by
      rw [hd']
      exact (Commute.refl d).mul_right hdz
    have hdd'D : d * (y * d * y⁻¹) ∈ D := by
      rw [hd', ← mul_assoc, hD.mul_self_eq_one hd, one_mul]
      exact hzD
    have hd'L := hthin _ hd'D had' had'D hdd' hdd'D
    have hd'1 : y * d * y⁻¹ ≠ 1 := hD.ne_one hd'D
    have hle : (rootGroup D a ⊔ rootGroup D d).map (MulAut.conj y).toMonoidHom ≤
        rootGroup D a ⊔ rootGroup D d := by
      rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass, hya.eq,
        mul_inv_cancel_right]
      exact sup_le le_sup_left
        (rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT hd'L hd'1)
    intro u hu
    exact hle ⟨u, hu, rfl⟩
  · exact absurd ⟨hodd.2, hodd.1⟩ (not_opposite_of_mem_twoCore_of_commute hD hdQ hy hya)

theorem lineTI_of_thin (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a)
    (hthin : ∀ c' ∈ D, Commute a c' → a * c' ∈ D → Commute d c' → d * c' ∈ D →
      c' ∈ rootGroup D a ⊔ rootGroup D d) : LineTI D a d := by
  have hD := h.root
  have hdaD : d * a ∈ D := by rw [← had.eq]; exact hadD
  have haT : a ∉ rootSet D d := fun h' => hdT (mem_rootSet_comm hd h')
  have hthin' : ∀ c' ∈ D, Commute d c' → d * c' ∈ D → Commute a c' → a * c' ∈ D →
      c' ∈ rootGroup D d ⊔ rootGroup D a := fun c' hc' h1 h2 h3 h4 => by
    rw [sup_comm]
    exact hthin c' hc' h3 h4 h1 h2
  refine lineTI_of_normalizesLine h hc hs ha hd had hadD hdT
    (fun y hy hya => normalizesLine_of_thin h hc hs ha hd had hadD hdT hthin hy hya)
    (fun y hy hyd => ?_)
  have := normalizesLine_of_thin h hc hs hd ha had.symm hdaD haT hthin' hy hyd
  intro u hu
  rw [sup_comm] at hu ⊢
  exact this u hu

theorem normalizesLine_of_mem_twoCore (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {y : G} (hy : y ∈ D)
    (hyQ : y ∈ Moufang.twoCore a) : NormalizesLine D a d y := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hya : Commute y a := Moufang.commute_of_mem_twoCore hyQ
  have hdN : d ∈ nCore D a :=
    mem_nCore_of_collinear hclass hD ha hd had.symm (by rw [← had.eq]; exact hadD)
  have hcomm := nCoreCommutatorInRoot_of_hyp h hc a ha y (mem_nCore_of_mem_twoCore hy hyQ) d hdN
  have hd'L : y * d * y⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
    have heq : y * d * y⁻¹ = y * d * y⁻¹ * d⁻¹ * d := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (right_mem_line hd)
  have hle : (rootGroup D a ⊔ rootGroup D d).map (MulAut.conj y).toMonoidHom ≤
      rootGroup D a ⊔ rootGroup D d := by
    rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass, hya.eq,
      mul_inv_cancel_right]
    exact sup_le le_sup_left (rootGroup_le_sup_of_mem h hc hs ha hd had hadD hdT hd'L
      (hD.ne_one (conj_mem_of_isClass hclass y hd)))
  intro u hu
  exact hle ⟨u, hu, rfl⟩

end Thin

section AllLines

variable {a d : G}

theorem lineTI_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hL : LineTI D a d) (g : G) :
    LineTI D (g * a * g⁻¹) (g * d * g⁻¹) := by
  have hmem : ∀ {u : G}, u ∈ rootGroup D (g * a * g⁻¹) ⊔ rootGroup D (g * d * g⁻¹) ↔
      g⁻¹ * u * g ∈ rootGroup D a ⊔ rootGroup D d := by
    intro u
    rw [rootGroup_conj hclass, rootGroup_conj hclass, ← Subgroup.map_sup, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [mul_assoc] using hv
    · intro hu
      exact ⟨_, hu, by simp [mul_assoc]⟩
  intro x hx u hu huL hxuL v hv hvL
  rw [hmem] at huL hxuL hvL ⊢
  have hx' : g⁻¹ * x * g ∈ D := by simpa using conj_mem_of_isClass hclass g⁻¹ hx
  have hu' : g⁻¹ * u * g ∈ D := by simpa using conj_mem_of_isClass hclass g⁻¹ hu
  have hv' : g⁻¹ * v * g ∈ D := by simpa using conj_mem_of_isClass hclass g⁻¹ hv
  have h1 := hL _ hx' _ hu' huL (by
    rw [show g⁻¹ * x * g * (g⁻¹ * u * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * u * x⁻¹) * g by group]
    exact hxuL) _ hv' hvL
  rwa [show g⁻¹ * x * g * (g⁻¹ * v * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * v * x⁻¹) * g by group]
    at h1

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem mem_twoCore_of_commute_of_lineTI (hconn : Moufang.ExcCollConnected D) (ha : a ∈ D)
    (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    (hL : LineTI D a d) {e y : G} (he : e ∈ D) (hy : y ∈ D) (hye : Commute y e) :
    y ∈ Moufang.twoCore e := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass ha he)
  have ha' : g * a * g⁻¹ ∈ D := conj_mem_of_isClass hclass g ha
  have hd' : g * d * g⁻¹ ∈ D := conj_mem_of_isClass hclass g hd
  have had' : Commute (g * a * g⁻¹) (g * d * g⁻¹) := (Commute.conj_iff g).2 had
  have hadD' : g * a * g⁻¹ * (g * d * g⁻¹) ∈ D := by
    rw [show g * a * g⁻¹ * (g * d * g⁻¹) = g * (a * d) * g⁻¹ by group]
    exact conj_mem_of_isClass hclass g hadD
  have hdT' : g * d * g⁻¹ ∉ rootSet D (g * a * g⁻¹) := by
    rw [rootSet_conj hclass]
    rintro ⟨x, hx, hxd⟩
    have hxd' : x = d := by
      have := congrArg (fun z => g⁻¹ * z * g) hxd
      simpa [mul_assoc] using this
    exact hdT (hxd' ▸ hx)
  rcases mem_rootSet_or_collinear_of_lineTI h hc hs hconn ha' hd' had' hadD' hdT'
      (lineTI_conj hclass hL g) hy hye with hT | ⟨h1, h2⟩
  · exact (rootSet_subset_twoCore_self hclass hD hc ha' y hT).2
  · exact mem_twoCore_of_collinear hclass hD ha' hy h1.symm (h1.eq ▸ h2)

theorem lineTI_of_lineTI (hconn : Moufang.ExcCollConnected D) (ha : a ∈ D) (hd : d ∈ D)
    (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) (hL : LineTI D a d)
    {b b' : G} (hb : b ∈ D) (hb' : b' ∈ D) (hbb' : Commute b b') (hbb'D : b * b' ∈ D)
    (hb'T : b' ∉ rootSet D b) : LineTI D b b' := by
  have hD := h.root
  have hb'bD : b' * b ∈ D := by rw [← hbb'.eq]; exact hbb'D
  have hbT : b ∉ rootSet D b' := fun h' => hb'T (mem_rootSet_comm hb' h')
  refine lineTI_of_normalizesLine h hc hs hb hb' hbb' hbb'D hb'T
    (fun y hy hyb => normalizesLine_of_mem_twoCore h hc hs hb hb' hbb' hbb'D hb'T hy
      (mem_twoCore_of_commute_of_lineTI h hc hs hconn ha hd had hadD hdT hL hb hy hyb))
    (fun y hy hyb' => ?_)
  have := normalizesLine_of_mem_twoCore h hc hs hb' hb hbb'.symm hb'bD hbT hy
    (mem_twoCore_of_commute_of_lineTI h hc hs hconn ha hd had hadD hdT hL hb' hy hyb')
  intro u hu
  rw [sup_comm] at hu ⊢
  exact this u hu

theorem mem_rootSet_sq_of_lineTI {u v w : G} (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D)
    (h4 : orderOf (u * v) = 4) (huw : Commute u w) (huwD : u * w ∈ D) (hvw : Commute v w)
    (hL : LineTI D u w) : w ∈ rootSet D ((u * v) ^ 2) := by
  have hD := h.root
  have huv := not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hu)
    (hD.mul_self_eq_one hv) h4
  have hwT : w ∉ rootSet D u := fun h' => huv ((h'.2 v hv).1 hvw.symm)
  have hN := normalizesLine_of_commute h hc hs hu hw huw huwD hwT hL hw (right_mem_line hw) hv hvw
  obtain ⟨-, hT⟩ := sq_mem_rootSet_of_normalizesLine h hc hs hu hw huw huwD hwT hv hN hw
    (right_mem_line hw) hu (left_mem_line hu) hvw fun h' => huv h'.symm
  exact mem_rootSet_comm hw hT

theorem opposite_of_lineTI {u v w : G} (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D)
    (h4 : orderOf (u * v) = 4) (hvw : Commute v w) (hwz : ¬ Commute w ((u * v) ^ 2))
    (hL : LineTI D ((u * v) ^ 2) v) : ¬ Commute u w ∧ Odd (orderOf (u * w)) := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have huv := not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hu)
    (hD.mul_self_eq_one hv) h4
  obtain ⟨hzD, huz, hvz, -⟩ := sq_mem_of_orderOf_eq_four hD hu hv h4
  have h4' : orderOf (v * u) = 4 := by rwa [orderOf_mul_comm_eq]
  have hzvD : (u * v) ^ 2 * v ∈ D := by
    rw [← hvz.eq, mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hu) (hD.mul_self_eq_one hv) h4]
    exact mul_sq_mem_of_orderOf_eq_four hclass hD hv hu h4'
  have hvT : v ∉ rootSet D ((u * v) ^ 2) := fun h' => huv ((h'.2 u hu).2 huz.symm).symm
  have hNu := normalizesLine_of_commute h hc hs hzD hv hvz.symm hzvD hvT hL hzD
    (left_mem_line hzD) hu huz
  have hNw := normalizesLine_of_commute h hc hs hzD hv hvz.symm hzvD hvT hL hv
    (right_mem_line hv) hw hvw.symm
  exact opposite_of_normalizesLine h hc hs hzD hv hvz.symm hzvD hvT hu hw hNu hNw
    (fun h' => huv h'.2) (fun h' => hwz h'.1) hzD hv (left_mem_line hzD) (right_mem_line hv) huz
    hvw.symm hvT

end AllLines

@[expose] def ThinGate (D : Set G) : Prop :=
  ∀ b ∈ D, ∀ x ∈ D, ¬ Commute b x → Odd (orderOf (b * x)) → OneOpposite D b x →
    ∀ a ∈ D, Commute b a → b * a ∈ D → a ∉ rootSet D b →
      ∃ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a ∧ orderOf (x * p) = 4

theorem thinOneOpposite_of_gate (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hK : ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a → LineTI D a d →
      ThinGate D) : ThinOneOpposite D := by
  intro a ha b hb c hcD x hx hab habD hbc hbcD hbx hoddbx hax hoddax hxc hthin
  have := h.finite
  have hD := h.root
  have hcT : c ∉ rootSet D b := fun hcT => by
    have h1 := (orderOf_mul_eq_four_iff_of_mem_rootSet hD hb hcT hx).1
      ((orderOf_mul_comm_eq x c).trans hxc)
    rw [h1] at hoddbx
    exact absurd hoddbx (by decide)
  have hgate := hK b hb c hcD hbc hbcD hcT (lineTI_of_thin h hc hs hb hcD hbc hbcD hcT hthin)
  by_cases haT : a ∈ rootSet D b
  ·
    refine ⟨c, hcD, (haT.2 c hcD).2 hbc, ?_, hxc⟩
    exact mul_mem_of_mem_rootGroup h hc hs (nCoreCommutatorInRoot_of_hyp h hc) hb hcD hbc hbcD
      hcT (rootSet_subset_rootGroup D b haT) (rootSet_subset_rootGroup D c (mem_rootSet_self hcD))
      (Or.inl (hD.ne_one ha))
  have hbaD : b * a ∈ D := by rw [← hab.eq]; exact habD
  obtain ⟨p, hp, hpL, hxp⟩ := hgate b hb x hx hbx hoddbx ⟨c, hcD, hbc, hbcD, hxc⟩ a ha hab.symm
    hbaD haT
  have hap : Commute a p := commute_of_mem_sup_rootGroup hb ha hab.symm (right_mem_line ha) hpL
  have hne : a * p ≠ 1 := by
    intro h1
    have hpa : p = a := (eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq ha)
    rw [hpa, orderOf_mul_comm_eq] at hxp
    rw [hxp] at hoddax
    exact absurd hoddax (by decide)
  exact ⟨p, hp, hap, mem_of_mem_sup_rootGroup h hc hs hb ha hab.symm hbaD haT
    (Subgroup.mul_mem _ (right_mem_line ha) hpL) hne, hxp⟩

end CFSG.Timmesfeld.Bridge
