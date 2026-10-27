module

public import CFSG.Timmesfeld.Bridge.RootStructN0CycleEnd
public import CFSG.Timmesfeld.Bridge.RootStructN0Local

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type} [Group G] {D : Set G}

namespace TorusPath

variable {g : G} {p : ℤ → G}

theorem false_of_four (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) (h3 : ¬ ThreeLines D)
    (hbad : ThinAllBad D) (hP : TorusPath D g p) (h03 : ¬ Commute (p 0) (p 3))
    (hodd03 : Odd (orderOf (p 0 * p 3))) (h14 : ¬ Commute (p 1) (p 4))
    (hodd14 : Odd (orderOf (p 1 * p 4))) {μ₁ μ₂ k₁ k₂ u₁ u₂ : G} (hμ₁ : μ₁ ∈ D) (hμ₂ : μ₂ ∈ D)
    (hr₁ : ∀ i, μ₁ * p (3 - i) * μ₁⁻¹ ∈ rootSet D (p i))
    (hr₂ : ∀ i, μ₂ * p (5 - i) * μ₂⁻¹ ∈ rootSet D (p i))
    (hk₁ : k₁ ∈ rootGroup D (p 0)) (hu₁ : u₁ ∈ rootSet D (p 3)) (hμ₁eq : μ₁ = k₁ * u₁ * k₁⁻¹)
    (hk₂ : k₂ ∈ rootGroup D (p 1)) (hu₂ : u₂ ∈ rootSet D (p 4)) (hμ₂eq : μ₂ = k₂ * u₂ * k₂⁻¹)
    (h4 : orderOf (μ₂ * μ₁) = 4) : False := by
  have hclass := h.isClass
  have hD := h.root
  have := h.finite
  have hp0 := hP.mem 0
  have hp1 := hP.mem 1
  have hp2 := hP.mem 2
  have hp3 := hP.mem 3
  have hp4 := hP.mem 4
  have c01 : Commute (p 0) (p 1) := by simpa using hP.comm 0
  have c12 : Commute (p 1) (p 2) := by simpa using hP.comm 1
  have c23 : Commute (p 2) (p 3) := by simpa using hP.comm 2
  have c34 : Commute (p 3) (p 4) := by simpa using hP.comm 3
  have m01 : p 0 * p 1 ∈ D := by simpa using hP.mul_mem 0
  have m12 : p 1 * p 2 ∈ D := by simpa using hP.mul_mem 1
  have m23 : p 2 * p 3 ∈ D := by simpa using hP.mul_mem 2
  have m34 : p 3 * p 4 ∈ D := by simpa using hP.mul_mem 3
  have n01 : p 1 ∉ rootSet D (p 0) := by simpa using hP.not_mem 0
  have n12 : p 2 ∉ rootSet D (p 1) := by simpa using hP.not_mem 1
  have n23 : p 3 ∉ rootSet D (p 2) := by simpa using hP.not_mem 2
  have n34 : p 4 ∉ rootSet D (p 3) := by simpa using hP.not_mem 3
  have t1 : p 2 ∉ rootGroup D (p 0) ⊔ rootGroup D (p 1) := by simpa using hP.turn 1
  have t2 : p 3 ∉ rootGroup D (p 1) ⊔ rootGroup D (p 2) := by simpa using hP.turn 2
  have t3 : p 4 ∉ rootGroup D (p 2) ⊔ rootGroup D (p 3) := by simpa using hP.turn 3
  have s02 : orderOf (p 0 * p 2) = 4 :=
    orderOf_mul_eq_four_of_path h hc hs hconn hAll hp0 hp1 hp2 c01 m01 n01 c12 m12 t1
  have s13 : orderOf (p 1 * p 3) = 4 :=
    orderOf_mul_eq_four_of_path h hc hs hconn hAll hp1 hp2 hp3 c12 m12 n12 c23 m23 t2
  have m21 : p 2 * p 1 ∈ D := by rw [← c12.eq]; exact m12
  have m32 : p 3 * p 2 ∈ D := by rw [← c23.eq]; exact m23
  have m10 : p 1 * p 0 ∈ D := by rw [← c01.eq]; exact m01
  have n21 : p 1 ∉ rootSet D (p 2) := fun h' => n12 (mem_rootSet_comm hp2 h')
  have n32 : p 2 ∉ rootSet D (p 3) := fun h' => n23 (mem_rootSet_comm hp3 h')
  have hL12 : p 3 ∉ rootGroup D (p 2) ⊔ rootGroup D (p 1) := by rwa [sup_comm]
  have hmem2 : ∀ {t : G}, t ∈ D → t ∈ rootGroup D (p 2) ⊔ rootGroup D (p 1) →
      t ∈ rootGroup D (p 2) ⊔ rootGroup D (p 3) → t ∈ rootSet D (p 2) := fun ht ht1 ht2 =>
    mem_rootSet_of_mem_two_lines h hc hs hp2 hp1 hp3 ⟨c12.symm, m21, n21⟩ ⟨c23, m23, n23⟩ hL12 ht
      ht1 ht2
  have hk₁T : k₁ ∈ rootSet D (p 0) := by
    rcases (mem_rootGroup_iff_of_rootClosure hD hc hp0).1 hk₁ with rfl | h'
    · exfalso
      have h1 := hr₁ 0
      simp only [sub_zero, hμ₁eq, one_mul, inv_one, mul_one] at h1
      have hc3 : Commute u₁ (p 3) := commute_of_mem_rootSet hp3 hu₁ (mem_rootSet_self hp3)
      rw [hc3.eq, mul_inv_cancel_right] at h1
      exact h03 ((h1.2 (p 0) hp0).2 (Commute.refl _)).symm
    · exact h'
  have hk₂T : k₂ ∈ rootSet D (p 1) := by
    rcases (mem_rootGroup_iff_of_rootClosure hD hc hp1).1 hk₂ with rfl | h'
    · exfalso
      have h1 := hr₂ 1
      rw [show (5 : ℤ) - 1 = 4 by norm_num] at h1
      simp only [hμ₂eq, one_mul, inv_one, mul_one] at h1
      have hc4 : Commute u₂ (p 4) := commute_of_mem_rootSet hp4 hu₂ (mem_rootSet_self hp4)
      rw [hc4.eq, mul_inv_cancel_right] at h1
      exact h14 ((h1.2 (p 1) hp1).2 (Commute.refl _)).symm
    · exact h'
  have hk₁D := hk₁T.1
  have hk₂D := hk₂T.1
  have hk₁i : k₁⁻¹ = k₁ := hD.inv_eq hk₁D
  have hk₂i : k₂⁻¹ = k₂ := hD.inv_eq hk₂D
  have hk₁1 : Commute k₁ (p 1) := commute_of_mem_rootSet_of_commute hp1 hk₁T
    (mem_rootSet_self hp1) c01
  have hk₂2 : Commute k₂ (p 2) := commute_of_mem_rootSet_of_commute hp2 hk₂T
    (mem_rootSet_self hp2) c12
  set c₁ := k₁ * p 2 * k₁⁻¹ with hc₁
  set v₁ := k₁ * p 3 * k₁⁻¹ with hv₁
  set c₂ := k₂ * p 3 * k₂⁻¹ with hc₂
  set v₂ := k₂ * p 4 * k₂⁻¹ with hv₂
  have hc₁D : c₁ ∈ D := conj_mem_of_isClass hclass _ hp2
  have hv₁D : v₁ ∈ D := conj_mem_of_isClass hclass _ hp3
  have hc₂D : c₂ ∈ D := conj_mem_of_isClass hclass _ hp3
  have hv₂D : v₂ ∈ D := conj_mem_of_isClass hclass _ hp4
  have hkk₁ : ∀ t, k₁ * (k₁ * t * k₁⁻¹) * k₁⁻¹ = t := fun t => by
    rw [show k₁ * (k₁ * t * k₁⁻¹) * k₁⁻¹ = (k₁ * k₁) * t * (k₁ * k₁)⁻¹ by group,
      hD.mul_self_eq_one hk₁D, one_mul, inv_one, mul_one]
  have hkk₂ : ∀ t, k₂ * (k₂ * t * k₂⁻¹) * k₂⁻¹ = t := fun t => by
    rw [show k₂ * (k₂ * t * k₂⁻¹) * k₂⁻¹ = (k₂ * k₂) * t * (k₂ * k₂)⁻¹ by group,
      hD.mul_self_eq_one hk₂D, one_mul, inv_one, mul_one]
  have hconjT : ∀ {k a b : G}, a ∈ rootSet D b → k * a * k⁻¹ ∈ rootSet D (k * b * k⁻¹) :=
    fun hab => conj_mem_rootSet_conj hclass hab
  have hconjnT : ∀ {k a b : G}, a ∉ rootSet D b → k * a * k⁻¹ ∉ rootSet D (k * b * k⁻¹) := by
    intro k a b hab h'
    apply hab
    have := conj_mem_rootSet_conj hclass (μ := k⁻¹) h'
    simpa [mul_assoc] using this
  have s20 : orderOf (p 2 * p 0) = 4 := by rwa [orderOf_mul_comm_eq]
  have s31 : orderOf (p 3 * p 1) = 4 := by rwa [orderOf_mul_comm_eq]
  have hk₁L : ∀ {t : G}, t ∈ rootGroup D (p 2) ⊔ rootGroup D (p 1) →
      k₁ * t * k₁⁻¹ ∈ rootGroup D (p 2) ⊔ rootGroup D (p 1) := fun ht =>
    conj_mem_sup_of_mem_rootGroup h hc hs hp2 hp1 c12.symm m21 hp0 c01.symm m10 s20 hk₁ ht
  have hk₂L : ∀ {t : G}, t ∈ rootGroup D (p 3) ⊔ rootGroup D (p 2) →
      k₂ * t * k₂⁻¹ ∈ rootGroup D (p 3) ⊔ rootGroup D (p 2) := fun ht =>
    conj_mem_sup_of_mem_rootGroup h hc hs hp3 hp2 c23.symm m32 hp1 c12.symm m21 s31 hk₂ ht
  have hc₁L : c₁ ∈ rootGroup D (p 2) ⊔ rootGroup D (p 1) := hk₁L (left_mem_line hp2)
  have hc₂L : c₂ ∈ rootGroup D (p 3) ⊔ rootGroup D (p 2) := hk₂L (left_mem_line hp3)
  have hv₁L : v₁ ∉ rootGroup D (p 2) ⊔ rootGroup D (p 1) := fun h' => hL12 (by
    have := hk₁L h'
    rwa [hv₁, hkk₁] at this)
  have hv₂L : v₂ ∉ rootGroup D (p 3) ⊔ rootGroup D (p 2) := fun h' => t3 (by
    have := hk₂L h'
    rw [hv₂, hkk₂] at this
    rwa [sup_comm] at this)
  have h4k₁ : orderOf (p 2 * k₁) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hp2 hp0 (mem_rootSet_self hp2) hk₁T s20
  have h4k₂ : orderOf (p 3 * k₂) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hp3 hp1 (mem_rootSet_self hp3) hk₂T s31
  have hc₁T2 : c₁ ∉ rootSet D (p 2) := fun h' =>
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hp2) (hD.mul_self_eq_one hk₁D) h4k₁
      (commute_of_conj_mem_rootSet hclass hD hp2 hk₁D h')
  have hc₂T3 : c₂ ∉ rootSet D (p 3) := fun h' =>
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hp3) (hD.mul_self_eq_one hk₂D) h4k₂
      (commute_of_conj_mem_rootSet hclass hD hp3 hk₂D h')
  have hc₁T1 : c₁ ∉ rootSet D (p 1) := by
    have := hconjnT (k := k₁) n12
    rwa [hk₁1.eq, mul_inv_cancel_right] at this
  have hc₂T2 : c₂ ∉ rootSet D (p 2) := by
    have := hconjnT (k := k₂) n23
    rwa [hk₂2.eq, mul_inv_cancel_right] at this
  have hne1 : ∀ {a t : G}, a ∈ D → t ∉ rootSet D a → a * t ≠ 1 := fun ha htT h1 => htT (by
    rw [eq_inv_of_mul_eq_one_right h1, hD.inv_eq ha]
    exact mem_rootSet_self ha)
  have hpc₁ : Commute (p 2) c₁ :=
    commute_of_mem_sup_rootGroup hp2 hp1 c12.symm (left_mem_line hp2) hc₁L
  have hpc₁D : p 2 * c₁ ∈ D := mem_of_mem_sup_rootGroup h hc hs hp2 hp1 c12.symm m21 n21
    (Subgroup.mul_mem _ (left_mem_line hp2) hc₁L) (hne1 hp2 hc₁T2)
  have hpc₂ : Commute (p 2) c₂ :=
    commute_of_mem_sup_rootGroup hp3 hp2 c23.symm (right_mem_line hp2) hc₂L
  have hpc₂D : p 2 * c₂ ∈ D := mem_of_mem_sup_rootGroup h hc hs hp3 hp2 c23.symm m32 n32
    (Subgroup.mul_mem _ (right_mem_line hp2) hc₂L) (hne1 hp2 hc₂T2)
  have h1c₁ : Commute (p 1) c₁ :=
    commute_of_mem_sup_rootGroup hp2 hp1 c12.symm (right_mem_line hp1) hc₁L
  have h1c₁D : p 1 * c₁ ∈ D := mem_of_mem_sup_rootGroup h hc hs hp2 hp1 c12.symm m21 n21
    (Subgroup.mul_mem _ (right_mem_line hp1) hc₁L) (hne1 hp1 hc₁T1)
  have h3c₂ : Commute (p 3) c₂ :=
    commute_of_mem_sup_rootGroup hp3 hp2 c23.symm (left_mem_line hp3) hc₂L
  have h3c₂D : p 3 * c₂ ∈ D := mem_of_mem_sup_rootGroup h hc hs hp3 hp2 c23.symm m32 n32
    (Subgroup.mul_mem _ (left_mem_line hp3) hc₂L) (hne1 hp3 hc₂T3)
  have hv₁c₁ : Commute v₁ c₁ := (Commute.conj_iff k₁).2 c23.symm
  have hv₁c₁D : v₁ * c₁ ∈ D := by
    have := conj_mem_of_isClass hclass k₁ m32
    rwa [show k₁ * (p 3 * p 2) * k₁⁻¹ = v₁ * c₁ by rw [hv₁, hc₁]; group] at this
  have hc₁Tv : c₁ ∉ rootSet D v₁ := hconjnT n32
  have hv₂c₂ : Commute v₂ c₂ := (Commute.conj_iff k₂).2 c34.symm
  have hv₂c₂D : v₂ * c₂ ∈ D := by
    have := conj_mem_of_isClass hclass k₂ (show p 4 * p 3 ∈ D by rw [← c34.eq]; exact m34)
    rwa [show k₂ * (p 4 * p 3) * k₂⁻¹ = v₂ * c₂ by rw [hv₂, hc₂]; group] at this
  have hc₂Tv : c₂ ∉ rootSet D v₂ := hconjnT (fun h' => n34 (mem_rootSet_comm hp4 h'))
  have hpc₁T : p 2 ∉ rootSet D c₁ := fun h' => hc₁T2 (mem_rootSet_comm hc₁D h')
  have hΛ₁ : rootGroup D c₁ ⊔ rootGroup D (p 2) = rootGroup D (p 2) ⊔ rootGroup D (p 1) :=
    sup_rootGroup_eq_of_mem h hc hs hp2 hp1 c12.symm m21 n21 hc₁L (left_mem_line hp2)
      (hD.ne_one hc₁D) (hD.ne_one hp2) hpc₁T
  have hc₂Λ₁ : c₂ ∉ rootGroup D (p 2) ⊔ rootGroup D (p 1) := fun h' =>
    hc₂T2 (hmem2 hc₂D h' (by rwa [sup_comm]))
  have h4c : orderOf (c₁ * c₂) = 4 :=
    orderOf_mul_eq_four_of_path h hc hs hconn hAll hc₁D hp2 hc₂D hpc₁.symm
      (by rw [← hpc₁.eq]; exact hpc₁D) hpc₁T hpc₂ hpc₂D (by rw [hΛ₁]; exact hc₂Λ₁)
  have hμ₁v : μ₁ ∈ rootSet D v₁ := by rw [hμ₁eq]; exact hconjT hu₁
  have hμ₂v : μ₂ ∈ rootSet D v₂ := by rw [hμ₂eq]; exact hconjT hu₂
  have h4v : orderOf (v₁ * v₂) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hμ₁ hμ₂ (mem_rootSet_comm hv₁D hμ₁v)
      (mem_rootSet_comm hv₂D hμ₂v) (by rwa [orderOf_mul_comm_eq])
  have h4c₁3 : orderOf (c₁ * p 3) = 4 :=
    orderOf_mul_eq_four_of_path h hc hs hconn hAll hc₁D hp2 hp3 hpc₁.symm
      (by rw [← hpc₁.eq]; exact hpc₁D) hpc₁T c23 m23 (by rw [hΛ₁]; exact hL12)
  have hpv₁ : ¬ Commute (p 2) v₁ := by
    have e : p 2 * v₁ = k₁ * (c₁ * p 3) * k₁⁻¹ := by
      rw [show k₁ * (c₁ * p 3) * k₁⁻¹ = (k₁ * c₁ * k₁⁻¹) * (k₁ * p 3 * k₁⁻¹) by group, hc₁,
        hkk₁]
    have h4' : orderOf (p 2 * v₁) = 4 := by rw [e, orderOf_conj_eq]; exact h4c₁3
    exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hp2) (hD.mul_self_eq_one hv₁D)
      h4'
  obtain ⟨hk₁3, hoddk₁3⟩ := opposite_of_mem_rootSet_of_opposite hD hp0 hp3 hk₁T
    (mem_rootSet_self hp3) ⟨h03, hodd03⟩
  obtain ⟨hv₁3, hoddv₁3⟩ := opposite_conj_self hD hk₁D hp3 hk₁3 hoddk₁3
  have h4v₂3 : orderOf (p 3 * v₂) = 4 :=
    orderOf_mul_eq_four_of_path h hc hs hconn hAll hp3 hc₂D hv₂D h3c₂ h3c₂D hc₂T3 hv₂c₂.symm
      (by rw [← hv₂c₂.eq]; exact hv₂c₂D) (by
        rw [sup_rootGroup_eq_of_mem h hc hs hp3 hp2 c23.symm m32 n32 (left_mem_line hp3) hc₂L
          (hD.ne_one hp3) (hD.ne_one hc₂D) hc₂T3]
        exact hv₂L)
  have hk₂1 : k₂ * p 1 * k₂⁻¹ ∈ rootSet D (p 1) := by
    rw [(commute_of_mem_rootSet hp1 hk₂T (mem_rootSet_self hp1)).eq, mul_inv_cancel_right]
    exact mem_rootSet_self hp1
  obtain ⟨h1v₂, hodd1v₂⟩ := opposite_conj_of_mem_rootSet hD hclass hp1 hp4 hk₂1 h14 hodd14
  have h4c₂1 : orderOf (p 1 * c₂) = 4 :=
    orderOf_mul_eq_four_of_path h hc hs hconn hAll hp1 hp2 hc₂D c12 m12 n12 hpc₂ hpc₂D
      (by rw [sup_comm]; exact hc₂Λ₁)
  have h4v₁1 : orderOf (p 1 * v₁) = 4 :=
    orderOf_mul_eq_four_of_path h hc hs hconn hAll hp1 hc₁D hv₁D h1c₁ h1c₁D hc₁T1 hv₁c₁.symm
      (by rw [← hv₁c₁.eq]; exact hv₁c₁D) (by
        rw [sup_rootGroup_eq_of_mem h hc hs hp2 hp1 c12.symm m21 n21 (right_mem_line hp1) hc₁L
          (hD.ne_one hp1) (hD.ne_one hc₁D) hc₁T1]
        exact hv₁L)
  exact ThinAllBad.false_of_special_of_collinear h hc hs hconn hAll hbad h3 hp2 hc₁D hc₂D hv₁D
    hv₂D hp3 hp1 hpc₁ hpc₁D hpc₂ hpc₂D h4c hv₁c₁ hv₁c₁D hc₁Tv hv₂c₂ hv₂c₂D hc₂Tv h4v hpv₁ hv₁3
    hoddv₁3 (by rwa [orderOf_mul_comm_eq]) h4v₂3 (fun h' => h1v₂ h'.symm)
    (by rwa [orderOf_mul_comm_eq]) h4c₂1 h4v₁1

end TorusPath

end CFSG.Timmesfeld.Bridge
