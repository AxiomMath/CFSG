module

public import CFSG.Timmesfeld.Bridge.RootStructN0CycleEnd

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type} [Group G] {D : Set G}

private theorem conj_mem_sup_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {k a d x : G}
    (hx : x ∈ rootGroup D a ⊔ rootGroup D d) :
    k * x * k⁻¹ ∈ rootGroup D (k * a * k⁻¹) ⊔ rootGroup D (k * d * k⁻¹) := by
  rw [rootGroup_conj hclass, rootGroup_conj hclass, ← Subgroup.map_sup]
  exact ⟨x, hx, rfl⟩

private theorem conj_not_mem_sup_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {k a d x : G}
    (hx : x ∉ rootGroup D a ⊔ rootGroup D d) :
    k * x * k⁻¹ ∉ rootGroup D (k * a * k⁻¹) ⊔ rootGroup D (k * d * k⁻¹) := fun h' =>
  hx (by simpa [mul_assoc] using conj_mem_sup_conj hclass (k := k⁻¹) h')

private theorem conj_not_mem_rootSet_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {k a b : G} (hab : a ∉ rootSet D b) : k * a * k⁻¹ ∉ rootSet D (k * b * k⁻¹) := fun h' =>
  hab (by simpa [mul_assoc] using conj_mem_rootSet_conj hclass (μ := k⁻¹) h')

private theorem conj_collinear (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {k a b : G}
    (hab : Commute a b) (habD : a * b ∈ D) :
    Commute (k * a * k⁻¹) (k * b * k⁻¹) ∧ k * a * k⁻¹ * (k * b * k⁻¹) ∈ D := by
  refine ⟨(Commute.conj_iff k).2 hab, ?_⟩
  have := conj_mem_of_isClass hclass k habD
  rwa [show k * (a * b) * k⁻¹ = k * a * k⁻¹ * (k * b * k⁻¹) by group] at this

private theorem isPeriod_of_eq {p : ℤ → G} {k k' : ℤ} (hk : IsPeriod D p k) (h : k = k') :
    IsPeriod D p k' :=
  h ▸ hk

private theorem reflection_point (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) {a₀ a₁ a₂ a₃ k u μ y : G}
    (h0 : a₀ ∈ D) (h1 : a₁ ∈ D) (h2 : a₂ ∈ D) (h3 : a₃ ∈ D) (c01 : Commute a₀ a₁)
    (m01 : a₀ * a₁ ∈ D) (n01 : a₁ ∉ rootSet D a₀) (c12 : Commute a₁ a₂) (m12 : a₁ * a₂ ∈ D)
    (n12 : a₂ ∉ rootSet D a₁) (c23 : Commute a₂ a₃) (m23 : a₂ * a₃ ∈ D)
    (n23 : a₃ ∉ rootSet D a₂) (t1 : a₂ ∉ rootGroup D a₀ ⊔ rootGroup D a₁)
    (t2 : a₃ ∉ rootGroup D a₁ ⊔ rootGroup D a₂) (h03 : ¬ Commute a₀ a₃)
    (hμ0 : μ * a₃ * μ⁻¹ ∈ rootSet D a₀) (hk : k ∈ rootGroup D a₀) (hu : u ∈ rootSet D a₃)
    (hμeq : μ = k * u * k⁻¹) (hy : y = k * a₂ * k⁻¹) :
    y ∈ D ∧ y ∈ rootGroup D a₂ ⊔ rootGroup D a₁ ∧ y ∉ rootSet D a₂ ∧ y ∉ rootSet D a₁ ∧
      (Commute μ y ∧ μ * y ∈ D ∧ y ∉ rootSet D μ) ∧ μ ∉ rootGroup D a₂ ⊔ rootGroup D a₁ ∧
      (Commute a₁ y ∧ a₁ * y ∈ D) ∧ (Commute a₂ y ∧ a₂ * y ∈ D) := by
  have hclass := h.isClass
  have hD := h.root
  have := h.finite
  subst hμeq
  subst hy
  have hkT : k ∈ rootSet D a₀ := by
    rcases (mem_rootGroup_iff_of_rootClosure hD hc h0).1 hk with rfl | h'
    · exfalso
      simp only [one_mul, inv_one, mul_one] at hμ0
      rw [(commute_of_mem_rootSet h3 hu (mem_rootSet_self h3)).eq, mul_inv_cancel_right] at hμ0
      exact h03 ((hμ0.2 a₀ h0).2 (Commute.refl _)).symm
    · exact h'
  have hkD := hkT.1
  have hk2 : k * k = 1 := hD.mul_self_eq_one hkD
  have hk1 : Commute k a₁ := commute_of_mem_rootSet_of_commute h1 hkT (mem_rootSet_self h1) c01
  have m21 : a₂ * a₁ ∈ D := by rw [← c12.eq]; exact m12
  have m10 : a₁ * a₀ ∈ D := by rw [← c01.eq]; exact m01
  have n21 : a₁ ∉ rootSet D a₂ := fun h' => n12 (mem_rootSet_comm h2 h')
  have n32 : a₂ ∉ rootSet D a₃ := fun h' => n23 (mem_rootSet_comm h3 h')
  have s20 : orderOf (a₂ * a₀) = 4 := by
    rw [orderOf_mul_comm_eq]
    exact orderOf_mul_eq_four_of_path h hc hs hconn hAll h0 h1 h2 c01 m01 n01 c12 m12 t1
  have hkL : ∀ {t : G}, t ∈ rootGroup D a₂ ⊔ rootGroup D a₁ →
      k * t * k⁻¹ ∈ rootGroup D a₂ ⊔ rootGroup D a₁ := fun ht =>
    conj_mem_sup_of_mem_rootGroup h hc hs h2 h1 c12.symm m21 h0 c01.symm m10 s20 hk ht
  have hyD : k * a₂ * k⁻¹ ∈ D := conj_mem_of_isClass hclass k h2
  have hyL : k * a₂ * k⁻¹ ∈ rootGroup D a₂ ⊔ rootGroup D a₁ := hkL (left_mem_line h2)
  have hyT2 : k * a₂ * k⁻¹ ∉ rootSet D a₂ := fun h' =>
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one h2) hk2
      (orderOf_mul_eq_four_of_mem_rootSet hD h2 h0 (mem_rootSet_self h2) hkT s20)
      (commute_of_conj_mem_rootSet hclass hD h2 hkD h')
  have hyT1 : k * a₂ * k⁻¹ ∉ rootSet D a₁ := by
    have := conj_not_mem_rootSet_conj hclass (k := k) n12
    rwa [hk1.eq, mul_inv_cancel_right] at this
  have hne1 : ∀ {a t : G}, a ∈ D → t ∉ rootSet D a → a * t ≠ 1 := fun ha htT h1' => htT (by
    rw [eq_inv_of_mul_eq_one_right h1', hD.inv_eq ha]
    exact mem_rootSet_self ha)
  have n2u : a₂ ∉ rootSet D u := by rw [rootSet_eq_of_mem hu]; exact n32
  obtain ⟨hua, huaD⟩ := collinear_of_collinear_mem_rootSet h hc hs hu.1 (mem_rootSet_comm h3 hu)
    h2 c23 m23 n2u
  have hcol := conj_collinear hclass (k := k) hua huaD
  have hμL : k * u * k⁻¹ ∉ rootGroup D a₂ ⊔ rootGroup D a₁ := by
    intro h'
    have huL : u ∈ rootGroup D a₂ ⊔ rootGroup D a₁ := by
      have := hkL h'
      rwa [show k * (k * u * k⁻¹) * k⁻¹ = (k * k) * u * (k * k)⁻¹ by group, hk2, one_mul,
        inv_one, mul_one] at this
    have huT : u ∉ rootSet D a₂ := fun h'' =>
      n23 (by rw [← rootSet_eq_of_mem h'']; exact mem_rootSet_comm h3 hu)
    have heq := sup_rootGroup_eq_of_mem h hc hs h2 h1 c12.symm m21 n21 (left_mem_line h2) huL
      (hD.ne_one h2) (hD.ne_one hu.1) huT
    apply t2
    rw [sup_comm, ← heq]
    exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D u (mem_rootSet_comm h3 hu))
  refine ⟨hyD, hyL, hyT2, hyT1, ⟨hcol.1, hcol.2, conj_not_mem_rootSet_conj hclass n2u⟩, hμL,
    ⟨commute_of_mem_sup_rootGroup h2 h1 c12.symm (right_mem_line h1) hyL, ?_⟩,
    ⟨commute_of_mem_sup_rootGroup h2 h1 c12.symm (left_mem_line h2) hyL, ?_⟩⟩
  · exact mem_of_mem_sup_rootGroup h hc hs h2 h1 c12.symm m21 n21
      (Subgroup.mul_mem _ (right_mem_line h1) hyL) (hne1 h1 hyT1)
  · exact mem_of_mem_sup_rootGroup h hc hs h2 h1 c12.symm m21 n21
      (Subgroup.mul_mem _ (left_mem_line h2) hyL) (hne1 h2 hyT2)

private theorem orderOf_conj_mul_eq_four (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    (hF : FixUnique D) {g : G} {p : ℤ → G} (hP : TorusPath D g p) {t : G} (ht : InvTorus D t)
    (htp : ∀ i, t * p i * t⁻¹ ∈ rootSet D (p i)) (j : ℤ) {y μ : G} (hy : y ∈ D)
    (hyL : y ∈ rootGroup D (p (j + 1)) ⊔ rootGroup D (p j)) (hy1 : y ∉ rootSet D (p (j + 1)))
    (hy0 : y ∉ rootSet D (p j)) (hμ : μ ∈ D) (hμy : Commute μ y) (hμyD : μ * y ∈ D)
    (hμL : μ ∉ rootGroup D (p (j + 1)) ⊔ rootGroup D (p j)) :
    orderOf (t * μ * t⁻¹ * y) = 4 := by
  have hclass := h.isClass
  have hD := h.root
  have hd := hP.mem (j + 1)
  have ha := hP.mem j
  have hda : Commute (p (j + 1)) (p j) := (hP.comm j).symm
  have hdaD : p (j + 1) * p j ∈ D := by rw [← (hP.comm j).eq]; exact hP.mul_mem j
  have haT : p j ∉ rootSet D (p (j + 1)) := fun h' => hP.not_mem j (mem_rootSet_comm hd h')
  have hfL : p (j + 1 + 1) ∉ rootGroup D (p (j + 1)) ⊔ rootGroup D (p j) := by
    have := hP.turn (j + 1)
    rwa [add_sub_cancel_right, sup_comm] at this
  have hy'D : t * y * t⁻¹ ∈ D := conj_mem_of_isClass hclass t hy
  have hμ'D : t * μ * t⁻¹ ∈ D := conj_mem_of_isClass hclass t hμ
  have hy'L : t * y * t⁻¹ ∈ rootGroup D (p (j + 1)) ⊔ rootGroup D (p j) :=
    conj_mem_sup_of_conj_mem_rootSet hclass (htp _) (htp _) hyL
  have hy'T : t * y * t⁻¹ ∉ rootSet D y := fun h' => hy0 ((hF hd ha hda hdaD haT
    (hP.mem (j + 1 + 1)) (hP.comm (j + 1)) (hP.mul_mem (j + 1)) hfL ht (htp _)
    (fun u hu => conj_mem_sup_of_conj_mem_rootSet hclass (htp _) (htp _) hu)
    (fun u hu => conj_mem_sup_of_conj_mem_rootSet hclass (htp _) (htp _) hu)).2 (p j) ha
    (right_mem_line ha) haT (htp j) y hy hyL hy1 h')
  have hyy' : Commute y (t * y * t⁻¹) := commute_of_mem_sup_rootGroup hd ha hda hyL hy'L
  have hyy'D : y * (t * y * t⁻¹) ∈ D := mem_of_mem_sup_rootGroup h hc hs hd ha hda hdaD haT
    (Subgroup.mul_mem _ hyL hy'L) fun h1 => hy'T (by
      rw [eq_inv_of_mul_eq_one_right h1, hD.inv_eq hy]
      exact mem_rootSet_self hy)
  have hμ'L : t * μ * t⁻¹ ∉ rootGroup D y ⊔ rootGroup D (t * y * t⁻¹) := by
    rw [sup_rootGroup_eq_of_mem h hc hs hd ha hda hdaD haT hyL hy'L (hD.ne_one hy)
      (hD.ne_one hy'D) hy'T]
    have := conj_not_mem_sup_conj hclass (k := t) hμL
    rwa [rootGroup_eq_of_mem (htp (j + 1)), rootGroup_eq_of_mem (htp j)] at this
  have hcol := conj_collinear hclass (k := t) hμy hμyD
  rw [orderOf_mul_comm_eq]
  exact orderOf_mul_eq_four_of_path h hc hs hconn hAll hy hy'D hμ'D hyy' hyy'D hy'T hcol.1.symm
    (by rw [← hcol.1.eq]; exact hcol.2) hμ'L

private theorem mul_conj_mem_rootSet_add_two (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {p : ℤ → G} {μ₁ μ₂ : G} (hr₁ : ∀ i, μ₁ * p (3 - i) * μ₁⁻¹ ∈ rootSet D (p i))
    (hr₂ : ∀ i, μ₂ * p (5 - i) * μ₂⁻¹ ∈ rootSet D (p i)) (i : ℤ) :
    μ₂ * μ₁ * p i * (μ₂ * μ₁)⁻¹ ∈ rootSet D (p (i + 2)) := by
  have h1 := hr₁ (3 - i)
  rw [sub_sub_cancel] at h1
  have h2 := hr₂ (i + 2)
  rw [show (5 : ℤ) - (i + 2) = 3 - i by ring] at h2
  have h3 := conj_mem_rootSet_conj hclass (μ := μ₂) h1
  rw [rootSet_eq_of_mem h2] at h3
  rwa [show μ₂ * μ₁ * p i * (μ₂ * μ₁)⁻¹ = μ₂ * (μ₁ * p i * μ₁⁻¹) * μ₂⁻¹ by group]

private theorem pow_conj_mem_rootSet_add (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {p : ℤ → G} {ρ : G} (hρ : ∀ i, ρ * p i * ρ⁻¹ ∈ rootSet D (p (i + 2)))
    (hD : ∀ i, p i ∈ D) (n : ℕ) (i j : ℤ) (hj : j = i + 2 * n) :
    ρ ^ n * p i * (ρ ^ n)⁻¹ ∈ rootSet D (p j) := by
  subst hj
  induction n generalizing i with
  | zero => simpa using mem_rootSet_self (hD i)
  | succ n ih =>
    have h1 := conj_mem_rootSet_conj hclass (μ := ρ ^ n) (hρ i)
    rw [rootSet_eq_of_mem (ih (i + 2))] at h1
    rw [pow_succ, show i + 2 * ((n + 1 : ℕ) : ℤ) = i + 2 + 2 * (n : ℤ) by push_cast; ring]
    rwa [show ρ ^ n * ρ * p i * (ρ ^ n * ρ)⁻¹ = ρ ^ n * (ρ * p i * ρ⁻¹) * (ρ ^ n)⁻¹ by group]

private theorem conj_pow_mul_self_eq {μ₁ μ₂ : G} (h1 : μ₁ * μ₁ = 1) (h2 : μ₂ * μ₂ = 1) {m : ℕ}
    (hm : orderOf (μ₂ * μ₁) = 2 * m + 1) :
    (μ₂ * μ₁) ^ (m + 1) * μ₁ * ((μ₂ * μ₁) ^ (m + 1))⁻¹ = μ₂ := by
  have hi1 : μ₁⁻¹ = μ₁ := inv_eq_of_mul_eq_one_right h1
  have hi2 : μ₂⁻¹ = μ₂ := inv_eq_of_mul_eq_one_right h2
  have e : μ₁ * (μ₂ * μ₁) * μ₁⁻¹ = (μ₂ * μ₁)⁻¹ := by
    calc μ₁ * (μ₂ * μ₁) * μ₁⁻¹ = μ₁ * μ₂ := by group
      _ = μ₁⁻¹ * μ₂⁻¹ := by rw [hi1, hi2]
      _ = (μ₂ * μ₁)⁻¹ := (mul_inv_rev μ₂ μ₁).symm
  have hc : ∀ n : ℕ, μ₁ * ((μ₂ * μ₁) ^ n)⁻¹ * μ₁⁻¹ = (μ₂ * μ₁) ^ n := by
    intro n
    have h' : (μ₁ * (μ₂ * μ₁) * μ₁⁻¹) ^ n = (μ₂ * μ₁)⁻¹ ^ n := by rw [e]
    rw [conj_pow, inv_pow] at h'
    calc μ₁ * ((μ₂ * μ₁) ^ n)⁻¹ * μ₁⁻¹ = (μ₁ * (μ₂ * μ₁) ^ n * μ₁⁻¹)⁻¹ := by group
      _ = (μ₂ * μ₁) ^ n := by rw [h', inv_inv]
  calc (μ₂ * μ₁) ^ (m + 1) * μ₁ * ((μ₂ * μ₁) ^ (m + 1))⁻¹
      = (μ₂ * μ₁) ^ (m + 1) * (μ₁ * ((μ₂ * μ₁) ^ (m + 1))⁻¹ * μ₁⁻¹) * μ₁ := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = (μ₂ * μ₁) ^ (2 * m + 1) * (μ₂ * μ₁) * μ₁ := by
        rw [hc, ← pow_add, ← pow_succ, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring]
    _ = μ₂ := by rw [← hm, pow_orderOf_eq_one, one_mul, mul_assoc, h1, mul_one]

private theorem opposite_conj_of_inv (hD : IsRootInvolutionSet D) {μ t : G} (hμ : μ ∈ D)
    (ht : InvTorus D t) (hμt : μ * t * μ⁻¹ = t⁻¹) :
    ¬ Commute μ (t * μ * t⁻¹) ∧ Odd (orderOf (μ * (t * μ * t⁻¹))) := by
  have e : μ * (t * μ * t⁻¹) = (t ^ 2)⁻¹ := by
    calc μ * (t * μ * t⁻¹) = μ * t * μ⁻¹ * t⁻¹ := by rw [hD.inv_eq hμ]; group
      _ = (t ^ 2)⁻¹ := by rw [hμt, sq, mul_inv_rev]
  have hodd : Odd (orderOf t) := ht.1.odd_of_ne_two ht.2.1
  have ho : orderOf (μ * (t * μ * t⁻¹)) = orderOf t := by
    rw [e, orderOf_inv, Nat.Coprime.orderOf_pow (Nat.coprime_two_right.2 hodd)]
  refine ⟨fun hcomm => ht.2.1 ?_, by rw [ho]; exact hodd⟩
  have hsq : t * μ * t⁻¹ * (t * μ * t⁻¹) = 1 := by
    rw [show t * μ * t⁻¹ * (t * μ * t⁻¹) = t * (μ * μ) * t⁻¹ by group, hD.mul_self_eq_one hμ,
      mul_one, mul_inv_cancel]
  have hdvd := orderOf_dvd_of_pow_eq_one
    ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hμ) hsq).1 hcomm)
  rw [ho] at hdvd
  have h2 := ht.1.two_le
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

namespace TorusPath

theorem false_of_odd (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) (h3 : ¬ ThreeLines D)
    (hbad : ThinAllBad D) (hF : FixUnique D) (hU : UniqueGate D) {g : G} (hg : InvTorus D g)
    {p : ℤ → G} (hP : TorusPath D g p) (h03 : ¬ Commute (p 0) (p 3))
    (hodd03 : Odd (orderOf (p 0 * p 3))) (h14 : ¬ Commute (p 1) (p 4))
    (_hodd14 : Odd (orderOf (p 1 * p 4))) {μ₁ μ₂ t₂ k₁ k₂ u₁ u₂ : G} (hμ₁ : μ₁ ∈ D)
    (hμ₂ : μ₂ ∈ D) (hr₁ : ∀ i, μ₁ * p (3 - i) * μ₁⁻¹ ∈ rootSet D (p i))
    (hr₂ : ∀ i, μ₂ * p (5 - i) * μ₂⁻¹ ∈ rootSet D (p i)) (ht₂ : InvTorus D t₂)
    (ht₂p : ∀ i, t₂ * p i * t₂⁻¹ ∈ rootSet D (p i)) (hμ₂t : μ₂ * t₂ * μ₂⁻¹ = t₂⁻¹)
    (hk₁ : k₁ ∈ rootGroup D (p 0)) (hu₁ : u₁ ∈ rootSet D (p 3)) (hμ₁eq : μ₁ = k₁ * u₁ * k₁⁻¹)
    (hk₂ : k₂ ∈ rootGroup D (p 1)) (hu₂ : u₂ ∈ rootSet D (p 4)) (hμ₂eq : μ₂ = k₂ * u₂ * k₂⁻¹)
    (_hnc : ¬ Commute μ₂ μ₁) (hodd : Odd (orderOf (μ₂ * μ₁))) : False := by
  have hclass := h.isClass
  have hD := h.root
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
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = k₁ * p 2 * k₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = k₂ * p 3 * k₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨hc₁D, hc₁L, hc₁T2, hc₁T1, ⟨hμ₁c₁, hμ₁c₁D, hc₁Tμ₁⟩, hμ₁L, ⟨h1c₁, h1c₁D⟩, -⟩ :=
    reflection_point h hc hs hconn hAll hp0 hp1 hp2 hp3 c01 m01 n01 c12 m12 n12 c23 m23 n23 t1 t2
      h03 (by simpa using hr₁ 0) hk₁ hu₁ hμ₁eq hc₁
  obtain ⟨hcD, hcL, hcT3, hcT2, ⟨hμ₂c, hμ₂cD, hcTμ₂⟩, hμ₂L, -, ⟨h3c, h3cD⟩⟩ :=
    reflection_point h hc hs hconn hAll hp1 hp2 hp3 hp4 c12 m12 n12 c23 m23 n23 c34 m34 n34 t2 t3
      h14 (by have := hr₂ 1; rwa [show (5 : ℤ) - 1 = 4 by norm_num] at this) hk₂ hu₂ hμ₂eq
      hcdef
  obtain ⟨m, hm⟩ := hodd
  have hρn := pow_conj_mem_rootSet_add hclass (mul_conj_mem_rootSet_add_two hclass hr₁ hr₂)
    hP.mem
  have h2r : IsPeriod D p (4 * m + 2) := by
    intro i
    have h1 : (μ₂ * μ₁) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
    have := hρn (2 * m + 1) i (i + (4 * m + 2)) (by push_cast; ring)
    rw [h1, one_mul, inv_one, mul_one] at this
    exact mem_rootSet_comm (hP.mem _) this
  obtain ⟨g', hg'⟩ : ∃ g' : G, g' = (μ₂ * μ₁) ^ (m + 1) := ⟨_, rfl⟩
  have hg'μ : g' * μ₁ * g'⁻¹ = μ₂ := by
    rw [hg']
    exact conj_pow_mul_self_eq (hD.mul_self_eq_one hμ₁) (hD.mul_self_eq_one hμ₂) hm
  have hshift : ∀ i j : ℤ, j = i + (2 * m + 2) → g' * p i * g'⁻¹ ∈ rootSet D (p j) := by
    intro i j hj
    rw [hg']
    exact hρn (m + 1) i j (by push_cast; omega)
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = 2 * m + 3 := ⟨_, rfl⟩
  have hs1 : g' * p 1 * g'⁻¹ ∈ rootSet D (p j) := hshift 1 j (by omega)
  have hs2 : g' * p 2 * g'⁻¹ ∈ rootSet D (p (j + 1)) := hshift 2 (j + 1) (by omega)
  obtain ⟨e, he⟩ : ∃ e, e = g' * c₁ * g'⁻¹ := ⟨_, rfl⟩
  have heD : e ∈ D := by rw [he]; exact conj_mem_of_isClass hclass g' hc₁D
  have heL : e ∈ rootGroup D (p (j + 1)) ⊔ rootGroup D (p j) := by
    have := conj_mem_sup_conj hclass (k := g') hc₁L
    rwa [rootGroup_eq_of_mem hs2, rootGroup_eq_of_mem hs1, ← he] at this
  have heT1 : e ∉ rootSet D (p (j + 1)) := by
    have := conj_not_mem_rootSet_conj hclass (k := g') hc₁T2
    rwa [rootSet_eq_of_mem hs2, ← he] at this
  have heT0 : e ∉ rootSet D (p j) := by
    have := conj_not_mem_rootSet_conj hclass (k := g') hc₁T1
    rwa [rootSet_eq_of_mem hs1, ← he] at this
  have hμ₂e : Commute μ₂ e ∧ μ₂ * e ∈ D := by
    have := conj_collinear hclass (k := g') hμ₁c₁ hμ₁c₁D
    rwa [hg'μ, ← he] at this
  have heTμ₂ : e ∉ rootSet D μ₂ := by
    have := conj_not_mem_rootSet_conj hclass (k := g') hc₁Tμ₁
    rwa [hg'μ, ← he] at this
  have hμ₂L' : μ₂ ∉ rootGroup D (p (j + 1)) ⊔ rootGroup D (p j) := by
    have := conj_not_mem_sup_conj hclass (k := g') hμ₁L
    rwa [hg'μ, rootGroup_eq_of_mem hs2, rootGroup_eq_of_mem hs1] at this
  have hje : Commute (p j) e ∧ p j * e ∈ D := by
    have h1 := conj_collinear hclass (k := g') h1c₁ h1c₁D
    rw [← he] at h1
    exact collinear_of_collinear_mem_rootSet h hc hs (hP.mem j) hs1 heD h1.1.symm
      (by rw [← h1.1.eq]; exact h1.2) heT0
  by_cases hcase : e ∈ rootGroup D μ₂ ⊔ rootGroup D c
  ·
    have h12 : (Commute c e ∧ c * e ∈ D) ∨ c = e := by
      by_cases hce : c = e
      · exact Or.inr hce
      · refine Or.inl ⟨commute_of_mem_sup_rootGroup hμ₂ hcD hμ₂c (right_mem_line hcD) hcase,
          mem_of_mem_sup_rootGroup h hc hs hμ₂ hcD hμ₂c hμ₂cD hcTμ₂
            (Subgroup.mul_mem _ (right_mem_line hcD) hcase) fun h1 => hce ?_⟩
        exact ((eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq hcD)).symm
    obtain ⟨n, hn, hn', hmem⟩ := exists_mem_rootSet_of_path3 h hc hs hconn hAll h3 hF hU hg hP
      (i := 3) hcD heD (hP.mem j) h3c h3cD h12 hje.1.symm (by rw [← hje.1.eq]; exact hje.2)
      (hP.fix j)
    have hper := isPeriod_of_mem_rootSet h hc hs h3 hF hg hP hmem
    rcases Int.even_or_odd n with ⟨a, ha⟩ | ⟨a, ha⟩
    ·
      have hk := (hper.add hper).sub hP.mem h2r
      rcases (show a = -1 ∨ 0 ≤ a by omega) with rfl | ha0
      · exact false_of_isPeriod_le_six h hc hs hconn hAll hbad h3 hP h03 hodd03
          (isPeriod_of_eq hk (k' := 2) (by omega)) (by norm_num) (by norm_num)
      · exact false_of_isPeriod_le_six h hc hs hconn hAll hbad h3 hP h03 hodd03
          (isPeriod_of_eq (hk.neg hP.mem) (k' := 4 * a + 2) (by omega)) (by omega) (by omega)
    ·
      exact false_of_isPeriod_odd h hc hs hconn hAll h3 hP hμ₁ hr₁ ⟨1, by norm_num⟩ hper
        ⟨m - a - 1, by omega⟩
  ·
    have h4c : orderOf (t₂ * μ₂ * t₂⁻¹ * c) = 4 :=
      orderOf_conj_mul_eq_four h hc hs hconn hAll hF hP ht₂ ht₂p 2 hcD hcL hcT3 hcT2 hμ₂ hμ₂c
        hμ₂cD hμ₂L
    have h4e : orderOf (t₂ * μ₂ * t₂⁻¹ * e) = 4 :=
      orderOf_conj_mul_eq_four h hc hs hconn hAll hF hP ht₂ ht₂p j heD heL heT1 heT0 hμ₂ hμ₂e.1
        hμ₂e.2 hμ₂L'
    obtain ⟨hnc', hodd'⟩ := opposite_conj_of_inv hD hμ₂ ht₂ hμ₂t
    refine hbad μ₂ hμ₂ _ (conj_mem_of_isClass hclass t₂ hμ₂) hnc' hodd'
      ⟨c, hcD, hμ₂c, hμ₂cD, h4c⟩ fun a ha hμa hμaD haT => ?_
    rcases mem_line_or_mem_line_of_not_threeLines h3 hμ₂ hcD heD ha ⟨hμ₂c, hμ₂cD, hcTμ₂⟩
        ⟨hμ₂e.1, hμ₂e.2, heTμ₂⟩ ⟨hμa, hμaD, haT⟩ hcase with h' | h'
    · refine ⟨c, hcD, ?_, h4c⟩
      rw [sup_rootGroup_eq_of_mem h hc hs hμ₂ hcD hμ₂c hμ₂cD hcTμ₂ (left_mem_line hμ₂) h'
        (hD.ne_one hμ₂) (hD.ne_one ha) haT]
      exact right_mem_line hcD
    · refine ⟨e, heD, ?_, h4e⟩
      rw [sup_rootGroup_eq_of_mem h hc hs hμ₂ heD hμ₂e.1 hμ₂e.2 heTμ₂ (left_mem_line hμ₂) h'
        (hD.ne_one hμ₂) (hD.ne_one ha) haT]
      exact right_mem_line heD

end TorusPath

end CFSG.Timmesfeld.Bridge
