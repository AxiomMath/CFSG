module

public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts
public import CFSG.Quasithin.EmptyFaithful.S143Aux

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.S1417

namespace T1531O4

variable {W : Type*} [CommGroup W]

structure IsLine (U₁ U₂ E : Subgroup W) : Prop where
  card_eq : Nat.card E = 4
  inf₁ : E ⊓ U₁ = ⊥
  inf₂ : E ⊓ U₂ = ⊥

theorem IsLine.symm {U₁ U₂ E : Subgroup W} (h : IsLine U₁ U₂ E) : IsLine U₂ U₁ E :=
  ⟨h.card_eq, h.inf₂, h.inf₁⟩

theorem le_normalizer_of_comm (A B : Subgroup W) : B ≤ Subgroup.normalizer (A : Set W) :=
  fun x _ => Subgroup.mem_normalizer_iff.mpr fun h => by
    rw [mul_comm x h, mul_inv_cancel_right]

theorem partner_unique {U₁ U₂ E : Subgroup W} (hE : IsLine U₁ U₂ E) {x y y' : W}
    (hy : y ∈ U₂) (hy' : y' ∈ U₂) (h : x * y ∈ E) (h' : x * y' ∈ E) : y = y' := by
  have h1 : y * y'⁻¹ ∈ E := by
    have := E.mul_mem h (E.inv_mem h')
    have e : x * y * (x * y')⁻¹ = y * y'⁻¹ := by
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    rw [e] at this
    exact this
  have h2 : y * y'⁻¹ ∈ E ⊓ U₂ := ⟨h1, U₂.mul_mem hy (U₂.inv_mem hy')⟩
  rw [hE.inf₂, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.mp h2

theorem partner_unique' {U₁ U₂ E : Subgroup W} (hE : IsLine U₁ U₂ E) {x x' y : W}
    (hx : x ∈ U₁) (hx' : x' ∈ U₁) (h : x * y ∈ E) (h' : x' * y ∈ E) : x = x' :=
  partner_unique hE.symm hx hx' (by rwa [mul_comm]) (by rwa [mul_comm])

theorem exists_partner_aux [Finite W] {E B : Subgroup W} (hW : Nat.card W = 16)
    (hE : Nat.card E = 4) (hB : Nat.card B = 4) (hEB : E ⊓ B = ⊥) (x : W) :
    ∃ y ∈ B, x * y ∈ E := by
  have h := S143.card_sup_mul_card_inf_of_le_normalizer (le_normalizer_of_comm E B)
  rw [hEB, Subgroup.card_bot, hE, hB] at h
  have htop : E ⊔ B = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hW]
    omega
  have hx' : x ∈ E ⊔ B := by rw [htop]; exact Subgroup.mem_top x
  obtain ⟨e, he, y, hy, hxy⟩ := Subgroup.mem_sup.mp hx'
  refine ⟨y⁻¹, B.inv_mem hy, ?_⟩
  rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
  exact he

section Graph

variable [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
theorem card_W (hS : OfourStruct X L₁ L₂ t) : Nat.card W = 16 := by
  have h := S143.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_comm (commV L₁) (commV L₂))
  rw [hS.inf, hS.sup, Subgroup.card_bot, hS.card_U₁, (card_of_actsAsNaturalL2 hS.nat₂).2] at h
  have e : Nat.card (⊤ : Subgroup W) = Nat.card W := Subgroup.card_top
  rw [e] at h
  omega

theorem exists_partner₂ (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) (x : W) : ∃ y ∈ commV L₂, x * y ∈ E :=
  exists_partner_aux (card_W hS) hE.card_eq (card_of_actsAsNaturalL2 hS.nat₂).2 hE.inf₂ x

theorem exists_partner₁ (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) (y : W) : ∃ x ∈ commV L₁, x * y ∈ E := by
  obtain ⟨x, hx, h⟩ := exists_partner_aux (card_W hS) hE.card_eq hS.card_U₁ hE.inf₁ y
  exact ⟨x, hx, by rwa [mul_comm]⟩

noncomputable def partnerHom (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) : ↥(commV L₁) →* ↥(commV L₂) where
  toFun x := ⟨(exists_partner₂ hS hE x.1).choose, (exists_partner₂ hS hE x.1).choose_spec.1⟩
  map_one' := by
    have h1 := (exists_partner₂ hS hE (1 : ↥(commV L₁)).1).choose_spec
    refine Subtype.ext ?_
    have : (exists_partner₂ hS hE (1 : ↥(commV L₁)).1).choose ∈ E ⊓ commV L₂ :=
      ⟨by simpa using h1.2, h1.1⟩
    rw [hE.inf₂, Subgroup.mem_bot] at this
    exact this
  map_mul' x x' := by
    have h1 := (exists_partner₂ hS hE x.1).choose_spec
    have h2 := (exists_partner₂ hS hE x'.1).choose_spec
    have h3 := (exists_partner₂ hS hE (x * x').1).choose_spec
    refine Subtype.ext ?_
    refine partner_unique hE h3.1 ((commV L₂).mul_mem h1.1 h2.1) h3.2 ?_
    show (x * x').1 * ((exists_partner₂ hS hE x.1).choose *
        (exists_partner₂ hS hE x'.1).choose) ∈ E
    have e : (x * x').1 * ((exists_partner₂ hS hE x.1).choose *
        (exists_partner₂ hS hE x'.1).choose) =
        (x.1 * (exists_partner₂ hS hE x.1).choose) * (x'.1 * (exists_partner₂ hS hE x'.1).choose) :=
      mul_mul_mul_comm _ _ _ _
    rw [e]
    exact E.mul_mem h1.2 h2.2

theorem partnerHom_mem (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) (x : ↥(commV L₁)) :
    x.1 * (partnerHom hS hE x).1 ∈ E :=
  (exists_partner₂ hS hE x.1).choose_spec.2

theorem partnerHom_eq (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) {x : ↥(commV L₁)} {y : ↥(commV L₂)}
    (h : x.1 * y.1 ∈ E) : partnerHom hS hE x = y :=
  Subtype.ext (partner_unique hE (partnerHom hS hE x).2 y.2 (partnerHom_mem hS hE x) h)

theorem partnerHom_injective (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) : Function.Injective (partnerHom hS hE) := by
  intro x x' h
  refine Subtype.ext (partner_unique' hE x.2 x'.2 (partnerHom_mem hS hE x) ?_)
  rw [h]
  exact partnerHom_mem hS hE x'

theorem partnerHom_surjective (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) : Function.Surjective (partnerHom hS hE) := by
  intro y
  obtain ⟨x, hx, h⟩ := exists_partner₁ hS hE y.1
  exact ⟨⟨x, hx⟩, partnerHom_eq hS hE h⟩

noncomputable def partnerEquiv (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) : ↥(commV L₁) ≃* ↥(commV L₂) :=
  MulEquiv.ofBijective (partnerHom hS hE) ⟨partnerHom_injective hS hE, partnerHom_surjective hS hE⟩

end Graph

section Stab

variable [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
theorem mul_apply_prod (hS : OfourStruct X L₁ L₂ t) {l₁ l₂ : MulAut W} (h₁ : l₁ ∈ L₁)
    (h₂ : l₂ ∈ L₂) {x y : W} (hx : x ∈ commV L₁) (hy : y ∈ commV L₂) :
    (l₁ * l₂) (x * y) = l₁ x * l₂ y := by
  rw [MulAut.mul_apply, map_mul, hS.L₂_fix₁ h₂ hx, map_mul,
    hS.L₁_fix₂ h₁ (commV_stable L₂ h₂ hy)]

omit [Finite W] in
theorem mem_stab_mul_iff (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W} {l₁ l₂ : MulAut W}
    (h₁ : l₁ ∈ L₁) (h₂ : l₂ ∈ L₂) :
    l₁ * l₂ ∈ stabSub E ↔
      ∀ x ∈ commV L₁, ∀ y ∈ commV L₂, (l₁ x * l₂ y ∈ E ↔ x * y ∈ E) := by
  constructor
  · intro h x hx y hy
    have := mem_stabSub.1 h (x * y)
    rwa [mul_apply_prod hS h₁ h₂ hx hy] at this
  · intro h
    refine mem_stabSub.2 fun w => ?_
    obtain ⟨x, hx, y, hy, rfl⟩ := hS.exists_decomp_W w
    rw [mul_apply_prod hS h₁ h₂ hx hy]
    exact h x hx y hy

theorem eq_one_of_mem_stab_L₁ (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) {l : MulAut W} (hl : l ∈ L₁) (hst : l ∈ stabSub E) :
    l = 1 := by
  refine eq_one_of_forall_apply_eq hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) hl ?_
  intro u hu
  obtain ⟨y, hy, hxy⟩ := exists_partner₂ hS hE u
  have h1 : l (u * y) ∈ E := (mem_stabSub.1 hst (u * y)).2 hxy
  rw [map_mul, hS.L₁_fix₂ hl hy] at h1
  exact partner_unique' hE (commV_stable L₁ hl hu) hu h1 hxy

theorem eq_one_of_mem_stab_L₂ (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) {l : MulAut W} (hl : l ∈ L₂) (hst : l ∈ stabSub E) :
    l = 1 := by
  refine eq_one_of_forall_apply_eq hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hl ?_
  intro u hu
  obtain ⟨x, hx, hxy⟩ := exists_partner₁ hS hE u
  have h1 : l (x * u) ∈ E := (mem_stabSub.1 hst (x * u)).2 hxy
  rw [map_mul, hS.L₂_fix₁ hl hx] at h1
  exact partner_unique hE (commV_stable L₂ hl hu) hu h1 hxy

omit [Finite W] in
theorem mul_self_mem_sup (hS : OfourStruct X L₁ L₂ t) {g : MulAut W} (hg : g ∈ X) :
    g * g ∈ L₁ ⊔ L₂ := by
  rcases hS.mem_or_mul_t_mem hg with h | h
  · exact (L₁ ⊔ L₂).mul_mem h h
  · have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hS.tsq
    have hN := Subgroup.mem_normalizer_iff.mp (hS.normalizer_sup hS.t_mem) (g * t)
    have h2 : t * (g * t) * t⁻¹ ∈ L₁ ⊔ L₂ := (hN).mp h
    have e : g * g = (g * t) * (t * (g * t) * t⁻¹) := by
      have h' : (g * t) * (t * (g * t) * t⁻¹) = g * (t * t) * g * (t * t⁻¹) := by group
      rw [h', hS.tsq]
      group
    rw [e]
    exact (L₁ ⊔ L₂).mul_mem h h2

omit [Finite W] in
theorem mem_sup_of_cube (hS : OfourStruct X L₁ L₂ t) {g : MulAut W} (hg : g ∈ X)
    (h3 : g ^ 3 = 1) : g ∈ L₁ ⊔ L₂ := by
  have hsq := mul_self_mem_sup hS hg
  have e : (g * g)⁻¹ = g := inv_eq_of_mul_eq_one_right ((pow_three' g).symm.trans h3)
  rw [← e]
  exact (L₁ ⊔ L₂).inv_mem hsq

theorem eq_one_of_cube_of_fix (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) {g : MulAut W} (hg : g ∈ X) (h3 : g ^ 3 = 1)
    (hfix : ∀ e ∈ E, g e = e) : g = 1 := by
  have hgs := mem_sup_of_cube hS hg h3
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hS.comm hgs
  have h1 : l₁ = 1 := by
    refine eq_one_of_forall_apply_eq hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) hl₁ ?_
    intro u hu
    obtain ⟨y, hy, hxy⟩ := exists_partner₂ hS hE u
    have h2 := hfix _ hxy
    rw [mul_apply_prod hS hl₁ hl₂ hu hy] at h2
    exact (eq_of_mul_eq_of_inf_eq_bot hS.inf (commV_stable L₁ hl₁ hu) hu
      (commV_stable L₂ hl₂ hy) hy h2).1
  have h2 : l₂ = 1 := by
    refine eq_one_of_forall_apply_eq hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hl₂ ?_
    intro u hu
    obtain ⟨x, hx, hxy⟩ := exists_partner₁ hS hE u
    have h2 := hfix _ hxy
    rw [mul_apply_prod hS hl₁ hl₂ hx hu] at h2
    exact (eq_of_mul_eq_of_inf_eq_bot hS.inf (commV_stable L₁ hl₁ hx) hx
      (commV_stable L₂ hl₂ hu) hu h2).2
  rw [h1, h2, mul_one]

theorem odd_orderOf_of_pow_three {α : Type*} [Monoid α] {a : α} (h : a ^ 3 = 1) :
    Odd (orderOf a) := by
  have hd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1 <;> rw [h1] <;> decide

theorem exists_L₂_of_pair (hS : OfourStruct X L₁ L₂ t) {E E' : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) (hE' : IsLine (commV L₁) (commV L₂) E') {a : MulAut W}
    (ha : a ∈ L₁) :
    ∃ l₂ ∈ L₂, ∀ x ∈ commV L₁, ∀ y ∈ commV L₂, (a x * l₂ y ∈ E' ↔ x * y ∈ E) := by
  have haS : a ∈ stabSub (commV L₁) := hS.sup_le_stab₁ (Subgroup.mem_sup_left ha)
  let φ := partnerEquiv hS hE
  let φ' := partnerEquiv hS hE'
  let aU : MulAut ↥(commV L₁) := resAut (commV L₁) ⟨a, haS⟩
  have haU : ∀ x : ↥(commV L₁), ((aU x : ↥(commV L₁)) : W) = a x := fun x => rfl
  let ψ : MulAut ↥(commV L₂) := (φ.symm.trans aU).trans φ'
  obtain ⟨l₂, hl₂, hl₂ψ⟩ := exists_apply_eq hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) ψ
  have hψφ : ∀ x : ↥(commV L₁), ψ (φ x) = φ' (aU x) := fun x => by simp [ψ]
  refine ⟨l₂, hl₂, fun x hx y hy => ?_⟩
  set xs : ↥(commV L₁) := ⟨x, hx⟩
  set ys : ↥(commV L₂) := ⟨y, hy⟩
  have hly : l₂ y = ((ψ ys : ↥(commV L₂)) : W) := hl₂ψ ys
  have hmem : (aU xs : W) * ((φ' (aU xs) : ↥(commV L₂)) : W) ∈ E' :=
    partnerHom_mem hS hE' (aU xs)
  constructor
  · intro h
    rw [hly, ← haU xs] at h
    have h2 : ((ψ ys : ↥(commV L₂)) : W) = ((φ' (aU xs) : ↥(commV L₂)) : W) :=
      partner_unique hE' (ψ ys).2 (φ' (aU xs)).2 h hmem
    have h3 : ψ ys = ψ (φ xs) := by
      rw [hψφ]
      exact Subtype.ext h2
    have h4 : ys = φ xs := ψ.injective h3
    have h5 : y = ((φ xs : ↥(commV L₂)) : W) := congrArg Subtype.val h4
    rw [h5]
    exact partnerHom_mem hS hE xs
  · intro h
    have h1 : y = ((φ xs : ↥(commV L₂)) : W) :=
      partner_unique hE hy (φ xs).2 h (partnerHom_mem hS hE xs)
    have h2 : ys = φ xs := Subtype.ext h1
    rw [hly, h2, hψφ, ← haU xs]
    exact hmem

theorem exists_L₂_of_L₁ (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) {a : MulAut W} (ha : a ∈ L₁) :
    ∃ l₂ ∈ L₂, a * l₂ ∈ stabSub E := by
  obtain ⟨l₂, hl₂, h⟩ := exists_L₂_of_pair hS hE hE ha
  exact ⟨l₂, hl₂, (mem_stab_mul_iff hS ha hl₂).2 h⟩

theorem exists_cube_stab (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) :
    ∃ p ∈ L₁ ⊔ L₂, p ^ 3 = 1 ∧ p ∈ stabSub E ∧ (∃ e ∈ E, p e ≠ e) ∧
      ∀ w : W, p w = w → w = 1 := by
  obtain ⟨a, ha, ha3, ha1⟩ := exists_orderThree hS.nat₁
  obtain ⟨l₂, hl₂, hpS⟩ := exists_L₂_of_L₁ hS hE ha
  have hc : Commute a l₂ := hS.comm a ha l₂ hl₂
  have hl₂3 : l₂ ^ 3 = 1 := by
    have h3 : (a * l₂) ^ 3 = l₂ ^ 3 := by
      rw [hc.mul_pow, ha3, one_mul]
    have hmemS : l₂ ^ 3 ∈ stabSub E := by
      rw [← h3]
      exact (stabSub E).pow_mem hpS 3
    exact eq_one_of_mem_stab_L₂ hS hE (L₂.pow_mem hl₂ 3) hmemS
  have hp3 : (a * l₂) ^ 3 = 1 := by
    rw [hc.mul_pow, ha3, hl₂3, one_mul]
  obtain ⟨x, hx, hax⟩ : ∃ x ∈ commV L₁, a x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact ha1 (eq_one_of_forall_apply_eq hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) ha hcon)
  have hl₂1 : l₂ ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hpS
    exact ha1 (eq_one_of_mem_stab_L₁ hS hE ha hpS)
  refine ⟨a * l₂, Subgroup.mul_mem_sup ha hl₂, hp3, hpS, ?_, ?_⟩
  · obtain ⟨y, hy, hxy⟩ := exists_partner₂ hS hE x
    refine ⟨x * y, hxy, fun h => hax ?_⟩
    rw [mul_apply_prod hS ha hl₂ hx hy] at h
    exact (eq_of_mul_eq_of_inf_eq_bot hS.inf (commV_stable L₁ ha hx) hx
      (commV_stable L₂ hl₂ hy) hy h).1
  · intro w hw
    obtain ⟨hwa, hwl⟩ := hS.fix_of_fix_mul ha hl₂ hw
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hS.exists_decomp_W w
    have hu₁1 : u₁ = 1 := by
      by_contra hne
      refine ha1 (eq_one_of_odd_of_fixed hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) ha
        (odd_orderOf_of_pow_three ha3) hu₁ hne ?_)
      have h2 : a (u₁ * u₂) = a u₁ * u₂ := by rw [map_mul, hS.L₁_fix₂ ha hu₂]
      rw [h2] at hwa
      exact mul_right_cancel hwa
    have hu₂1 : u₂ = 1 := by
      by_contra hne
      refine hl₂1 (eq_one_of_odd_of_fixed hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hl₂
        (odd_orderOf_of_pow_three hl₂3) hu₂ hne ?_)
      have h2 : l₂ (u₁ * u₂) = u₁ * l₂ u₂ := by rw [map_mul, hS.L₂_fix₁ hl₂ hu₁]
      rw [h2] at hwl
      exact mul_left_cancel hwl
    rw [hu₁1, hu₂1, mul_one]

omit [Finite W] in
theorem isLine_map_t (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) :
    IsLine (commV L₁) (commV L₂) (E.map (t : MulAut W).toMonoidHom) := by
  have htt : ∀ w : W, t (t w) = w := fun w => by
    have := congrArg (fun φ : MulAut W => φ w) hS.tsq
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (t : MulAut W).injective]
    exact hE.card_eq
  · rw [eq_bot_iff]
    rintro w ⟨⟨e, he, rfl⟩, hw⟩
    have h1 : e ∈ E ⊓ commV L₂ := ⟨he, by simpa [htt] using hS.swap₁ _ hw⟩
    rw [hE.inf₂, Subgroup.mem_bot] at h1
    simp [h1]
  · rw [eq_bot_iff]
    rintro w ⟨⟨e, he, rfl⟩, hw⟩
    have h1 : e ∈ E ⊓ commV L₁ := ⟨he, by simpa [htt] using hS.swap₂ _ hw⟩
    rw [hE.inf₁, Subgroup.mem_bot] at h1
    simp [h1]

theorem exists_swap_stab (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) :
    ∃ c ∈ X, c ∉ L₁ ⊔ L₂ ∧ c ∈ stabSub E := by
  have htt : ∀ w : W, t (t w) = w := fun w => by
    have := congrArg (fun φ : MulAut W => φ w) hS.tsq
    simpa using this
  obtain ⟨l₂, hl₂, h⟩ := exists_L₂_of_pair hS (isLine_map_t hS hE) hE (Subgroup.one_mem L₁)
  refine ⟨l₂ * t, X.mul_mem (hS.L₂_le hl₂) hS.t_mem, fun hc => hS.t_not_mem_sup ?_, ?_⟩
  · have := (L₁ ⊔ L₂).mul_mem (Subgroup.inv_mem _ (Subgroup.mem_sup_right hl₂)) hc
    simpa using this
  · refine mem_stabSub.2 fun w => ?_
    obtain ⟨x, hx, y, hy, hxy⟩ := hS.exists_decomp_W (t w)
    have e1 : (l₂ * t) w = x * l₂ y := by
      rw [MulAut.mul_apply, hxy, map_mul, hS.L₂_fix₁ hl₂ hx]
    have h1 := h x hx y hy
    simp only [MulAut.one_apply] at h1
    rw [e1]
    have e2 : x * y ∈ E.map (t : MulAut W).toMonoidHom ↔ w ∈ E := by
      rw [← hxy]
      constructor
      · rintro ⟨e, he, hew⟩
        have : e = w := by simpa [htt] using congrArg t hew
        rwa [← this]
      · intro hw
        exact ⟨w, hw, rfl⟩
    rw [h1, e2]

end Stab

end T1531O4

end CFSG.Quasithin
