module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
public import CFSG.Quasithin.Background.G93ApplyRestrict

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

theorem conj_of_odd {G : Type*} [Group G] {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (s * t))) : ∃ n : ℕ, (s * t) ^ n * s * ((s * t) ^ n)⁻¹ = t := by
  obtain ⟨n, hn⟩ := hodd
  refine ⟨n, ?_⟩
  set u := s * t with hu
  have hm : u ^ (2 * n + 1) = 1 := by rw [← hn]; exact pow_orderOf_eq_one u
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hsu : s * u * s⁻¹ = u⁻¹ := by
    rw [hu, mul_inv_rev, ht', hs']
    calc s * (s * t) * s = (s * s) * t * s := by group
      _ = t * s := by rw [hs, one_mul]
  have hsu' : s * u⁻¹ * s⁻¹ = u := by
    have := congrArg (fun x => x⁻¹) hsu
    simpa [mul_inv_rev, mul_assoc] using this
  have hpow : s * (u⁻¹) ^ n * s⁻¹ = u ^ n := by
    have := map_pow (MulAut.conj s) (u⁻¹) n
    simp only [MulAut.conj_apply] at this
    rw [this, hsu']
  have h2n : u ^ (2 * n) = u⁻¹ := by
    have : u ^ (2 * n) * u = 1 := by rw [← pow_succ]; exact hm
    exact eq_inv_of_mul_eq_one_left this
  have key : s * (u ^ n)⁻¹ * s⁻¹ = u ^ n := by rw [← inv_pow]; exact hpow
  calc u ^ n * s * (u ^ n)⁻¹ = u ^ n * (s * (u ^ n)⁻¹ * s⁻¹) * s := by group
    _ = u ^ n * u ^ n * s := by rw [key]
    _ = u ^ (2 * n) * s := by rw [← pow_add]; congr 2; ring
    _ = t := by rw [h2n, hu, mul_inv_rev, inv_mul_cancel_right, ht']

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem odd_orderOf_of_commutes [Finite V] {H : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}
    (hJ : IsIrr H J) {u : ↥J ≃ₗ[ZMod 2] ↥J}
    (hu : ∀ (h : GLV V) (hh : h ∈ H),
      u * restrictEquiv h J (hJ.1.conjSub_eq hh) = restrictEquiv h J (hJ.1.conjSub_eq hh) * u) :
    Odd (orderOf u) := by
  by_contra hev
  have hev' : 2 ∣ orderOf u := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
  haveI : Finite ↥J := inferInstance
  haveI : Finite (↥J ≃ₗ[ZMod 2] ↥J) := Finite.of_injective _ DFunLike.coe_injective
  have hpos : 0 < orderOf u := orderOf_pos u
  set w : ↥J ≃ₗ[ZMod 2] ↥J := u ^ (orderOf u / 2) with hw
  have hwo : orderOf w = 2 := orderOf_pow_orderOf_div hpos.ne' hev'
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hwo
    omega
  have hww : w * w = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hwo])
  have hwc : ∀ (h : GLV V) (hh : h ∈ H),
      w * restrictEquiv h J (hJ.1.conjSub_eq hh) = restrictEquiv h J (hJ.1.conjSub_eq hh) * w :=
    fun h hh => (Commute.pow_left (hu h hh) _ : Commute (u ^ (orderOf u / 2)) _)
  set N : ↥J →ₗ[ZMod 2] ↥J := (w : ↥J →ₗ[ZMod 2] ↥J) - LinearMap.id with hN
  have hNN : ∀ x, N (N x) = 0 := by
    intro x
    have hx : w (w x) = x := by
      have := congrArg (fun g : ↥J ≃ₗ[ZMod 2] ↥J => g x) hww
      exact this
    have h1 : N (N x) = (x + x) - (w x + w x) := by
      simp only [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub, hx]
      abel
    rw [h1, CFSG.ComponentClassification.OutcomeLocal.zmod2_add_self x,
      CFSG.ComponentClassification.OutcomeLocal.zmod2_add_self (w x), sub_self]
  set Km : Submodule (ZMod 2) V := (LinearMap.ker N).map J.subtype with hKm
  have hKminv : Invariant H Km := by
    rintro h hh _ ⟨x, hx, rfl⟩
    refine ⟨restrictEquiv h J (hJ.1.conjSub_eq hh) x, ?_, rfl⟩
    have hNx : N x = 0 := hx
    have h1 : w (restrictEquiv h J (hJ.1.conjSub_eq hh) x) =
        restrictEquiv h J (hJ.1.conjSub_eq hh) (w x) := by
      have := congrArg (fun g : ↥J ≃ₗ[ZMod 2] ↥J => g x) (hwc h hh)
      exact this
    have hwx : w x = x := by
      have : w x - x = 0 := hNx
      exact sub_eq_zero.1 this
    show N (restrictEquiv h J (hJ.1.conjSub_eq hh) x) = 0
    simp only [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    rw [h1, hwx, sub_self]
  rcases hJ.eq_bot_or_eq hKminv (Submodule.map_subtype_le J _) with h0 | h1
  ·
    apply hJ.ne_bot
    rw [eq_bot_iff]
    intro y hy
    have hker : ∀ x : ↥J, N x = 0 → x = 0 := by
      intro x hx
      have : (x : V) ∈ Km := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact Subtype.ext this
    have hy' : (⟨y, hy⟩ : ↥J) = 0 := hker _ (hker _ (hNN _))
    have := congrArg Subtype.val hy'
    simpa using this
  ·
    apply hw1
    refine LinearEquiv.ext fun x => ?_
    have hx : (x : V) ∈ Km := by rw [h1]; exact x.2
    obtain ⟨x', hx', hxx'⟩ := hx
    have : x' = x := Subtype.ext hxx'
    subst this
    have hNx : N x' = 0 := hx'
    have : w x' - x' = 0 := hNx
    exact sub_eq_zero.1 this

theorem comm_of_conj_involutions {G : Type*} [Group G] {s t b : G} (hs : s * s = 1)
    (ht : t * t = 1) (hb : s * b * s = t * b * t) : s * t * b = b * (s * t) := by
  calc s * t * b = s * (t * b * t) * t := by
        rw [show s * (t * b * t) * t = s * t * b * (t * t) by group, ht, mul_one]
    _ = s * (s * b * s) * t := by rw [hb]
    _ = (s * s) * b * (s * t) := by group
    _ = b * (s * t) := by rw [hs, one_mul]

theorem hiso_sup_zpowers [Finite V] {H : Subgroup (GLV V)} {a : GLV V}
    {J₁ J₂ : Submodule (ZMod 2) V} (hJ₁ : IsIrr H J₁) (hJ₂ : IsIrr H J₂)
    (haN : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (ha2 : a * a = 1) (haJ₁ : conjSub a J₁ = J₁)
    (haJ₂ : conjSub a J₂ = J₂) (hiso : HIso H J₁ J₂) : HIso (H ⊔ Subgroup.zpowers a) J₁ J₂ := by
  obtain ⟨φ₀, hφ₀⟩ := hiso
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  set t₁ := restrictEquiv a J₁ haJ₁ with ht₁d
  set t₂ := restrictEquiv a J₂ haJ₂ with ht₂d
  have ht₁ : t₁ * t₁ = 1 := by
    ext i
    show a (a (i : V)) = i
    exact congrArg (fun g : GLV V => g (i : V)) ha2
  have ht₂ : t₂ * t₂ = 1 := by
    ext i
    show a (a (i : V)) = i
    exact congrArg (fun g : GLV V => g (i : V)) ha2
  have hint : ∀ (h : GLV V) (hh : h ∈ H) (i : ↥J₁),
      φ₀ (restrictEquiv h J₁ (hJ₁.1.conjSub_eq hh) i) =
        restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) (φ₀ i) := fun h hh i =>
    Subtype.ext (hφ₀ h hh i (restrictEquiv h J₁ (hJ₁.1.conjSub_eq hh) i) rfl).symm
  set s : ↥J₂ ≃ₗ[ZMod 2] ↥J₂ := φ₀.symm.trans (t₁.trans φ₀) with hsd
  have hsx : ∀ x, s x = φ₀ (t₁ (φ₀.symm x)) := fun x => rfl
  have hss : s * s = 1 := by
    ext x
    show ((s (s x) : ↥J₂) : V) = x
    rw [hsx, hsx]
    simp only [LinearEquiv.symm_apply_apply]
    have : t₁ (t₁ (φ₀.symm x)) = φ₀.symm x := by
      have := congrArg (fun g : ↥J₁ ≃ₗ[ZMod 2] ↥J₁ => g (φ₀.symm x)) ht₁
      exact this
    rw [this, LinearEquiv.apply_symm_apply]
  have hR : ∀ (h : GLV V) (hh : h ∈ H),
      s * restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) * s =
        t₂ * restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) * t₂ := by
    intro h hh
    have hah : a * h * a ∈ H := by
      have := haN h hh
      rwa [hai] at this
    have hahJ₁ : conjSub (a * h * a) J₁ = J₁ := hJ₁.1.conjSub_eq hah
    have hahJ₂ : conjSub (a * h * a) J₂ = J₂ := hJ₂.1.conjSub_eq hah
    have e1 : restrictEquiv (a * h * a) J₁ hahJ₁ =
        t₁ * restrictEquiv h J₁ (hJ₁.1.conjSub_eq hh) * t₁ := by
      ext i
      rfl
    have e2 : restrictEquiv (a * h * a) J₂ hahJ₂ =
        t₂ * restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) * t₂ := by
      ext i
      rfl
    ext x
    have h1 := hint (a * h * a) hah (φ₀.symm x)
    rw [e1, e2, LinearEquiv.apply_symm_apply] at h1
    have hint' : ∀ y : ↥J₁, φ₀ (restrictEquiv h J₁ (hJ₁.1.conjSub_eq hh) y) =
        restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) (φ₀ y) := hint h hh
    show ((s (restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) (s x)) : ↥J₂) : V) = _
    rw [hsx, hsx, ← hint', LinearEquiv.symm_apply_apply]
    exact congrArg Subtype.val h1
  set u : ↥J₂ ≃ₗ[ZMod 2] ↥J₂ := s * t₂ with hud
  have hu : ∀ (h : GLV V) (hh : h ∈ H), u * restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) =
      restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) * u := fun h hh =>
    comm_of_conj_involutions hss ht₂ (hR h hh)
  have hodd : Odd (orderOf u) := odd_orderOf_of_commutes hJ₂ hu
  obtain ⟨n, hn⟩ := conj_of_odd hss ht₂ hodd
  set d : ↥J₂ ≃ₗ[ZMod 2] ↥J₂ := u ^ n with hd
  have hdc : ∀ (h : GLV V) (hh : h ∈ H), d * restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) =
      restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) * d := fun h hh => (Commute.pow_left (hu h hh) n)
  have hdt : d * s = t₂ * d := by
    have h1 : d * s * d⁻¹ = t₂ := hn
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  set φ' : ↥J₁ ≃ₗ[ZMod 2] ↥J₂ := φ₀.trans d with hφ'
  have hφ'a : ∀ x, φ' (t₁ x) = t₂ (φ' x) := by
    intro x
    show d (φ₀ (t₁ x)) = t₂ (d (φ₀ x))
    have h1 : φ₀ (t₁ x) = s (φ₀ x) := by rw [hsx, LinearEquiv.symm_apply_apply]
    rw [h1]
    have := congrArg (fun g : ↥J₂ ≃ₗ[ZMod 2] ↥J₂ => g (φ₀ x)) hdt
    exact this
  have hφ'H : ∀ (h : GLV V) (hh : h ∈ H) (x : ↥J₁),
      φ' (restrictEquiv h J₁ (hJ₁.1.conjSub_eq hh) x) =
        restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) (φ' x) := by
    intro h hh x
    show d (φ₀ (restrictEquiv h J₁ (hJ₁.1.conjSub_eq hh) x)) =
      restrictEquiv h J₂ (hJ₂.1.conjSub_eq hh) (d (φ₀ x))
    rw [hint h hh x]
    have := congrArg (fun g : ↥J₂ ≃ₗ[ZMod 2] ↥J₂ => g (φ₀ x)) (hdc h hh)
    exact this
  have key : ∀ k ∈ Subgroup.closure ((H : Set (GLV V)) ∪ {a}),
      ∃ (hk1 : conjSub k J₁ = J₁) (hk2 : conjSub k J₂ = J₂), ∀ x : ↥J₁,
        φ' (restrictEquiv k J₁ hk1 x) = restrictEquiv k J₂ hk2 (φ' x) := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem k hk =>
      rcases hk with hkH | hka
      · exact ⟨hJ₁.1.conjSub_eq hkH, hJ₂.1.conjSub_eq hkH, hφ'H k hkH⟩
      · rw [Set.mem_singleton_iff] at hka
        subst hka
        exact ⟨haJ₁, haJ₂, hφ'a⟩
    | one => exact ⟨conjSub_one J₁, conjSub_one J₂, fun x => rfl⟩
    | mul a' b' ha hb iha ihb =>
      obtain ⟨ha1, ha2, hA⟩ := iha
      obtain ⟨hb1, hb2, hB⟩ := ihb
      refine ⟨by rw [conjSub_mul, hb1, ha1], by rw [conjSub_mul, hb2, ha2], fun x => ?_⟩
      show φ' (restrictEquiv a' J₁ ha1 (restrictEquiv b' J₁ hb1 x)) =
        restrictEquiv a' J₂ ha2 (restrictEquiv b' J₂ hb2 (φ' x))
      rw [hA, hB]
    | inv a' ha iha =>
      obtain ⟨ha1, ha2, hA⟩ := iha
      refine ⟨conjSub_inv_eq_of_conjSub_eq ha1, conjSub_inv_eq_of_conjSub_eq ha2, fun x => ?_⟩
      have hinv : ∀ {I : Submodule (ZMod 2) V} (h : conjSub a' I = I) (z : ↥I),
          restrictEquiv a'⁻¹ I (conjSub_inv_eq_of_conjSub_eq h) z = (restrictEquiv a' I h).symm z := by
        intro I h z
        apply Subtype.ext
        show a'⁻¹ (z : V) = (((restrictEquiv a' I h).symm z : ↥I) : V)
        have h1 : a' (((restrictEquiv a' I h).symm z : ↥I) : V) = (z : V) := by
          have := (restrictEquiv a' I h).apply_symm_apply z
          exact congrArg Subtype.val this
        conv_lhs => rw [← h1]
        simp
      rw [hinv ha1, hinv ha2]
      have h1 := hA ((restrictEquiv a' J₁ ha1).symm x)
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [h1]
      simp
  have hsub : H ⊔ Subgroup.zpowers a ≤ Subgroup.closure ((H : Set (GLV V)) ∪ {a}) :=
    sup_le (fun x hx => Subgroup.subset_closure (Or.inl hx))
      ((Subgroup.zpowers_le).2 (Subgroup.subset_closure (Or.inr rfl)))
  refine ⟨φ', fun k hk i j hij => ?_⟩
  obtain ⟨hk1, hk2, hP⟩ := key k (hsub hk)
  have e : restrictEquiv k J₁ hk1 i = j := Subtype.ext hij
  show ((restrictEquiv k J₂ hk2 (φ' i) : ↥J₂) : V) = ((φ' j : ↥J₂) : V)
  rw [← hP i, e]

end G11

end CFSG.Quasithin
