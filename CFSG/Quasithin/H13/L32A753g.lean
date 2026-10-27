module

public import CFSG.Quasithin.H13.L32A753f
public import CFSG.Quasithin.H13.L32A753b

public section

namespace CFSG.Quasithin.H13.L32A.M753

open CFSG.Open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

omit [Finite V] in
theorem mul_inv_mem_of_not_mem
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hP : B42TypeU33 ↥K)
    {x y : MulAut V} (hx : x ∈ X) (hy : y ∈ X) (hxK : x ∉ K) (hyK : y ∉ K) : x * y⁻¹ ∈ K := by
  obtain ⟨ψ, hψ, hψK, hψD⟩ := exists_embedding_of_le hKX hXN hCK hP
  have hout : ∀ z : ↥X, (z : MulAut V) ∉ K → ψ z ∉ g2Derived (ZMod 2) := by
    intro z hz hzD
    obtain ⟨w, hwK, hw⟩ := hψD _ hzD
    exact hz (hψ hw ▸ hwK)
  have h2 := (Subgroup.mul_mem_iff_of_index_two B45U33.index_g2Derived (a := ψ ⟨x, hx⟩)
    (b := (ψ ⟨y, hy⟩)⁻¹)).2 (by
      constructor
      · intro h; exact absurd h (hout ⟨x, hx⟩ hxK)
      · intro h; exact absurd ((Subgroup.inv_mem_iff _).1 h) (hout ⟨y, hy⟩ hyK))
  rw [← map_inv, ← map_mul] at h2
  obtain ⟨w, hwK, hw⟩ := hψD _ h2
  have := hψ hw
  have e : (w : MulAut V) = x * y⁻¹ := congrArg Subtype.val this
  rw [← e]
  exact hwK

theorem relIndex_ne_zero_of_finite (H J : Subgroup V) : H.relIndex J ≠ 0 :=
  Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf J)

theorem relIndex_le_index {J C₀ D : Subgroup V} (hD : D ⊓ J ≤ C₀) : C₀.relIndex J ≤ D.index := by
  have h1 : C₀.relIndex J ≤ (D ⊓ J).relIndex J :=
    Subgroup.relIndex_le_of_le_left hD (relIndex_ne_zero_of_finite _ _)
  rw [Subgroup.inf_relIndex_right] at h1
  rw [← Subgroup.relIndex_top_right]
  exact h1.trans (Subgroup.relIndex_le_of_le_right le_top (relIndex_ne_zero_of_finite _ _))

omit [Finite V] in
theorem mem_fixV_zpowers_of {c : MulAut V} {v : V} (h : c v = v) :
    v ∈ fixV (Subgroup.zpowers c) :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply.2 h

theorem stab_of_offender
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hP : B42TypeU33 ↥K)
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hidx : (fixV A).index ≤ Nat.card A ^ 2) {J : Subgroup V} (hKJ : K ≤ stabSub J)
    (hC₀J : fixV K ≤ J) (hirr : IrrBetween K (fixV K) J)
    (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ fixV K) (h64 : (fixV K).relIndex J = 2 ^ 6) :
    A ≤ stabSub J := by
  by_contra hstab
  obtain ⟨a, haA, hamove⟩ : ∃ a ∈ A, a ∉ stabSub J := by
    by_contra h
    push Not at h
    exact hstab h
  have haX := hAX haA
  have hXC₀ := le_stabSub_fixV hXN
  have hKC₀ : K ≤ stabSub (fixV K) := hKX.trans hXC₀
  set J' : Subgroup V := J.map a.toMonoidHom with hJ'
  have hcK : ∀ k ∈ K, a⁻¹ * k * a ∈ K := fun k hk => by
    have := (Subgroup.mem_normalizer_iff.mp (hXN (X.inv_mem haX)) k).mp hk
    simpa using this
  have hKJ' : ∀ k ∈ K, ∀ v ∈ J', k v ∈ J' := by
    rintro k hk _ ⟨w, hw, rfl⟩
    refine ⟨(a⁻¹ * k * a) w, ((hKJ (hcK k hk)) w).2 hw, ?_⟩
    simp [MulAut.mul_apply]
  have hC₀J' : fixV K ≤ J' := by
    intro c hc
    have hc' : a⁻¹ c ∈ fixV K := ((hXC₀ (X.inv_mem haX)) c).2 hc
    exact ⟨a⁻¹ c, hC₀J hc', by simp⟩
  have hinf : J ⊓ J' = fixV K := by
    rcases hirr (J ⊓ J') (le_inf hC₀J hC₀J') inf_le_left (fun k hk v hv =>
        ⟨(hKJ hk v).2 hv.1, hKJ' k hk v hv.2⟩) with h | h
    · exact h
    · exfalso
      have hle : J ≤ J' := h ▸ inf_le_right
      have hcard : Nat.card J' = Nat.card J :=
        Subgroup.card_map_of_injective (f := a.toMonoidHom) a.injective
      have heq : J = J' := Subgroup.eq_of_le_of_card_ge hle hcard.le
      apply hamove
      intro v
      constructor
      · intro hv
        have : a v ∈ J' := by rw [← heq]; exact hv
        obtain ⟨w, hw, hwe⟩ := this
        rw [show w = v from a.injective hwe] at hw
        exact hw
      · intro hv
        have : a v ∈ J' := ⟨v, hv, rfl⟩
        rwa [← heq] at this
  have hfixa : fixV (Subgroup.zpowers a) ⊓ J ≤ fixV K := by
    rintro v ⟨hva, hvJ⟩
    have hav : a v = v := hva a (Subgroup.mem_zpowers a)
    rw [← hinf]
    exact ⟨hvJ, ⟨v, hvJ, hav⟩⟩
  have hidxa : 2 ^ 6 ≤ (fixV (Subgroup.zpowers a)).index := h64 ▸ relIndex_le_index hfixa
  have hAa : fixV A ≤ fixV (Subgroup.zpowers a) := fun v hv x hx =>
    hv x ((Subgroup.zpowers_le.2 haA) hx)
  have hidxle : (fixV (Subgroup.zpowers a)).index ≤ (fixV A).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hAa)
  obtain ⟨r, m, hr, -, hr3, -, -⟩ := short_generation_of_le hKX hXN hCK hP hAX hA1 hAe
  have hA8 : Nat.card A ≤ 8 := hr ▸ (Nat.pow_le_pow_right (by norm_num) hr3).trans (by norm_num)
  have hsq : Nat.card A ^ 2 ≤ 2 ^ 6 :=
    (Nat.pow_le_pow_left hA8 2).trans (by norm_num)
  have heqidx : (fixV A).index = (fixV (Subgroup.zpowers a)).index :=
    le_antisymm (hidx.trans (hsq.trans hidxa)) hidxle
  have hfixeq : fixV (Subgroup.zpowers a) ≤ fixV A := by
    have h1 := (fixV A).card_mul_index
    have h2 := (fixV (Subgroup.zpowers a)).card_mul_index
    have hpos : 0 < (fixV A).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [← heqidx] at h2
    have hc := Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    exact (Subgroup.eq_of_le_of_card_ge hAa hc.symm.le).symm.le
  have hA3 : 2 < Nat.card A := by
    by_contra hle
    push Not at hle
    have h4 : Nat.card A ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hle 2
    have := hidxa.trans (hidxle.trans (hidx.trans h4))
    norm_num at this
  obtain ⟨b, hbA, hbK, hb1⟩ : ∃ b ∈ A, b ∈ K ∧ b ≠ 1 := by
    by_contra hno
    push Not at hno
    obtain ⟨x₀, hx₀A, hx₀1⟩ := (Subgroup.bot_or_exists_ne_one A).resolve_left hA1
    have hx₀K : x₀ ∉ K := fun h => hx₀1 (hno x₀ hx₀A h)
    have hle : A ≤ Subgroup.zpowers x₀ := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]; exact Subgroup.one_mem _
      · have hyK : y ∉ K := fun h => hy1 (hno y hy h)
        have h1 := mul_inv_mem_of_not_mem hKX hXN hCK hP (hAX hx₀A) (hAX hy) hx₀K hyK
        have h2 : x₀ * y⁻¹ = 1 := hno _ (A.mul_mem hx₀A (A.inv_mem hy)) h1
        rw [mul_inv_eq_one] at h2
        rw [← h2]
        exact Subgroup.mem_zpowers x₀
    have hc := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at hc
    have ho : orderOf x₀ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (hAe.2 x₀ hx₀A)
    omega
  have ha2 : a * a = 1 := by
    have := hAe.2 a haA
    rwa [pow_two] at this
  have h1 : secHom hKJ hKC₀ ⟨b, hbK⟩ = 1 := by
    rw [secHom_eq_one_iff]
    intro j hj
    have hja : a (j * a j) = j * a j := by
      rw [map_mul, ← MulAut.mul_apply, ha2, MulAut.one_apply, mul_comm]
    have hbj : b (j * a j) = j * a j := hfixeq (mem_fixV_zpowers_of hja) b hbA
    rw [map_mul] at hbj
    rw [← hinf]
    refine ⟨J.mul_mem ((hKJ hbK j).2 hj) (J.inv_mem hj), ?_⟩
    have e : b j * j⁻¹ = a j * (b (a j))⁻¹ := by
      calc b j * j⁻¹ = b j * b (a j) * (b (a j))⁻¹ * j⁻¹ := by rw [mul_inv_cancel_right]
        _ = j * a j * (b (a j))⁻¹ * j⁻¹ := by rw [hbj]
        _ = a j * (b (a j))⁻¹ := by
          rw [mul_comm j (a j), mul_right_comm (a j) j, mul_inv_cancel_right]
    rw [e]
    have haj : a j ∈ J' := ⟨j, hj, rfl⟩
    exact J'.mul_mem haj (J'.inv_mem (hKJ' b hbK _ haj))
  exact hb1 (congrArg Subtype.val
    (secHom_injective hKJ hKC₀ (isSimpleGroup_of_b42 hP) hnt (h1.trans (map_one _).symm)))

omit [Finite V] in
theorem le_stabSub_of_inv {K : Subgroup (MulAut V)} {J : Subgroup V}
    (h : ∀ k ∈ K, ∀ v ∈ J, k v ∈ J) : K ≤ stabSub J := by
  intro k hk v
  refine ⟨fun hv => ?_, h k hk v⟩
  have := h k⁻¹ (K.inv_mem hk) _ hv
  simpa using this

omit [Finite V] in
theorem card_sec_eq (J C : Subgroup V) : Nat.card (Sec J C) = C.relIndex J := rfl

theorem structure_fixV
    (hV : ∀ v : V, v ^ 2 = 1) {K : Subgroup (MulAut V)} (hP : B42TypeU33 ↥K) (hcomm : commV K = ⊤)
    (h12 : (fixV K).index ≤ 2 ^ 12) :
    (IrrBetween K (fixV K) ⊤ ∧ Nat.card (Sec ⊤ (fixV K)) = 2 ^ 6 ∧
        G2NaturalDerived (autSec K ⊤ (fixV K)) ⊤ ⊥ 1) ∨
      ∃ J : Subgroup V, K ≤ stabSub J ∧ fixV K < J ∧ J < ⊤ ∧ IrrBetween K (fixV K) J ∧
        IrrBetween K J ⊤ ∧ (∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ fixV K) ∧
        (∃ k ∈ K, ∃ v ∈ (⊤ : Subgroup V), k v * v⁻¹ ∉ J) ∧
        Nat.card (Sec J (fixV K)) = 2 ^ 6 ∧ G2NaturalDerived (autSec K J (fixV K)) ⊤ ⊥ 1 ∧
        Nat.card (Sec ⊤ J) = 2 ^ 6 ∧ G2NaturalDerived (autSec K ⊤ J) ⊤ ⊥ 1 := by
  set C₀ := fixV K with hC₀
  have hKC₀ : K ≤ stabSub C₀ := le_stabSub_fixV (X := K) (Subgroup.le_normalizer)
  have hC₀top : C₀ < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    have hK1 : K = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      rw [Subgroup.mem_bot]
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ C₀ := h ▸ Subgroup.mem_top v
      exact hv k hk
    have h6048 := B42U33.card_of_b42TypeU33 hP
    rw [hK1, Subgroup.card_bot] at h6048
    norm_num at h6048
  obtain ⟨J₁, ⟨hJ₁inv, hC₀J₁⟩, hJ₁min⟩ := exists_minimal_of_wellFoundedLT
    (fun J : Subgroup V => (∀ k ∈ K, ∀ v ∈ J, k v ∈ J) ∧ C₀ < J)
    ⟨⊤, fun _ _ _ _ => Subgroup.mem_top _, hC₀top⟩
  have hirr₁ : IrrBetween K C₀ J₁ := by
    intro J' hCJ' hJ'J hJ'inv
    by_cases h : J' = C₀
    · exact Or.inl h
    · exact Or.inr (le_antisymm hJ'J (hJ₁min ⟨hJ'inv, lt_of_le_of_ne hCJ' (Ne.symm h)⟩ hJ'J))
  have hnt₁ : ∃ k ∈ K, ∃ j ∈ J₁, k j * j⁻¹ ∉ C₀ := by
    by_contra h
    push Not at h
    exact absurd (trivial_of_le hP h) (not_le_of_gt hC₀J₁)
  have hKJ₁ := le_stabSub_of_inv hJ₁inv
  have hc₁ : Nat.card (Sec J₁ C₀) ≤ 2 ^ 12 := by
    rw [card_sec_eq]
    rw [← Subgroup.relIndex_top_right C₀] at h12
    exact (Subgroup.relIndex_le_of_le_right le_top (relIndex_ne_zero_of_finite _ _)).trans h12
  obtain ⟨h64₁, hnat₁⟩ := natural_of_sec hV hKJ₁ hKC₀ hC₀J₁.le hP hnt₁ hirr₁ hc₁
  by_cases hJ₁top : J₁ = ⊤
  · subst hJ₁top
    exact Or.inl ⟨hirr₁, h64₁, hnat₁⟩
  obtain ⟨J₂, ⟨hJ₂inv, hJ₁J₂, hJ₂top⟩, hJ₂max⟩ := exists_maximal_of_wellFoundedGT
    (fun J : Subgroup V => (∀ k ∈ K, ∀ v ∈ J, k v ∈ J) ∧ J₁ ≤ J ∧ J < ⊤)
    ⟨J₁, hJ₁inv, le_rfl, lt_top_iff_ne_top.2 hJ₁top⟩
  have hirr₂ : IrrBetween K J₂ ⊤ := by
    intro J' hJ₂J' _ hJ'inv
    by_cases h : J' = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (hJ₂max ⟨hJ'inv, hJ₁J₂.trans hJ₂J', lt_top_iff_ne_top.2 h⟩
        hJ₂J') hJ₂J')
  have hnt₂ : ∃ k ∈ K, ∃ v ∈ (⊤ : Subgroup V), k v * v⁻¹ ∉ J₂ := by
    by_contra h
    push Not at h
    have hle : commV K ≤ J₂ :=
      (Subgroup.closure_le _).2 (by rintro _ ⟨k, hk, v, rfl⟩; exact h k hk v (Subgroup.mem_top v))
    rw [hcomm] at hle
    exact absurd (top_le_iff.1 hle) (ne_of_lt hJ₂top)
  have hKJ₂ := le_stabSub_of_inv hJ₂inv
  have hC₀J₂ : C₀ ≤ J₂ := hC₀J₁.le.trans hJ₁J₂
  have hidx : C₀.index = J₂.index * (C₀.relIndex J₁ * J₁.relIndex J₂) := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hC₀J₁.le hJ₁J₂, mul_comm,
      Subgroup.relIndex_mul_index hC₀J₂]
  have hc₂ : Nat.card (Sec ⊤ J₂) ≤ 2 ^ 12 := by
    rw [card_sec_eq, Subgroup.relIndex_top_right]
    refine le_trans ?_ h12
    rw [hidx]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex_mul_relIndex _ _ _ hC₀J₁.le hJ₁J₂]
      exact relIndex_ne_zero_of_finite _ _))
  obtain ⟨h64₂, hnat₂⟩ := natural_of_sec hV (le_stabSub_of_inv fun _ _ _ _ => Subgroup.mem_top _)
    hKJ₂ le_top hP hnt₂ hirr₂ hc₂
  have h1 : J₁.relIndex J₂ = 1 := by
    have e1 := h64₁
    have e2 := h64₂
    rw [card_sec_eq] at e1 e2
    rw [Subgroup.relIndex_top_right] at e2
    rw [e2, e1] at hidx
    have hpos : 0 < J₁.relIndex J₂ := Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite _ _)
    have : 2 ^ 6 * (2 ^ 6 * J₁.relIndex J₂) ≤ 2 ^ 12 := hidx ▸ h12
    norm_num at this
    omega
  have hJ : J₂ = J₁ := le_antisymm (Subgroup.relIndex_eq_one.1 h1) hJ₁J₂
  rw [hJ] at hirr₂ hnt₂ h64₂ hnat₂
  exact Or.inr ⟨J₁, hKJ₁, hC₀J₁, lt_top_iff_ne_top.2 hJ₁top, hirr₁, hirr₂, hnt₁, hnt₂, h64₁, hnat₁,
    h64₂, hnat₂⟩

theorem index_mul_index_le {A : Subgroup (MulAut V)} {J C : Subgroup V} (hCJ : C ≤ J)
    (hAJ : A ≤ stabSub J) :
    (fixV (autSec A J C)).index * (fixV (autSec A ⊤ J)).index ≤ (fixV A).index := by
  have h1 := card_inf_fixV_le_autSec (A := A) (le_top : J ≤ ⊤) (fun a _ v => by simp)
  have h2 := card_inf_fixV_le_autSec (A := A) hCJ hAJ
  have h3 := card_sec_mul (V := V) (le_top : J ≤ ⊤)
  have h4 := card_sec_mul (V := V) hCJ
  have h5 := (fixV (autSec A J C)).card_mul_index
  have h6 := (fixV (autSec A ⊤ J)).card_mul_index
  have h7 := (fixV A).card_mul_index
  have hc : Nat.card ↥(C ⊓ fixV A) ≤ Nat.card C := Subgroup.card_le_of_le inf_le_left
  have htop : Nat.card ↥((⊤ : Subgroup V) ⊓ fixV A) = Nat.card (fixV A) := by rw [top_inf_eq]
  rw [htop] at h1
  rw [Subgroup.card_top] at h3
  set i₁ := (fixV (autSec A J C)).index
  set i₂ := (fixV (autSec A ⊤ J)).index
  set f₁ := Nat.card (fixV (autSec A J C))
  set f₂ := Nat.card (fixV (autSec A ⊤ J))
  set f := Nat.card (fixV A)
  have hfpos : 0 < f := Nat.card_pos
  have hV : Nat.card V = i₂ * i₁ * (f₂ * (f₁ * Nat.card C)) := by
    rw [← h3, ← h4, ← h5, ← h6]
    ring
  have hf : f ≤ f₂ * (f₁ * Nat.card C) :=
    h1.trans (Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ hc)))
  have key : i₁ * i₂ * f ≤ (fixV A).index * f := by
    calc i₁ * i₂ * f ≤ i₁ * i₂ * (f₂ * (f₁ * Nat.card C)) := Nat.mul_le_mul_left _ hf
      _ = Nat.card V := by rw [hV]; ring
      _ = (fixV A).index * f := by rw [← h7, mul_comm]
  exact Nat.le_of_mul_le_mul_right key hfpos

end CFSG.Quasithin.H13.L32A.M753
