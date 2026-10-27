module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G]

theorem R_card_modEq3 {T : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (T : Set G))
    (h3 : a ^ 3 = 1) : Nat.card (T ⊓ Cen a : Subgroup G) ≡ Nat.card T [MOD 3] := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype T := Fintype.ofFinite T
  let φ : MulAut T := T.normalizerMonoidHom ⟨a, ha⟩
  have hφ : ∀ u : T, ((φ u : T) : G) = a * u * a⁻¹ := fun u => rfl
  have hφ3 : ∀ u : T, (φ (φ (φ u)) : T) = u := by
    intro u
    apply Subtype.ext
    rw [hφ, hφ, hφ]
    have h3' : a * (a * a) = 1 := by rw [← pow_three]; exact h3
    calc a * (a * (a * (u : G) * a⁻¹) * a⁻¹) * a⁻¹
        = (a * (a * a)) * u * (a * (a * a))⁻¹ := by group
      _ = u := by rw [h3']; group
  let f : Function.End T := fun u => φ u
  have hf : f ^ 3 ^ 1 = 1 := by
    funext u
    show f (f (f u)) = u
    exact hφ3 u
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  have e : Nat.card f.fixedPoints = Nat.card (T ⊓ Cen a : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun u => ⟨(u.1 : G), Subgroup.mem_inf.2 ⟨u.1.2, ?_⟩⟩
        invFun := fun v => ⟨⟨(v : G), (Subgroup.mem_inf.1 v.2).1⟩, ?_⟩
        left_inv := fun u => rfl
        right_inv := fun v => rfl }
    · have hu : f u.1 = u.1 := u.2
      have hu' : a * (u.1 : G) * a⁻¹ = u.1 := congrArg Subtype.val hu
      apply S36_mem_cen_of
      calc a * (u.1 : G) = a * (u.1 : G) * a⁻¹ * a := by group
        _ = (u.1 : G) * a := by rw [hu']
    · show φ ⟨(v : G), (Subgroup.mem_inf.1 v.2).1⟩ = ⟨(v : G), (Subgroup.mem_inf.1 v.2).1⟩
      apply Subtype.ext
      rw [hφ]
      have hv : a * (v : G) = (v : G) * a := S36_comm_of_cen (Subgroup.mem_inf.1 v.2).2
      rw [hv, mul_inv_cancel_right]
  simp only [← Nat.card_eq_fintype_card] at h
  rw [e] at h
  exact h.symm

theorem R_card_cen {X T L : Subgroup G} {a : G} (hTX : T ≤ X) (hLX : L ≤ X)
    (hXT : X ≤ Subgroup.normalizer (T : Set G))
    (hTL : T ⊓ L = ⊥) (hdec : ∀ x ∈ X, ∃ u ∈ T, ∃ l ∈ L, x = u * l) (haL : a ∈ L) :
    Nat.card (X ⊓ Cen a : Subgroup G) = Nat.card (T ⊓ Cen a : Subgroup G) *
      Nat.card (L ⊓ Cen a : Subgroup G) := by
  rw [← Nat.card_prod]
  have hmul : ∀ p : ↥(T ⊓ Cen a : Subgroup G) × ↥(L ⊓ Cen a : Subgroup G),
      (p.1 : G) * (p.2 : G) ∈ (X ⊓ Cen a : Subgroup G) := by
    rintro ⟨⟨u, hu⟩, ⟨l, hl⟩⟩
    obtain ⟨huT, huc⟩ := Subgroup.mem_inf.1 hu
    obtain ⟨hlL, hlc⟩ := Subgroup.mem_inf.1 hl
    refine Subgroup.mem_inf.2 ⟨mul_mem (hTX huT) (hLX hlL), ?_⟩
    apply S36_mem_cen_of
    show a * (u * l) = u * l * a
    rw [← mul_assoc, S36_comm_of_cen huc, mul_assoc, S36_comm_of_cen hlc, mul_assoc]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => (⟨(p.1 : G) * (p.2 : G), hmul p⟩ : ↥(X ⊓ Cen a : Subgroup G))) ⟨?_, ?_⟩)
  · rintro ⟨⟨u, hu⟩, ⟨l, hl⟩⟩ ⟨⟨u', hu'⟩, ⟨l', hl'⟩⟩ h
    have h1 : u * l = u' * l' := congrArg Subtype.val h
    have hT' : u'⁻¹ * u ∈ T := mul_mem (T.inv_mem (Subgroup.mem_inf.1 hu').1)
      (Subgroup.mem_inf.1 hu).1
    have hL' : l' * l⁻¹ ∈ L := mul_mem (Subgroup.mem_inf.1 hl').1
      (L.inv_mem (Subgroup.mem_inf.1 hl).1)
    have heq : u'⁻¹ * u = l' * l⁻¹ := by
      calc u'⁻¹ * u = u'⁻¹ * (u * l) * l⁻¹ := by group
        _ = u'⁻¹ * (u' * l') * l⁻¹ := by rw [h1]
        _ = l' * l⁻¹ := by group
    have hbot : u'⁻¹ * u ∈ T ⊓ L := Subgroup.mem_inf.2 ⟨hT', heq ▸ hL'⟩
    rw [hTL, Subgroup.mem_bot] at hbot
    have hu_eq : u = u' := by
      calc u = u' * (u'⁻¹ * u) := by group
        _ = u' := by rw [hbot, mul_one]
    have hl_eq : l = l' := by
      have : l' * l⁻¹ = 1 := by rw [← heq, hbot]
      calc l = (l' * l⁻¹)⁻¹ * l' := by group
        _ = l' := by rw [this]; group
    subst hu_eq
    subst hl_eq
    rfl
  · rintro ⟨y, hy⟩
    obtain ⟨hyX, hyc⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨u, hu, l, hl, rfl⟩ := hdec y hyX
    have hyc' : a * (u * l) = (u * l) * a := S36_comm_of_cen hyc
    have hconj : u * (l * a * l⁻¹) * u⁻¹ = a := by
      calc u * (l * a * l⁻¹) * u⁻¹ = (u * l) * a * (u * l)⁻¹ := by group
        _ = a * (u * l) * (u * l)⁻¹ := by rw [← hyc']
        _ = a := by group
    have ha' : l * a * l⁻¹ ∈ L := mul_mem (mul_mem hl haL) (L.inv_mem hl)
    have hτ : a * (l * a * l⁻¹)⁻¹ ∈ T := by
      have h1 : (l * a * l⁻¹) * u⁻¹ * (l * a * l⁻¹)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.1 (hXT (hLX ha')) _).1 (T.inv_mem hu)
      have h2 : a * (l * a * l⁻¹)⁻¹ = u * ((l * a * l⁻¹) * u⁻¹ * (l * a * l⁻¹)⁻¹) := by
        calc a * (l * a * l⁻¹)⁻¹ = (u * (l * a * l⁻¹) * u⁻¹) * (l * a * l⁻¹)⁻¹ := by rw [hconj]
          _ = _ := by group
      rw [h2]
      exact mul_mem hu h1
    have hτL : a * (l * a * l⁻¹)⁻¹ ∈ L := mul_mem haL (L.inv_mem ha')
    have hbot : a * (l * a * l⁻¹)⁻¹ ∈ T ⊓ L := Subgroup.mem_inf.2 ⟨hτ, hτL⟩
    rw [hTL, Subgroup.mem_bot] at hbot
    have hla : l * a = a * l := by
      have h3 : a = l * a * l⁻¹ := mul_inv_eq_one.1 hbot
      calc l * a = (l * a * l⁻¹) * l := by group
        _ = a * l := by rw [← h3]
    have hlc : l ∈ Cen a := S36_mem_cen_of hla.symm
    have huc : u ∈ Cen a := by
      apply S36_mem_cen_of
      have : a * u * l = u * a * l := by
        calc a * u * l = a * (u * l) := mul_assoc _ _ _
          _ = (u * l) * a := hyc'
          _ = u * (l * a) := mul_assoc _ _ _
          _ = u * (a * l) := by rw [hla]
          _ = u * a * l := (mul_assoc _ _ _).symm
      exact mul_right_cancel this
    exact ⟨(⟨⟨u, Subgroup.mem_inf.2 ⟨hu, huc⟩⟩, ⟨l, Subgroup.mem_inf.2 ⟨hl, hlc⟩⟩⟩ :
      ↥(T ⊓ Cen a : Subgroup G) × ↥(L ⊓ Cen a : Subgroup G)), rfl⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
