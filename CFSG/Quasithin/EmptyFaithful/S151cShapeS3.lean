module

public import CFSG.Quasithin.EmptyFaithful.S151cOne
public import CFSG.Quasithin.EmptyFaithful.S151cGrp
public import CFSG.Quasithin.EmptyFaithful.S151cS3
public import CFSG.Quasithin.EmptyFaithful.S151cCases

public section

namespace CFSG.Quasithin

open CFSG.Open

section ShapeS3151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

theorem d3_sq_cube : ∀ x : DihedralGroup 3, x * x * (x * x) * (x * x) = 1 := by
  decide

theorem fittingOf_pow_three_of_equiv_D3 {Y : Subgroup (MulAut V)} (hO2 : pCoreOf 2 Y = ⊥)
    (e : ↥Y ≃* DihedralGroup 3) : ∀ x ∈ fittingOf Y, x ^ 3 = 1 := by
  intro x hx
  have hYcard : Nat.card Y = 6 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hodd := odd_card_fittingOf hO2
  have hFdvd : Nat.card (fittingOf Y) ∣ 6 :=
    hYcard ▸ Subgroup.card_dvd_of_le (fittingOf_le _)
  have h1 : x ^ Nat.card (fittingOf Y) = 1 := by
    have := pow_card_eq_one' (G := ↥(fittingOf Y)) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  have h2 : Nat.card (fittingOf Y) ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card (fittingOf Y)) 2 :=
      Nat.coprime_two_right.mpr hodd
    have h62 : (6 : ℕ) = 3 * 2 := by norm_num
    rw [h62] at hFdvd
    exact hcop.dvd_of_dvd_mul_right hFdvd
  obtain ⟨k, hk⟩ := h2
  rw [hk, pow_mul, h1, one_pow]

theorem hfix_order_three_of_equiv_D3 (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 Y = ⊥) (hcomm : commV (fittingOf Y) = ⊤) (e : ↥Y ≃* DihedralGroup 3) :
    ∀ g ∈ Y, orderOf g = 3 → ∀ u : V, g u = u → u = 1 := by
  intro g hg hg3 u hu
  have hfixF : fixV (fittingOf Y) = ⊥ := fixV_fittingOf_eq_bot hV hO2 hcomm
  have hF3 := fittingOf_pow_three_of_equiv_D3 hO2 e
  have hg3' : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    rintro rfl
    simp at hg3
  set a : ↥Y := ⟨g, hg⟩
  have hacube : e a * e a * e a = 1 := by
    have h3 : a ^ 3 = 1 := Subtype.ext hg3'
    have := congrArg e h3
    rw [map_pow, map_one, pow_three'] at this
    exact this
  have hne1 : e a ≠ 1 := fun h' =>
    hg1 (congrArg Subtype.val (e.injective (h'.trans (map_one e).symm)))
  have hu' : u ∈ fixV (fittingOf Y) := by
    intro x hx
    have hx' : x ∈ Y := fittingOf_le _ hx
    have hx3 : (⟨x, hx'⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (hF3 x hx)
    have hxc : e ⟨x, hx'⟩ * e ⟨x, hx'⟩ * e ⟨x, hx'⟩ = 1 := by
      have := congrArg e hx3
      rw [map_pow, map_one, pow_three'] at this
      exact this
    rcases d3_cube_eq (e a) (e ⟨x, hx'⟩) hacube hne1 hxc with h1 | h1 | h1
    · have : (⟨x, hx'⟩ : ↥Y) = 1 := e.injective (h1.trans (map_one e).symm)
      have hx1 : x = 1 := congrArg Subtype.val this
      rw [hx1]
      rfl
    · have : (⟨x, hx'⟩ : ↥Y) = a := e.injective h1
      have hxg : x = g := congrArg Subtype.val this
      rw [hxg]
      exact hu
    · have : (⟨x, hx'⟩ : ↥Y) = a * a := e.injective (h1.trans (map_mul e a a).symm)
      have hxg : x = g * g := congrArg Subtype.val this
      rw [hxg]
      show g (g u) = u
      rw [hu, hu]
  rw [hfixF] at hu'
  exact Subgroup.mem_bot.mp hu'

theorem sq_mem_fittingOf_of_equiv_D3 (hV : ∀ v : V, v ^ 2 = 1) (hnt : 1 < Nat.card V)
    {Y : Subgroup (MulAut V)} (hO2 : pCoreOf 2 Y = ⊥) (hcomm : commV (fittingOf Y) = ⊤)
    (e : ↥Y ≃* DihedralGroup 3) : ∀ l ∈ Y, l ^ 2 ∈ fittingOf Y := by
  intro l hl
  have hfixF : fixV (fittingOf Y) = ⊥ := fixV_fittingOf_eq_bot hV hO2 hcomm
  have hF3 := fittingOf_pow_three_of_equiv_D3 hO2 e
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp hnt
  obtain ⟨a, haF, ha1⟩ : ∃ a ∈ fittingOf Y, a ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ a ∈ fittingOf Y, a = 1 := fun a ha => by
      by_contra h
      exact hcon ⟨a, ha, h⟩
    obtain ⟨u, hu⟩ := exists_ne (1 : V)
    have hu' : u ∈ fixV (fittingOf Y) := fun g hg => by rw [hcon' g hg]; rfl
    rw [hfixF] at hu'
    exact hu (Subgroup.mem_bot.mp hu')
  have haY : a ∈ Y := fittingOf_le _ haF
  set a' : ↥Y := ⟨a, haY⟩
  set l' : ↥Y := ⟨l, hl⟩
  have ha3 : e a' * e a' * e a' = 1 := by
    have h3 : a' ^ 3 = 1 := Subtype.ext (hF3 a haF)
    have := congrArg e h3
    rw [map_pow, map_one, pow_three'] at this
    exact this
  have ha1' : e a' ≠ 1 := fun h' =>
    ha1 (congrArg Subtype.val (e.injective (h'.trans (map_one e).symm)))
  rcases d3_cube_eq (e a') (e l' * e l') ha3 ha1' (d3_sq_cube (e l')) with h1 | h1 | h1
  · have : l' * l' = 1 := e.injective (by rw [map_mul, h1, map_one])
    have hl1 : l * l = 1 := congrArg Subtype.val this
    rw [pow_two, hl1]
    exact (fittingOf Y).one_mem
  · have : l' * l' = a' := e.injective (by rw [map_mul]; exact h1)
    have hl1 : l * l = a := congrArg Subtype.val this
    rw [pow_two, hl1]
    exact haF
  · have : l' * l' = a' * a' := e.injective (by rw [map_mul, map_mul]; exact h1)
    have hl1 : l * l = a * a := congrArg Subtype.val this
    rw [pow_two, hl1]
    exact (fittingOf Y).mul_mem haF haF

theorem rk_commV_zpowers_eq_two_of_isOmegaFourPlus {Y : Subgroup (MulAut V)}
    (hY : IsOmegaFourPlus Y) {c : MulAut V} (hcY : c ∈ Y) (hc1 : c ≠ 1) (hc2 : c ^ 2 = 1) :
    rk (commV (Subgroup.zpowers c)) = 2 := by
  obtain ⟨c₀, rfl⟩ := S152O4.om4_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  have hA : IsA2 (S152O4.rhoV c₀).range (Subgroup.zpowers c) :=
    ⟨Subgroup.zpowers_le.mpr hcY, fun h => hc1 (Subgroup.zpowers_eq_bot.mp h),
      isElemAbelian2_zpowers151c hc2⟩
  have hcard2 : Nat.card (Subgroup.zpowers c) = 2 := by rw [Nat.card_zpowers, hord]
  have hrA := S151cOm4.rAV_of_card_two c₀ hA hcard2
  have hrk1 : rk (Subgroup.zpowers c) = 1 := by
    unfold rk
    rw [hcard2]
    simp
  unfold rAV at hrA
  rw [hrk1, rkIdx_fixV_zpowers] at hrA
  have h2 : ((rk (commV (Subgroup.zpowers c)) : ℕ) : ℚ) = 2 := by simpa using hrA
  exact_mod_cast h2

theorem nonempty_mulEquiv_prod_of_commute_inf_bot {G : Type*} [Group G] {X A B : Subgroup G}
    (hAX : A ≤ X) (hBX : B ≤ X) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hgen : ∀ x ∈ X, ∃ a ∈ A, ∃ b ∈ B, x = a * b) : Nonempty (↥X ≃* ↥A × ↥B) := by
  let φ : ↥A × ↥B →* ↥X := (Subgroup.inclusion hAX).noncommCoprod (Subgroup.inclusion hBX)
    (fun a b => Subtype.ext (hcomm a a.2 b b.2))
  have hφ : ∀ p : ↥A × ↥B, ((φ p : ↥X) : G) = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have h1 : (p.1 : G) * (p.2 : G) = 1 := by
      rw [← hφ p, hp]
      rfl
    have h2 : (p.1 : G) = (p.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (p.1 : G) ∈ A ⊓ B := ⟨p.1.2, by rw [h2]; exact B.inv_mem p.2.2⟩
    rw [hinf] at h3
    have h4 : (p.1 : G) = 1 := Subgroup.mem_bot.mp h3
    have h5 : (p.2 : G) = 1 := by rwa [h4, one_mul] at h1
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨a, ha, b, hb, hx⟩ := hgen x x.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (by rw [hφ]; exact hx.symm)⟩
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

theorem shape_S3 (B : OneBlock151c X Tb Xc J r) (e : Nonempty (↥J ≃* DihedralGroup 3))
    (hr : r = 2) (hrk : rk V = 4) : (ACase1 X J ∨ ACase2 X J) ∧ TwoNilpAut X := by
  obtain ⟨e⟩ := e
  set C : Subgroup (MulAut V) := Subgroup.centralizer (J : Set (MulAut V))
  have hcard : Nat.card V = 16 := by
    rw [card_eq_two_pow_rk B.sq, hrk]
    norm_num
  have hfix := hfix_order_three_of_equiv_D3 B.sq B.hyp.o2 B.hyp.comm_fitting e
  have hC6 : Nat.card C = 6 := S3mod_card_centralizer_of_equiv B.sq hcard e hfix
  have hΩ : IsOmegaFourPlus (J ⊔ C) := isOmegaFourPlus_of_S3_centralizer B.sq hcard e hfix
  have hJC : J ⊓ C = ⊥ := inf_centralizer_eq_bot_D3 e
  have hnorm : ∀ x ∈ X, x ∈ Subgroup.normalizer (J : Set (MulAut V)) := fun x hx =>
    B.normal.le_normalizer hx
  have hdecomp : ∀ x ∈ X, ∃ l ∈ J, ∃ d ∈ X ⊓ C, x = l * d := by
    intro x hx
    obtain ⟨l, hl, d, hdX, hdc, hxd⟩ := exists_mul_eq_of_normalizes_D3 e B.le hnorm hx
    exact ⟨l, hl, d, ⟨hdX, Subgroup.mem_centralizer_iff.mpr fun m hm => (hdc m hm).symm⟩, hxd⟩
  have hcommJY : ∀ a ∈ J, ∀ b ∈ X ⊓ C, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ha
  have hodd : ¬ 2 ∣ Nat.card ↥(X ⊓ C) := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcord : orderOf (c : MulAut V) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
    have hc2 : (c : MulAut V) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (c : MulAut V)
      rwa [hcord] at this
    have hc1 : (c : MulAut V) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hcord
      omega
    have hcX : (c : MulAut V) ∈ X := c.2.1
    have hcC : (c : MulAut V) ∈ C := c.2.2
    have hrk2 :=
      rk_commV_zpowers_eq_two_of_isOmegaFourPlus hΩ (Subgroup.mem_sup_right hcC) hc1 hc2
    have hcJ : (c : MulAut V) ∈ J := B.offender hcX hc1 hc2 (by rw [hrk2, hr]; norm_num)
    have hcJC : (c : MulAut V) ∈ J ⊓ C := ⟨hcJ, hcC⟩
    rw [hJC] at hcJC
    exact hc1 (Subgroup.mem_bot.mp hcJC)
  have hdvd6 : Nat.card ↥(X ⊓ C) ∣ 6 := hC6 ▸ Subgroup.card_dvd_of_le inf_le_right
  have hdvd3 : Nat.card ↥(X ⊓ C) ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card ↥(X ⊓ C)) 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    have h62 : (6 : ℕ) = 3 * 2 := by norm_num
    rw [h62] at hdvd6
    exact hcop.dvd_of_dvd_mul_right hdvd6
  have hTN : TwoNilpAut X := by
    have hF3 := fittingOf_pow_three_of_equiv_D3 B.hyp.o2 e
    have hsq := sq_mem_fittingOf_of_equiv_D3 B.sq (by omega) B.hyp.o2 B.hyp.comm_fitting e
    have hconjF : ∀ g ∈ X, ∀ f ∈ fittingOf J, g * f * g⁻¹ ∈ fittingOf J := by
      intro g hg f hf
      obtain ⟨l, hl, d, hd, rfl⟩ := hdecomp g hg
      have hdf : d * f = f * d := (hcommJY f (fittingOf_le J hf) d hd).symm
      have h : l * d * f * (l * d)⁻¹ = l * f * l⁻¹ := by
        calc l * d * f * (l * d)⁻¹ = l * (d * f) * d⁻¹ * l⁻¹ := by group
          _ = l * (f * d) * d⁻¹ * l⁻¹ := by rw [hdf]
          _ = l * f * l⁻¹ := by group
      rw [h]
      exact conj_mem_fittingOf hl hf
    have hconjY : ∀ g ∈ X, ∀ y ∈ X ⊓ C, g * y * g⁻¹ ∈ X ⊓ C := by
      intro g hg y hy
      obtain ⟨l, hl, d, hd, rfl⟩ := hdecomp g hg
      have hy' : d * y * d⁻¹ ∈ X ⊓ C :=
        (X ⊓ C).mul_mem ((X ⊓ C).mul_mem hd hy) ((X ⊓ C).inv_mem hd)
      have hc : l * (d * y * d⁻¹) = (d * y * d⁻¹) * l := hcommJY l hl _ hy'
      have h : l * d * y * (l * d)⁻¹ = d * y * d⁻¹ := by
        calc l * d * y * (l * d)⁻¹ = l * (d * y * d⁻¹) * l⁻¹ := by group
          _ = (d * y * d⁻¹) * l * l⁻¹ := by rw [hc]
          _ = d * y * d⁻¹ := by group
      rw [h]
      exact hy'
    have hK3 : IsPGroup 3 ↥(fittingOf J) := fun x =>
      ⟨1, Subtype.ext (by simpa using hF3 x x.2)⟩
    have hN3 : IsPGroup 3 ↥(X ⊓ C) :=
      IsPGroup.of_card_dvd_pow (n := 1) (by rw [pow_one]; exact hdvd3)
    have hcommFY : ∀ a ∈ fittingOf J, ∀ b ∈ X ⊓ C, a * b = b * a := fun a ha b hb =>
      hcommJY a (fittingOf_le J ha) b hb
    have hNodd : Odd (Nat.card ↥(fittingOf J ⊔ (X ⊓ C))) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).mp (isPGroup_sup_of_commute151c hK3 hN3 hcommFY)
      rw [hn]
      exact Odd.pow (by decide)
    refine ⟨fittingOf J ⊔ (X ⊓ C), sup_le ((fittingOf_le J).trans B.le) inf_le_left, ?_, hNodd, ?_⟩
    · intro g hg y hy
      obtain ⟨f, hf, d', hd', rfl⟩ := mem_sup_of_commute216 hcommFY hy
      have h : g * (f * d') * g⁻¹ = (g * f * g⁻¹) * (g * d' * g⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem_sup (hconjF g hg f hf) (hconjY g hg d' hd')
    · intro x hx
      refine ⟨1, ?_⟩
      obtain ⟨l, hl, d, hd, rfl⟩ := hdecomp x hx
      have hc : Commute l d := hcommJY l hl d hd
      rw [pow_one, hc.mul_pow]
      exact Subgroup.mul_mem_sup (hsq l hl) ((X ⊓ C).pow_mem hd 2)
  refine ⟨?_, hTN⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
  · left
    have hbot : X ⊓ C = ⊥ := Subgroup.card_eq_one.mp h1
    refine ⟨hcard, le_antisymm (fun x hx => ?_) B.le, ⟨e⟩⟩
    obtain ⟨l, hl, d, hd, rfl⟩ := hdecomp x hx
    rw [hbot] at hd
    rw [Subgroup.mem_bot.mp hd, mul_one]
    exact hl
  · right
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
    have eY : ↥(X ⊓ C) ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq h3 hcard3
    have hinf : J ⊓ (X ⊓ C) = ⊥ := by
      rw [eq_bot_iff, ← hJC]
      exact inf_le_inf_left J inf_le_right
    obtain ⟨eX⟩ := nonempty_mulEquiv_prod_of_commute_inf_bot (X := X) (A := J) (B := X ⊓ C)
      B.le inf_le_left hcommJY hinf hdecomp
    exact ⟨hcard, ⟨e⟩, ⟨eX.trans (MulEquiv.prodCongr e eY)⟩⟩

end ShapeS3151c

end CFSG.Quasithin
