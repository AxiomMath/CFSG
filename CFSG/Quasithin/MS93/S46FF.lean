module

public import CFSG.Quasithin.MS93.S32Dict
public import CFSG.Quasithin.MS93.SkTypes
public import CFSG.Quasithin.MS93.S4AEA
public import CFSG.Quasithin.MS93.ML3Split
public import CFSG.Quasithin.Background.SmithC27RCaseIOrd

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix

section SL3

variable {F : Type} [Field F]

theorem isQuasisimple_SL3 [Finite F] : CFSG.IsQuasisimple (SL3 F) :=
  CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
    (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem isPerfect_SL3 : Group.IsPerfect (SL3 F) :=
  CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl

theorem pow_three_eq_one_of_mem_center {g : SL3 F} (hg : g ∈ Subgroup.center (SL3 F)) :
    g ^ 3 = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrg, ← map_pow, hr, map_one]
  rfl

theorem card_center_SL3_le : Nat.card (Subgroup.center (SL3 F)) ≤ 3 := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) 0
  rw [Nat.card_congr e.toEquiv, Fintype.card_fin]
  exact card_rootsOfUnity (R := F) (k := 3)

end SL3

theorem eq_one_of_pow_three {G : Type*} [Monoid G] {g : G} (h3 : g ^ 3 = 1) {e : ℕ}
    (he : g ^ 2 ^ e = 1) : g = 1 := by
  have h1 : orderOf g ∣ Nat.gcd 3 (2 ^ e) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one he)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e (by norm_num)), Nat.dvd_one] at h1
  exact orderOf_eq_one_iff.mp h1

section Arith

theorem two_pow_mul_odd_eq {x y u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ x * u = 2 ^ y * v) : x = y ∧ u = v := by
  have key : ∀ {x y u v : ℕ}, Odd u → Odd v → 2 ^ x * u = 2 ^ y * v → x ≤ y →
      x = y ∧ u = v := by
    intro x y u v hu _ h hxy
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [pow_add, mul_assoc] at h
    have h' : u = 2 ^ d * v := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa using h'
    · exfalso
      rw [h'] at hu
      have : Even (2 ^ d * v) := (Nat.even_pow.2 ⟨even_two, hd.ne'⟩).mul_right v
      exact (Nat.not_even_iff_odd.2 hu) this
  rcases le_total x y with hxy | hyx
  · exact key hu hv h hxy
  · obtain ⟨h1, h2⟩ := key hv hu h.symm hyx
    exact ⟨h1.symm, h2.symm⟩

theorem odd_two_pow_pow_sub_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : Odd ((2 ^ n) ^ k - 1) := by
  rw [← pow_mul]
  have hnk : n * k ≠ 0 := by positivity
  exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hnk⟩) odd_one

theorem card_SL3_two_pow {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) =
      2 ^ (3 * n) * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) ∧
      Odd (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) :=
  ⟨by rw [← pow_mul, mul_comm n 3],
    (odd_two_pow_pow_sub_one hn (by norm_num)).mul (odd_two_pow_pow_sub_one hn (by norm_num))⟩

theorem eq_of_card_SL3_eq {n m c : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hc : Odd c)
    (h : (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) =
      c * ((2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))) : n = m := by
  obtain ⟨e1, o1⟩ := card_SL3_two_pow hn
  obtain ⟨e2, o2⟩ := card_SL3_two_pow hm
  have h' : 2 ^ (3 * n) * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) =
      2 ^ (3 * m) * (c * (((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1))) := by
    rw [← e1, h, ← pow_mul, mul_comm 3 m, pow_mul]
    ring
  have := (two_pow_mul_odd_eq o1 (hc.mul o2) h').1
  omega

theorem card_SL3_ne_eight_mul {n c d : ℕ} (hn : 1 ≤ n) (hc : Odd c) (hd : Odd d) (hd21 : 21 < d)
    (h : (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) = c * (2 ^ 3 * d)) : False := by
  obtain ⟨e1, o1⟩ := card_SL3_two_pow hn
  have h' : 2 ^ (3 * n) * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) = 2 ^ 3 * (c * d) := by
    rw [← e1, h]
    ring
  obtain ⟨h3, hu⟩ := two_pow_mul_odd_eq o1 (hc.mul hd) h'
  have hn1 : n = 1 := by omega
  subst hn1
  have hc1 : 1 ≤ c := hc.pos
  have : 21 = c * d := by rw [← hu]; norm_num
  nlinarith

theorem card_SL3_ne_card_G2 {n m c : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hc : c = 1 ∨ c = 3)
    (h : (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) =
      c * ((2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)))) : False := by
  have hco : Odd c := by rcases hc with rfl | rfl <;> decide
  obtain ⟨e1, o1⟩ := card_SL3_two_pow hn
  have o2 : Odd (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) :=
    (odd_two_pow_pow_sub_one hm (by norm_num)).mul (odd_two_pow_pow_sub_one hm (by norm_num))
  have h' : 2 ^ (3 * n) * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) =
      2 ^ (6 * m) * (c * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) := by
    rw [← e1, h, ← pow_mul, mul_comm 6 m]
    ring
  obtain ⟨h3, hu⟩ := two_pow_mul_odd_eq o1 (hco.mul o2) h'
  have hnm : n = 2 * m := by omega
  subst hnm
  set y := (2 ^ m) ^ 2 with hy
  have hy4 : 4 ≤ y := by
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [hy]
    nlinarith
  have e3 : (2 ^ (2 * m)) ^ 3 = y ^ 3 := by rw [hy]; ring
  have e2 : (2 ^ (2 * m)) ^ 2 = y ^ 2 := by rw [hy]; ring
  have e6 : (2 ^ m) ^ 6 = y ^ 3 := by rw [hy]; ring
  rw [e3, e2, e6] at hu
  have hy3 : 1 ≤ y ^ 3 - 1 := by
    have : 64 ≤ y ^ 3 := by nlinarith
    omega
  have hu' : (y ^ 2 - 1) = c * (y - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < y ^ 3 - 1 by omega)
    rw [hu]
    ring
  have hsq : y ^ 2 - 1 = (y - 1) * (y + 1) := by
    have : 1 ≤ y := by omega
    zify [this, Nat.one_le_pow 2 y (by omega)]
    ring
  rw [hsq] at hu'
  have hpos : 0 < y - 1 := by omega
  have : y + 1 = c := by
    have := Nat.eq_of_mul_eq_mul_left hpos (hu'.trans (mul_comm c (y - 1)))
    exact this
  rcases hc with rfl | rfl <;> omega

end Arith

theorem mem_range_apply {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) : f g ∈ f.range :=
  MonoidHom.mem_range.mpr ⟨g, rfl⟩

section Rep

variable {F : Type} [Field F] [Finite F] {V : Type} [CommGroup V] (ρ : SL3 F →* MulAut V)

omit [Finite F] in
theorem exists_rangeRestrict_ne_one (hnt : ∃ g v, ρ g v ≠ v) : ∃ g, ρ.rangeRestrict g ≠ 1 := by
  obtain ⟨g, v, hv⟩ := hnt
  refine ⟨g, fun h => hv ?_⟩
  have h' : ρ g = 1 := congrArg Subtype.val h
  rw [h', MulAut.one_apply]

theorem ker_le_center (hnt : ∃ g v, ρ g v ≠ v) : ρ.ker ≤ Subgroup.center (SL3 F) := by
  rw [← MonoidHom.ker_rangeRestrict]
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple isQuasisimple_SL3
    (exists_rangeRestrict_ne_one ρ hnt)

theorem isQuasisimple_range (hnt : ∃ g v, ρ g v ≠ v) : CFSG.IsQuasisimple ↥ρ.range :=
  CFSG.LieType.CurtisTits.isQuasisimple_of_surjective isQuasisimple_SL3
    ρ.rangeRestrict_surjective (exists_rangeRestrict_ne_one ρ hnt)

omit [Finite F] in
theorem card_SL3_eq_mul : Nat.card (SL3 F) = Nat.card ρ.ker * Nat.card ρ.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm]

theorem card_ker_cases (hnt : ∃ g v, ρ g v ≠ v) :
    Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3 := by
  have hle := ker_le_center ρ hnt
  have h3 : Nat.card ρ.ker ≤ 3 := (Subgroup.card_le_of_le hle).trans card_center_SL3_le
  have h0 : 0 < Nat.card ρ.ker := Nat.card_pos
  have h2 : Nat.card ρ.ker ≠ 2 := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥ρ.ker) 2 (by rw [h2])
    have hg3 : g ^ 3 = 1 :=
      Subtype.ext (by simpa using pow_three_eq_one_of_mem_center (hle g.2))
    have := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at this
    norm_num at this
  omega

theorem rankTwo_range {n : ℕ} (hF : Nat.card F = 2 ^ n) (hnt : ∃ g v, ρ g v ≠ v) :
    IsRankTwoLie2Derived (↥ρ.range ⧸ Subgroup.center ↥ρ.range) := by
  have hker : ρ.rangeRestrict.ker ≤ Subgroup.center (SL3 F) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_le_center ρ hnt
  exact isRankTwoLie2Derived_of_mulEquiv
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple isQuasisimple_SL3
      ρ.rangeRestrict_surjective hker)
    (Or.inl ⟨n, (isPSL_quot_of_equiv_statedSL_three hF
      (specialLinearGroupEquivStatedSL 3 F).symm).2.1⟩)

theorem pow_three_eq_one_of_central (hnt : ∃ g v, ρ g v ≠ v) {c : MulAut V} (hc : c ∈ ρ.range)
    (hck : ∀ k ∈ ρ.range, c * k = k * c) : c ^ 3 = 1 := by
  have hker : ρ.rangeRestrict.ker ≤ Subgroup.center (SL3 F) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_le_center ρ hnt
  have hZ := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple isQuasisimple_SL3
    ρ.rangeRestrict_surjective hker
  have hcZ : (⟨c, hc⟩ : ↥ρ.range) ∈ Subgroup.center ↥ρ.range := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hck k k.2).symm
  rw [hZ] at hcZ
  obtain ⟨z, hz, hzc⟩ := hcZ
  have hcz : ρ z = c := by
    have := congrArg Subtype.val hzc
    rwa [MonoidHom.coe_rangeRestrict] at this
  rw [← hcz, ← map_pow, pow_three_eq_one_of_mem_center hz, map_one]

theorem cent_range (hnt : ∃ g v, ρ g v ≠ v) : ∀ c ∈ ρ.range, (∀ k ∈ ρ.range, c * k = k * c) →
    ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1 := fun _ hc hck _ he =>
  eq_one_of_pow_three (pow_three_eq_one_of_central ρ hnt hc hck) he

variable [Finite V]

omit [Finite F] in
theorem gen_range (hV2 : ∀ v : V, v ^ 2 = 1)
    (hirr : ∀ W : Subgroup V, (∀ g : SL3 F, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ g v, ρ g v ≠ v) :
    ∃ T : Subgroup (MulAut V), IsSylowTwoOf T ρ.range ∧
      G6.submoduleClosure ρ.range (fixV T) = ⊤ := by
  obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : ⊥ ≤ ρ.range) IsPGroup.of_bot
  refine ⟨T, hT, ?_⟩
  have hVne : (⊤ : Subgroup V) ≠ ⊥ := by
    obtain ⟨g, v, hv⟩ := hnt
    intro h
    have hv1 : v = 1 := by
      have : v ∈ (⊤ : Subgroup V) := Subgroup.mem_top v
      rwa [h, Subgroup.mem_bot] at this
    exact hv (by rw [hv1, map_one])
  obtain ⟨m, -, hm1, hmfix⟩ := B1.exists_fixed_ne_one hV2 hT.2.1 (M := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _) hVne
  rcases hirr _ (fun g w hw => submoduleClosure_inv (mem_range_apply ρ g) hw) with h0 | h1
  · exfalso
    have : m ∈ G6.submoduleClosure ρ.range (fixV T) :=
      le_submoduleClosure _ _ (fun b hb => hmfix b hb)
    rw [h0, Subgroup.mem_bot] at this
    exact hm1 this
  · exact h1

omit [Finite F] [Finite V] in
theorem fix_range (hirr : ∀ W : Subgroup V, (∀ g : SL3 F, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ g v, ρ g v ≠ v) : fixV ρ.range = ⊥ := by
  rcases hirr (fixV ρ.range) (fun g w hw => by rw [hw (ρ g) (mem_range_apply ρ g)]; exact hw)
    with h | h
  · exact h
  · exfalso
    obtain ⟨g, v, hv⟩ := hnt
    have : v ∈ fixV ρ.range := by rw [h]; trivial
    exact hv (this (ρ g) (mem_range_apply ρ g))

theorem ffHyp_range (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F)) {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hV2 : ∀ v : V, v ^ 2 = 1)
    (hirr : ∀ W : Subgroup V, (∀ g : SL3 F, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ g v, ρ g v ≠ v) (hff : IsFFModule ρ.range) : FFHyp ρ.range ρ.range where
  le := le_rfl
  le_normalizer := Subgroup.le_normalizer
  quasisimple := isQuasisimple_range ρ hnt
  sqtk := hSQ (SL3 F) ↥ρ.range hsq ρ.rangeRestrict ρ.rangeRestrict_surjective
    (isQuasisimple_range ρ hnt)
  rankTwo := rankTwo_range ρ hF hnt
  cent := cent_range ρ hnt
  two := fun x hx => ⟨0, by simpa using hx⟩
  gen := gen_range ρ hV2 hirr hnt
  fix := fix_range ρ hirr hnt
  ff := hff

end Rep

theorem card_eq_of_coord {F' V : Type} [CommGroup V] [AddCommGroup F']
    (θ : V ≃* Multiplicative (Fin 3 → F')) {P : Subgroup V} {S : Set (Fin 3 → F')}
    (h : ∀ v, v ∈ P ↔ Multiplicative.toAdd (θ v) ∈ S) : Nat.card P = Nat.card S := by
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd (θ v), (h v).1 v.2⟩
      invFun := fun x => ⟨θ.symm (Multiplicative.ofAdd x), (h _).2 (by simp)⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

theorem card_of_coord {F' V : Type} [CommGroup V] [AddCommGroup F'] [Finite F']
    (θ : V ≃* Multiplicative (Fin 3 → F')) : Nat.card V = Nat.card F' ^ 3 := by
  rw [Nat.card_congr θ.toEquiv]
  show Nat.card (Fin 3 → F') = _
  rw [Nat.card_fun, Nat.card_fin]

section Coord

variable {F' : Type} [Field F'] {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}
  (σ : SL3 F' ≃* ↥K) (θ : V ≃* Multiplicative (Fin 3 → F'))

abbrev IsNatCoord : Prop :=
  ∀ (g : SL3 F') (v : V), θ ((σ g : MulAut V) v) =
    Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F') *ᵥ Multiplicative.toAdd (θ v))

variable {σ θ}

theorem symm_ofAdd_mulVec (hθ : IsNatCoord σ θ) (g : SL3 F') (x : Fin 3 → F') :
    θ.symm (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F') *ᵥ x)) =
      (σ g : MulAut V) (θ.symm (Multiplicative.ofAdd x)) := by
  apply θ.injective
  rw [hθ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]

variable {E : Subgroup (SL3 F')} {B : Subgroup (MulAut V)}

theorem mem_fixV_iff_coord (hθ : IsNatCoord σ θ) (hE : ∀ g, g ∈ E ↔ (σ g : MulAut V) ∈ B)
    (hBK : B ≤ K) (v : V) : v ∈ fixV B ↔ Multiplicative.toAdd (θ v) ∈ fixN E := by
  constructor
  · intro hv g hg
    have h1 := hθ g v
    rw [hv _ ((hE g).1 hg)] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  · intro hx b hb
    have hg : σ.symm ⟨b, hBK hb⟩ ∈ E := (hE _).2 (by rw [MulEquiv.apply_symm_apply]; exact hb)
    have h1 := hθ (σ.symm ⟨b, hBK hb⟩) v
    rw [hx _ hg, MulEquiv.apply_symm_apply, ofAdd_toAdd] at h1
    exact θ.injective h1

theorem mem_commV_iff_coord (hθ : IsNatCoord σ θ) (hE : ∀ g, g ∈ E ↔ (σ g : MulAut V) ∈ B)
    (hBK : B ≤ K) (v : V) : v ∈ commV B ↔ Multiplicative.toAdd (θ v) ∈ commN E := by
  constructor
  · intro hv
    induction hv using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨b, hb, v₀, rfl⟩ := hw
      have hg : σ.symm ⟨b, hBK hb⟩ ∈ E :=
        (hE _).2 (by rw [MulEquiv.apply_symm_apply]; exact hb)
      have h1 := hθ (σ.symm ⟨b, hBK hb⟩) v₀
      rw [MulEquiv.apply_symm_apply] at h1
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h1, toAdd_ofAdd, ← sub_eq_add_neg]
      exact sub_mem_commN hg _
    | one => rw [map_one, toAdd_one]; exact (commN E).zero_mem
    | mul a b _ _ ha hb =>
      rw [map_mul, toAdd_mul]
      exact (commN E).add_mem ha hb
    | inv a _ ha =>
      rw [map_inv, toAdd_inv]
      exact (commN E).neg_mem ha
  · intro hx
    rw [← Submodule.mem_toAddSubgroup, commN_eq_closure] at hx
    suffices h : ∀ x ∈ AddSubgroup.closure {y | ∃ g ∈ E, ∃ x : Fin 3 → F',
        ((g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ x - x = y},
        θ.symm (Multiplicative.ofAdd x) ∈ commV B by
      simpa using h _ hx
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨g, hg, x, rfl⟩ := hy
      rw [ofAdd_sub, map_div, symm_ofAdd_mulVec hθ, div_eq_mul_inv]
      exact Subgroup.subset_closure ⟨_, (hE g).1 hg, _, rfl⟩
    | zero => rw [ofAdd_zero, map_one]; exact (commV B).one_mem
    | add a b _ _ ha hb =>
      rw [ofAdd_add, map_mul]
      exact (commV B).mul_mem ha hb
    | neg a _ ha =>
      rw [ofAdd_neg, map_inv]
      exact (commV B).inv_mem ha

theorem card_lt_of_coord [Finite F'] [CharP F' 2] [Finite V] (hθ : IsNatCoord σ θ)
    (hBK : B ≤ K) (hB : B ≠ ⊥) (hBe : IsElemAbelian2 B) :
    Nat.card B < (fixV B).index * Nat.card (commV B) := by
  set E : Subgroup (SL3 F') := (B.subgroupOf K).comap σ.toMonoidHom with hEdef
  have hE : ∀ g, g ∈ E ↔ (σ g : MulAut V) ∈ B := fun g => Iff.rfl
  have hcard : Nat.card E = Nat.card B := by
    have h1 : E.map σ.toMonoidHom = B.subgroupOf K :=
      Subgroup.map_comap_eq_self_of_surjective σ.surjective _
    rw [← Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective, h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  have h2 : ∀ g ∈ E, g * g = 1 := by
    intro g hg
    apply σ.injective
    rw [map_mul, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    exact hBe.2 _ ((hE g).1 hg)
  have hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g := by
    intro g hg g' hg'
    apply σ.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hBe.1 _ ((hE g).1 hg) _ ((hE g').1 hg')
  have hE1 : E ≠ ⊥ := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
    intro hbot
    have hg : σ.symm ⟨b, hBK hb⟩ ∈ E := (hE _).2 (by rw [MulEquiv.apply_symm_apply]; exact hb)
    rw [hbot, Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at hg
    have hb' : b = 1 := congrArg Subtype.val hg
    exact hb1 (Subtype.ext hb')
  set q := Nat.card F' with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  set d := Module.finrank F' (fixN E) with hd
  set s := Module.finrank F' (commN E) with hs
  have hsd : s ≤ d := finrank_commN_le_finrank_fixN_of_elemAb h2 hc
  have hs1 : 1 ≤ s := by
    refine Nat.pos_of_ne_zero fun h0 => commN_ne_bot hE1 ?_
    exact Submodule.finrank_eq_zero.mp h0
  have hd3 : d ≤ 3 := by
    have := Submodule.finrank_le (fixN E)
    rwa [Module.finrank_fin_fun] at this
  have hd2 : d ≤ 2 := by
    by_contra hcon
    have htop : fixN E = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      omega
    apply hE1
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact eq_one_of_mulVec_eq_self fun x => by
      have hx : x ∈ fixN E := by rw [htop]; trivial
      exact hx g hg
  have hle : Nat.card E ≤ q ^ ((3 - d) * s) := card_le_of_elemAb h2 hc
  have hfix : Nat.card (fixV B) = q ^ d := by
    rw [card_eq_of_coord θ (S := (fixN E : Set (Fin 3 → F'))) (mem_fixV_iff_coord hθ hE hBK)]
    exact card_fixN E
  have hcomm : Nat.card (commV B) = q ^ s := by
    rw [card_eq_of_coord θ (S := (commN E : Set (Fin 3 → F')))
      (mem_commV_iff_coord hθ hE hBK)]
    exact Module.natCard_eq_pow_finrank
  have hidx : (fixV B).index = q ^ (3 - d) := by
    have h1 := (fixV B).index_mul_card
    rw [hfix, card_of_coord θ, ← hq] at h1
    have h3 : q ^ 3 = q ^ (3 - d) * q ^ d := by rw [← pow_add, Nat.sub_add_cancel hd3]
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  rw [← hcard, hidx, hcomm, ← pow_add]
  refine hle.trans_lt (Nat.pow_lt_pow_right hq2 ?_)
  rcases (by omega : d = 1 ∨ d = 2) with h | h <;> rw [h] at hsd ⊢ <;> omega

theorem form_eq_one_of_coord (hθ : IsNatCoord σ θ) {M : Type*} [CommGroup M]
    (f : V →* V →* M) (hf : ∀ k ∈ K, ∀ v w, f (k v) (k w) = f v w) : f = 1 := by
  classical
  set ι : (Fin 3 → F') → V := fun x => θ.symm (Multiplicative.ofAdd x) with hι
  have hι_add : ∀ x y, ι (x + y) = ι x * ι y := fun x y => by
    simp only [hι, ofAdd_add, map_mul]
  have hι_zero : ι 0 = 1 := by simp only [hι, ofAdd_zero, map_one]
  have hsingle : ∀ (i k : Fin 3) (c b : F'), f (ι (Pi.single i c)) (ι (Pi.single k b)) = 1 := by
    intro i k c b
    obtain ⟨j, hji, hjk⟩ : ∃ j : Fin 3, j ≠ i ∧ j ≠ k := by
      fin_cases i <;> fin_cases k
      exacts [⟨1, by decide, by decide⟩, ⟨2, by decide, by decide⟩, ⟨1, by decide, by decide⟩,
        ⟨2, by decide, by decide⟩, ⟨0, by decide, by decide⟩, ⟨0, by decide, by decide⟩,
        ⟨1, by decide, by decide⟩, ⟨0, by decide, by decide⟩, ⟨0, by decide, by decide⟩]
    have hij : i ≠ j := hji.symm
    have h1 : (σ (rootElt i j c) : MulAut V) (ι (Pi.single j 1)) =
        ι (Pi.single j 1 + Pi.single i c) := by
      rw [hι, ← symm_ofAdd_mulVec hθ, rootElt_mulVec hij, Pi.single_eq_same, mul_one]
    have h2 : (σ (rootElt i j c) : MulAut V) (ι (Pi.single k b)) = ι (Pi.single k b) := by
      rw [hι, ← symm_ofAdd_mulVec hθ, rootElt_mulVec hij, Pi.single_eq_of_ne hjk, mul_zero,
        Pi.single_zero, add_zero]
    have := hf _ (σ (rootElt i j c)).2 (ι (Pi.single j 1)) (ι (Pi.single k b))
    rw [h1, h2, hι_add, map_mul, MonoidHom.mul_apply] at this
    exact mul_eq_left.mp this
  have hfirst : ∀ (x : Fin 3 → F') (k : Fin 3) (b : F'), f (ι x) (ι (Pi.single k b)) = 1 := by
    intro x k b
    rw [← Finset.univ_sum_single x]
    refine Finset.sum_induction _ (fun y => f (ι y) (ι (Pi.single k b)) = 1) ?_ ?_ ?_
    · intro y z hy hz
      rw [hι_add, map_mul, MonoidHom.mul_apply, hy, hz, mul_one]
    · rw [hι_zero, map_one, MonoidHom.one_apply]
    · intro i _
      exact hsingle i k (x i) b
  have hall : ∀ (v : V) (y : Fin 3 → F'), f v (ι y) = 1 := by
    intro v y
    have hv : v = ι (Multiplicative.toAdd (θ v)) := by simp [hι]
    rw [hv, ← Finset.univ_sum_single y]
    refine Finset.sum_induction _ (fun z => f (ι (Multiplicative.toAdd (θ v))) (ι z) = 1)
      ?_ ?_ ?_
    · intro y z hy hz
      rw [hι_add, map_mul, hy, hz, mul_one]
    · rw [hι_zero, map_one]
    · intro k _
      exact hfirst _ k (y k)
  ext v w
  have hw : w = ι (Multiplicative.toAdd (θ w)) := by simp [hι]
  rw [hw, hall v]
  rfl

end Coord

section Main

variable {F : Type} [Field F] [Finite F] {V : Type} [CommGroup V] [Finite V]
  (ρ : SL3 F →* MulAut V)

theorem exists_natCoord (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F)) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hV2 : ∀ v : V, v ^ 2 = 1)
    (hirr : ∀ W : Subgroup V, (∀ g : SL3 F, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ g v, ρ g v ≠ v) (hff : IsFFModule ρ.range) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = Nat.card F ∧
      ∃ (σ : SL3 F' ≃* ↥ρ.range) (θ : V ≃* Multiplicative (Fin 3 → F')), IsNatCoord σ θ := by
  obtain ⟨-, -, hcases, -⟩ := h14 V hV2 _ _ (ffHyp_range ρ hSQ hsq hF hV2 hirr hnt hff)
  have hn : 1 ≤ n := R3c2.one_le_of_natCard_eq_two_pow hF
  have hcard : Nat.card (SL3 F) = Nat.card ρ.ker * Nat.card ρ.range := card_SL3_eq_mul ρ
  have hc13 := card_ker_cases ρ hnt
  set c := Nat.card ρ.ker with hcdef
  have hco : Odd c := by rcases hc13 with h | h <;> rw [h] <;> decide
  rw [card_SL3, hF] at hcard
  rcases hcases with ⟨n', F', iF', fF', hn', hF', -, -, hnat | hdsum⟩ | ⟨-, hHat, -, -⟩ |
    (⟨n', hn', F'', iF'', fF'', hF'', π, hπ⟩ | ⟨π, hπ⟩) |
    (⟨n', hn', F'', iF'', fF'', hF'', π, hπ⟩ | ⟨-, hne, -⟩)
  ·
    obtain ⟨π, hπ⟩ := hnat
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    have hK : Nat.card ρ.range = Nat.card (StatedSL 3 F') := (Nat.card_congr e.toEquiv).symm
    rw [hK, CFSG.SectionRank.OddCover.card_statedSL_three, hF'] at hcard
    have hnn := eq_of_card_SL3_eq hn hn' hco hcard
    obtain ⟨β, hβs, hβk, hβe⟩ :=
      FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL 3 F')) rfl rfl hπ
    have hβi : Function.Injective β := by
      rw [injective_iff_map_eq_one]
      intro u hu
      exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
    let θ : V ≃* Multiplicative (Fin 3 → F') :=
      (Subgroup.topEquiv (G := V)).symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)
    let σ : SL3 F' ≃* ↥ρ.range := (specialLinearGroupEquivStatedSL 3 F').trans e
    refine ⟨F', iF', fF', by rw [hF', hF, hnn], σ, θ, fun g v => ?_⟩
    exact hβe (specialLinearGroupEquivStatedSL 3 F' g) ⟨v, Subgroup.mem_top v⟩ trivial
  ·
    exfalso
    obtain ⟨I, π, -, hind, hsup, hreal⟩ := hdsum
    have h01 : I 0 ⊓ I 1 = ⊥ := by
      apply le_bot_iff.mp
      rw [← hind 0]
      refine inf_le_inf_left _ (le_sup_of_le_right ?_)
      exact le_iSup₂_of_le (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1 (by decide) le_rfl
    have hne : ∀ i, I i ≠ ⊥ := by
      intro i hi
      have h1 := card_of_realizesVia_nat (hreal i)
      rw [hi, Subgroup.card_bot, Fintype.card_fin, hF'] at h1
      have : 2 ≤ 2 ^ n' := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn'
      have : 2 ≤ (2 ^ n') ^ 3 := this.trans (Nat.le_self_pow (by norm_num) _)
      omega
    rcases hirr (I 0) (fun g w hw => (hreal 0).2.2.2.1 ⟨ρ g, mem_range_apply ρ g⟩ w hw) with
      h0 | h0
    · exact hne 0 h0
    · apply hne 1
      rw [← h01, h0, top_inf_eq]
  ·
    rw [SmithC27.card_of_isHat_alt6 hHat] at hcard
    exact (card_SL3_ne_eight_mul hn hco (by decide : Odd 135) (by norm_num)
      (by rw [hcard]; norm_num)).elim
  ·
    exfalso
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    have hK : Nat.card ρ.range = Nat.card (StatedSp 2 F'') := (Nat.card_congr e.toEquiv).symm
    rw [hK, SmithC27.card_statedSp_two', hF''] at hcard
    exact card_sl3_ne_card_sp4 hn' hc13 (by rw [← hcard]; ring)
  ·
    exfalso
    let e := FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ
    have hK : Nat.card ρ.range = 360 := by
      rw [← Nat.card_congr e.toEquiv]
      exact CFSG.QuasithinUnique.Setup.X3.card_alt6
    rw [hK] at hcard
    exact card_SL3_ne_eight_mul hn hco (by decide : Odd 45) (by norm_num)
      (by rw [hcard]; norm_num)
  ·
    exfalso
    have : CharP F'' 2 := FFC.charP_two_of_card_pow hF''
    let e := FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ
    have hK : Nat.card ρ.range = Nat.card (CFSG.Open.quasithinG2 F'') :=
      (Nat.card_congr e.toEquiv).symm
    rw [hK, SmithC27.card_quasithinG2' hF'', hF''] at hcard
    exact card_SL3_ne_card_G2 hn (by omega) hc13 hcard
  · exact absurd rfl hne

end Main

end CFSG.Quasithin.MS93.S46
