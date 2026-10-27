module

public import CFSG.RankThree.PartTwo.Sec4.T444.Gap452Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4.ResidualGen

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.OddKernel Module
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec4.Residual452

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure ResidualData (T : Type) [Group T] [Finite T] : Prop where
  simple : IsSimpleGroup T
  nonabelian : ∃ a b : T, a * b ≠ b * a
  big : 5040 < Nat.card T
  e16 : ∃ E : Subgroup T, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
    Nat.card E = 16
  e9 : ∃ E : Subgroup T, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
    Nat.card E = 9 ∧
    (∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (E : Set T), n * x * n⁻¹ = y) ∧
    ∃ s : T, s * s = 1 ∧ ∀ x ∈ E, s * x * s⁻¹ = x⁻¹

structure IsSimpleCover {G T : Type*} [Group G] [Group T] (π : G →* T) : Prop where
  surjective : Function.Surjective π
  solvable : Group.IsSolvable π.ker

section Cover

variable {G : Type*} [Group G] [Group.IsPerfect G] {T : Type} [Group T] [IsSimpleGroup T]
  {π : G →* T}

theorem IsSimpleCover.eq_one_or_ker_le (hπ : IsSimpleCover π) {H : Type*} [Group H]
    (f : G →* H) : (∀ g, f g = 1) ∨ f.ker ≤ π.ker := by
  have : (f.ker.map π).Normal := (f.normal_ker).map π hπ.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map π) with h | h
  · right
    intro x hx
    have hx' : π x ∈ f.ker.map π := ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at hx'
  · left
    have := hπ.solvable
    let ψ : π.ker →* f.range := (f.comp π.ker.subtype).codRestrict f.range fun k => ⟨k, rfl⟩
    have hψ : Function.Surjective ψ := by
      rintro ⟨_, g, rfl⟩
      have hg : π g ∈ f.ker.map π := h ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨⟨k⁻¹ * g, ?_⟩, Subtype.ext ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
      · change f (k⁻¹ * g) = f g
        rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
    exact eq_one_of_isSolvable_range f (Group.isSolvable_of_surjective hψ)

theorem IsSimpleCover.eq_one_or_ker_le' (hπ : IsSimpleCover π) {M : Type*} [Monoid M]
    (f : G →* M) : (∀ g, f g = 1) ∨ ∀ g, f g = 1 → π g = 1 := by
  rcases hπ.eq_one_or_ker_le f.toHomUnits with h | h
  · exact Or.inl fun g => by simpa using congrArg Units.val (h g)
  · refine Or.inr fun g hg => h (MonoidHom.mem_ker.mpr (Units.ext ?_))
    rw [MonoidHom.coe_toHomUnits, hg, Units.val_one]

theorem IsSimpleCover.eq_one_of_card_lt [Finite G] [Finite T] (hπ : IsSimpleCover π)
    {H : Type*} [Group H] [Finite H] (f : G →* H) (hH : Nat.card H < Nat.card T) (g : G) :
    f g = 1 := by
  rcases hπ.eq_one_or_ker_le f with h | h
  · exact h g
  · exfalso
    let π' : G ⧸ f.ker →* T := QuotientGroup.lift f.ker π h
    have hπ' : Function.Surjective π' := by
      intro y
      obtain ⟨x, rfl⟩ := hπ.surjective y
      exact ⟨x, rfl⟩
    have h1 : Nat.card T ≤ Nat.card (G ⧸ f.ker) := Nat.card_le_card_of_surjective _ hπ'
    have h2 : Nat.card (G ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.range ≤ Nat.card H := Subgroup.card_le_card_group _
    omega

theorem IsSimpleCover.le_center_of_card_le [Finite G] [Finite T] (hπ : IsSimpleCover π)
    (hT : 5040 < Nat.card T) (R : Subgroup G) [R.Normal] (hR : Nat.card R ≤ 8) :
    R ≤ Subgroup.center G := by
  have hcard : Nat.card (MulAut R) < Nat.card T :=
    calc Nat.card (MulAut R) ≤ (Nat.card R - 1).factorial := card_mulAut_le
      _ ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
      _ = 5040 := by decide
      _ < Nat.card T := hT
  intro r hr
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun σ : MulAut R => ((σ ⟨r, hr⟩ : R) : G))
    (hπ.eq_one_of_card_lt (MulAut.conjNormal (H := R)) hcard g)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc g * r = g * r * g⁻¹ * g := by group
    _ = r * g := by rw [h1]

theorem IsSimpleCover.rep_eq_one_of_finrank_le_two [Finite G]
    [Finite T] (hπ : IsSimpleCover π)
    (hE9 : ∃ E : Subgroup T, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9) {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
    [FiniteDimensional (ZMod p) U] (hU : finrank (ZMod p) U ≤ 2)
    (ρ : G →* Module.End (ZMod p) U) (g : G) : ρ g = 1 := by
  classical
  rcases Nat.lt_or_ge (finrank (ZMod p) U) 2 with h1 | h2
  · exact map_eq_one_of_commute ρ (fun a b => commute_of_finrank_le_one (by omega) _ _) g
  have h2' : finrank (ZMod p) U = 2 := le_antisymm hU h2
  rcases hπ.eq_one_or_ker_le' ρ with h | hker
  · exact h g
  exfalso
  let bs := Module.finBasisOfFinrankEq (ZMod p) U h2'
  have hdet : ∀ x, LinearMap.det (ρ x) = 1 := fun x =>
    map_eq_one_of_commute ((LinearMap.det : Module.End (ZMod p) U →* ZMod p).comp ρ)
      (fun _ _ => mul_comm _ _) x
  let ψ : G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    { toFun := fun x => ⟨LinearMap.toMatrix bs bs (ρ x), by rw [LinearMap.det_toMatrix, hdet]⟩
      map_one' := Subtype.ext (by
        change LinearMap.toMatrix bs bs (ρ 1) = 1
        rw [map_one, LinearMap.toMatrix_one])
      map_mul' := fun x y => Subtype.ext (by
        change LinearMap.toMatrix bs bs (ρ (x * y)) =
          LinearMap.toMatrix bs bs (ρ x) * LinearMap.toMatrix bs bs (ρ y)
        rw [map_mul, LinearMap.toMatrix_mul]) }
  have hψker : ψ.ker ≤ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    apply hker
    have hx' : LinearMap.toMatrix bs bs (ρ x) = 1 := congrArg Subtype.val hx
    apply (LinearMap.toMatrix bs bs).injective
    rw [hx', LinearMap.toMatrix_one]
  let F : ψ.range →* T := (QuotientGroup.lift ψ.ker π hψker).comp
    (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := hπ.surjective y
    refine ⟨⟨ψ x, x, rfl⟩, ?_⟩
    have : (QuotientGroup.quotientKerEquivRange ψ).symm ⟨ψ x, x, rfl⟩ = (x : G ⧸ ψ.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    change QuotientGroup.lift ψ.ker π hψker
      ((QuotientGroup.quotientKerEquivRange ψ).symm ⟨ψ x, x, rfl⟩) = π x
    rw [this, QuotientGroup.lift_mk]
  obtain ⟨E, hEexp, hEcard⟩ := hE9
  exact false_of_surjective_of_isCyclic_sylow F hF (isCyclic_sylow_three_of_le_SL2 hp5 ψ.range)
    hEexp hEcard

theorem exists_sylow_comap_map_eq {H K : Type*} [Group H] [Group K] [Finite H] {q : ℕ}
    [Fact q.Prime] {f : H →* K} (hf : Function.Surjective f) {E : Subgroup K}
    (hE : IsPGroup q E) :
    ∃ P : Sylow q (E.comap f), ((P : Subgroup (E.comap f)).map (E.comap f).subtype).map f = E := by
  set W := E.comap f with hW
  let ψ : W →* E := (f.comp W.subtype).codRestrict E fun w => w.2
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨x, hx⟩ := hf e
    exact ⟨⟨x, show f x ∈ E by rw [hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow q W) := inferInstance
  have htop : ((T.mapSurjective hψ : Sylow q E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hE.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨T, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2
  · intro e he
    have : (⟨e, he⟩ : E) ∈ (T : Subgroup W).map ψ := htop ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwe⟩ := this
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwe⟩

theorem exists_mul_conj_mem_sylow {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {W : Subgroup H} (T : Sylow p W) (h : H) (hh : ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hh' : ∀ w ∈ W, h⁻¹ * w * h ∈ W) :
    ∃ w ∈ W, ∀ x ∈ (T : Subgroup W).map W.subtype, w * h * x * (w * h)⁻¹ ∈
      (T : Subgroup W).map W.subtype := by
  let φ : W →* W :=
    { toFun := fun w => ⟨h * w * h⁻¹, hh w w.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hφ : Function.Surjective φ := fun w =>
    ⟨⟨h⁻¹ * w * h, hh' w w.2⟩, Subtype.ext (by
      change h * (h⁻¹ * (w : H) * h) * h⁻¹ = w
      group)⟩
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq W (T.mapSurjective hφ) T
  refine ⟨w, w.2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have h1 : MulAut.conj w (φ t) ∈ ((w • (T.mapSurjective hφ) : Sylow p W) : Subgroup W) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨φ t, ?_, rfl⟩
    rw [Sylow.coe_mapSurjective]
    exact ⟨t, ht, rfl⟩
  rw [hw] at h1
  refine ⟨_, h1, ?_⟩
  change ((w * φ t * w⁻¹ : W) : H) = _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  change (w : H) * (h * (t : H) * h⁻¹) * (w : H)⁻¹ = w * h * (t : H) * (w * h)⁻¹
  group

theorem IsSimpleCover.false_of_rep [Finite G] [Finite T]
    (hπ : IsSimpleCover π) (hT : ResidualData T) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h3c : ∀ c : G, π c = 1 → (∃ k : ℕ, c ^ 3 ^ k = 1) → c ∈ Subgroup.center G)
    {U : Type*} [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]
    (hU0 : 0 < finrank (ZMod p) U) (hU4 : finrank (ZMod p) U ≤ 4)
    (ρ : G →* Module.End (ZMod p) U) {z : G} (hz : ρ z = -1) : False := by
  classical
  obtain ⟨E, hEc, hE3, hE9, htrans, s, hss, hsinv⟩ := hT.e9
  have hE9exp : ∃ E : Subgroup T, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 :=
    ⟨E, Monoid.exponent_dvd_of_forall_pow_eq_one (fun x : E => Subtype.ext (hE3 x x.2)), hE9⟩
  have hcast : ∀ n : ℕ, n < p → 0 < n → ((n : ℕ) : ZMod p) ≠ 0 := by
    intro n hn hn0 h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hn0 h) (by omega)
  have h2p : (2 : ZMod p) ≠ 0 := by exact_mod_cast hcast 2 (by omega) (by norm_num)
  have h3p : (3 : ZMod p) ≠ 0 := by exact_mod_cast hcast 3 (by omega) (by norm_num)
  have hm1 : (-1 : ZMod p) ≠ 1 := fun h => h2p (by linear_combination -h)
  have hz1 : ρ z ≠ 1 := hz ▸ neg_one_ne_one_end h2p hU0
  have hker : ∀ g, ρ g = 1 → π g = 1 :=
    (hπ.eq_one_or_ker_le' ρ).resolve_left fun h => hz1 (h z)
  have h4 : finrank (ZMod p) U = 4 := by
    obtain ⟨r, hr⟩ := even_finrank_of_eq_neg_one hm1 ρ hz
    by_contra h4
    exact hz1 (hπ.rep_eq_one_of_finrank_le_two hE9exp hp5 (by omega) ρ z)
  have h3triv : ∀ c : G, π c = 1 → (∃ k : ℕ, c ^ 3 ^ k = 1) → ρ c = 1 := by
    rintro c hc ⟨k, hk⟩
    by_contra hne
    have hord : orderOf (ρ c) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, pow_zero, orderOf_eq_one_iff] at hj
        exact absurd hj hne
      · exact h0
    set c' := c ^ 3 ^ (j - 1) with hc'
    have hc'3 : ρ c' ^ 3 = 1 := by
      rw [hc', map_pow, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hj1, ← hj,
        pow_orderOf_eq_one]
    have hc'1 : ρ c' ≠ 1 := by
      intro h
      rw [hc', map_pow] at h
      have h' := orderOf_dvd_of_pow_eq_one h
      rw [hj] at h'
      have h1 := Nat.le_of_dvd (by positivity) h'
      have h2 : 3 ^ (j - 1) < 3 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hc'c : c' ∈ Subgroup.center G := h3c c' (by rw [hc', map_pow, hc, one_pow])
      ⟨k, by rw [hc', ← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
    have hcomm : ∀ g, ρ c' * ρ g = ρ g * ρ c' := fun g => by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc'c g)]
    have hinv1 : ∀ g, ∀ v ∈ fixSpace (ρ c'), ρ g v ∈ fixSpace (ρ c') := fun g =>
      fixSpace_invariant fun v => by rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply]
    let ρ1 := restrictRep ρ (fixSpace (ρ c')) hinv1
    have hz1' : ρ1 z = -1 := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      rw [restrictRep_apply, hz]
      rfl
    have hlt1 : finrank (ZMod p) (fixSpace (ρ c')) < 4 := by
      have hne' : fixSpace (ρ c') ≠ ⊤ := by
        intro htop
        apply hc'1
        apply LinearMap.ext
        intro v
        have hv : v ∈ fixSpace (ρ c') := htop ▸ Submodule.mem_top
        rw [mem_fixSpace.mp hv, Module.End.one_apply]
      have := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne')
      rwa [finrank_top, h4] at this
    obtain ⟨r, hr⟩ := even_finrank_of_eq_neg_one hm1 ρ1 hz1'
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have hbot : fixSpace (ρ c') = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      have h3d := three_dvd_finrank_of_central_fpf (by omega) ρ c' hcomm hc'3 hbot
      rw [h4] at h3d
      norm_num at h3d
    · have h1 := hπ.rep_eq_one_of_finrank_le_two hE9exp hp5 (by omega) ρ1 z
      rw [hz1'] at h1
      exact neg_one_ne_one_end h2p (by omega) h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3p : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨P, hPp, hPE, P3, hP3⟩ : ∃ P : Subgroup G, IsPGroup 3 P ∧ P.map π = E ∧
      ∃ P3 : Sylow 3 (E.comap π), (P3 : Subgroup (E.comap π)).map (E.comap π).subtype = P := by
    obtain ⟨P3, hP3E⟩ := exists_sylow_comap_map_eq hπ.surjective hE3p
    exact ⟨_, P3.isPGroup'.map _, hP3E, P3, rfl⟩
  have hπP : ∀ x ∈ P, π x ∈ E := fun x hx => hPE ▸ Subgroup.mem_map_of_mem π hx
  have hρeq : ∀ x y : G, x * y⁻¹ ∈ P → π x = π y → ρ x = ρ y := by
    intro x y hxy hxy'
    have h1 : ρ (x * y⁻¹) = 1 := by
      refine h3triv _ (by rw [map_mul, map_inv, hxy', mul_inv_cancel]) ?_
      obtain ⟨k, hk'⟩ := hPp ⟨_, hxy⟩
      exact ⟨k, congrArg Subtype.val hk'⟩
    calc ρ x = ρ (x * y⁻¹ * y) := by rw [inv_mul_cancel_right]
      _ = ρ (x * y⁻¹) * ρ y := map_mul _ _ _
      _ = ρ y := by rw [h1, one_mul]
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx)
    rw [hbot, Subgroup.card_bot] at hE9
    norm_num at hE9
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 a haE) ha1
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle : E ≤ Subgroup.zpowers a := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hab1 : a * b ≠ 1 := fun h => hba (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
  have habb1 : a * b * b ≠ 1 := fun h => hba (by
    have hbb : b * b = a⁻¹ := by
      rw [mul_assoc] at h
      exact eq_inv_of_mul_eq_one_right h
    have : b = a⁻¹ * a⁻¹ := by
      calc b = b ^ 3 * b := by rw [hE3 b hbE, one_mul]
        _ = (b * b) * (b * b) := by rw [pow_succ, sq, mul_assoc (b * b) b b]
        _ = a⁻¹ * a⁻¹ := by rw [hbb]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)))
  obtain ⟨a', haP, rfl⟩ : a ∈ P.map π := hPE.symm ▸ haE
  obtain ⟨b', hbP, rfl⟩ : b ∈ P.map π := hPE.symm ▸ hbE
  set A := ρ a' with hA
  set B := ρ b' with hB
  have hAB : A * B = B * A := by
    rw [hA, hB, ← map_mul, ← map_mul]
    refine hρeq _ _ ?_ ?_
    · exact P.mul_mem (P.mul_mem haP hbP) (P.inv_mem (P.mul_mem hbP haP))
    · rw [map_mul, map_mul]
      exact hEc _ (hπP a' haP) _ (hπP b' hbP)
  have hpow3 : ∀ x ∈ P, ρ x ^ 3 = 1 := by
    intro x hx
    rw [← map_pow, ← map_one ρ]
    refine hρeq _ _ (by rw [inv_one, mul_one]; exact P.pow_mem hx 3) ?_
    rw [map_pow, map_one]
    exact hE3 _ (hπP x hx)
  have hA1 : fixSpace A ≠ ⊤ := by
    intro htop
    apply ha1
    apply hker
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixSpace A := htop ▸ Submodule.mem_top
    rw [mem_fixSpace.mp hv, Module.End.one_apply]
  have hlift : ∀ n ∈ Subgroup.normalizer (E : Set T), ∃ g : G,
      (∀ x ∈ P, g * x * g⁻¹ ∈ P) ∧ ∃ e ∈ E, π g = e * n := by
    intro n hn
    obtain ⟨h, rfl⟩ := hπ.surjective n
    have hh : ∀ w ∈ E.comap π, h * w * h⁻¹ ∈ E.comap π := fun w hw => by
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp hw
    have hh' : ∀ w ∈ E.comap π, h⁻¹ * w * h ∈ E.comap π := fun w hw => by
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      rw [Subgroup.mem_normalizer_iff.mp hn ((π h)⁻¹ * π w * π h)]
      have : π h * ((π h)⁻¹ * π w * π h) * (π h)⁻¹ = π w := by group
      rw [this]
      exact hw
    obtain ⟨w, hwW, hwN⟩ := exists_mul_conj_mem_sylow P3 h hh hh'
    rw [hP3] at hwN
    exact ⟨w * h, hwN, π w, hwW, map_mul _ _ _⟩
  have hfix : ∀ y' ∈ P, π y' ≠ 1 →
      finrank (ZMod p) (fixSpace (ρ y')) = finrank (ZMod p) (fixSpace A) := by
    intro y' hyP hy1
    obtain ⟨n, hnN, hn⟩ := htrans (π a') (hπP a' haP) ha1 (π y') (hπP y' hyP) hy1
    obtain ⟨g, hgN, e, heE, hge⟩ := hlift n hnN
    have hρ : ρ (g * a' * g⁻¹) = ρ y' := by
      refine hρeq _ _ (P.mul_mem (hgN a' haP) (P.inv_mem hyP)) ?_
      rw [map_mul, map_mul, map_inv, hge]
      calc e * n * π a' * (e * n)⁻¹ = e * (n * π a' * n⁻¹) * e⁻¹ := by group
        _ = e * π y' * e⁻¹ := by rw [hn]
        _ = π y' := by rw [hEc e heE _ (hπP y' hyP), mul_inv_cancel_right]
    rw [← hρ, map_mul, map_mul]
    exact finrank_fixSpace_conj A (ρ g) (ρ g⁻¹) (by rw [← map_mul, inv_mul_cancel, map_one])
      (by rw [← map_mul, mul_inv_cancel, map_one])
  have hsN : s ∈ Subgroup.normalizer (E : Set T) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hsinv x hx]
      exact E.inv_mem hx
    · intro hx
      have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
      have hx' : x = s * (s * x * s⁻¹) * s⁻¹ := by
        rw [hsi]
        calc x = (s * s) * x * (s * s) := by rw [hss, one_mul, mul_one]
          _ = s * (s * x * s) * s := by group
      rw [hx', hsinv _ hx]
      exact E.inv_mem hx
  obtain ⟨gs, hgsN, es, hesE, hgs⟩ := hlift s hsN
  have hS : ∀ x ∈ P, ρ gs * ρ x = ρ x * ρ x * ρ gs := by
    intro x hx
    have hπx : π x ∈ E := hπP x hx
    have hinvx : (π x)⁻¹ = π x * π x := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_two, ← pow_succ, hE3 _ hπx]
    have hconj' : ρ (gs * x * gs⁻¹) = ρ (x * x) := by
      refine hρeq _ _ (P.mul_mem (hgsN x hx) (P.inv_mem (P.mul_mem hx hx))) ?_
      rw [map_mul, map_mul, map_inv, hgs, map_mul, ← hinvx]
      calc es * s * π x * (es * s)⁻¹ = es * (s * π x * s⁻¹) * es⁻¹ := by group
        _ = es * (π x)⁻¹ * es⁻¹ := by rw [hsinv _ hπx]
        _ = (π x)⁻¹ := by
          rw [hEc es hesE _ (E.inv_mem hπx), mul_inv_cancel_right]
    calc ρ gs * ρ x = ρ (gs * x * gs⁻¹) * ρ gs := by
          rw [map_mul, map_mul, mul_assoc (ρ gs * ρ x), ← map_mul ρ gs⁻¹ gs, inv_mul_cancel,
            map_one, mul_one]
      _ = ρ (x * x) * ρ gs := by rw [hconj']
      _ = ρ x * ρ x * ρ gs := by rw [map_mul]
  exact false_of_nine_dim_four h3p h4 A B (ρ gs) (ρ gs⁻¹) hAB (hpow3 a' haP) (hpow3 b' hbP)
    (by rw [← map_mul, inv_mul_cancel, map_one]) (hS a' haP) (hS b' hbP) (hfix b' hbP hb1)
    (by rw [hA, hB, ← map_mul]; exact hfix _ (P.mul_mem haP hbP) (by rwa [map_mul]))
    (by
      rw [hA, hB, ← map_mul, ← map_mul]
      exact hfix _ (P.mul_mem (P.mul_mem haP hbP) hbP) (by rwa [map_mul, map_mul]))
    hA1

end Cover

theorem center_eq_bot_of_simple_nonabelian {T : Type*} [Group T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center T := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem le_center_of_isPGroup {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] {T : Type} [Group T] [Finite T] (hT : ResidualData T) {π : X →* T}
    (hπ : IsSimpleCover π) (h9 : ¬ 9 ∣ Nat.card π.ker)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p X ≤ 2)
    (R : Subgroup X) [R.Normal] (hR : IsPGroup p R) : R ≤ Subgroup.center X := by
  classical
  haveI : IsSimpleGroup T := hT.simple
  have hcenterT : Subgroup.center T = ⊥ := center_eq_bot_of_simple_nonabelian hT.nonabelian
  have hlayerT : CFSG.layer T = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit) (S := fun _ => T)
      (fun _ => hT.nonabelian) (MulEquiv.funUnique Unit T).symm
  have hE9exp : ∃ E : Subgroup T, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
    obtain ⟨E, -, hE3, hE9, -⟩ := hT.e9
    exact ⟨E, Monoid.exponent_dvd_of_forall_pow_eq_one (fun x : E => Subtype.ext (hE3 x x.2)),
      hE9⟩
  by_contra hRZ
  have hcomm : ⁅(⊤ : Subgroup X), R⁆ ≠ ⊥ := by
    intro h
    apply hRZ
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hx
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hR1 : R ≠ ⊥ := fun h => hRZ (h ▸ bot_le)
  obtain ⟨D, hDc, -, hDexp, -, -, hclass, hrange, -, hdet, hfixD⟩ :=
    odd_prime_kernel_critical_involution_fixed_spaces (by omega) R hR hR1 hcomm hloc
  set α := (SectionRank.Ccomm.frattiniAction D).comp (MulAut.conjNormal (H := R)) with hα
  have hDp : IsPGroup p D := hR.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := SectionRank.Ccomm.frattini_quotient_elementary hDp
  have hWp : IsPGroup p (D ⧸ frattini D) := fun x => ⟨1, by rw [pow_one, hWpow]⟩
  obtain ⟨n, hn⟩ := hWp.exists_card_eq
  obtain ⟨e⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hWcomm hWpow hn
  let φ : X →* Module.End (ZMod p) (Fin n → ZMod p) :=
    { toFun := fun x => coordLin e (α x)
      map_one' := by rw [map_one, coordLin_one]; rfl
      map_mul' := fun x y => by rw [map_mul, coordLin_mul]; rfl }
  have hφ : ∀ x, φ x = coordLin e (α x) := fun _ => rfl
  have hφα : ∀ x, φ x = 1 → α x = 1 := fun x h =>
    coordLin_injective e (by rw [← hφ, h, coordLin_one]; rfl)
  have hfixdim : ∀ t : X, orderOf t = 2 → finrank (ZMod p) (fixSpace (φ t)) ≤ 2 := by
    intro t ht
    have h := (hfixD t ht).2
    rw [card_fixed_eq_pow e] at h
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h
  by_cases hcase : ∃ t : X, orderOf t = 2 ∧ α t = 1
  ·
    obtain ⟨t, ht, hαt⟩ := hcase
    have hn2 : n ≤ 2 := by
      have h := hfixdim t ht
      have htop : fixSpace (φ t) = ⊤ := by
        rw [eq_top_iff]
        intro v _
        rw [mem_fixSpace, hφ, hαt, coordLin_one, LinearMap.id_apply]
      rwa [htop, finrank_top, Module.finrank_fin_fun] at h
    apply hrange
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_bot]
    exact hφα x (hπ.rep_eq_one_of_finrank_le_two hE9exp hp5
      (by rwa [Module.finrank_fin_fun]) φ x)
  push Not at hcase
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)
  obtain ⟨Y, -, hYmin⟩ := Finite.exists_le_minimal (p := fun Y : Subgroup X => Y.map π = ⊤)
    (show (⊤ : Subgroup X).map π = ⊤ from Subgroup.map_top_of_surjective π hπ.surjective)
  have hYS : Y.map π = ⊤ := hYmin.prop
  have hYmin' : ∀ U < Y, U.map π ≠ ⊤ := fun U hUY hU => hUY.not_ge (hYmin.2 hU hUY.le)
  obtain ⟨hYp, hCnil, hsyl⟩ := minimal_cover_facts hlayerT π Y hYS hYmin'
  have := hYp
  set πY : Y →* T := π.comp Y.subtype with hπYdef
  set C : Subgroup Y := (Subgroup.center T).comap πY with hCdef
  have hCmem : ∀ c : Y, c ∈ C ↔ πY c = 1 := fun c => by
    rw [hCdef, Subgroup.mem_comap, hcenterT, Subgroup.mem_bot]
  have hπYs : Function.Surjective πY := by
    intro y
    have hy : y ∈ Y.map π := hYS ▸ Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hCker : C = πY.ker := by
    ext c
    rw [hCmem, MonoidHom.mem_ker]
  have hπY : IsSimpleCover πY := ⟨hπYs, by rw [← hCker]; have := hCnil; infer_instance⟩
  have hCdvd : Nat.card C ∣ Nat.card π.ker := by
    have hle : C.map Y.subtype ≤ π.ker := by
      rintro _ ⟨c, hc, rfl⟩
      exact (hCmem c).mp hc
    rw [Nat.card_congr (C.equivMapOfInjective Y.subtype Y.subtype_injective).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  have hfaith : ∀ a : X, a ^ 2 = 1 → (∀ d ∈ D, a * ((d : R) : X) * a⁻¹ = d) → a = 1 := by
    intro a ha2 hcent
    by_contra ha1
    exact hcase a (orderOf_eq_prime ha2 ha1) (frattiniAction_conjNormal_eq_one hcent)
  have hE16 : ∀ A : Subgroup X, (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 2 = 1) →
      Nat.card A = 16 → False := fun A hAc hA2 hA16 =>
    false_of_elementary_sixteen (by omega) hR hDexp hclass (fun t ht => (hfixD t ht).1) A hAc
      hA2 hA16 fun a ha hcent => hfaith a (hA2 a ha) hcent
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E16, hE16c, hE16sq, hE16card⟩ := hT.e16
  have hE16p : IsPGroup 2 E16 := IsPGroup.of_card (n := 4) (by rw [hE16card]; norm_num)
  obtain ⟨P, hP2, hPE⟩ := exists_isPGroup_map_eq hπYs hE16p
  by_cases hCodd : Odd (Nat.card C)
  ·
    have hPC : ∀ x ∈ P, πY x = 1 → x = 1 := by
      intro x hx hx1
      have hxC : x ∈ C := (hCmem x).mpr hx1
      obtain ⟨k, hk⟩ := hP2 ⟨x, hx⟩
      have h1 : orderOf x ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have h2 : orderOf x ∣ Nat.card C := by
        rw [← Subgroup.orderOf_mk x hxC]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (2 ^ k) (Nat.card C) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hCodd)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    have hinj : Function.Injective (πY.comp P.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hPC x x.2 hx)
    obtain ⟨hPc, hPsq, hPcard⟩ := props_of_injective_map πY hinj hPE hE16c hE16sq
    refine hE16 (P.map Y.subtype) ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hPc x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hPsq x hx)
    · rw [← hE16card, ← hPcard]
      exact Nat.card_congr (P.equivMapOfInjective Y.subtype Y.subtype_injective).toEquiv.symm
  have hCeven : 2 ∣ Nat.card C := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hCodd)
  obtain ⟨S2⟩ : Nonempty (Sylow 2 C) := inferInstance
  set S : Subgroup Y := (S2 : Subgroup C).map C.subtype with hSdef
  have hSn : S.Normal := hsyl 2 S2
  have hS2 : IsPGroup 2 S := S2.isPGroup'.map _
  have hS1 : S ≠ ⊥ := by
    rw [hSdef, Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact S2.ne_bot_of_dvd_card hCeven
  set Z : Subgroup Y := S ⊓ Subgroup.centralizer (S : Set Y) with hZdef
  have hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
  let Ω : Subgroup Y :=
    { carrier := {x | x ∈ Z ∧ x ^ 2 = 1}
      mul_mem' := fun {x y} hx hy => ⟨Z.mul_mem hx.1 hy.1, by
        rw [(show Commute x y from hZc x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨Z.one_mem, one_pow 2⟩
      inv_mem' := fun {x} hx => ⟨Z.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hΩmem : ∀ x, x ∈ Ω ↔ x ∈ Z ∧ x ^ 2 = 1 := fun x => Iff.rfl
  have hZn : Z.Normal := inferInstance
  have hΩn : Ω.Normal := ⟨fun x hx g => (hΩmem _).mpr ⟨hZn.conj_mem x ((hΩmem x).mp hx).1 g, by
    rw [conj_pow, ((hΩmem x).mp hx).2, mul_one, mul_inv_cancel]⟩⟩
  have hΩ8 : Nat.card Ω ≤ 8 := by
    have hΩ2 : IsPGroup 2 Ω := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow]
      exact ((hΩmem _).mp x.2).2)⟩
    obtain ⟨m, hm⟩ := hΩ2.exists_card_eq
    by_contra h8
    have hm4 : 4 ≤ m := by
      by_contra h
      have : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := Ω) 2 (n := 4)
      (by rw [hm]; exact pow_dvd_pow 2 hm4)
    refine hE16 ((Q.map Ω.subtype).map Y.subtype) ?_ ?_ ?_
    · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩ _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact congrArg Subtype.val (hZc _ ((hΩmem _).mp x.2).1 _ ((hΩmem _).mp y.2).1)
    · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact congrArg Subtype.val ((hΩmem _).mp x.2).2
    · rw [← Nat.card_congr ((Q.map Ω.subtype).equivMapOfInjective Y.subtype
        Y.subtype_injective).toEquiv, ← Nat.card_congr (Q.equivMapOfInjective Ω.subtype
        Ω.subtype_injective).toEquiv, hQ]
      norm_num
  have hΩZ := hπY.le_center_of_card_le hT.big Ω hΩ8
  obtain ⟨z, hzΩ, hz2⟩ : ∃ z ∈ Ω, orderOf z = 2 := by
    have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
    have hZS : Nontrivial (Subgroup.center S) := hS2.center_nontrivial
    have h2c : 2 ∣ Nat.card (Subgroup.center S) := by
      rcases (hS2.to_subgroup (Subgroup.center S)).card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hZS).ne'
      · exact h
    obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 h2c
    have hz0' : orderOf ((z0 : S) : Y) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz0]
    refine ⟨((z0 : S) : Y), (hΩmem _).mpr ⟨Subgroup.mem_inf.mpr ⟨(z0 : S).2, ?_⟩, ?_⟩, hz0'⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z0.2 ⟨s, hs⟩)
    · rw [← hz0', pow_orderOf_eq_one]
  have hzc : z ∈ Subgroup.center Y := hΩZ hzΩ
  obtain ⟨t, ht2, htz⟩ : ∃ t : Y, orderOf t = 2 ∧ t ≠ z := by
    by_contra hnone
    push Not at hnone
    have hrank : DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions P := by
      intro t1 t2 _
      apply Subtype.ext
      apply Subtype.ext
      rw [hnone ((t1 : P) : Y) (by rw [Subgroup.orderOf_coe]; exact t1.2),
        hnone ((t2 : P) : Y) (by rw [Subgroup.orderOf_coe]; exact t2.2)]
    let f : P →* E16 := (πY.comp P.subtype).codRestrict E16
      (fun x => hPE ▸ Subgroup.mem_map_of_mem πY x.2)
    have hf : Function.Surjective f := by
      intro e
      have he : (e : T) ∈ P.map πY := hPE.symm ▸ e.2
      obtain ⟨x, hx, hxe⟩ := he
      exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
    have hE2 : ∀ x : E16, x ^ 2 = 1 := fun x => Subtype.ext (hE16sq x x.2)
    rcases DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hP2 hrank with
      hcyc | ⟨k, -, ⟨eQ⟩⟩
    · have : IsCyclic E16 := isCyclic_of_surjective f hf
      have hexp := IsCyclic.exponent_eq_card (α := E16)
      have hdvd : Monoid.exponent E16 ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hE2
      rw [hexp, hE16card] at hdvd
      norm_num at hdvd
    · have h4 := card_le_four_of_quaternion (by positivity) (f.comp eQ.toMonoidHom)
        (hf.comp eQ.surjective) hE2
      rw [hE16card] at h4
      norm_num at h4
  set zX : X := (z : X) with hzX
  set tX : X := (t : X) with htX
  have hzX2 : orderOf zX = 2 := by rw [hzX, Subgroup.orderOf_coe, hz2]
  have htX2 : orderOf tX = 2 := by rw [htX, Subgroup.orderOf_coe, ht2]
  have hcz : ∀ y : Y, (y : X) * zX = zX * (y : X) := fun y =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzc) y)
  have hzX1 : zX ^ 2 = 1 := by rw [← hzX2]; exact pow_orderOf_eq_one zX
  have htX1 : tX ^ 2 = 1 := by rw [← htX2]; exact pow_orderOf_eq_one tX
  have htzX : tX * zX ≠ 1 := by
    intro h
    apply htz
    apply Subtype.ext
    have hzinv : zX⁻¹ = zX := inv_eq_of_mul_eq_one_right (by rw [← sq, hzX1])
    change tX = zX
    rw [← hzinv]
    exact eq_inv_of_mul_eq_one_left h
  have htzX2 : orderOf (tX * zX) = 2 := by
    refine orderOf_eq_prime ?_ htzX
    rw [(show Commute tX zX from hcz t).mul_pow, htX1, hzX1, one_mul]
  have hinvol : ∀ x : X, orderOf x = 2 → ∀ w, φ x (φ x w) = w := by
    intro x hx w
    rw [← Module.End.mul_apply, ← map_mul, ← sq, ← hx, pow_orderOf_eq_one, map_one,
      Module.End.one_apply]
  have hcommφ : ∀ w, φ tX (φ zX w) = φ zX (φ tX w) := by
    intro w
    rw [← Module.End.mul_apply, ← map_mul, hcz t, map_mul, Module.End.mul_apply]
  have h4 := finrank_four_group h2p (φ tX) (φ zX) (hinvol tX htX2) (hinvol zX hzX2) hcommφ ⊤
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
  have hdec := finrank_eq_fix_add_neg h2p (φ zX) (hinvol zX hzX2) ⊤
    (fun _ _ => Submodule.mem_top)
  repeat rw [top_inf_eq] at h4
  repeat rw [top_inf_eq] at hdec
  rw [finrank_top] at hdec h4
  have hft := hfixdim tX htX2
  have hftz := hfixdim (tX * zX) htzX2
  rw [map_mul, Module.End.mul_eq_comp] at hftz
  obtain ⟨h4a, h4b, h4c, h4d⟩ := h4
  have hU4 : finrank (ZMod p) (negSpace (φ zX)) ≤ 4 := by omega
  have hU0 : 0 < finrank (ZMod p) (negSpace (φ zX)) := by
    by_contra h0
    have hfix : fixSpace (φ zX) = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    apply hcase zX hzX2
    apply hφα
    apply LinearMap.ext
    intro v
    rw [Module.End.one_apply]
    exact mem_fixSpace.mp (hfix ▸ Submodule.mem_top)
  have hinvU : ∀ y : Y, ∀ v ∈ negSpace (φ zX), (φ.comp Y.subtype) y v ∈ negSpace (φ zX) := by
    intro y v hv
    rw [mem_negSpace] at hv ⊢
    change φ zX (φ (y : X) v) = -φ (y : X) v
    rw [← Module.End.mul_apply, ← map_mul, ← hcz y, map_mul, Module.End.mul_apply, hv, map_neg]
  let ρ := restrictRep (φ.comp Y.subtype) (negSpace (φ zX)) hinvU
  have hρz : ρ z = -1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [restrictRep_apply, LinearMap.neg_apply, Module.End.one_apply, Submodule.coe_neg]
    exact mem_negSpace.mp v.2
  have h3c : ∀ c : Y, πY c = 1 → (∃ k : ℕ, c ^ 3 ^ k = 1) → c ∈ Subgroup.center Y := by
    rintro c hc ⟨k, hk⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Q3⟩ : Nonempty (Sylow 3 C) := inferInstance
    set T3 : Subgroup Y := (Q3 : Subgroup C).map C.subtype with hT3
    have hT3n : T3.Normal := hsyl 3 Q3
    have hcC : c ∈ C := (hCmem c).mpr hc
    have hQ3n : (Q3 : Subgroup C).Normal := by
      have h := hT3n.subgroupOf C
      have heq : T3.subgroupOf C = (Q3 : Subgroup C) := by
        rw [hT3, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      rwa [heq] at h
    have hcT : c ∈ T3 := by
      have hord : orderOf (⟨c, hcC⟩ : C) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow]; exact hk))
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
      have hzp : IsPGroup 3 (Subgroup.zpowers (⟨c, hcC⟩ : C)) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
      obtain ⟨S3, hS3⟩ := hzp.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q3 S3
      have hQS : S3 = Q3 := by rw [← hg]; exact Sylow.smul_eq_of_normal
      have hmem : (⟨c, hcC⟩ : C) ∈ (Q3 : Subgroup C) := hQS ▸ hS3 (Subgroup.mem_zpowers _)
      exact ⟨⟨c, hcC⟩, hmem, rfl⟩
    have hT3card : Nat.card T3 ≤ 3 := by
      have hdvd : Nat.card T3 ∣ Nat.card π.ker := by
        rw [hT3, Subgroup.card_map_of_injective C.subtype_injective]
        exact (Subgroup.card_subgroup_dvd_card _).trans hCdvd
      obtain ⟨m, hm⟩ := (Q3.isPGroup'.map C.subtype : IsPGroup 3 T3).exists_card_eq
      rw [hm] at hdvd ⊢
      by_contra h3
      have hm2 : 2 ≤ m := by
        by_contra h
        have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact h9 ((pow_dvd_pow 3 hm2).trans hdvd)
    exact hπY.le_center_of_card_le hT.big T3 (by omega) hcT
  exact hπY.false_of_rep hT hp5 h3c hU0 hU4 ρ hρz

theorem isQuasisimple_of_residualData {T : Type} [Group T]
    [Finite T] (hT : ResidualData T) {X : Type} [Group X] [Finite X]
    (hX : SectionFourHyp X) (hXp : Group.IsPerfect X) (hO2 : CFSG.pCore 2 X = ⊥)
    (K : Subgroup X) [K.Normal] (hK : Group.IsSolvable K) (h9 : ¬ 9 ∣ Nat.card K)
    (ψ : X ⧸ K ≃* T) : IsQuasisimple X := by
  classical
  haveI : IsSimpleGroup T := hT.simple
  have hcenterT : Subgroup.center T = ⊥ := center_eq_bot_of_simple_nonabelian hT.nonabelian
  let π : X →* T := ψ.toMonoidHom.comp (QuotientGroup.mk' K)
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨q, hq⟩ := ψ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    exact ⟨x, hq⟩
  have hπker : π.ker = K := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (x : X ⧸ K) = 1 ↔ x ∈ K
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hπ : IsSimpleCover π := ⟨hπs, by rw [hπker]; exact hK⟩
  have h9' : ¬ 9 ∣ Nat.card π.ker := by rw [hπker]; exact h9
  have hcore : ∀ (q : ℕ) [Fact q.Prime] (N : Subgroup X) [N.Normal], IsPGroup q N → N ≤ K →
      N ≤ Subgroup.center X := by
    intro q hq N _ hN hNK
    by_cases hq2 : q = 2
    · subst hq2
      have hle : N ≤ CFSG.pCore 2 X := le_sSup ⟨inferInstance, hN⟩
      rw [hO2, le_bot_iff] at hle
      rw [hle]
      exact bot_le
    by_cases hq3 : q = 3
    · subst hq3
      refine hπ.le_center_of_card_le hT.big N ?_
      obtain ⟨m, hm⟩ := hN.exists_card_eq
      have hdvd : Nat.card N ∣ Nat.card K := Subgroup.card_dvd_of_le hNK
      rw [hm] at hdvd ⊢
      by_contra h8
      have hm2 : 2 ≤ m := by
        by_contra h
        have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact h9 ((pow_dvd_pow 3 hm2).trans hdvd)
    have hq5 : 5 ≤ q := by
      have h2 := hq.out.two_le
      have h4 : q ≠ 4 := by
        rintro rfl
        exact absurd hq.out (by norm_num)
      omega
    exact le_center_of_isPGroup hT hπ h9' hq5
      (Nat.lt_succ_iff.mp (hX.localRank_lt q hq.out (by omega))) N hN
  have hpc : ∀ q : (Nat.card K).primeFactors.attach,
      (CFSG.pCore q.1.1 K).map K.subtype ≤ Subgroup.center X := fun q =>
    hcore q.1.1 _ (CFSG.pCore_isPGroup.map _) (Subgroup.map_subtype_le _)
  have hFX : (CFSG.fittingSubgroup K).map K.subtype ≤ Subgroup.center X := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    exact iSup_le hpc
  have hFc : CFSG.fittingSubgroup K ≤ Subgroup.center K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hFX ⟨x, hx, rfl⟩)) y)
  have htop : CFSG.fittingSubgroup K = ⊤ := by
    have hc : Subgroup.centralizer (CFSG.fittingSubgroup K : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_center_iff.mp (hFc hx) y).symm
    have h := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hK
    rw [hc] at h
    exact top_le_iff.mp h
  have hKZ : K ≤ Subgroup.center X := by
    intro x hx
    exact hFX ⟨⟨x, hx⟩, htop ▸ Subgroup.mem_top _, rfl⟩
  have hZK : Subgroup.center X = π.ker := by
    rw [hπker]
    refine le_antisymm ?_ hKZ
    intro x hx
    rw [← hπker, MonoidHom.mem_ker]
    have hxc : π x ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := hπs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx g]
    rwa [hcenterT, Subgroup.mem_bot] at hxc
  let e : X ⧸ Subgroup.center X ≃* T := (QuotientGroup.quotientMulEquivOfEq hZK).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπs)
  refine ⟨hXp, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hT.nonabelian
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end CFSG.RankThree.PartTwo.Sec4.ResidualGen
