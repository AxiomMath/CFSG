module

public import CFSG.Quasithin.Recognition.RuRank3RuAut
public import CFSG.Quasithin.Recognition.RuRank3Iface
public import CFSG.Sporadic.Schreier.RuIso

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open MulAction

theorem exists_equiv_of_orbits {F X Y ι : Type*} [Group F] [MulAction F X] [MulAction F Y]
    (x : ι → X) (y : ι → Y) (hX : ∀ z : X, ∃ i, z ∈ orbit F (x i))
    (hY : ∀ z : Y, ∃ i, z ∈ orbit F (y i))
    (hXd : ∀ i j, x j ∈ orbit F (x i) → i = j) (hYd : ∀ i j, y j ∈ orbit F (y i) → i = j)
    (hst : ∀ i (f : F), f • x i = x i ↔ f • y i = y i) :
    ∃ Φ : X ≃ Y, (∀ (f : F) (z : X), Φ (f • z) = f • Φ z) ∧ ∀ i, Φ (x i) = y i := by
  choose idx hidx using hX
  choose fz hfz' using hidx
  have hfz : ∀ z, fz z • x (idx z) = z := hfz'
  set φ : X → Y := fun z => fz z • y (idx z) with hφ
  have hkey : ∀ (f : F) i z, f • x i = z → φ z = f • y i := by
    intro f i z hz
    have e : fz z • x (idx z) = f • x i := (hfz z).trans hz.symm
    have hi : idx z = i := by
      apply hXd
      refine ⟨f⁻¹ * fz z, ?_⟩
      show (f⁻¹ * fz z) • x (idx z) = x i
      rw [mul_smul, e, inv_smul_smul]
    subst hi
    have hfix : (f⁻¹ * fz z) • x (idx z) = x (idx z) := by
      rw [mul_smul, e, inv_smul_smul]
    have := (hst (idx z) _).1 hfix
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this
  have hφeq : ∀ (f : F) (z : X), φ (f • z) = f • φ z := by
    intro f z
    rw [hkey (f * fz z) (idx z) (f • z) (by rw [mul_smul, hfz z]), mul_smul]
  have hφx : ∀ i, φ (x i) = y i := fun i => by rw [hkey 1 i (x i) (one_smul _ _), one_smul]
  have hinj : Function.Injective φ := by
    intro z z' hzz
    have e : fz z • y (idx z) = fz z' • y (idx z') := hzz
    have hi : idx z = idx z' := by
      apply hYd
      refine ⟨(fz z')⁻¹ * fz z, ?_⟩
      show ((fz z')⁻¹ * fz z) • y (idx z) = y (idx z')
      rw [mul_smul, e, inv_smul_smul]
    have e' := e
    rw [hi] at e'
    have hfix : ((fz z')⁻¹ * fz z) • y (idx z') = y (idx z') := by
      rw [mul_smul, e', inv_smul_smul]
    have := (hst (idx z') _).2 hfix
    rw [mul_smul, inv_smul_eq_iff] at this
    rw [← hfz z, ← hfz z', hi, this]
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨i, f, rfl⟩ := hY w
    exact ⟨f • x i, hkey f i _ rfl⟩
  exact ⟨Equiv.ofBijective φ ⟨hinj, hsurj⟩, hφeq, hφx⟩

theorem eq_of_mem_orbit_of_ncard {F X ι : Type*} [Group F] [MulAction F X] (v : ι → X)
    (nc : ι → ℕ) (hnc : Function.Injective nc) (hv : ∀ i, (orbit F (v i)).ncard = nc i) :
    ∀ i j, v j ∈ orbit F (v i) → i = j := by
  intro i j hj
  apply hnc
  rw [← hv i, ← hv j, orbit_eq_iff.2 hj]

section Abstract

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose] def orbAdj (G : Type*) {Ω : Type*} [Group G] [MulAction G Ω] (ω δ z y : Ω) : Prop :=
  ∃ g : G, g • ω = z ∧ g • δ = y

theorem orbAdj_smul (g : G) (ω δ z y : Ω) :
    orbAdj G ω δ (g • z) (g • y) ↔ orbAdj G ω δ z y := by
  constructor
  · rintro ⟨k, hk1, hk2⟩
    exact ⟨g⁻¹ * k, by rw [mul_smul, hk1, inv_smul_smul], by rw [mul_smul, hk2, inv_smul_smul]⟩
  · rintro ⟨k, rfl, rfl⟩
    exact ⟨g * k, mul_smul _ _ _, mul_smul _ _ _⟩

theorem orbAdj_base_iff (ω δ y : Ω) :
    orbAdj G ω δ ω y ↔ y ∈ orbit (stabilizer G ω) δ := by
  constructor
  · rintro ⟨k, hk1, rfl⟩
    exact ⟨⟨k, hk1⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, f.2, rfl⟩

theorem orbAdj_symm {ω δ : Ω} {h : G} (h1 : h • ω = δ) (h2 : h • δ = ω) {z y : Ω}
    (hzy : orbAdj G ω δ z y) : orbAdj G ω δ y z := by
  obtain ⟨k, rfl, rfl⟩ := hzy
  exact ⟨k * h, by rw [mul_smul, h1], by rw [mul_smul, h2]⟩

theorem card_stab_stab_smul (g : G) (a b : Ω) :
    Nat.card (stabilizer (stabilizer G (g • a)) (g • b)) =
      Nat.card (stabilizer (stabilizer G a) b) := by
  rw [← map_stabilizerConj_stabilizer]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (stabilizerConj g a).injective).toEquiv).symm

theorem card_stab_stab_comm (a b : Ω) :
    Nat.card (stabilizer (stabilizer G a) b) = Nat.card (stabilizer (stabilizer G b) a) :=
  Nat.card_congr
    { toFun := fun c => ⟨⟨c.1.1, c.2⟩, c.1.2⟩
      invFun := fun c => ⟨⟨c.1.1, c.2⟩, c.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem exists_smul_swap [IsPretransitive G Ω] {ω δ : Ω}
    (hδ : ∀ z : Ω, Nat.card (stabilizer (stabilizer G ω) z) =
      Nat.card (stabilizer (stabilizer G ω) δ) → z ∈ orbit (stabilizer G ω) δ) :
    ∃ h : G, h • ω = δ ∧ h • δ = ω := by
  obtain ⟨g, hg⟩ := exists_smul_eq G ω δ
  have hc : Nat.card (stabilizer (stabilizer G ω) (g⁻¹ • ω)) =
      Nat.card (stabilizer (stabilizer G ω) δ) := by
    rw [← card_stab_stab_smul g ω (g⁻¹ • ω), smul_inv_smul, hg, card_stab_stab_comm]
  obtain ⟨f, hf⟩ := hδ _ hc
  have hf' : (f : G) • δ = g⁻¹ • ω := hf
  have hfω : (f : G) • ω = ω := f.2
  refine ⟨g * f, ?_, ?_⟩
  · rw [mul_smul, hfω, hg]
  · rw [mul_smul, hf', smul_inv_smul]

end Abstract

theorem exists_not_mem_orbit_titsK0
    : ∃ j : Fin 1755, j ∉ orbit titsK0 (0 : Fin 1755) := by
  by_contra hcon
  have hall : ∀ j : Fin 1755, j ∈ orbit titsK0 (0 : Fin 1755) := fun j => by
    by_contra hj
    exact hcon ⟨j, hj⟩
  have e : orbit titsK0 (0 : Fin 1755) = Set.univ := Set.eq_univ_of_forall hall
  have h := ncard_orbit_titsK0_zero
  rw [e, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  norm_num at h

theorem exists_adj_ruB
    {s : Fin 4060} (hs : s ∈ ruS) : ∃ m ∈ Set.range ruB, ruAdj s m := by
  obtain ⟨j, hj⟩ := exists_not_mem_orbit_titsK0
  obtain ⟨p, hp, rfl⟩ := exists_ruR0_g0 hs
  refine ⟨p (ruB j), (ruR0_mem_range_ruB_iff hp _).2 ⟨j, rfl⟩, ?_⟩
  rw [ruAdj_apply (ruR0_le_ruP hp)]
  exact (ruAdj_g0_ruB_iff j).2 hj

theorem orbit_ruR0_zero : orbit ruR0 (0 : Fin 4060) = {0} := by
  ext z
  constructor
  · rintro ⟨r, rfl⟩
    exact ruR0_apply_zero r.2
  · rintro rfl
    exact mem_orbit_self _

theorem orbit_ruR0_of_mem_range
    {d : Fin 4060} (hd : d ∈ Set.range ruB) :
    orbit ruR0 d = Set.range ruB := by
  rw [← orbit_ruR0_one] at hd ⊢
  exact orbit_eq_iff.2 hd

theorem orbit_ruR0_of_mem_ruS
    {s : Fin 4060} (hs : s ∈ ruS) : orbit ruR0 s = ruS := by
  rw [← orbit_ruR0_g0] at hs ⊢
  exact orbit_eq_iff.2 hs

section Main

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem IsRudvalisRank3.exists_graph_equiv_of
    (h : IsRudvalisRank3 G Ω) (ω δ : Ω)
    (hδcard : Nat.card (stabilizer (stabilizer G ω) δ) = 2 ^ 12 * 5) :
    ∃ Φ : Ω ≃ Fin 4060, ∀ z y, orbAdj G ω δ z y ↔ ruAdj (Φ z) (Φ y) := by
  classical
  have htr := h.transitive
  obtain ⟨ψ⟩ := h.twoF4 ω
  obtain ⟨γ, hγ⟩ := h.l225 ω
  have hFcard : Nat.card (stabilizer G ω) = 35942400 := by
    rw [Nat.card_congr ψ.toEquiv, card_titsA]
  have hγcard : Nat.card (stabilizer (stabilizer G ω) γ) = 15600 := by
    obtain ⟨K, -, hK2, ⟨e⟩, -, -⟩ := id hγ
    have := K.card_mul_index
    rw [(psl225_witnesses e).1, hK2] at this
    rw [← this]
  have horb : ∀ z : Ω, (orbit (stabilizer G ω) z).ncard *
      Nat.card (stabilizer (stabilizer G ω) z) = 35942400 := by
    intro z
    rw [← index_stabilizer, mul_comm, Subgroup.card_mul_index, hFcard]
  have hωorb : orbit (stabilizer G ω) ω = {ω} := by
    ext z
    constructor
    · rintro ⟨f, rfl⟩
      exact f.2
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact mem_orbit_self ω
  have hn0 : (orbit (stabilizer G ω) ω).ncard = 1 := by rw [hωorb, Set.ncard_singleton]
  have hn1 : (orbit (stabilizer G ω) δ).ncard = 1755 := by
    have := horb δ
    rw [hδcard] at this
    omega
  have hn2 : (orbit (stabilizer G ω) γ).ncard = 2304 := by
    have := horb γ
    rw [hγcard] at this
    omega
  set x : Fin 3 → Ω := ![ω, δ, γ] with hx
  have hxn : ∀ i, (orbit (stabilizer G ω) (x i)).ncard = ![1, 1755, 2304] i := by
    intro i
    fin_cases i
    · exact hn0
    · exact hn1
    · exact hn2
  have hinjn : Function.Injective (![1, 1755, 2304] : Fin 3 → ℕ) := by decide
  have hXd := eq_of_mem_orbit_of_ncard x _ hinjn hxn
  have hX : ∀ z, ∃ i, z ∈ orbit (stabilizer G ω) (x i) := by
    intro z
    have hrank := h.rank_three ω
    have hfin : Finite (orbitRel.Quotient (stabilizer G ω) Ω) :=
      Nat.finite_of_card_ne_zero (by rw [hrank]; norm_num)
    let q : Fin 3 → orbitRel.Quotient (stabilizer G ω) Ω := fun i => Quotient.mk'' (x i)
    have hq : Function.Injective q := by
      intro i j hij
      have := Quotient.exact' hij
      rw [orbitRel_apply] at this
      exact (hXd j i this).symm
    have hbij := hq.bijective_of_nat_card_le
      (by rw [hrank, Nat.card_eq_fintype_card, Fintype.card_fin])
    obtain ⟨i, hi⟩ := hbij.2 (Quotient.mk'' z)
    refine ⟨i, ?_⟩
    have := Quotient.exact' hi
    rw [orbitRel_apply] at this
    exact mem_orbit_symm.1 this
  set θ : stabilizer G ω ≃* ruR0 := ψ.trans ruR0Equiv.symm with hθ
  have hθψ : ∀ f, ruR0Equiv (θ f) = ψ f := fun f => MulEquiv.apply_symm_apply _ _
  let _ : MulAction (stabilizer G ω) (Fin 4060) :=
    MulAction.compHom (Fin 4060) (ruR0.subtype.comp θ.toMonoidHom)
  have hsmul : ∀ (f : stabilizer G ω) (n : Fin 4060),
      f • n = ((θ f : ruR0) : Equiv.Perm (Fin 4060)) n := fun f n => rfl
  have horbθ : ∀ n : Fin 4060, orbit (stabilizer G ω) n = orbit ruR0 n := by
    intro n
    ext m
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨θ f, rfl⟩
    · rintro ⟨r, rfl⟩
      refine ⟨θ.symm r, ?_⟩
      show θ.symm r • n = r • n
      rw [hsmul, MulEquiv.apply_symm_apply]
      rfl
  obtain ⟨d, hdD, hd⟩ := exists_stab_eq_of_card (H := (stabilizer (stabilizer G ω) δ).map
    ψ.toMonoidHom) (by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ ψ.injective).toEquiv, hδcard]
      norm_num)
  have hγ' : IsL225Plus ((stabilizer (stabilizer G ω) γ).map ψ.toMonoidHom) :=
    hγ.of_mulEquiv (Subgroup.equivMapOfInjective _ _ ψ.injective)
  obtain ⟨s, hsS, hs⟩ := exists_stab_eq_of_isL225Plus hγ'
  have hst0 : ∀ f : stabilizer G ω, f • ω = ω ↔ f • (0 : Fin 4060) = 0 := by
    intro f
    rw [hsmul, ruR0_apply_zero (θ f).2]
    exact iff_of_true f.2 rfl
  have hst1 : ∀ f : stabilizer G ω, f • δ = δ ↔ f • d = d := by
    intro f
    rw [hsmul, ← hd (θ f), hθψ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
      mem_stabilizer_iff]
  have hst2 : ∀ f : stabilizer G ω, f • γ = γ ↔ f • s = s := by
    intro f
    rw [hsmul, ← hs (θ f), hθψ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
      mem_stabilizer_iff]
  set y : Fin 3 → Fin 4060 := ![0, d, s] with hy
  have hyn : ∀ i, (orbit (stabilizer G ω) (y i)).ncard = ![1, 1755, 2304] i := by
    intro i
    fin_cases i
    · show (orbit (stabilizer G ω) (0 : Fin 4060)).ncard = 1
      rw [horbθ, orbit_ruR0_zero, Set.ncard_singleton]
    · show (orbit (stabilizer G ω) d).ncard = 1755
      rw [horbθ, orbit_ruR0_of_mem_range hdD, Set.ncard_range_of_injective ruB_injective,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    · show (orbit (stabilizer G ω) s).ncard = 2304
      rw [horbθ, orbit_ruR0_of_mem_ruS hsS, ncard_ruS]
  have hYd := eq_of_mem_orbit_of_ncard y _ hinjn hyn
  have hY : ∀ n : Fin 4060, ∃ i, n ∈ orbit (stabilizer G ω) (y i) := by
    intro n
    by_cases h0 : n = 0
    · refine ⟨0, ?_⟩
      show n ∈ orbit (stabilizer G ω) (0 : Fin 4060)
      rw [horbθ, orbit_ruR0_zero, h0]
      rfl
    by_cases hD : n ∈ Set.range ruB
    · refine ⟨1, ?_⟩
      show n ∈ orbit (stabilizer G ω) d
      rw [horbθ, orbit_ruR0_of_mem_range hdD]
      exact hD
    · refine ⟨2, ?_⟩
      show n ∈ orbit (stabilizer G ω) s
      rw [horbθ, orbit_ruR0_of_mem_ruS hsS]
      exact ⟨h0, hD⟩
  have hst : ∀ i (f : stabilizer G ω), f • x i = x i ↔ f • y i = y i := by
    intro i
    fin_cases i
    · exact hst0
    · exact hst1
    · exact hst2
  obtain ⟨Φ, hΦeq, hΦx⟩ := exists_equiv_of_orbits x y hX hY hXd hYd hst
  have hΦω : Φ ω = 0 := hΦx 0
  have hΦδ : Φ δ = d := hΦx 1
  have hΦγ : Φ γ = s := hΦx 2
  have hfinΩ : Finite Ω := Finite.of_equiv _ Φ.symm
  have hω0 : Φ.symm 0 = ω := by rw [← hΦω, Equiv.symm_apply_apply]
  have hΦsymm : ∀ (f : stabilizer G ω) (n : Fin 4060), Φ.symm (f • n) = f • Φ.symm n := by
    intro f n
    apply Φ.injective
    rw [hΦeq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hΦorb : ∀ z w : Ω, Φ w ∈ orbit (stabilizer G ω) (Φ z) ↔ w ∈ orbit (stabilizer G ω) z := by
    intro z w
    constructor
    · rintro ⟨f, hf⟩
      have hf' : f • Φ z = Φ w := hf
      refine ⟨f, Φ.injective ?_⟩
      show Φ (f • z) = Φ w
      rw [hΦeq, hf']
    · rintro ⟨f, rfl⟩
      exact ⟨f, (hΦeq f z).symm⟩
  have hΦD : ∀ w, Φ w ∈ Set.range ruB ↔ w ∈ orbit (stabilizer G ω) δ := by
    intro w
    rw [← hΦorb, hΦδ, horbθ, orbit_ruR0_of_mem_range hdD]
  have hΦS : ∀ w, Φ w ∈ ruS ↔ w ∈ orbit (stabilizer G ω) γ := by
    intro w
    rw [← hΦorb, hΦγ, horbθ, orbit_ruR0_of_mem_ruS hsS]
  obtain ⟨hsw, hsw1, hsw2⟩ : ∃ hh : G, hh • ω = δ ∧ hh • δ = ω := by
    apply exists_smul_swap
    intro z hz
    obtain ⟨i, hi⟩ := hX z
    have hn : (orbit (stabilizer G ω) z).ncard = 1755 := by
      have := horb z
      rw [hz, hδcard] at this
      omega
    rw [orbit_eq_iff.2 hi, hxn] at hn
    have hi1 : i = 1 := hinjn (hn.trans (by rfl))
    rw [hi1] at hi
    exact hi
  have hA_symm : ∀ {z w : Ω}, orbAdj G ω δ z w → orbAdj G ω δ w z :=
    fun hzw => orbAdj_symm hsw1 hsw2 hzw
  have hA_F : ∀ (f : stabilizer G ω) (z w : Ω),
      orbAdj G ω δ (f • z) (f • w) ↔ orbAdj G ω δ z w := fun f z w => orbAdj_smul (f : G) ω δ z w
  have hA_irr : ∀ z, ¬ orbAdj G ω δ z z := by
    intro z hz
    obtain ⟨g, rfl⟩ := exists_smul_eq G ω z
    rw [orbAdj_smul, orbAdj_base_iff, ← orbit_eq_iff] at hz
    have := hn0
    rw [hz, hn1] at this
    norm_num at this
  have hA_card : ∀ z, {w | orbAdj G ω δ z w}.ncard = 1755 := by
    intro z
    obtain ⟨g, rfl⟩ := exists_smul_eq G ω z
    have e : {w | orbAdj G ω δ (g • ω) w} = (fun w => g • w) '' orbit (stabilizer G ω) δ := by
      ext w
      constructor
      · intro hw
        refine ⟨g⁻¹ • w, ?_, smul_inv_smul g w⟩
        rw [← orbAdj_base_iff, ← orbAdj_smul g, smul_inv_smul]
        exact hw
      · rintro ⟨w', hw', rfl⟩
        show orbAdj G ω δ (g • ω) (g • w')
        rw [orbAdj_smul, orbAdj_base_iff]
        exact hw'
    rw [e, Set.ncard_image_of_injective _ (MulAction.injective g), hn1]
  have hθP : ∀ f : stabilizer G ω, ((θ f : ruR0) : Equiv.Perm (Fin 4060)) ∈ ruP :=
    fun f => ruR0_le_ruP (θ f).2
  have hgood : ∀ (f : stabilizer G ω) (z : Ω),
      (∀ w, orbAdj G ω δ z w ↔ ruAdj (Φ z) (Φ w)) →
      ∀ w, orbAdj G ω δ (f • z) w ↔ ruAdj (Φ (f • z)) (Φ w) := by
    intro f z hz w
    have e1 : orbAdj G ω δ (f • z) w ↔ orbAdj G ω δ z (f⁻¹ • w) := by
      have := hA_F f z (f⁻¹ • w)
      rwa [smul_inv_smul] at this
    rw [e1, hz, hΦeq, hΦeq]
    conv_rhs => rw [← smul_inv_smul f (Φ w)]
    rw [hsmul f (Φ z), hsmul f (f⁻¹ • Φ w), ruAdj_apply (hθP f)]
  have hgood0 : ∀ w, orbAdj G ω δ ω w ↔ ruAdj (Φ ω) (Φ w) := by
    intro w
    rw [orbAdj_base_iff, hΦω, ruAdj_zero_iff, hΦD]
  have hinvT : ∀ (z : Ω) (n : Fin 4060) (r : Equiv.Perm (Fin 4060)), r ∈ ruR0 → r n = n →
      Φ z = n → ∀ m, (r m ∈ {k | orbAdj G ω δ z (Φ.symm k)} ↔
        m ∈ {k | orbAdj G ω δ z (Φ.symm k)}) := by
    intro z n r hr hrn hzn m
    set f : stabilizer G ω := θ.symm ⟨r, hr⟩ with hf
    have hfr : ∀ k, f • k = r k := by
      intro k
      rw [hsmul, hf, MulEquiv.apply_symm_apply]
    have hfz : f • z = z := by
      apply Φ.injective
      rw [hΦeq, hzn, hfr, hrn]
    show orbAdj G ω δ z (Φ.symm (r m)) ↔ orbAdj G ω δ z (Φ.symm m)
    rw [← hfr, hΦsymm]
    conv_lhs => rw [← hfz]
    exact hA_F f z (Φ.symm m)
  have hcardT : ∀ z : Ω, {k | orbAdj G ω δ z (Φ.symm k)}.ncard = 1755 := by
    intro z
    have e : {k | orbAdj G ω δ z (Φ.symm k)} = Φ '' {w | orbAdj G ω δ z w} := by
      ext k
      constructor
      · intro hk
        exact ⟨Φ.symm k, hk, Equiv.apply_symm_apply _ _⟩
      · rintro ⟨w, hw, rfl⟩
        show orbAdj G ω δ z (Φ.symm (Φ w))
        rw [Equiv.symm_apply_apply]
        exact hw
    rw [e, Set.ncard_image_of_injective _ Φ.injective, hA_card]
  have hgood2 : ∀ w, orbAdj G ω δ γ w ↔ ruAdj (Φ γ) (Φ w) := by
    have h0 : (0 : Fin 4060) ∉ {k | orbAdj G ω δ γ (Φ.symm k)} := by
      intro hk
      change orbAdj G ω δ γ (Φ.symm 0) at hk
      rw [hω0] at hk
      have := hA_symm hk
      rw [orbAdj_base_iff, ← orbit_eq_iff] at this
      have h2 := hn2
      rw [this, hn1] at h2
      norm_num at h2
    have hsT : s ∉ {k | orbAdj G ω δ γ (Φ.symm k)} := by
      intro hk
      change orbAdj G ω δ γ (Φ.symm s) at hk
      rw [← hΦγ, Equiv.symm_apply_apply] at hk
      exact hA_irr γ hk
    rcases ru_rf2 hsS (fun r hr hrs => hinvT γ s r hr hrs hΦγ) (hcardT γ) h0 hsT with hT | hT
    · intro w
      rw [hΦγ, ← hT (Φ w)]
      show _ ↔ orbAdj G ω δ γ (Φ.symm (Φ w))
      rw [Equiv.symm_apply_apply]
    · exfalso
      have hsub : orbit (stabilizer G ω) γ ⊆ {w | orbAdj G ω δ δ w} := by
        rintro _ ⟨f, rfl⟩
        apply hA_symm
        have e1 : orbAdj G ω δ (f • γ) δ ↔ orbAdj G ω δ γ (f⁻¹ • δ) := by
          have := hA_F f γ (f⁻¹ • δ)
          rwa [smul_inv_smul] at this
        rw [e1]
        have := (hT (Φ (f⁻¹ • δ))).2 ((hΦD _).2 ⟨f⁻¹, rfl⟩)
        simpa using this
      have hle := Set.ncard_le_ncard hsub
      rw [hn2, hA_card] at hle
      norm_num at hle
  have hgood1 : ∀ w, orbAdj G ω δ δ w ↔ ruAdj (Φ δ) (Φ w) := by
    have h0 : (0 : Fin 4060) ∈ {k | orbAdj G ω δ δ (Φ.symm k)} := by
      show orbAdj G ω δ δ (Φ.symm 0)
      rw [← hΦω, Equiv.symm_apply_apply]
      exact hA_symm ((orbAdj_base_iff ω δ δ).2 (mem_orbit_self δ))
    have hdT : d ∉ {k | orbAdj G ω δ δ (Φ.symm k)} := by
      intro hk
      change orbAdj G ω δ δ (Φ.symm d) at hk
      rw [← hΦδ, Equiv.symm_apply_apply] at hk
      exact hA_irr δ hk
    rcases ru_rf1 hdD (fun r hr hrd => hinvT δ d r hr hrd hΦδ) (hcardT δ) h0 hdT with hT | hT
    · intro w
      rw [hΦδ, ← hT (Φ w)]
      show _ ↔ orbAdj G ω δ δ (Φ.symm (Φ w))
      rw [Equiv.symm_apply_apply]
    · exfalso
      obtain ⟨m, hmD, hsm⟩ := exists_adj_ruB hsS
      have hw : orbAdj G ω δ γ (Φ.symm m) := by
        rw [hgood2, hΦγ, Equiv.apply_symm_apply]
        exact hsm
      have hwD : Φ.symm m ∈ orbit (stabilizer G ω) δ := by
        rw [← hΦD, Equiv.apply_symm_apply]
        exact hmD
      obtain ⟨f, hf⟩ := hwD
      rw [← hf] at hw
      have e1 : orbAdj G ω δ (f⁻¹ • γ) δ := by
        rw [← hA_F f, smul_inv_smul]
        exact hw
      have hmem : Φ (f⁻¹ • γ) ∈ {k | orbAdj G ω δ δ (Φ.symm k)} := by
        show orbAdj G ω δ δ (Φ.symm (Φ (f⁻¹ • γ)))
        rw [Equiv.symm_apply_apply]
        exact hA_symm e1
      exact hT _ hmem ((hΦS _).2 ⟨f⁻¹, rfl⟩)
  refine ⟨Φ, fun z w => ?_⟩
  obtain ⟨i, f, rfl⟩ := hX z
  fin_cases i
  · exact hgood f ω hgood0 w
  · exact hgood f δ hgood1 w
  · exact hgood f γ hgood2 w

theorem IsRudvalisRank3.exists_graph_equiv
    (h : IsRudvalisRank3 G Ω) :
    ∃ (Φ : Ω ≃ Fin 4060) (ω δ : Ω), ∀ z y, orbAdj G ω δ z y ↔ ruAdj (Φ z) (Φ y) := by
  obtain ⟨ω⟩ := h.nonempty
  obtain ⟨δ, hδ, -⟩ := h.parabolic ω
  obtain ⟨Φ, hΦ⟩ := h.exists_graph_equiv_of ω δ hδ
  exact ⟨Φ, ω, δ, hΦ⟩

theorem IsRudvalisRank3.range_conj_eq
    (h : IsRudvalisRank3 G Ω) {ω δ : Ω} {Φ : Ω ≃ Fin 4060}
    (hΦ : ∀ z y, orbAdj G ω δ z y ↔ ruAdj (Φ z) (Φ y)) :
    Function.Injective ((Equiv.permCongrHom Φ).toMonoidHom.comp (MulAction.toPermHom G Ω)) ∧
      ((Equiv.permCongrHom Φ).toMonoidHom.comp (MulAction.toPermHom G Ω)).range = ruP := by
  have hfaith := h.faithful
  have htr := h.transitive
  set σ : G →* Equiv.Perm (Fin 4060) :=
    (Equiv.permCongrHom Φ).toMonoidHom.comp (MulAction.toPermHom G Ω) with hσdef
  have hσ : ∀ (g : G) (n : Fin 4060), σ g n = Φ (g • Φ.symm n) := fun g n => rfl
  have hσP : ∀ g, σ g ∈ ruP := by
    intro g
    apply mem_ruP_of_adj
    intro a b
    rw [hσ, hσ, ← hΦ, orbAdj_smul, hΦ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply hfaith.eq_of_smul_eq_smul
    intro z
    have e := congrArg (fun p : Equiv.Perm (Fin 4060) => p (Φ z)) hg
    simp only [hσ, Equiv.symm_apply_apply, Equiv.Perm.one_apply] at e
    rw [one_smul]
    exact Φ.injective e
  have hΩ : Nat.card Ω = 4060 := by
    rw [Nat.card_congr Φ, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨ψ⟩ := h.twoF4 ω
  have hG : Nat.card G = 145926144000 := by
    have h1 := Subgroup.card_mul_index (stabilizer G ω)
    rw [index_stabilizer_of_transitive, hΩ, Nat.card_congr ψ.toEquiv, card_titsA] at h1
    rw [← h1]
  refine ⟨hinj, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, rfl⟩
    exact hσP g
  · rw [card_ruP, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hG]

theorem IsRudvalisRank3.nonempty_mulEquiv_ruP
    (h : IsRudvalisRank3 G Ω) :
    Nonempty (G ≃* ruP) := by
  obtain ⟨Φ, ω, δ, hΦ⟩ := h.exists_graph_equiv
  obtain ⟨hinj, hrange⟩ := h.range_conj_eq hΦ
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem IsRudvalisRank3.nonempty_mulEquiv_ru
    (h : IsRudvalisRank3 G Ω) :
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Ru) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_ruP
  exact ⟨e.trans ruEquivP.symm⟩

end Main

theorem statementJ514
    :
    ∀ (G Ω : Type) [Group G] [MulAction G Ω], IsRudvalisRank3 G Ω →
      Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Ru) := fun _ _ _ _ h => h.nonempty_mulEquiv_ru

end CFSG.Quasithin.RuRank3
