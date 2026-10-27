module

public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA02Quot
public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.T1515Concl
public import CFSG.Quasithin.EmptyFaithful.T1515cF
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top card_range_dvd quotPCore_subgroupOf_equiv
  pRank_subgroupOf_eq map_oPrimeResidualOf_top)

section Consumer

variable {G : Type} [Group G] [Finite G]

structure A318Exclusion (X : Type) [Group X] [Finite X] : Prop where
  simple : IsSimpleGroup X
  rank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)
  noImage : ∀ (Y : Type) [Group Y] (s : Bool) (p k : ℕ), p.Prime → 1 ≤ k → IsPSLEps3 s p k Y →
    Int.ModEq 3 ((p ^ k : ℕ) : ℤ) (if s then 1 else -1) → ∀ f : Y →* X, ¬ Function.Surjective f

theorem A318Exclusion.nine_dvd_card {X : Type} [Group X] [Finite X] (h : A318Exclusion X) :
    9 ∣ Nat.card X := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
  rw [hE]
  exact (pow_dvd_pow 3 h.rank : 3 ^ 2 ∣ _)

theorem A318Exclusion.center_eq_bot {X : Type} [Group X] [Finite X] (h : A318Exclusion X) :
    Subgroup.center X = ⊥ := by
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht
  · exact hb
  · exfalso
    have hc : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top a) b).symm
    let _ : CommGroup X := { ‹Group X› with mul_comm := hc }
    have hp : Nat.Prime (Nat.card X) := IsSimpleGroup.prime_card
    have h9 := h.nine_dvd_card
    have h3 : 3 ∣ Nat.card X := dvd_trans (by norm_num) h9
    rcases (Nat.dvd_prime hp).mp h3 with h1 | h1
    · omega
    · rw [← h1] at h9
      omega

theorem A318Exclusion.three_dvd_card {X : Type} [Group X] [Finite X] (h : A318Exclusion X) :
    3 ∣ Nat.card X := dvd_trans (by norm_num) h.nine_dvd_card

theorem exists_central_order_three_of_scalar1515e {K : Type} [Field K] (H : Subgroup (GL (Fin 3) K))
    (ω : Kˣ) (hω : orderOf ω = 3) (hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ H) :
    ∃ z ∈ Subgroup.center ↥H, orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
  · apply orderOf_eq_prime
    · refine Subtype.ext ?_
      change (Matrix.GeneralLinearGroup.scalar (Fin 3) ω) ^ 3 = 1
      rw [← map_pow, ← hω, pow_orderOf_eq_one, map_one]
    · intro h
      have h1 := congrArg (fun g : H => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h
      simp [Matrix.GeneralLinearGroup.coe_scalar] at h1
      have : ω = 1 := h1
      rw [this, orderOf_one] at hω
      omega

theorem exists_unit_orderOf_three1515e {K : Type} [Field K] [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  exact exists_prime_orderOf_dvd_card' 3 (by rw [hc]; exact h)

theorem scalar_mem_statedSL1515e {K : Type} [Field K] (ω : Kˣ) (h : ω ^ 3 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 K := by
  refine Subgroup.subset_closure ?_
  show (((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) K)) :
    Matrix (Fin 3) (Fin 3) K).det = 1
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
  simpa [Finset.prod_const] using congrArg Units.val h

open scoped Matrix in
theorem scalar_mem_statedSU1515e {K : Type} [Field K] (q : ℕ) (hq : q ≠ 0) (ω : Kˣ)
    (h : ω ^ 3 = 1) (hq1 : 3 ∣ q + 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 q K := by
  obtain ⟨m, hm⟩ := hq1
  have h3 : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val h
  have hω : (ω : K) ^ q * (ω : K) = 1 := by
    rw [← pow_succ, hm, pow_mul, h3, one_pow]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · show (((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K).det = 1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
    simpa [Finset.prod_const] using h3
  · show (((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ *
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_map (f := fun x : K => x ^ q) (zero_pow hq), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    simp only [hω]
    exact Matrix.diagonal_one

theorem exists_central_order_three_of_equiv1515e {X H : Type} [Group X] [Group H] (e : X ≃* H)
    (h : ∃ z ∈ Subgroup.center H, orderOf z = 3) : ∃ z ∈ Subgroup.center X, orderOf z = 3 := by
  obtain ⟨z, hz, hzo⟩ := h
  refine ⟨e.symm z, ?_, by rw [MulEquiv.orderOf_eq]; exact hzo⟩
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  apply e.injective
  simpa using hz (e g)

theorem exists_central_order_three_of_a318Case3Group1515e {X : Type} [Group X] [Finite X]
    (h : A318Case3Group X) : ∃ z ∈ Subgroup.center X, orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hhat : ∀ {S : Type} [Group S], IsHat X S → ∃ z ∈ Subgroup.center X, orderOf z = 3 := by
    intro S _ hS
    obtain ⟨-, hc, -⟩ := hS
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 3 (by rw [hc])
    exact ⟨z, z.2, by rw [← hz, Subgroup.orderOf_coe]⟩
  rcases h with ⟨s, q, hmod, hs⟩ | h | h | h
  · cases s
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hs
      have hq1 : 3 ∣ q + 1 := by
        have := hmod
        simp only [Bool.false_eq_true, ite_false, Int.ModEq] at this
        omega
      have hq0 : q ≠ 0 := by omega
      have hq2 : 3 ∣ q ^ 2 - 1 := by
        have h2 : q % 3 = 2 := by omega
        have h3 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h2]
        omega
      obtain ⟨ω, hω⟩ := exists_unit_orderOf_three1515e (K := K) (by rw [hK]; exact hq2)
      have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
      exact exists_central_order_three_of_equiv1515e e
        (exists_central_order_three_of_scalar1515e _ ω hω
          (scalar_mem_statedSU1515e q hq0 ω hω3 hq1))
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hs
      have hq1 : 3 ∣ q - 1 := by
        have := hmod
        simp only [ite_true, Int.ModEq] at this
        omega
      obtain ⟨ω, hω⟩ := exists_unit_orderOf_three1515e (K := K) (by rw [hK]; exact hq1)
      have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
      exact exists_central_order_three_of_equiv1515e e
        (exists_central_order_three_of_scalar1515e _ ω hω (scalar_mem_statedSL1515e ω hω3))
  · exact hhat h
  · exact hhat h
  · exact hhat h

theorem exists_starHom1515e {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥)
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ ψ : ↥(starImage 3 L) →* (↥L ⧸ CFSG.pCore 2 ↥L), Function.Surjective ψ ∧
      ∀ y : ↥(starImage 3 L), ψ y = 1 → ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ₀ : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ₀
  set π₃ := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ₃
  let ρ : ↥L →* ↥(starImage 3 L) :=
    (π₃.comp L.subtype).codRestrict (starImage 3 L) (fun x => ⟨x, x.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : ↥L, x ∈ ρ.ker → (x : H) ∈ CFSG.pPrimeCore 3 H := by
    intro x hx
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    change π₃ (x : H) = 1 at h1
    rwa [hπ₃, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hN3 : Nat.Coprime 3 (Nat.card ρ.ker) := by
    have hle : ρ.ker.map L.subtype ≤ CFSG.pPrimeCore 3 H := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker x hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have hNX : ρ.ker.map φ₀ = ⊥ := by
    have hn : (ρ.ker.map φ₀).Normal :=
      Subgroup.Normal.map inferInstance φ₀ (QuotientGroup.mk'_surjective _)
    have hne : ρ.ker.map φ₀ ≠ ⊤ := by
      intro htop
      have h1 : Nat.card (ρ.ker.map φ₀) ∣ Nat.card ρ.ker := by
        rw [← MonoidHom.domRestrict_range]
        exact card_range_dvd _
      rw [htop, Subgroup.card_top] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right h1 hN3) h3)
        (by norm_num)
    have hle := le_center_of_normal_ne_top hQ hne
    rw [hZ] at hle
    exact le_bot_iff.mp hle
  have hle : ρ.ker ≤ φ₀.ker := by
    intro x hx
    have : φ₀ x ∈ ρ.ker.map φ₀ := Subgroup.mem_map_of_mem φ₀ hx
    rw [hNX, Subgroup.mem_bot] at this
    exact this
  set e := QuotientGroup.quotientKerEquivOfSurjective ρ hρ with he
  have he' : ∀ x : ↥L, e.symm (ρ x) = (x : ↥L ⧸ ρ.ker) := fun x => e.symm_apply_eq.mpr rfl
  set ψ := (QuotientGroup.lift ρ.ker φ₀ hle).comp e.symm.toMonoidHom with hψ
  have hψρ : ∀ x : ↥L, ψ (ρ x) = φ₀ x := by
    intro x
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he', QuotientGroup.lift_mk]
  refine ⟨ψ, fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
    exact ⟨ρ x, hψρ x⟩
  · obtain ⟨x, rfl⟩ := hρ y
    rw [hψρ, hφ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this, map_one]

theorem not_case2_case3_of_exclusion
    {H L : Subgroup G} (hLH : L ≤ H) (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {S : Type} [Group S] [Finite S] (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* S) (hS : A318Exclusion S) :
    ¬ A318Case2 (starImage 3 (L.subgroupOf H)) ∧
      ¬ A318Case3Group ↥(starImage 3 (L.subgroupOf H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := hS.center_eq_bot
  have hr := hS.rank
  have hX := hS.noImage
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  set e' := e₀.trans e
  have hQ' : CFSG.IsQuasisimple (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hZ' : Subgroup.center (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) = ⊥ := by
    have h1 := Subgroup.map_center_eq e'
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h1
  have h3 : 3 ∣ Nat.card (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) := by
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (⊤ : Subgroup S)
    rw [Nat.card_congr e'.toEquiv]
    refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨ψ, hψ, hψk⟩ := exists_starHom1515e hQ' hZ' h3
  set ψ' := e'.toMonoidHom.comp ψ with hψ'
  have hψ's : Function.Surjective ψ' := e'.surjective.comp hψ
  refine ⟨fun h2 => ?_, fun h3' => ?_⟩
  · obtain ⟨s, q, hmod, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩ := h2
    subst hq
    exact hX _ s r k hrp hk1 hPSL hmod ψ' hψ's
  · obtain ⟨z, hzcen, hz⟩ := exists_central_order_three_of_a318Case3Group1515e h3'
    have hzc : ψ' z ∈ Subgroup.center S := Subgroup.map_center_le_center hψ's ⟨_, hzcen, rfl⟩
    rw [hZ, Subgroup.mem_bot] at hzc
    have h1 : ψ z = 1 := by
      have := congrArg e'.symm hzc
      rwa [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        map_one] at this
    obtain ⟨k, hk⟩ := hψk _ h1
    have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [hz] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega

theorem eq_oPrimeResidualOf_three_of_exclusion (hF : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK)
    {H L : Subgroup G} (hH : SQTKGroup ↥H) (hL : L ∈ cComp H)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {S : Type} [Group S] [Finite S] (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* S) (hS : A318Exclusion S) :
    L = oPrimeResidualOf 3 H := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hSQ := SQTKHyp.of_sqtkGroup ↥H hH
  have hLc := subgroupOf_mem_cComp hL
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hr : 1 < CFSG.Open.pRank 3 (L.subgroupOf H) := by
    rw [pRank_subgroupOf_eq hLH Nat.prime_three (by norm_num),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    have := hS.rank
    omega
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' Nat.prime_three (by norm_num) hr
  obtain ⟨hn2, hn3⟩ := not_case2_case3_of_exclusion hLH hQ e hS
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, h3, -⟩
  · rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hLH]
  · exact absurd h2 hn2
  · exact absurd h3 hn3

theorem pCore_two_eq_bot_of_simple {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (h3 : 3 ∣ Nat.card X) : CFSG.pCore 2 X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := X))
    rw [ht, Subgroup.card_top] at hn
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

theorem quotPCore_equiv_of_simple {L : Subgroup G} (hs : IsSimpleGroup ↥L)
    (h3 : 3 ∣ Nat.card ↥L) : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥L) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (pCore_two_eq_bot_of_simple hs h3)).trans
    QuotientGroup.quotientBot⟩

omit [Finite G] in
theorem quotPCore_equiv_alt_of_isAltBlockType {L : Subgroup G} {m : ℕ} (h : IsAltBlockType L m) :
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin m)) := by
  obtain ⟨-, α, hs, hk, -⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hs)⟩

theorem pCore_eq_center_of_simple_quot {L : Subgroup G} (hZ : IsPGroup 2 (Subgroup.center ↥L))
    (hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L)) (h3 : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) :
    CFSG.pCore 2 ↥L = Subgroup.center ↥L := by
  refine le_antisymm ?_ ?_
  · set f := QuotientGroup.mk' (Subgroup.center ↥L) with hf
    have hn : ((CFSG.pCore 2 ↥L).map f).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal f (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥L).map f) with hb | ht
    · intro x hx
      have : f x ∈ (CFSG.pCore 2 ↥L).map f := Subgroup.mem_map_of_mem f hx
      rw [hb, Subgroup.mem_bot, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exfalso
      have hP := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map f
      obtain ⟨n, hn2⟩ := (IsPGroup.iff_card).1 hP
      rw [ht, Subgroup.card_top] at hn2
      rw [hn2] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  · try with_reducible rfl
    exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance hZ

structure KnownFacts15122Types : Prop where
  alt7 : A318Exclusion (alternatingGroup (Fin 7))
  alt6 : A318Exclusion (alternatingGroup (Fin 6))
  u33 : ∀ (X : Type) [Group X] [Finite X], IsPSU 3 3 1 X → A318Exclusion X
  l42 : ∀ (X : Type) [Group X] [Finite X], IsPSL 4 2 1 X → A318Exclusion X
  l52 : ∀ (X : Type) [Group X] [Finite X], IsPSL 5 2 1 X → A318Exclusion X
  tits : ∀ (X : Type) [Group X] [Finite X], IsTits X → A318Exclusion X
  d42 : ∀ (X : Type) [Group X] [Finite X], Is3D4 2 1 X → A318Exclusion X
  j2 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .J2 X → A318Exclusion X
  he : ∀ (X : Type) [Group X] [Finite X], IsSporadic .He X → A318Exclusion X
  m12 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .M12 X → A318Exclusion X
  m22 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .M22 X → A318Exclusion X
  m23 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .M23 X → A318Exclusion X
  m24 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .M24 X → A318Exclusion X
  m11 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .M11 X → A318Exclusion X

theorem exists_model_of_exclusion_self {L : Subgroup G} (h : A318Exclusion ↥L) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S), Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* S) ∧
      A318Exclusion S := by
  obtain ⟨e⟩ := quotPCore_equiv_of_simple h.simple h.three_dvd_card
  exact ⟨↥L, inferInstance, inferInstance, ⟨e⟩, h⟩

theorem exists_exclusion_model_of_case15122 (hK : KnownFacts15122Types)
    {T Mc M Z₁ L : Subgroup G} (hO : oddCoreIn (g1_1516 Z₁) = ⊥) (hL : IsL1519 Mc Z₁ L)
    (hn3 : ¬ IsLnBlock L 3) (h22 : Lemma15122Concl T Mc M Z₁ L) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S), Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* S) ∧
      A318Exclusion S := by
  rcases h22 with h | h | h | h | h | h | h
  · exact ⟨alternatingGroup (Fin 7), inferInstance, inferInstance,
      quotPCore_equiv_alt_of_isAltBlockType h.1, hK.alt7⟩
  · rcases h.1 with h1 | h1 | h1
    · exact absurd h1 hn3
    · exact ⟨alternatingGroup (Fin 6), inferInstance, inferInstance,
        quotPCore_equiv_alt_of_isAltBlockType h1, hK.alt6⟩
    · exact ⟨↥L ⧸ CFSG.pCore 2 ↥L, inferInstance, inferInstance, ⟨MulEquiv.refl _⟩,
        hK.u33 _ h1.2.1⟩
  · rcases h.2.1 with h1 | h1
    · exact ⟨↥L ⧸ CFSG.pCore 2 ↥L, inferInstance, inferInstance, ⟨MulEquiv.refl _⟩, hK.l42 _ h1⟩
    · exact ⟨↥L ⧸ CFSG.pCore 2 ↥L, inferInstance, inferInstance, ⟨MulEquiv.refl _⟩, hK.l52 _ h1⟩
  · rcases h.1 with h1 | h1 | h1
    · exact exists_model_of_exclusion_self (hK.u33 _ h1)
    · exact exists_model_of_exclusion_self (hK.tits _ h1)
    · exact exists_model_of_exclusion_self (hK.d42 _ h1)
  ·
    have hX : A318Exclusion (↥L ⧸ Subgroup.center ↥L) := by
      rcases h.1 with h1 | h1 | h1 | h1 | h1 | h1
      exacts [hK.j2 _ h1, hK.he _ h1, hK.m12 _ h1, hK.m22 _ h1, hK.m23 _ h1, hK.m24 _ h1]
    have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hL.comp
    have hperf : commutator ↥L = ⊤ := by
      have := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hL.comp)
      exact this.commutator_eq_top
    have hqs : CFSG.Open.IsQuasisimple ↥L := ⟨hperf, hX.simple⟩
    have hZ := isPGroup_two_center_of_isComponentOf1515c
      (show IsComponentOf L (g1_1516 Z₁) from ⟨hLG, subnormal_of_mem_cComp hL.comp, hqs⟩) hO
    have hP := pCore_eq_center_of_simple_quot hZ hX.simple hX.three_dvd_card
    exact ⟨↥L ⧸ Subgroup.center ↥L, inferInstance, inferInstance,
      ⟨QuotientGroup.quotientMulEquivOfEq hP⟩, hX⟩
  · exact exists_model_of_exclusion_self (hK.m11 _ h.1)
  · rcases h.1 with h1 | h1
    · exact exists_model_of_exclusion_self (hK.l42 _ h1)
    · exact exists_model_of_exclusion_self (hK.l52 _ h1)

end Consumer

end CFSG.Quasithin
