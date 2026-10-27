module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrimeCoordinates
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitDiagonalPlane
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.RankThree.Classical2
  CFSG.LieType.Universal.Spin
open scoped commutatorElement

section Transport

variable {H H' : Type*} [Group H] [Group H']

theorem map_centralizer_singleton (e : H ≃* H') (a : H) :
    (Subgroup.centralizer ({a} : Set H)).map e.toMonoidHom =
      Subgroup.centralizer ({e a} : Set H') := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    replace hy : y ∈ Subgroup.centralizer ({a} : Set H) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    show e y * e a = e a * e y
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    show e.symm x ∈ Subgroup.centralizer ({a} : Set H)
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hx

theorem map_derivedCentralizer (e : H ≃* H') (G₀ : Subgroup H) (a : H) :
    (derivedCentralizer G₀ a).map e.toMonoidHom =
      derivedCentralizer (G₀.map e.toMonoidHom) (e a) := by
  unfold derivedCentralizer
  rw [Subgroup.map_commutator, Subgroup.map_inf _ _ _ e.injective, map_centralizer_singleton]

theorem iSup_derivedCentralizer_of_map (e : H ≃* H') (Ω G : Subgroup H)
    (h : (⨆ (a : H') (_ : a ∈ G.map e.toMonoidHom ∧ a ≠ 1),
        derivedCentralizer (Ω.map e.toMonoidHom) a) = Ω.map e.toMonoidHom) :
    (⨆ (x : H) (_ : x ∈ G ∧ x ≠ 1), derivedCentralizer Ω x) = Ω := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_iSup]
  simp only [Subgroup.map_iSup, map_derivedCentralizer]
  refine Eq.trans ?_ h
  refine le_antisymm (iSup_le fun x => iSup_le fun hx => ?_)
    (iSup_le fun a => iSup_le fun ha => ?_)
  · exact le_iSup₂_of_le (e x) ⟨⟨x, hx.1, rfl⟩, fun h1 => hx.2 (e.injective (by rw [h1, map_one]))⟩
      le_rfl
  · obtain ⟨⟨x, hxG, rfl⟩, ha1⟩ := ha
    exact le_iSup₂_of_le x ⟨hxG, fun h1 => ha1 (by rw [h1, map_one])⟩ le_rfl

theorem isElemAbelian_map {p : ℕ} (e : H ≃* H') {G : Subgroup H} (hG : Assembly.IsElemAbelian p G)
    (hcard : Nat.card G = p ^ 2) :
    Assembly.IsElemAbelian p (G.map e.toMonoidHom) ∧ Nat.card (G.map e.toMonoidHom) = p ^ 2 := by
  have := hG.1
  refine ⟨⟨⟨⟨?_⟩⟩, ?_⟩, by rw [Subgroup.card_map_of_injective e.injective, hcard]⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show e a * e b = e b * e a
    have h : a * b = b * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : G) ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, h]
  · rintro _ ⟨a, ha, rfl⟩
    show (e a) ^ p = 1
    rw [← map_pow, hG.2 a ha, map_one]

theorem exists_transport_chars {p : ℕ} (e : H ≃* H') (G : Subgroup H) {ι : Type*}
    (χ : ι → (G →* Multiplicative (ZMod p))) :
    ∃ χ' : ι → ((G.map e.toMonoidHom) →* Multiplicative (ZMod p)),
      ∀ g' : ↥(G.map e.toMonoidHom), ∃ g : ↥G, (g' : H') = e (g : H) ∧ ∀ i, χ' i g' = χ i g := by
  refine ⟨fun i => (χ i).comp (e.subgroupMap G).symm.toMonoidHom, fun g' => ?_⟩
  refine ⟨(e.subgroupMap G).symm g', ?_, fun i => rfl⟩
  have := congrArg Subtype.val ((e.subgroupMap G).apply_symm_apply g')
  exact this.symm

end Transport

section Root

theorem exists_root_of_dvd_card_sub_one {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card K - 1) : ∃ ζ : K, orderOf ζ = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  exact ⟨x, by rw [orderOf_units, hx]⟩

theorem natCast_ne_zero_of_dvd_card_sub_one {K : Type*} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (h : p ∣ Nat.card K - 1) : (p : K) ≠ 0 := by
  intro h0
  have := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hc : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).mp h0
  have hpc : p = ringChar K := ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hc).symm
  have hdvd : p ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn, hpc]
    exact dvd_pow_self _ n.ne_zero
  have h1 : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hdvd h
  rw [Nat.sub_sub_self Nat.card_pos] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

end Root

section Main

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orthogonal_plane_derived_centralizers_generate
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1)
    (G : Subgroup (V ≃ₗ[K] V)) (hGΩ : G ≤ orthDerived Q) (hG : Assembly.IsElemAbelian p G)
    (hGcard : Nat.card G = p ^ 2) :
    (⨆ (x : V ≃ₗ[K] V) (_ : x ∈ G ∧ x ≠ 1), derivedCentralizer (orthDerived Q) x) =
      orthDerived Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ζ, hζord⟩ := exists_root_of_dvd_card_sub_one hp hpq
  have hζ : IsPrimitiveRoot ζ p := by
    rw [← hζord]
    exact IsPrimitiveRoot.orderOf ζ
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_dvd_card_sub_one hp hpq
  have hΩ : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hGQ : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg => hΩO (hGΩ hg)
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : IsMulCommutative G := hG.1
  have hGcardK : (Nat.card G : K) ≠ 0 := by
    rw [hGcard, Nat.cast_pow]
    exact pow_ne_zero 2 hpK
  obtain ⟨r, U, φ, χ, hφQ, hani, -, hdiag, hfix⟩ :=
    exists_split_coordinates hQ hp hp2 hζ G hGQ hG.2 hGcardK
  have hani' : (Q.comp U.subtype).Anisotropic := fun u hu => Subtype.ext (hani u u.2 hu)
  have hr3 : 3 ≤ r := by
    obtain ⟨L, hL3, hLs⟩ := hT
    have hsing : ∀ x ∈ L.map (φ : V →ₗ[K] _), quadTail r (Q.comp U.subtype) x = 0 := by
      rintro _ ⟨v, hv, rfl⟩
      rw [LinearEquiv.coe_coe, hφQ]
      exact hLs v hv
    have := finrank_le_of_totSing_tail hani' hsing
    rwa [LinearEquiv.finrank_map_eq, hL3] at this
  by_cases hU0 : U = ⊥
  ·
    have : Subsingleton ↥U := Submodule.subsingleton_iff_eq_bot.mpr hU0
    have : Unique ↥U := Unique.mk' _
    set Φ : V ≃ₗ[K] (Fin r ⊕ Fin r → K) := φ.trans LinearEquiv.prodUnique with hΦ
    have hΦapp : ∀ v, Φ v = (φ v).1 := fun v => rfl
    have hΦsymm : ∀ z, Φ.symm z = φ.symm (z, 0) := fun z => by
      rw [LinearEquiv.symm_apply_eq, hΦapp, LinearEquiv.apply_symm_apply]
    have hΦQ : ∀ v, quadPlus r K (Φ v) = Q v := by
      intro v
      have h := hφQ v
      rw [quadTail_apply] at h
      have h0 : (φ v).2 = 0 := Subsingleton.elim _ _
      rw [h0] at h
      rw [hΦapp]
      simpa using h
    have hconj : ∀ (g : V ≃ₗ[K] V) (z : Fin r ⊕ Fin r → K),
        LinearEquiv.autCongr Φ g z = (LinearEquiv.autCongr φ g (z, 0)).1 := by
      intro g z
      rw [LinearEquiv.autCongr_apply_apply, LinearEquiv.autCongr_apply_apply, hΦsymm, hΦapp]
    let hiso : Q.IsometryEquiv (quadPlus r K) := { Φ with map_app' := hΦQ }
    have hmap : (orthDerived Q).map (LinearEquiv.autCongr Φ).toMonoidHom =
        orthElementaryGroup (quadPlus r K) := by
      rw [hΩ]
      exact CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryGroup_map
        hiso
    have hAle : G.map (LinearEquiv.autCongr Φ).toMonoidHom ≤
        orthElementaryGroup (quadPlus r K) := by
      rw [← hmap]
      exact Subgroup.map_mono hGΩ
    obtain ⟨hAel, hAcard⟩ := isElemAbelian_map (LinearEquiv.autCongr Φ) hG hGcard
    obtain ⟨χ', hχ'⟩ := exists_transport_chars (LinearEquiv.autCongr Φ) G χ
    have hgen := (split_diagonal_orthogonal_plane_derived_centralizer_generation.{0, 0} hp hp3
      hζord hr3).1 (G.map (LinearEquiv.autCongr Φ).toMonoidHom) hAle hAel hAcard χ' (fun g' i => by
        obtain ⟨g, hg, hχ⟩ := hχ' g'
        rw [hg, hχ i, hconj, hconj]
        exact ⟨congrArg Prod.fst (hdiag g i).1, congrArg Prod.fst (hdiag g i).2⟩)
    exact iSup_derivedCentralizer_of_map (LinearEquiv.autCongr Φ) (orthDerived Q) G
      (by rw [hmap]; exact hgen.2.1)
  ·
    obtain ⟨u, hu⟩ : ∃ u : ↥U, u ≠ 0 := by
      by_contra h
      push Not at h
      exact hU0 ((Submodule.eq_bot_iff U).mpr fun x hx => congrArg Subtype.val (h ⟨x, hx⟩))
    let hiso : Q.IsometryEquiv (quadTail r (Q.comp U.subtype)) := { φ with map_app' := hφQ }
    have hmap : (orthDerived Q).map (LinearEquiv.autCongr φ).toMonoidHom =
        orthElementaryGroup (quadTail r (Q.comp U.subtype)) := by
      rw [hΩ]
      exact CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryGroup_map
        hiso
    have hAle : G.map (LinearEquiv.autCongr φ).toMonoidHom ≤
        orthElementaryGroup (quadTail r (Q.comp U.subtype)) := by
      rw [← hmap]
      exact Subgroup.map_mono hGΩ
    obtain ⟨hAel, hAcard⟩ := isElemAbelian_map (LinearEquiv.autCongr φ) hG hGcard
    obtain ⟨χ', hχ'⟩ := exists_transport_chars (LinearEquiv.autCongr φ) G χ
    have hgen := (split_diagonal_orthogonal_plane_derived_centralizer_generation hp hp3 hζord
      hr3).2 (Q.comp U.subtype) hani' ⟨u, hu⟩ (G.map (LinearEquiv.autCongr φ).toMonoidHom) hAle
      hAel hAcard χ' (fun g' i => by
        obtain ⟨g, hg, hχ⟩ := hχ' g'
        rw [hg, hχ i]
        exact hdiag g i) (fun g' u' => by
        obtain ⟨g, hg, -⟩ := hχ' g'
        rw [hg]
        exact hfix g u')
    exact iSup_derivedCentralizer_of_map (LinearEquiv.autCongr φ) (orthDerived Q) G
      (by rw [hmap]; exact hgen.2.1)

end Main

end CFSG.RankThree.PartOne.KCOrthogonal
