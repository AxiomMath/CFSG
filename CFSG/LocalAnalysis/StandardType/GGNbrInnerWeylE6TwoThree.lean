module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open TableBExc.E6Three E6TwoPilot

section Main

theorem ggE6TwoThree_mem_zpowers_map_mulEquiv_iff {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (a b : G) :
    e a ∈ Subgroup.zpowers (e b) ↔ a ∈ Subgroup.zpowers b := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, e.injective (by rw [map_zpow, hk])⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← map_zpow, hk]⟩

theorem ggE6TwoThree_normalizer_of_action {M : Type} [Group M] {G : Type} [Group G]
    (f : M →* G) (n : G) (φ : M ≃* M) (h : ∀ m, n * f m * n⁻¹ = f (φ m)) :
    n ∈ Subgroup.normalizer (f.range : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨φ v, (h v).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨φ.symm v, ?_⟩
    have h1 := h (φ.symm v)
    rw [φ.apply_symm_apply] at h1
    rw [hv] at h1
    have h2 := congrArg (fun y => n⁻¹ * y * n) h1
    simpa [mul_assoc] using h2

theorem ggSCNoLine_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGSCNoLine p r R') : GGSCNoLine p r R := by
  intro E hE hr h3 hsc e₀ he₀ he₀1
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.mp b.2
      show (↑a : R') * ↑b = ↑b * ↑a
      rw [← ha'e, ← hb'e, ← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha' hb']
    · obtain ⟨x', hx', hx'e⟩ := Subgroup.mem_map.mp hx
      rw [← hx'e, ← map_pow, hE.2 x' hx', map_one]
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) e.injective
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    have hg₀ : e.symm g ∈ E := by
      refine hsc (e.symm g) (fun x hx => ?_) (by rw [← map_pow, hgp, map_one])
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hg (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨e.symm g, hg₀, by simp⟩
  obtain ⟨g', hg', hmove'⟩ := h (E.map e.toMonoidHom) hE' (by rw [hcard]; exact hr)
    (by rw [hcard]; exact h3) hsc' (e e₀) (Subgroup.mem_map.mpr ⟨e₀, he₀, rfl⟩)
    (fun h => he₀1 (e.injective (by rw [h, map_one])))
  refine ⟨e.symm g', ?_, ?_⟩
  · have hnormmap : (Subgroup.normalizer E).map e.toMonoidHom =
        Subgroup.normalizer (E.map e.toMonoidHom) := Subgroup.map_equiv_normalizer_eq E e
    rw [← hnormmap] at hg'
    rcases Subgroup.mem_map.mp hg' with ⟨g, hg, hge⟩
    have hg_eq : g = e.symm g' := by
      rw [← hge]
      exact (e.symm_apply_apply g).symm
    rwa [hg_eq] at hg
  · intro hmem
    apply hmove'
    have heq : e (e.symm g' * e₀ * (e.symm g')⁻¹) = g' * e e₀ * g'⁻¹ := by
      simp only [map_mul, map_inv, e.apply_symm_apply]
    have h2 := (ggE6TwoThree_mem_zpowers_map_mulEquiv_iff e
      (e.symm g' * e₀ * (e.symm g')⁻¹) e₀).mpr hmem
    rwa [heq] at h2

theorem reflE6Two_invol : ∀ (i : Fin 4) (v : Multiplicative (Fin 4 → ZMod 3)),
    reflE6Two i (reflE6Two i v) = v := by
  decide +kernel

@[expose] noncomputable def ggE6TwoThree_reflEquiv (i : Fin 4) :
    Multiplicative (Fin 4 → ZMod 3) ≃* Multiplicative (Fin 4 → ZMod 3) :=
  MulEquiv.ofBijective (reflE6Two i) ⟨fun a b h => by
      have := congrArg (reflE6Two i) h
      simpa only [reflE6Two_invol] using this,
    fun b => ⟨reflE6Two i b, reflE6Two_invol i b⟩⟩

theorem e6Two_exists_move_fin : ∀ (v : Fin 4 → ZMod 3), v ≠ 0 →
    (∃ i : Fin 4, ∀ a : ZMod 3, v - reflFunE6Two i v • Pi.single i 1 ≠ a • v) ∨
    (∀ a : ZMod 3, mtFun v ≠ a • v) ∨
    (∀ a : ZMod 3, msFun v ≠ a • v) := by
  decide +kernel

theorem torusE6Two_mem_zpowers_imp_exists_smul {K : Type} [Field K] (h2 : (2 : K) = 0)
    {v w : Fin 4 → ZMod 3}
    (hmem : torusE6Two h2 (Multiplicative.ofAdd w) ∈
      Subgroup.zpowers (torusE6Two h2 (Multiplicative.ofAdd v))) :
    ∃ a : ZMod 3, w = a • v := by
  have hbridge : (Multiplicative.ofAdd w : Multiplicative (Fin 4 → ZMod 3)) ∈
      Subgroup.zpowers (Multiplicative.ofAdd v) := by
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, torusE6Two_injective h2 (by rw [map_zpow, hk])⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbridge
  refine ⟨(k : ZMod 3), ?_⟩
  have h1 : (k : ZMod 3) • v = w := by
    have h := congrArg Multiplicative.toAdd hk
    rw [toAdd_zpow, toAdd_ofAdd] at h
    rwa [Int.cast_smul_eq_zsmul]
  exact h1.symm

theorem torusE6Two_not_mem_zpowers_of_not_smul {K : Type} [Field K] (h2 : (2 : K) = 0)
    {v w : Fin 4 → ZMod 3} (hw : ∀ a : ZMod 3, w ≠ a • v) :
    torusE6Two h2 (Multiplicative.ofAdd w) ∉
      Subgroup.zpowers (torusE6Two h2 (Multiplicative.ofAdd v)) := fun hmem =>
  let ⟨a, ha⟩ := torusE6Two_mem_zpowers_imp_exists_smul h2 hmem
  hw a ha

theorem ggCenterPrime_recipe_E6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {p : ℕ} (hp : p.Prime) : GGCenterPrime p (TableBExc.RecipeGroup .E6 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  have hfinj : Function.Injective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldTwo.e6Isogeny_injective_two (K := K) hK
  have hfsurj : Function.Surjective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K) :=
    CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective K
  let qe : ↥((CFSG.LieType.Steinberg.Minuscule.e6Data_valid).minGroup K) ≃*
      TableBExc.RecipeGroup .E6 K :=
    (MulEquiv.ofBijective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K) ⟨hfinj, hfsurj⟩).trans
      (TableBExc.recipeEquiv .E6 K).symm
  have hZ : Subgroup.center ↥((CFSG.LieType.Steinberg.Minuscule.e6Data_valid).minGroup K) = ⊥ := by
    have h1 := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := K)).1
    rw [hK] at h1
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using h1)
  intro L' _ _ ψ hψ hker hperf hdvd
  have hψ' : Function.Surjective (qe.symm.toMonoidHom.comp ψ) := qe.symm.surjective.comp hψ
  have hker' : (qe.symm.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' := by
    intro x hx
    exact hker (by simpa [MonoidHom.mem_ker] using hx)
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.FieldTwo.e6_two_exists_section
      (K := K) hK L' (qe.symm.toMonoidHom.comp ψ) hψ' hker'
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  have hbot : (qe.symm.toMonoidHom.comp ψ).ker = ⊥ :=
    CFSG.SectionRank.ker_eq_bot_of_section_of_perfect _ hker' σ hσ
  have hcenter : Subgroup.center L' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hkerz : (qe.symm.toMonoidHom.comp ψ) z = 1 := by
      have hmem : (qe.symm.toMonoidHom.comp ψ) z ∈
          Subgroup.center ↥((CFSG.LieType.Steinberg.Minuscule.e6Data_valid).minGroup K) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨l, rfl⟩ := hψ' g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
      rwa [hZ, Subgroup.mem_bot] at hmem
    rw [← hbot]
    exact MonoidHom.mem_ker.mpr hkerz
  rw [hcenter, Subgroup.card_bot] at hdvd
  exact hp.not_dvd_one hdvd

theorem ggSCNoLine_adjoint_E6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGSCNoLine 3 4 (adjointGroup .E6 K) := by
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  intro E hE h4 h3 hsc e he he1
  obtain ⟨c, hc⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hE h4
  set B : Subgroup (adjointGroup .E6 K) := (torusE6Two h2).range with hB
  have hcE : E.map (MulAut.conj c).toMonoidHom = B := hc
  have hE_B : ∀ h, h ∈ E ↔ MulAut.conj c h ∈ B := by
    intro h
    rw [← hcE]
    constructor
    · intro hh; exact ⟨h, hh, rfl⟩
    · rintro ⟨y, hy, hyh⟩
      have : y = h := (MulAut.conj c).injective hyh
      rwa [this] at hy
  set ε := MulAut.conj c e with hε
  have hεB : ε ∈ B := by
    rw [hε]; exact (hE_B e).mp he
  obtain ⟨v, hv⟩ := hεB
  have hv1 : v ≠ 1 := by
    intro h1
    have hε1 : ε = 1 := by rw [← hv, h1, map_one]
    have heq : MulAut.conj c e = MulAut.conj c 1 := by rw [← hε, hε1, map_one]
    exact he1 ((MulAut.conj c).injective heq)
  let u : Fin 4 → ZMod 3 := v.toAdd
  have hvu : (Multiplicative.ofAdd u : Multiplicative (Fin 4 → ZMod 3)) = v :=
    ofAdd_toAdd v
  have hu : u ≠ 0 := by
    intro h0
    apply hv1
    rw [← hvu, h0, ofAdd_zero]
  have hvε : torusE6Two h2 (Multiplicative.ofAdd u) = ε := by
    rw [hvu]; exact hv
  have transport : ∀ n : adjointGroup .E6 K,
      n ∈ Subgroup.normalizer (B : Set _) → n * ε * n⁻¹ ∉ Subgroup.zpowers ε →
      (∃ g ∈ Subgroup.normalizer (E : Set _), g * e * g⁻¹ ∉ Subgroup.zpowers e) := by
    intro n hnB hmove
    refine ⟨MulAut.conj c⁻¹ n, ?_, ?_⟩
    · have hnormmap : (Subgroup.normalizer E).map (MulAut.conj c).toMonoidHom =
          Subgroup.normalizer B := by
        rw [Subgroup.map_equiv_normalizer_eq, hcE]
      have hmem : MulAut.conj c (MulAut.conj c⁻¹ n) ∈
          (Subgroup.normalizer E).map (MulAut.conj c).toMonoidHom := by
        rw [hnormmap]
        have hconj : MulAut.conj c (MulAut.conj c⁻¹ n) = n := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
        rw [hconj]; exact hnB
      rcases Subgroup.mem_map.mp hmem with ⟨g, hg, hgc⟩
      have hg_eq : g = MulAut.conj c⁻¹ n := by
        apply (MulAut.conj c).injective
        simpa using hgc
      rwa [hg_eq] at hg
    · intro hmem
      apply hmove
      have ha : MulAut.conj c (MulAut.conj c⁻¹ n * e * (MulAut.conj c⁻¹ n)⁻¹) =
          n * ε * n⁻¹ := by
        rw [hε]
        simp only [MulAut.conj_apply]
        group
      have h := (ggE6TwoThree_mem_zpowers_map_mulEquiv_iff (MulAut.conj c)
        (MulAut.conj c⁻¹ n * e * (MulAut.conj c⁻¹ n)⁻¹) e).mpr hmem
      rwa [ha, ← hε] at h
  rcases e6Two_exists_move_fin u hu with ⟨i, hi⟩ | hmt | hms
  · refine transport (nE6Two i) (ggE6TwoThree_normalizer_of_action (torusE6Two h2) (nE6Two i)
      (ggE6TwoThree_reflEquiv i)
      (fun m => by
        have h := nE6Two_conj_torus h2 i (Multiplicative.toAdd m)
        rwa [ofAdd_toAdd m] at h)) ?_
    rw [← hvε, nE6Two_conj_torus h2 i u]
    exact torusE6Two_not_mem_zpowers_of_not_smul h2 hi
  · refine transport (tE6Two K) (ggE6TwoThree_normalizer_of_action (torusE6Two h2) (tE6Two K) mtAut
      (fun m => torusE6Two_mtAut h2 m)) ?_
    rw [← hvε, torusE6Two_mtAut h2, mtAut_ofAdd]
    exact torusE6Two_not_mem_zpowers_of_not_smul h2 hmt
  · refine transport (sE6Two K) (ggE6TwoThree_normalizer_of_action (torusE6Two h2) (sE6Two K) msAut
      (fun m => torusE6Two_msAut h2 m)) ?_
    rw [← hvε, torusE6Two_msAut h2, msAut_ofAdd]
    exact torusE6Two_not_mem_zpowers_of_not_smul h2 hms

theorem largeEvenLabelAll_torusLift_E6_two {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 4 R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn1⟩ := h
  dsimp only at htag hn1
  subst htag
  subst hn1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, TableBExc.E6Three.ggTorusLift_E6_two⟩

theorem largeEvenLabelAll_noLine_e6_two_three {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLine 3 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn1⟩ := h
  dsimp only at htag hn1
  subst htag
  subst hn1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa only [pow_one] using hK
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  intro hs hna
  exact ggTorusNoLine_of_scNoLine Nat.prime_three (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK hφ)
    (ggCenterPrime_recipe_E6_two hK2 Nat.prime_three)
    (ggSCNoLine_of_mulEquiv (TableBExc.recipeEquiv .E6 K) (ggSCNoLine_adjoint_E6_two hK2))

theorem largeEvenLabelAll_torusLift_noLine_e6_two_three {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift 3 r R ∨ r = 0) ∧ GGTorusNoLine 3 r R I :=
  (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_E6_two h)
    (largeEvenLabelAll_noLine_e6_two_three hlab h)).mono fun _ _ _ _ ⟨hl, hn⟩ hs hna =>
      ⟨4, Or.inl hl, hn hs hna⟩

end Main

end CFSG.StandardType

end
