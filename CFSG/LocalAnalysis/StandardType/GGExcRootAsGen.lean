module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcRootAsElt
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoEndNode
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType.ExcRootAs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType TableBSymp

section General

variable {G : Type} [Group G]

theorem exists_le_inf_centralizer_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A V : Subgroup G} (hA : IsElemAbelian p A) (hA1 : A ≠ ⊥) (hV1 : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ B ≤ A, Nat.card A = p * Nat.card B ∧ V ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  classical
  have : CFSG.IsElementaryAbelian p ↥A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hA.2 a a.2) }
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA1
  let _ : MulDistribMulAction A V := Subgroup.conjMulDistribMulActionOfLeNormalizer A V hAV
  have hp : ¬ p ∣ Nat.card V := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := V) hp
  by_contra hcon
  push Not at hcon
  apply hV1
  have hle : ⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B V ≤ ⊥ := by
    refine iSup₂_le fun B hB => ?_
    have hRc : Nat.card A = p * Nat.card (B.map A.subtype) := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, ← hB, B.index_mul_card]
    have h := hcon (B.map A.subtype) (Subgroup.map_subtype_le B) hRc
    intro x hx
    rw [Subgroup.mem_bot]
    have hxR : (x : G) ∈ V ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hbx := congrArg Subtype.val (hx ⟨b, hb⟩)
      change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hbx
      calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
        _ = (x : G) * (b : G) := by rw [hbx]
    rw [h, Subgroup.mem_bot] at hxR
    exact Subtype.ext hxR
  rw [hgen, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro v hv
  have hv' : (⟨v, hv⟩ : V) ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
  rw [hle, Subgroup.mem_bot] at hv'
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hv'

theorem le_of_isPGroup_two_of_mul {X D U : Subgroup G} (hX3 : ∀ y ∈ X, y ^ 3 = 1)
    (hXD : X ≤ Subgroup.centralizer (D : Set G)) (hfac : ∀ c ∈ U, ∃ y ∈ X, ∃ d ∈ D, c = y * d)
    (hU : IsPGroup 2 U) : U ≤ D := by
  intro u hu
  obtain ⟨w, hw⟩ := (hU.powEquiv (n := 3) (by norm_num)).surjective ⟨u, hu⟩
  rw [IsPGroup.powEquiv_apply] at hw
  have hu' : u = (w : G) ^ 3 := by
    rw [← Subgroup.coe_pow, hw]
  obtain ⟨y, hy, d, hd, hwyd⟩ := hfac w w.2
  have hcomm : Commute y d := (Subgroup.mem_centralizer_iff.mp (hXD hy) d hd).symm
  rw [hu', hwyd, hcomm.mul_pow, hX3 y hy, one_mul]
  exact pow_mem hd 3

theorem largeEvenLayer_centralizer_eq_map_conj {t : G} (g : G) {D : Subgroup G}
    (hcen : Subgroup.centralizer ({g * t * g⁻¹} : Set G) = Subgroup.zpowers (g * t * g⁻¹) ⊔ D)
    (htD : Subgroup.zpowers (g * t * g⁻¹) ≤ Subgroup.centralizer (D : Set G))
    (hD : CFSG.IsQuasisimple D) :
    LargeEvenLayer (Subgroup.centralizer ({t} : Set G)) =
      D.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hTT : ∀ a ∈ Subgroup.zpowers (g * t * g⁻¹), ∀ b ∈ Subgroup.zpowers (g * t * g⁻¹),
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have hTD : ∀ a ∈ Subgroup.zpowers (g * t * g⁻¹), ∀ d ∈ D, a * d = d * a := fun a ha d hd =>
    (Subgroup.mem_centralizer_iff.mp (htD ha) d hd).symm
  obtain ⟨hlay, -⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem
    (H := Subgroup.centralizer ({g * t * g⁻¹} : Set G)) (D := D)
    (by rw [hcen]; exact le_sup_right)
    (fun a ha b hb => by
      rw [hcen] at ha hb
      exact TableBExc.commutator_mem_of_mem_sup hTT hTD ha hb) hD
  have ht : (MulAut.conj g⁻¹) (g * t * g⁻¹) = t := by
    rw [MulAut.conj_apply]
    group
  have hC : Subgroup.centralizer ({t} : Set G) =
      (Subgroup.centralizer ({g * t * g⁻¹} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [TableBSymp.map_centralizer_singleton, ht]
  rw [hC, largeEvenLayer_map_of_injective _ (MulAut.conj g⁻¹).injective, hlay]

theorem prime_mul_card_le_of_lt [Finite G] {p : ℕ} [Fact p.Prime] {A As : Subgroup G}
    (hA : IsElemAbelian p A) (hAs : IsElemAbelian p As) (hAAs : A < As) :
    p * Nat.card A ≤ Nat.card As := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hAs)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hA)
  have hp1 : 0 < p := (Fact.out : p.Prime).pos
  have ham : a < m := by
    by_contra h
    have h1 : Nat.card As ≤ Nat.card A := by
      rw [hm, ha]
      exact Nat.pow_le_pow_right hp1 (not_lt.mp h)
    exact hAAs.ne (Subgroup.eq_of_le_of_card_ge hAAs.le h1)
  rw [ha, hm, ← pow_succ']
  exact Nat.pow_le_pow_right hp1 ham

theorem ggEndNodeRootEltBigAs_of_rootFusion [Finite G] {r : ℕ} {J D : Subgroup G}
    (hfus : ∀ As B : Subgroup G, IsElemAbelian 3 As → 3 ^ (r + 1) ≤ Nat.card As → B ≤ As →
      3 ^ (r - 1) ≤ Nat.card B → ∃ t ∈ B, t ≠ 1 ∧ ∃ g : G, g * t * g⁻¹ ∈ J)
    (hcen : ∀ X : Subgroup G, X ≤ J → Nat.card X = 3 → IsCyclic X →
      Subgroup.centralizer (X : Set G) = X ⊔ D ∧ X ≤ Subgroup.centralizer (D : Set G) ∧
        ∀ c ∈ Subgroup.centralizer (X : Set G), ∃ y ∈ X, ∃ d ∈ D, c = y * d)
    (hD : CFSG.IsQuasisimple D) (hZ : Subgroup.center D = ⊥) (hbig : GGBigLayer D) :
    GGEndNodeRootEltBigAs 3 r G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro A As hA hAAs hAs _ hr h27 ⟨V, hV1, hV2, hAV⟩
  have hAs' : 3 ^ (r + 1) ≤ Nat.card As :=
    calc 3 ^ (r + 1) = 3 * 3 ^ r := pow_succ' 3 r
      _ ≤ 3 * Nat.card A := Nat.mul_le_mul_left 3 hr
      _ ≤ Nat.card As := prime_mul_card_le_of_lt hA hAs hAAs
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h27
    norm_num at h27
  obtain ⟨B, hBA, hcardB, hVB⟩ :=
    exists_le_inf_centralizer_ne_bot (by norm_num) hA hA1 hV1 hV2 hAV
  have hB : 3 ^ (r - 1) ≤ Nat.card B := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0]
      exact Nat.card_pos
    · have e : 3 ^ r = 3 * 3 ^ (r - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
  obtain ⟨t, htB, ht1, g, hg⟩ := hfus As B hAs hAs' (hBA.trans hAAs.le) hB
  have htA : t ∈ A := hBA htB
  have hX := TableBExcTwo.card_zpowers_conj_eq_three hA htA ht1 g
  obtain ⟨hcenX, hXD, hfac⟩ :=
    hcen (Subgroup.zpowers (g * t * g⁻¹)) (Subgroup.zpowers_le.mpr hg) hX inferInstance
  rw [TableBExcTwo.centralizer_zpowers_eq] at hcenX hfac
  have hend := TableBExcTwo.endNodeAt_of_conj_centralizer hA htA ht1 g hcenX hXD hD hZ
  have hlay := largeEvenLayer_centralizer_eq_map_conj g hcenX hXD hD
  have hx3 : (g * t * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hA.2 t htA, mul_one, mul_inv_cancel]
  have hX3 : ∀ y ∈ Subgroup.zpowers (g * t * g⁻¹), y ^ 3 = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, hx3, one_zpow]
  refine ⟨t, hend, fun _ => ?_, V ⊓ Subgroup.centralizer (B : Set G), ?_, hVB,
    hV2.to_le inf_le_left, ?_⟩
  ·
    rw [hlay]
    rcases hbig with h7 | h2
    · exact Or.inl (by rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective])
    · exact Or.inr (by rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective])
  ·
    rw [hlay]
    have hU2 : IsPGroup 2 ((V ⊓ Subgroup.centralizer (B : Set G)).map
        (MulAut.conj g).toMonoidHom) := (hV2.to_le inf_le_left).map _
    have hle := le_of_isPGroup_two_of_mul hX3 hXD (fun c hc => hfac c (by
      obtain ⟨u, hu, rfl⟩ := hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hut : u * t = t * u := (Subgroup.mem_centralizer_iff.mp hu.2 t htB).symm
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * u * g⁻¹ * (g * t * g⁻¹) = g * (u * t) * g⁻¹ := by group
        _ = g * (t * u) * g⁻¹ := by rw [hut]
        _ = g * t * g⁻¹ * (g * u * g⁻¹) := by group)) hU2
    intro u hu
    refine ⟨g * u * g⁻¹, hle ⟨u, hu, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  ·
    intro a ha
    have haC : a ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact TableB.IsElemAbelian.comm hA (hBA hb) ha
    have haV := Subgroup.mem_normalizer_iff.mp (hAV ha)
    have haN := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer haC)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at haV haN ⊢
    exact and_congr (haV h) (haN h)

end General

section Inner

variable
  {τ : Tag} {K : Type} [Field K]

theorem mem_range_conj_adjoint_E7_E8 (hτ : τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2)
    (φ : MulAut (adjointGroup τ K)) :
    φ ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.LieType.Chevalley.even_E7_E8_exact_inner_field_automorphism_normal_form (f := 1) le_rfl
      K (by rw [hK]; norm_num) τ hτ
  rw [← hker, MonoidHom.mem_ker]
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have h := FiniteField.pow_card_sub_one_eq_one c hc
      rw [← Nat.card_eq_fintype_card, hK] at h
      simpa using h
  refine RingEquiv.ext fun c => ?_
  show (Θ φ) c = c
  rcases h01 c with rfl | rfl
  · exact map_zero _
  · exact map_one _

theorem ggOutdiagPrime_recipe_E7_E8 [Finite K] (hτ : τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2)
    (p : ℕ) : GGOutdiagPrime p (TableBExc.RecipeGroup τ K) Set.univ := by
  intro φ _ _
  set e := TableBExc.recipeEquiv τ K with he
  obtain ⟨g, hg⟩ := mem_range_conj_adjoint_E7_E8 hτ hK ((e.symm.trans φ).trans e)
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h := congrArg (fun ψ : MulAut (adjointGroup τ K) => ψ (e x)) hg
  simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h]

theorem ggEndNodeRootAs_recipe_of_eltBigAs [Finite K] (hτ : τ = .E7 ∨ τ = .E8)
    (hK : Nat.card K = 2) {r : ℕ} (h : GGEndNodeRootEltBigAs 3 r (adjointGroup τ K)) :
    GGEndNodeRootAs 3 r (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) :=
  ggEndNodeRootAs_of_eltBigAs (ggOutdiagPrime_recipe_E7_E8 hτ hK 3)
    (TableBExc.center_recipeGroup_eq_bot τ K)
    (ggEndNodeRootEltBigAs_of_mulEquiv (TableBExc.recipeEquiv τ K).symm h)

theorem seven_dvd_card_perpLevi_E7 [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    7 ∣ Nat.card (CFSG.SeitzReduction.EPilot.perpLevi .E7 K) := by
  have hsc := (CFSG.SeitzReduction.E7Pilot.lieModel_perpLevi_E7 (f := 1)
    (by rw [hK]; norm_num)).statedClassicalModel (by decide)
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.2.2.1 rfl]
  decide +kernel

end Inner

end CFSG.StandardType.ExcRootAs
