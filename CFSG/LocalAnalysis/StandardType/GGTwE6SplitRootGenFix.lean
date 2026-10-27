module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapRankOneFixed
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
public import CFSG.RankThree.PartOne.KLAY.SL2
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotPositionFacts
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteB
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignCores
public import CFSG.RankThree.Chevalley.EvenFourCommutingSL2

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Blueprint.Chevalley.TwistTag
  CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot CFSG.SeitzReduction.TwistedE6Pilot
  CFSG.RankThree.PartOne.KLAY

variable {K : Type} [Field K]

private theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hP : A ⊔ B ≤
      { carrier := {x : G | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
        one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (one_mul 1)⟩
        mul_mem' := by
          rintro x y ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
          refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
          calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * (b₁ * b₂)) := by rw [mul_assoc]
            _ = a₁ * ((a₂ * b₁) * b₂) := by rw [mul_assoc]
            _ = a₁ * ((b₁ * a₂) * b₂) := by rw [(hcomm a₂ ha₂ b₁ hb₁).eq]
            _ = a₁ * (b₁ * (a₂ * b₂)) := by rw [mul_assoc]
            _ = a₁ * b₁ * (a₂ * b₂) := by rw [← mul_assoc]
        inv_mem' := by
          rintro x ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
          rw [mul_inv_rev, (hcomm a ha b hb).inv_inv.eq] } := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨a, ha, 1, B.one_mem, (mul_one a)⟩
    · intro b hb
      exact ⟨1, A.one_mem, b, hb, (one_mul b)⟩
  exact hP hx


private theorem exists_unit_orbitField_orderOf {K : Type} [Field K] (σ : K →+* K) {p : ℕ}
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζσ : σ (ζ : K) = ζ)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    ∃ ζL : (orbitField TwistTag.E6 K σ a)ˣ, orderOf ζL = p := by
  have hfix : ∀ n : ℕ, (σ ^ n) (ζ : K) = ζ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        simp only [RingHom.coe_mul, Function.comp_apply]
        rw [hζσ, ih]
  have hζmem : (ζ : K) ∈ orbitField TwistTag.E6 K σ a :=
    (mem_orbitField).2 (hfix _)
  let ζL : (orbitField TwistTag.E6 K σ a)ˣ :=
    Units.mk0 ⟨(ζ : K), hζmem⟩ (by
      intro h
      exact ζ.ne_zero (congrArg Subtype.val h))
  refine ⟨ζL, ?_⟩
  have h1 : orderOf ((ζL : orbitField TwistTag.E6 K σ a) : K) =
      orderOf (ζL : orbitField TwistTag.E6 K σ a) :=
    orderOf_injective (Subfield.subtype (orbitField TwistTag.E6 K σ a)).toMonoidHom
      (Subfield.subtype (orbitField TwistTag.E6 K σ a)).injective
      (ζL : orbitField TwistTag.E6 K σ a)
  have h2 : orderOf (ζL : orbitField TwistTag.E6 K σ a) = orderOf ζL := orderOf_units
  have h3 : ((ζL : orbitField TwistTag.E6 K σ a) : K) = (ζ : K) := rfl
  rw [h3, orderOf_units, hζo] at h1
  rw [← h2]
  exact h1.symm

private theorem four_le_card_orbitField [Finite K] (σ : K →+* K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζσ : σ (ζ : K) = ζ)
    (a : Fin TwistTag.E6.foldedTag.rank) : 4 ≤ Nat.card (orbitField TwistTag.E6 K σ a) := by
  obtain ⟨ζL, hζL⟩ := exists_unit_orbitField_orderOf σ hζo hζσ a
  haveI : Finite (orbitField TwistTag.E6 K σ a) := Subtype.finite
  have hdvd : p ∣ Nat.card (orbitField TwistTag.E6 K σ a)ˣ := hζL ▸ orderOf_dvd_natCard ζL
  have hp_le : p ≤ Nat.card (orbitField TwistTag.E6 K σ a)ˣ :=
    Nat.le_of_dvd Nat.card_pos hdvd
  have hu : Nat.card (orbitField TwistTag.E6 K σ a)ˣ =
      Nat.card (orbitField TwistTag.E6 K σ a) - 1 := Nat.card_units (orbitField TwistTag.E6 K σ a)
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hpos : 0 < Nat.card (orbitField TwistTag.E6 K σ a) := Nat.card_pos
  omega

theorem orbitRankOneGroup_le_rootSpan_twE6
    (σ : K →+* K) (a : Fin Tag.F4.rank) :
    orbitRankOneGroup TwistTag.E6 K σ a ≤
      rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) := by
  let a' : Fin TwistTag.E6.foldedTag.rank := a
  change orbitRankOneGroup TwistTag.E6 K σ a' ≤
    rootSpan TwistTag.E6.tag K
      (signedSimpleRoots (↑(TwistTag.E6.orbit a') : Set (Fin TwistTag.E6.tag.rank)))
  change Subgroup.closure (Set.range (fun c : orbitField TwistTag.E6 K σ a' =>
      (orbitX TwistTag.E6 K σ a' c : ModGL TwistTag.E6.tag K)) ∪
    Set.range (fun c : orbitField TwistTag.E6 K σ a' =>
      (orbitY TwistTag.E6 K σ a' c : ModGL TwistTag.E6.tag K))) ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · change (orbitX TwistTag.E6 K σ a' c : ModGL TwistTag.E6.tag K) ∈ _
    rw [coe_orbitX a' c]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rw [← closure_xUnit_yUnit_eq_rootSpan]
    exact Subgroup.subset_closure
      ⟨_, perm_pow_mem_orbit TwistTag.E6 (orbitMin_mem TwistTag.E6 a') k, _,
        Or.inl rfl⟩
  · change (orbitY TwistTag.E6 K σ a' c : ModGL TwistTag.E6.tag K) ∈ _
    rw [coe_orbitY a' c]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rw [← closure_xUnit_yUnit_eq_rootSpan]
    exact Subgroup.subset_closure
      ⟨_, perm_pow_mem_orbit TwistTag.E6 (orbitMin_mem TwistTag.E6 a') k, _,
        Or.inr rfl⟩

section Certificates


private theorem range_rankOneHom_inf_eq_bot_twE6 [CharP K 2]
    {a : Fin TwistTag.E6.foldedTag.rank} {i j : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ TwistTag.E6.orbit a) (hj : j ∈ TwistTag.E6.orbit a) (hij : i ≠ j) :
    (rankOneHom TwistTag.E6 K i).range ⊓ (rankOneHom TwistTag.E6 K j).range = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨⟨g, rfl⟩, ⟨h, hzh⟩⟩
  have hcomm : ∀ g' : SL2 K, Commute (rankOneHom TwistTag.E6 K i g)
      (rankOneHom TwistTag.E6 K i g') := by
    intro g'
    have hc := commute_rankOneHom (a := a) hj hi (Ne.symm hij) h g'
    rwa [hzh] at hc
  have hcenter : g ∈ Subgroup.center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g'
    apply rankOneHom_injective_of_charTwo TwistTag.E6 i
    rw [map_mul, map_mul, (hcomm g').eq]
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := CharTwo.sq_injective (by simpa using hr)
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  rw [Subgroup.mem_bot, hg1]
  exact map_one (rankOneHom TwistTag.E6 K i)


private theorem pair_mem_orbitRankOneGroup_twE6 [CharP K 2] (σ : K →+* K)
    {a : Fin TwistTag.E6.foldedTag.rank} {i j : Fin TwistTag.E6.tag.rank}
    (hij : i ≠ j) (hmin : TwistTag.E6.orbitMin a = i)
    (hcard : (TwistTag.E6.orbit a).card = 2)
    (hset : (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)) = {i, j})
    (hpi : TwistTag.E6.perm i = j) (hpj : TwistTag.E6.perm j = i)
    {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) ⊓
      twistedFixedGroup TwistTag.E6 K σ) :
    x ∈ orbitRankOneGroup TwistTag.E6 K σ a := by
  have hminmem : i ∈ TwistTag.E6.orbit a :=
    hmin ▸ orbitMin_mem TwistTag.E6 a
  have hjmem : j ∈ TwistTag.E6.orbit a := by
    have h := CFSG.Blueprint.Chevalley.TwistTag.perm_mem_orbit TwistTag.E6 hminmem
    rwa [hpi] at h
  have hQle : rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) ≤
      (rankOneHom TwistTag.E6 K i).range ⊔ (rankOneHom TwistTag.E6 K j).range := by
    rw [← closure_xUnit_yUnit_eq_rootSpan, hset]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, c, rfl | rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with hk | hk
      · rw [hk]; exact Subgroup.mem_sup_left ⟨uSL c, rankOneHom_uSL i c⟩
      · rw [hk]; exact Subgroup.mem_sup_right ⟨uSL c, rankOneHom_uSL j c⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with hk | hk
      · rw [hk]; exact Subgroup.mem_sup_left ⟨vSL c, rankOneHom_vSL i c⟩
      · rw [hk]; exact Subgroup.mem_sup_right ⟨vSL c, rankOneHom_vSL j c⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_mul_of_mem_sup_of_commute
    (A := (rankOneHom TwistTag.E6 K i).range)
    (B := (rankOneHom TwistTag.E6 K j).range)
    (fun p hp q hq => by
      obtain ⟨g, rfl⟩ := hp
      obtain ⟨h, rfl⟩ := hq
      exact commute_rankOneHom (a := a) hminmem hjmem hij g h)
    (hQle hx.1)
  obtain ⟨g, rfl⟩ := hp
  obtain ⟨h, rfl⟩ := hq
  have hFx : twistHom TwistTag.E6 K σ x = x :=
    ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6) (K := K) (σ := σ)).1 hx.2).2
  rw [← hpq] at hFx
  rw [map_mul, twistHom_rankOneHom' TwistTag.E6 σ i g,
    twistHom_rankOneHom' TwistTag.E6 σ j h, hpi, hpj] at hFx
  have hcommCD : Commute (rankOneHom TwistTag.E6 K i (Matrix.SpecialLinearGroup.map σ h))
      (rankOneHom TwistTag.E6 K j (Matrix.SpecialLinearGroup.map σ g)) :=
    commute_rankOneHom (a := a) hminmem hjmem hij _ _
  rw [← hcommCD.eq] at hFx
  have hEq : (rankOneHom TwistTag.E6 K i (Matrix.SpecialLinearGroup.map σ h))⁻¹ *
      rankOneHom TwistTag.E6 K i g =
      rankOneHom TwistTag.E6 K j (Matrix.SpecialLinearGroup.map σ g) *
        (rankOneHom TwistTag.E6 K j h)⁻¹ := by
    have h := congrArg
      (fun t => (rankOneHom TwistTag.E6 K i (Matrix.SpecialLinearGroup.map σ h))⁻¹ *
        t * (rankOneHom TwistTag.E6 K j h)⁻¹) hFx
    simpa [mul_assoc] using h.symm
  have hEq' : rankOneHom TwistTag.E6 K i ((Matrix.SpecialLinearGroup.map σ h)⁻¹ * g) =
      rankOneHom TwistTag.E6 K j (Matrix.SpecialLinearGroup.map σ g * h⁻¹) := by
    simpa only [map_mul, map_inv] using hEq
  have hmem : rankOneHom TwistTag.E6 K i ((Matrix.SpecialLinearGroup.map σ h)⁻¹ * g) ∈
      (rankOneHom TwistTag.E6 K i).range ⊓ (rankOneHom TwistTag.E6 K j).range := by
    refine Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, ?_⟩
    rw [hEq']
    exact ⟨_, rfl⟩
  have hbot := range_rankOneHom_inf_eq_bot_twE6 (K := K) (a := a) (i := i) (j := j)
    hminmem hjmem hij
  rw [hbot, Subgroup.mem_bot] at hmem
  have hg : g = Matrix.SpecialLinearGroup.map σ h := by
    have h1 : (Matrix.SpecialLinearGroup.map σ h)⁻¹ * g = 1 :=
      rankOneHom_injective_of_charTwo TwistTag.E6 i (by simpa using hmem)
    exact (inv_mul_eq_one.mp h1).symm
  have hh : h = Matrix.SpecialLinearGroup.map σ g := by
    have hmem' : rankOneHom TwistTag.E6 K j (Matrix.SpecialLinearGroup.map σ g * h⁻¹) = 1 := by
      rw [← hEq']
      exact hmem
    have h1 : Matrix.SpecialLinearGroup.map σ g * h⁻¹ = 1 :=
      rankOneHom_injective_of_charTwo TwistTag.E6 j (by simpa using hmem')
    exact (mul_inv_eq_one.mp h1).symm
  have hσ2 : g = Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ g) := by
    rw [hh] at hg
    exact hg
  have hmemL : ∀ p q, ((g : Matrix (Fin 2) (Fin 2) K) p q) ∈
      orbitField TwistTag.E6 K σ a := by
    intro p q
    rw [mem_orbitField, hcard]
    have h := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) p q) hσ2
    simpa [pow_two, Matrix.SpecialLinearGroup.map_apply_coe] using h.symm
  set g' : SL2 (orbitField TwistTag.E6 K σ a) :=
    ⟨Matrix.of fun p q => ⟨(g : Matrix (Fin 2) (Fin 2) K) p q, hmemL p q⟩, by
      apply Subtype.val_injective
      have h1 := g.2
      rw [Matrix.det_fin_two] at h1 ⊢
      simpa using h1⟩ with hg'def
  have hmap : Matrix.SpecialLinearGroup.map (orbitField TwistTag.E6 K σ a).subtype g' = g := by
    ext p q
    rfl
  rw [orbitRankOneGroup, ← orbitRankOneHom_range]
  refine ⟨g', ?_⟩
  rw [orbitRankOneHom_apply, hcard, hmin]
  have hrange : List.range 2 = [0, 1] := by decide
  rw [hrange]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
    pow_one, Equiv.Perm.coe_one, id_eq]
  have h0 : (RingHom.comp (1 : K →+* K) (orbitField TwistTag.E6 K σ a).subtype) =
      (orbitField TwistTag.E6 K σ a).subtype := by
    ext x
    rfl
  have h1 : Matrix.SpecialLinearGroup.map (σ.comp (orbitField TwistTag.E6 K σ a).subtype) g' =
      Matrix.SpecialLinearGroup.map σ
        (Matrix.SpecialLinearGroup.map (orbitField TwistTag.E6 K σ a).subtype g') := by
    ext p q
    rfl
  rw [h0, h1, hmap, hpi, ← hh]
  exact hpq


private theorem singleton_mem_orbitRankOneGroup_twE6 [CharP K 2] (σ : K →+* K)
    {a : Fin TwistTag.E6.foldedTag.rank} {i : Fin TwistTag.E6.tag.rank}
    (hmin : TwistTag.E6.orbitMin a = i) (hcard : (TwistTag.E6.orbit a).card = 1)
    (hset : (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)) = {i})
    (hpi : TwistTag.E6.perm i = i)
    {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) ⊓
      twistedFixedGroup TwistTag.E6 K σ) :
    x ∈ orbitRankOneGroup TwistTag.E6 K σ a := by
  have hQle : rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) ≤
      (rankOneHom TwistTag.E6 K i).range := by
    rw [← closure_xUnit_yUnit_eq_rootSpan, hset]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, c, rfl | rfl⟩
    · simp only [Set.mem_singleton_iff] at hk
      rw [hk]
      exact ⟨uSL c, rankOneHom_uSL i c⟩
    · simp only [Set.mem_singleton_iff] at hk
      rw [hk]
      exact ⟨vSL c, rankOneHom_vSL i c⟩
  obtain ⟨g, rfl⟩ := hQle hx.1
  have hF : twistHom TwistTag.E6 K σ (rankOneHom TwistTag.E6 K i g) =
      rankOneHom TwistTag.E6 K i g :=
    ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6) (K := K) (σ := σ)).1 hx.2).2
  rw [twistHom_rankOneHom' TwistTag.E6 σ i g, hpi] at hF
  have hg : Matrix.SpecialLinearGroup.map σ g = g :=
    rankOneHom_injective_of_charTwo TwistTag.E6 i hF
  have hmemL : ∀ p q, ((g : Matrix (Fin 2) (Fin 2) K) p q) ∈
      orbitField TwistTag.E6 K σ a := by
    intro p q
    rw [mem_orbitField, hcard, pow_one]
    have h := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) p q) hg
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h
  set g' : SL2 (orbitField TwistTag.E6 K σ a) :=
    ⟨Matrix.of fun p q => ⟨(g : Matrix (Fin 2) (Fin 2) K) p q, hmemL p q⟩, by
      apply Subtype.val_injective
      have h1 := g.2
      rw [Matrix.det_fin_two] at h1 ⊢
      simpa using h1⟩ with hg'def
  have hmap : Matrix.SpecialLinearGroup.map (orbitField TwistTag.E6 K σ a).subtype g' = g := by
    ext p q
    rfl
  rw [orbitRankOneGroup, ← orbitRankOneHom_range]
  refine ⟨g', ?_⟩
  rw [orbitRankOneHom_apply, hcard, hmin]
  simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    pow_zero, Equiv.Perm.coe_one, id_eq]
  have h0 : (RingHom.comp (1 : K →+* K) (orbitField TwistTag.E6 K σ a).subtype) =
      (orbitField TwistTag.E6 K σ a).subtype := by
    ext x
    rfl
  rw [h0, hmap]


theorem orbitRankOneHom_injective_twE6 [CharP K 2] (σ : K →+* K) (a : Fin Tag.F4.rank) :
    Function.Injective (orbitRankOneHom TwistTag.E6 K σ a) :=
  CFSG.RankThree.Chevalley.injective_of_ker_scalar_of_charTwo
    fun _ hg => eq_smul_one_of_mem_ker_orbitRankOneHom hg

theorem rootSpan_inf_twistedFixedGroup_le_twE6 [CharP K 2] (σ : K →+* K) (a : Fin Tag.F4.rank) :
    rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) ⊓
      twistedFixedGroup TwistTag.E6 K σ ≤ orbitRankOneGroup TwistTag.E6 K σ a := by
  fin_cases a
  · let a' : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩
    change rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a') : Set (Fin TwistTag.E6.tag.rank))) ⊓
      twistedFixedGroup TwistTag.E6 K σ ≤ orbitRankOneGroup TwistTag.E6 K σ a'
    intro x hx
    exact pair_mem_orbitRankOneGroup_twE6 σ
      (a := a') (i := ⟨0, by decide⟩) (j := ⟨5, by decide⟩)
      (by decide) (by decide) (by decide)
      (by
        have h : TwistTag.E6.orbit a' =
            ({⟨0, by decide⟩, ⟨5, by decide⟩} : Finset (Fin TwistTag.E6.tag.rank)) := by
          decide
        rw [h]
        simp)
      (by decide) (by decide) hx
  · let a' : Fin TwistTag.E6.foldedTag.rank := ⟨1, by decide⟩
    change rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a') : Set (Fin TwistTag.E6.tag.rank))) ⊓
      twistedFixedGroup TwistTag.E6 K σ ≤ orbitRankOneGroup TwistTag.E6 K σ a'
    intro x hx
    exact pair_mem_orbitRankOneGroup_twE6 σ
      (a := a') (i := ⟨2, by decide⟩) (j := ⟨4, by decide⟩)
      (by decide) (by decide) (by decide)
      (by
        have h : TwistTag.E6.orbit a' =
            ({⟨2, by decide⟩, ⟨4, by decide⟩} : Finset (Fin TwistTag.E6.tag.rank)) := by
          decide
        rw [h]
        simp)
      (by decide) (by decide) hx
  · let a' : Fin TwistTag.E6.foldedTag.rank := ⟨2, by decide⟩
    change rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a') : Set (Fin TwistTag.E6.tag.rank))) ⊓
      twistedFixedGroup TwistTag.E6 K σ ≤ orbitRankOneGroup TwistTag.E6 K σ a'
    intro x hx
    exact singleton_mem_orbitRankOneGroup_twE6 σ
      (a := a') (i := ⟨3, by decide⟩)
      (by decide) (by decide)
      (by
        have h : TwistTag.E6.orbit a' =
            ({⟨3, by decide⟩} : Finset (Fin TwistTag.E6.tag.rank)) := by
          decide
        rw [h]
        simp)
      (by decide) hx
  · let a' : Fin TwistTag.E6.foldedTag.rank := ⟨3, by decide⟩
    change rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a') : Set (Fin TwistTag.E6.tag.rank))) ⊓
      twistedFixedGroup TwistTag.E6 K σ ≤ orbitRankOneGroup TwistTag.E6 K σ a'
    intro x hx
    exact singleton_mem_orbitRankOneGroup_twE6 σ
      (a := a') (i := ⟨1, by decide⟩)
      (by decide) (by decide)
      (by
        have h : TwistTag.E6.orbit a' =
            ({⟨1, by decide⟩} : Finset (Fin TwistTag.E6.tag.rank)) := by
          decide
        rw [h]
        simp)
      (by decide) hx

theorem isQuasisimple_orbitRankOneGroup_twE6 [Finite K] [CharP K 2] (σ : K →+* K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζσ : σ (ζ : K) = ζ)
    (a : Fin Tag.F4.rank) :
    CFSG.Assembly.IsQuasisimple ↥(orbitRankOneGroup TwistTag.E6 K σ a) := by
  let a' : Fin TwistTag.E6.foldedTag.rank := a
  change CFSG.Assembly.IsQuasisimple ↥(orbitRankOneGroup TwistTag.E6 K σ a')
  haveI : CharP (orbitField TwistTag.E6 K σ a') 2 :=
    Subfield.charP (orbitField TwistTag.E6 K σ a') 2
  have h4 := four_le_card_orbitField (K := K) σ hp hp2 hζo hζσ a'
  haveI : IsSimpleGroup (SL2 (orbitField TwistTag.E6 K σ a')) :=
    CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup h4
  have hnonab : ∃ x y : SL2 (orbitField TwistTag.E6 K σ a'), x * y ≠ y * x := by
    refine ⟨uSL 1, vSL 1, fun h => ?_⟩
    have h00 := congrArg (fun g : SL2 (orbitField TwistTag.E6 K σ a') =>
      (g : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.E6 K σ a')) 0 0) h
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, Matrix.mul_apply,
      Fin.sum_univ_two] at h00
  have hQn := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab
  have hQ : CFSG.Assembly.IsQuasisimple (SL2 (orbitField TwistTag.E6 K σ a')) :=
    ⟨hQn.1.1.commutator_eq_top, hQn.1.2.1⟩
  have e : SL2 (orbitField TwistTag.E6 K σ a') ≃*
      ↥(orbitRankOneGroup TwistTag.E6 K σ a') := by
    have e0 := MonoidHom.ofInjective
      (orbitRankOneHom_injective_twE6 (K := K) σ a')
    rwa [orbitRankOneHom_range] at e0
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv e.symm hQ

theorem dvd_card_orbitRankOneGroup_twE6 [CharP K 2] (σ : K →+* K) {p : ℕ} {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζσ : σ (ζ : K) = ζ) (a : Fin Tag.F4.rank) :
    p ∣ Nat.card ↥(orbitRankOneGroup TwistTag.E6 K σ a) := by
  let a' : Fin TwistTag.E6.foldedTag.rank := a
  change p ∣ Nat.card ↥(orbitRankOneGroup TwistTag.E6 K σ a')
  obtain ⟨ζL, hζL⟩ := exists_unit_orbitField_orderOf (K := K) σ hζo hζσ a'
  have hord : orderOf (orbitRankOneHom TwistTag.E6 K σ a' (HSLhom ζL)) = p := by
    rw [orderOf_injective (orbitRankOneHom TwistTag.E6 K σ a')
      (orbitRankOneHom_injective_twE6 (K := K) σ a')]
    rw [orderOf_injective HSLhom HSLhom_injective]
    exact hζL
  have hmem : orbitRankOneHom TwistTag.E6 K σ a' (HSLhom ζL) ∈
      orbitRankOneGroup TwistTag.E6 K σ a' := by
    rw [orbitRankOneGroup, ← orbitRankOneHom_range]
    exact ⟨HSLhom ζL, rfl⟩
  let y : ↥(orbitRankOneGroup TwistTag.E6 K σ a') := ⟨_, hmem⟩
  have hy : orderOf y = p := (Subgroup.orderOf_coe y).symm.trans hord
  exact hy ▸ orderOf_dvd_natCard y

end Certificates

end CFSG.StandardType.TwE6SplitRootGen

end
