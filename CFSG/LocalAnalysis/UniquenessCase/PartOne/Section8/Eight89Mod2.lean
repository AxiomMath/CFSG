module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.GroupTheory.ChiefSectionPGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

private theorem k89m2_card_of_IsA6Z3 {Y : Type} [Group Y] (h : IsA6Z3 Y) : Nat.card Y = 1080 := by
  obtain ⟨-, hz, e⟩ := h
  have hq : Nat.card (Y ⧸ Subgroup.center Y) = 360 := by
    obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
  rw [hq, hz] at hcard
  omega

private theorem k89m2_mem_normalizer_zpowers {G : Type} [Group G] {g y : G}
    (hg : g * y = y * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
  have hc : Commute g y := hg
  have hfix : ∀ s ∈ Subgroup.zpowers y, g * s * g⁻¹ = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (hc.zpow_right k).mul_inv_cancel
  have hfix' : ∀ s ∈ Subgroup.zpowers y, g⁻¹ * s * g = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (hc.zpow_right k).inv_mul_cancel
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hfix h hh]
    exact hh
  · intro hh
    have h2 : h = g * h * g⁻¹ := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g * h * g⁻¹ := hfix' _ hh
    rw [h2]
    exact hh

private theorem k89m2_le_normalizer_centralizer {G : Type} [Group G] {K T : Subgroup G}
    (hKT : K ≤ normalizer (T : Set G)) :
    K ≤ normalizer (centralizer (T : Set G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro t ht
    have hkt : k⁻¹ * t * k ∈ T := by
      have h := (Subgroup.mem_normalizer_iff.mp (hKT hk)) (k⁻¹ * t * k)
      rw [show k * (k⁻¹ * t * k) * k⁻¹ = t by group] at h
      exact h.mpr ht
    calc t * (k * x * k⁻¹) = k * ((k⁻¹ * t * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * t * k)) * k⁻¹ := by rw [hx (k⁻¹ * t * k) hkt]
      _ = (k * x * k⁻¹) * t := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro t ht
    have hkt : k * t * k⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hKT hk) t).mp ht
    have h2 := hx (k * t * k⁻¹) hkt
    have h4 : k⁻¹ * ((k * x * k⁻¹) * (k * t * k⁻¹)) * k = x * t := by group
    have h5 : k⁻¹ * ((k * t * k⁻¹) * (k * x * k⁻¹)) * k = t * x := by group
    rw [← h2, h5] at h4
    exact h4

private noncomputable def k89m2_conjRep {actors target : Type*} [Group actors] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive target)] (action : actors →* MulAut target) :
    actors →* Module.End (ZMod prime) (Additive target) where
  toFun actor :=
    AddMonoidHom.toZModLinearMap prime (MonoidHom.toAdditive (action actor).toMonoidHom)
  map_one' := by
    ext element
    change Additive.ofMul (action 1 element.toMul) = element
    rw [map_one]
    rfl
  map_mul' first second := by
    ext element
    change Additive.ofMul (action (first * second) element.toMul) =
      Additive.ofMul (action first (action second element.toMul))
    rw [map_mul]
    rfl

private theorem k89m2_conjRep_apply {actors target : Type*} [Group actors] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive target)] (action : actors →* MulAut target)
    (actor : actors) (element : target) :
    k89m2_conjRep prime action actor (Additive.ofMul element) =
      Additive.ofMul (action actor element) := rfl

private theorem k89m2_normalizer_smul_coe {G : Type} [Group G] {H : Subgroup G}
    (g : Subgroup.normalizer (H : Set G)) (h : H) :
    (((g • h : H) : G)) = (g : G) * (h : G) * (g : G)⁻¹ := rfl

private theorem k89m2_action_coe {G : Type} [Group G] {K A : Subgroup G}
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (k : ↥K) (a : ↥A) :
    ((((A.normalizerMonoidHom.comp (Subgroup.inclusion hKA)) k) a : ↥A) : G) =
      (k : G) * (a : G) * (k : G)⁻¹ := rfl

private theorem k89m2_card_Z {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    {ω : G} (hω : Set889 D L P ω) (hF : Facts889 D L P ω) :
    Nat.card (ZOf (P ⊓ L)) = 3 := by
  classical
  set K : Subgroup G := K889 L ω with hK
  set Z : Subgroup G := ZOf (P ⊓ L) with hZ
  set T : Subgroup ↥K := CFSG.pCore 2 ↥K with hT
  have hZQ : Z ≤ P ⊓ L := by rw [hZ]; exact inf_le_left
  have hZK : Z ≤ K := hZQ.trans (by rw [hK]; exact hF.qLe)
  have hZP : Z ≤ P := hZQ.trans inf_le_left
  have hZ3 : IsPGroup 3 Z := IsPGroup.to_le (CFSG.ABGLocalTools.IsSylowOf.isPGroup hω.sylow3) hZP
  let mkZr : ↥Z →* Bar2 K := (QuotientGroup.mk' T).comp (Subgroup.inclusion hZK)
  have hrange : mkZr.range = Subgroup.center (Bar2 K) := by
    rw [show mkZr = (QuotientGroup.mk' T).comp (Subgroup.inclusion hZK) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range]
    simpa [hZ, hK, hT] using hF.centerEq
  have hker : mkZr.ker = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [Subgroup.mem_bot]
    have hxT : (⟨(x : G), hZK x.2⟩ : ↥K) ∈ T := by
      have hx' : QuotientGroup.mk' T (⟨(x : G), hZK x.2⟩ : ↥K) = 1 := hx
      exact (QuotientGroup.eq_one_iff (N := T) _).mp hx'
    have hxTg : (x : G) ∈ T.map K.subtype := Subgroup.mem_map_of_mem K.subtype hxT
    have hxZ : (x : G) ∈ Z := x.2
    have hdisj : T.map K.subtype ⊓ Z = ⊥ :=
      disjoint_iff.mp (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _
        (IsPGroup.map CFSG.pCore_isPGroup K.subtype) hZ3)
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact ⟨hxTg, hxZ⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hinj : Function.Injective mkZr := (MonoidHom.ker_eq_bot_iff mkZr).mp hker
  have hcardZ : Nat.card Z = 3 := by
    have h1 : Nat.card Z = Nat.card mkZr.range := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (f := mkZr) hinj,
        Subgroup.card_top]
    rw [h1, hrange]
    exact hF.alt6.2.1
  simpa [hZ] using hcardZ

private theorem k89m2_minimal_elementary {G : Type} [Group G] [Finite G]
    {K U : Subgroup G} (hU2 : IsPGroup 2 U) (hUne : U ≠ ⊥)
    (hKN : K ≤ normalizer (U : Set G)) :
    ∃ A : Subgroup G, A ≤ U ∧ A ≠ ⊥ ∧ K ≤ normalizer (A : Set G) ∧
      (∀ W : Subgroup G, W ≤ U → W ≠ ⊥ → K ≤ normalizer (W : Set G) → W ≤ A → W = A) ∧
      IsPGroup 2 A ∧ (∀ x ∈ A, x ^ 2 = 1) ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, ⟨hAU, hAne, hKNA⟩, hAmin⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup.exists_minimal_subgroup
      (fun A : Subgroup G => A ≤ U ∧ A ≠ ⊥ ∧ K ≤ normalizer (A : Set G))
      ⟨U, le_rfl, hUne, hKN⟩
  have hA2 : IsPGroup 2 A := hU2.to_le hAU
  have hexp : ∀ x ∈ A, x ^ 2 = 1 := by
    let Ω : Subgroup G := Subgroup.closure {x ^ 2 | x ∈ A}
    have hΩA : Ω ≤ A := by
      refine (Subgroup.closure_le (K := A)).2 ?_
      rintro _ ⟨x, hx, rfl⟩
      exact A.pow_mem hx 2
    have hΩlt : Ω < A := by
      have h := CFSG.GroupTheory.sup_pow_closure_lt_of_isPGroup (G := G) (p := 2)
        (X := A) (V := ⊥) bot_le hA2 (by simpa using hAne.symm)
      simpa using h
    have hKΩ : K ≤ normalizer (Ω : Set G) :=
      CFSG.GroupTheory.le_normalizer_closure_pow (n := 2) hKNA
    have hΩbot : Ω = ⊥ := by
      by_contra hΩne
      exact absurd (hAmin Ω ⟨hΩA.trans hAU, hΩne, hKΩ⟩ hΩA) hΩlt.ne
    intro x hx
    have hxΩ : x ^ 2 ∈ Ω := Subgroup.subset_closure ⟨x, hx, rfl⟩
    rw [hΩbot] at hxΩ
    simpa using hxΩ
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hx' : x * x = 1 := by simpa [pow_two] using hexp x hx
    have hy' : y * y = 1 := by simpa [pow_two] using hexp y hy
    have h1 : (x * y) * (x * y) = 1 := by
      simpa [pow_two] using hexp (x * y) (A.mul_mem hx hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right hy', inv_eq_of_mul_eq_one_right hx']
  exact ⟨A, hAU, hAne, hKNA,
    (fun W hWU hWne hKNW hWA => hAmin W ⟨hWU, hWne, hKNW⟩ hWA), hA2, hexp, hcomm⟩

theorem s889_mod2 {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h885 : R885 D) (h887 : R887 D) (hFacts : AllFacts889 D) (hcore : Alt6ModTwoCore) :
    S889Mod2 D := by
  intro L P ω hω U hU2 hUne hKN
  by_contra hUM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hFactsω := hFacts L P ω hω
  have hS := hω.set880
  have h885' := h885 L P hS
  set K : Subgroup G := K889 L ω with hK
  set Z : Subgroup G := ZOf (P ⊓ L) with hZ
  have hqLe : P ⊓ L ≤ K := by rw [hK]; exact hFactsω.qLe
  have hA6K : IsA6Z3 (Bar2 K) := by simpa [hK] using hFactsω.alt6
  have hcenterEq : (Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) =
      Subgroup.center (Bar2 K) := by
    have h := hFactsω.centerEq
    rw [← hZ, ← hK] at h
    exact h
  have hKLM : K ≤ D.M := by
    rw [hK]; exact (r889_K889_le_left L ω).trans (r889_le_M hS)
  have hZcard : Nat.card Z = 3 := by simpa [hZ] using k89m2_card_Z hω hFactsω
  have hZQ : Z ≤ P ⊓ L := by rw [hZ]; exact inf_le_left
  have hZK : Z ≤ K := hZQ.trans hqLe
  have hZP : Z ≤ P := hZQ.trans inf_le_left
  have hZ3 : IsPGroup 3 Z :=
    IsPGroup.to_le (CFSG.ABGLocalTools.IsSylowOf.isPGroup hω.sylow3) hZP
  obtain ⟨z, hzZ, hz3⟩ : ∃ z ∈ Z, orderOf z = 3 := by
    have h3dvd : 3 ∣ Nat.card Z := by rw [hZcard]
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 h3dvd
    exact ⟨(z : G), z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩
  have hzK : z ∈ K := hZK hzZ
  have hzp : Subgroup.zpowers z = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzZ) ?_
    rw [Nat.card_zpowers, hz3, hZcard]
  obtain ⟨f, hf5⟩ : ∃ f : ↥K, orderOf f = 5 := by
    have hcard : Nat.card (Bar2 K) = 1080 := k89m2_card_of_IsA6Z3 hA6K
    have hdvd : 5 ∣ Nat.card ↥K := by
      have h1 : 5 ∣ Nat.card (Bar2 K) := by rw [hcard]; norm_num
      exact h1.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))
    exact exists_prime_orderOf_dvd_card' 5 hdvd
  have hfM : (f : G) ∈ D.M := hKLM f.2
  have hf5G : orderOf (f : G) = 5 := by rw [Subgroup.orderOf_coe, hf5]
  have hsp : IsStronglyPEmbedded 5 D.M := by
    have hns : ¬ Group.IsSolvable ↥D.M :=
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hS.mem
    have h5 : (5 : ℕ) ∈ D.sig := by rw [h885'.2.1]; exact Set.mem_singleton 5
    exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns h5
  have hCz : centralizer ({z} : Set G) ≤ D.M := by
    intro g hg
    have hgz : g * z = z * g :=
      ((Subgroup.mem_centralizer_iff.mp hg) z (Set.mem_singleton z)).symm
    have hgn : g ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
      k89m2_mem_normalizer_zpowers hgz
    rw [hzp, hZ] at hgn
    exact h887 L P hS hgn
  have hCUz : U ⊓ centralizer ({z} : Set G) = ⊥ := by
    have hle : U ⊓ centralizer ({z} : Set G) ≤ U ⊓ D.M := inf_le_inf_left U hCz
    rw [hUM] at hle
    exact le_bot_iff.mp hle
  have hCf : centralizer ({(f : G)} : Set G) ≤ D.M :=
    r889_centralizer_le_of_five hsp hfM hf5G
  have hCUf : U ⊓ centralizer ({(f : G)} : Set G) = ⊥ := by
    have hle : U ⊓ centralizer ({(f : G)} : Set G) ≤ U ⊓ D.M := inf_le_inf_left U hCf
    rw [hUM] at hle
    exact le_bot_iff.mp hle
  have hKN' : K ≤ normalizer (U : Set G) := by rw [hK]; exact hKN
  obtain ⟨A, hAU, hAne, hKNA, hAmin, hA2, hAexp, hAcomm⟩ :=
    k89m2_minimal_elementary hU2 hUne hKN'
  set T : Subgroup ↥K := CFSG.pCore 2 ↥K with hT
  set Tg : Subgroup G := T.map K.subtype with hTg
  have hTg2 : IsPGroup 2 Tg := by
    rw [hTg, hT]
    exact IsPGroup.map CFSG.pCore_isPGroup K.subtype
  have hTgK : Tg ≤ K := by
    rw [hTg, hT]
    exact Subgroup.map_subtype_le _
  have hTgN : K ≤ normalizer (Tg : Set G) := by
    have hEq : Tg.subgroupOf K = T := by
      ext x
      rw [Subgroup.mem_subgroupOf, hTg]
      constructor
      · intro hx
        obtain ⟨t, ht, ht'⟩ := Subgroup.mem_map.mp hx
        have htx : t = x := Subtype.ext ht'
        exact htx ▸ ht
      · intro hx
        exact Subgroup.mem_map_of_mem K.subtype hx
    have hnorm : (Tg.subgroupOf K).Normal := by rw [hEq]; exact CFSG.pCore_normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hTgK).mp hnorm
  have hTgNcent : K ≤ normalizer (centralizer (Tg : Set G) : Set G) :=
    k89m2_le_normalizer_centralizer hTgN
  have hKNC : K ≤ normalizer ((A ⊓ centralizer (Tg : Set G) : Subgroup G) : Set G) :=
    fun x hx => r889_mem_normalizer_inf (hKNA hx) (hTgNcent hx)
  have hAnontriv : Nontrivial ↥A := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    exact ⟨a, 1, ha⟩
  have hcardA : 2 ∣ Nat.card ↥A := by
    obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hA2).mp hAnontriv
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  let actTg : ↥Tg →* ↥(normalizer (A : Set G)) :=
    Subgroup.inclusion (hTgK.trans hKNA)
  let : MulAction ↥Tg ↥A := MulAction.compHom (↥A) actTg
  obtain ⟨b, hbfix, hbne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point (p := 2) hTg2 ↥A hcardA
      (a := (1 : ↥A))
      (by
        intro a
        apply Subtype.ext
        rw [MulAction.compHom_smul_def, k89m2_normalizer_smul_coe]
        simp)
  have hbC : (b : G) ∈ A ⊓ centralizer (Tg : Set G) := by
    refine ⟨b.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro t ht
    have hfix := MulAction.mem_fixedPoints.mp hbfix (⟨t, ht⟩ : ↥Tg)
    have hcoe : (((⟨t, ht⟩ : ↥Tg) • b : ↥A) : G) = t * (b : G) * t⁻¹ := by
      rw [MulAction.compHom_smul_def]
      exact k89m2_normalizer_smul_coe (actTg ⟨t, ht⟩) b
    have hb1 : t * (b : G) * t⁻¹ = (b : G) := by
      have h := congrArg Subtype.val hfix
      rwa [hcoe] at h
    calc t * (b : G) = t * (b : G) * t⁻¹ * t := by group
      _ = (b : G) * t := by rw [hb1]
  have hCne : A ⊓ centralizer (Tg : Set G) ≠ ⊥ := by
    intro hbot
    have hb0 : (b : G) ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hbC
    exact hbne (Subtype.ext (Subgroup.mem_bot.mp hb0)).symm
  have hCeq : A ⊓ centralizer (Tg : Set G) = A :=
    hAmin (A ⊓ centralizer (Tg : Set G)) (inf_le_left.trans hAU) hCne hKNC inf_le_left
  have hAleCent : A ≤ centralizer (Tg : Set G) := hCeq ▸ inf_le_right
  let : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with
      mul_comm := fun x y => Subtype.ext (hAcomm x x.2 y y.2) }
  let W := Additive ↥A
  let : Module (ZMod 2) W := AddCommGroup.zmodModule (n := 2) fun x => by
    change Additive.ofMul (x.toMul ^ 2) = 0
    apply Additive.ext
    change x.toMul ^ 2 = 1
    apply Subtype.ext
    simpa using hAexp x.toMul x.toMul.2
  let action : ↥K →* MulAut ↥A := A.normalizerMonoidHom.comp (Subgroup.inclusion hKNA)
  let ρ : ↥K →* Module.End (ZMod 2) W := k89m2_conjRep 2 action
  have hρ_apply : ∀ (k : ↥K) (a : ↥A),
      ρ k (Additive.ofMul a) = Additive.ofMul (action k a) :=
    fun k a => k89m2_conjRep_apply 2 action k a
  have hTle_ker : T ≤ ρ.ker := by
    intro t ht
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro w
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective w
    rw [hρ_apply, Module.End.one_apply]
    have htTg : (t : G) ∈ Tg := by
      rw [hTg, hT]
      exact Subgroup.mem_map_of_mem K.subtype ht
    have hacomm : (t : G) * (a : G) = (a : G) * (t : G) :=
      (Subgroup.mem_centralizer_iff.mp (hAleCent a.2)) (t : G) htTg
    have haction : action t a = a := by
      apply Subtype.ext
      rw [k89m2_action_coe hKNA]
      calc (t : G) * (a : G) * (t : G)⁻¹ = (a : G) * (t : G) * (t : G)⁻¹ := by rw [hacomm]
        _ = (a : G) := by group
    exact congrArg Additive.ofMul haction
  let ρbar : Bar2 K →* Module.End (ZMod 2) W :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) ρ hTle_ker
  have hρbar_mk : ∀ k : ↥K, ρbar (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k) = ρ k :=
    fun k => rfl
  have hzbar_center : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨z, hzK⟩ ∈
      Subgroup.center (Bar2 K) := by
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨z, hzK⟩ ∈
        (Z.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzZ)
    rw [← hcenterEq]
    exact hmem
  have hzbar_ne : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨z, hzK⟩ ≠ 1 := by
    intro h1
    have hzT : (⟨z, hzK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) _).mp h1
    have hzTg : z ∈ Tg := by
      rw [hTg, hT]
      exact Subgroup.mem_map_of_mem K.subtype hzT
    have hzTg_ne : (⟨z, hzTg⟩ : ↥Tg) ≠ 1 := by
      intro hh
      have hz1 : z = 1 := by simpa using congrArg Subtype.val hh
      rw [hz1, orderOf_one] at hz3
      omega
    have h2dvd : 2 ∣ orderOf (⟨z, hzTg⟩ : ↥Tg) := hTg2.dvd_orderOf hzTg_ne
    have hord : orderOf (⟨z, hzTg⟩ : ↥Tg) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨z, hzTg⟩ : ↥Tg)]
      exact hz3
    rw [hord] at h2dvd
    omega
  have hzbar_fix : ∀ w : W, ρbar (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨z, hzK⟩) w = w →
      w = 0 := by
    intro w hw
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective w
    have h1 : ρ ⟨z, hzK⟩ (Additive.ofMul a) = Additive.ofMul a := by
      rw [← hρbar_mk]
      exact hw
    rw [hρ_apply] at h1
    have haction : action ⟨z, hzK⟩ a = a := Additive.ofMul.injective h1
    have hcom : z * (a : G) * z⁻¹ = (a : G) := by
      have h := congrArg Subtype.val haction
      rw [k89m2_action_coe hKNA] at h
      exact h
    have haz : (a : G) ∈ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      calc z * (a : G) = z * (a : G) * z⁻¹ * z := by group
        _ = (a : G) * z := by rw [hcom]
    have hmem : (a : G) ∈ U ⊓ centralizer ({z} : Set G) := ⟨hAU a.2, haz⟩
    rw [hCUz] at hmem
    have ha1 : a = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem)
    rw [ha1]
    rfl
  have hfbar5 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) f) = 5 := by
    have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) f) ∣ orderOf f :=
      orderOf_map_dvd _ f
    rw [hf5] at hdvd
    have hne : QuotientGroup.mk' (CFSG.pCore 2 ↥K) f ≠ 1 := by
      intro h1
      have hfT : f ∈ CFSG.pCore 2 ↥K :=
        (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) _).mp h1
      have hfTg : (f : G) ∈ Tg := by
        rw [hTg, hT]
        exact Subgroup.mem_map_of_mem K.subtype hfT
      have hfTg_ne : (⟨(f : G), hfTg⟩ : ↥Tg) ≠ 1 := by
        intro hh
        have hf1 : (f : G) = 1 := by simpa using congrArg Subtype.val hh
        rw [hf1, orderOf_one] at hf5G
        omega
      have h2dvd : 2 ∣ orderOf (⟨(f : G), hfTg⟩ : ↥Tg) := hTg2.dvd_orderOf hfTg_ne
      have hord : orderOf (⟨(f : G), hfTg⟩ : ↥Tg) = 5 := by
        rw [← Subgroup.orderOf_coe (⟨(f : G), hfTg⟩ : ↥Tg)]
        exact hf5G
      rw [hord] at h2dvd
      omega
    rcases Nat.prime_five.eq_one_or_self_of_dvd _ hdvd with h1 | h5'
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h5'
  obtain ⟨w, hwne, hwfix⟩ :=
    hcore (Bar2 K) hA6K W ρbar (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨z, hzK⟩)
      hzbar_center hzbar_ne hzbar_fix (QuotientGroup.mk' (CFSG.pCore 2 ↥K) f) hfbar5
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective w
  have h1 : ρ f (Additive.ofMul a) = Additive.ofMul a := by
    rw [← hρbar_mk]
    exact hwfix
  rw [hρ_apply] at h1
  have haction : action f a = a := Additive.ofMul.injective h1
  have hcom : (f : G) * (a : G) * (f : G)⁻¹ = (a : G) := by
    have h := congrArg Subtype.val haction
    rw [k89m2_action_coe hKNA] at h
    exact h
  have haf : (a : G) ∈ centralizer ({(f : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc (f : G) * (a : G) = (f : G) * (a : G) * (f : G)⁻¹ * (f : G) := by group
      _ = (a : G) * (f : G) := by rw [hcom]
  have hmem : (a : G) ∈ U ⊓ centralizer ({(f : G)} : Set G) := ⟨hAU a.2, haf⟩
  rw [hCUf] at hmem
  have ha1 : a = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem)
  exact hwne (by rw [ha1]; rfl)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
