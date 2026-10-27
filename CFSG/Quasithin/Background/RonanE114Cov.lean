module

public import CFSG.Quasithin.Vol2.Ch11SecOE7M
public import CFSG.Quasithin.Vol2.Ch11SecE3Sz
public import CFSG.Quasithin.Vol2.Ch11SecE3LieL2Up
public import CFSG.Quasithin.Vol2.Ch11SecE3LieSL2
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Vol2.Ch11SecOE7A
public import CFSG.Quasithin.Vol2.Ch11SecOE7B
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem3
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11 CFSG.Quasithin.Vol2.Ch11.SecE3
open CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
open scoped MatrixGroups commutatorElement

structure Rk1 (n : ℕ) (Y : Type) [Group Y] : Prop where
  simple : IsSimpleGroup Y
  nonabelian : ∃ x y : Y, x * y ≠ y * x
  rank : ∀ {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}, SecE3.AlmostSimple L →
    Nonempty (↥L ≃* Y) → ∀ {A : Subgroup Q}, IsElemAbelian 2 A → Nat.card A ≤ 2 ^ n

theorem Rk1.sl2 {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ n)
    (hF4 : 4 ≤ Nat.card F) : Rk1 n SL(2, F) where
  simple := E1.RootLift.isSimpleGroup_SL2 hF4
  nonabelian := SecE3.sl2_nonabelian
  rank := fun {_ _ _ _} hAS he {_} hA => by
    obtain ⟨e⟩ := he
    exact SecE3.card_le_of_isElemAbelian_sl2 hAS e hF hA

theorem Rk1.suzuki {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Rk1 (2 * a + 1) (CFSG.Blueprint.suzukiGroup a K) where
  simple := (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
  nonabelian := SecE3.suzuki_nonabelian ha hK
  rank := fun {Q _ _ L} hAS he {A} hA => by
    obtain ⟨e⟩ := he
    have hSz : CFSG.Blueprint.SuzukiModel ↥L 2 (2 * a + 1) :=
      ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨e⟩⟩
    have hOut := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 _
      hSz).1.2.2
    have := hAS.normal
    have hAL : A ≤ L := fun x hx =>
      SecE3.mem_of_pow_two_pow_eq_one hAS.centralizer_eq hOut (k := 1) (by simpa using hA.2 x hx)
    have hA' := SecE3.isElemAbelian_map e.toMonoidHom (SecE3.isElemAbelian_subgroupOf hA L)
    have h1 : Nat.card ↥((A.subgroupOf L).map e.toMonoidHom) = Nat.card A := by
      rw [Subgroup.card_map_of_injective e.injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
    rw [← h1, ← hK]
    exact SecE3.card_le_of_isElemAbelian_suzuki hK hA'

variable {G : Type} [Group G] [Finite G]

theorem isE_of_almostSimple_quot_gen {n : ℕ} {Y : Type} [Group Y] (hY : Rk1 n Y)
    {Q' : Type} [Group Q'] [Finite Q'] {T A K : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hτK : E1.tauOf ⊤ T A ≤ K)
    (hSyl : IsSylowIn 2 (T ⊓ K) K) (ψ : ↥K →* Q') (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) {L' : Subgroup Q'} (hAS : SecE3.AlmostSimple L')
    (eL : ↥L' ≃* Y) (hB : (A.subgroupOf K).map ψ ≠ ⊥) :
    E1.IsE n ⊤ T A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτT : E1.tauOf ⊤ T A ≤ T := E1.tauOf_le _ _ _
  have hAτ : A ≤ E1.tauOf ⊤ T A := le_sup_left.trans (E1.le_tauOf hT hAT hA)
  have hAK : A ≤ K := hAτ.trans hτK
  refine ⟨le_top, le_inf hτT hτK, hSyl, Or.inr ?_⟩
  have hO2 : CFSG.Open.pCore 2 Q' = ⊥ :=
    le_bot_iff.mp (E3.pCore_two_le_solvableRadical.trans hAS.solvableRadical_eq_bot.le)
  have hZC : E1.IsTwoClosed ((CFSG.Open.pCore 2 Q').comap ψ) := by
    rw [hO2, MonoidHom.comap_bot]
    exact ⟨ψ.ker, ⟨le_rfl, hker, by rw [Subgroup.relIndex_self]; norm_num⟩,
      by rw [Subgroup.subgroupOf_self]; infer_instance⟩
  have hSylQ : IsSylowIn 2 ((T ⊓ K).subgroupOf K) ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (H := K) inf_le_right le_rfl).mpr hSyl
    rwa [Subgroup.subgroupOf_self] at h
  have hBS : A.subgroupOf K ≤ (T ⊓ K).subgroupOf K := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hAT hx, hAK hx⟩
  have hCS : ψ.ker ≤ (T ⊓ K).subgroupOf K := by
    have h2 := B6.pCoreOf_two_le_of_isSylowTwoOf hSylQ
    rw [E1.pCoreOf_top_eq] at h2
    exact (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hker).trans h2
  have hres : twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) :=
    E1.twoResidual_eq_perfectCore_of_surjective ψ hψ hSylQ
      (fun M hSM hM => by rwa [sup_eq_left.mpr (hCS.trans hSM)] at hM)
      (by rw [hAS.twoResidual_eq, hAS.perfectCore_eq])
  refine ⟨E1.eTwo_of_surjective ψ hψ hZC hSylQ.2.1 hBS hres (hAS.eTwo hB), ?_⟩
  rw [← E1.card_barRad_eq_of_surjective ψ hψ (E1.isSolvable_ker_of_isTwoClosed ψ hZC)]
  unfold E1.barRad
  rw [Subgroup.card_map_of_injective (by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hAS.solvableRadical_eq_bot])]
  have hAψ : IsElemAbelian 2 ((A.subgroupOf K).map ψ) := by
    refine E1.isElemAbelian_map' ψ ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := E1.commute_of_isElemAbelian hA (Subgroup.mem_subgroupOf.mp x.2)
        (Subgroup.mem_subgroupOf.mp y.2)
      simpa using this
    · have := hA.2 _ (Subgroup.mem_subgroupOf.mp hx)
      exact Subtype.ext (by simpa using this)
  exact hY.rank hAS ⟨eL⟩ hAψ

omit [Finite G] in
theorem ker_eq_pCore_gen {Y : Type} [Group Y] [IsSimpleGroup Y] (hnab : ∃ x y : Y, x * y ≠ y * x)
    {X : Type*} [Group X] [Finite X] (φ : X →* Y) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : φ.ker = CFSG.Open.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_surjective φ hφ
  refine le_antisymm (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hker) ?_
  have h1 := CFSG.LieType.BorelTits.map_pCore_le 2 φ hφ
  have h2 : CFSG.Open.pCore 2 Y = ⊥ := by
    have : (CFSG.Open.pCore 2 Y).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 Y) with h | h
    · exact h
    · exfalso
      have hp := CFSG.LieType.BorelTits.pCore_isPGroup (G := Y) 2
      rw [h] at hp
      have hnil : Group.IsNilpotent Y := (hp.of_equiv Subgroup.topEquiv).isNilpotent
      have hsolv : Group.IsSolvable Y := inferInstance
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy ((IsSimpleGroup.comm_iff_isSolvable (G := Y)).mpr hsolv x y)
  rw [h2, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
  exact h1

theorem isE_sup_tauOf_of_quot_gen {n : ℕ} {Y : Type} [Group Y] (hY : Rk1 n Y)
    {T A X : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (φ : ↥X →* Y) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hτN : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (X : Set G)) (hL : IsSylowIn 2 (T ⊓ X) X)
    (hAC : ¬ ∀ a ∈ A, ∀ x ∈ X, ⁅a, x⁆ ∈ φ.ker.map X.subtype) :
    E1.IsE n ⊤ T A (X ⊔ E1.tauOf ⊤ T A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup Y := hY.simple
  set τ := E1.tauOf ⊤ T A with hτdef
  have hτT : τ ≤ T := E1.tauOf_le _ _ _
  have hT2 : IsPGroup 2 T := hT.2.1
  set K := X ⊔ τ with hKdef
  have hXK : X ≤ K := le_sup_left
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hτN
  have hSyl : IsSylowIn 2 (T ⊓ K) K := SecU1.Comp.isSylowIn_sup hT2 hτT hτN hL
  set R : Subgroup G := φ.ker.map X.subtype with hRdef
  have hRX : R ≤ X := Subgroup.map_subtype_le _
  have hRc : R = (CFSG.Open.pCore 2 ↥X).map X.subtype := by
    rw [hRdef, ker_eq_pCore_gen hY.nonabelian φ hφ hker]
  have hKR : K ≤ Subgroup.normalizer (R : Set G) := by
    have : (CFSG.Open.pCore 2 ↥X).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
    rw [hRc]
    exact hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hR2 : IsPGroup 2 R := hker.map X.subtype
  set XK := X.subgroupOf K with hXKdef
  set RK := R.subgroupOf K with hRKdef
  have hXKn : XK.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKN
  have hRKn : RK.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hRX.trans hXK)).mpr hKR
  have hRK2 : IsPGroup 2 RK := hR2.comap_of_injective K.subtype K.subtype_injective
  have hτ' : IsPGroup 2 ↥(τ.subgroupOf K) :=
    (hT2.to_le hτT).comap_of_injective K.subtype K.subtype_injective
  have hsup : XK ⊔ τ.subgroupOf K = ⊤ := (Subgroup.codisjoint_subgroupOf_sup X τ).eq_top
  have htwoK : ∀ q : ↥K, ∃ k : ℕ, q ^ 2 ^ k ∈ XK := fun q => by
    have hq : q ∈ XK ⊔ τ.subgroupOf K := hsup ▸ Subgroup.mem_top q
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hq
    obtain ⟨k, hk⟩ := hτ' ⟨z, hz⟩
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow,
      show z ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, QuotientGroup.mk_one]
  set π₁ := QuotientGroup.mk' RK with hπ₁
  have hπ₁s : Function.Surjective π₁ := QuotientGroup.mk'_surjective RK
  set Xt := XK.map π₁ with hXtdef
  have hXtn : Xt.Normal := hXKn.map π₁ hπ₁s
  set f₁ := π₁.subgroupMap XK with hf₁
  have hf₁s : Function.Surjective f₁ := π₁.subgroupMap_surjective XK
  set eX := Subgroup.subgroupOfEquivOfLe hXK with heX
  set f₂ : ↥XK →* Y := φ.comp eX.toMonoidHom with hf₂
  have hf₂s : Function.Surjective f₂ := hφ.comp eX.surjective
  have hkereq : f₁.ker = f₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : π₁ (x : ↥K) = 1 := congrArg Subtype.val hx
      rw [hπ₁, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRKdef,
        Subgroup.mem_subgroupOf] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hyx' : y = eX x := Subtype.ext hyx
      rw [hf₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hyx']
      exact hy
    · intro hx
      apply Subtype.ext
      change π₁ (x : ↥K) = 1
      rw [hπ₁, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRKdef,
        Subgroup.mem_subgroupOf]
      exact ⟨eX x, hx, rfl⟩
  let eXt : ↥Xt ≃* Y :=
    (QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁s).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkereq).trans
        (QuotientGroup.quotientKerEquivOfSurjective f₂ hf₂s))
  have : IsSimpleGroup ↥Xt := eXt.isSimpleGroup
  have hnabXt : ∃ x y : ↥Xt, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hY.nonabelian
    exact ⟨eXt.symm x, eXt.symm y, fun h => hxy (eXt.symm.injective (by
      rw [map_mul, map_mul, h]))⟩
  set Ct := Subgroup.centralizer (Xt : Set (↥K ⧸ RK)) with hCtdef
  have hZ := SecE3.center_eq_bot_of_simple hnabXt
  have hLC : Xt ⊓ Ct = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    have hc : (⟨x, hxX⟩ : ↥Xt) ∈ Subgroup.center ↥Xt := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hc)
  have hcent : ∀ q : ↥K ⧸ RK, (∀ l ∈ Xt, l * q = q * l) → q ∈ Ct := fun q h =>
    Subgroup.mem_centralizer_iff.mpr fun l hl => h l hl
  have htwo : ∀ q : ↥K ⧸ RK, ∃ k : ℕ, q ^ 2 ^ k ∈ Xt := fun q => by
    obtain ⟨y, rfl⟩ := hπ₁s q
    obtain ⟨k, hk⟩ := htwoK y
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_map_of_mem π₁ hk⟩
  have hAS := SecU1.Comp.almostSimple_map hnabXt hLC hcent htwo
  have hCt2 : IsPGroup 2 Ct := SecU1.Comp.isPGroup_two hLC htwo
  set ψ := (QuotientGroup.mk' Ct).comp π₁ with hψdef
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective Ct).comp hπ₁s
  have hψker : IsPGroup 2 ψ.ker := by
    intro k
    have hk : π₁ (k : ↥K) ∈ Ct := by
      have h1 : QuotientGroup.mk' Ct (π₁ (k : ↥K)) = 1 := MonoidHom.mem_ker.mp k.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨a, ha⟩ := hCt2 ⟨_, hk⟩
    have ha' : (k : ↥K) ^ 2 ^ a ∈ RK := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ₁, map_pow]
      simpa using congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := hRK2 ⟨_, ha'⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((k : ↥K) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    rw [← pow_mul, ← pow_add] at hb'
    simpa using hb'
  set χ := QuotientGroup.mk' Ct with hχ
  have hinj : Function.Injective (χ.comp Xt.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hχ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h : (x : ↥K ⧸ RK) ∈ Xt ⊓ Ct := ⟨x.2, hx⟩
    rw [hLC, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext h)
  have hrange : (χ.comp Xt.subtype).range = Xt.map χ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eL : ↥(Xt.map χ) ≃* Y :=
    ((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm).trans eXt
  have hB : (A.subgroupOf K).map ψ ≠ ⊥ := by
    intro h0
    apply hAC
    intro a ha x hx
    have hAτ : A ≤ τ := le_sup_left.trans (E1.le_tauOf hT hAT hA)
    have haK : a ∈ K := (le_sup_right : τ ≤ K) (hAτ ha)
    have hψa : ψ ⟨a, haK⟩ = 1 := by
      have : ψ ⟨a, haK⟩ ∈ (A.subgroupOf K).map ψ := ⟨⟨a, haK⟩, ha, rfl⟩
      rwa [h0, Subgroup.mem_bot] at this
    have haC : π₁ ⟨a, haK⟩ ∈ Ct := by
      have h1 : QuotientGroup.mk' Ct (π₁ ⟨a, haK⟩) = 1 := hψa
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hxt : π₁ ⟨x, hXK hx⟩ ∈ Xt := ⟨⟨x, hXK hx⟩, hx, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp haC _ hxt
    have hc : π₁ ⁅(⟨a, haK⟩ : ↥K), ⟨x, hXK hx⟩⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    rw [hπ₁, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRKdef,
      Subgroup.mem_subgroupOf] at hc
    simpa [commutatorElement_def] using hc
  exact isE_of_almostSimple_quot_gen hY hT hAT hA le_sup_right hSyl ψ hψs hψker hAS eL hB


theorem inEFor_top_of_quot_gen {n : ℕ} {ι : Type*} {T : Subgroup G} (X : ι → Subgroup G)
    (hT : IsSylowIn 2 T ⊤) (hTX : ∀ i, T ≤ Subgroup.normalizer (X i : Set G))
    (hφ : ∀ i, ∃ (Y : Type) (_ : Group Y) (φ : ↥(X i) →* Y), Rk1 n Y ∧ Function.Surjective φ ∧
      IsPGroup 2 φ.ker)
    (hgen : (⨆ i, X i) ⊔ T = ⊤) : E1.InEFor n ⊤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Ω hΩ
  refine eq_top_iff.mpr (hgen.symm.trans_le ?_)
  refine sup_le (iSup_le fun i => ?_) fun x hx =>
    Subgroup.mem_sup_right ⟨Subgroup.mem_top x, E1.le_normalizer_weakClosure hΩ hx⟩
  obtain ⟨Y, _, φ, hY, hφs, hker⟩ := hφ i
  have : IsSimpleGroup Y := hY.simple
  set R : Subgroup G := φ.ker.map (X i).subtype with hRdef
  set H := (X i) ⊔ T with hHdef
  have hTH : IsSylowIn 2 T H := B6.isSylowTwoOf_mono hT le_sup_right le_top
  have hHN : H ≤ Subgroup.normalizer ((X i) : Set G) := sup_le Subgroup.le_normalizer (hTX i)
  have hXsyl : IsSylowIn 2 (T ⊓ (X i)) (X i) := by
    have h1 := B6.isSylowTwoOf_inf_normal (⟨hTH.1, hTH.2.1, hTH.2.2⟩ :
      QuasithinUnique.IsSylowTwoOf T H) le_sup_left hHN
    exact ⟨h1.1, h1.2.1, h1.2.2⟩
  have hRc : R = (CFSG.Open.pCore 2 ↥(X i)).map (X i).subtype := by
    rw [hRdef, ker_eq_pCore_gen hY.nonabelian φ hφs hker]
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := by
    have : (CFSG.Open.pCore 2 ↥(X i)).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic 2
    rw [hRc]
    exact hHN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  by_cases hc : ∃ A ∈ Ω, A ≤ T ∧ ¬ ∀ a ∈ A, ∀ x ∈ (X i), ⁅a, x⁆ ∈ R
  · obtain ⟨A, hA, hAT, hAC⟩ := hc
    have hmem := isE_sup_tauOf_of_quot_gen hY hT hAT (hΩ.isElemAbelian A hA) φ hφs hker
      ((E1.tauOf_le _ _ _).trans (hTX i)) hXsyl hAC
    exact le_sup_left.trans ((E1.le_eGen hA hAT hmem).trans le_sup_left)
  · push Not at hc
    set C := Lie3.centQuot H (X i) R hHN hHR with hCdef
    have hZ := SecE3.center_eq_bot_of_simple hY.nonabelian
    have hCX : ∀ y ∈ C, y ∈ (X i) → y ∈ R := by
      intro y hy hyX
      have hc : φ ⟨y, hyX⟩ ∈ Subgroup.center Y := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨z, rfl⟩ := hφs s
        have h1 := hy.2 z z.2
        rw [hRdef] at h1
        obtain ⟨w, hw, hwz⟩ := h1
        have hw' : w = ⁅(⟨y, hyX⟩ : ↥(X i)), z⁆ := Subtype.ext hwz
        have hw2 : φ ⁅(⟨y, hyX⟩ : ↥(X i)), z⁆ = 1 := by rw [← hw']; exact hw
        rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at hw2
        calc φ z * φ ⟨y, hyX⟩ = (φ ⟨y, hyX⟩ * φ z * (φ ⟨y, hyX⟩)⁻¹ * (φ z)⁻¹)⁻¹ *
              (φ ⟨y, hyX⟩ * φ z) := by group
          _ = φ ⟨y, hyX⟩ * φ z := by rw [hw2, inv_one, one_mul]
      rw [hZ, Subgroup.mem_bot] at hc
      exact ⟨⟨y, hyX⟩, hc, rfl⟩
    have hCH : C ≤ H := fun y hy => hy.1
    have hCn : (C.subgroupOf H).Normal := by
      refine ⟨fun c hc h => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      refine ⟨H.mul_mem (H.mul_mem h.2 hc.1) (H.inv_mem h.2), fun y hy => ?_⟩
      have hz : (h : G)⁻¹ * y * (h : G)⁻¹⁻¹ ∈ (X i) :=
        (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem h.2)) y).mp hy
      have h1 : ⁅(h : G) * c * (h : G)⁻¹, y⁆ =
          (h : G) * ⁅(c : G), (h : G)⁻¹ * y * (h : G)⁻¹⁻¹⁆ * (h : G)⁻¹ := by
        simp only [commutatorElement_def]
        group
      push_cast
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp (hHR h.2) _).mp (hc.2 _ hz)
    have hτ' : IsPGroup 2 ↥(T.subgroupOf H) :=
      hT.2.1.comap_of_injective H.subtype H.subtype_injective
    have hC2 : IsPGroup 2 ↥C := by
      intro c
      have hcH : (c : G) ∈ (X i) ⊔ T := hCH c.2
      have hXHn : ((X i).subgroupOf H).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHN
      have hsup : (X i).subgroupOf H ⊔ T.subgroupOf H = ⊤ :=
        (Subgroup.codisjoint_subgroupOf_sup (X i) T).eq_top
      have hq : (⟨c, hcH⟩ : ↥H) ∈ (X i).subgroupOf H ⊔ T.subgroupOf H := hsup ▸ Subgroup.mem_top _
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hq
      obtain ⟨k, hk⟩ := hτ' ⟨z, hz⟩
      have hck : ((⟨c, hcH⟩ : ↥H)) ^ 2 ^ k ∈ (X i).subgroupOf H := by
        rw [← hyz, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
          (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow,
          show z ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk,
          QuotientGroup.mk_one]
      have hckX : (c : G) ^ 2 ^ k ∈ (X i) := by simpa [Subgroup.mem_subgroupOf] using hck
      have hckR : (c : G) ^ 2 ^ k ∈ R := hCX _ (C.pow_mem c.2 _) hckX
      obtain ⟨b, hb⟩ := (hker.map (X i).subtype) ⟨_, hckR⟩
      refine ⟨k + b, Subtype.ext ?_⟩
      have hb' : ((c : G) ^ 2 ^ k) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      rw [← pow_mul, ← pow_add] at hb'
      simpa using hb'
    have hCT : C ≤ T := hTH.le_of_normal hCH hCn hC2
    have hWC : E1.weakClosure T Ω ≤ C := by
      refine iSup₂_le fun A hA => iSup_le fun hAT a ha => ?_
      exact ⟨(le_sup_right : T ≤ H) (hAT ha), hc A hA hAT a ha⟩
    intro x hx
    refine Subgroup.mem_sup_right ⟨Subgroup.mem_top x, ?_⟩
    refine E1.mem_normalizer_weakClosure hΩ fun w hw => hCT ?_
    have h1 := hCn.conj_mem ⟨w, hCH (hWC hw)⟩ (by rw [Subgroup.mem_subgroupOf]; exact hWC hw)
      ⟨x, (le_sup_left : X i ≤ H) hx⟩
    rwa [Subgroup.mem_subgroupOf] at h1


omit [Finite G] in
theorem isPGroup_ker_comp {A B C : Type*} [Group A] [Group B] [Group C] (f : B →* C)
    (e : A ≃* B) (h : IsPGroup 2 f.ker) : IsPGroup 2 (f.comp e.toMonoidHom).ker := by
  intro x
  obtain ⟨k, hk⟩ := h ⟨e x.1, x.2⟩
  have h1 : (e x.1) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, Subtype.ext (e.injective ?_)⟩
  rw [Subgroup.coe_pow, map_pow, h1, OneMemClass.coe_one, map_one]

end CFSG.Quasithin.RonanE114
