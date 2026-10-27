module
public import CFSG.Milestones.ASVolI.I2GUniversal
public import CFSG.Quasithin.Vol2.KGNatReal
public import CFSG.Quasithin.Vol2.KGNatSp4Flag
public import CFSG.Quasithin.Vol2.KGNatSL2Nat
public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11G2Q8N13
public import CFSG.Quasithin.MS93.M15Omega5
public import CFSG.Quasithin.Vol2.Ch3B513NSpC
public import CFSG.Quasithin.Vol2.Ch3B513NC1SL2
public import CFSG.Quasithin.MS93.M15G2
public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.Quasithin.Background.JonesParshallSp4Perfect
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Vol2.Ch11G2Q8SiegelM
public import CFSG.Quasithin.Vol2.Ch11G2Q8InvLong
public import CFSG.Quasithin.Vol2.Ch11G2Q8Point
public import CFSG.Quasithin.H13.VolIAltCoverG2
public import CFSG.Quasithin.H13.VolIAltCoverG2Field
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Quasithin.Background.B5FinSpCore
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.FFC5Dich
public import CFSG.Quasithin.Background.FFC5Main
public import CFSG.Quasithin.Background.G64ExtSq
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Background.SmithB51SL3A
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecCFacts4
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3B513NC1Nat
public import CFSG.Quasithin.Vol2.KGNatSL2Borel
public import CFSG.Quasithin.Vol2.KGNatSL2H
public import CFSG.Quasithin.Vol2.KGNatSp4Sim
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement

public section
namespace CFSG.ASVolI
open CFSG.Open

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_hol_mul {V : Type} [CommGroup V] (a b : V) (g h : MulAut V) :
    ((⟨a, g⟩ : I23Holomorph V) * ⟨b, h⟩) = ⟨a * g b, g * h⟩ := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_hol_one {V : Type} [CommGroup V] : (1 : I23Holomorph V) = ⟨1, 1⟩ := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_hol_inv {V : Type} [CommGroup V] (a : V) (g : MulAut V) :
    ((⟨a, g⟩ : I23Holomorph V))⁻¹ = ⟨(g⁻¹ a)⁻¹, g⁻¹⟩ := by
  apply inv_eq_of_mul_eq_one_right
  rw [burnsideI23x_hol_mul]
  apply SemidirectProduct.ext
  · show a * g ((g⁻¹ a)⁻¹) = 1
    rw [map_inv, MulAut.apply_inv_self, mul_inv_cancel]
  · show g * g⁻¹ = 1
    exact mul_inv_cancel g

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_mem_moduleSubgroup {V : Type} [CommGroup V] {U : Subgroup V}
    (y : I23Holomorph V) : y ∈ i23ModuleSubgroup U ↔ y.right = 1 ∧ y.left ∈ U := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨rfl, hu⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y.left, h2, SemidirectProduct.ext rfl h1.symm⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_hol_conj_inl {V : Type} [CommGroup V] (v : V) (g : MulAut V) (u : V) :
    ((⟨v, g⟩ : I23Holomorph V) * ⟨u, 1⟩ * (⟨v, g⟩ : I23Holomorph V)⁻¹) = ⟨g u, 1⟩ := by
  rw [burnsideI23x_hol_inv, burnsideI23x_hol_mul, burnsideI23x_hol_mul]
  apply SemidirectProduct.ext
  · show v * g u * g ((g⁻¹ v)⁻¹) = g u
    rw [map_inv, MulAut.apply_inv_self, mul_comm v (g u), mul_inv_cancel_right]
  · show g * 1 * g⁻¹ = 1
    group

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_mem_normalizer {V : Type} [CommGroup V] {U : Subgroup V} (v : V)
    (g : MulAut V) :
    (⟨v, g⟩ : I23Holomorph V) ∈ Subgroup.normalizer (i23ModuleSubgroup U : Set (I23Holomorph V)) ↔
      g ∈ stabSub U := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h u
    have := h ⟨u, 1⟩
    rw [burnsideI23x_hol_conj_inl, burnsideI23x_mem_moduleSubgroup,
      burnsideI23x_mem_moduleSubgroup] at this
    simp only [true_and] at this
    exact this.symm
  · intro h y
    obtain ⟨w, k⟩ := y
    rw [burnsideI23x_mem_moduleSubgroup]
    by_cases hk : k = 1
    · subst hk
      have e : (⟨w, (1 : MulAut V)⟩ : I23Holomorph V) = ⟨w, 1⟩ := rfl
      rw [burnsideI23x_hol_conj_inl, burnsideI23x_mem_moduleSubgroup]
      simp only [true_and]
      exact (h w).symm
    · have hne : ((⟨v, g⟩ : I23Holomorph V) * ⟨w, k⟩ * (⟨v, g⟩ : I23Holomorph V)⁻¹).right ≠ 1 := by
        rw [burnsideI23x_hol_inv, burnsideI23x_hol_mul, burnsideI23x_hol_mul]
        intro h1
        apply hk
        have h1' : g * k * g⁻¹ = 1 := h1
        calc k = g⁻¹ * (g * k * g⁻¹) * g := by group
          _ = 1 := by rw [h1']; group
      constructor
      · intro h2
        exact absurd h2.1 hk
      · intro h2
        rw [burnsideI23x_mem_moduleSubgroup] at h2
        exact absurd h2.1 hne

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_mem_ext {V : Type} [CommGroup V] (G : Subgroup (MulAut V)) (U : Subgroup V)
    (v : V) (g : MulAut V) :
    (⟨v, g⟩ : I23Holomorph V) ∈ i23Extension G ⊓
        Subgroup.normalizer (i23ModuleSubgroup U : Set (I23Holomorph V)) ↔
      g ∈ G ⊓ stabSub U := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (burnsideI23x_mem_normalizer v g).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (burnsideI23x_mem_normalizer v g).2 h2⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_pCore_hol {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (G : Subgroup (MulAut V)) (U : Subgroup V) (v : V) (g : MulAut V) :
    (⟨v, g⟩ : I23Holomorph V) ∈ pCoreOf 2 (i23Extension G ⊓
        Subgroup.normalizer (i23ModuleSubgroup U : Set (I23Holomorph V))) ↔
      g ∈ pCoreOf 2 (G ⊓ stabSub U) := by
  set E := i23Extension G ⊓ Subgroup.normalizer (i23ModuleSubgroup U : Set (I23Holomorph V))
    with hE
  set H := G ⊓ stabSub U with hH
  let φ : ↥E →* ↥H :=
    { toFun := fun e => ⟨e.1.right, (burnsideI23x_mem_ext G U e.1.left e.1.right).1 e.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hφs : Function.Surjective φ := fun h =>
    ⟨⟨⟨1, h⟩, (burnsideI23x_mem_ext G U 1 h).2 h.2⟩, Subtype.ext rfl⟩
  constructor
  · rintro ⟨e, he, hex⟩
    have hmap : (CFSG.pCore 2 ↥E).map φ ≤ CFSG.pCore 2 ↥H := by
      unfold CFSG.pCore
      exact le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal φ hφs, CFSG.pCore_isPGroup.map φ⟩
    have h1 := hmap ⟨e, he, rfl⟩
    refine ⟨φ e, h1, ?_⟩
    have : (e : I23Holomorph V) = ⟨v, g⟩ := hex
    show (e : I23Holomorph V).right = g
    rw [this]
  · rintro ⟨h, hh, rfl⟩
    have hhE : (⟨v, (h : MulAut V)⟩ : I23Holomorph V) ∈ E :=
      (burnsideI23x_mem_ext G U v h).2 h.2
    let Y : Subgroup ↥E := (CFSG.pCore 2 ↥H).comap φ
    have hYn : Y.Normal := Subgroup.Normal.comap CFSG.pCore_normal φ
    have hYp : IsPGroup 2 Y := by
      intro y
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨φ y.1, y.2⟩
      refine ⟨a + 1, ?_⟩
      have h1 : (φ y.1) ^ 2 ^ a = 1 := by
        have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => (z : ↥H)) ha
        simpa using this
      have h2 : ((y.1 ^ 2 ^ a : ↥E) : I23Holomorph V).right = 1 := by
        have h1' : φ (y.1 ^ 2 ^ a) = 1 := by rw [map_pow]; exact h1
        exact congrArg (fun z : ↥H => (z : MulAut V)) h1'
      have hz2 : (y.1 ^ 2 ^ a : ↥E) ^ 2 = 1 := by
        generalize y.1 ^ 2 ^ a = z at h2 ⊢
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
        have e1 : (z : I23Holomorph V) = ⟨(z : I23Holomorph V).left, 1⟩ :=
          SemidirectProduct.ext rfl h2
        rw [e1, burnsideI23x_hol_mul]
        apply SemidirectProduct.ext
        · show (z : I23Holomorph V).left * (1 : MulAut V) (z : I23Holomorph V).left = 1
          rw [show (1 : MulAut V) (z : I23Holomorph V).left = (z : I23Holomorph V).left from rfl]
          have := hV (z : I23Holomorph V).left
          rw [pow_two] at this
          exact this
        · show (1 : MulAut V) * 1 = 1
          exact mul_one 1
      have : (y.1 : ↥E) ^ 2 ^ (a + 1) = 1 := by
        rw [pow_succ, pow_mul]
        exact hz2
      exact Subtype.ext (by simpa using this)
    have hYle : Y ≤ CFSG.pCore 2 ↥E := by
      unfold CFSG.pCore
      exact le_sSup ⟨hYn, hYp⟩
    exact ⟨⟨_, hhE⟩, hYle (show (⟨_, hhE⟩ : ↥E) ∈ Y from hh), rfl⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_centralCoreCompatibility : I23CentralCoreCompatibility := by
  intro V _ _ hV G U
  unfold I23LiteralCentralCore
  constructor
  · intro h g hg u hu
    obtain ⟨c, hc, hcu⟩ := h ⟨u, hu, rfl⟩
    have hy : (⟨1, g⟩ : I23Holomorph V) ∈ pCoreOf 2 (i23Extension G ⊓
        Subgroup.normalizer (i23ModuleSubgroup U : Set (I23Holomorph V))) :=
      (burnsideI23x_pCore_hol hV G U 1 g).2 hg
    have hcomm := Subgroup.mem_center_iff.1 hc ⟨_, hy⟩
    have h1 := congrArg Subtype.val hcomm
    have hcu' : (c : I23Holomorph V) = ⟨u, 1⟩ := hcu
    have h2 : (⟨1, g⟩ : I23Holomorph V) * (c : I23Holomorph V) =
        (c : I23Holomorph V) * ⟨1, g⟩ := h1
    rw [hcu', burnsideI23x_hol_mul, burnsideI23x_hol_mul] at h2
    have h3 := congrArg SemidirectProduct.left h2
    simp only [map_one, one_mul, mul_one] at h3
    exact h3
  · intro hcen x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem : (⟨u, 1⟩ : I23Holomorph V) ∈ pCoreOf 2 (i23Extension G ⊓
        Subgroup.normalizer (i23ModuleSubgroup U : Set (I23Holomorph V))) :=
      (burnsideI23x_pCore_hol hV G U u 1).2 (Subgroup.one_mem _)
    refine ⟨⟨⟨u, 1⟩, hmem⟩, ?_, rfl⟩
    show _ ∈ Subgroup.center _
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨w, k⟩, hz⟩
    have hk := (burnsideI23x_pCore_hol hV G U w k).1 hz
    have hku : k u = u := mem_centSub.1 (hcen hk) u hu
    apply Subtype.ext
    show (⟨w, k⟩ : I23Holomorph V) * ⟨u, 1⟩ = ⟨u, 1⟩ * ⟨w, k⟩
    rw [burnsideI23x_hol_mul, burnsideI23x_hol_mul]
    apply SemidirectProduct.ext
    · show w * k u = u * (1 : MulAut V) w
      rw [hku]
      exact mul_comm _ _
    · show k * 1 = 1 * k
      simp
open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_realizesVia {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {D : FFModel} {π : D.Gam →* ↥L}
    {β : V →* ↥D.sec ⧸ D.ker.subgroupOf D.sec} (h : I23SectionMap D L W0 π β)
    (hW0 : W0 ≤ fixV L) : D.RealizesVia L ⊤ W0 π := by
  obtain ⟨hπ, hβs, hβk, hkerle, hsecinv, hkerinv, hequiv⟩ := h
  refine ⟨hπ, le_top, hkerle, fun _ _ _ => Subgroup.mem_top _, ?_, hsecinv, hkerinv,
    β.comp (⊤ : Subgroup V).subtype, ?_, ?_, ?_⟩
  · intro g z hz
    rw [mem_fixV.1 (hW0 hz) g g.2]
    exact hz
  · intro y
    obtain ⟨v, hv⟩ := hβs y
    exact ⟨⟨v, Subgroup.mem_top v⟩, hv⟩
  · intro u
    show β (u : V) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hβk]
  · intro γ u m hu hm hum
    exact hequiv γ (u : V) m hm hum
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
structure burnsideI23x_ScalarAgree (m : ℕ) (F : Type) [Field F] {M : Type} [AddCommGroup M]
    [Module F M] (LM : LinModel (i23NaturalModel m F) F M) : Prop where
  mem : ∀ (c : F) (x : ↥(i23NaturalModel m F).sec),
    i23NaturalScalar m F c (x : (i23NaturalModel m F).Amb) ∈ (i23NaturalModel m F).sec
  eq : ∀ (c : F) (x : ↥(i23NaturalModel m F).sec)
    (hx : i23NaturalScalar m F c (x : (i23NaturalModel m F).Amb) ∈ (i23NaturalModel m F).sec),
    Multiplicative.toAdd (LM.e (QuotientGroup.mk
      ⟨i23NaturalScalar m F c (x : (i23NaturalModel m F).Amb), hx⟩)) =
      c • Multiplicative.toAdd (LM.e (QuotientGroup.mk x))

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_isCoord {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] (LM : LinModel (i23NaturalModel m F) F M)
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β) :
    IsCoord LM L W0 π (fun v => Multiplicative.toAdd (LM.e (β v))) := by
  obtain ⟨hπ, hβs, hβk, hkerle, hsecinv, hkerinv, hequiv⟩ := h
  refine ⟨fun u u' => ?_, fun u => ?_, fun x => ?_, fun γ u => ?_, hπ⟩
  · simp only [map_mul]
    rfl
  · rw [← hβk, MonoidHom.mem_ker, ← LM.e.map_eq_one_iff]
    exact ⟨fun h0 => congrArg Multiplicative.ofAdd h0, fun h1 => congrArg Multiplicative.toAdd h1⟩
  · obtain ⟨q, hq⟩ := LM.e.surjective (Multiplicative.ofAdd x)
    obtain ⟨v, hv⟩ := hβs q
    exact ⟨v, by simp only [hv, hq]; rfl⟩
  · obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (β u)
    have hact := hsecinv γ y y.2
    have h1 := hequiv γ u y hact hy.symm
    show Multiplicative.toAdd (LM.e (β ((π γ : MulAut V) u))) = _
    rw [h1, LM.e_act γ y hact, ← hy]
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_native_iff_img {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM)
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β) {U : Subgroup V} :
    (∀ (scalar : F) (vector : V), vector ∈ U →
      ∀ native : ↥(i23NaturalModel m F).sec, β vector = QuotientGroup.mk native →
        ∃ image : V, image ∈ U ∧
          ∃ hNative : i23NaturalScalar m F scalar (native : (i23NaturalModel m F).Amb) ∈
              (i23NaturalModel m F).sec,
            β image = QuotientGroup.mk ⟨i23NaturalScalar m F scalar
              (native : (i23NaturalModel m F).Amb), hNative⟩) ↔
    ∀ (c : F), ∀ x ∈ (burnsideI23x_isCoord LM h).img U, c • x ∈ (burnsideI23x_isCoord LM h).img U := by
  have hf := burnsideI23x_isCoord LM h
  constructor
  · rintro hcl c x ⟨u, hu, rfl⟩
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (β u)
    obtain ⟨image, himg, hN, hβ⟩ := hcl c u hu y hy.symm
    refine ⟨image, himg, ?_⟩
    show Multiplicative.toAdd (LM.e (β image)) = c • Multiplicative.toAdd (LM.e (β u))
    rw [hβ, ← hy]
    exact hS.eq c y hN
  · intro hcl c v hv y hy
    obtain ⟨image, himg, hfi⟩ := hcl c _ ⟨v, hv, rfl⟩
    have hN := hS.mem c y
    refine ⟨image, himg, hN, ?_⟩
    have h1 : LM.e (β image) = LM.e (QuotientGroup.mk ⟨i23NaturalScalar m F c (y : _), hN⟩) := by
      apply Multiplicative.toAdd.injective
      show Multiplicative.toAdd (LM.e (β image)) = _
      have : Multiplicative.toAdd (LM.e (β image)) = c • Multiplicative.toAdd (LM.e (β v)) := hfi
      rw [this, hy, hS.eq c y hN]
    exact LM.e.injective h1
open CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_mem_stabW_of_invariant {V : Type} [CommGroup V] {T : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : ∀ t ∈ T, ∀ u ∈ U, t u ∈ U) {t : MulAut V} (ht : t ∈ T) :
    t ∈ stabW U := by
  rw [mem_stabW]
  intro u
  refine ⟨fun hu => hU t ht u hu, fun hu => ?_⟩
  have := hU t⁻¹ (T.inv_mem ht) _ hu
  rwa [MulAut.inv_apply_self] at this

theorem burnsideI23x_card_iff_relIndex {V : Type} [CommGroup V] [Finite V] {W0 U : Subgroup V}
    (h : W0 ≤ U) (q i : ℕ) :
    Nat.card ↥U = Nat.card ↥W0 * q ^ i ↔ W0.relIndex U = q ^ i := by
  have h1 := Subgroup.relIndex_mul_card W0 U
  rw [inf_eq_left.mpr h] at h1
  have hpos : 0 < Nat.card ↥W0 := Nat.card_pos
  rw [← h1]
  constructor
  · intro h2
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h2, mul_comm]
  · intro h2
    rw [h2, mul_comm]

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_marked_imp_flag {m n : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β)
    (hcomm : ∀ T : M →+ M, (∀ (γ : (i23NaturalModel m F).Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    {U : Subgroup V} {i : ℕ} (hM : IsI23MarkedSubspace m n i F T W0 U β) :
    IsFlagW L (T ⊓ L) W0 (2 ^ n) i U := by
  obtain ⟨hWU, hT, hcard, hscal⟩ := hM
  have hf := burnsideI23x_isCoord LM h
  refine ⟨hWU, ?_, ?_, ?_⟩
  · rw [hf.endStableW_iff hV hcomm hWU]
    exact (burnsideI23x_native_iff_img hS h).1 hscal
  · exact (burnsideI23x_card_iff_relIndex hWU _ _).1 hcard
  · intro x hx
    exact burnsideI23x_mem_stabW_of_invariant hT hx.1

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_flag_imp_marked {m n : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β)
    (hcomm : ∀ T : M →+ M, (∀ (γ : (i23NaturalModel m F).Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    {U : Subgroup V} {i : ℕ} (hF : IsFlagW L (T ⊓ L) W0 (2 ^ n) i U)
    (hT : ∀ t ∈ T, ∀ u ∈ U, t u ∈ U) :
    IsI23MarkedSubspace m n i F T W0 U β := by
  obtain ⟨hWU, hend, hidx, -⟩ := hF
  have hf := burnsideI23x_isCoord LM h
  refine ⟨hWU, hT, (burnsideI23x_card_iff_relIndex hWU _ _).2 hidx, ?_⟩
  rw [burnsideI23x_native_iff_img hS h]
  exact (hf.endStableW_iff hV hcomm hWU).1 hend
open CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_flag12_of_unique {V : Type} [CommGroup V] {H P : Subgroup (MulAut V)}
    {Z : Subgroup V} {q : ℕ} (h : HasUniqueFlagW H P Z q) :
    ∃ U₁ U₂ : Subgroup V, IsFlagW H P Z q 1 U₁ ∧ IsFlagW H P Z q 2 U₂ ∧ U₁ ≤ U₂ ∧
      (∀ U, IsFlagW H P Z q 1 U → U = U₁) ∧ (∀ U, IsFlagW H P Z q 2 U → U = U₂) := by
  obtain ⟨U₁, U₂, U₃, h1, h2, h3, h12, h23, u1, u2, u3⟩ := h
  exact ⟨U₁, U₂, h1, h2, h12, u1, u2⟩
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_marked_flags {m n : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β)
    (hcomm : ∀ T : M →+ M, (∀ (γ : (i23NaturalModel m F).Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0)
    (hflag : ∃ U₁ U₂ : Subgroup V, IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U₁ ∧
      IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 U₂ ∧ U₁ ≤ U₂ ∧
      (∀ U, IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U → U = U₁) ∧
      (∀ U, IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 U → U = U₂)) :
    ∃ V1 V2 : Subgroup V, IsI23MarkedSubspace m n 1 F T W0 V1 β ∧
      IsI23MarkedSubspace m n 2 F T W0 V2 β ∧ V1 ≤ V2 ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace m n 1 F T W0 U β → U = V1) ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace m n 2 F T W0 U β → U = V2) := by
  obtain ⟨U₁, U₂, h1, h2, h12, u1, u2⟩ := hflag
  have hinvar : ∀ {i : ℕ} {U : Subgroup V}, IsFlagW L (T ⊓ L) W0 (2 ^ n) i U →
      (∀ U' : Subgroup V, IsFlagW L (T ⊓ L) W0 (2 ^ n) i U' → U' = U) →
      ∀ t ∈ T, ∀ u ∈ U, t u ∈ U := by
    intro i U hU huniq t ht u hu
    have hτW0 : t ∈ stabW W0 := burnsideI23x_mem_stabW_of_invariant hTW0 ht
    have hmap := isFlagW_map hU hτW0 (fun l hl => hTL t ht l hl) (fun p hp => by
      have hp' : t⁻¹ * p * t ∈ T ⊓ L := ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hp.1) ht,
        by simpa using hTL t⁻¹ (T.inv_mem ht) p hp.2⟩
      exact hU.2.2.2 hp')
    have := huniq _ hmap
    rw [← this]
    exact ⟨u, hu, rfl⟩
  refine ⟨U₁, U₂, burnsideI23x_flag_imp_marked hS hV h hcomm h1 (hinvar h1 u1),
    burnsideI23x_flag_imp_marked hS hV h hcomm h2 (hinvar h2 u2), h12, fun U hU => ?_,
    fun U hU => ?_⟩
  · exact u1 U (burnsideI23x_marked_imp_flag hS hV h hcomm hU)
  · exact u2 U (burnsideI23x_marked_imp_flag hS hV h hcomm hU)
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in
@[expose] noncomputable def burnsideI23x_LM3 (F : Type) [Field F] [CharP F 2] :
    LinModel (i23NaturalModel 3 F) F (CFSG.Quasithin.JonesParshall.Ix3 → F) :=
  linModelZorn ⁅quasithinG2 F, quasithinG2 F⁆ g2Derived_le

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_scalar3_apply (F : Type) [Field F] (c : F)
    (x : Multiplicative (quasithinZorn F)) :
    i23NaturalScalar 3 F c x = Multiplicative.ofAdd (c • Multiplicative.toAdd x) := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_sec3 (F : Type) [Field F] :
    (i23NaturalModel 3 F).sec = CFSG.Quasithin.zornO0 F := rfl

open CFSG.Quasithin CFSG.Quasithin.JonesParshall in
theorem burnsideI23x_zornO0_smul (F : Type) [Field F] (c : F) (x : Multiplicative (quasithinZorn F))
    (hx : x ∈ zornO0 F) : Multiplicative.ofAdd (c • Multiplicative.toAdd x) ∈ zornO0 F := by
  rw [mem_zornO0] at hx ⊢
  show Explicit.cayleyTr (c • Multiplicative.toAdd x) = 0
  have h : Explicit.cayleyTr (c • Multiplicative.toAdd x) = c * Explicit.cayleyTr (Multiplicative.toAdd x) := by
    simp only [Explicit.cayleyTr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [h, hx, mul_zero]

open CFSG.Quasithin CFSG.Quasithin.JonesParshall in
theorem burnsideI23x_zornPHom_smul (F : Type) [Field F] (c : F) (x : ↥(zornO0 F))
    (hx : Multiplicative.ofAdd (c • Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))) ∈
      zornO0 F) :
    Multiplicative.toAdd (zornPHom (F := F) ⟨Multiplicative.ofAdd
      (c • Multiplicative.toAdd (x : Multiplicative (quasithinZorn F))), hx⟩) =
      c • Multiplicative.toAdd (zornPHom (F := F) x) :=
  zP_smul c _

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in
theorem burnsideI23x_scalarAgree3 (F : Type) [Field F] [CharP F 2] :
    burnsideI23x_ScalarAgree 3 F (burnsideI23x_LM3 F) := by
  refine ⟨fun c x => ?_, fun c x hx => ?_⟩
  · exact burnsideI23x_zornO0_smul F c x.1 x.2
  · exact burnsideI23x_zornPHom_smul F c x hx

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in
theorem burnsideI23x_marked_flags_m3 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel 3 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 3 F).sec ⧸
      (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec}
    (h : I23SectionMap (i23NaturalModel 3 F) L W0 π β) (hW0 : W0 ≤ fixV L)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0)
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) :
    ∃ V1 V2 : Subgroup V, IsI23MarkedSubspace 3 n 1 F T W0 V1 β ∧
      IsI23MarkedSubspace 3 n 2 F T W0 V2 β ∧ V1 ≤ V2 ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 3 n 1 F T W0 U β → U = V1) ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 3 n 2 F T W0 U β → U = V2) := by
  have hchar : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hF
  have hflag := factFlagG2_holds F n hn hF V hV L W0 π (burnsideI23x_realizesVia h hW0)
    (T ⊓ L) hP
  exact burnsideI23x_marked_flags (burnsideI23x_scalarAgree3 F) hV h
    (fun T hT => commutant_g2Derived hc0 hc1 _ T hT) hTL hTW0 (burnsideI23x_flag12_of_unique hflag)
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
@[expose] noncomputable def burnsideI23x_LM2 (F : Type) [Field F] :
    LinModel (i23NaturalModel 2 F) F (Fin 2 ⊕ Fin 2 → F) :=
  linModelNat ⁅StatedSp 2 F, StatedSp 2 F⁆

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_scalar2_apply (F : Type) [Field F] (c : F)
    (x : Multiplicative (Fin 2 ⊕ Fin 2 → F)) :
    i23NaturalScalar 2 F c x = Multiplicative.ofAdd (c • Multiplicative.toAdd x) := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_sec2 (F : Type) [Field F] :
    (i23NaturalModel 2 F).sec = ⊤ := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_scalarAgree2 (F : Type) [Field F] :
    burnsideI23x_ScalarAgree 2 F (burnsideI23x_LM2 F) := by
  refine ⟨fun c x => ?_, fun c x hx => ?_⟩
  · exact Subgroup.mem_top _
  · rfl

open CFSG.Quasithin CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_sp_perfect {F : Type} [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) : ⁅StatedSp 2 F, StatedSp 2 F⁆ = StatedSp 2 F := by
  rw [CFSG.Quasithin.MS93.statedSp_eq_sp4']
  exact CFSG.Quasithin.JonesParshall.sp4_commutator_eq hc0 hc1

open CFSG.Quasithin in
theorem burnsideI23x_realizes_nat_congr {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Γ₁ Γ₂ : Subgroup (Matrix.GeneralLinearGroup ι K)} (heq : Γ₁ = Γ₂)
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {Z : Subgroup V} {π : ↥Γ₁ →* ↥H}
    (h : (FFModel.nat Γ₁).RealizesVia H ⊤ Z π) :
    ∃ π' : ↥Γ₂ →* ↥H, (FFModel.nat Γ₂).RealizesVia H ⊤ Z π' := by
  subst heq
  exact ⟨π, h⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_marked_flags_m2 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel 2 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 2 F).sec ⧸
      (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec}
    (h : I23SectionMap (i23NaturalModel 2 F) L W0 π β) (hW0 : W0 ≤ fixV L)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0)
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) :
    ∃ V1 V2 : Subgroup V, IsI23MarkedSubspace 2 n 1 F T W0 V1 β ∧
      IsI23MarkedSubspace 2 n 2 F T W0 V2 β ∧ V1 ≤ V2 ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 2 n 1 F T W0 U β → U = V1) ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 2 n 2 F T W0 U β → U = V2) := by
  have hchar : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hF
  have hperf := burnsideI23x_sp_perfect hc0 hc1
  have hR := burnsideI23x_realizesVia h hW0
  obtain ⟨π', hπ'⟩ := burnsideI23x_realizes_nat_congr hperf (π := π) hR
  have hflag := factFlagSp4_holds F n hn hF V hV L W0 π' hπ' (T ⊓ L) hP
  refine burnsideI23x_marked_flags (burnsideI23x_scalarAgree2 F) hV h
    (fun T' hT' => commutant_statedSp T' (fun γ x => ?_)) hTL hTW0 (burnsideI23x_flag12_of_unique hflag)
  exact hT' ⟨(γ : GL (Fin 2 ⊕ Fin 2) F), hperf.ge γ.2⟩ x
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
@[expose] noncomputable def burnsideI23x_LM1 (F : Type) [Field F] :
    LinModel (i23NaturalModel 1 F) F (Fin 2 → F) :=
  linModelNat (StatedSL 2 F)

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_scalar1_apply (F : Type) [Field F] (c : F) (x : Multiplicative (Fin 2 → F)) :
    i23NaturalScalar 1 F c x = Multiplicative.ofAdd (c • Multiplicative.toAdd x) := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_scalarAgree1 (F : Type) [Field F] :
    burnsideI23x_ScalarAgree 1 F (burnsideI23x_LM1 F) := by
  refine ⟨fun c x => ?_, fun c x hx => ?_⟩
  · exact Subgroup.mem_top _
  · rfl

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 in
theorem burnsideI23x_sylow_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    {π : ↥(StatedSL 2 F) →* ↥H} {f : W → (Fin 2 → F)}
    (hf : IsCoord (linModelNat (StatedSL 2 F)) H Z π f) {P : Subgroup (MulAut W)}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ x : MulAut W,
      x ∈ P ↔ ∃ v ∈ utri F, x = ((rho2 π (g * v * g⁻¹) : ↥H) : MulAut W) := by
  obtain ⟨hPH, hP2, hPi⟩ := hP
  have hinj : Function.Injective (rho2 π) :=
    hf.injective_nat.comp (specialLinearGroupEquivStatedSL 2 F).injective
  have hsurj : Function.Surjective (rho2 π) :=
    hf.onto.comp (specialLinearGroupEquivStatedSL 2 F).surjective
  have hQ2 := isPGroup_comap (rho2 π) hinj hP2
  have hQi : ¬ 2 ∣ ((P.subgroupOf H).comap (rho2 π)).index := by
    rw [index_comap (rho2 π) hsurj]
    exact hPi
  obtain ⟨g, hg⟩ := exists_conj_utri_eq_of_index hQ2 hQi
  refine ⟨g, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := hsurj ⟨x, hPH hx⟩
    have hAQ : A ∈ (P.subgroupOf H).comap (rho2 π) := by
      rw [Subgroup.mem_comap, hA, Subgroup.mem_subgroupOf]
      exact hx
    rw [← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hAQ
    refine ⟨g⁻¹ * A * g, hAQ, ?_⟩
    rw [show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hA]
  · rintro ⟨v, hv, rfl⟩
    have hmem : g * v * g⁻¹ ∈ (P.subgroupOf H).comap (rho2 π) := by
      rw [← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hmem
    exact hmem

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 in
theorem burnsideI23x_card_span_single {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] (v : M) (hv : v ≠ 0) : Nat.card (Submodule.span F {v}) = Nat.card F :=
  (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton F M v hv).toEquiv).symm

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 in
open scoped Matrix in
theorem burnsideI23x_line_sl2 {F : Type} [Field F] [Finite F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (T : Submodule F (Fin 2 → F)) (hcard : Nat.card T = Nat.card F)
    (hst : ∀ y : Fin 2 → F,
      ((g * utriElt 1 * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y
        ∈ T ↔ y ∈ T) :
    T = Submodule.span F {(g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]} := by
  have he0 := sl2_e0_ne_zero g
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hspan := burnsideI23x_card_span_single (F := F) _ he0
  obtain ⟨t, htT, ht0⟩ : ∃ t ∈ T, t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : T = ⊥ := by
      rw [eq_bot_iff]
      exact fun x hx => (Submodule.mem_bot F).2 (hcon x hx)
    rw [this] at hcard
    simp at hcard
    omega
  have hmem : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] ∈ T := by
    set t' := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ t with ht'
    have htg : t = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ t' := by rw [ht', sl_mul_inv_mulVec]
    by_cases hb : t' 1 = 0
    · have hta : t' = t' 0 • ![1, 0] := by
        ext i
        fin_cases i <;> simp [hb]
      have ha : t' 0 ≠ 0 := by
        intro h0
        apply ht0
        rw [htg, hta, h0, zero_smul, Matrix.mulVec_zero]
      have : t = t' 0 • ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) := by
        have h5 : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ t' =
            t' 0 • ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) := by
          conv_lhs => rw [hta]
          rw [Matrix.mulVec_smul]
        rw [htg]
        exact h5
      have h2 : (t' 0)⁻¹ • t = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] := by
        rw [this, smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [← h2]
      exact T.smul_mem _ htT
    · have h1 := (hst t).2 htT
      have hu : ((utriElt 1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ t'
          = t' + t' 1 • ![1, 0] := by
        ext i
        fin_cases i <;> simp [mulVec_two_apply, utriElt_apply_00, utriElt_apply_01,
          utriElt_apply_10, utriElt_apply_11]
      have h2 : ((g * utriElt 1 * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *ᵥ t - t =
          t' 1 • ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) := by
        rw [conjSL_mulVec, ← ht', hu, Matrix.mulVec_add, Matrix.mulVec_smul, ← htg]
        abel
      have h3 := T.sub_mem h1 htT
      rw [h2] at h3
      have h4 := T.smul_mem (t' 1)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at h4
  have hle : Submodule.span F {(g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]} ≤ T :=
    Submodule.span_le.2 (by simpa using hmem)
  have := AddSubgroup.eq_of_le_of_card_ge
    (H := (Submodule.span F {(g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]}).toAddSubgroup)
    (K := T.toAddSubgroup) hle (by
      show Nat.card T ≤ Nat.card (Submodule.span F {(g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]})
      rw [hcard, hspan])
  exact (Submodule.toAddSubgroup_injective this).symm

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 in
open scoped Matrix in
theorem burnsideI23x_mem_gline {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (y : Fin 2 → F) :
    y ∈ Submodule.span F {(g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]} ↔
      (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y) 1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, sl_inv_mul_mulVec]
    simp
  · intro h
    obtain ⟨w, hw⟩ : ∃ w : Fin 2 → F,
        w = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y :=
      ⟨_, rfl⟩
    rw [← hw] at h
    refine ⟨w 0, ?_⟩
    have hz : w = w 0 • ![1, 0] := by
      ext i
      fin_cases i <;> simp [h]
    rw [← Matrix.mulVec_smul, ← hz, hw, sl_mul_inv_mulVec]

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 in
open scoped Matrix in
theorem burnsideI23x_utri_apply1 {F : Type} [Field F] {v : Matrix.SpecialLinearGroup (Fin 2) F}
    (hv : v ∈ utri F) (z : Fin 2 → F) :
    (((v : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ z) 1 = z 1 := by
  have h10 : (v : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hv.1
  have h00 : (v : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := hv.2
  have hdet := v.2
  rw [Matrix.det_fin_two, h10, h00] at hdet
  have h11 : (v : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by linear_combination hdet
  rw [mulVec_two_apply, h10, h11]
  ring

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75
  CFSG.Quasithin.Vol2.Ch11.SecA in
open scoped Matrix in
theorem burnsideI23x_flag12_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSL 2 F) →* ↥H} {f : W → (Fin 2 → F)}
    (hf : IsCoord (linModelNat (StatedSL 2 F)) H Z π f) {P : Subgroup (MulAut W)}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) :
    ∃ U₁ U₂ : Subgroup W, IsFlagW H P Z (Nat.card F) 1 U₁ ∧ IsFlagW H P Z (Nat.card F) 2 U₂ ∧
      U₁ ≤ U₂ ∧ (∀ U, IsFlagW H P Z (Nat.card F) 1 U → U = U₁) ∧
      (∀ U, IsFlagW H P Z (Nat.card F) 2 U → U = U₂) := by
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_sl2 hf hP
  have hcomm : ∀ T : (Fin 2 → F) →+ (Fin 2 → F),
      (∀ (γ : ↥(StatedSL 2 F)) (x : Fin 2 → F),
        T ((linModelNat (StatedSL 2 F)).lin γ x) = (linModelNat (StatedSL 2 F)).lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x := fun T hT => commutant_statedSL (by norm_num) T hT
  have he0 := sl2_e0_ne_zero g
  set S : AddSubgroup (Fin 2 → F) :=
    (Submodule.span F {(g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]}).toAddSubgroup with hS
  have hspan := burnsideI23x_card_span_single (F := F) _ he0
  have hact : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (w : W),
      f (((rho2 π A : ↥H) : MulAut W) w) = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ f w :=
    fun A w => (hf.act _ w).trans (linModelNat_lin _ _ _)
  have himgtop : hf.img (⊤ : Subgroup W) = ⊤ := by
    ext x
    obtain ⟨w, rfl⟩ := hf.surj x
    exact ⟨fun _ => trivial, fun _ => ⟨w, trivial, rfl⟩⟩
  have hstab : ∀ v ∈ utri F, ∀ y : Fin 2 → F,
      ((g * v * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y ∈ S ↔
        y ∈ S := by
    intro v hv y
    show _ ∈ Submodule.span F _ ↔ _ ∈ Submodule.span F _
    rw [burnsideI23x_mem_gline, burnsideI23x_mem_gline, conjSL_mulVec, sl_inv_mul_mulVec,
      burnsideI23x_utri_apply1 hv]
  refine ⟨hf.pre S, ⊤, ⟨hf.le_pre S, ?_, ?_, fun x hx => ?_⟩, ⟨le_top, ?_, ?_, fun x hx => ?_⟩,
    le_top, fun U hU => ?_, fun U hU => ?_⟩
  · rw [hf.endStableW_iff hW hcomm (hf.le_pre S), hf.img_pre]
    exact fun c x hx => (Submodule.span F {(g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]}).smul_mem c hx
  · rw [← hf.card_img, hf.img_pre, pow_one]
    exact hspan
  · obtain ⟨v, hv, rfl⟩ := (hg x).mp hx
    rw [mem_stabW]
    intro u
    rw [hf.mem_pre, hf.mem_pre, hact (g * v * g⁻¹) u]
    exact (hstab v hv (f u)).symm
  · exact fun φ _ _ u _ => Subgroup.mem_top _
  · rw [← hf.card_img, himgtop, Nat.card_congr (AddSubgroup.topEquiv (G := Fin 2 → F)).toEquiv,
      Nat.card_fun, Nat.card_fin]
  · exact (mem_stabW).2 fun u => ⟨fun _ => trivial, fun _ => trivial⟩
  · obtain ⟨hZU, hst, hidx, hPU⟩ := hU
    have hsc := (hf.endStableW_iff hW hcomm hZU).1 hst
    let T : Submodule F (Fin 2 → F) :=
      { carrier := hf.img U
        add_mem' := (hf.img U).add_mem
        zero_mem' := (hf.img U).zero_mem
        smul_mem' := fun c x hx => hsc c x hx }
    have hTcard : Nat.card T = Nat.card F := by
      rw [← pow_one (Nat.card F), ← hidx, ← hf.card_img]
      rfl
    have hst' : ∀ y : Fin 2 → F,
        ((g * utriElt 1 * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *ᵥ y ∈ T ↔ y ∈ T := by
      intro y
      have h1 : ((rho2 π (g * utriElt 1 * g⁻¹) : ↥H) : MulAut W) ∈ stabW U :=
        hPU ((hg _).mpr ⟨utriElt 1, utriElt_mem_utri 1, rfl⟩)
      have h2 := (hf.mem_stabW_iff hZU (specialLinearGroupEquivStatedSL 2 F
        (g * utriElt 1 * g⁻¹))).1 h1 y
      exact h2.symm
    have hTS := burnsideI23x_line_sl2 g T hTcard hst'
    rw [← hf.pre_img hZU]
    congr 1
    exact congrArg Submodule.toAddSubgroup hTS
  · obtain ⟨hZU, hst, hidx, hPU⟩ := hU
    have h1 : Nat.card (hf.img U) = Nat.card (Fin 2 → F) := by
      rw [hf.card_img, hidx, Nat.card_fun, Nat.card_fin]
    have h2 : hf.img U = ⊤ := AddSubgroup.eq_top_of_card_eq _ h1
    rw [← hf.pre_img hZU, h2]
    ext w
    simp [IsCoord.pre]

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_marked_flags_m1 {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel 1 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 1 F).sec ⧸
      (i23NaturalModel 1 F).ker.subgroupOf (i23NaturalModel 1 F).sec}
    (h : I23SectionMap (i23NaturalModel 1 F) L W0 π β) (hW0 : W0 ≤ fixV L)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0)
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) :
    ∃ V1 V2 : Subgroup V, IsI23MarkedSubspace 1 n 1 F T W0 V1 β ∧
      IsI23MarkedSubspace 1 n 2 F T W0 V2 β ∧ V1 ≤ V2 ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 1 n 1 F T W0 U β → U = V1) ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 1 n 2 F T W0 U β → U = V2) := by
  have hchar : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have hR := burnsideI23x_realizesVia h hW0
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat (StatedSL 2 F)) hR
  have hflag := burnsideI23x_flag12_sl2 hV hf hP
  rw [hF] at hflag
  exact burnsideI23x_marked_flags (burnsideI23x_scalarAgree1 F) hV h
    (fun T' hT' => commutant_statedSL (by norm_num) T' hT') hTL hTW0 hflag
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_fixV_eq {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M] [Module F M]
    (LM : LinModel (i23NaturalModel m F) F M)
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β) (hW0 : W0 ≤ fixV L)
    (hnofix : ∀ x : M, (∀ γ : (i23NaturalModel m F).Gam, LM.lin γ x = x) → x = 0) :
    fixV L = W0 := by
  have hf := burnsideI23x_isCoord LM h
  refine le_antisymm (fun v hv => ?_) hW0
  have h0 : Multiplicative.toAdd (LM.e (β v)) = 0 := by
    apply hnofix
    intro γ
    rw [← hf.act γ v, mem_fixV.1 hv (π γ : MulAut V) (π γ).2]
  exact (hf.ker v).1 h0

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_nofix1 (F : Type) [Field F] (x : Fin 2 → F)
    (hx : ∀ γ : ↥(StatedSL 2 F), (burnsideI23x_LM1 F).lin γ x = x) : x = 0 := by
  have key : ∀ (i j : Fin 2), i ≠ j → x j = 0 := by
    intro i j hij
    have hdet := Matrix.det_transvection_of_ne i j hij (1 : F)
    have h := hx (specialLinearGroupEquivStatedSL 2 F ⟨Matrix.transvection i j (1 : F), hdet⟩)
    have h' : (Matrix.transvection i j (1 : F)) *ᵥ x = x := h
    have := congrFun h' i
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [Matrix.transvection, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.single_apply] at this <;> exact this
  ext i
  fin_cases i
  · exact key 1 0 (by decide)
  · exact key 0 1 (by decide)

theorem burnsideI23x_smul_ne {F : Type} [Field F] {M : Type} [AddCommGroup M] [Module F M]
    {x : M} (hx : x ≠ 0) {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : a • x ≠ 0 ∧ a • x ≠ x := by
  refine ⟨smul_ne_zero ha0 hx, fun h => ha1 ?_⟩
  have h2 : (a - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 hx

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_nofix2 (F : Type) [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (x : Fin 2 ⊕ Fin 2 → F)
    (hx : ∀ γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆, (burnsideI23x_LM2 F).lin γ x = x) : x = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := burnsideI23x_smul_ne hne hc0 hc1
  obtain ⟨γ, hγ⟩ := exists_sp4_lin_eq x (c • x) hne h1
  have hperf := burnsideI23x_sp_perfect hc0 hc1
  have := hx ⟨(γ : GL (Fin 2 ⊕ Fin 2) F), hperf.ge γ.2⟩
  exact h2 (hγ.symm.trans this)

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in
theorem burnsideI23x_nofix3 (F : Type) [Field F] [Finite F] [CharP F 2] {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (x : Ix3 → F)
    (hx : ∀ γ : ↥⁅quasithinG2 F, quasithinG2 F⁆, (burnsideI23x_LM3 F).lin γ x = x) : x = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := burnsideI23x_smul_ne hne hc0 hc1
  obtain ⟨γ, hγ⟩ := exists_g2_lin_eq hc0 hc1 x (c • x) hne h1
  exact h2 (hγ.symm.trans (hx γ))
open CFSG.QuasithinUnique in
theorem burnsideI23x_sylow_map {X Y : Type} [Group X] [Group Y] {G T : Subgroup X}
    (hT : IsSylowTwoOf T G) (φ : ↥G →* Y) :
    IsSylowTwoOf ((T.subgroupOf G).map φ) φ.range := by
  obtain ⟨hTG, hT2, hTi⟩ := hT
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have h1 : IsPGroup 2 (T.subgroupOf G) := hT2.comap_of_injective G.subtype G.subtype_injective
    exact h1.map φ
  · have hsub : ((T.subgroupOf G).map φ).subgroupOf φ.range =
        (T.subgroupOf G).map φ.rangeRestrict := by
      ext y
      constructor
      · rintro ⟨h, hh, hy⟩
        exact ⟨h, hh, Subtype.ext hy⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, rfl⟩
    rw [hsub]
    intro hdvd
    exact hTi (hdvd.trans (Subgroup.index_map_dvd _ φ.rangeRestrict_surjective))

theorem burnsideI23x_range_eq_sup {X Y : Type} [Group X] [Group Y] {G L T : Subgroup X}
    (hLG : L ≤ G) (hGT : G = L ⊔ T) (φ : ↥G →* Y) :
    φ.range = (L.subgroupOf G).map φ ⊔ (T.subgroupOf G).map φ := by
  have hTG : T ≤ G := hGT ▸ le_sup_right
  rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLG hTG, ← hGT, Subgroup.subgroupOf_self,
    MonoidHom.range_eq_map]

theorem burnsideI23x_range_comp_incl {X Y : Type} [Group X] [Group Y] {G L : Subgroup X}
    (hLG : L ≤ G) (φ : ↥G →* Y) :
    (φ.comp (Subgroup.inclusion hLG)).range = (L.subgroupOf G).map φ := by
  ext y
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Subgroup.inclusion hLG l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg⟩, rfl⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_marked_comap {m n i : ℕ} {F : Type} [Field F] {V U : Type} [CommGroup V]
    [Finite V] [CommGroup U] [Finite U] {G T : Subgroup (MulAut V)} (ρ : ↥G →* MulAut U)
    (θ : U →* V) (hθs : Function.Surjective θ)
    (hθe : ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u))
    {W0 : Subgroup V} {K : Subgroup U} (hK : K = W0.comap θ)
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    {Vi : Subgroup V} (h : IsI23MarkedSubspace m n i F T W0 Vi β) :
    IsI23MarkedSubspace m n i F ((T.subgroupOf G).map ρ) K (Vi.comap θ) (β.comp θ) := by
  obtain ⟨hWV, hT, hcard, hscal⟩ := h
  subst hK
  have hKle : W0.comap θ ≤ Vi.comap θ := fun u hu => hWV hu
  refine ⟨hKle, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ u hu
    show θ (ρ a u) ∈ Vi
    rw [hθe]
    exact hT a (Subgroup.mem_subgroupOf.1 ha) (θ u) hu
  · rw [burnsideI23x_card_iff_relIndex hKle]
    have h1 := (burnsideI23x_card_iff_relIndex hWV _ _).1 hcard
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hθs]
    exact h1
  · intro scalar u hu native hβ
    obtain ⟨image, himg, hN, hβi⟩ := hscal scalar (θ u) hu native hβ
    obtain ⟨u', rfl⟩ := hθs image
    exact ⟨u', himg, hN, hβi⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_sectionMap_lift {D : FFModel} {V U : Type} [CommGroup V] [CommGroup U]
    {G L : Subgroup (MulAut V)} (hLG : L ≤ G) (ρ : ↥G →* MulAut U) (θ : U →* V)
    (hθs : Function.Surjective θ) (hθe : ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u))
    {W0 : Subgroup V} {K : Subgroup U} (hK : K = W0.comap θ) {marking : D.Gam →* ↥L}
    {β : V →* ↥D.sec ⧸ D.ker.subgroupOf D.sec} (h : I23SectionMap D L W0 marking β) :
    I23SectionMap D (ρ.comp (Subgroup.inclusion hLG)).range K
      ((ρ.comp (Subgroup.inclusion hLG)).rangeRestrict.comp marking) (β.comp θ) := by
  obtain ⟨hπ, hβs, hβk, hkerle, hsecinv, hkerinv, hequiv⟩ := h
  refine ⟨(MonoidHom.rangeRestrict_surjective _).comp hπ, hβs.comp hθs, ?_, hkerle, hsecinv,
    hkerinv, ?_⟩
  · rw [← MonoidHom.comap_ker, hβk, hK]
  · intro γ u native hN hum
    have h1 : (((ρ.comp (Subgroup.inclusion hLG)).rangeRestrict.comp marking) γ :
        MulAut U) u = ρ (Subgroup.inclusion hLG (marking γ)) u := rfl
    show β (θ ((((ρ.comp (Subgroup.inclusion hLG)).rangeRestrict.comp marking) γ : MulAut U) u)) = _
    rw [h1, hθe]
    exact hequiv γ (θ u) native hN hum

theorem burnsideI23x_inv_lift {V U : Type} [CommGroup V] [CommGroup U] {G : Subgroup (MulAut V)}
    (ρ : ↥G →* MulAut U) (θ : U →* V)
    (hθe : ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u))
    {W0 : Subgroup V} (hGW0 : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) {K : Subgroup U}
    (hK : K = W0.comap θ) : ∀ x ∈ ρ.range, ∀ w ∈ K, x w ∈ K := by
  rintro _ ⟨a, rfl⟩ w hw
  subst hK
  show θ (ρ a w) ∈ W0
  rw [hθe]
  exact hGW0 a a.2 _ hw

theorem burnsideI23x_norm_lift {V U : Type} [CommGroup V] [CommGroup U] {G L : Subgroup (MulAut V)}
    (hLG : L ≤ G) (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (ρ : ↥G →* MulAut U) :
    ∀ x ∈ ρ.range, ∀ y ∈ (ρ.comp (Subgroup.inclusion hLG)).range,
      x * y * x⁻¹ ∈ (ρ.comp (Subgroup.inclusion hLG)).range := by
  rintro _ ⟨a, rfl⟩ _ ⟨l, rfl⟩
  refine ⟨⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hnorm a a.2 l l.2⟩, ?_⟩
  have h : Subgroup.inclusion hLG ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hnorm a a.2 l l.2⟩ =
      a * Subgroup.inclusion hLG l * a⁻¹ := Subtype.ext rfl
  simp only [MonoidHom.comp_apply]
  rw [h, map_mul, map_mul, map_inv]

open CFSG.Quasithin in
theorem burnsideI23x_pCore_lift {V U : Type} [CommGroup V] [CommGroup U] {G : Subgroup (MulAut V)}
    (ρ : ↥G →* MulAut U) (θ : U →* V) (hθs : Function.Surjective θ)
    (hθe : ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u)) (Vi : Subgroup V) :
    ∀ x ∈ pCoreOf 2 (G ⊓ stabSub Vi), ∃ hx : x ∈ G,
      ρ ⟨x, hx⟩ ∈ pCoreOf 2 (ρ.range ⊓ stabSub (Vi.comap θ)) := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := hx
  refine ⟨h.2.1, ?_⟩
  have hstab : ∀ (a : ↥G), (a : MulAut V) ∈ stabSub Vi ↔ ρ a ∈ stabSub (Vi.comap θ) := by
    intro a
    constructor
    · intro ha u
      show θ (ρ a u) ∈ Vi ↔ θ u ∈ Vi
      rw [hθe]
      exact ha (θ u)
    · intro ha v
      obtain ⟨u, rfl⟩ := hθs v
      have := ha u
      change θ (ρ a u) ∈ Vi ↔ θ u ∈ Vi at this
      rwa [hθe] at this
  let ψ : ↥(G ⊓ stabSub Vi) →* ↥(ρ.range ⊓ stabSub (Vi.comap θ)) :=
    { toFun := fun h => ⟨ρ ⟨h, h.2.1⟩, ⟨⟨_, rfl⟩, (hstab ⟨h, h.2.1⟩).1 h.2.2⟩⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun a b => Subtype.ext (map_mul ρ ⟨a, a.2.1⟩ ⟨b, b.2.1⟩) }
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, ⟨a, rfl⟩, hy⟩
    exact ⟨⟨(a : MulAut V), ⟨a.2, (hstab a).2 hy⟩⟩, Subtype.ext rfl⟩
  have hY : (CFSG.pCore 2 ↥(G ⊓ stabSub Vi)).map ψ ≤
      CFSG.pCore 2 ↥(ρ.range ⊓ stabSub (Vi.comap θ)) := by
    unfold CFSG.pCore
    exact le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal ψ hψs,
      CFSG.pCore_isPGroup.map ψ⟩
  exact ⟨ψ h, hY ⟨h, hh, rfl⟩, rfl⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_root_gen_iff {V U : Type} [CommGroup V] [CommGroup U]
    {G L : Subgroup (MulAut V)} (hLG : L ≤ G) (ρ : ↥G →* MulAut U) (θ : U →* V)
    (hθs : Function.Surjective θ)
    (hθe : ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u))
    {W0 : Subgroup V} {K : Subgroup U} (hK : K = W0.comap θ) (V1 : Subgroup V) (l : MulAut V)
    (hl : l ∈ L) :
    (l ∈ L ∧ (∀ vector : V, l vector * vector⁻¹ ∈ V1) ∧
      (∀ vector ∈ V1, l vector * vector⁻¹ ∈ W0) ∧ ∃ vector : V, l vector * vector⁻¹ ∉ W0) ↔
    (ρ ⟨l, hLG hl⟩ ∈ (ρ.comp (Subgroup.inclusion hLG)).range ∧
      (∀ u : U, ρ ⟨l, hLG hl⟩ u * u⁻¹ ∈ V1.comap θ) ∧
      (∀ u ∈ V1.comap θ, ρ ⟨l, hLG hl⟩ u * u⁻¹ ∈ K) ∧
      ∃ u : U, ρ ⟨l, hLG hl⟩ u * u⁻¹ ∉ K) := by
  subst hK
  have key : ∀ u : U, θ (ρ ⟨l, hLG hl⟩ u * u⁻¹) = l (θ u) * (θ u)⁻¹ := by
    intro u
    rw [map_mul, map_inv, hθe]
  refine ⟨fun ⟨_, h1, h2, v, hv⟩ => ⟨⟨⟨l, hl⟩, rfl⟩, fun u => ?_, fun u hu => ?_, ?_⟩,
    fun ⟨_, h1, h2, u, hu⟩ => ⟨hl, fun v => ?_, fun v hv => ?_, ?_⟩⟩
  · show θ _ ∈ V1
    rw [key]
    exact h1 _
  · show θ _ ∈ W0
    rw [key]
    exact h2 _ hu
  · obtain ⟨u, rfl⟩ := hθs v
    exact ⟨u, fun h => hv (by rw [← key]; exact h)⟩
  · obtain ⟨u, rfl⟩ := hθs v
    rw [← key]
    exact h1 u
  · obtain ⟨u, rfl⟩ := hθs v
    rw [← key]
    exact h2 u hv
  · exact ⟨θ u, fun h => hu (by show θ _ ∈ W0; rw [key]; exact h)⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_root_le {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) (W0 U : Subgroup V) :
    i23TransvectionRoot L W0 U ≤ L := by
  unfold i23TransvectionRoot
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_root_lift_mem {V U : Type} [CommGroup V] [CommGroup U]
    {G L : Subgroup (MulAut V)} (hLG : L ≤ G) (ρ : ↥G →* MulAut U) (θ : U →* V)
    (hθs : Function.Surjective θ)
    (hθe : ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u))
    {W0 : Subgroup V} {K : Subgroup U} (hK : K = W0.comap θ) (V1 : Subgroup V) :
    ∀ y ∈ i23TransvectionRoot (ρ.comp (Subgroup.inclusion hLG)).range K (V1.comap θ),
      ∃ a ∈ i23TransvectionRoot L W0 V1, ∃ ha : a ∈ G, y = ρ ⟨a, ha⟩ := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨l, hl⟩ := hy.1
    have hl' : y = ρ ⟨(l : MulAut V), hLG l.2⟩ := hl.symm
    have hlmem := (burnsideI23x_root_gen_iff hLG ρ θ hθs hθe hK V1 (l : MulAut V) l.2).2
      (by rw [← hl']; exact hy)
    exact ⟨l, Subgroup.subset_closure hlmem, hLG l.2, hl'⟩
  | one => exact ⟨1, Subgroup.one_mem _, G.one_mem, (map_one ρ).symm⟩
  | mul y1 y2 _ _ h1 h2 =>
    obtain ⟨a1, ha1, hG1, rfl⟩ := h1
    obtain ⟨a2, ha2, hG2, rfl⟩ := h2
    exact ⟨a1 * a2, Subgroup.mul_mem _ ha1 ha2, G.mul_mem hG1 hG2, (map_mul ρ ⟨a1, hG1⟩ ⟨a2, hG2⟩).symm⟩
  | inv y _ h =>
    obtain ⟨a, ha, hG, rfl⟩ := h
    exact ⟨a⁻¹, Subgroup.inv_mem _ ha, G.inv_mem hG, (map_inv ρ ⟨a, hG⟩).symm⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_root_mem_lift {V U : Type} [CommGroup V] [CommGroup U]
    {G L : Subgroup (MulAut V)} (hLG : L ≤ G) (ρ : ↥G →* MulAut U) (θ : U →* V)
    (hθs : Function.Surjective θ)
    (hθe : ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u))
    {W0 : Subgroup V} {K : Subgroup U} (hK : K = W0.comap θ) (V1 : Subgroup V) :
    ∀ a ∈ i23TransvectionRoot L W0 V1, ∀ ha : a ∈ G,
      ρ ⟨a, ha⟩ ∈ i23TransvectionRoot (ρ.comp (Subgroup.inclusion hLG)).range K (V1.comap θ) := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    intro hG
    have := (burnsideI23x_root_gen_iff hLG ρ θ hθs hθe hK V1 a ha.1).1 ha
    exact Subgroup.subset_closure this
  | one => intro hG; exact (map_one ρ).symm ▸ Subgroup.one_mem _
  | mul a b ha hb iha ihb =>
    intro hG
    have haG : a ∈ G := hLG (burnsideI23x_root_le L W0 V1 ha)
    have hbG : b ∈ G := hLG (burnsideI23x_root_le L W0 V1 hb)
    have := Subgroup.mul_mem _ (iha haG) (ihb hbG)
    rwa [← map_mul ρ ⟨a, haG⟩ ⟨b, hbG⟩] at this
  | inv a ha iha =>
    intro hG
    have haG : a ∈ G := hLG (burnsideI23x_root_le L W0 V1 ha)
    have := Subgroup.inv_mem _ (iha haG)
    rwa [← map_inv ρ ⟨a, haG⟩] at this

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_commV_root_le {V : Type} [CommGroup V] (L : Subgroup (MulAut V))
    (W0 V1 : Subgroup V) : commV (i23TransvectionRoot L W0 V1) ≤ V1 := by
  have key : ∀ a ∈ i23TransvectionRoot L W0 V1, ∀ v : V, a v * v⁻¹ ∈ V1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha => exact ha.2.1
    | one => intro v; simp
    | mul a b _ _ iha ihb =>
      intro v
      have h1 := V1.mul_mem (iha (b v)) (ihb v)
      have e : (a * b) v * v⁻¹ = a (b v) * (b v)⁻¹ * (b v * v⁻¹) := by
        simp [MulAut.mul_apply]
      rw [e]
      exact h1
    | inv a _ iha =>
      intro v
      have h1 := V1.inv_mem (iha (a⁻¹ v))
      have e : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
        simp [MulAut.apply_inv_self]
      rw [e]
      exact h1
  unfold commV
  rw [Subgroup.closure_le]
  rintro _ ⟨y, hy, v, rfl⟩
  exact key y hy v

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_comm_root_lift {V U : Type} [CommGroup V] [CommGroup U]
    {G L : Subgroup (MulAut V)} (hLG : L ≤ G) (ρ : ↥G →* MulAut U) (θ : U →* V)
    (hθs : Function.Surjective θ)
    (hθe : ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u))
    {W0 : Subgroup V} {K : Subgroup U} (hK : K = W0.comap θ) (V1 : Subgroup V)
    (hcU : V1.comap θ = commV (i23TransvectionRoot (ρ.comp (Subgroup.inclusion hLG)).range K
        (V1.comap θ)) ∧
      commV (i23TransvectionRoot (ρ.comp (Subgroup.inclusion hLG)).range K (V1.comap θ)) ≤
        fixV (i23TransvectionRoot (ρ.comp (Subgroup.inclusion hLG)).range K (V1.comap θ))) :
    V1 = commV (i23TransvectionRoot L W0 V1) ∧
      commV (i23TransvectionRoot L W0 V1) ≤ fixV (i23TransvectionRoot L W0 V1) := by
  obtain ⟨hc1, hc2⟩ := hcU
  have hle := burnsideI23x_commV_root_le L W0 V1
  have hV1 : V1 ≤ commV (i23TransvectionRoot L W0 V1) := by
    intro v hv
    obtain ⟨u, rfl⟩ := hθs v
    have hu : u ∈ commV (i23TransvectionRoot (ρ.comp (Subgroup.inclusion hLG)).range K
        (V1.comap θ)) := by rw [← hc1]; exact hv
    clear hv
    unfold commV at hu
    induction hu using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨r, hr, u', rfl⟩ := hy
      obtain ⟨a, ha, hG, rfl⟩ := burnsideI23x_root_lift_mem hLG ρ θ hθs hθe hK V1 r hr
      refine Subgroup.subset_closure ⟨a, ha, θ u', ?_⟩
      rw [map_mul, map_inv, hθe ⟨a, hG⟩]
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  have hEq : V1 = commV (i23TransvectionRoot L W0 V1) := le_antisymm hV1 hle
  refine ⟨hEq, fun w hw a ha => ?_⟩
  have hwV1 : w ∈ V1 := hle hw
  obtain ⟨u0, rfl⟩ := hθs w
  have hu0 : u0 ∈ commV (i23TransvectionRoot (ρ.comp (Subgroup.inclusion hLG)).range K
      (V1.comap θ)) := by rw [← hc1]; exact hwV1
  have haG : a ∈ G := hLG (burnsideI23x_root_le L W0 V1 ha)
  have hfix := hc2 hu0 (ρ ⟨a, haG⟩) (burnsideI23x_root_mem_lift hLG ρ θ hθs hθe hK V1 a ha haG)
  rw [← hθe ⟨a, haG⟩ u0]
  show θ (ρ ⟨a, haG⟩ u0) = θ u0
  rw [hfix]
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_UCg (m n : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
  ∀ (G L T : Subgroup (MulAut U)) (K : Subgroup U),
    L ≤ G → (∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) → G = L ⊔ T → IsSylowTwoOf T G →
    (∀ g ∈ G, ∀ w ∈ K, g w ∈ K) → IsUniversalCovering L K →
    ∀ (marking : (i23NaturalModel m F).Gam →* ↥L)
      (β : U →* ↥(i23NaturalModel m F).sec ⧸
        (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec),
      I23SectionMap (i23NaturalModel m F) L K marking β →
      ∀ U1 U2 : Subgroup U, IsI23MarkedSubspace m n 1 F T K U1 β →
        IsI23MarkedSubspace m n 2 F T K U2 β →
        (∃ u ∈ U1, u ∈ fixV T ∧ u ∉ fixV L) ∧
        (pCoreOf 2 (G ⊓ stabSub U1) ≤ centSub U1 ∧ pCoreOf 2 (G ⊓ stabSub U2) ≤ centSub U2) ∧
        (1 < n → m ≠ 3 → U1 = commV (i23TransvectionRoot L K U1) ∧
          commV (i23TransvectionRoot L K U1) ≤ fixV (i23TransvectionRoot L K U1))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK in
theorem burnsideI23x_transfer {m n : ℕ} (hUC : burnsideI23x_UCg m n) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    (hLG : L ≤ G) (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hGT : G = L ⊔ T)
    (hT : IsSylowTwoOf T G) (hGW0 : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) (hW0 : W0 ≤ fixV L)
    (hfixV : fixV L = W0) (hcomm : commV L = ⊤)
    {marking : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (hsec : I23SectionMap (i23NaturalModel m F) L W0 marking β)
    {V1 V2 : Subgroup V} (h1 : IsI23MarkedSubspace m n 1 F T W0 V1 β)
    (h2 : IsI23MarkedSubspace m n 2 F T W0 V2 β) :
    ¬ (fixV T ⊓ V1 ≤ fixV L) ∧
      (pCoreOf 2 (G ⊓ stabSub V1) ≤ centSub V1 ∧ pCoreOf 2 (G ⊓ stabSub V2) ≤ centSub V2) ∧
      (1 < n → m ≠ 3 → V1 = commV (i23TransvectionRoot L W0 V1) ∧
        commV (i23TransvectionRoot L W0 V1) ≤ fixV (i23TransvectionRoot L W0 V1)) := by
  have hTG : T ≤ G := hGT ▸ le_sup_right
  obtain ⟨hLG', U, _, _, ρ, K, θ, hexp, huniv, hθs, hK, hθe⟩ :=
    burnsideI23_relUniversalLift hV hLG hnorm hGW0 hW0 hcomm
  have hLU : (ρ.comp (Subgroup.inclusion hLG')).range = (L.subgroupOf G).map ρ :=
    burnsideI23x_range_comp_incl hLG' ρ
  have hGU : ρ.range = (ρ.comp (Subgroup.inclusion hLG')).range ⊔ (T.subgroupOf G).map ρ := by
    rw [hLU]
    exact burnsideI23x_range_eq_sup hLG' hGT ρ
  have hTU : IsSylowTwoOf ((T.subgroupOf G).map ρ) ρ.range := burnsideI23x_sylow_map hT ρ
  have hnormU := burnsideI23x_norm_lift hLG' hnorm ρ
  have hinvK := burnsideI23x_inv_lift ρ θ hθe hGW0 hK
  have hsecU := burnsideI23x_sectionMap_lift hLG' ρ θ hθs hθe hK hsec
  have hm1 := burnsideI23x_marked_comap ρ θ hθs hθe hK h1
  have hm2 := burnsideI23x_marked_comap ρ θ hθs hθe hK h2
  obtain ⟨ha, hb, hc⟩ := hUC F hF U hexp ρ.range (ρ.comp (Subgroup.inclusion hLG')).range
    ((T.subgroupOf G).map ρ) K (by rintro y ⟨l, rfl⟩; exact ⟨Subgroup.inclusion hLG' l, rfl⟩) hnormU hGU hTU hinvK huniv
    _ _ hsecU _ _ hm1 hm2
  refine ⟨?_, ⟨?_, ?_⟩, fun hn hm3 => ?_⟩
  · intro hle
    obtain ⟨u, hu1, huT, huL⟩ := ha
    apply huL
    have hx : θ u ∈ fixV T ⊓ V1 := by
      refine ⟨fun t ht => ?_, hu1⟩
      have := mem_fixV.1 huT (ρ ⟨t, hTG ht⟩) ⟨⟨t, hTG ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
      rw [← hθe ⟨t, hTG ht⟩, this]
    have hxW0 : θ u ∈ W0 := hfixV ▸ hle hx
    exact huniv.1 (by rw [hK]; exact hxW0)
  · intro x hx v hv
    obtain ⟨hxG, hxU⟩ := burnsideI23x_pCore_lift ρ θ hθs hθe V1 x hx
    have hcen := mem_centSub.1 (hb.1 hxU)
    obtain ⟨u, rfl⟩ := hθs v
    rw [← hθe ⟨x, hxG⟩ u, hcen u hv]
  · intro x hx v hv
    obtain ⟨hxG, hxU⟩ := burnsideI23x_pCore_lift ρ θ hθs hθe V2 x hx
    have hcen := mem_centSub.1 (hb.2 hxU)
    obtain ⟨u, rfl⟩ := hθs v
    rw [← hθe ⟨x, hxG⟩ u, hcen u hv]
  · exact burnsideI23x_comm_root_lift hLG' ρ θ hθs hθe hK V1 (hc hn hm3)
structure burnsideI23x_SD (F : Type) [Field F] (N : Type) [AddCommGroup N] [Module F N] where
  B : N →ₗ[F] N →ₗ[F] F
  Q0 : N → F
  Q0_add : ∀ x y, Q0 (x + y) = Q0 x + Q0 y + B x y
  Q0_smul : ∀ (c : F) (x : N), Q0 (c • x) = c ^ 2 * Q0 x
  alt : ∀ x, B x x = 0
  nondeg : ∀ x, (∀ y, B x y = 0) → x = 0

namespace burnsideI23x_SD

variable {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

@[expose] def Qw (S : burnsideI23x_SD F N) (w : N × F) : F := S.Q0 w.1 + w.2 ^ 2

@[expose] def Bw (S : burnsideI23x_SD F N) (w w' : N × F) : F := S.B w.1 w'.1

end burnsideI23x_SD

@[expose] noncomputable def burnsideI23x_sqrt (F : Type) [Field F] [Finite F] [CharP F 2] : F ≃+* F :=
  (frobeniusEquiv F 2).symm

theorem burnsideI23x_sqrt_sq {F : Type} [Field F] [Finite F] [CharP F 2] (a : F) :
    (burnsideI23x_sqrt F a) ^ 2 = a := by
  have h := (frobeniusEquiv F 2).apply_symm_apply a
  rwa [frobeniusEquiv_apply] at h

theorem burnsideI23x_sqrt_of_sq {F : Type} [Field F] [Finite F] [CharP F 2] (a : F) :
    burnsideI23x_sqrt F (a ^ 2) = a := by
  have h := (frobeniusEquiv F 2).symm_apply_apply a
  rwa [frobeniusEquiv_apply] at h

theorem burnsideI23x_sq_injective {F : Type} [Field F] [CharP F 2] {a b : F} (h : a ^ 2 = b ^ 2) :
    a = b := by
  apply frobenius_inj F 2
  rw [frobenius_def, frobenius_def]
  exact h

namespace burnsideI23x_SD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] def Symp (M : N ≃ₗ[F] N) : Prop := ∀ x y, S.B (M x) (M y) = S.B x y

@[expose] noncomputable def lf (M : N ≃ₗ[F] N) (x : N) : F :=
  burnsideI23x_sqrt F (S.Q0 x + S.Q0 (M x))

theorem lf_sq (M : N ≃ₗ[F] N) (x : N) : (S.lf M x) ^ 2 = S.Q0 x + S.Q0 (M x) :=
  burnsideI23x_sqrt_sq _

theorem two_eq_zero_F : (2 : F) = 0 := CharP.cast_eq_zero F 2

theorem add_self_F (a : F) : a + a = 0 := by
  rw [← two_mul, two_eq_zero_F, zero_mul]

theorem lf_add {M : N ≃ₗ[F] N} (hM : S.Symp M) (x y : N) :
    S.lf M (x + y) = S.lf M x + S.lf M y := by
  unfold lf
  rw [← map_add]
  congr 1
  rw [S.Q0_add, map_add, S.Q0_add, hM x y]
  have h := add_self_F (S.B x y)
  linear_combination h

theorem lf_smul (M : N ≃ₗ[F] N) (c : F) (x : N) : S.lf M (c • x) = c * S.lf M x := by
  unfold lf
  rw [map_smul, S.Q0_smul, S.Q0_smul, ← mul_add]
  conv_lhs => rw [show c ^ 2 * (S.Q0 x + S.Q0 (M x)) = c ^ 2 * (S.Q0 x + S.Q0 (M x)) from rfl]
  rw [map_mul, burnsideI23x_sqrt_of_sq]

theorem symp_symm {M : N ≃ₗ[F] N} (hM : S.Symp M) : S.Symp M.symm := fun x y => by
  have := hM (M.symm x) (M.symm y)
  simp only [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem lf_symm {M : N ≃ₗ[F] N} (x : N) : S.lf M.symm (M x) = S.lf M x := by
  unfold lf
  rw [LinearEquiv.symm_apply_apply, add_comm]

theorem lf_apply_symm {M : N ≃ₗ[F] N} (x : N) : S.lf M (M.symm x) = S.lf M.symm x := by
  unfold lf
  rw [LinearEquiv.apply_symm_apply, add_comm]

@[expose] noncomputable def lift {M : N ≃ₗ[F] N} (hM : S.Symp M) : (N × F) ≃ₗ[F] (N × F) where
  toFun w := (M w.1, w.2 + S.lf M w.1)
  map_add' w w' := by
    refine Prod.ext (map_add M _ _) ?_
    show w.2 + w'.2 + S.lf M (w.1 + w'.1) = w.2 + S.lf M w.1 + (w'.2 + S.lf M w'.1)
    rw [S.lf_add hM]
    ring
  map_smul' c w := by
    refine Prod.ext (map_smul M _ _) ?_
    show c * w.2 + S.lf M (c • w.1) = c * (w.2 + S.lf M w.1)
    rw [S.lf_smul]
    ring
  invFun w := (M.symm w.1, w.2 + S.lf M.symm w.1)
  left_inv w := by
    refine Prod.ext (M.symm_apply_apply _) ?_
    show w.2 + S.lf M w.1 + S.lf M.symm (M w.1) = w.2
    rw [S.lf_symm]
    have := add_self_F (S.lf M w.1)
    linear_combination this
  right_inv w := by
    refine Prod.ext (M.apply_symm_apply _) ?_
    show w.2 + S.lf M.symm w.1 + S.lf M (M.symm w.1) = w.2
    rw [S.lf_apply_symm]
    have := add_self_F (S.lf M.symm w.1)
    linear_combination this

theorem lift_apply {M : N ≃ₗ[F] N} (hM : S.Symp M) (w : N × F) :
    S.lift hM w = (M w.1, w.2 + S.lf M w.1) := rfl

theorem Qw_lift {M : N ≃ₗ[F] N} (hM : S.Symp M) (w : N × F) : S.Qw (S.lift hM w) = S.Qw w := by
  show S.Q0 (M w.1) + (w.2 + S.lf M w.1) ^ 2 = S.Q0 w.1 + w.2 ^ 2
  have h := S.lf_sq M w.1
  have h3 : (2 : F) = 0 := two_eq_zero_F
  linear_combination h + (S.Q0 (M w.1) + w.2 * S.lf M w.1) * h3

end burnsideI23x_SD

namespace burnsideI23x_SD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem lift_unique {M : N ≃ₗ[F] N} (hM : S.Symp M) (g : N × F → N × F)
    (hg1 : ∀ w, (g w).1 = M w.1) (hgQ : ∀ w, S.Qw (g w) = S.Qw w) (w : N × F) :
    g w = S.lift hM w := by
  refine Prod.ext (hg1 w) ?_
  show (g w).2 = w.2 + S.lf M w.1
  apply burnsideI23x_sq_injective
  have h1 := hgQ w
  have h2 := S.lf_sq M w.1
  have h3 := two_eq_zero_F (F := F)
  have h4 : S.Q0 (g w).1 + (g w).2 ^ 2 = S.Q0 w.1 + w.2 ^ 2 := h1
  rw [hg1 w] at h4
  linear_combination h4 - h2 - (S.Q0 (M w.1) + w.2 * S.lf M w.1) * h3

theorem symp_one : S.Symp (1 : N ≃ₗ[F] N) := fun _ _ => rfl

theorem lift_one_apply (w : N × F) : S.lift S.symp_one w = w :=
  (S.lift_unique S.symp_one (fun w => w) (fun _ => rfl) (fun _ => rfl) w).symm

theorem symp_mul {M M' : N ≃ₗ[F] N} (hM : S.Symp M) (hM' : S.Symp M') : S.Symp (M * M') :=
  fun x y => by
    show S.B (M (M' x)) (M (M' y)) = S.B x y
    rw [hM, hM']

theorem lift_mul_apply {M M' : N ≃ₗ[F] N} (hM : S.Symp M) (hM' : S.Symp M') (w : N × F) :
    S.lift (S.symp_mul hM hM') w = S.lift hM (S.lift hM' w) := by
  symm
  refine S.lift_unique (S.symp_mul hM hM') (fun w => S.lift hM (S.lift hM' w)) (fun w => rfl)
    (fun w => ?_) w
  rw [S.Qw_lift, S.Qw_lift]

end burnsideI23x_SD

namespace burnsideI23x_SD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] noncomputable def liftMul {M : N ≃ₗ[F] N} (hM : S.Symp M) :
    MulAut (Multiplicative (N × F)) :=
  (S.lift hM).toAddEquiv.toMultiplicative

theorem toAdd_liftMul {M : N ≃ₗ[F] N} (hM : S.Symp M) (w : Multiplicative (N × F)) :
    Multiplicative.toAdd (S.liftMul hM w) = S.lift hM (Multiplicative.toAdd w) := rfl

theorem liftMul_apply {M : N ≃ₗ[F] N} (hM : S.Symp M) (w : N × F) :
    S.liftMul hM (Multiplicative.ofAdd w) = Multiplicative.ofAdd (S.lift hM w) := rfl

@[expose] noncomputable def liftHom {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
    (hA : ∀ γ, S.Symp (A γ)) : Γ →* MulAut (Multiplicative (N × F)) where
  toFun γ := S.liftMul (hA γ)
  map_one' := by
    refine MulEquiv.ext fun w => Multiplicative.toAdd.injective ?_
    rw [toAdd_liftMul]
    exact (S.lift_unique (hA 1) (fun w => w) (fun w => by simp) (fun _ => rfl)
      (Multiplicative.toAdd w)).symm
  map_mul' γ δ := by
    refine MulEquiv.ext fun w => Multiplicative.toAdd.injective ?_
    show Multiplicative.toAdd (S.liftMul (hA (γ * δ)) w) =
      Multiplicative.toAdd (S.liftMul (hA γ) (S.liftMul (hA δ) w))
    rw [toAdd_liftMul, toAdd_liftMul, toAdd_liftMul]
    refine (S.lift_unique (hA (γ * δ)) (fun w => S.lift (hA γ) (S.lift (hA δ) w))
      (fun w => by rw [map_mul]; rfl) (fun w => ?_) (Multiplicative.toAdd w)).symm
    rw [S.Qw_lift, S.Qw_lift]

theorem liftHom_apply {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N)) (hA : ∀ γ, S.Symp (A γ))
    (γ : Γ) (w : N × F) :
    S.liftHom A hA γ (Multiplicative.ofAdd w) = Multiplicative.ofAdd (S.lift (hA γ) w) := rfl

end burnsideI23x_SD
namespace burnsideI23x_SD

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem lf_zero (M : N ≃ₗ[F] N) : S.lf M 0 = 0 := by
  have h := S.lf_sq M 0
  have h0 : S.Q0 0 = 0 := by
    have := S.Q0_smul (0 : F) 0
    simpa using this
  rw [map_zero, h0, add_zero] at h
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h

@[expose] def radSub (S : burnsideI23x_SD F N) : Subgroup (Multiplicative (N × F)) where
  carrier := {w | (Multiplicative.toAdd w).1 = 0}
  one_mem' := rfl
  mul_mem' := fun {a b} ha hb => by
    show (Multiplicative.toAdd a + Multiplicative.toAdd b).1 = 0
    rw [Prod.fst_add]
    show (Multiplicative.toAdd a).1 + (Multiplicative.toAdd b).1 = 0
    rw [ha, hb, add_zero]
  inv_mem' := fun {a} ha => by
    show (-(Multiplicative.toAdd a)).1 = 0
    rw [Prod.fst_neg]
    show -(Multiplicative.toAdd a).1 = 0
    rw [ha, neg_zero]

theorem mem_radSub {w : Multiplicative (N × F)} : w ∈ S.radSub ↔ (Multiplicative.toAdd w).1 = 0 :=
  Iff.rfl

@[expose] def projHom : Multiplicative (N × F) →* Multiplicative N where
  toFun w := Multiplicative.ofAdd (Multiplicative.toAdd w).1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projHom_surjective : Function.Surjective (projHom (F := F) (N := N)) := fun x =>
  ⟨Multiplicative.ofAdd (Multiplicative.toAdd x, 0), rfl⟩

theorem projHom_ker : (projHom (F := F) (N := N)).ker = S.radSub := by
  ext w
  rw [MonoidHom.mem_ker, mem_radSub]
  exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

theorem sq_eq_one_W (w : Multiplicative (N × F)) : w ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, two_eq_zero_F, zero_smul]

end burnsideI23x_SD

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_univ_iso {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type}
    [AddCommGroup N] [Module F N] [Finite N] (S : burnsideI23x_SD F N)
    {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N)) (hA : ∀ γ, S.Symp (A γ))
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} {W0 : Subgroup V} (huniv : IsUniversalCovering L W0)
    (π : Γ →* ↥L) (hπ : Function.Bijective π) (f : V →* Multiplicative N)
    (hfs : Function.Surjective f) (hfk : f.ker = W0)
    (hfπ : ∀ (γ : Γ) (v : V), f ((π γ : MulAut V) v) =
      Multiplicative.ofAdd (A γ (Multiplicative.toAdd (f v))))
    (hbound : Nat.card W0 ≤ Nat.card F)
    (hgen : ∀ w : Multiplicative (N × F), w ∈ Subgroup.closure
      {x | ∃ (γ : Γ) (y : Multiplicative (N × F)), x = S.liftHom A hA γ y * y⁻¹}) :
    ∃ ψ : V ≃* Multiplicative (N × F),
      (∀ (γ : Γ) (v : V), ψ ((π γ : MulAut V) v) = S.liftHom A hA γ (ψ v)) ∧
      ∀ v : V, (Multiplicative.toAdd (ψ v)).1 = Multiplicative.toAdd (f v) := by
  classical
  let eΓ : Γ ≃* ↥L := MulEquiv.ofBijective π hπ
  let ρ' : ↥L →* MulAut (Multiplicative (N × F)) := (S.liftHom A hA).comp eΓ.symm.toMonoidHom
  have hρ' : ∀ γ w, ρ' (π γ) w = S.liftHom A hA γ w := by
    intro γ w
    show S.liftHom A hA (eΓ.symm (π γ)) w = _
    have : eΓ.symm (π γ) = γ := eΓ.symm_apply_apply γ
    rw [this]
  let fe : V ⧸ W0 ≃* Multiplicative N :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  have hfe : ∀ v : V, fe (QuotientGroup.mk v) = f v := fun v => rfl
  let ψ' : Multiplicative (N × F) →* V ⧸ W0 := fe.symm.toMonoidHom.comp (burnsideI23x_SD.projHom)
  have hψ'v : ∀ (w : Multiplicative (N × F)) (v : V), ψ' w = QuotientGroup.mk v ↔
      Multiplicative.ofAdd (Multiplicative.toAdd w).1 = f v := by
    intro w v
    constructor
    · intro h
      have h1 := congrArg fe h
      have h2 : fe (ψ' w) = Multiplicative.ofAdd (Multiplicative.toAdd w).1 :=
        fe.apply_symm_apply _
      rw [h2, hfe] at h1
      exact h1
    · intro h
      show fe.symm (Multiplicative.ofAdd (Multiplicative.toAdd w).1) = QuotientGroup.mk v
      rw [h, ← hfe v, MulEquiv.symm_apply_apply]
  have hfix' : ∀ w ∈ S.radSub, ∀ g : ↥L, ρ' g w = w := by
    intro w hw g
    obtain ⟨γ, rfl⟩ := hπ.2 g
    rw [hρ']
    apply Multiplicative.toAdd.injective
    show S.lift (hA γ) (Multiplicative.toAdd w) = Multiplicative.toAdd w
    have hw1 : (Multiplicative.toAdd w).1 = 0 := hw
    refine Prod.ext ?_ ?_
    · show A γ (Multiplicative.toAdd w).1 = (Multiplicative.toAdd w).1
      rw [hw1, map_zero]
    · show (Multiplicative.toAdd w).2 + S.lf (A γ) (Multiplicative.toAdd w).1 =
        (Multiplicative.toAdd w).2
      rw [hw1, S.lf_zero, add_zero]
  have hgen' : Subgroup.closure
      {w : Multiplicative (N × F) | ∃ (g : ↥L) (v : Multiplicative (N × F)),
        w = ρ' g v * v⁻¹} = ⊤ := by
    rw [eq_top_iff]
    intro w _
    refine Subgroup.closure_mono ?_ (hgen w)
    rintro _ ⟨γ, y, rfl⟩
    exact ⟨π γ, y, by rw [hρ']⟩
  have hψs : Function.Surjective ψ' := fun q => by
    obtain ⟨w, hw⟩ := burnsideI23x_SD.projHom_surjective (F := F) (N := N) (fe q)
    refine ⟨w, ?_⟩
    show fe.symm (burnsideI23x_SD.projHom w) = q
    rw [hw, MulEquiv.symm_apply_apply]
  have hker : ψ'.ker = S.radSub := by
    ext w
    rw [MonoidHom.mem_ker]
    show fe.symm (burnsideI23x_SD.projHom w) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, S.projHom_ker]
  have hequiv : ∀ (g : ↥L) (v' : Multiplicative (N × F)) (v : V), ψ' v' = QuotientGroup.mk v →
      ψ' (ρ' g v') = QuotientGroup.mk ((g : MulAut V) v) := by
    intro g v' v hv
    obtain ⟨γ, rfl⟩ := hπ.2 g
    rw [hρ', hψ'v]
    rw [hψ'v] at hv
    have h1 : (Multiplicative.toAdd (S.liftHom A hA γ v')).1 = A γ (Multiplicative.toAdd v').1 := rfl
    rw [h1, hfπ]
    have h2 : (Multiplicative.toAdd v').1 = Multiplicative.toAdd (f v) := by
      rw [← hv]
      rfl
    rw [h2]
  obtain ⟨θ, hθs, hθe, hθψ⟩ := huniv.2.2 (Multiplicative (N × F)) ρ' S.radSub ψ'
    (fun w => burnsideI23x_SD.sq_eq_one_W (F := F) (N := N) w) hfix' hgen' hψs hker hequiv
  have hcardV : Nat.card V = Nat.card W0 * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup W0, mul_comm]
    congr 1
    exact Nat.card_congr fe.toEquiv
  have hcardW : Nat.card (Multiplicative (N × F)) = Nat.card N * Nat.card F := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (N × F) ≃ N × F), Nat.card_prod]
  have hle1 : Nat.card (Multiplicative (N × F)) ≤ Nat.card V := Nat.card_le_card_of_surjective _ hθs
  have hle2 : Nat.card V ≤ Nat.card (Multiplicative (N × F)) := by
    rw [hcardV, hcardW, mul_comm (Nat.card N)]
    exact Nat.mul_le_mul_right _ hbound
  have hbij : Function.Bijective θ := hθs.bijective_of_nat_card_le hle2
  refine ⟨MulEquiv.ofBijective θ hbij, fun γ v => ?_, fun v => ?_⟩
  · show θ ((π γ : MulAut V) v) = S.liftHom A hA γ (θ v)
    rw [hθe, hρ']
  · have h1 := hθψ v
    rw [hψ'v] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    exact h2
section HypSD

variable {F : Type} [Field F] [CharP F 2] (ι : Type) [Fintype ι] [DecidableEq ι]

@[expose] def burnsideI23x_hypB : (ι ⊕ ι → F) →ₗ[F] (ι ⊕ ι → F) →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => ∑ i, (x (Sum.inl i) * y (Sum.inr i) + x (Sum.inr i) * y (Sum.inl i)))
    (fun x x' y => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]
      ring)
    (fun c x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
    (fun x y y' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]
      ring)
    (fun c x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)

theorem burnsideI23x_hypB_apply (x y : ι ⊕ ι → F) :
    burnsideI23x_hypB ι x y =
      ∑ i, (x (Sum.inl i) * y (Sum.inr i) + x (Sum.inr i) * y (Sum.inl i)) := by
  simp [burnsideI23x_hypB, LinearMap.mk₂]

@[expose] def burnsideI23x_hypSD : burnsideI23x_SD F (ι ⊕ ι → F) where
  B := burnsideI23x_hypB ι
  Q0 x := ∑ i, x (Sum.inl i) * x (Sum.inr i)
  Q0_add x y := by
    rw [burnsideI23x_hypB_apply, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  Q0_smul c x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  alt x := by
    rw [burnsideI23x_hypB_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination (x (Sum.inl i) * x (Sum.inr i)) * h
  nondeg x hx := by
    classical
    funext j
    rcases j with j | j
    · have := hx (Pi.single (Sum.inr j) 1)
      rw [burnsideI23x_hypB_apply] at this
      simpa [Pi.single_apply] using this
    · have := hx (Pi.single (Sum.inl j) 1)
      rw [burnsideI23x_hypB_apply] at this
      simpa [Pi.single_apply] using this

end HypSD
namespace burnsideI23x_SD

section Gen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ))

include hA in
@[expose] def GenW : Prop :=
  ∀ w : N × F, w ∈ AddSubgroup.closure {y | ∃ (γ : Γ) (x : N × F), y = S.lift (hA γ) x - x}

theorem vanish_of_gen (hgen : S.GenW A hA) {M : Type} [AddCommGroup M] (h : (N × F) →+ M)
    (hv : ∀ (γ : Γ) (x : N × F), h (S.lift (hA γ) x - x) = 0) (w : N × F) : h w = 0 := by
  have hle : AddSubgroup.closure {y | ∃ (γ : Γ) (x : N × F), y = S.lift (hA γ) x - x} ≤ h.ker :=
    (AddSubgroup.closure_le _).2 (by rintro y ⟨γ, x, rfl⟩; exact hv γ x)
  exact hle (hgen w)

include hA in
theorem B_symp_apply (γ : Γ) (x y : N) : S.B x (A γ y) = S.B (A γ⁻¹ x) y := by
  have h := hA γ (A γ⁻¹ x) y
  have e : A γ (A γ⁻¹ x) = x := by
    have := congrArg (fun f : N ≃ₗ[F] N => f x)
      (show A γ * A γ⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
    simpa using this
  rw [e] at h
  exact h

theorem fix_iff (hgen : S.GenW A hA) (w : N × F) :
    (∀ γ, S.lift (hA γ) w = w) ↔ w.1 = 0 := by
  constructor
  · intro hw
    have hx : ∀ γ, A γ w.1 = w.1 := fun γ => congrArg Prod.fst (hw γ)
    apply S.nondeg
    intro y
    let h : (N × F) →+ F :=
      { toFun := fun v => S.B w.1 v.1
        map_zero' := by simp
        map_add' := fun a b => by simp }
    have hv : ∀ (γ : Γ) (x : N × F), h (S.lift (hA γ) x - x) = 0 := by
      intro γ x
      show S.B w.1 (S.lift (hA γ) x - x).1 = 0
      have : (S.lift (hA γ) x - x).1 = A γ x.1 - x.1 := rfl
      rw [this, map_sub, S.B_symp_apply A hA, hx γ⁻¹, sub_self]
    exact S.vanish_of_gen A hA hgen h hv (y, 0)
  · intro h γ
    refine Prod.ext ?_ ?_
    · show A γ w.1 = w.1
      rw [h, map_zero]
    · show w.2 + S.lf (A γ) w.1 = w.2
      rw [h, S.lf_zero, add_zero]

end Gen

end burnsideI23x_SD
namespace burnsideI23x_SD

section Comm

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ))

theorem lift_fst (γ : Γ) (w : N × F) : (S.lift (hA γ) w).1 = A γ w.1 := rfl

include hA in
theorem comm_scalar (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) (D : (N × F) →+ (N × F))
    (hDc : ∀ γ w, D (S.lift (hA γ) w) = S.lift (hA γ) (D w))
    (hDK : ∀ w : N × F, w.1 = 0 → (D w).1 = 0) : ∃ d : F, ∀ w, D w = d • w := by
  let δ : N →+ N := (AddMonoidHom.fst N F).comp (D.comp (AddMonoidHom.inl N F))
  have hδ : ∀ γ x, δ (A γ x) = A γ (δ x) := by
    intro γ x
    have h1 := congrArg Prod.fst (hDc γ (x, 0))
    have h3 : S.lift (hA γ) (x, 0) = (A γ x, 0) + (0, S.lf (A γ) x) := by
      refine Prod.ext ?_ ?_ <;> simp [S.lift_apply]
    rw [h3, map_add, Prod.fst_add, hDK (0, S.lf (A γ) x) rfl, add_zero, S.lift_fst A hA] at h1
    exact h1
  obtain ⟨d, hd⟩ := hEnd δ hδ
  refine ⟨d, ?_⟩
  let D2 : (N × F) →+ (N × F) :=
    { toFun := fun w => D w - d • w
      map_zero' := by simp
      map_add' := fun a b => by simp [smul_add]; abel }
  have hD2fst : ∀ w, (D2 w).1 = 0 := by
    intro w
    show (D w - d • w).1 = 0
    have hw : w = (w.1, 0) + (0, w.2) := by ext <;> simp
    have h1 : (D w).1 = δ w.1 := by
      conv_lhs => rw [hw, map_add, Prod.fst_add, hDK (0, w.2) rfl, add_zero]
      rfl
    rw [Prod.fst_sub, h1, hd, Prod.smul_fst, sub_self]
  have hD2c : ∀ γ w, D2 (S.lift (hA γ) w) = S.lift (hA γ) (D2 w) := by
    intro γ w
    show D (S.lift (hA γ) w) - d • S.lift (hA γ) w = S.lift (hA γ) (D w - d • w)
    rw [hDc, map_sub, map_smul]
  let h : (N × F) →+ F := (AddMonoidHom.snd N F).comp D2
  have hv : ∀ (γ : Γ) (x : N × F), h (S.lift (hA γ) x - x) = 0 := by
    intro γ x
    show (D2 (S.lift (hA γ) x - x)).2 = 0
    rw [map_sub, hD2c]
    have h0 : (D2 x).1 = 0 := hD2fst x
    have : S.lift (hA γ) (D2 x) = D2 x := by
      refine Prod.ext ?_ ?_
      · rw [S.lift_fst A hA, h0, map_zero]
      · show (D2 x).2 + S.lf (A γ) (D2 x).1 = (D2 x).2
        rw [h0, S.lf_zero, add_zero]
    rw [this, sub_self]
    rfl
  intro w
  have h2 : (D2 w).2 = 0 := S.vanish_of_gen A hA hgen h hv w
  have h3 : D2 w = 0 := Prod.ext (hD2fst w) h2
  exact sub_eq_zero.1 h3

end Comm

end burnsideI23x_SD
namespace burnsideI23x_SD

section Normalizer

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ))

structure NormW (g : (N × F) ≃+ (N × F)) : Prop where
  fwd : ∀ γ, ∃ γ', ∀ w, g (S.lift (hA γ) w) = S.lift (hA γ') (g w)
  bwd : ∀ γ, ∃ γ', ∀ w, g (S.lift (hA γ') w) = S.lift (hA γ) (g w)

theorem Qw_add (w w' : N × F) : S.Qw (w + w') = S.Qw w + S.Qw w' + S.Bw w w' := by
  show S.Q0 (w + w').1 + (w + w').2 ^ 2 = S.Q0 w.1 + w.2 ^ 2 + (S.Q0 w'.1 + w'.2 ^ 2) + S.B w.1 w'.1
  rw [Prod.fst_add, Prod.snd_add, S.Q0_add]
  have h := two_eq_zero_F (F := F)
  linear_combination (w.2 * w'.2) * h

theorem Qw_smul (c : F) (w : N × F) : S.Qw (c • w) = c ^ 2 * S.Qw w := by
  show S.Q0 (c • w).1 + (c • w).2 ^ 2 = c ^ 2 * (S.Q0 w.1 + w.2 ^ 2)
  rw [Prod.smul_fst, Prod.smul_snd, S.Q0_smul, smul_eq_mul]
  ring

variable {S A hA}

theorem NormW.map_rad {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g) (hgen : S.GenW A hA)
    {w : N × F} (hw : w.1 = 0) : (g w).1 = 0 := by
  rw [← S.fix_iff A hA hgen]
  intro γ
  obtain ⟨γ', h⟩ := hn.bwd γ
  rw [← h w, (S.fix_iff A hA hgen w).2 hw γ']

theorem NormW.symm_rad {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g) (hgen : S.GenW A hA)
    {w : N × F} (hw : w.1 = 0) : (g.symm w).1 = 0 := by
  rw [← S.fix_iff A hA hgen]
  intro γ
  obtain ⟨γ', h⟩ := hn.fwd γ
  apply g.injective
  rw [h, g.apply_symm_apply, (S.fix_iff A hA hgen w).2 hw γ']

variable (S A hA)

@[expose] def tauOf (g : (N × F) ≃+ (N × F)) : N →+ N :=
  (AddMonoidHom.fst N F).comp (g.toAddMonoidHom.comp (AddMonoidHom.inl N F))

variable {S A hA}

theorem tauOf_apply (g : (N × F) ≃+ (N × F)) (x : N) : tauOf g x = (g (x, 0)).1 := rfl

theorem NormW.fst_g {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g) (hgen : S.GenW A hA)
    (w : N × F) : (g w).1 = tauOf g w.1 := by
  have hw : w = (w.1, 0) + (0, w.2) := by ext <;> simp
  conv_lhs => rw [hw, map_add, Prod.fst_add, hn.map_rad hgen (w := (0, w.2)) rfl, add_zero]
  rfl

theorem NormW.tau_lift {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g) (hgen : S.GenW A hA)
    (γ : Γ) {γ' : Γ} (h : ∀ w, g (S.lift (hA γ) w) = S.lift (hA γ') (g w)) (x : N) :
    tauOf g (A γ x) = A γ' (tauOf g x) := by
  have h1 := congrArg Prod.fst (h (x, 0))
  rw [hn.fst_g hgen, S.lift_fst A hA] at h1
  exact h1

end Normalizer

end burnsideI23x_SD
namespace burnsideI23x_SD

section Sigma

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)}

theorem scalar_faithful {c d : F} (h : ∀ w : N × F, c • w = d • w) : c = d := by
  have := congrArg Prod.snd (h (0, 1))
  simpa using this

theorem NormW.scalar_conj {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g)
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) (a : F) : ∃ d : F, ∀ w, g (a • g.symm w) = d • w := by
  let D : (N × F) →+ (N × F) :=
    { toFun := fun w => g (a • g.symm w)
      map_zero' := by simp
      map_add' := fun x y => by simp [smul_add] }
  refine S.comm_scalar A hA hEnd hgen D (fun γ w => ?_) (fun w hw => ?_)
  · obtain ⟨γ', h⟩ := hn.bwd γ
    show g (a • g.symm (S.lift (hA γ) w)) = S.lift (hA γ) (g (a • g.symm w))
    have h1 : g.symm (S.lift (hA γ) w) = S.lift (hA γ') (g.symm w) := by
      apply g.injective
      rw [h, g.apply_symm_apply, g.apply_symm_apply]
    rw [h1, ← map_smul, h]
  · show (g (a • g.symm w)).1 = 0
    apply hn.map_rad hgen
    rw [Prod.smul_fst, hn.symm_rad hgen hw, smul_zero]

theorem NormW.exists_sigma {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g)
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) : ∃ σ : F ≃+* F, ∀ (a : F) (w : N × F), g (a • w) = σ a • g w := by
  choose σ0 hσ0 using fun a => hn.scalar_conj hEnd hgen a
  have hs : ∀ (a : F) (w : N × F), g (a • w) = σ0 a • g w := by
    intro a w
    have := hσ0 a (g w)
    rwa [g.symm_apply_apply] at this
  have hadd : ∀ a b : F, σ0 (a + b) = σ0 a + σ0 b := by
    intro a b
    apply scalar_faithful (N := N)
    intro w
    have h1 := hs (a + b) (g.symm w)
    rw [add_smul, map_add, hs, hs, g.apply_symm_apply] at h1
    rw [add_smul]
    exact h1.symm
  have hmul : ∀ a b : F, σ0 (a * b) = σ0 a * σ0 b := by
    intro a b
    apply scalar_faithful (N := N)
    intro w
    have h1 := hs (a * b) (g.symm w)
    rw [mul_smul, hs, hs, g.apply_symm_apply] at h1
    rw [mul_smul]
    exact h1.symm
  have hone : σ0 1 = 1 := by
    apply scalar_faithful (N := N)
    intro w
    have h1 := hs 1 (g.symm w)
    rw [one_smul, g.apply_symm_apply] at h1
    rw [one_smul]
    exact h1.symm
  let σr : F →+* F :=
    { toFun := σ0
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have := hadd 0 0
        simpa using this
      map_add' := hadd }
  have hinj : Function.Injective σr := fun a b hab => by
    have h1 : σ0 a = σ0 b := hab
    have h2 : ∀ w : N × F, a • w = b • w := fun w => by
      apply g.injective
      rw [hs, hs, h1]
    exact scalar_faithful (N := N) h2
  exact ⟨RingEquiv.ofBijective σr ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩,
    fun a w => hs a w⟩

end Sigma

end burnsideI23x_SD
namespace burnsideI23x_SD

section Form

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)}

theorem nondegenerate (S : burnsideI23x_SD F N) : S.B.Nondegenerate := by
  have hsymm : ∀ x y, S.B x y = S.B y x := fun x y => by
    have h := S.alt (x + y)
    simp only [map_add, LinearMap.add_apply, S.alt, zero_add, add_zero] at h
    have h2 := add_self_F (S.B y x)
    linear_combination h - h2
  refine ⟨fun x hx => S.nondeg x hx, fun y hy => S.nondeg y (fun x => ?_)⟩
  rw [hsymm]
  exact hy x

theorem tauOf_smul {g : (N × F) ≃+ (N × F)} {σ : F ≃+* F}
    (hσ : ∀ (a : F) (w : N × F), g (a • w) = σ a • g w) (a : F) (x : N) :
    tauOf g (a • x) = σ a • tauOf g x := by
  rw [tauOf_apply, tauOf_apply]
  have h : (a • x, (0 : F)) = a • (x, (0 : F)) := by simp
  rw [h, hσ, Prod.smul_fst]

theorem NormW.tau_surj {g : (N × F) ≃+ (N × F)} (hn : NormW S A hA g) (hgen : S.GenW A hA)
    (x' : N) : ∃ x, tauOf g x = x' := by
  refine ⟨(g.symm (x', 0)).1, ?_⟩
  rw [← hn.fst_g hgen, g.apply_symm_apply]

end Form

end burnsideI23x_SD
namespace burnsideI23x_SD

section Form2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)}

include hA in
theorem B_symp_left (γ : Γ) (a y : N) : S.B (A γ a) y = S.B a (A γ⁻¹ y) := by
  have h := hA γ a (A γ⁻¹ y)
  have e : A γ (A γ⁻¹ y) = y := by
    have := congrArg (fun f : N ≃ₗ[F] N => f y)
      (show A γ * A γ⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
    simpa using this
  rw [e] at h
  exact h

theorem NormW.exists_form_scalar [Nontrivial N] [Finite N] {g : (N × F) ≃+ (N × F)}
    (hn : NormW S A hA g)
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) {σ : F ≃+* F} (hσ : ∀ (a : F) (w : N × F), g (a • w) = σ a • g w) :
    ∃ ν : F, ν ≠ 0 ∧ ∀ x y, S.B (tauOf g x) (tauOf g y) = ν * σ (S.B x y) := by
  classical
  let Bp : LinearMap.BilinForm F N :=
    LinearMap.mk₂ F (fun x y => σ.symm (S.B (tauOf g x) (tauOf g y)))
      (fun x x' y => by simp only [map_add, LinearMap.add_apply])
      (fun a x y => by simp [tauOf_smul hσ, map_mul])
      (fun x y y' => by simp only [map_add])
      (fun a x y => by simp [tauOf_smul hσ, map_mul])
  have hBp : ∀ x y, Bp x y = σ.symm (S.B (tauOf g x) (tauOf g y)) := fun x y => rfl
  have hinv : ∀ γ x y, Bp (A γ x) (A γ y) = Bp x y := by
    intro γ x y
    obtain ⟨γ', h⟩ := hn.fwd γ
    rw [hBp, hBp, hn.tau_lift hgen γ h, hn.tau_lift hgen γ h, hA γ']
  haveI : FiniteDimensional F N := Module.Finite.of_finite
  have hnd := S.nondegenerate
  let Bf : LinearMap.BilinForm F N := S.B
  let φ : N →ₗ[F] N :=
    ((LinearMap.BilinForm.toDual Bf hnd).symm : Module.Dual F N →ₗ[F] N).comp Bp
  have hφ : ∀ x y, S.B (φ x) y = Bp x y := fun x y =>
    LinearMap.BilinForm.apply_toDual_symm_apply (B := Bf) (hB := hnd) (Bp x) y
  have hcomm : ∀ γ x, φ.toAddMonoidHom (A γ x) = A γ (φ.toAddMonoidHom x) := by
    intro γ x
    show φ (A γ x) = A γ (φ x)
    have e : ∀ y, A γ (A γ⁻¹ y) = y := fun y => by
      have := congrArg (fun f : N ≃ₗ[F] N => f y)
        (show A γ * A γ⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
      simpa using this
    have h0 : φ (A γ x) - A γ (φ x) = 0 := by
      apply S.nondeg
      intro y
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hφ, B_symp_left (hA := hA) γ, hφ]
      have := hinv γ x (A γ⁻¹ y)
      rw [e] at this
      exact this
    exact sub_eq_zero.1 h0
  obtain ⟨μ, hμ⟩ := hEnd φ.toAddMonoidHom hcomm
  have hform : ∀ x y, S.B (tauOf g x) (tauOf g y) = σ μ * σ (S.B x y) := by
    intro x y
    have h1 : Bp x y = μ * S.B x y := by
      rw [← hφ]
      have : φ x = μ • x := hμ x
      rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hBp] at h1
    have h2 := congrArg σ h1
    rw [σ.apply_symm_apply, map_mul] at h2
    exact h2
  refine ⟨σ μ, ?_, hform⟩
  intro h0
  have hz : ∀ a b : N, S.B a b = 0 := by
    intro a b
    obtain ⟨x, rfl⟩ := hn.tau_surj hgen a
    obtain ⟨y, rfl⟩ := hn.tau_surj hgen b
    rw [hform, h0, zero_mul]
  obtain ⟨x, hx⟩ := exists_ne (0 : N)
  exact hx (S.nondeg x (fun y => hz x y))

end Form2

end burnsideI23x_SD
namespace burnsideI23x_SD

section Normalizer3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)}

theorem Q0_zero (S : burnsideI23x_SD F N) : S.Q0 0 = 0 := by
  have := S.Q0_smul (0 : F) 0
  simpa using this

theorem Qw_zero (S : burnsideI23x_SD F N) : S.Qw 0 = 0 := by
  show S.Q0 (0 : N × F).1 + (0 : N × F).2 ^ 2 = 0
  simp [S.Q0_zero]

theorem NormW.exists_semilinear_isometry [Nontrivial N] [Finite N] {g : (N × F) ≃+ (N × F)}
    (hn : NormW S A hA g)
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) :
    ∃ (σ : F ≃+* F) (c : F), c ≠ 0 ∧ (∀ (a : F) (w : N × F), g (a • w) = σ a • g w) ∧
      ∀ w : N × F, S.Qw (c • g w) = σ (S.Qw w) := by
  obtain ⟨σ, hσ⟩ := hn.exists_sigma hEnd hgen
  obtain ⟨ν, hν, hform⟩ := hn.exists_form_scalar hEnd hgen hσ
  have hcsq : (burnsideI23x_sqrt F ν⁻¹) ^ 2 = ν⁻¹ := burnsideI23x_sqrt_sq _
  have hc0 : burnsideI23x_sqrt F ν⁻¹ ≠ 0 := by
    intro h0
    rw [h0] at hcsq
    have : ν⁻¹ = 0 := by simpa using hcsq.symm
    exact hν (inv_eq_zero.1 this)
  refine ⟨σ, burnsideI23x_sqrt F ν⁻¹, hc0, hσ, ?_⟩
  set c := burnsideI23x_sqrt F ν⁻¹ with hcdef
  have hc : c ^ 2 * ν = 1 := by rw [hcsq]; exact inv_mul_cancel₀ hν
  have hΦ1 : ∀ w : N × F, (c • g w).1 = c • tauOf g w.1 := by
    intro w
    rw [Prod.smul_fst, hn.fst_g hgen]
  have hBΦ : ∀ w w' : N × F, S.Bw (c • g w) (c • g w') = σ (S.Bw w w') := by
    intro w w'
    show S.B (c • g w).1 (c • g w').1 = σ (S.B w.1 w'.1)
    rw [hΦ1, hΦ1]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hform]
    linear_combination (σ (S.B w.1 w'.1)) * hc
  let D : (N × F) →+ F :=
    { toFun := fun w => S.Qw (c • g w) + σ (S.Qw w)
      map_zero' := by simp [S.Qw_zero]
      map_add' := fun w w' => by
        have h1 : c • g (w + w') = c • g w + c • g w' := by rw [map_add, smul_add]
        rw [h1, S.Qw_add, S.Qw_add, map_add, map_add, hBΦ]
        have := add_self_F (σ (S.Bw w w'))
        linear_combination this }
  have hD : ∀ w, S.Qw (c • g w) + σ (S.Qw w) = 0 := by
    have hv : ∀ (γ : Γ) (x : N × F), D (S.lift (hA γ) x - x) = 0 := by
      intro γ x
      obtain ⟨γ', h⟩ := hn.fwd γ
      have h1 : D (S.lift (hA γ) x) = D x := by
        show S.Qw (c • g (S.lift (hA γ) x)) + σ (S.Qw (S.lift (hA γ) x)) =
          S.Qw (c • g x) + σ (S.Qw x)
        rw [h, ← map_smul, S.Qw_lift, S.Qw_lift]
      rw [map_sub, h1, sub_self]
    intro w
    exact S.vanish_of_gen A hA hgen D hv w
  intro w
  have := add_self_F (σ (S.Qw w))
  have hDw := hD w
  linear_combination hDw - this

end Normalizer3

end burnsideI23x_SD
namespace burnsideI23x_SD

section GW

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

@[expose] def gW (ψ : U ≃* Multiplicative (N × F)) (g : MulAut U) : (N × F) ≃+ (N × F) :=
  AddEquiv.toMultiplicative.symm (ψ.symm.trans (g.trans ψ))

theorem gW_apply (ψ : U ≃* Multiplicative (N × F)) (g : MulAut U) (w : N × F) :
    gW ψ g w = Multiplicative.toAdd (ψ (g (ψ.symm (Multiplicative.ofAdd w)))) := rfl

theorem gW_mul (ψ : U ≃* Multiplicative (N × F)) (g h : MulAut U) (w : N × F) :
    gW ψ (g * h) w = gW ψ g (gW ψ h w) := by
  rw [gW_apply, gW_apply, gW_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply, MulAut.mul_apply]

theorem gW_one (ψ : U ≃* Multiplicative (N × F)) (w : N × F) : gW ψ 1 w = w := by
  rw [gW_apply]
  simp

theorem gW_inv (ψ : U ≃* Multiplicative (N × F)) (g : MulAut U) (w : N × F) :
    gW ψ g⁻¹ (gW ψ g w) = w := by
  rw [← gW_mul, inv_mul_cancel, gW_one]

theorem gW_pow (ψ : U ≃* Multiplicative (N × F)) (g : MulAut U) (k : ℕ) (w : N × F) :
    gW ψ (g ^ k) w = (gW ψ g)^[k] w := by
  induction k generalizing w with
  | zero => simp [gW_one]
  | succ k ih =>
    rw [pow_succ, gW_mul, ih, Function.iterate_succ_apply]

theorem gW_lift (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)} (π : Γ →* ↥L)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u)) (γ : Γ)
    (w : N × F) : gW ψ (π γ : MulAut U) w = S.lift (hA γ) w := by
  rw [gW_apply, hψ, MulEquiv.apply_symm_apply]
  rfl

theorem normW_gW (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)} (π : Γ →* ↥L)
    (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    {g : MulAut U} (h1 : ∀ l ∈ L, g * l * g⁻¹ ∈ L) (h2 : ∀ l ∈ L, g⁻¹ * l * g ∈ L) :
    NormW S A hA (gW ψ g) := by
  refine ⟨fun γ => ?_, fun γ => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hπs ⟨g * (π γ : MulAut U) * g⁻¹, h1 _ (π γ).2⟩
    refine ⟨γ', fun w => ?_⟩
    have hmul : g * (π γ : MulAut U) = (π γ' : MulAut U) * g := by
      have := congrArg Subtype.val hγ'
      simp only at this
      rw [this]
      group
    rw [← gW_lift ψ π hψ γ, ← gW_lift ψ π hψ γ', ← gW_mul, ← gW_mul, hmul]
  · obtain ⟨γ', hγ'⟩ := hπs ⟨g⁻¹ * (π γ : MulAut U) * g, h2 _ (π γ).2⟩
    refine ⟨γ', fun w => ?_⟩
    have hmul : g * (π γ' : MulAut U) = (π γ : MulAut U) * g := by
      have := congrArg Subtype.val hγ'
      simp only at this
      rw [this]
      group
    rw [← gW_lift ψ π hψ γ, ← gW_lift ψ π hψ γ', ← gW_mul, ← gW_mul, hmul]

end GW

end burnsideI23x_SD
theorem burnsideI23x_pCoreOf_isPGroup {X : Type*} [Group X] (H : Subgroup X) :
    IsPGroup 2 (pCoreOf 2 H) := by
  have h : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
  exact h.map H.subtype

theorem burnsideI23x_pCoreOf_le {X : Type*} [Group X] (H : Subgroup X) : pCoreOf 2 H ≤ H := by
  rintro _ ⟨h, _, rfl⟩
  exact h.2

theorem burnsideI23x_pCoreOf_conj {X : Type*} [Group X] {H : Subgroup X} {h x : X} (hh : h ∈ H)
    (hx : x ∈ pCoreOf 2 H) : h * x * h⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, ?_, rfl⟩
  exact (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem y hy ⟨h, hh⟩

theorem burnsideI23x_pow_two_pow_eq_one {F : Type} [Field F] [CharP F 2] {c : F} {k : ℕ}
    (h : c ^ 2 ^ k = 1) : c = 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply burnsideI23x_sq_injective
    rw [← pow_mul, ← pow_succ]
    simpa using h
namespace burnsideI23x_SD

section CC

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] [Nontrivial N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ]
  {A : Γ →* (N ≃ₗ[F] N)} {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

theorem tauOf_gW_mul (ψ : U ≃* Multiplicative (N × F)) (hgen : S.GenW A hA) {a : MulAut U}
    (hn : NormW S A hA (gW ψ a)) (b : MulAut U) (x : N) :
    tauOf (gW ψ (a * b)) x = tauOf (gW ψ a) (tauOf (gW ψ b) x) := by
  rw [tauOf_apply, gW_mul, hn.fst_g hgen, ← tauOf_apply]

theorem tauOf_gW_one (ψ : U ≃* Multiplicative (N × F)) (x : N) : tauOf (gW ψ 1) x = x := by
  rw [tauOf_apply, gW_one]

theorem tauOf_gW_lift (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u)) (γ : Γ) (x : N) :
    tauOf (gW ψ (π γ : MulAut U)) x = A γ x := by
  rw [tauOf_apply, gW_lift ψ π hψ]
  rfl

theorem trivial_of_tau_trivial (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) {ℓ : AddSubgroup N} (hℓF : ∀ (a : F) (x : N), x ∈ ℓ → a • x ∈ ℓ)
    {e₀ : N} (he₀ : e₀ ∈ ℓ) (he₀0 : e₀ ≠ 0) {x : MulAut U} {k : ℕ} (hxk : x ^ 2 ^ k = 1)
    (h1 : ∀ l ∈ L, x * l * x⁻¹ ∈ L) (h2 : ∀ l ∈ L, x⁻¹ * l * x ∈ L)
    (htau : ∀ e ∈ ℓ, tauOf (gW ψ x) e = e) (w : N × F) (hw : w.1 ∈ ℓ) :
    gW ψ x w = w := by
  have hn : NormW S A hA (gW ψ x) := normW_gW ψ π hπs hψ h1 h2
  obtain ⟨σ, c, hc0, hsemi, hiso⟩ := hn.exists_semilinear_isometry hEnd hgen
  have hσ : ∀ a : F, σ a = a := by
    intro a
    have e1 : (gW ψ x ((a • e₀, (0 : F)))).1 = a • e₀ := by
      rw [hn.fst_g hgen]
      exact htau _ (hℓF a e₀ he₀)
    have e2 : (gW ψ x (a • (e₀, (0 : F)))).1 = σ a • e₀ := by
      rw [hsemi, Prod.smul_fst, hn.fst_g hgen]
      show σ a • tauOf (gW ψ x) e₀ = σ a • e₀
      rw [htau _ he₀]
    have e3 : (a • (e₀, (0 : F))) = (a • e₀, (0 : F)) := by simp
    rw [e3] at e2
    have e4 : σ a • e₀ = a • e₀ := e2.symm.trans e1
    have e5 : (σ a - a) • e₀ = 0 := by rw [sub_smul, e4, sub_self]
    rcases smul_eq_zero.1 e5 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h he₀0
  have hQ : ∀ w : N × F, S.Qw (c • gW ψ x w) = S.Qw w := fun w => by rw [hiso, hσ]
  have hrad : ∀ z : F, gW ψ x (0, z) = (0, c⁻¹ * z) := by
    intro z
    have h0 : (gW ψ x (0, z)).1 = 0 := hn.map_rad hgen rfl
    obtain ⟨ζ, hζ⟩ : ∃ ζ : F, gW ψ x (0, z) = (0, ζ) := ⟨(gW ψ x (0, z)).2, Prod.ext h0 rfl⟩
    have := hQ (0, z)
    rw [hζ] at this
    have e6 : S.Qw (c • ((0 : N), ζ)) = (c * ζ) ^ 2 := by
      show S.Q0 (c • (0 : N)) + (c * ζ) ^ 2 = (c * ζ) ^ 2
      rw [smul_zero, S.Q0_zero, zero_add]
    have e7 : S.Qw ((0 : N), z) = z ^ 2 := by
      show S.Q0 0 + z ^ 2 = z ^ 2
      rw [S.Q0_zero, zero_add]
    rw [e6, e7] at this
    have e8 : c * ζ = z := burnsideI23x_sq_injective this
    rw [hζ]
    congr 1
    rw [← e8]
    field_simp
  have hiter : ∀ j : ℕ, (gW ψ x)^[j] (0, 1) = (0, (c⁻¹) ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hrad]
      simp [pow_succ, mul_comm]
  have hc1 : c = 1 := by
    have h3 : gW ψ (x ^ 2 ^ k) (0, 1) = (0, 1) := by rw [hxk, gW_one]
    rw [gW_pow, hiter] at h3
    have h4 : (c⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Prod.snd h3
    have h5 : c ^ 2 ^ k = 1 := by
      have h6 : (c ^ 2 ^ k)⁻¹ = 1 := by rw [← inv_pow]; exact h4
      simpa using h6
    exact burnsideI23x_pow_two_pow_eq_one h5
  have hQ1 : S.Qw (gW ψ x w) = S.Qw w := by
    have := hQ w
    rwa [hc1, one_smul] at this
  have hw1 : (gW ψ x w).1 = w.1 := by
    rw [hn.fst_g hgen]
    exact htau _ hw
  refine Prod.ext hw1 ?_
  have h6 : (gW ψ x w).2 ^ 2 = w.2 ^ 2 := by
    have e9 : S.Q0 (gW ψ x w).1 + (gW ψ x w).2 ^ 2 = S.Q0 w.1 + w.2 ^ 2 := hQ1
    rw [hw1] at e9
    linear_combination e9
  exact burnsideI23x_sq_injective h6

end CC

end burnsideI23x_SD
namespace burnsideI23x_SD

section CC2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] [Nontrivial N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ]
  {A : Γ →* (N ≃ₗ[F] N)} {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

open CFSG.Quasithin in
theorem tau_trivial_of_pCore (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    (hgen : S.GenW A hA) {G : Subgroup (MulAut U)} (hLG : L ≤ G)
    (hnormG : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) {ℓ : AddSubgroup N} {Ui : Subgroup U}
    (hUi : ∀ u, u ∈ Ui ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ) {e₀ : N} (he₀ : e₀ ∈ ℓ)
    (he₀0 : e₀ ≠ 0)
    (hirr : ∀ C : AddSubgroup N, C ≠ ⊥ → C ≤ ℓ →
      (∀ γ, (∀ x, A γ x ∈ ℓ ↔ x ∈ ℓ) → ∀ x ∈ C, A γ x ∈ C) → ℓ ≤ C) :
    ∀ y ∈ pCoreOf 2 (G ⊓ stabSub Ui), ∀ e ∈ ℓ, tauOf (gW ψ y) e = e := by
  classical
  set H := G ⊓ stabSub Ui with hH
  have hNorm : ∀ y ∈ G, NormW S A hA (gW ψ y) := fun y hy =>
    normW_gW ψ π hπs hψ (hnormG y hy)
      (fun l hl => by simpa using hnormG y⁻¹ (G.inv_mem hy) l hl)
  have hmem : ∀ y ∈ H, ∀ e ∈ ℓ, tauOf (gW ψ y) e ∈ ℓ := by
    intro y hy e he
    have hu : ψ.symm (Multiplicative.ofAdd (e, (0 : F))) ∈ Ui := by
      rw [hUi]; simpa using he
    have hyu : y (ψ.symm (Multiplicative.ofAdd (e, (0 : F)))) ∈ Ui := (hy.2 _).2 hu
    rw [hUi] at hyu
    exact hyu
  have hXp : IsPGroup 2 (pCoreOf 2 H) := burnsideI23x_pCoreOf_isPGroup H
  have hXH : pCoreOf 2 H ≤ H := burnsideI23x_pCoreOf_le H
  let act : MulAction (pCoreOf 2 H) ℓ :=
    { smul := fun y e => ⟨tauOf (gW ψ (y : MulAut U)) (e : N), hmem y (hXH y.2) e e.2⟩
      one_smul := fun e => Subtype.ext (tauOf_gW_one ψ (e : N))
      mul_smul := fun y z e => Subtype.ext
        (tauOf_gW_mul ψ hgen (hNorm y (hXH y.2).1) (z : MulAut U) (e : N)) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ℓ := by
    have h1 : addOrderOf (⟨e₀, he₀⟩ : ℓ) = 2 := by
      apply addOrderOf_eq_prime
      · apply Subtype.ext
        have h2 : e₀ + e₀ = 0 := by
          have := two_eq_zero_F (F := F)
          calc e₀ + e₀ = (2 : F) • e₀ := by rw [two_smul]
            _ = 0 := by rw [this, zero_smul]
        simp only [two_nsmul, AddSubgroup.coe_add, AddSubgroup.coe_zero]
        exact h2
      · intro h
        exact he₀0 (congrArg Subtype.val h)
    rw [← h1]
    exact addOrderOf_dvd_natCard _
  have h0 : (0 : ℓ) ∈ MulAction.fixedPoints (pCoreOf 2 H) ℓ := fun y => by
    apply Subtype.ext
    exact map_zero (tauOf (gW ψ (y : MulAut U)))
  obtain ⟨b, hb, hb0⟩ := hXp.exists_fixed_point_of_prime_dvd_card_of_fixed_point ℓ hdvd h0
  let C : AddSubgroup N :=
    { carrier := {e | e ∈ ℓ ∧ ∀ y ∈ pCoreOf 2 H, tauOf (gW ψ y) e = e}
      zero_mem' := ⟨ℓ.zero_mem, fun y _ => map_zero _⟩
      add_mem' := fun {a b} ha hb => ⟨ℓ.add_mem ha.1 hb.1, fun y hy => by
        rw [map_add, ha.2 y hy, hb.2 y hy]⟩
      neg_mem' := fun {a} ha => ⟨ℓ.neg_mem ha.1, fun y hy => by
        rw [map_neg, ha.2 y hy]⟩ }
  have hCb : (b : N) ∈ C := ⟨b.2, fun y hy => congrArg Subtype.val (hb ⟨y, hy⟩)⟩
  have hCne : C ≠ ⊥ := by
    intro h
    have : (b : N) = 0 := by
      have := hCb
      rw [h] at this
      exact (AddSubgroup.mem_bot.1 this)
    exact hb0 (Subtype.ext this.symm)
  have hCle : C ≤ ℓ := fun e he => he.1
  have hCinv : ∀ γ, (∀ x, A γ x ∈ ℓ ↔ x ∈ ℓ) → ∀ x ∈ C, A γ x ∈ C := by
    intro γ hγ x hx
    refine ⟨(hγ x).2 hx.1, fun y hy => ?_⟩
    have hl : (π γ : MulAut U) ∈ H := by
      refine Subgroup.mem_inf.2 ⟨hLG (π γ).2, ?_⟩
      rw [mem_stabSub]
      intro u
      rw [hUi, hUi, hψ]
      show (S.lift (hA γ) (Multiplicative.toAdd (ψ u))).1 ∈ ℓ ↔ _
      rw [S.lift_fst A hA]
      exact hγ _
    have hy' : (π γ : MulAut U)⁻¹ * y * (π γ : MulAut U) ∈ pCoreOf 2 H := by
      have := burnsideI23x_pCoreOf_conj (H := H) (H.inv_mem hl) hy
      simpa using this
    have hy2 : y * (π γ : MulAut U) = (π γ : MulAut U) * ((π γ : MulAut U)⁻¹ * y * (π γ : MulAut U)) := by
      group
    have e1 := tauOf_gW_mul ψ hgen (hNorm y (hXH hy).1) (π γ : MulAut U) x
    rw [tauOf_gW_lift ψ π hψ] at e1
    rw [← e1, hy2, tauOf_gW_mul ψ hgen (hNorm _ (hLG (π γ).2)), hx.2 _ hy',
      tauOf_gW_lift ψ π hψ]
  intro y hy e he
  exact (hirr C hCne hCle hCinv he).2 y hy

end CC2

end burnsideI23x_SD
theorem burnsideI23x_exists_fixed_of_isPGroup {W : Type*} [CommGroup W] [Finite W]
    {S : Subgroup (MulAut W)} (hS : IsPGroup 2 S) {U : Subgroup W}
    (hU : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U) (hUne : U ≠ ⊥) (hU2 : IsPGroup 2 U) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ s ∈ S, s u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction S U :=
    { smul := fun s u => ⟨(s : MulAut W) u, hU s s.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun s t u => Subtype.ext rfl }
  have hdvd : 2 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hUne
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have h1 : (1 : U) ∈ MulAction.fixedPoints S U := fun s =>
    Subtype.ext (map_one (s : MulAut W))
  obtain ⟨b, hb, hb1⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun s hs => ?_⟩
  exact congrArg Subtype.val (hb ⟨s, hs⟩)

namespace burnsideI23x_SD

section CC3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] [Nontrivial N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ]
  {A : Γ →* (N ≃ₗ[F] N)} {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

open CFSG.Quasithin in
theorem central_core (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) {G : Subgroup (MulAut U)} (hLG : L ≤ G)
    (hnormG : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) {ℓ : AddSubgroup N}
    (hℓF : ∀ (a : F) (x : N), x ∈ ℓ → a • x ∈ ℓ) {Ui : Subgroup U}
    (hUi : ∀ u, u ∈ Ui ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ) {e₀ : N} (he₀ : e₀ ∈ ℓ)
    (he₀0 : e₀ ≠ 0)
    (hirr : ∀ C : AddSubgroup N, C ≠ ⊥ → C ≤ ℓ →
      (∀ γ, (∀ x, A γ x ∈ ℓ ↔ x ∈ ℓ) → ∀ x ∈ C, A γ x ∈ C) → ℓ ≤ C) :
    pCoreOf 2 (G ⊓ stabSub Ui) ≤ centSub Ui := by
  intro x hx
  rw [mem_centSub]
  intro u hu
  have hxG : x ∈ G := (burnsideI23x_pCoreOf_le _ hx).1
  have htau := tau_trivial_of_pCore ψ π hπs hψ hgen hLG hnormG hUi he₀ he₀0 hirr x hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := burnsideI23x_pCoreOf_isPGroup (G ⊓ stabSub Ui) ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have h1 : ∀ l ∈ L, x * l * x⁻¹ ∈ L := hnormG x hxG
  have h2 : ∀ l ∈ L, x⁻¹ * l * x ∈ L := fun l hl => by
    simpa using hnormG x⁻¹ (G.inv_mem hxG) l hl
  have h3 := trivial_of_tau_trivial ψ π hπs hψ hEnd hgen hℓF he₀ he₀0 hk h1 h2 htau
    (Multiplicative.toAdd (ψ u)) ((hUi u).1 hu)
  rw [gW_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h3
  apply ψ.injective
  exact Multiplicative.toAdd.injective h3

open CFSG.Quasithin in
theorem exists_T_fixed (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    (hEnd : ∀ φ : N →+ N, (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x)
    (hgen : S.GenW A hA) {G T : Subgroup (MulAut U)} (hTG : T ≤ G)
    (hnormG : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hT2 : IsPGroup 2 T) [Finite U]
    {ℓ : AddSubgroup N} {e₀ : N} (he₀0 : e₀ ≠ 0) (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀)
    {U1 : Subgroup U} (hU1 : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ)
    (hTU1 : ∀ t ∈ T, ∀ u ∈ U1, t u ∈ U1) :
    ∃ u ∈ U1, u ∈ fixV T ∧ u ∉ fixV L := by
  classical
  set z₀ : F := burnsideI23x_sqrt F (S.Q0 e₀) with hz₀
  set s₀ : N × F := (e₀, z₀) with hs₀
  have hz₀sq : z₀ ^ 2 = S.Q0 e₀ := burnsideI23x_sqrt_sq _
  have hQs₀ : S.Qw s₀ = 0 := by
    show S.Q0 e₀ + z₀ ^ 2 = 0
    rw [hz₀sq]
    exact add_self_F _
  let P : Subgroup U :=
    { carrier := {u | ∃ a : F, Multiplicative.toAdd (ψ u) = a • s₀}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := fun {u v} hu hv => by
        obtain ⟨a, ha⟩ := hu
        obtain ⟨b, hb⟩ := hv
        exact ⟨a + b, by rw [map_mul, toAdd_mul, ha, hb, add_smul]⟩
      inv_mem' := fun {u} hu => by
        obtain ⟨a, ha⟩ := hu
        exact ⟨-a, by rw [map_inv, toAdd_inv, ha, neg_smul]⟩ }
  have hmemP : ∀ u, u ∈ P ↔ ∃ a : F, Multiplicative.toAdd (ψ u) = a • s₀ := fun u => Iff.rfl
  have hs₀ne : s₀ ≠ 0 := fun h => he₀0 (congrArg Prod.fst h)
  have hu₀ : ψ.symm (Multiplicative.ofAdd s₀) ∈ P := ⟨1, by simp⟩
  have hPne : P ≠ ⊥ := by
    intro h
    have : ψ.symm (Multiplicative.ofAdd s₀) = 1 := by
      have := hu₀
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    apply hs₀ne
    have h1 := congrArg ψ this
    rw [MulEquiv.apply_symm_apply, map_one] at h1
    exact Multiplicative.ofAdd.injective h1
  have hP2 : IsPGroup 2 P := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have : (g : U) ^ 2 = 1 := by
      apply ψ.injective
      rw [map_pow, map_one]
      exact burnsideI23x_SD.sq_eq_one_W (F := F) (N := N) _
    simpa using this
  have hTP : ∀ t ∈ T, ∀ p ∈ P, t p ∈ P := by
    intro t ht p hp
    have hG : t ∈ G := hTG ht
    have hn : NormW S A hA (gW ψ t) :=
      normW_gW ψ π hπs hψ (hnormG t hG) (fun l hl => by simpa using hnormG t⁻¹ (G.inv_mem hG) l hl)
    obtain ⟨σ, c, hc0, hsemi, hiso⟩ := hn.exists_semilinear_isometry hEnd hgen
    obtain ⟨a, ha⟩ := hp
    have hu₀U1 : ψ.symm (Multiplicative.ofAdd s₀) ∈ U1 := by
      rw [hU1]; simpa using (show e₀ ∈ ℓ from (hℓ e₀).2 ⟨1, by simp⟩)
    have hgs₀ : ∃ b : F, gW ψ t s₀ = b • s₀ := by
      have h1 := hTU1 t ht _ hu₀U1
      rw [hU1] at h1
      have h2 : (gW ψ t s₀) = Multiplicative.toAdd
          (ψ (t (ψ.symm (Multiplicative.ofAdd s₀)))) := rfl
      rw [← h2] at h1
      obtain ⟨b, hb⟩ := (hℓ _).1 h1
      have hq : S.Qw (gW ψ t s₀) = 0 := by
        have := hiso s₀
        rw [hQs₀, map_zero, Qw_smul] at this
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (pow_eq_zero_iff (two_ne_zero)|>.1 h) hc0
        · exact h
      refine ⟨b, ?_⟩
      have hfst : (gW ψ t s₀).1 = b • e₀ := hb
      have hsq : (gW ψ t s₀).2 ^ 2 = (b * z₀) ^ 2 := by
        have e1 : S.Q0 (gW ψ t s₀).1 + (gW ψ t s₀).2 ^ 2 = 0 := hq
        rw [hfst, S.Q0_smul] at e1
        have e2 := add_self_F (b ^ 2 * S.Q0 e₀)
        rw [mul_pow, hz₀sq]
        linear_combination e1 - e2
      have hsnd : (gW ψ t s₀).2 = b * z₀ := burnsideI23x_sq_injective hsq
      exact Prod.ext (by rw [hfst]; rfl) (by rw [hsnd]; rfl)
    obtain ⟨b, hb⟩ := hgs₀
    refine ⟨σ a * b, ?_⟩
    have h3 : Multiplicative.toAdd (ψ (t p)) = gW ψ t (Multiplicative.toAdd (ψ p)) := by
      rw [gW_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    rw [h3, ha, hsemi, hb, smul_smul]
  obtain ⟨p, hpP, hp1, hpT⟩ := burnsideI23x_exists_fixed_of_isPGroup hT2 hTP hPne hP2
  refine ⟨p, ?_, fun t ht => hpT t ht, fun hpL => ?_⟩
  · obtain ⟨a, ha⟩ := hpP
    rw [hU1, ha]
    exact (hℓ _).2 ⟨a, by simp [hs₀]⟩
  · obtain ⟨a, ha⟩ := hpP
    have hfix : ∀ γ, S.lift (hA γ) (Multiplicative.toAdd (ψ p)) = Multiplicative.toAdd (ψ p) := by
      intro γ
      have := hψ γ p
      rw [mem_fixV.1 hpL (π γ : MulAut U) (π γ).2] at this
      have h2 := congrArg Multiplicative.toAdd this
      exact h2.symm
    have h4 := (S.fix_iff A hA hgen _).1 hfix
    rw [ha] at h4
    have h5 : a • e₀ = 0 := by simpa [hs₀] using h4
    have ha0 : a = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact h
      · exact absurd h he₀0
    apply hp1
    apply ψ.injective
    apply Multiplicative.toAdd.injective
    rw [ha, ha0, zero_smul]
    simp

end CC3

end burnsideI23x_SD
namespace burnsideI23x_SD

section Tv

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem B_comm (x y : N) : S.B x y = S.B y x := by
  have h := S.alt (x + y)
  simp only [map_add, LinearMap.add_apply, S.alt, zero_add, add_zero] at h
  have h2 := add_self_F (S.B y x)
  linear_combination h - h2

theorem B_zero_left (y : N) : S.B 0 y = 0 := by simp

theorem Q0_add_smul (x e : N) (a : F) :
    S.Q0 (x + a • e) = S.Q0 x + a ^ 2 * S.Q0 e + a * S.B x e := by
  rw [S.Q0_add, S.Q0_smul]
  simp [map_smul]

@[expose] def tvLin (e : N) (c : F) : N →ₗ[F] N where
  toFun x := x + (c * S.B x e) • e
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, mul_add, add_smul]
    abel
  map_smul' a x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]
    rw [mul_left_comm]

theorem tvLin_apply (e : N) (c : F) (x : N) : S.tvLin e c x = x + (c * S.B x e) • e := rfl

theorem tvLin_invol (e : N) (c : F) (x : N) : S.tvLin e c (S.tvLin e c x) = x := by
  rw [tvLin_apply, tvLin_apply]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    mul_zero, add_zero, zero_smul]
  have h := add_self_F (c * S.B x e)
  have : x + (c * S.B x e) • e + (c * S.B x e) • e = x := by
    rw [add_assoc, ← add_smul, h, zero_smul, add_zero]
  exact this

@[expose] def tvEquiv (e : N) (c : F) : N ≃ₗ[F] N :=
  LinearEquiv.ofInvolutive (S.tvLin e c) (fun x => S.tvLin_invol e c x)

theorem tvEquiv_apply (e : N) (c : F) (x : N) : S.tvEquiv e c x = x + (c * S.B x e) • e := rfl

theorem tvEquiv_symp (e : N) (c : F) : S.Symp (S.tvEquiv e c) := by
  intro x y
  rw [tvEquiv_apply, tvEquiv_apply]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    mul_zero, add_zero]
  have h1 := S.B_comm e y
  have h2 := add_self_F (c * S.B x e * S.B y e)
  rw [h1]
  linear_combination h2

end Tv

end burnsideI23x_SD
namespace burnsideI23x_SD

section TvLift

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] noncomputable def tvκ (e : N) (c : F) : F :=
  burnsideI23x_sqrt F (c + c ^ 2 * S.Q0 e)

theorem tvκ_sq (e : N) (c : F) : S.tvκ e c ^ 2 = c + c ^ 2 * S.Q0 e :=
  burnsideI23x_sqrt_sq _

theorem lf_tv (e : N) (c : F) (x : N) :
    S.lf (S.tvEquiv e c) x = S.B x e * S.tvκ e c := by
  unfold lf tvκ
  rw [tvEquiv_apply, Q0_add_smul]
  have h : S.Q0 x + (S.Q0 x + (c * S.B x e) ^ 2 * S.Q0 e + c * S.B x e * S.B x e) =
      (S.B x e) ^ 2 * (c + c ^ 2 * S.Q0 e) := by
    have h2 := add_self_F (S.Q0 x)
    linear_combination h2
  rw [h, map_mul, burnsideI23x_sqrt_of_sq]

theorem lift_tv_apply (e : N) (c : F) (w : N × F) :
    S.lift (S.tvEquiv_symp e c) w =
      (w.1 + (c * S.B w.1 e) • e, w.2 + S.B w.1 e * S.tvκ e c) := by
  rw [lift_apply, tvEquiv_apply, lf_tv]

theorem exists_B_eq_one {e : N} (he : e ≠ 0) : ∃ x : N, S.B x e = 1 := by
  have h : ∃ y, S.B e y ≠ 0 := by
    by_contra hcon
    exact he (S.nondeg e (fun y => by_contra fun hy => hcon ⟨y, hy⟩))
  obtain ⟨y, hy⟩ := h
  refine ⟨(S.B e y)⁻¹ • y, ?_⟩
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, S.B_comm y e]
  exact inv_mul_cancel₀ hy

end TvLift

end burnsideI23x_SD
namespace burnsideI23x_SD

section TvGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Nontrivial N] (S : burnsideI23x_SD F N) {Γ : Type} (lin : Γ → N →ₗ[F] N)

@[expose] def GenW' : Prop :=
  ∀ w : N × F, w ∈ AddSubgroup.closure
    {y | ∃ (γ : Γ) (x : N), y = (lin γ x - x, burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x)))}

theorem genW'_of_tv (htv : ∀ (e : N) (c : F), e ≠ 0 → ∃ γ, ∀ x, lin γ x = S.tvEquiv e c x)
    {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : GenW' S lin := by
  classical
  set C : AddSubgroup (N × F) := AddSubgroup.closure
    {y | ∃ (γ : Γ) (x : N), y = (lin γ x - x, burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x)))}
    with hC
  have hsmul : ∀ (b : F) (y : N × F), y ∈ C → b • y ∈ C := by
    intro b y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨γ, x, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨γ, b • x, ?_⟩
      refine Prod.ext ?_ ?_
      · show b • (lin γ x - x) = lin γ (b • x) - b • x
        rw [map_smul, smul_sub]
      · show b * burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x)) =
          burnsideI23x_sqrt F (S.Q0 (b • x) + S.Q0 (lin γ (b • x)))
        rw [map_smul, S.Q0_smul, S.Q0_smul, ← mul_add, map_mul, burnsideI23x_sqrt_of_sq]
    | zero => simp
    | add y₁ y₂ _ _ h1 h2 => rw [smul_add]; exact C.add_mem h1 h2
    | neg y _ h => rw [smul_neg]; exact C.neg_mem h
  have hvec : ∀ (e : N) (c : F), e ≠ 0 → ((c • e, S.tvκ e c) : N × F) ∈ C := by
    intro e c he
    obtain ⟨γ, hγ⟩ := htv e c he
    obtain ⟨x, hx⟩ := S.exists_B_eq_one he
    apply AddSubgroup.subset_closure
    refine ⟨γ, x, ?_⟩
    have h1 := hγ x
    refine Prod.ext ?_ ?_
    · show c • e = lin γ x - x
      rw [h1, S.tvEquiv_apply, hx, mul_one]
      abel
    · show S.tvκ e c = burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x))
      rw [h1]
      have := S.lf_tv e c x
      unfold lf at this
      rw [this, hx, one_mul]
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : N)
  have hδ : a * S.tvκ e₀ 1 - S.tvκ e₀ a ≠ 0 := by
    intro hcon
    have h' : a * S.tvκ e₀ 1 = S.tvκ e₀ a := sub_eq_zero.1 hcon
    have hsq : (a * S.tvκ e₀ 1) ^ 2 = S.tvκ e₀ a ^ 2 := by rw [h']
    rw [mul_pow, S.tvκ_sq, S.tvκ_sq] at hsq
    have h2 : a * (a - 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 h2 with h | h
    · exact ha0 h
    · exact ha1 (sub_eq_zero.1 h)
  have hK : ∀ d : F, ((0 : N), d) ∈ C := by
    intro d
    have h1 := hsmul a _ (hvec e₀ 1 he₀)
    have h2 := hvec e₀ a he₀
    have h3 : ((a * S.tvκ e₀ 1 - S.tvκ e₀ a) • ((0 : N), (1 : F))) ∈ C := by
      have := C.sub_mem h1 h2
      convert this using 1
      refine Prod.ext ?_ ?_
      · show (a * S.tvκ e₀ 1 - S.tvκ e₀ a) • (0 : N) = (a • (1 : F) • e₀ - a • e₀)
        rw [one_smul, sub_self, smul_zero]
      · show (a * S.tvκ e₀ 1 - S.tvκ e₀ a) * 1 = a * S.tvκ e₀ 1 - S.tvκ e₀ a
        ring
    have h4 := hsmul ((a * S.tvκ e₀ 1 - S.tvκ e₀ a)⁻¹ * d) _ h3
    convert h4 using 1
    refine Prod.ext ?_ ?_
    · show (0 : N) = _
      simp
    · show d = _
      show d = ((a * S.tvκ e₀ 1 - S.tvκ e₀ a)⁻¹ * d) * ((a * S.tvκ e₀ 1 - S.tvκ e₀ a) * 1)
      field_simp
  intro w
  by_cases hw : w.1 = 0
  · have : w = ((0 : N), w.2) := Prod.ext hw rfl
    rw [this]
    exact hK _
  · have h1 := hvec w.1 1 hw
    have h2 := hK (w.2 - S.tvκ w.1 1)
    have := C.add_mem h1 h2
    convert this using 1
    refine Prod.ext ?_ ?_
    · show w.1 = (1 : F) • w.1 + 0
      rw [one_smul, add_zero]
    · show w.2 = S.tvκ w.1 1 + (w.2 - S.tvκ w.1 1)
      ring

end TvGen

end burnsideI23x_SD
namespace burnsideI23x_SD

section TvEnd

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Nontrivial N] (S : burnsideI23x_SD F N) {Γ : Type} (lin : Γ → N →ₗ[F] N)

theorem hEnd_of_tv (htv : ∀ (e : N) (c : F), e ≠ 0 → ∃ γ, ∀ x, lin γ x = S.tvEquiv e c x) :
    ∀ φ : N →+ N, (∀ γ x, φ (lin γ x) = lin γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x := by
  classical
  intro φ hφ
  have heig : ∀ e : N, e ≠ 0 → ∃ l : F, φ e = l • e := by
    intro e he
    obtain ⟨γ, hγ⟩ := htv e 1 he
    obtain ⟨x, hx⟩ := S.exists_B_eq_one he
    have h1 := hφ γ x
    rw [hγ x, hγ (φ x), S.tvEquiv_apply, S.tvEquiv_apply, hx, map_add] at h1
    refine ⟨S.B (φ x) e, ?_⟩
    have h2 : φ (((1 : F) * 1) • e) = φ x + (1 * S.B (φ x) e) • e - φ x := by
      rw [← h1]; abel
    rw [mul_one, one_smul] at h2
    rw [h2, one_mul]
    abel
  let lam : N → F := fun e => if h : e = 0 then 0 else Classical.choose (heig e h)
  have hlam : ∀ e : N, e ≠ 0 → φ e = lam e • e := by
    intro e he
    simp only [lam, dif_neg he]
    exact Classical.choose_spec (heig e he)
  have hadj : ∀ e e' : N, e ≠ 0 → e' ≠ 0 → S.B e e' ≠ 0 → lam e = lam e' := by
    intro e e' he he' hB
    have hsum : e + e' ≠ 0 := by
      intro h
      have : e' = e := by
        have h2 : e' = -e := eq_neg_of_add_eq_zero_right h
        rw [h2]
        have := add_self_F (1 : F)
        calc -e = (-1 : F) • e := by rw [neg_one_smul]
          _ = e := by
            have h3 : (-1 : F) = 1 := by
              have := two_eq_zero_F (F := F)
              linear_combination -this
            rw [h3, one_smul]
      apply hB
      rw [← this, S.alt]
    have h1 := hlam (e + e') hsum
    rw [map_add, hlam e he, hlam e' he'] at h1
    have h2 := congrArg (fun v => S.B v e') h1
    have h3 := congrArg (fun v => S.B e v) h1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.alt, mul_zero, add_zero, zero_add] at h2 h3
    have e1 : lam e = lam (e + e') := by
      have : lam e * S.B e e' = lam (e + e') * S.B e e' := by linear_combination h2
      exact mul_right_cancel₀ hB this
    have e2 : lam e' = lam (e + e') := by
      have : lam e' * S.B e e' = lam (e + e') * S.B e e' := by linear_combination h3
      exact mul_right_cancel₀ hB this
    rw [e1, e2]
  have hall : ∀ e e' : N, e ≠ 0 → e' ≠ 0 → lam e = lam e' := by
    intro e e' he he'
    obtain ⟨d, hd⟩ := S.exists_B_eq_one he
    obtain ⟨d', hd'⟩ := S.exists_B_eq_one he'
    have hd1 : S.B e d = 1 := by rw [S.B_comm]; exact hd
    have hd1' : S.B e' d' = 1 := by rw [S.B_comm]; exact hd'
    have hdne : d ≠ 0 := fun h => by rw [h] at hd1; simp at hd1
    have hd'ne : d' ≠ 0 := fun h => by rw [h] at hd1'; simp at hd1'
    by_cases h1 : S.B e' d = 0
    · by_cases h2 : S.B e d' = 0
      ·
        have hdd : d + d' ≠ 0 := by
          intro h
          have := congrArg (fun v => S.B e v) h
          simp only [map_add, map_zero] at this
          rw [hd1, h2] at this
          simp at this
        have hB1 : S.B e (d + d') ≠ 0 := by rw [map_add, hd1, h2]; simp
        have hB2 : S.B e' (d + d') ≠ 0 := by rw [map_add, h1, hd1']; simp
        exact (hadj e (d + d') he hdd hB1).trans (hadj e' (d + d') he' hdd hB2).symm
      · have hB1 := hadj e d' he hd'ne h2
        have hB2 := hadj e' d' he' hd'ne (by rw [hd1']; exact one_ne_zero)
        exact hB1.trans hB2.symm
    · have hB1 := hadj e d he hdne (by rw [hd1]; exact one_ne_zero)
      have hB2 := hadj e' d he' hdne h1
      exact hB1.trans hB2.symm
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : N)
  refine ⟨lam e₀, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, smul_zero]
  · rw [hlam x hx, hall x e₀ hx he₀]

end TvEnd

end burnsideI23x_SD
section LinHom

variable {D : CFSG.Quasithin.FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
  {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : D.Gam →* ↥H}
  {f : W → M} (LM : CFSG.Quasithin.Vol2.KGNat.LinModel D K M)

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_lin_mul (hf : IsCoord LM H Z π f) (γ δ : D.Gam) (x : M) :
    LM.lin (γ * δ) x = LM.lin γ (LM.lin δ x) := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hf.act, ← hf.act, ← hf.act, map_mul]
  rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_lin_one (hf : IsCoord LM H Z π f) (x : M) : LM.lin 1 x = x := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hf.act, map_one]
  rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
@[expose] noncomputable def burnsideI23x_linHom (hf : IsCoord LM H Z π f) :
    D.Gam →* (M ≃ₗ[K] M) where
  toFun γ := LinearEquiv.ofLinear (LM.lin γ) (LM.lin γ⁻¹)
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [← burnsideI23x_lin_mul LM hf, mul_inv_cancel, burnsideI23x_lin_one LM hf])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [← burnsideI23x_lin_mul LM hf, inv_mul_cancel, burnsideI23x_lin_one LM hf])
  map_one' := LinearEquiv.ext fun x => burnsideI23x_lin_one LM hf x
  map_mul' γ δ := LinearEquiv.ext fun x => burnsideI23x_lin_mul LM hf γ δ x

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_linHom_apply (hf : IsCoord LM H Z π f) (γ : D.Gam) (x : M) :
    burnsideI23x_linHom LM hf γ x = LM.lin γ x := rfl

end LinHom

namespace burnsideI23x_SD

section GenBridge

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ)) (lin : Γ → N →ₗ[F] N)

include hA in
theorem GenW'.toGenW (hAlin : ∀ γ x, A γ x = lin γ x) (h : S.GenW' lin) : S.GenW A hA := by
  intro w
  refine AddSubgroup.closure_mono ?_ (h w)
  rintro _ ⟨γ, x, rfl⟩
  refine ⟨γ, (x, 0), ?_⟩
  refine Prod.ext ?_ ?_
  · show lin γ x - x = A γ x - x
    rw [hAlin]
  · show burnsideI23x_sqrt F (S.Q0 x + S.Q0 (lin γ x)) = 0 + S.lf (A γ) x - 0
    unfold lf
    rw [hAlin]
    simp

end GenBridge

end burnsideI23x_SD
namespace burnsideI23x_SD

section GenMul

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ] (A : Γ →* (N ≃ₗ[F] N))
  (hA : ∀ γ, S.Symp (A γ))

include hA in
theorem genW_mul (hgen : S.GenW A hA) : ∀ w : Multiplicative (N × F), w ∈ Subgroup.closure
    {x | ∃ (γ : Γ) (y : Multiplicative (N × F)), x = S.liftHom A hA γ y * y⁻¹} := by
  intro w
  have h := hgen (Multiplicative.toAdd w)
  have key : ∀ a : N × F, a ∈ AddSubgroup.closure
      {y | ∃ (γ : Γ) (x : N × F), y = S.lift (hA γ) x - x} →
      Multiplicative.ofAdd a ∈ Subgroup.closure
        {x | ∃ (γ : Γ) (y : Multiplicative (N × F)), x = S.liftHom A hA γ y * y⁻¹} := by
    intro a ha
    induction ha using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨γ, x, rfl⟩ := hy
      apply Subgroup.subset_closure
      exact ⟨γ, Multiplicative.ofAdd x, by rw [S.liftHom_apply, ofAdd_sub, div_eq_mul_inv]⟩
    | zero => exact Subgroup.one_mem _
    | add a b _ _ h1 h2 => exact Subgroup.mul_mem _ h1 h2
    | neg a _ h => exact Subgroup.inv_mem _ h
  exact key _ h

end GenMul

end burnsideI23x_SD

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_plumb {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {M : Type} [AddCommGroup M] [Module F M] [Finite M] [Nontrivial M]
    (LM : LinModel (i23NaturalModel m F) F M) (S : burnsideI23x_SD F M)
    (hsymp : ∀ γ x y, S.B (LM.lin γ x) (LM.lin γ y) = S.B x y)
    (hfaith : ∀ γ, (∀ x, LM.lin γ x = x) → γ = 1)
    (hgenM : S.GenW' LM.lin)
    (hbound : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut V)) (W0 : Subgroup V) (π : (i23NaturalModel m F).Gam →* ↥L),
        (i23NaturalModel m F).RealizesVia L ⊤ W0 π → W0 = fixV L → commV L = ⊤ →
        Nat.card W0 ≤ Nat.card F)
    {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {L : Subgroup (MulAut U)} {K : Subgroup U} (huniv : IsUniversalCovering L K)
    {marking : (i23NaturalModel m F).Gam →* ↥L}
    {β : U →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (hsec : I23SectionMap (i23NaturalModel m F) L K marking β) :
    ∃ (A : (i23NaturalModel m F).Gam →* (M ≃ₗ[F] M)) (hA : ∀ γ, S.Symp (A γ))
      (ψ : U ≃* Multiplicative (M × F)),
      (∀ γ x, A γ x = LM.lin γ x) ∧ S.GenW A hA ∧ Function.Surjective marking ∧
      fixV L = K ∧
      (∀ (γ : (i23NaturalModel m F).Gam) (u : U),
        ψ ((marking γ : MulAut U) u) = S.liftHom A hA γ (ψ u)) ∧
      (∀ u : U, (Multiplicative.toAdd (ψ u)).1 = Multiplicative.toAdd (LM.e (β u))) := by
  classical
  have hf := burnsideI23x_isCoord LM hsec
  set A := burnsideI23x_linHom LM hf with hAdef
  have hAlin : ∀ γ x, A γ x = LM.lin γ x := fun γ x => rfl
  have hA : ∀ γ, S.Symp (A γ) := fun γ x y => hsymp γ x y
  have hgen : S.GenW A hA := burnsideI23x_SD.GenW'.toGenW S A hA LM.lin hAlin hgenM
  have hKfix : K ≤ fixV L := huniv.1
  have hcommtop : commV L = ⊤ := huniv.2.1
  have hnofix : ∀ x : M, (∀ γ, LM.lin γ x = x) → x = 0 := by
    intro x hx
    have := (S.fix_iff A hA hgen (x, 0)).1 (fun γ => by
      refine Prod.ext (hx γ) ?_
      show 0 + S.lf (A γ) x = 0
      unfold burnsideI23x_SD.lf
      rw [hAlin, hx γ, burnsideI23x_SD.add_self_F, map_zero, zero_add])
    exact this
  have hfixV : fixV L = K := burnsideI23x_fixV_eq LM hsec hKfix hnofix
  have hinj : Function.Injective marking := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply hfaith
    intro x
    obtain ⟨v, rfl⟩ := hf.surj x
    rw [← hf.act, hγ]
    rfl
  have hbij : Function.Bijective marking := ⟨hinj, hsec.1⟩
  have hbound' := hbound U hU L K marking (burnsideI23x_realizesVia hsec hKfix) hfixV.symm
    hcommtop
  let fMul : U →* Multiplicative M := LM.e.toMonoidHom.comp β
  have hfs : Function.Surjective fMul := LM.e.surjective.comp hsec.2.1
  have hfk : fMul.ker = K := by
    ext v
    rw [MonoidHom.mem_ker, ← hsec.2.2.1, MonoidHom.mem_ker]
    exact LM.e.map_eq_one_iff
  have hfπ : ∀ (γ : (i23NaturalModel m F).Gam) (v : U), fMul ((marking γ : MulAut U) v) =
      Multiplicative.ofAdd (A γ (Multiplicative.toAdd (fMul v))) := fun γ v => by
    have := hf.act γ v
    exact congrArg Multiplicative.ofAdd this
  obtain ⟨ψ, hψ1, hψ2⟩ := burnsideI23x_univ_iso S A hA hU huniv marking hbij fMul hfs hfk hfπ
    hbound' (S.genW_mul A hA hgen)
  exact ⟨A, hA, ψ, hAlin, hgen, hsec.1, hfixV, hψ1, hψ2⟩
namespace burnsideI23x_SD

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] def torusLin (e e' : N) (b : F) : N →ₗ[F] N where
  toFun x := x + ((b - 1) * S.B x e') • e + ((b⁻¹ - 1) * S.B x e) • e'
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, mul_add, add_smul]
    abel
  map_smul' a x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_smul]
    rw [mul_left_comm (b - 1), mul_left_comm (b⁻¹ - 1)]

theorem torusLin_apply (e e' : N) (b : F) (x : N) :
    S.torusLin e e' b x = x + ((b - 1) * S.B x e') • e + ((b⁻¹ - 1) * S.B x e) • e' := rfl

theorem torusLin_e {e e' : N} (hee : S.B e e' = 1) (b : F) : S.torusLin e e' b e = b • e := by
  rw [torusLin_apply, S.alt, hee]
  module

theorem torusLin_e' {e e' : N} (hee : S.B e e' = 1) (b : F) :
    S.torusLin e e' b e' = b⁻¹ • e' := by
  rw [torusLin_apply, S.alt, S.B_comm e' e, hee]
  module

theorem torusLin_symp {e e' : N} (hee : S.B e e' = 1) {b : F} (hb : b ≠ 0) (x y : N) :
    S.B (S.torusLin e e' b x) (S.torusLin e e' b y) = S.B x y := by
  rw [torusLin_apply, torusLin_apply]
  have h1 : S.B e' e = 1 := by rw [S.B_comm]; exact hee
  have h6 := S.B_comm e y
  have h7 := S.B_comm e' y
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    mul_zero, add_zero, zero_add, hee, h1, h6, h7, mul_one]
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  linear_combination (S.B x e * S.B y e' + S.B x e' * S.B y e) * hbb

end Torus

end burnsideI23x_SD

namespace burnsideI23x_SD

section Torus2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem torusLin_comp_inv {e e' : N} (hee : S.B e e' = 1) {b : F} (hb : b ≠ 0) (x : N) :
    S.torusLin e e' b (S.torusLin e e' b⁻¹ x) = x := by
  have h1 : S.B e' e = 1 := by rw [S.B_comm]; exact hee
  rw [torusLin_apply S e e' b (S.torusLin e e' b⁻¹ x), torusLin_apply S e e' b⁻¹ x]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    hee, h1, mul_zero, add_zero, zero_add, mul_one, inv_inv]
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  have c1 : (b⁻¹ - 1) * S.B x e' + (b - 1) * (S.B x e' + (b⁻¹ - 1) * S.B x e') = 0 := by
    linear_combination (S.B x e') * hbb
  have c2 : (b - 1) * S.B x e + (b⁻¹ - 1) * (S.B x e + (b - 1) * S.B x e) = 0 := by
    linear_combination (S.B x e) * hbb
  have e1 : x + ((b⁻¹ - 1) * S.B x e') • e + ((b - 1) * S.B x e) • e' +
      ((b - 1) * (S.B x e' + (b⁻¹ - 1) * S.B x e')) • e +
      ((b⁻¹ - 1) * (S.B x e + (b - 1) * S.B x e)) • e' =
      x + (((b⁻¹ - 1) * S.B x e') + ((b - 1) * (S.B x e' + (b⁻¹ - 1) * S.B x e'))) • e +
      (((b - 1) * S.B x e) + ((b⁻¹ - 1) * (S.B x e + (b - 1) * S.B x e))) • e' := by
    module
  rw [e1, c1, c2]
  simp

@[expose] def torusEquiv {e e' : N} (hee : S.B e e' = 1) {b : F} (hb : b ≠ 0) : N ≃ₗ[F] N :=
  LinearEquiv.ofLinear (S.torusLin e e' b) (S.torusLin e e' b⁻¹)
    (LinearMap.ext fun x => S.torusLin_comp_inv hee hb x)
    (LinearMap.ext fun x => by
      have := S.torusLin_comp_inv hee (inv_ne_zero hb) x
      rwa [inv_inv] at this)

theorem torusEquiv_apply {e e' : N} (hee : S.B e e' = 1) {b : F} (hb : b ≠ 0) (x : N) :
    S.torusEquiv hee hb x = S.torusLin e e' b x := rfl

theorem torusEquiv_symp {e e' : N} (hee : S.B e e' = 1) {b : F} (hb : b ≠ 0) :
    S.Symp (S.torusEquiv hee hb) := fun x y => S.torusLin_symp hee hb x y

end Torus2

end burnsideI23x_SD
namespace burnsideI23x_SD

section Irred

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {Γ : Type} (lin : Γ → N →ₗ[F] N)

theorem exists_partner {e : N} (he : e ≠ 0) : ∃ e' : N, S.B e e' = 1 := by
  obtain ⟨x, hx⟩ := S.exists_B_eq_one he
  exact ⟨x, by rw [S.B_comm]; exact hx⟩

theorem irred_line (hsurj : ∀ M : N ≃ₗ[F] N, S.Symp M → ∃ γ, ∀ x, lin γ x = M x) {e : N}
    (he : e ≠ 0) {ℓ : AddSubgroup N} (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e)
    (C : AddSubgroup N) (hC : C ≠ ⊥) (hCℓ : C ≤ ℓ)
    (hCinv : ∀ γ, (∀ x, lin γ x ∈ ℓ ↔ x ∈ ℓ) → ∀ x ∈ C, lin γ x ∈ C) : ℓ ≤ C := by
  obtain ⟨⟨x₀, hx₀C⟩, hx₀'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
  have hx₀ : x₀ ≠ 0 := fun h => hx₀' (Subtype.ext h)
  obtain ⟨a₀, ha₀⟩ := (hℓ x₀).1 (hCℓ hx₀C)
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (by simpa using ha₀)
  obtain ⟨e', hee⟩ := S.exists_partner he
  intro y hy
  obtain ⟨t, rfl⟩ := (hℓ y).1 hy
  by_cases ht : t = 0
  · rw [ht, zero_smul]; exact C.zero_mem
  · set b : F := t / a₀ with hb
    have hb0 : b ≠ 0 := div_ne_zero ht ha₀0
    obtain ⟨γ, hγ⟩ := hsurj (S.torusEquiv hee hb0) (S.torusEquiv_symp hee hb0)
    have hstab : ∀ x, lin γ x ∈ ℓ ↔ x ∈ ℓ := by
      intro x
      rw [hγ, S.torusEquiv_apply]
      constructor
      · intro hx
        obtain ⟨c, hc⟩ := (hℓ _).1 hx
        have h2 := S.torusLin_comp_inv hee (inv_ne_zero hb0) x
        rw [inv_inv] at h2
        rw [← h2, hc, map_smul, S.torusLin_e hee]
        exact (hℓ _).2 ⟨c * b⁻¹, by rw [smul_smul]⟩
      · intro hx
        obtain ⟨c, hc⟩ := (hℓ _).1 hx
        rw [hc, map_smul, S.torusLin_e hee]
        exact (hℓ _).2 ⟨c * b, by rw [smul_smul]⟩
    have := hCinv γ hstab x₀ hx₀C
    rw [hγ, S.torusEquiv_apply, ha₀, map_smul, S.torusLin_e hee, smul_smul] at this
    convert this using 2
    rw [hb]
    field_simp

theorem irred_top (hsurj : ∀ M : N ≃ₗ[F] N, S.Symp M → ∃ γ, ∀ x, lin γ x = M x)
    {ℓ : AddSubgroup N} (hℓ : ∀ x, x ∈ ℓ)
    (C : AddSubgroup N) (hC : C ≠ ⊥) (hCinv : ∀ γ, (∀ x, lin γ x ∈ ℓ ↔ x ∈ ℓ) →
      ∀ x ∈ C, lin γ x ∈ C) : ℓ ≤ C := by
  obtain ⟨⟨x₀, hx₀C⟩, hx₀'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
  have hx₀ : x₀ ≠ 0 := fun h => hx₀' (Subtype.ext h)
  have hadj : ∀ y : N, S.B x₀ y ≠ 0 → y ∈ C := by
    intro y hy
    set b : F := S.B x₀ y with hb
    set e : N := b⁻¹ • y with he
    have hBe : S.B x₀ e = 1 := by
      rw [he, map_smul, smul_eq_mul, ← hb, inv_mul_cancel₀ hy]
    obtain ⟨γ, hγ⟩ := hsurj (S.tvEquiv e b) (S.tvEquiv_symp e b)
    have := hCinv γ (fun x => by simp only [hℓ]) x₀ hx₀C
    rw [hγ, S.tvEquiv_apply, hBe, mul_one, he, smul_smul, mul_inv_cancel₀ hy, one_smul] at this
    have h2 := C.sub_mem this hx₀C
    simpa using h2
  intro y _
  by_cases hy : S.B x₀ y = 0
  · obtain ⟨d, hd⟩ : ∃ d, S.B x₀ d ≠ 0 := by
      by_contra hcon
      exact hx₀ (S.nondeg x₀ (fun d => by_contra fun hd => hcon ⟨d, hd⟩))
    have h1 := hadj d hd
    have h2 := hadj (y + d) (by rw [map_add, hy, zero_add]; exact hd)
    have h3 := C.sub_mem h2 h1
    simpa using h3
  · exact hadj y hy

end Irred

end burnsideI23x_SD
@[expose] def burnsideI23x_B1 (F : Type) [Field F] : (Fin 2 → F) →ₗ[F] (Fin 2 → F) →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => x 0 * y 1 + x 1 * y 0)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem burnsideI23x_B1_apply (F : Type) [Field F] (x y : Fin 2 → F) :
    burnsideI23x_B1 F x y = x 0 * y 1 + x 1 * y 0 := rfl

@[expose] def burnsideI23x_sd1 (F : Type) [Field F] [CharP F 2] : burnsideI23x_SD F (Fin 2 → F) where
  B := burnsideI23x_B1 F
  Q0 x := x 0 * x 1
  Q0_add x y := by
    rw [burnsideI23x_B1_apply]
    simp only [Pi.add_apply]
    ring
  Q0_smul c x := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  alt x := by
    rw [burnsideI23x_B1_apply]
    have h : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination (x 0 * x 1) * h
  nondeg x hx := by
    funext i
    fin_cases i
    · have h := hx (Pi.single 1 1)
      rw [burnsideI23x_B1_apply] at h
      simpa using h
    · have h := hx (Pi.single 0 1)
      rw [burnsideI23x_B1_apply] at h
      simpa using h

theorem burnsideI23x_sd1_B (F : Type) [Field F] [CharP F 2] (x y : Fin 2 → F) :
    (burnsideI23x_sd1 F).B x y = x 0 * y 1 + x 1 * y 0 := rfl

theorem burnsideI23x_sd1_Q0 (F : Type) [Field F] [CharP F 2] (x : Fin 2 → F) :
    (burnsideI23x_sd1 F).Q0 x = x 0 * x 1 := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_hsymp1 (F : Type) [Field F] [CharP F 2] (γ : ↥(StatedSL 2 F))
    (x y : Fin 2 → F) :
    (burnsideI23x_sd1 F).B ((burnsideI23x_LM1 F).lin γ x) ((burnsideI23x_LM1 F).lin γ y) =
      (burnsideI23x_sd1 F).B x y := by
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective γ
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  show (burnsideI23x_sd1 F).B ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x)
    ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ y) = _
  rw [burnsideI23x_sd1_B, burnsideI23x_sd1_B]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (x 0 * y 1 + x 1 * y 0) * hdet +
    ((x 0 * y 1 + x 1 * y 0) * ((A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0) +
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 * x 0 * y 0 +
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 * x 1 * y 1) * h2

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_hfaith1 (F : Type) [Field F] (γ : ↥(StatedSL 2 F))
    (h : ∀ x, (burnsideI23x_LM1 F).lin γ x = x) : γ = 1 := by
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective γ
  have hA : A = 1 := by
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    have h2 : ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pi.single j 1 : Fin 2 → F)) i =
        (Pi.single j 1 : Fin 2 → F) i := this
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    rw [h2]
  rw [hA, map_one]

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_htv1 (F : Type) [Field F] [Finite F] [CharP F 2] (e : Fin 2 → F) (c : F) :
    ∃ γ : ↥(StatedSL 2 F), ∀ x, (burnsideI23x_LM1 F).lin γ x =
      (burnsideI23x_sd1 F).tvEquiv e c x := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hdet : (!![1 + c * e 0 * e 1, c * e 0 * e 0; c * e 1 * e 1, 1 + c * e 0 * e 1] :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (c * e 0 * e 1) * h2
  refine ⟨specialLinearGroupEquivStatedSL 2 F ⟨_, hdet⟩, fun x => ?_⟩
  show (!![1 + c * e 0 * e 1, c * e 0 * e 0; c * e 1 * e 1, 1 + c * e 0 * e 1] :
      Matrix (Fin 2) (Fin 2) F) *ᵥ x = _
  rw [burnsideI23x_SD.tvEquiv_apply, burnsideI23x_sd1_B]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
namespace burnsideI23x_SD

section LineSub

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem tvκ_diff_ne (e : N) {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    a * S.tvκ e 1 - S.tvκ e a ≠ 0 := by
  intro hcon
  have h' : a * S.tvκ e 1 = S.tvκ e a := sub_eq_zero.1 hcon
  have hsq : (a * S.tvκ e 1) ^ 2 = S.tvκ e a ^ 2 := by rw [h']
  rw [mul_pow, S.tvκ_sq, S.tvκ_sq] at hsq
  have h2 : a * (a - 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 h2 with h | h
  · exact ha0 h
  · exact ha1 (sub_eq_zero.1 h)

theorem line_sub (D : AddSubgroup (N × F)) (hD : ∀ (a : F) (y : N × F), y ∈ D → a • y ∈ D)
    {e : N} {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (h1 : (((1 : F) • e, S.tvκ e 1) : N × F) ∈ D) (h2 : ((a • e, S.tvκ e a) : N × F) ∈ D)
    (t z : F) : ((t • e, z) : N × F) ∈ D := by
  have hδ := S.tvκ_diff_ne e ha0 ha1
  have hK : ∀ d : F, ((0 : N), d) ∈ D := by
    intro d
    have h3 : ((a * S.tvκ e 1 - S.tvκ e a) • ((0 : N), (1 : F))) ∈ D := by
      have := D.sub_mem (hD a _ h1) h2
      convert this using 1
      refine Prod.ext ?_ ?_
      · show (a * S.tvκ e 1 - S.tvκ e a) • (0 : N) = (a • (1 : F) • e - a • e)
        rw [one_smul, sub_self, smul_zero]
      · show (a * S.tvκ e 1 - S.tvκ e a) * 1 = a * S.tvκ e 1 - S.tvκ e a
        ring
    have h4 := hD ((a * S.tvκ e 1 - S.tvκ e a)⁻¹ * d) _ h3
    convert h4 using 1
    refine Prod.ext ?_ ?_
    · show (0 : N) = _
      simp
    · show d = ((a * S.tvκ e 1 - S.tvκ e a)⁻¹ * d) * ((a * S.tvκ e 1 - S.tvκ e a) * 1)
      field_simp
  have h5 := D.add_mem (hD t _ h1) (hK (z - t * S.tvκ e 1))
  convert h5 using 1
  refine Prod.ext ?_ ?_
  · show t • e = t • (1 : F) • e + 0
    rw [one_smul, add_zero]
  · show z = t * S.tvκ e 1 + (z - t * S.tvκ e 1)
    ring

end LineSub

end burnsideI23x_SD
namespace burnsideI23x_SD

section UCg3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

theorem lift_eq_self_of_fix (γ : Γ) {x : N} (hx : A γ x = x) (z : F) :
    S.lift (hA γ) (x, z) = (x, z) := by
  refine Prod.ext hx ?_
  show z + S.lf (A γ) x = z
  unfold lf
  rw [hx, add_self_F, map_zero, add_zero]

theorem lift_eq_of_tv (γ : Γ) {e : N} {c : F} (h : ∀ x, A γ x = S.tvEquiv e c x) (w : N × F) :
    S.lift (hA γ) w = (w.1 + (c * S.B w.1 e) • e, w.2 + S.B w.1 e * S.tvκ e c) := by
  rw [lift_apply]
  have h1 : S.lf (A γ) w.1 = S.lf (S.tvEquiv e c) w.1 := by
    unfold lf
    rw [h]
  rw [h1, S.lf_tv, h, S.tvEquiv_apply]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem root_generation (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    {K : Subgroup U} (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    (hψK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0)
    {e₀ : N} (he₀ : e₀ ≠ 0) {ℓ : AddSubgroup N} (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀)
    {U1 : Subgroup U} (hU1 : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ)
    {a : F} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (htv : ∀ c : F, ∃ γ, ∀ x, A γ x = S.tvEquiv e₀ c x) :
    U1 = commV (i23TransvectionRoot L K U1) ∧
      commV (i23TransvectionRoot L K U1) ≤ fixV (i23TransvectionRoot L K U1) := by
  classical
  have hlift : ∀ (γ : Γ) (u : U), Multiplicative.toAdd (ψ ((π γ : MulAut U) u)) =
      S.lift (hA γ) (Multiplicative.toAdd (ψ u)) := fun γ u => by rw [hψ]; rfl
  have hcommvec : ∀ (γ : Γ) (u : U), Multiplicative.toAdd (ψ ((π γ : MulAut U) u * u⁻¹)) =
      S.lift (hA γ) (Multiplicative.toAdd (ψ u)) - Multiplicative.toAdd (ψ u) := by
    intro γ u
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hlift, sub_eq_add_neg]
  have hgenfix : ∀ r : MulAut U, r ∈ L → (∀ v ∈ U1, r v * v⁻¹ ∈ K) → ∀ u ∈ U1, r u = u := by
    intro r hrL hr u hu
    obtain ⟨γ, hγ⟩ := hπs ⟨r, hrL⟩
    have hγr : (π γ : MulAut U) = r := congrArg Subtype.val hγ
    have h1 := (hψK _).1 (hr u hu)
    rw [← hγr, hcommvec] at h1
    have h2 : A γ (Multiplicative.toAdd (ψ u)).1 = (Multiplicative.toAdd (ψ u)).1 := by
      have : (S.lift (hA γ) (Multiplicative.toAdd (ψ u)) - Multiplicative.toAdd (ψ u)).1 =
          A γ (Multiplicative.toAdd (ψ u)).1 - (Multiplicative.toAdd (ψ u)).1 := rfl
      rw [this] at h1
      exact sub_eq_zero.1 h1
    have h3 : S.lift (hA γ) (Multiplicative.toAdd (ψ u)) = Multiplicative.toAdd (ψ u) := by
      have := lift_eq_self_of_fix (S := S) (A := A) (hA := hA) γ h2
        (Multiplicative.toAdd (ψ u)).2
      simpa using this
    apply ψ.injective
    rw [← hγr, hψ]
    apply Multiplicative.toAdd.injective
    exact h3
  have hRfix : ∀ r ∈ i23TransvectionRoot L K U1, ∀ u ∈ U1, r u = u := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem r hr => exact hgenfix r hr.1 hr.2.2.1
    | one => intro u _; rfl
    | mul r s _ _ ihr ihs => intro u hu; rw [MulAut.mul_apply, ihs u hu, ihr u hu]
    | inv r _ ihr =>
      intro u hu
      apply r.injective
      rw [MulAut.apply_inv_self]
      exact (ihr u hu).symm
  have hcomm_le := burnsideI23x_commV_root_le L K U1
  refine ⟨le_antisymm ?_ hcomm_le, fun w hw => mem_fixV.2 fun r hr => hRfix r hr w (hcomm_le hw)⟩
  obtain ⟨γ₁, h1⟩ := htv 1
  obtain ⟨γ₂, h2⟩ := htv a
  have hmemgen : ∀ (c : F) (γ : Γ), c ≠ 0 → (∀ x, A γ x = S.tvEquiv e₀ c x) →
      (π γ : MulAut U) ∈ i23TransvectionRoot L K U1 := by
    intro c γ hc hγ
    refine Subgroup.subset_closure ⟨(π γ).2, ?_, ?_, ?_⟩
    · intro v
      rw [hU1, hcommvec, lift_eq_of_tv (S := S) (A := A) (hA := hA) γ hγ]
      apply (hℓ _).2
      exact ⟨c * S.B (Multiplicative.toAdd (ψ v)).1 e₀, by
        show (_ + _) - _ = _
        simp⟩
    · intro v hv
      rw [hψK, hcommvec, lift_eq_of_tv (S := S) (A := A) (hA := hA) γ hγ]
      obtain ⟨t, ht⟩ := (hℓ _).1 ((hU1 v).1 hv)
      show ((Multiplicative.toAdd (ψ v)).1 + (c * S.B (Multiplicative.toAdd (ψ v)).1 e₀) • e₀ -
        (Multiplicative.toAdd (ψ v)).1) = 0
      rw [ht, map_smul, LinearMap.smul_apply, S.alt]
      simp
    · obtain ⟨x, hx⟩ := S.exists_B_eq_one he₀
      refine ⟨ψ.symm (Multiplicative.ofAdd (x, 0)), ?_⟩
      have hv : Multiplicative.toAdd (ψ (ψ.symm (Multiplicative.ofAdd ((x, (0 : F)))))) =
          (x, 0) := by simp
      rw [hψK, hcommvec, hv, lift_eq_of_tv (S := S) (A := A) (hA := hA) γ hγ]
      intro hcon
      simp only [Prod.fst_sub, hx, mul_one, add_sub_cancel_left] at hcon
      exact he₀ ((smul_eq_zero.1 hcon).resolve_left hc)
  set R := i23TransvectionRoot L K U1 with hR
  let D : AddSubgroup (N × F) :=
    { carrier := {w | ψ.symm (Multiplicative.ofAdd w) ∈ commV R}
      zero_mem' := by
        show ψ.symm (Multiplicative.ofAdd 0) ∈ commV R
        rw [ofAdd_zero, map_one]; exact Subgroup.one_mem _
      add_mem' := fun {x y} hx hy => by
        show ψ.symm (Multiplicative.ofAdd (x + y)) ∈ commV R
        rw [ofAdd_add, map_mul]; exact Subgroup.mul_mem _ hx hy
      neg_mem' := fun {x} hx => by
        show ψ.symm (Multiplicative.ofAdd (-x)) ∈ commV R
        rw [ofAdd_neg, map_inv]; exact Subgroup.inv_mem _ hx }
  have hD : ∀ (b : F) (y : N × F), y ∈ D → b • y ∈ D := by
    intro b y hy
    have hy' : ψ.symm (Multiplicative.ofAdd y) ∈ commV R := hy
    have key : ∀ u ∈ commV R,
        ψ.symm (Multiplicative.ofAdd (b • Multiplicative.toAdd (ψ u))) ∈ commV R := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨r, hr, v, rfl⟩ := hx
        obtain ⟨γ, hγ⟩ := hπs ⟨r, burnsideI23x_root_le L K U1 hr⟩
        have hγr : (π γ : MulAut U) = r := congrArg Subtype.val hγ
        subst hγr
        apply Subgroup.subset_closure
        refine ⟨(π γ : MulAut U), hr, ψ.symm (Multiplicative.ofAdd (b • Multiplicative.toAdd (ψ v))),
          ?_⟩
        apply ψ.injective
        apply Multiplicative.toAdd.injective
        rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, hcommvec, hcommvec, MulEquiv.apply_symm_apply,
          toAdd_ofAdd, map_smul, smul_sub]
      | one =>
        rw [map_one, toAdd_one, smul_zero, ofAdd_zero, map_one]
        exact Subgroup.one_mem _
      | mul x y _ _ hx hy =>
        rw [map_mul, toAdd_mul, smul_add, ofAdd_add, map_mul]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        rw [map_inv, toAdd_inv, smul_neg, ofAdd_neg, map_inv]
        exact Subgroup.inv_mem _ hx
    have h5 := key _ hy'
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h5
    exact h5
  have hvec : ∀ (c : F) (γ : Γ), c ≠ 0 → (∀ x, A γ x = S.tvEquiv e₀ c x) →
      (((c • e₀, S.tvκ e₀ c)) : N × F) ∈ D := by
    intro c γ hc hγ
    obtain ⟨x, hx⟩ := S.exists_B_eq_one he₀
    show ψ.symm (Multiplicative.ofAdd _) ∈ commV R
    have hmem : (π γ : MulAut U) (ψ.symm (Multiplicative.ofAdd (x, (0 : F)))) *
        (ψ.symm (Multiplicative.ofAdd (x, (0 : F))))⁻¹ ∈ commV R :=
      Subgroup.subset_closure ⟨π γ, hmemgen c γ hc hγ, _, rfl⟩
    convert hmem using 1
    apply ψ.injective
    apply Multiplicative.toAdd.injective
    rw [hcommvec, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      toAdd_ofAdd, lift_eq_of_tv (S := S) (A := A) (hA := hA) γ hγ]
    refine Prod.ext ?_ ?_
    · simp [hx]
    · simp [hx]
  have hline := S.line_sub D hD ha0 ha1 (hvec 1 γ₁ one_ne_zero h1) (hvec a γ₂ ha0 h2)
  intro u hu
  obtain ⟨t, ht⟩ := (hℓ _).1 ((hU1 u).1 hu)
  have h3 := hline t (Multiplicative.toAdd (ψ u)).2
  have hw : ((t • e₀, (Multiplicative.toAdd (ψ u)).2) : N × F) = Multiplicative.toAdd (ψ u) :=
    Prod.ext ht.symm rfl
  rw [hw] at h3
  have h' : ψ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (ψ u))) ∈ commV R := h3
  simpa using h'

end UCg3

end burnsideI23x_SD
theorem burnsideI23x_exists_ne_zero_one {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  by_contra hcon
  have hall : ∀ a : F, a = 0 ∨ a = 1 := fun a => by
    by_cases h0 : a = 0
    · exact Or.inl h0
    · by_cases h1 : a = 1
      · exact Or.inr h1
      · exact absurd ⟨a, h0, h1⟩ hcon
  have h2 : Nat.card F ≤ 2 := by
    classical
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card F ≤ Fintype.card Bool :=
          Fintype.card_le_of_injective (fun a => decide (a = 1)) (fun a b h => by
            rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;> simp_all)
      _ = 2 := rfl
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem burnsideI23x_line_of_card {F : Type} [Field F] [Finite F] {M : Type} [AddCommGroup M]
    [Module F M] [Finite M] (ℓ : AddSubgroup M) (hF : ∀ (a : F) (x : M), x ∈ ℓ → a • x ∈ ℓ)
    (hcard : Nat.card ℓ = Nat.card F) :
    ∃ e₀ : M, e₀ ≠ 0 ∧ ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀ := by
  have hlt : 1 < Nat.card ℓ := by
    rw [hcard]
    exact Finite.one_lt_card
  haveI : Nontrivial ℓ := Finite.one_lt_card_iff_nontrivial.1 hlt
  obtain ⟨⟨e₀, he₀⟩, hne⟩ := exists_ne (0 : ℓ)
  have hne' : e₀ ≠ 0 := fun h => hne (Subtype.ext h)
  refine ⟨e₀, hne', fun x => ⟨fun hx => ?_, fun ⟨a, ha⟩ => ha ▸ hF a e₀ he₀⟩⟩
  have hle : (Submodule.span F {e₀}).toAddSubgroup ≤ ℓ := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact hF a e₀ he₀
  have hspan : Nat.card (Submodule.span F {e₀}) = Nat.card F :=
    (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton F M e₀ hne').toEquiv).symm
  have heq := AddSubgroup.eq_of_le_of_card_ge hle (by
    show Nat.card ℓ ≤ Nat.card (Submodule.span F {e₀})
    rw [hcard, hspan])
  rw [← heq] at hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx
  exact ⟨a, ha.symm⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_hsurj1 (F : Type) [Field F] [Finite F] [CharP F 2]
    (M : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (hM : (burnsideI23x_sd1 F).Symp M) :
    ∃ γ : ↥(StatedSL 2 F), ∀ x, (burnsideI23x_LM1 F).lin γ x = M x := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set Mat := LinearMap.toMatrix' (M : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) with hMat
  have hMx : ∀ x, M x = Mat *ᵥ x := fun x => by
    have := congrArg (fun f => f x)
      (Matrix.toLin'_toMatrix' (M : (Fin 2 → F) →ₗ[F] (Fin 2 → F)))
    exact this.symm.trans (Matrix.toLin'_apply _ _)
  have hB := hM (Pi.single 0 1) (Pi.single 1 1)
  rw [burnsideI23x_sd1_B, burnsideI23x_sd1_B, hMx, hMx] at hB
  have hdet : Mat.det = 1 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] at hB
    simp at hB
    linear_combination hB - (Mat 0 1 * Mat 1 0) * h2
  refine ⟨specialLinearGroupEquivStatedSL 2 F ⟨Mat, hdet⟩, fun x => ?_⟩
  rw [hMx]
  rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_hbound1 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ n) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut V)) (W0 : Subgroup V)
        (π : (i23NaturalModel 1 F).Gam →* ↥L),
        (i23NaturalModel 1 F).RealizesVia L ⊤ W0 π → W0 = fixV L → commV L = ⊤ →
        Nat.card W0 ≤ Nat.card F := by
  intro V _ _ hV L W0 π hreal hW0 hcomm
  subst hW0
  have hcommOf : XMod.commOf ↥L (⊤ : Subgroup V) = ⊤ := by
    rw [CFSG.Quasithin.MS93.xmodCommOf_top_eq]
    exact hcomm
  have hreal' : (FFModel.nat (StatedSL 2 F)).Realizes L ⊤ (fixV L ⊓ ⊤) := by
    rw [inf_top_eq]
    exact ⟨π, hreal⟩
  have := CFSG.Quasithin.B513N.card_fixV_le_of_sl2 hV L ⊤ (fun x _ v _ => Subgroup.mem_top _)
    hcommOf hn hF hreal'
  rw [inf_top_eq, ← hF] at this
  exact this

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_marked_ell {m n i : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM)
    {V : Type} [CommGroup V] [Finite V] {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β) {U : Subgroup V}
    (hM : IsI23MarkedSubspace m n i F T W0 U β) :
    (∀ u, u ∈ U ↔ Multiplicative.toAdd (LM.e (β u)) ∈ (burnsideI23x_isCoord LM h).img U) ∧
    (∀ (a : F) (x : M), x ∈ (burnsideI23x_isCoord LM h).img U →
      a • x ∈ (burnsideI23x_isCoord LM h).img U) ∧
    Nat.card ((burnsideI23x_isCoord LM h).img U) = (2 ^ n) ^ i := by
  obtain ⟨hWU, hT, hcard, hscal⟩ := hM
  refine ⟨fun u => (burnsideI23x_isCoord LM h).mem_iff hWU u,
    fun a x hx => (burnsideI23x_native_iff_img hS h).1 hscal a x hx, ?_⟩
  rw [(burnsideI23x_isCoord LM h).card_img]
  exact (burnsideI23x_card_iff_relIndex hWU _ _).1 hcard
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_UCg_one {n : ℕ} (hn : 2 ≤ n) : burnsideI23x_UCg 1 n := by
  intro F _ _ hF U _ _ hU G L T K hLG hnorm hGT hT hGK huniv marking β hsec U1 U2 h1 h2
  haveI : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have hS := burnsideI23x_scalarAgree1 F
  obtain ⟨a, ha0, ha1⟩ := burnsideI23x_exists_ne_zero_one hF hn
  have htv' : ∀ (e : Fin 2 → F) (c : F), e ≠ 0 → ∃ γ, ∀ x,
      (burnsideI23x_LM1 F).lin γ x = (burnsideI23x_sd1 F).tvEquiv e c x :=
    fun e c _ => burnsideI23x_htv1 F e c
  have hgenM := burnsideI23x_SD.genW'_of_tv (burnsideI23x_sd1 F) (burnsideI23x_LM1 F).lin htv'
    ha0 ha1
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM1 F) (burnsideI23x_sd1 F) (burnsideI23x_hsymp1 F) (burnsideI23x_hfaith1 F)
    hgenM (burnsideI23x_hbound1 hn hF) hU huniv hsec
  have hEndLin := burnsideI23x_SD.hEnd_of_tv (burnsideI23x_sd1 F) (burnsideI23x_LM1 F).lin htv'
  have hEnd : ∀ φ : (Fin 2 → F) →+ (Fin 2 → F), (∀ γ x, φ (A γ x) = A γ (φ x)) →
      ∃ c : F, ∀ x, φ x = c • x := fun φ hφ =>
    hEndLin φ (fun γ x => by simpa only [hAlin] using hφ γ x)
  have hsurj : ∀ M : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F), (burnsideI23x_sd1 F).Symp M →
      ∃ γ, ∀ x, A γ x = M x := fun M hM => by
    obtain ⟨γ, hγ⟩ := burnsideI23x_hsurj1 F M hM
    exact ⟨γ, fun x => (hAlin γ x).trans (hγ x)⟩
  have hf := burnsideI23x_isCoord (burnsideI23x_LM1 F) hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  obtain ⟨hU2i, hU2F, hU2c⟩ := burnsideI23x_marked_ell hS hsec h2
  have hU1' : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hU2' : ∀ u, u ∈ U2 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U2 := fun u => by
    rw [hψfst]; exact hU2i u
  have hcard1 : Nat.card (hf.img U1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img U1) hU1F hcard1
  have hℓ₂ : ∀ x, x ∈ hf.img U2 := by
    have hc : Nat.card (hf.img U2) = Nat.card (Fin 2 → F) := by
      rw [hU2c, Nat.card_fun, Nat.card_fin, hF]
    have := AddSubgroup.eq_top_of_card_eq (hf.img U2) hc
    intro x
    rw [this]
    exact AddSubgroup.mem_top x
  have hirr1 : ∀ C : AddSubgroup (Fin 2 → F), C ≠ ⊥ → C ≤ hf.img U1 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U1 ↔ x ∈ hf.img U1) → ∀ x ∈ C, A γ x ∈ C) → hf.img U1 ≤ C :=
    fun C hC hCℓ hCinv => (burnsideI23x_sd1 F).irred_line (burnsideI23x_LM1 F).lin
      (burnsideI23x_hsurj1 F) he₀ hℓ₁ C hC hCℓ (fun γ hγ x hx => by
        have := hCinv γ (fun y => by simpa only [hAlin] using hγ y) x hx
        simpa only [hAlin] using this)
  have hirr2 : ∀ C : AddSubgroup (Fin 2 → F), C ≠ ⊥ → C ≤ hf.img U2 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U2 ↔ x ∈ hf.img U2) → ∀ x ∈ C, A γ x ∈ C) → hf.img U2 ≤ C :=
    fun C hC hCℓ hCinv => (burnsideI23x_sd1 F).irred_top (burnsideI23x_LM1 F).lin
      (burnsideI23x_hsurj1 F) hℓ₂ C hC (fun γ hγ x hx => by
        have := hCinv γ (fun y => by simpa only [hAlin] using hγ y) x hx
        simpa only [hAlin] using this)
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have he₀ℓ : e₀ ∈ hf.img U1 := (hℓ₁ e₀).2 ⟨1, (one_smul F e₀).symm⟩
  obtain ⟨e₂, he₂⟩ := exists_ne (0 : Fin 2 → F)
  have hψK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0 := fun u => by
    rw [hψfst]
    exact (hf.ker u).symm
  have htvA : ∀ c : F, ∃ γ, ∀ x, A γ x = (burnsideI23x_sd1 F).tvEquiv e₀ c x := fun c => by
    obtain ⟨γ, hγ⟩ := burnsideI23x_htv1 F e₀ c
    exact ⟨γ, fun x => (hAlin γ x).trans (hγ x)⟩
  refine ⟨?_, ⟨?_, ?_⟩, fun hn' _ => ?_⟩
  · exact burnsideI23x_SD.exists_T_fixed ψ marking hπs hψact hEnd hgenW hTG hnorm hT2 he₀ hℓ₁
      hU1' (fun t ht u hu => h1.2.1 t ht u hu)
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU1F hU1' he₀ℓ he₀
      hirr1
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU2F hU2'
      (hℓ₂ e₂) he₂ hirr2
  · exact burnsideI23x_SD.root_generation ψ marking hπs hψact hψK he₀ hℓ₁ hU1' ha0 ha1 htvA
namespace burnsideI23x_SD

section UCo

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem polar_Qw (w w' : N × F) : polarOf S.Qw w w' = S.B w.1 w'.1 := by
  unfold polarOf
  rw [S.Qw_add]
  show S.Qw w + S.Qw w' + S.B w.1 w'.1 - S.Qw w - S.Qw w' = S.B w.1 w'.1
  ring

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem orth_radical (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    {K : Subgroup U} (hψK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0)
    (hfixV : fixV L = K) :
    (∀ v : U, v ∈ fixV L ↔ ∀ w : N × F, polarOf S.Qw (Multiplicative.toAdd (ψ v)) w = 0) ∧
      Nat.card ↥(fixV L) = Nat.card F := by
  subst hfixV
  refine ⟨fun v => ?_, ?_⟩
  · rw [hψK]
    simp only [polar_Qw]
    constructor
    · intro h w
      rw [h, map_zero, LinearMap.zero_apply]
    · intro h
      exact S.nondeg _ (fun y => h (y, 0))
  · have hbij : Function.Bijective (fun v : ↥(fixV L) => (Multiplicative.toAdd (ψ v.1)).2) := by
      constructor
      · intro v v' h
        apply Subtype.ext
        apply ψ.injective
        apply Multiplicative.toAdd.injective
        have h1 := (hψK v.1).1 v.2
        have h2 := (hψK v'.1).1 v'.2
        exact Prod.ext (h1.trans h2.symm) h
      · intro z
        refine ⟨⟨ψ.symm (Multiplicative.ofAdd (0, z)), (hψK _).2 (by simp)⟩, ?_⟩
        simp
    exact Nat.card_congr (Equiv.ofBijective _ hbij)

end UCo

end burnsideI23x_SD

namespace burnsideI23x_SD

section UCoPoint

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem orth_point (ψ : U ≃* Multiplicative (N × F)) {K : Subgroup U}
    (hψK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0) {e₀ : N} (he₀ : e₀ ≠ 0)
    {ℓ : AddSubgroup N} (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀) {U1 : Subgroup U}
    (hU1 : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ) :
    ∃! P : Subgroup U, IsFSubspaceVia (F := F) ψ P 1 ∧
      (∀ v ∈ P, S.Qw (Multiplicative.toAdd (ψ v)) = 0) ∧ U1 = P ⊔ K ∧ P ⊓ K = ⊥ := by
  classical
  set z₀ : F := burnsideI23x_sqrt F (S.Q0 e₀) with hz₀
  set s₀ : N × F := (e₀, z₀) with hs₀
  have hz₀sq : z₀ ^ 2 = S.Q0 e₀ := burnsideI23x_sqrt_sq _
  have hs₀ne : s₀ ≠ 0 := fun h => he₀ (congrArg Prod.fst h)
  let Sp : Submodule F (N × F) := Submodule.span F {s₀}
  have hSp : ∀ w, w ∈ Sp ↔ ∃ a : F, w = a • s₀ := fun w => by
    rw [Submodule.mem_span_singleton]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  let P : Subgroup U :=
    { carrier := {u | Multiplicative.toAdd (ψ u) ∈ Sp}
      one_mem' := by
        show Multiplicative.toAdd (ψ 1) ∈ Sp
        rw [map_one, toAdd_one]; exact Sp.zero_mem
      mul_mem' := fun {u v} hu hv => by
        show Multiplicative.toAdd (ψ (u * v)) ∈ Sp
        rw [map_mul, toAdd_mul]; exact Sp.add_mem hu hv
      inv_mem' := fun {u} hu => by
        show Multiplicative.toAdd (ψ u⁻¹) ∈ Sp
        rw [map_inv, toAdd_inv]; exact Sp.neg_mem hu }
  have hmemP : ∀ u, u ∈ P ↔ Multiplicative.toAdd (ψ u) ∈ Sp := fun u => Iff.rfl
  have hQs₀ : S.Qw s₀ = 0 := by
    show S.Q0 e₀ + z₀ ^ 2 = 0
    rw [hz₀sq]; exact add_self_F _
  have hPline : IsFSubspaceVia (F := F) ψ P 1 :=
    ⟨Sp, finrank_span_singleton hs₀ne, fun v => Iff.rfl⟩
  have hPsing : ∀ v ∈ P, S.Qw (Multiplicative.toAdd (ψ v)) = 0 := by
    intro v hv
    obtain ⟨a, ha⟩ := (hSp _).1 hv
    rw [ha, Qw_smul, hQs₀, mul_zero]
  have hPsup : U1 = P ⊔ K := by
    apply le_antisymm
    · intro u hu
      obtain ⟨t, ht⟩ := (hℓ _).1 ((hU1 u).1 hu)
      have hw : Multiplicative.toAdd (ψ u) = t • s₀ + (0, (Multiplicative.toAdd (ψ u)).2 - t * z₀) := by
        refine Prod.ext ?_ ?_
        · show (Multiplicative.toAdd (ψ u)).1 = t • e₀ + 0
          rw [ht, add_zero]
        · show (Multiplicative.toAdd (ψ u)).2 = t * z₀ + ((Multiplicative.toAdd (ψ u)).2 - t * z₀)
          ring
      have h1 : ψ.symm (Multiplicative.ofAdd (t • s₀)) ∈ P := by
        rw [hmemP, MulEquiv.apply_symm_apply, toAdd_ofAdd]
        exact (hSp _).2 ⟨t, rfl⟩
      have h2 : ψ.symm (Multiplicative.ofAdd ((0 : N), (Multiplicative.toAdd (ψ u)).2 - t * z₀)) ∈ K := by
        rw [hψK, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      have h3 := Subgroup.mul_mem_sup h1 h2
      convert h3 using 1
      apply ψ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← ofAdd_add, ← hw,
        ofAdd_toAdd]
    · refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · obtain ⟨a, ha⟩ := (hSp _).1 ((hmemP u).1 hu)
        rw [hU1, ha]
        exact (hℓ _).2 ⟨a, rfl⟩
      · rw [hU1, (hψK u).1 hu]
        exact (hℓ _).2 ⟨0, by simp⟩
  have hPinf : P ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro u ⟨hu, huK⟩
    obtain ⟨a, ha⟩ := (hSp _).1 ((hmemP u).1 hu)
    have h0 := (hψK u).1 huK
    rw [ha] at h0
    have h5 : a • e₀ = 0 := h0
    have ha0 : a = 0 := ((smul_eq_zero.1 h5).resolve_right he₀)
    apply Subgroup.mem_bot.2
    apply ψ.injective
    apply Multiplicative.toAdd.injective
    rw [ha, ha0, zero_smul, map_one, toAdd_one]
  refine ⟨P, ⟨hPline, hPsing, hPsup, hPinf⟩, fun P' ⟨hP'line, hP'sing, hP'sup, hP'inf⟩ => ?_⟩
  obtain ⟨S', hS'rank, hS'⟩ := hP'line
  obtain ⟨⟨w', hw'S⟩, hw'ne, hw'gen⟩ := finrank_eq_one_iff'.1 hS'rank
  have hw'ne' : w' ≠ 0 := fun h => hw'ne (Subtype.ext h)
  have hP'U1 : ∀ u ∈ P', u ∈ U1 := fun u hu => by
    rw [hP'sup]; exact Subgroup.mem_sup_left hu
  have hu' : ψ.symm (Multiplicative.ofAdd w') ∈ P' := by
    rw [hS', MulEquiv.apply_symm_apply, toAdd_ofAdd]; exact hw'S
  obtain ⟨t, ht⟩ := (hℓ _).1 ((hU1 _).1 (hP'U1 _ hu'))
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hK' : ψ.symm (Multiplicative.ofAdd w') ∈ K := by
      rw [hψK, MulEquiv.apply_symm_apply, toAdd_ofAdd, ht, zero_smul]
    have hmem : ψ.symm (Multiplicative.ofAdd w') ∈ P' ⊓ K := ⟨hu', hK'⟩
    rw [hP'inf] at hmem
    have h6 : ψ.symm (Multiplicative.ofAdd w') = 1 := Subgroup.mem_bot.1 hmem
    apply hw'ne'
    have h7 := congrArg ψ h6
    rw [MulEquiv.apply_symm_apply, map_one] at h7
    exact Multiplicative.ofAdd.injective h7
  have hw's₀ : w' = t • s₀ := by
    have hq : S.Qw w' = 0 := by
      have := hP'sing _ hu'
      rwa [MulEquiv.apply_symm_apply, toAdd_ofAdd] at this
    refine Prod.ext (by rw [ht]; rfl) ?_
    have e1 : S.Q0 w'.1 + w'.2 ^ 2 = 0 := hq
    rw [ht, S.Q0_smul] at e1
    have e2 := add_self_F (t ^ 2 * S.Q0 e₀)
    have hsq : w'.2 ^ 2 = (t * z₀) ^ 2 := by
      rw [mul_pow, hz₀sq]
      linear_combination e1 - e2
    exact burnsideI23x_sq_injective hsq
  apply Subgroup.ext
  intro v
  rw [hS' v, hmemP]
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := hw'gen ⟨_, hv⟩
    have hc' : c • w' = Multiplicative.toAdd (ψ v) := congrArg Subtype.val hc
    rw [← hc', hw's₀, smul_smul]
    exact (hSp _).2 ⟨_, rfl⟩
  · intro hv
    obtain ⟨a, ha⟩ := (hSp _).1 hv
    have : Multiplicative.toAdd (ψ v) = (a * t⁻¹) • w' := by
      rw [ha, hw's₀, smul_smul, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
    rw [this]
    exact S'.smul_mem _ hw'S

end UCoPoint

end burnsideI23x_SD

namespace burnsideI23x_SD

section UCoFix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem fixes_line_of_two_elt (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    {T : Subgroup (MulAut U)} (hT2 : IsPGroup 2 T) {γ : Γ} (hγT : (π γ : MulAut U) ∈ T)
    {e₀ : N} (he₀ : e₀ ≠ 0) (hlam : ∃ lam : F, A γ e₀ = lam • e₀) : A γ e₀ = e₀ := by
  obtain ⟨lam, hlam⟩ := hlam
  obtain ⟨k, hk⟩ := hT2 ⟨_, hγT⟩
  have hk' : ((π γ : MulAut U)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hpow : ∀ j : ℕ, A (γ ^ j) e₀ = lam ^ j • e₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, hlam, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have h1 : A (γ ^ 2 ^ k) e₀ = e₀ := by
    have h2 : ((π (γ ^ 2 ^ k) : ↥L) : MulAut U) = 1 := by
      rw [map_pow]
      exact hk'
    have h3 := hψ (γ ^ 2 ^ k) (ψ.symm (Multiplicative.ofAdd (e₀, 0)))
    rw [h2, MulAut.one_apply, MulEquiv.apply_symm_apply] at h3
    have h4 := congrArg (fun w => (Multiplicative.toAdd w).1) h3
    exact h4.symm
  rw [hpow] at h1
  have h5 : (lam ^ 2 ^ k - 1) • e₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  have h6 : lam ^ 2 ^ k = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h5).resolve_right he₀)
  have h7 : lam = 1 := burnsideI23x_pow_two_pow_eq_one h6
  rw [hlam, h7, one_smul]

end UCoFix

end burnsideI23x_SD

namespace burnsideI23x_SD

section UCoFix2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem line_le_fixV_P (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    {T : Subgroup (MulAut U)} (hT2 : IsPGroup 2 T) {e₀ : N} (he₀ : e₀ ≠ 0) {ℓ : AddSubgroup N}
    (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀) {U1 : Subgroup U}
    (hU1 : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ)
    (hT1 : ∀ t ∈ T, ∀ u ∈ U1, t u ∈ U1) : U1 ≤ fixV (T ⊓ L) := by
  intro u hu
  rw [mem_fixV]
  intro p hp
  obtain ⟨γ, hγ⟩ := hπs ⟨p, hp.2⟩
  have hγp : (π γ : MulAut U) = p := congrArg Subtype.val hγ
  have hmem : A γ e₀ ∈ ℓ := by
    have hu₁ : ψ.symm (Multiplicative.ofAdd (e₀, (0 : F))) ∈ U1 := by
      rw [hU1, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact (hℓ _).2 ⟨1, (one_smul F e₀).symm⟩
    have h2 := hT1 p hp.1 _ hu₁
    rw [hU1, ← hγp, hψ, MulEquiv.apply_symm_apply] at h2
    exact h2
  obtain ⟨lam, hlam⟩ := (hℓ _).1 hmem
  have hfix := fixes_line_of_two_elt ψ π hψ hT2 (by rw [hγp]; exact hp.1) he₀ ⟨lam, hlam⟩
  obtain ⟨t, ht⟩ := (hℓ _).1 ((hU1 u).1 hu)
  have hAx : A γ (Multiplicative.toAdd (ψ u)).1 = (Multiplicative.toAdd (ψ u)).1 := by
    rw [ht, map_smul, hfix]
  have h3 : S.lift (hA γ) (Multiplicative.toAdd (ψ u)) = Multiplicative.toAdd (ψ u) := by
    have := lift_eq_self_of_fix (S := S) (A := A) (hA := hA) γ hAx (Multiplicative.toAdd (ψ u)).2
    simpa using this
  apply ψ.injective
  rw [← hγp, hψ]
  apply Multiplicative.toAdd.injective
  exact h3

end UCoFix2

end burnsideI23x_SD

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_fixV_P_le {m n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {M : Type} [AddCommGroup M] [Module F M] [Finite M]
    {LM : LinModel (i23NaturalModel m F) F M}
    (hcomm : ∀ T : M →+ M, (∀ (γ : (i23NaturalModel m F).Gam) (x : M),
      T (LM.lin γ x) = LM.lin γ (T x)) → ∃ c : F, ∀ x, T x = c • x)
    (hF : Nat.card F = 2 ^ n) {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {L T : Subgroup (MulAut U)} {K : Subgroup U}
    {marking : (i23NaturalModel m F).Gam →* ↥L}
    {β : U →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (hsec : I23SectionMap (i23NaturalModel m F) L K marking β) (hKfix : K ≤ fixV L)
    {U1 : Subgroup U} (hKU1 : K ≤ U1)
    (hflag1 : ∀ U', IsFlagW L (T ⊓ L) K (2 ^ n) 1 U' → U' = U1) :
    fixV (T ⊓ L) ≤ U1 := by
  classical
  intro u hu
  by_contra hnu
  have hf := burnsideI23x_isCoord LM hsec
  set w₁ : M := Multiplicative.toAdd (LM.e (β u)) with hw₁
  have hw₁ne : w₁ ≠ 0 := by
    intro h0
    exact hnu (hKU1 ((hf.ker u).1 h0))
  let ℓ' : AddSubgroup M := (Submodule.span F {w₁}).toAddSubgroup
  have hℓ' : ∀ x, x ∈ ℓ' ↔ ∃ a : F, x = a • w₁ := fun x => by
    show x ∈ Submodule.span F {w₁} ↔ _
    rw [Submodule.mem_span_singleton]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  have hflag : IsFlagW L (T ⊓ L) K (2 ^ n) 1 (hf.pre ℓ') := by
    refine ⟨hf.le_pre ℓ', ?_, ?_, ?_⟩
    · rw [hf.endStableW_iff hU hcomm (hf.le_pre ℓ'), hf.img_pre]
      intro c x hx
      exact Submodule.smul_mem _ c hx
    · rw [← hf.card_img, hf.img_pre, pow_one, ← hF]
      exact burnsideI23x_card_span_single w₁ hw₁ne
    · intro x hx
      obtain ⟨γ, hγ⟩ := hf.onto ⟨x, hx.2⟩
      have hγx : (marking γ : MulAut U) = x := congrArg Subtype.val hγ
      rw [← hγx]
      rw [hf.mem_stabW_iff (hf.le_pre ℓ') γ, hf.img_pre]
      have hfixw : LM.lin γ w₁ = w₁ := by
        have h1 := hf.act γ u
        rw [hγx, mem_fixV.1 hu x hx] at h1
        exact h1.symm
      intro y
      constructor
      · intro hy
        obtain ⟨a, rfl⟩ := (hℓ' y).1 hy
        rw [map_smul, hfixw]
        exact (hℓ' _).2 ⟨a, rfl⟩
      · intro hy
        obtain ⟨a, ha⟩ := (hℓ' _).1 hy
        have h2 : LM.lin γ y = LM.lin γ (a • w₁) := by rw [ha, map_smul, hfixw]
        have h3 : y = a • w₁ :=
          (burnsideI23x_linHom LM hf γ).injective h2
        rw [h3]
        exact (hℓ' _).2 ⟨a, rfl⟩
  have h5 := hflag1 _ hflag
  apply hnu
  rw [← h5]
  exact (hℓ' _).2 ⟨1, (one_smul F w₁).symm⟩
namespace burnsideI23x_SD

section RootClassify

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

theorem tvEquiv_zero (e : N) (x : N) : S.tvEquiv e 0 x = x := by
  rw [tvEquiv_apply]; simp

theorem tvEquiv_add (e : N) (c c' : F) (x : N) :
    S.tvEquiv e (c + c') x = S.tvEquiv e c (S.tvEquiv e c' x) := by
  rw [tvEquiv_apply, tvEquiv_apply, tvEquiv_apply]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    mul_zero, add_zero]
  rw [add_assoc, ← add_smul]
  congr 2
  ring

theorem tv_char {e₀ : N} (he₀ : e₀ ≠ 0) {M : N ≃ₗ[F] N} (hM : S.Symp M)
    (hMx : ∀ x, ∃ a : F, M x = x + a • e₀) : ∃ c : F, ∀ x, M x = S.tvEquiv e₀ c x := by
  obtain ⟨x₁, hx₁⟩ := S.exists_B_eq_one he₀
  obtain ⟨c, hc⟩ := hMx x₁
  refine ⟨c, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hMx x
  have h1 := hM x x₁
  rw [ha, hc] at h1
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    mul_zero, add_zero] at h1
  have h2 : S.B e₀ x₁ = 1 := by rw [S.B_comm]; exact hx₁
  rw [h2] at h1
  have h3 : a = c * S.B x e₀ := by
    have h2' := two_eq_zero_F (F := F)
    linear_combination h1 - (c * S.B x e₀) * h2'
  rw [ha, tvEquiv_apply, h3]

end RootClassify

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClassify2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem root_classify (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    {K : Subgroup U} (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    {e₀ : N} (he₀ : e₀ ≠ 0) {ℓ : AddSubgroup N} (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀)
    {U1 : Subgroup U} (hU1 : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ) :
    ∀ r ∈ i23TransvectionRoot L K U1, ∃ (γ : Γ) (c : F), (π γ : MulAut U) = r ∧
      ∀ x, A γ x = S.tvEquiv e₀ c x := by
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨γ, hγ⟩ := hπs ⟨r, hr.1⟩
    have hγr : (π γ : MulAut U) = r := congrArg Subtype.val hγ
    have hMx : ∀ x, ∃ a : F, A γ x = x + a • e₀ := by
      intro x
      have h1 := hr.2.1 (ψ.symm (Multiplicative.ofAdd (x, (0 : F))))
      rw [hU1, ← hγr, map_mul, map_inv, toAdd_mul, toAdd_inv, hψ, MulEquiv.apply_symm_apply] at h1
      have h1' : A γ x - x ∈ ℓ := by rw [sub_eq_add_neg]; exact h1
      obtain ⟨a, ha⟩ := (hℓ _).1 h1'
      refine ⟨a, ?_⟩
      rw [← ha]; abel
    obtain ⟨c, hc⟩ := S.tv_char he₀ (hA γ) hMx
    exact ⟨γ, c, hγr, hc⟩
  | one => exact ⟨1, 0, by simp, fun x => by rw [map_one, S.tvEquiv_zero]; rfl⟩
  | mul r s _ _ hr hs =>
    obtain ⟨γ, c, hγ, hc⟩ := hr
    obtain ⟨γ', c', hγ', hc'⟩ := hs
    refine ⟨γ * γ', c + c', ?_, fun x => ?_⟩
    · rw [map_mul, Subgroup.coe_mul, hγ, hγ']
    · rw [map_mul, LinearEquiv.mul_apply, hc', hc, S.tvEquiv_add]
  | inv r _ hr =>
    obtain ⟨γ, c, hγ, hc⟩ := hr
    refine ⟨γ⁻¹, c, ?_, fun x => ?_⟩
    · rw [map_inv, Subgroup.coe_inv, hγ]
    · have h1 : S.tvEquiv e₀ c (A γ⁻¹ x) = x := by
        rw [← hc]
        have := congrArg (fun f : N ≃ₗ[F] N => f x)
          (show A γ * A γ⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
        simpa using this
      have h2 : S.tvEquiv e₀ c (S.tvEquiv e₀ c (A γ⁻¹ x)) = A γ⁻¹ x := by
        rw [← S.tvEquiv_add, ← two_mul, two_eq_zero_F, zero_mul, S.tvEquiv_zero]
      rw [← h2, h1]

end RootClassify2

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClause

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

theorem ψ_comm_vec (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u)) (γ : Γ) (u : U) :
    Multiplicative.toAdd (ψ ((π γ : MulAut U) u * u⁻¹)) =
      S.lift (hA γ) (Multiplicative.toAdd (ψ u)) - Multiplicative.toAdd (ψ u) := by
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hψ, sub_eq_add_neg]
  rfl

theorem ψ_comm_vec_tv (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u)) {γ : Γ}
    {e₀ : N} {c : F} (hγ : ∀ x, A γ x = S.tvEquiv e₀ c x) (u : U) :
    Multiplicative.toAdd (ψ ((π γ : MulAut U) u * u⁻¹)) =
      S.B (Multiplicative.toAdd (ψ u)).1 e₀ • ((c • e₀, S.tvκ e₀ c) : N × F) := by
  rw [ψ_comm_vec ψ π hψ, lift_eq_of_tv (S := S) (A := A) (hA := hA) γ hγ]
  refine Prod.ext ?_ ?_
  · show (Multiplicative.toAdd (ψ u)).1 + (c * S.B (Multiplicative.toAdd (ψ u)).1 e₀) • e₀ -
      (Multiplicative.toAdd (ψ u)).1 = S.B (Multiplicative.toAdd (ψ u)).1 e₀ • c • e₀
    rw [smul_smul, mul_comm]
    abel
  · show (Multiplicative.toAdd (ψ u)).2 + S.B (Multiplicative.toAdd (ψ u)).1 e₀ * S.tvκ e₀ c -
      (Multiplicative.toAdd (ψ u)).2 = S.B (Multiplicative.toAdd (ψ u)).1 e₀ * S.tvκ e₀ c
    ring

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem lifted_tv_zero (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u)) {γ : Γ}
    (hγ : ∀ x, A γ x = x) : (π γ : MulAut U) = 1 := by
  apply MulEquiv.ext
  intro u
  rw [MulAut.one_apply]
  apply ψ.injective
  rw [hψ]
  apply Multiplicative.toAdd.injective
  show S.lift (hA γ) (Multiplicative.toAdd (ψ u)) = Multiplicative.toAdd (ψ u)
  have := lift_eq_self_of_fix (S := S) (A := A) (hA := hA) γ (hγ (Multiplicative.toAdd (ψ u)).1)
    (Multiplicative.toAdd (ψ u)).2
  simpa using this

end RootClause

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClause2

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem commV_zpowers_tv (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)}
    (π : Γ →* ↥L)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u)) {γ : Γ}
    {e₀ : N} (he₀ : e₀ ≠ 0) {c : F} (hγ : ∀ x, A γ x = S.tvEquiv e₀ c x) (u : U) :
    u ∈ commV (Subgroup.zpowers (π γ : MulAut U)) ↔
      ∃ a : F, Multiplicative.toAdd (ψ u) = a • ((c • e₀, S.tvκ e₀ c) : N × F) := by
  have hr2 : (π γ : MulAut U) ^ 2 = 1 := by
    have h1 : (π (γ ^ 2) : MulAut U) = 1 := by
      apply lifted_tv_zero ψ π hψ
      intro x
      rw [pow_two, map_mul, LinearEquiv.mul_apply, hγ, hγ, ← S.tvEquiv_add, ← two_mul,
        two_eq_zero_F, zero_mul, S.tvEquiv_zero]
    rw [map_pow] at h1
    exact h1
  let H2 : Subgroup (MulAut U) :=
    { carrier := {x | x = 1 ∨ x = (π γ : MulAut U)}
      one_mem' := Or.inl rfl
      mul_mem' := fun {a b} ha hb => by
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl (mul_one 1)
        · exact Or.inr (one_mul _)
        · exact Or.inr (mul_one _)
        · exact Or.inl (by rw [← pow_two]; exact hr2)
      inv_mem' := fun {a} ha => by
        rcases ha with rfl | rfl
        · exact Or.inl inv_one
        · exact Or.inr (by
            have : (π γ : MulAut U) * (π γ : MulAut U) = 1 := by rw [← pow_two]; exact hr2
            exact inv_eq_of_mul_eq_one_right this) }
  have hzp : Subgroup.zpowers (π γ : MulAut U) ≤ H2 := Subgroup.zpowers_le.2 (Or.inr rfl)
  constructor
  · intro hu
    unfold commV at hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, v, rfl⟩ := hx
      rcases hzp hy with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨_, ψ_comm_vec_tv ψ π hψ hγ v⟩
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_mul, toAdd_mul, ha, hb, add_smul]⟩
    | inv x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨-a, by rw [map_inv, toAdd_inv, ha, neg_smul]⟩
  · rintro ⟨a, ha⟩
    obtain ⟨x₁, hx₁⟩ := S.exists_B_eq_one he₀
    have hv := ψ_comm_vec_tv ψ π hψ hγ (ψ.symm (Multiplicative.ofAdd (a • x₁, (0 : F))))
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hv
    have hBa : S.B (a • x₁, (0 : F)).1 e₀ = a := by
      show S.B (a • x₁) e₀ = a
      rw [map_smul, LinearMap.smul_apply, hx₁, smul_eq_mul, mul_one]
    rw [hBa] at hv
    have hu : u = (π γ : MulAut U) (ψ.symm (Multiplicative.ofAdd (a • x₁, (0 : F)))) *
        (ψ.symm (Multiplicative.ofAdd (a • x₁, (0 : F))))⁻¹ := by
      apply ψ.injective
      apply Multiplicative.toAdd.injective
      rw [hv, ha]
    rw [hu]
    exact Subgroup.subset_closure ⟨(π γ : MulAut U), Subgroup.mem_zpowers _, _, rfl⟩

end RootClause2

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClause3

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

theorem lines_inf_bot {e₀ : N} (he₀ : e₀ ≠ 0) {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hcc : c ≠ c') {a a' : F}
    (h : a • ((c • e₀, S.tvκ e₀ c) : N × F) = a' • ((c' • e₀, S.tvκ e₀ c') : N × F)) : a = 0 := by
  by_contra ha0
  have h1 : a * c = a' * c' := by
    have := congrArg Prod.fst h
    simp only [Prod.smul_fst, smul_smul] at this
    exact smul_left_injective F he₀ this
  have h2 : a * S.tvκ e₀ c = a' * S.tvκ e₀ c' := by
    have := congrArg Prod.snd h
    simpa using this
  have h3 : (a * S.tvκ e₀ c) ^ 2 = (a' * S.tvκ e₀ c') ^ 2 := by rw [h2]
  rw [mul_pow, mul_pow, S.tvκ_sq, S.tvκ_sq] at h3
  have h4 : a * c * (a - a') = 0 := by
    have h5 : (a * c) ^ 2 = (a' * c') ^ 2 := by rw [h1]
    linear_combination h3 - (S.Q0 e₀) * h5 - a' * h1
  have h6 : a - a' = 0 := by
    rcases mul_eq_zero.1 h4 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' ha0
      · exact absurd h' hc
    · exact h
  have h7 : a = a' := sub_eq_zero.1 h6
  rw [← h7] at h1
  exact hcc (mul_left_cancel₀ ha0 h1)

end RootClause3

end burnsideI23x_SD

namespace burnsideI23x_SD

section RootClause4

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem orth_roots (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)} {K : Subgroup U}
    (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    (hψK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0)
    {e₀ : N} (he₀ : e₀ ≠ 0) {ℓ : AddSubgroup N} (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀)
    {U1 : Subgroup U} (hU1 : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ) :
    ∀ r ∈ i23TransvectionRoot L K U1, r ≠ 1 →
      (IsFSubspaceVia (F := F) ψ (commV (Subgroup.zpowers r)) 1 ∧
        (∃ v ∈ commV (Subgroup.zpowers r), S.Qw (Multiplicative.toAdd (ψ v)) ≠ 0) ∧
        commV (Subgroup.zpowers r) ≤ U1 ∧ commV (Subgroup.zpowers r) ≠ K) ∧
      (∀ s ∈ i23TransvectionRoot L K U1, s ∉ Subgroup.zpowers r →
        commV (Subgroup.zpowers r) ⊓ commV (Subgroup.zpowers s) = ⊥) := by
  intro r hr hr1
  obtain ⟨γ, c, hγr, hc⟩ := S.root_classify ψ π hπs hψ he₀ hℓ hU1 r hr
  subst hγr
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hr1 (lifted_tv_zero ψ π hψ (fun x => by rw [hc, S.tvEquiv_zero]))
  have hdesc := fun u => commV_zpowers_tv ψ π hψ he₀ hc u
  have hsc1 : (c • e₀ : N) ≠ 0 := fun h => he₀ ((smul_eq_zero.1 h).resolve_left hc0)
  have hscne : ((c • e₀, S.tvκ e₀ c) : N × F) ≠ 0 := fun h => hsc1 (congrArg Prod.fst h)
  refine ⟨⟨⟨Submodule.span F {((c • e₀, S.tvκ e₀ c) : N × F)}, finrank_span_singleton hscne,
    fun u => ?_⟩, ?_, ?_, ?_⟩, fun s hs hsr => ?_⟩
  · rw [hdesc, Submodule.mem_span_singleton]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  · refine ⟨ψ.symm (Multiplicative.ofAdd ((c • e₀, S.tvκ e₀ c) : N × F)),
      (hdesc _).2 ⟨1, by simp⟩, ?_⟩
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    show S.Q0 (c • e₀) + S.tvκ e₀ c ^ 2 ≠ 0
    rw [S.Q0_smul, S.tvκ_sq]
    have h2 := add_self_F (c ^ 2 * S.Q0 e₀)
    intro h
    apply hc0
    linear_combination h - h2
  · intro u hu
    obtain ⟨a, ha⟩ := (hdesc u).1 hu
    rw [hU1, ha]
    exact (hℓ _).2 ⟨a * c, by simp [smul_smul]⟩
  · intro hEq
    have hmem : ψ.symm (Multiplicative.ofAdd ((c • e₀, S.tvκ e₀ c) : N × F)) ∈
        commV (Subgroup.zpowers (π γ : MulAut U)) := (hdesc _).2 ⟨1, by simp⟩
    rw [hEq, hψK, MulEquiv.apply_symm_apply, toAdd_ofAdd] at hmem
    exact hsc1 hmem
  · obtain ⟨γ', c', hγ's, hc'⟩ := S.root_classify ψ π hπs hψ he₀ hℓ hU1 s hs
    subst hγ's
    have hs1 : (π γ' : MulAut U) ≠ 1 := fun h => hsr (h ▸ Subgroup.one_mem _)
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      exact hs1 (lifted_tv_zero ψ π hψ (fun x => by rw [hc', S.tvEquiv_zero]))
    have hcc : c ≠ c' := by
      rintro rfl
      apply hsr
      have : (π γ' : MulAut U) = (π γ : MulAut U) := by
        apply MulEquiv.ext
        intro u
        apply ψ.injective
        rw [hψ, hψ]
        apply Multiplicative.toAdd.injective
        show S.lift (hA γ') (Multiplicative.toAdd (ψ u)) = S.lift (hA γ) (Multiplicative.toAdd (ψ u))
        rw [lift_eq_of_tv (S := S) (A := A) (hA := hA) γ' hc',
          lift_eq_of_tv (S := S) (A := A) (hA := hA) γ hc]
      rw [this]
      exact Subgroup.mem_zpowers _
    rw [eq_bot_iff]
    intro u ⟨hu1, hu2⟩
    obtain ⟨a, ha⟩ := (hdesc u).1 hu1
    obtain ⟨a', ha'⟩ := (commV_zpowers_tv ψ π hψ he₀ hc' u).1 hu2
    have ha0 : a = 0 := S.lines_inf_bot he₀ hc0 hc'0 hcc (ha.symm.trans ha')
    apply Subgroup.mem_bot.2
    apply ψ.injective
    apply Multiplicative.toAdd.injective
    rw [ha, ha0, zero_smul, map_one, toAdd_one]

end RootClause4

end burnsideI23x_SD
@[expose] noncomputable def burnsideI23x_glEquiv (ι : Type) [Fintype ι] [DecidableEq ι] (F : Type)
    [Field F] : Matrix.GeneralLinearGroup ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))

open scoped Matrix in
theorem burnsideI23x_glEquiv_apply (ι : Type) [Fintype ι] [DecidableEq ι] (F : Type) [Field F]
    (A : Matrix.GeneralLinearGroup ι F) (v : ι → F) :
    burnsideI23x_glEquiv ι F A v = (A : Matrix ι ι F) *ᵥ v := rfl

namespace burnsideI23x_SD

section ExistsLift

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] (S : burnsideI23x_SD F N)

theorem isometry_Bw {g : (N × F) ≃ₗ[F] (N × F)} (hg : ∀ w, S.Qw (g w) = S.Qw w) (w w' : N × F) :
    S.Bw (g w) (g w') = S.Bw w w' := by
  have h1 := S.Qw_add w w'
  have h2 := S.Qw_add (g w) (g w')
  rw [← map_add, hg, hg, hg] at h2
  have : S.Bw (g w) (g w') = S.Bw w w' := by linear_combination h1 - h2
  exact this

theorem isometry_rad {g : (N × F) ≃ₗ[F] (N × F)} (hg : ∀ w, S.Qw (g w) = S.Qw w) {w : N × F}
    (hw : w.1 = 0) : (g w).1 = 0 := by
  apply S.nondeg
  intro y
  obtain ⟨w', hw'⟩ : ∃ w', g w' = (y, 0) := ⟨g.symm (y, 0), g.apply_symm_apply _⟩
  have h := S.isometry_Bw hg w w'
  rw [hw'] at h
  have h0 : S.Bw w w' = 0 := by
    show S.B w.1 w'.1 = 0
    rw [hw, map_zero, LinearMap.zero_apply]
  show S.B (g w).1 y = 0
  have : S.Bw (g w) (y, 0) = 0 := by rw [h, h0]
  exact this

theorem exists_lift_of_isometry {g : (N × F) ≃ₗ[F] (N × F)} (hg : ∀ w, S.Qw (g w) = S.Qw w) :
    ∃ (M : N ≃ₗ[F] N) (hM : S.Symp M), ∀ w, g w = S.lift hM w := by
  have hgi : ∀ w, S.Qw (g.symm w) = S.Qw w := fun w => by
    have := hg (g.symm w)
    rw [g.apply_symm_apply] at this
    exact this.symm
  let Ml : N →ₗ[F] N := (LinearMap.fst F N F).comp (g.toLinearMap.comp (LinearMap.inl F N F))
  have hMl : ∀ w, (g w).1 = Ml w.1 := by
    intro w
    have hw : w = (w.1, 0) + (0, w.2) := by ext <;> simp
    conv_lhs => rw [hw, map_add, Prod.fst_add, S.isometry_rad hg (w := (0, w.2)) rfl, add_zero]
    rfl
  have hinj : Function.Injective Ml := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (g (x, 0)).1 = 0 := by rw [hMl]; exact hx
    have h2 := S.isometry_rad hgi (w := g (x, 0)) h1
    rw [g.symm_apply_apply] at h2
    exact h2
  haveI : FiniteDimensional F N := Module.Finite.of_finite
  let M : N ≃ₗ[F] N := LinearEquiv.ofInjectiveEndo Ml hinj
  have hMapp : ∀ x, M x = Ml x := fun x => by
    rw [show M x = (LinearEquiv.ofInjectiveEndo Ml hinj) x from rfl, LinearEquiv.coe_ofInjectiveEndo]
  have hMsymp : S.Symp M := by
    intro x y
    rw [hMapp, hMapp, show Ml x = (g (x, 0)).1 from (hMl (x, 0)).symm,
      show Ml y = (g (y, 0)).1 from (hMl (y, 0)).symm]
    exact S.isometry_Bw hg (x, 0) (y, 0)
  refine ⟨M, hMsymp, fun w => ?_⟩
  exact (S.lift_unique hMsymp (fun w => g w) (fun w => by rw [hMl, hMapp]) hg w)

end ExistsLift

end burnsideI23x_SD
namespace burnsideI23x_SD

section PhiHom

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem lift_one_eq (w : N × F) : S.lift (hA 1) w = w := by
  have := lift_eq_self_of_fix (S := S) (A := A) (hA := hA) 1 (x := w.1)
    (by rw [map_one]; rfl) w.2
  simpa using this

theorem lift_mul_eq (γ δ : Γ) (w : N × F) :
    S.lift (hA (γ * δ)) w = S.lift (hA γ) (S.lift (hA δ) w) := by
  have h := congrArg Multiplicative.toAdd
    (congrArg (fun f : MulAut (Multiplicative (N × F)) => f (Multiplicative.ofAdd w))
      (map_mul (S.liftHom A hA) γ δ))
  exact h

variable (S A hA)

@[expose] noncomputable def phiHom (κ : (N × F) ≃ₗ[F] (ι → F)) : Γ →* Matrix.GeneralLinearGroup ι F where
  toFun γ := (burnsideI23x_glEquiv ι F).symm (κ.symm.trans ((S.lift (hA γ)).trans κ))
  map_one' := by
    rw [MulEquiv.symm_apply_eq, MulEquiv.map_one]
    apply LinearEquiv.ext
    intro v
    show κ (S.lift (hA 1) (κ.symm v)) = v
    rw [lift_one_eq, LinearEquiv.apply_symm_apply]
  map_mul' γ δ := by
    rw [MulEquiv.symm_apply_eq, MulEquiv.map_mul, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    apply LinearEquiv.ext
    intro v
    show κ (S.lift (hA (γ * δ)) (κ.symm v)) =
      κ (S.lift (hA γ) (κ.symm (κ (S.lift (hA δ) (κ.symm v)))))
    rw [lift_mul_eq, LinearEquiv.symm_apply_apply]

variable {S A hA}

open scoped Matrix in
theorem phiHom_mulVec (κ : (N × F) ≃ₗ[F] (ι → F)) (γ : Γ) (w : N × F) :
    ((phiHom S A hA κ γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *ᵥ (κ w) =
      κ (S.lift (hA γ) w) := by
  show (burnsideI23x_glEquiv ι F) ((burnsideI23x_glEquiv ι F).symm
    (κ.symm.trans ((S.lift (hA γ)).trans κ))) (κ w) = _
  rw [MulEquiv.apply_symm_apply]
  show κ (S.lift (hA γ) (κ.symm (κ w))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem phiHom_injective (κ : (N × F) ≃ₗ[F] (ι → F))
    (hfaith : ∀ γ, (∀ x, A γ x = x) → γ = 1) : Function.Injective (phiHom S A hA κ) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply hfaith
  intro x
  have h := phiHom_mulVec κ γ (x, 0) (hA := hA) (A := A) (S := S)
  rw [hγ] at h
  have h2 : κ (x, (0 : F)) = κ (S.lift (hA γ) (x, 0)) := by
    rw [← h]
    simp
  have h3 := κ.injective h2
  exact (congrArg Prod.fst h3).symm

end PhiHom

end burnsideI23x_SD

open scoped Matrix in
theorem burnsideI23x_mem_isometryCore {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (Q : (ι → F) → F) (A : Matrix.GeneralLinearGroup ι F) :
    A ∈ CFSG.MatrixModel.isometryCore Q ↔
      ∀ v : ι → F, Q ((A : Matrix ι ι F) *ᵥ v) = Q v := by
  constructor
  · intro h
    unfold CFSG.MatrixModel.isometryCore at h
    induction h using Subgroup.closure_induction with
    | mem A hA => exact hA
    | one => intro v; simp
    | mul A B _ _ hA hB =>
      intro v
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
    | inv A _ hA =>
      intro v
      have h1 : (A : Matrix ι ι F) *ᵥ ((A⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *ᵥ v = v := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← hA (((A⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) *ᵥ v), h1]
  · intro h
    exact Subgroup.subset_closure h

namespace burnsideI23x_SD

section PhiRange

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Matrix in
theorem phiHom_range (κ : (N × F) ≃ₗ[F] (ι → F)) (Q' : (ι → F) → F)
    (hκ : ∀ w, Q' (κ w) = S.Qw w)
    (hsurj : ∀ M : N ≃ₗ[F] N, S.Symp M → ∃ γ, ∀ x, A γ x = M x)
    (hperf : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ = (⊤ : Subgroup Γ)) :
    (phiHom S A hA κ).range =
      ⁅CFSG.MatrixModel.isometryCore Q', CFSG.MatrixModel.isometryCore Q'⁆ := by
  set O := CFSG.MatrixModel.isometryCore Q' with hO
  have hrO : (phiHom S A hA κ).range ≤ O := by
    rintro _ ⟨γ, rfl⟩
    rw [hO, burnsideI23x_mem_isometryCore]
    intro v
    obtain ⟨w, rfl⟩ := κ.surjective v
    rw [phiHom_mulVec, hκ, hκ, S.Qw_lift]
  apply le_antisymm
  · have h1 : (phiHom S A hA κ).range = (⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆).map (phiHom S A hA κ) := by
      rw [hperf, MonoidHom.range_eq_map]
    rw [h1, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    exact Subgroup.commutator_mono hrO hrO
  · have hcomm : ⁅O, O⁆ ≤ O := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact O.mul_mem (O.mul_mem (O.mul_mem ha hb) (O.inv_mem ha)) (O.inv_mem hb)
    refine hcomm.trans (fun Am hAm => ?_)
    have hiso := (burnsideI23x_mem_isometryCore Q' Am).1 hAm
    let g : (N × F) ≃ₗ[F] (N × F) := (κ.trans (burnsideI23x_glEquiv ι F Am)).trans κ.symm
    have hg : ∀ w, S.Qw (g w) = S.Qw w := by
      intro w
      show S.Qw (κ.symm ((Am : Matrix ι ι F) *ᵥ κ w)) = S.Qw w
      rw [← hκ, LinearEquiv.apply_symm_apply, hiso, hκ]
    obtain ⟨M, hM, hgM⟩ := S.exists_lift_of_isometry hg
    obtain ⟨γ, hγ⟩ := hsurj M hM
    refine ⟨γ, ?_⟩
    apply (burnsideI23x_glEquiv ι F).injective
    apply LinearEquiv.ext
    intro v
    obtain ⟨w, rfl⟩ := κ.surjective v
    rw [burnsideI23x_glEquiv_apply, burnsideI23x_glEquiv_apply, phiHom_mulVec]
    have h1 : (Am : Matrix ι ι F) *ᵥ κ w = κ (g w) := by
      show _ = κ (κ.symm ((Am : Matrix ι ι F) *ᵥ κ w))
      rw [LinearEquiv.apply_symm_apply]
    rw [h1, hgM]
    congr 1
    refine Prod.ext ?_ ?_
    · exact (hγ w.1)
    · show w.2 + S.lf (A γ) w.1 = w.2 + S.lf M w.1
      unfold lf
      rw [hγ]

end PhiRange

end burnsideI23x_SD

namespace burnsideI23x_SD

section PiOmega

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_piOmega (κ : (N × F) ≃ₗ[F] (ι → F)) (Ωg : Subgroup (Matrix.GeneralLinearGroup ι F))
    (hrange : (phiHom S A hA κ).range = Ωg) (hfaith : ∀ γ, (∀ x, A γ x = x) → γ = 1)
    {U : Type} [CommGroup U] {L : Subgroup (MulAut U)} (marking : Γ →* ↥L)
    (hms : Function.Surjective marking) :
    ∃ π : ↥Ωg →* ↥L, Function.Surjective π ∧ ∀ A' : ↥Ωg, ∃ γ : Γ, π A' = marking γ ∧
      (A' : Matrix.GeneralLinearGroup ι F) = phiHom S A hA κ γ := by
  have hinj := phiHom_injective κ hfaith (S := S) (A := A) (hA := hA)
  let eΩ : ↥Ωg ≃* Γ :=
    (MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm
  refine ⟨marking.comp eΩ.toMonoidHom, hms.comp eΩ.surjective, fun A' => ⟨eΩ A', rfl, ?_⟩⟩
  have h1 : (MonoidHom.ofInjective hinj) (eΩ A') = (MulEquiv.subgroupCongr hrange).symm A' := by
    show (MonoidHom.ofInjective hinj) ((MonoidHom.ofInjective hinj).symm
      ((MulEquiv.subgroupCongr hrange).symm A')) = _
    rw [MulEquiv.apply_symm_apply]
  have h2 := congrArg (fun x : ↥(phiHom S A hA κ).range => (x : Matrix.GeneralLinearGroup ι F)) h1
  exact h2.symm

end PiOmega

end burnsideI23x_SD
namespace burnsideI23x_SD

section Transport

variable {F : Type} [Field F] {W W' : Type} [AddCommGroup W] [Module F W] [AddCommGroup W']
  [Module F W'] {V : Type} [CommGroup V]

@[expose] def psiTrans (ψ : V ≃* Multiplicative W) (κ : W ≃ₗ[F] W') : V ≃* Multiplicative W' :=
  ψ.trans κ.toAddEquiv.toMultiplicative

theorem toAdd_psiTrans (ψ : V ≃* Multiplicative W) (κ : W ≃ₗ[F] W') (v : V) :
    Multiplicative.toAdd (psiTrans ψ κ v) = κ (Multiplicative.toAdd (ψ v)) := rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem isFSubspaceVia_transport (ψ : V ≃* Multiplicative W) (κ : W ≃ₗ[F] W') (P : Subgroup V)
    (k : ℕ) : IsFSubspaceVia (F := F) ψ P k ↔ IsFSubspaceVia (F := F) (psiTrans ψ κ) P k := by
  constructor
  · rintro ⟨S, hS, hmem⟩
    refine ⟨S.map κ.toLinearMap, ?_, fun v => ?_⟩
    · rw [LinearEquiv.finrank_map_eq]
      exact hS
    · rw [toAdd_psiTrans, hmem v]
      constructor
      · intro h; exact ⟨_, h, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        have : x = Multiplicative.toAdd (ψ v) := κ.injective hxy
        rw [← this]; exact hx
  · rintro ⟨S, hS, hmem⟩
    refine ⟨S.map κ.symm.toLinearMap, ?_, fun v => ?_⟩
    · rw [LinearEquiv.finrank_map_eq]
      exact hS
    · rw [hmem v, toAdd_psiTrans]
      constructor
      · intro h; exact ⟨_, h, by simp⟩
      · rintro ⟨x, hx, hxy⟩
        have : x = κ (Multiplicative.toAdd (ψ v)) := by
          rw [← hxy]; simp
        rw [← this]; exact hx

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem polarOf_transport (Q : W → F) (Q' : W' → F) (κ : W ≃ₗ[F] W') (hκ : ∀ w, Q' (κ w) = Q w)
    (x y : W) : polarOf Q' (κ x) (κ y) = polarOf Q x y := by
  unfold polarOf
  rw [← map_add, hκ, hκ, hκ]

end Transport

end burnsideI23x_SD

namespace burnsideI23x_SD

section OrthMarked

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {Γ : Type} [Group Γ] {A : Γ →* (N ≃ₗ[F] N)}
  {hA : ∀ γ, S.Symp (A γ)} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem orthConclMarked_tv {m n : ℕ} (hm : m = 1 ∨ m = 2) (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {W' : Type} [AddCommGroup W'] [Module F W'] (Q' : W' → F)
    (κ : (N × F) ≃ₗ[F] W') (hκ : ∀ w, Q' (κ w) = S.Qw w)
    (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)} {K : Subgroup U}
    (π : Γ →* ↥L) (hπs : Function.Surjective π)
    (hψ : ∀ (γ : Γ) (u : U), ψ ((π γ : MulAut U) u) = S.liftHom A hA γ (ψ u))
    (hψK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0) (hfixV : fixV L = K)
    {e₀ : N} (he₀ : e₀ ≠ 0) {ℓ : AddSubgroup N} (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀)
    {U1 U2 : Subgroup U} (hU1 : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ)
    {T : Subgroup (MulAut U)} (hfixP : U1 = fixV (T ⊓ L))
    (hroot : U1 = commV (i23TransvectionRoot L K U1) ∧
      commV (i23TransvectionRoot L K U1) ≤ fixV (i23TransvectionRoot L K U1))
    (S' : Subgroup (MulAut U)) :
    OrthConclMarked Q' m n (psiTrans ψ κ) L T (i23TransvectionRoot L K U1) S' U1 U2 := by
  have hQ : ∀ v, Q' (Multiplicative.toAdd (psiTrans ψ κ v)) =
      S.Qw (Multiplicative.toAdd (ψ v)) := fun v => by rw [toAdd_psiTrans, hκ]
  refine ⟨?_, ⟨hfixP, ?_⟩, fun _ => ⟨fun r hr hr1 => ?_, fun _ => ?_⟩, fun h => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2⟩ := S.orth_radical ψ hψK hfixV
    refine ⟨fun v => ?_, by rw [h2, hF]⟩
    rw [h1 v]
    constructor
    · intro h w'
      obtain ⟨w, rfl⟩ := κ.surjective w'
      rw [toAdd_psiTrans, polarOf_transport S.Qw Q' κ hκ]
      exact h w
    · intro h w
      have := h (κ w)
      rwa [toAdd_psiTrans, polarOf_transport S.Qw Q' κ hκ] at this
  · obtain ⟨P, hP, hPu⟩ := S.orth_point ψ hψK he₀ hℓ hU1
    rw [← hfixV] at hP hPu
    refine ⟨P, ⟨(isFSubspaceVia_transport ψ κ P 1).1 hP.1, fun v hv => by
      rw [hQ]; exact hP.2.1 v hv, hP.2.2.1, hP.2.2.2⟩, fun P' hP' => hPu P' ⟨
        (isFSubspaceVia_transport ψ κ P' 1).2 hP'.1, fun v hv => by
        rw [← hQ]; exact hP'.2.1 v hv, hP'.2.2.1, hP'.2.2.2⟩⟩
  · obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := S.orth_roots ψ π hπs hψ hψK he₀ hℓ hU1 r hr hr1
    refine ⟨⟨(isFSubspaceVia_transport ψ κ _ 1).1 h1, ?_, h3, by rw [hfixV]; exact h4⟩, ?_⟩
    · obtain ⟨v, hv, hne⟩ := h2
      exact ⟨v, hv, by rw [hQ]; exact hne⟩
    · intro _ s hs hsr
      exact h5 s hs hsr
  · exact hroot
  · exact absurd h.2 (by omega)
  · exact absurd h (by omega)

end OrthMarked

end burnsideI23x_SD
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_scalarCompat {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM) {V : Type} [CommGroup V]
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    {ψ₀ : V ≃* Multiplicative (M × F)}
    (hψfst : ∀ u : V, (Multiplicative.toAdd (ψ₀ u)).1 = Multiplicative.toAdd (LM.e (β u)))
    {W' : Type} [AddCommGroup W'] [Module F W'] (κ : (M × F) ≃ₗ[F] W') :
    I23ScalarCompatibility m F (burnsideI23x_SD.psiTrans ψ₀ κ) β := by
  intro scalar vector native hβ
  refine ⟨hS.mem scalar native, ?_⟩
  set u' := (burnsideI23x_SD.psiTrans ψ₀ κ).symm (Multiplicative.ofAdd
    (scalar • Multiplicative.toAdd (burnsideI23x_SD.psiTrans ψ₀ κ vector))) with hu'
  have h1 : Multiplicative.toAdd (ψ₀ u') = scalar • Multiplicative.toAdd (ψ₀ vector) := by
    have h2 : burnsideI23x_SD.psiTrans ψ₀ κ u' = Multiplicative.ofAdd
        (scalar • Multiplicative.toAdd (burnsideI23x_SD.psiTrans ψ₀ κ vector)) := by
      rw [hu', MulEquiv.apply_symm_apply]
    have h3 := congrArg Multiplicative.toAdd h2
    rw [burnsideI23x_SD.toAdd_psiTrans, toAdd_ofAdd, burnsideI23x_SD.toAdd_psiTrans,
      ← map_smul] at h3
    exact κ.injective h3
  have h4 : Multiplicative.toAdd (LM.e (β u')) = scalar • Multiplicative.toAdd (LM.e (β vector)) := by
    rw [← hψfst, ← hψfst, h1]
    rfl
  have h5 := hS.eq scalar native (hS.mem scalar native)
  rw [← hβ] at h5
  have h6 : LM.e (β u') = LM.e (QuotientGroup.mk ⟨i23NaturalScalar m F scalar
      (native : (i23NaturalModel m F).Amb), hS.mem scalar native⟩) := by
    apply Multiplicative.toAdd.injective
    rw [h4, h5]
  exact LM.e.injective h6

@[expose] noncomputable def burnsideI23x_kappa1 (F : Type) [Field F] :
    ((Fin 2 → F) × F) ≃ₗ[F] (Fin 1 ⊕ Fin 1 ⊕ Unit → F) where
  toFun w := fun i => match i with
    | Sum.inl _ => w.1 0
    | Sum.inr (Sum.inl _) => w.1 1
    | Sum.inr (Sum.inr _) => w.2
  invFun v := (![v (Sum.inl 0), v (Sum.inr (Sum.inl 0))], v (Sum.inr (Sum.inr ())))
  map_add' w w' := by
    funext i
    rcases i with i | i | i <;> simp
  map_smul' c w := by
    funext i
    rcases i with i | i | i <;> simp
  left_inv w := by
    refine Prod.ext ?_ rfl
    funext j
    fin_cases j <;> rfl
  right_inv v := by
    funext i
    rcases i with i | i | i
    · have : i = 0 := Subsingleton.elim _ _
      subst this; rfl
    · have : i = 0 := Subsingleton.elim _ _
      subst this; rfl
    · rfl

theorem burnsideI23x_kappa1_Q (F : Type) [Field F] [CharP F 2] (w : (Fin 2 → F) × F) :
    StatedQuadOdd 1 F (burnsideI23x_kappa1 F w) = (burnsideI23x_sd1 F).Qw w := by
  show _ = (burnsideI23x_sd1 F).Q0 w.1 + w.2 ^ 2
  rw [burnsideI23x_sd1_Q0]
  show ∑ i : Fin 1, w.1 0 * w.1 1 + w.2 ^ 2 = _
  simp
open CFSG.Quasithin CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_statedSL2_perfect {F : Type} [Field F] [CharP F 2] {a : F} (ha0 : a ≠ 0)
    (ha1 : a ≠ 1) :
    ⁅(⊤ : Subgroup ↥(StatedSL 2 F)), (⊤ : Subgroup ↥(StatedSL 2 F))⁆ =
      (⊤ : Subgroup ↥(StatedSL 2 F)) := by
  have hsq : a ^ 2 ≠ 1 := by
    intro h
    apply ha1
    apply burnsideI23x_sq_injective
    rw [h, one_pow]
  have hcomm := Matrix.SL2.commutator_eq_top ha0 hsq
  let e := specialLinearGroupEquivStatedSL 2 F
  have h1 : Subgroup.map e.toMonoidHom (⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))⁆) =
      ⁅Subgroup.map e.toMonoidHom (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
        Subgroup.map e.toMonoidHom (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))⁆ :=
    Subgroup.map_commutator _ _ _
  have hcomm' : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))⁆ = ⊤ := hcomm
  have htop : Subgroup.map e.toMonoidHom (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 e.surjective
  rw [hcomm', htop] at h1
  exact h1.symm

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_part1_m1 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 1 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 1 F).sec ⧸
      (i23NaturalModel 1 F).ker.subgroupOf (i23NaturalModel 1 F).sec}
    (hsec : I23SectionMap (i23NaturalModel 1 F) L W0 marking β)
    (hT2 : IsPGroup 2 T) {V1 : Subgroup V} (h1 : IsI23MarkedSubspace 1 n 1 F T W0 V1 β)
    (hflag1 : ∀ U', IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U' → U' = V1)
    (S' : Subgroup (MulAut V)) (V2 : Subgroup V) (huniv : IsUniversalCovering L W0) :
    ∃ (ψ : V ≃* Multiplicative (Fin 1 ⊕ Fin 1 ⊕ Unit → F))
      (π : ↥(StatedOmega (StatedQuadOdd 1 F)) →* ↥L),
      Function.Surjective π ∧
      (∀ (γ : ↥(StatedOmega (StatedQuadOdd 1 F))) (v : V), ψ ((π γ : MulAut V) v) =
        Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin 1 ⊕ Unit) F) :
          Matrix (Fin 1 ⊕ Fin 1 ⊕ Unit) (Fin 1 ⊕ Fin 1 ⊕ Unit) F).mulVec
            (Multiplicative.toAdd (ψ v)))) ∧
      I23ScalarCompatibility 1 F ψ β ∧
      OrthConclMarked (StatedQuadOdd 1 F) 1 n ψ L T (i23TransvectionRoot L W0 V1) S' V1 V2 := by
  haveI : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have hS := burnsideI23x_scalarAgree1 F
  obtain ⟨a, ha0, ha1⟩ := burnsideI23x_exists_ne_zero_one hF hn
  have htv' : ∀ (e : Fin 2 → F) (c : F), e ≠ 0 → ∃ γ, ∀ x,
      (burnsideI23x_LM1 F).lin γ x = (burnsideI23x_sd1 F).tvEquiv e c x :=
    fun e c _ => burnsideI23x_htv1 F e c
  have hgenM := burnsideI23x_SD.genW'_of_tv (burnsideI23x_sd1 F) (burnsideI23x_LM1 F).lin htv'
    ha0 ha1
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM1 F) (burnsideI23x_sd1 F) (burnsideI23x_hsymp1 F) (burnsideI23x_hfaith1 F)
    hgenM (burnsideI23x_hbound1 hn hF) hV huniv hsec
  have hEndLin := burnsideI23x_SD.hEnd_of_tv (burnsideI23x_sd1 F) (burnsideI23x_LM1 F).lin htv'
  have hsurj : ∀ M : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F), (burnsideI23x_sd1 F).Symp M →
      ∃ γ, ∀ x, A γ x = M x := fun M hM => by
    obtain ⟨γ, hγ⟩ := burnsideI23x_hsurj1 F M hM
    exact ⟨γ, fun x => (hAlin γ x).trans (hγ x)⟩
  have hfaith : ∀ γ, (∀ x, A γ x = x) → γ = 1 := fun γ h =>
    burnsideI23x_hfaith1 F γ (fun x => (hAlin γ x).symm.trans (h x))
  have hf := burnsideI23x_isCoord (burnsideI23x_LM1 F) hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  have hU1' : ∀ u, u ∈ V1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img V1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hcard1 : Nat.card (hf.img V1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img V1) hU1F hcard1
  have hψK : ∀ u, u ∈ W0 ↔ (Multiplicative.toAdd (ψ u)).1 = 0 := fun u => by
    rw [hψfst]
    exact (hf.ker u).symm
  have htvA : ∀ c : F, ∃ γ, ∀ x, A γ x = (burnsideI23x_sd1 F).tvEquiv e₀ c x := fun c => by
    obtain ⟨γ, hγ⟩ := burnsideI23x_htv1 F e₀ c
    exact ⟨γ, fun x => (hAlin γ x).trans (hγ x)⟩
  have hroot := burnsideI23x_SD.root_generation ψ marking hπs hψact hψK he₀ hℓ₁ hU1' ha0 ha1 htvA
  have hfixP : V1 = fixV (T ⊓ L) :=
    le_antisymm (burnsideI23x_SD.line_le_fixV_P ψ marking hπs hψact hT2 he₀ hℓ₁ hU1' h1.2.1)
      (burnsideI23x_fixV_P_le hEndLin hF hV hsec huniv.1 h1.1 hflag1)
  have hOrth := burnsideI23x_SD.orthConclMarked_tv (m := 1) (n := n) (Or.inl rfl) hn hF
    (StatedQuadOdd 1 F) (burnsideI23x_kappa1 F) (burnsideI23x_kappa1_Q F) ψ marking hπs hψact
    hψK hfixV he₀ hℓ₁ hU1' hfixP hroot S' (U2 := V2)
  have hrange := burnsideI23x_SD.phiHom_range (burnsideI23x_kappa1 F) (StatedQuadOdd 1 F)
    (burnsideI23x_kappa1_Q F) hsurj (burnsideI23x_statedSL2_perfect ha0 ha1)
    (S := burnsideI23x_sd1 F) (A := A) (hA := hA)
  obtain ⟨π, hπsurj, hπΩ⟩ := burnsideI23x_SD.exists_piOmega (burnsideI23x_kappa1 F)
    (StatedOmega (StatedQuadOdd 1 F)) hrange hfaith marking hπs
  refine ⟨burnsideI23x_SD.psiTrans ψ (burnsideI23x_kappa1 F), π, hπsurj, ?_,
    burnsideI23x_scalarCompat hS hψfst (burnsideI23x_kappa1 F), hOrth⟩
  intro A' v
  obtain ⟨γ, hπγ, hAγ⟩ := hπΩ A'
  rw [hπγ, hAγ]
  show Multiplicative.ofAdd (burnsideI23x_kappa1 F (Multiplicative.toAdd (ψ ((marking γ : MulAut V) v)))) = _
  rw [hψact]
  rw [burnsideI23x_SD.toAdd_psiTrans, burnsideI23x_SD.phiHom_mulVec]
  rfl
open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideI23x_sylow_inf_normal {Y : Type*} [Group Y] [Finite Y] {G L T : Subgroup Y}
    (hLG : L ≤ G) (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hT : IsSylowTwoOf T G) :
    IsSylowTwoOf (T ⊓ L) L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (L.subgroupOf G).Normal := ⟨fun n hn g => by
    have := hnorm g.1 g.2 n.1 hn
    exact this⟩
  exact (show IsSylowIn 2 T G from hT).inf_normal hLG hN
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_marked_flags' {m n : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β)
    (hcomm : ∀ T : M →+ M, (∀ (γ : (i23NaturalModel m F).Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0)
    (hflag : ∃ U₁ U₂ : Subgroup V, IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U₁ ∧
      IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 U₂ ∧ U₁ ≤ U₂ ∧
      (∀ U, IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U → U = U₁) ∧
      (∀ U, IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 U → U = U₂)) :
    ∃ V1 V2 : Subgroup V, IsI23MarkedSubspace m n 1 F T W0 V1 β ∧
      IsI23MarkedSubspace m n 2 F T W0 V2 β ∧ V1 ≤ V2 ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace m n 1 F T W0 U β → U = V1) ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace m n 2 F T W0 U β → U = V2) ∧
      (∀ U, IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U → U = V1) ∧
      (∀ U, IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 U → U = V2) := by
  obtain ⟨U₁, U₂, h1, h2, h12, u1, u2⟩ := hflag
  have hinvar : ∀ {i : ℕ} {U : Subgroup V}, IsFlagW L (T ⊓ L) W0 (2 ^ n) i U →
      (∀ U' : Subgroup V, IsFlagW L (T ⊓ L) W0 (2 ^ n) i U' → U' = U) →
      ∀ t ∈ T, ∀ u ∈ U, t u ∈ U := by
    intro i U hU huniq t ht u hu
    have hτW0 : t ∈ stabW W0 := burnsideI23x_mem_stabW_of_invariant hTW0 ht
    have hmap := isFlagW_map hU hτW0 (fun l hl => hTL t ht l hl) (fun p hp => by
      have hp' : t⁻¹ * p * t ∈ T ⊓ L := ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hp.1) ht,
        by simpa using hTL t⁻¹ (T.inv_mem ht) p hp.2⟩
      exact hU.2.2.2 hp')
    have := huniq _ hmap
    rw [← this]
    exact ⟨u, hu, rfl⟩
  refine ⟨U₁, U₂, burnsideI23x_flag_imp_marked hS hV h hcomm h1 (hinvar h1 u1),
    burnsideI23x_flag_imp_marked hS hV h hcomm h2 (hinvar h2 u2), h12, fun U hU => ?_,
    fun U hU => ?_, u1, u2⟩
  · exact u1 U (burnsideI23x_marked_imp_flag hS hV h hcomm hU)
  · exact u2 U (burnsideI23x_marked_imp_flag hS hV h hcomm hU)

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_marked_flags_m1' {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel 1 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 1 F).sec ⧸
      (i23NaturalModel 1 F).ker.subgroupOf (i23NaturalModel 1 F).sec}
    (h : I23SectionMap (i23NaturalModel 1 F) L W0 π β) (hW0 : W0 ≤ fixV L)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0)
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) :
    ∃ V1 V2 : Subgroup V, IsI23MarkedSubspace 1 n 1 F T W0 V1 β ∧
      IsI23MarkedSubspace 1 n 2 F T W0 V2 β ∧ V1 ≤ V2 ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 1 n 1 F T W0 U β → U = V1) ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 1 n 2 F T W0 U β → U = V2) ∧
      (∀ U, CFSG.Quasithin.Vol2.Ch11.SecA.IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U → U = V1) ∧
      (∀ U, CFSG.Quasithin.Vol2.Ch11.SecA.IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 U → U = V2) := by
  have hchar : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have hR := burnsideI23x_realizesVia h hW0
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat (StatedSL 2 F)) hR
  have hflag := burnsideI23x_flag12_sl2 hV hf hP
  rw [hF] at hflag
  exact burnsideI23x_marked_flags' (burnsideI23x_scalarAgree1 F) hV h
    (fun T' hT' => commutant_statedSL (by norm_num) T' hT') hTL hTW0 hflag
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_Concl (m n : ℕ) (F : Type) [Field F] [Finite F] (V : Type)
    [CommGroup V] [Finite V] (G L T : Subgroup (MulAut V)) (W0 : Subgroup V)
    (marking : (i23NaturalModel m F).Gam →* ↥L)
    (β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec) : Prop :=
      ∃ V1 V2 : Subgroup V,
        IsI23MarkedSubspace m n 1 F T W0 V1 β ∧
        IsI23MarkedSubspace m n 2 F T W0 V2 β ∧
        (∀ U : Subgroup V, IsI23MarkedSubspace m n 1 F T W0 U β → U = V1) ∧
        (∀ U : Subgroup V, IsI23MarkedSubspace m n 2 F T W0 U β → U = V2) ∧
        let R := i23TransvectionRoot L W0 V1
        ∃ S : Subgroup (MulAut V),
          (m = 3 → IsI23MarkedLongRoot m F L marking S ∧
            S = ChIJK.omegaOne (ChIJK.centerOf (T ⊓ L)) ∧
            (1 < n → S = ChIJK.centerOf (T ⊓ L))) ∧
          (m = 2 ∧ n = 1 → R = ⊥) ∧
      (IsUniversalCovering L W0 →
          ((m = 1 ∨ m = 2) →
            ∃ (ψ : V ≃* Multiplicative (Fin m ⊕ Fin m ⊕ Unit → F))
              (π : ↥(StatedOmega (StatedQuadOdd m F)) →* ↥L),
              Function.Surjective π ∧
              (∀ (γ : ↥(StatedOmega (StatedQuadOdd m F))) (v : V),
                ψ ((π γ : MulAut V) v) = Multiplicative.ofAdd
                  (((γ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m ⊕ Unit) F) :
                    Matrix (Fin m ⊕ Fin m ⊕ Unit) (Fin m ⊕ Fin m ⊕ Unit) F).mulVec
                    (Multiplicative.toAdd (ψ v)))) ∧
              I23ScalarCompatibility m F ψ β ∧
              OrthConclMarked (StatedQuadOdd m F) m n ψ L T R S V1 V2) ∧
          (m = 3 →
            ∃ (ψ : V ≃* Multiplicative ↥(zornO0F F))
              (π : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L),
              Function.Surjective π ∧
              (∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (v : V),
                ((Multiplicative.toAdd (ψ ((π γ : MulAut V) v)) : ↥(zornO0F F)) : quasithinZorn F) =
                  (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
                    ((Multiplicative.toAdd (ψ v) : ↥(zornO0F F)) : quasithinZorn F)) ∧
              I23ScalarCompatibility m F ψ β ∧
              OrthConclMarked (fun x : ↥(zornO0F F) => zornNorm F (x : quasithinZorn F)) m n ψ L T R S V1 V2)) ∧
      (¬ (fixV T ⊓ V1 ≤ fixV L) ∧
        I23LiteralCentralCore G V1 ∧ I23LiteralCentralCore G V2) ∧
      (1 < n → fixV L ≤ V1 ∧ (m ≠ 3 → V1 = commV R ∧ commV R ≤ fixV R))
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_case_m1 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    (hL : L = quasithinGenFitting G) (hGT : G = L ⊔ T) (hT : IsSylowTwoOf T G)
    (hGW0 : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) (hW0 : W0 ≤ fixV L) (hcomm : commV L = ⊤)
    (marking : (i23NaturalModel 1 F).Gam →* ↥L)
    (β : V →* ↥(i23NaturalModel 1 F).sec ⧸
      (i23NaturalModel 1 F).ker.subgroupOf (i23NaturalModel 1 F).sec)
    (hsec : I23SectionMap (i23NaturalModel 1 F) L W0 marking β) :
    burnsideI23x_Concl 1 n F V G L T W0 marking β := by
  haveI : Finite (MulAut V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hLG : L ≤ G := by rw [hL]; exact CFSG.Quasithin.quasithinGenFitting_le G
  have hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have h := CFSG.Quasithin.le_normalizer_quasithinGenFitting G hg
    rw [← hL] at h
    exact (Subgroup.mem_normalizer_iff.1 h l).1 hl
  have hTG : T ≤ G := hT.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht => hnorm t (hTG ht)
  have hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0 := fun t ht => hGW0 t (hTG ht)
  obtain ⟨V1, V2, h1, h2, h12, u1, u2, f1, f2⟩ :=
    burnsideI23x_marked_flags_m1' (by omega) hF hV hsec hW0 hTL hTW0 hP
  have hfixV : fixV L = W0 :=
    burnsideI23x_fixV_eq (burnsideI23x_LM1 F) hsec hW0 (burnsideI23x_nofix1 F)
  obtain ⟨t1, t2, t3⟩ := burnsideI23x_transfer (burnsideI23x_UCg_one hn) hF hV hLG hnorm hGT hT
    hGW0 hW0 hfixV hcomm hsec h1 h2
  refine ⟨V1, V2, h1, h2, u1, u2, ?_⟩
  intro R
  refine ⟨⊥, fun h => absurd h (by norm_num), fun h => absurd h.1 (by norm_num),
    fun huniv => ⟨fun _ => burnsideI23x_part1_m1 hn hF hV hsec hT.2.1 h1 f1 ⊥ V2 huniv,
      fun h3 => absurd h3 (by norm_num)⟩,
    ⟨t1, (burnsideI23x_centralCoreCompatibility V hV G V1).2 t2.1,
      (burnsideI23x_centralCoreCompatibility V hV G V2).2 t2.2⟩,
    fun hn' => ⟨by rw [hfixV]; exact h1.1, fun _ => t3 hn' (by norm_num)⟩⟩
open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 in
@[expose] def burnsideI23x_B2 (F : Type) [Field F] :
    (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F) →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => bil x y)
    (fun x x' y => by simp only [bil, Pi.add_apply]; ring)
    (fun c x y => by simp only [bil, Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [bil, Pi.add_apply]; ring)
    (fun c x y => by simp only [bil, Pi.smul_apply, smul_eq_mul]; ring)

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 in
theorem burnsideI23x_B2_apply (F : Type) [Field F] (x y : Fin 2 ⊕ Fin 2 → F) :
    burnsideI23x_B2 F x y = bil x y := rfl

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 in
@[expose] def burnsideI23x_sd2 (F : Type) [Field F] [CharP F 2] :
    burnsideI23x_SD F (Fin 2 ⊕ Fin 2 → F) where
  B := burnsideI23x_B2 F
  Q0 := sp4Quad F
  Q0_add x y := by
    rw [burnsideI23x_B2_apply]
    exact sp4Quad_add x y
  Q0_smul c x := by
    simp only [sp4Quad, Pi.smul_apply, smul_eq_mul]
    ring
  alt x := by
    rw [burnsideI23x_B2_apply]
    have h : (2 : F) = 0 := CharP.cast_eq_zero F 2
    simp only [bil]
    linear_combination (x (.inl 0) * x (.inr 0) + x (.inl 1) * x (.inr 1)) * h
  nondeg x hx := by
    funext i
    rcases i with i | i <;> fin_cases i
    · have h := hx (Pi.single (Sum.inr 0) 1)
      rw [burnsideI23x_B2_apply] at h
      simpa [bil, Pi.single_apply] using h
    · have h := hx (Pi.single (Sum.inr 1) 1)
      rw [burnsideI23x_B2_apply] at h
      simpa [bil, Pi.single_apply] using h
    · have h := hx (Pi.single (Sum.inl 0) 1)
      rw [burnsideI23x_B2_apply] at h
      simpa [bil, Pi.single_apply] using h
    · have h := hx (Pi.single (Sum.inl 1) 1)
      rw [burnsideI23x_B2_apply] at h
      simpa [bil, Pi.single_apply] using h

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 in
theorem burnsideI23x_sd2_B (F : Type) [Field F] [CharP F 2] (x y : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_sd2 F).B x y = bil x y := rfl

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 in
theorem burnsideI23x_sd2_Q0 (F : Type) [Field F] [CharP F 2] (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_sd2 F).Q0 x = sp4Quad F x := rfl
open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_gram_of_bil {F : Type} [Field F] {M : Matrix Ix Ix F}
    (h : ∀ x y, bil (M *ᵥ x) (M *ᵥ y) = bil x y) : Mᵀ * spJ F * M = spJ F := by
  have hkey : ∀ (N : Matrix Ix Ix F) (x y : Ix → F),
      bil (N *ᵥ x) (N *ᵥ y) = (x ᵥ* (Nᵀ * spJ F * N)) ⬝ᵥ y := by
    intro N x y
    rw [bil_eq, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, ← Matrix.mul_assoc]
  have hkey1 : ∀ x y : Ix → F, bil x y = (x ᵥ* spJ F) ⬝ᵥ y := by
    intro x y
    rw [bil_eq, Matrix.dotProduct_mulVec]
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [hkey, hkey1] at h1
  simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h1

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_hsymp2 (F : Type) [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) (x y : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_sd2 F).B ((burnsideI23x_LM2 F).lin γ x) ((burnsideI23x_LM2 F).lin γ y) =
      (burnsideI23x_sd2 F).B x y := by
  have hγ : (γ : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F :=
    (burnsideI23x_sp_perfect hc0 hc1).le γ.2
  show bil (((γ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ x)
    (((γ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ y) = _
  exact bil_statedSp ⟨(γ : GL (Fin 2 ⊕ Fin 2) F), hγ⟩ x y

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_hfaith2 (F : Type) [Field F] (γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (h : ∀ x, (burnsideI23x_LM2 F).lin γ x = x) : γ = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  have h2 : (((γ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ (Pi.single j 1 : Fin 2 ⊕ Fin 2 → F)) i =
      (Pi.single j 1 : Fin 2 ⊕ Fin 2 → F) i := this
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  show (((γ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F)) i j = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j
  rw [Matrix.one_apply, h2]

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_hsurj2 (F : Type) [Field F] [Finite F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (M : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F))
    (hM : (burnsideI23x_sd2 F).Symp M) :
    ∃ γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆, ∀ x, (burnsideI23x_LM2 F).lin γ x = M x := by
  set Mat := LinearMap.toMatrix' (M : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F)) with hMat
  have hMx : ∀ x, M x = Mat *ᵥ x := fun x => by
    have := congrArg (fun f => f x)
      (Matrix.toLin'_toMatrix' (M : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F)))
    exact this.symm.trans (Matrix.toLin'_apply _ _)
  have hgram : Matᵀ * CFSG.Quasithin.Explicit.spJ F * Mat = CFSG.Quasithin.Explicit.spJ F := by
    apply burnsideI23x_gram_of_bil
    intro x y
    have := hM x y
    rw [hMx, hMx] at this
    exact this
  have hmem : (spUnit Mat hgram : GL (Fin 2 ⊕ Fin 2) F) ∈ ⁅StatedSp 2 F, StatedSp 2 F⁆ := by
    rw [burnsideI23x_sp_perfect hc0 hc1, statedSp_eq_sp4']
    exact hgram
  refine ⟨⟨spUnit Mat hgram, hmem⟩, fun x => ?_⟩
  rw [hMx]
  rfl
namespace burnsideI23x_SD

section Siegel

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N)

@[expose] def sieLin (u v : N) : N →ₗ[F] N where
  toFun z := z + S.B z u • v + S.B z v • u
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, add_smul]
    abel
  map_smul' c x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

theorem sieLin_apply (u v z : N) : S.sieLin u v z = z + S.B z u • v + S.B z v • u := rfl

theorem sieLin_invol {u v : N} (huv : S.B u v = 0) (z : N) :
    S.sieLin u v (S.sieLin u v z) = z := by
  have hvu : S.B v u = 0 := by rw [S.B_comm]; exact huv
  rw [sieLin_apply, sieLin_apply]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    huv, hvu, mul_zero, add_zero]
  have h2 := two_eq_zero_F (F := F)
  have e1 : z + S.B z u • v + S.B z v • u + S.B z u • v + S.B z v • u =
      z + ((2 : F) * S.B z u) • v + ((2 : F) * S.B z v) • u := by module
  rw [e1, h2]
  simp

@[expose] def sieEquiv {u v : N} (huv : S.B u v = 0) : N ≃ₗ[F] N :=
  LinearEquiv.ofInvolutive (S.sieLin u v) (fun z => S.sieLin_invol huv z)

theorem sieEquiv_apply {u v : N} (huv : S.B u v = 0) (z : N) :
    S.sieEquiv huv z = z + S.B z u • v + S.B z v • u := rfl

theorem sieEquiv_symp {u v : N} (huv : S.B u v = 0) : S.Symp (S.sieEquiv huv) := by
  intro x y
  have hvu : S.B v u = 0 := by rw [S.B_comm]; exact huv
  rw [sieEquiv_apply, sieEquiv_apply]
  have h1 := S.B_comm v y
  have h2 := S.B_comm u y
  have h3 := add_self_F (S.B y u * S.B x v)
  have h4 := add_self_F (S.B y v * S.B x u)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, S.alt,
    huv, hvu, mul_zero, add_zero, h1, h2]
  linear_combination h3 + h4

theorem exists_dual_pair {x u : N} (hu : u ≠ 0) (hx : ∀ a : F, x ≠ a • u) :
    ∃ v : N, S.B x v = 1 ∧ S.B u v = 0 := by
  obtain ⟨v₀, hv₀⟩ := S.exists_partner hu
  have hx' : x - S.B x v₀ • u ≠ 0 := fun h => hx (S.B x v₀) (sub_eq_zero.1 h)
  obtain ⟨w, hw⟩ := S.exists_partner hx'
  refine ⟨w - S.B u w • v₀, ?_, ?_⟩
  · have h1 : S.B (x - S.B x v₀ • u) w = 1 := hw
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1 ⊢
    linear_combination h1
  · simp only [map_sub, map_smul, smul_eq_mul, hv₀, mul_one, sub_self]

end Siegel

end burnsideI23x_SD

namespace burnsideI23x_SD

section IrredIso

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  [Finite N] (S : burnsideI23x_SD F N) {Γ : Type} (lin : Γ → N →ₗ[F] N)

theorem irred_isotropic (hsurj : ∀ M : N ≃ₗ[F] N, S.Symp M → ∃ γ, ∀ x, lin γ x = M x)
    {ℓ : AddSubgroup N} (hℓF : ∀ (a : F) (x : N), x ∈ ℓ → a • x ∈ ℓ)
    (hiso : ∀ x ∈ ℓ, ∀ y ∈ ℓ, S.B x y = 0) (hcard : Nat.card ℓ = Nat.card F ^ 2)
    (C : AddSubgroup N) (hC : C ≠ ⊥) (hCℓ : C ≤ ℓ)
    (hCinv : ∀ γ, (∀ x, lin γ x ∈ ℓ ↔ x ∈ ℓ) → ∀ x ∈ C, lin γ x ∈ C) : ℓ ≤ C := by
  classical
  obtain ⟨⟨x₀, hx₀C⟩, hx₀'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
  have hx₀ : x₀ ≠ 0 := fun h => hx₀' (Subtype.ext h)
  have hx₀ℓ : x₀ ∈ ℓ := hCℓ hx₀C
  have step1 : ∀ u ∈ ℓ, (∀ a : F, u ≠ a • x₀) → u ∈ C := by
    intro u huℓ hu
    have hu0 : u ≠ 0 := fun h => hu 0 (by rw [zero_smul]; exact h)
    have hx : ∀ a : F, x₀ ≠ a • u := by
      intro a ha
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hx₀ (by rw [ha, zero_smul])
      apply hu a⁻¹
      rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    obtain ⟨v, hv1, hv2⟩ := S.exists_dual_pair hu0 hx
    obtain ⟨γ, hγ⟩ := hsurj (S.sieEquiv hv2) (S.sieEquiv_symp hv2)
    have hE : ∀ x ∈ ℓ, lin γ x ∈ ℓ := by
      intro x hx
      rw [hγ, S.sieEquiv_apply, hiso x hx u huℓ, zero_smul, add_zero]
      exact ℓ.add_mem hx (hℓF _ _ huℓ)
    have hstab : ∀ x, lin γ x ∈ ℓ ↔ x ∈ ℓ := by
      intro x
      refine ⟨fun h => ?_, hE x⟩
      have h2 := hE _ h
      rw [hγ, hγ] at h2
      have := S.sieLin_invol hv2 x
      show x ∈ ℓ
      have h3 : S.sieEquiv hv2 (S.sieEquiv hv2 x) = x := this
      rwa [h3] at h2
    have h1 := hCinv γ hstab x₀ hx₀C
    rw [hγ, S.sieEquiv_apply, hiso x₀ hx₀ℓ u huℓ, zero_smul, add_zero, hv1, one_smul] at h1
    have h5 := C.sub_mem h1 hx₀C
    simpa using h5
  have hex : ∃ y ∈ ℓ, ∀ a : F, y ≠ a • x₀ := by
    by_contra hcon
    have hall : ∀ y ∈ ℓ, ∃ a : F, y = a • x₀ := by
      intro y hy
      by_contra hna
      apply hcon
      exact ⟨y, hy, fun a ha => hna ⟨a, ha⟩⟩
    have hle : ℓ ≤ (Submodule.span F {x₀}).toAddSubgroup := by
      intro y hy
      obtain ⟨a, rfl⟩ := hall y hy
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x₀)
    have h1 := AddSubgroup.card_le_of_le hle
    have h2 : Nat.card (Submodule.span F {x₀}) = Nat.card F :=
      (Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton F N x₀ hx₀).toEquiv).symm
    have h3 : Nat.card (Submodule.span F {x₀}).toAddSubgroup = Nat.card F := h2
    rw [hcard, h3] at h1
    have h4 : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  intro z hz
  by_cases hdep : ∃ a : F, z = a • x₀
  · obtain ⟨a, rfl⟩ := hdep
    obtain ⟨y, hyℓ, hy⟩ := hex
    have hyC : y ∈ C := step1 y hyℓ hy
    have hsum : a • x₀ + y ∈ C := step1 _ (ℓ.add_mem hz hyℓ) (fun b hb => hy (b - a) (by
      have : y = b • x₀ - a • x₀ := by rw [← hb]; abel
      rw [this, sub_smul]))
    have h5 := C.sub_mem hsum hyC
    simpa using h5
  · exact step1 z hz (fun a ha => hdep ⟨a, ha⟩)

end IrredIso

end burnsideI23x_SD
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_plane_isotropic {m n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {M : Type} [AddCommGroup M] [Module F M] [Finite M]
    {LM : LinModel (i23NaturalModel m F) F M} (S : burnsideI23x_SD F M)
    (hsymp : ∀ γ x y, S.B (LM.lin γ x) (LM.lin γ y) = S.B x y)
    (hcomm : ∀ T : M →+ M, (∀ (γ : (i23NaturalModel m F).Gam) (x : M),
      T (LM.lin γ x) = LM.lin γ (T x)) → ∃ c : F, ∀ x, T x = c • x)
    (hF : Nat.card F = 2 ^ n) (hMcard : Nat.card M = Nat.card F ^ 4)
    {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {L T : Subgroup (MulAut U)} {K : Subgroup U}
    {marking : (i23NaturalModel m F).Gam →* ↥L}
    {β : U →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (hsec : I23SectionMap (i23NaturalModel m F) L K marking β)
    {U2 : Subgroup U} (hK : K ≤ U2)
    (hflag2 : ∀ U', IsFlagW L (T ⊓ L) K (2 ^ n) 2 U' → U' = U2)
    (hP2 : ∀ x ∈ T ⊓ L, x ∈ stabW U2)
    (hU2F : ∀ (a : F) (x : M), x ∈ (burnsideI23x_isCoord LM hsec).img U2 →
      a • x ∈ (burnsideI23x_isCoord LM hsec).img U2)
    (hU2c : Nat.card ((burnsideI23x_isCoord LM hsec).img U2) = (2 ^ n) ^ 2) :
    ∀ x ∈ (burnsideI23x_isCoord LM hsec).img U2, ∀ y ∈ (burnsideI23x_isCoord LM hsec).img U2,
      S.B x y = 0 := by
  classical
  have hf := burnsideI23x_isCoord LM hsec
  set ℓ := hf.img U2 with hℓ
  let Wsub : Submodule F M :=
    { carrier := ℓ
      add_mem' := ℓ.add_mem
      zero_mem' := ℓ.zero_mem
      smul_mem' := fun c x hx => hU2F c x hx }
  haveI : FiniteDimensional F M := Module.Finite.of_finite
  have hnd := S.nondegenerate
  have hF2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hfrM : Module.finrank F M = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := M)
    rw [hMcard] at h
    exact (Nat.pow_right_injective hF2 h).symm
  have hfrW : Module.finrank F Wsub = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := Wsub)
    have h2 : Nat.card Wsub = Nat.card ℓ := rfl
    rw [h2, hU2c, hF, ← hF] at h
    exact (Nat.pow_right_injective hF2 h).symm
  let Bf : LinearMap.BilinForm F M := S.B
  let horth : Submodule F M := Bf.orthogonal Wsub
  have hmemh : ∀ y, y ∈ horth ↔ ∀ z ∈ ℓ, S.B z y = 0 := fun y =>
    LinearMap.BilinForm.mem_orthogonal_iff
  have hfrO : Module.finrank F horth = 2 := by
    have h := LinearMap.BilinForm.finrank_orthogonal (B := Bf) hnd Wsub
    rw [hfrM, hfrW] at h
    exact h
  have hcardO : Nat.card horth = (2 ^ n) ^ 2 := by
    have h := Module.natCard_eq_pow_finrank (K := F) (V := horth)
    rw [hfrO, hF] at h
    exact h
  let ℓ' : AddSubgroup M := horth.toAddSubgroup
  have hℓ' : ∀ y, y ∈ ℓ' ↔ ∀ z ∈ ℓ, S.B z y = 0 := hmemh
  have hflag : IsFlagW L (T ⊓ L) K (2 ^ n) 2 (hf.pre ℓ') := by
    refine ⟨hf.le_pre ℓ', ?_, ?_, ?_⟩
    · rw [hf.endStableW_iff hU hcomm (hf.le_pre ℓ'), hf.img_pre]
      intro c x hx
      exact horth.smul_mem c hx
    · rw [← hf.card_img, hf.img_pre]
      exact hcardO
    · intro x hx
      obtain ⟨γ, hγ⟩ := hf.onto ⟨x, hx.2⟩
      have hγx : (marking γ : MulAut U) = x := congrArg Subtype.val hγ
      have hstab2 : ∀ γ' : (i23NaturalModel m F).Gam, (marking γ' : MulAut U) ∈ T ⊓ L →
          ∀ y, y ∈ ℓ ↔ LM.lin γ' y ∈ ℓ := by
        intro γ' hγ' y
        have := (hf.mem_stabW_iff hK γ').1 (hP2 _ hγ')
        exact this y
      have hxi : (marking γ⁻¹ : MulAut U) ∈ T ⊓ L := by
        have h1 : (marking γ⁻¹ : MulAut U) = ((marking γ : MulAut U))⁻¹ := by
          rw [map_inv]; rfl
        rw [h1, hγx]
        exact (T ⊓ L).inv_mem hx
      rw [← hγx, hf.mem_stabW_iff (hf.le_pre ℓ') γ, hf.img_pre]
      intro y
      rw [hℓ', hℓ']
      constructor
      · intro hy z hz
        have hz' : LM.lin γ⁻¹ z ∈ ℓ := (hstab2 γ⁻¹ hxi z).1 hz
        have hzz : LM.lin γ (LM.lin γ⁻¹ z) = z := by
          rw [← burnsideI23x_lin_mul LM hf, mul_inv_cancel, burnsideI23x_lin_one LM hf]
        have := hy _ hz'
        rw [← hsymp γ, hzz] at this
        exact this
      · intro hy z hz
        have := hy (LM.lin γ z) ((hstab2 γ (by rw [hγx]; exact hx) z).1 hz)
        rwa [hsymp] at this
  have h5 := hflag2 _ hflag
  intro x hx y hy
  have hy' : y ∈ hf.img (hf.pre ℓ') := by rw [h5]; exact hy
  rw [hf.img_pre] at hy'
  exact (hℓ' y).1 hy' x hx
open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_marked_flags_m2' {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel 2 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 2 F).sec ⧸
      (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec}
    (h : I23SectionMap (i23NaturalModel 2 F) L W0 π β) (hW0 : W0 ≤ fixV L)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0)
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) :
    ∃ V1 V2 : Subgroup V, IsI23MarkedSubspace 2 n 1 F T W0 V1 β ∧
      IsI23MarkedSubspace 2 n 2 F T W0 V2 β ∧ V1 ≤ V2 ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 2 n 1 F T W0 U β → U = V1) ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 2 n 2 F T W0 U β → U = V2) ∧
      (∀ U, CFSG.Quasithin.Vol2.Ch11.SecA.IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U → U = V1) ∧
      (∀ U, CFSG.Quasithin.Vol2.Ch11.SecA.IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 U → U = V2) := by
  have hchar : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hF
  have hperf := burnsideI23x_sp_perfect hc0 hc1
  have hR := burnsideI23x_realizesVia h hW0
  obtain ⟨π', hπ'⟩ := burnsideI23x_realizes_nat_congr hperf (π := π) hR
  have hflag := factFlagSp4_holds F n hn hF V hV L W0 π' hπ' (T ⊓ L) hP
  refine burnsideI23x_marked_flags' (burnsideI23x_scalarAgree2 F) hV h
    (fun T' hT' => commutant_statedSp T' (fun γ x => ?_)) hTL hTW0 (burnsideI23x_flag12_of_unique hflag)
  exact hT' ⟨(γ : GL (Fin 2 ⊕ Fin 2) F), hperf.ge γ.2⟩ x

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in
theorem burnsideI23x_marked_flags_m3' {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel 3 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 3 F).sec ⧸
      (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec}
    (h : I23SectionMap (i23NaturalModel 3 F) L W0 π β) (hW0 : W0 ≤ fixV L)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) (hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0)
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) :
    ∃ V1 V2 : Subgroup V, IsI23MarkedSubspace 3 n 1 F T W0 V1 β ∧
      IsI23MarkedSubspace 3 n 2 F T W0 V2 β ∧ V1 ≤ V2 ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 3 n 1 F T W0 U β → U = V1) ∧
      (∀ U : Subgroup V, IsI23MarkedSubspace 3 n 2 F T W0 U β → U = V2) ∧
      (∀ U, CFSG.Quasithin.Vol2.Ch11.SecA.IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U → U = V1) ∧
      (∀ U, CFSG.Quasithin.Vol2.Ch11.SecA.IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 U → U = V2) := by
  have hchar : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hF
  have hflag := factFlagG2_holds F n hn hF V hV L W0 π (burnsideI23x_realizesVia h hW0)
    (T ⊓ L) hP
  exact burnsideI23x_marked_flags' (burnsideI23x_scalarAgree3 F) hV h
    (fun T hT => commutant_g2Derived hc0 hc1 _ T hT) hTL hTW0 (burnsideI23x_flag12_of_unique hflag)
open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_hbound2 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ n) {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut V)) (W0 : Subgroup V)
        (π : (i23NaturalModel 2 F).Gam →* ↥L),
        (i23NaturalModel 2 F).RealizesVia L ⊤ W0 π → W0 = fixV L → commV L = ⊤ →
        Nat.card W0 ≤ Nat.card F := by
  intro V _ _ hV L W0 π hreal hW0 hcomm
  subst hW0
  have hcommOf : XMod.commOf ↥L (⊤ : Subgroup V) = ⊤ := by
    rw [CFSG.Quasithin.MS93.xmodCommOf_top_eq]
    exact hcomm
  obtain ⟨π', hπ'⟩ := burnsideI23x_realizes_nat_congr (burnsideI23x_sp_perfect hc0 hc1)
    (π := π) hreal
  have hreal' : (FFModel.nat (StatedSp 2 F)).Realizes L ⊤ (fixV L ⊓ ⊤) := by
    rw [inf_top_eq]
    exact ⟨π', hπ'⟩
  have := CFSG.Quasithin.B513N.card_fixV_le_of_sp4 hV L ⊤ (fun x _ v _ => Subgroup.mem_top _)
    hcommOf hn hF hreal'
  rw [inf_top_eq, ← hF] at this
  exact this

theorem burnsideI23x_card_Ix {F : Type} [Field F] [Finite F] :
    Nat.card (Fin 2 ⊕ Fin 2 → F) = Nat.card F ^ 4 := by
  rw [Nat.card_fun, Nat.card_sum, Nat.card_fin]

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_UCg_two {n : ℕ} (hn : 2 ≤ n) : burnsideI23x_UCg 2 n := by
  intro F _ _ hF U _ _ hU G L T K hLG hnorm hGT hT hGK huniv marking β hsec U1 U2 h1 h2
  haveI : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  haveI : Finite (MulAut U) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hS := burnsideI23x_scalarAgree2 F
  obtain ⟨a, ha0, ha1⟩ := burnsideI23x_exists_ne_zero_one hF hn
  have hsurjLin : ∀ M : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F),
      (burnsideI23x_sd2 F).Symp M → ∃ γ, ∀ x, (burnsideI23x_LM2 F).lin γ x = M x :=
    fun M hM => burnsideI23x_hsurj2 F ha0 ha1 M hM
  have htv' : ∀ (e : Fin 2 ⊕ Fin 2 → F) (c : F), e ≠ 0 → ∃ γ, ∀ x,
      (burnsideI23x_LM2 F).lin γ x = (burnsideI23x_sd2 F).tvEquiv e c x := fun e c _ =>
    hsurjLin _ ((burnsideI23x_sd2 F).tvEquiv_symp e c)
  have hgenM := burnsideI23x_SD.genW'_of_tv (burnsideI23x_sd2 F) (burnsideI23x_LM2 F).lin htv'
    ha0 ha1
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM2 F) (burnsideI23x_sd2 F) (burnsideI23x_hsymp2 F ha0 ha1)
    (burnsideI23x_hfaith2 F) hgenM (burnsideI23x_hbound2 hn hF ha0 ha1) hU huniv hsec
  have hEndLin := burnsideI23x_SD.hEnd_of_tv (burnsideI23x_sd2 F) (burnsideI23x_LM2 F).lin htv'
  have hEnd : ∀ φ : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x := fun φ hφ =>
    hEndLin φ (fun γ x => by simpa only [hAlin] using hφ γ x)
  have hf := burnsideI23x_isCoord (burnsideI23x_LM2 F) hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  obtain ⟨hU2i, hU2F, hU2c⟩ := burnsideI23x_marked_ell hS hsec h2
  have hU1' : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hU2' : ∀ u, u ∈ U2 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U2 := fun u => by
    rw [hψfst]; exact hU2i u
  have hcard1 : Nat.card (hf.img U1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img U1) hU1F hcard1
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht => hnorm t (hTG ht)
  have hTW0 : ∀ t ∈ T, ∀ w ∈ K, t w ∈ K := fun t ht => hGK t (hTG ht)
  obtain ⟨V1', V2', m1', m2', -, um1, um2, f1, f2⟩ :=
    burnsideI23x_marked_flags_m2' hn hF hU hsec huniv.1 hTL hTW0 hP
  have hU2eq : U2 = V2' := um2 U2 h2
  have hflag2 : ∀ U', IsFlagW L (T ⊓ L) K (2 ^ n) 2 U' → U' = U2 := fun U' hU' =>
    (f2 U' hU').trans hU2eq.symm
  have hfl2 : IsFlagW L (T ⊓ L) K (2 ^ n) 2 U2 :=
    burnsideI23x_marked_imp_flag hS hU hsec
      (fun T' hT' => hEndLin T' hT') h2
  have hiso := burnsideI23x_plane_isotropic (m := 2) (n := n) (LM := burnsideI23x_LM2 F)
    (burnsideI23x_sd2 F) (burnsideI23x_hsymp2 F ha0 ha1) hEndLin hF burnsideI23x_card_Ix hU hsec h2.1 hflag2 hfl2.2.2.2 hU2F hU2c
  have hcardF2 : Nat.card (hf.img U2) = Nat.card F ^ 2 := by rw [hU2c, hF]
  have hirr1 : ∀ C : AddSubgroup (Fin 2 ⊕ Fin 2 → F), C ≠ ⊥ → C ≤ hf.img U1 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U1 ↔ x ∈ hf.img U1) → ∀ x ∈ C, A γ x ∈ C) → hf.img U1 ≤ C :=
    fun C hC hCℓ hCinv => (burnsideI23x_sd2 F).irred_line (burnsideI23x_LM2 F).lin hsurjLin he₀
      hℓ₁ C hC hCℓ (fun γ hγ x hx => by
        have := hCinv γ (fun y => by simpa only [hAlin] using hγ y) x hx
        simpa only [hAlin] using this)
  have hirr2 : ∀ C : AddSubgroup (Fin 2 ⊕ Fin 2 → F), C ≠ ⊥ → C ≤ hf.img U2 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U2 ↔ x ∈ hf.img U2) → ∀ x ∈ C, A γ x ∈ C) → hf.img U2 ≤ C :=
    fun C hC hCℓ hCinv => (burnsideI23x_sd2 F).irred_isotropic (burnsideI23x_LM2 F).lin
      hsurjLin hU2F hiso hcardF2 C hC hCℓ (fun γ hγ x hx => by
        have := hCinv γ (fun y => by simpa only [hAlin] using hγ y) x hx
        simpa only [hAlin] using this)
  have he₀ℓ : e₀ ∈ hf.img U1 := (hℓ₁ e₀).2 ⟨1, (one_smul F e₀).symm⟩
  have hψK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0 := fun u => by
    rw [hψfst]
    exact (hf.ker u).symm
  have htvA : ∀ c : F, ∃ γ, ∀ x, A γ x = (burnsideI23x_sd2 F).tvEquiv e₀ c x := fun c => by
    obtain ⟨γ, hγ⟩ := hsurjLin _ ((burnsideI23x_sd2 F).tvEquiv_symp e₀ c)
    exact ⟨γ, fun x => (hAlin γ x).trans (hγ x)⟩
  have he₂ : ∃ e₂ ∈ hf.img U2, e₂ ≠ 0 := by
    have hlt : 1 < Nat.card (hf.img U2) := by
      rw [hcardF2]
      have : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    haveI : Nontrivial (hf.img U2) := Finite.one_lt_card_iff_nontrivial.1 hlt
    obtain ⟨⟨e₂, he₂⟩, hne⟩ := exists_ne (0 : hf.img U2)
    exact ⟨e₂, he₂, fun h => hne (Subtype.ext h)⟩
  obtain ⟨e₂, he₂ℓ, he₂0⟩ := he₂
  refine ⟨?_, ⟨?_, ?_⟩, fun hn' _ => ?_⟩
  · exact burnsideI23x_SD.exists_T_fixed ψ marking hπs hψact hEnd hgenW hTG hnorm hT2 he₀ hℓ₁
      hU1' (fun t ht u hu => h1.2.1 t ht u hu)
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU1F hU1' he₀ℓ he₀
      hirr1
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU2F hU2' he₂ℓ
      he₂0 hirr2
  · exact burnsideI23x_SD.root_generation ψ marking hπs hψact hψK he₀ hℓ₁ hU1' ha0 ha1 htvA
@[expose] noncomputable def burnsideI23x_kappa2 (F : Type) [Field F] :
    ((Fin 2 ⊕ Fin 2 → F) × F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 ⊕ Unit → F) where
  toFun w := fun i => match i with
    | Sum.inl j => w.1 (Sum.inl j)
    | Sum.inr (Sum.inl j) => w.1 (Sum.inr j)
    | Sum.inr (Sum.inr _) => w.2
  invFun v := (fun i => match i with
    | Sum.inl j => v (Sum.inl j)
    | Sum.inr j => v (Sum.inr (Sum.inl j)), v (Sum.inr (Sum.inr ())))
  map_add' w w' := by
    funext i
    rcases i with i | i | i <;> simp
  map_smul' c w := by
    funext i
    rcases i with i | i | i <;> simp
  left_inv w := by
    refine Prod.ext ?_ rfl
    funext i
    rcases i with i | i <;> rfl
  right_inv v := by
    funext i
    rcases i with i | i | i
    · rfl
    · rfl
    · rfl

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 in
theorem burnsideI23x_kappa2_Q (F : Type) [Field F] [CharP F 2] (w : (Fin 2 ⊕ Fin 2 → F) × F) :
    StatedQuadOdd 2 F (burnsideI23x_kappa2 F w) = (burnsideI23x_sd2 F).Qw w := by
  show _ = (burnsideI23x_sd2 F).Q0 w.1 + w.2 ^ 2
  rw [burnsideI23x_sd2_Q0]
  show ∑ i : Fin 2, w.1 (Sum.inl i) * w.1 (Sum.inr i) + w.2 ^ 2 = sp4Quad F w.1 + w.2 ^ 2
  simp [Fin.sum_univ_two, sp4Quad]

theorem burnsideI23x_top_perfect_of_perfect {X : Type*} [Group X] {H : Subgroup X}
    (h : ⁅H, H⁆ = H) : ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ = (⊤ : Subgroup ↥H) := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator]
  have htop : Subgroup.map H.subtype (⊤ : Subgroup ↥H) = H := by
    rw [← MonoidHom.range_eq_map]
    exact H.range_subtype
  rw [htop, h]

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_part1_m2 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 2 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 2 F).sec ⧸
      (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec}
    (hsec : I23SectionMap (i23NaturalModel 2 F) L W0 marking β)
    (hT2 : IsPGroup 2 T) {V1 : Subgroup V} (h1 : IsI23MarkedSubspace 2 n 1 F T W0 V1 β)
    (hflag1 : ∀ U', IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U' → U' = V1)
    (S' : Subgroup (MulAut V)) (V2 : Subgroup V) (huniv : IsUniversalCovering L W0) :
    ∃ (ψ : V ≃* Multiplicative (Fin 2 ⊕ Fin 2 ⊕ Unit → F))
      (π : ↥(StatedOmega (StatedQuadOdd 2 F)) →* ↥L),
      Function.Surjective π ∧
      (∀ (γ : ↥(StatedOmega (StatedQuadOdd 2 F))) (v : V), ψ ((π γ : MulAut V) v) =
        Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2 ⊕ Unit) F) :
          Matrix (Fin 2 ⊕ Fin 2 ⊕ Unit) (Fin 2 ⊕ Fin 2 ⊕ Unit) F).mulVec
            (Multiplicative.toAdd (ψ v)))) ∧
      I23ScalarCompatibility 2 F ψ β ∧
      OrthConclMarked (StatedQuadOdd 2 F) 2 n ψ L T (i23TransvectionRoot L W0 V1) S' V1 V2 := by
  haveI : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have hS := burnsideI23x_scalarAgree2 F
  obtain ⟨a, ha0, ha1⟩ := burnsideI23x_exists_ne_zero_one hF hn
  have hsurjLin : ∀ M : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F),
      (burnsideI23x_sd2 F).Symp M → ∃ γ, ∀ x, (burnsideI23x_LM2 F).lin γ x = M x :=
    fun M hM => burnsideI23x_hsurj2 F ha0 ha1 M hM
  have htv' : ∀ (e : Fin 2 ⊕ Fin 2 → F) (c : F), e ≠ 0 → ∃ γ, ∀ x,
      (burnsideI23x_LM2 F).lin γ x = (burnsideI23x_sd2 F).tvEquiv e c x := fun e c _ =>
    hsurjLin _ ((burnsideI23x_sd2 F).tvEquiv_symp e c)
  have hgenM := burnsideI23x_SD.genW'_of_tv (burnsideI23x_sd2 F) (burnsideI23x_LM2 F).lin htv'
    ha0 ha1
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM2 F) (burnsideI23x_sd2 F) (burnsideI23x_hsymp2 F ha0 ha1)
    (burnsideI23x_hfaith2 F) hgenM (burnsideI23x_hbound2 hn hF ha0 ha1) hV huniv hsec
  have hEndLin := burnsideI23x_SD.hEnd_of_tv (burnsideI23x_sd2 F) (burnsideI23x_LM2 F).lin htv'
  have hsurj : ∀ M : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F),
      (burnsideI23x_sd2 F).Symp M → ∃ γ, ∀ x, A γ x = M x := fun M hM => by
    obtain ⟨γ, hγ⟩ := hsurjLin M hM
    exact ⟨γ, fun x => (hAlin γ x).trans (hγ x)⟩
  have hfaith : ∀ γ, (∀ x, A γ x = x) → γ = 1 := fun γ h =>
    burnsideI23x_hfaith2 F γ (fun x => (hAlin γ x).symm.trans (h x))
  have hf := burnsideI23x_isCoord (burnsideI23x_LM2 F) hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  have hU1' : ∀ u, u ∈ V1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img V1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hcard1 : Nat.card (hf.img V1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img V1) hU1F hcard1
  have hψK : ∀ u, u ∈ W0 ↔ (Multiplicative.toAdd (ψ u)).1 = 0 := fun u => by
    rw [hψfst]
    exact (hf.ker u).symm
  have htvA : ∀ c : F, ∃ γ, ∀ x, A γ x = (burnsideI23x_sd2 F).tvEquiv e₀ c x := fun c => by
    obtain ⟨γ, hγ⟩ := hsurjLin _ ((burnsideI23x_sd2 F).tvEquiv_symp e₀ c)
    exact ⟨γ, fun x => (hAlin γ x).trans (hγ x)⟩
  have hroot := burnsideI23x_SD.root_generation ψ marking hπs hψact hψK he₀ hℓ₁ hU1' ha0 ha1 htvA
  have hfixP : V1 = fixV (T ⊓ L) :=
    le_antisymm (burnsideI23x_SD.line_le_fixV_P ψ marking hπs hψact hT2 he₀ hℓ₁ hU1' h1.2.1)
      (burnsideI23x_fixV_P_le hEndLin hF hV hsec huniv.1 h1.1 hflag1)
  have hOrth := burnsideI23x_SD.orthConclMarked_tv (m := 2) (n := n) (Or.inr rfl) hn hF
    (StatedQuadOdd 2 F) (burnsideI23x_kappa2 F) (burnsideI23x_kappa2_Q F) ψ marking hπs hψact
    hψK hfixV he₀ hℓ₁ hU1' hfixP hroot S' (U2 := V2)
  have hperf : ⁅(⊤ : Subgroup ↥⁅StatedSp 2 F, StatedSp 2 F⁆),
      (⊤ : Subgroup ↥⁅StatedSp 2 F, StatedSp 2 F⁆)⁆ = ⊤ :=
    burnsideI23x_top_perfect_of_perfect (by
      have h := burnsideI23x_sp_perfect ha0 ha1
      rw [h, h])
  have hrange := burnsideI23x_SD.phiHom_range (burnsideI23x_kappa2 F) (StatedQuadOdd 2 F)
    (burnsideI23x_kappa2_Q F) hsurj hperf
    (S := burnsideI23x_sd2 F) (A := A) (hA := hA)
  obtain ⟨π, hπsurj, hπΩ⟩ := burnsideI23x_SD.exists_piOmega (burnsideI23x_kappa2 F)
    (StatedOmega (StatedQuadOdd 2 F)) hrange hfaith marking hπs
  refine ⟨burnsideI23x_SD.psiTrans ψ (burnsideI23x_kappa2 F), π, hπsurj, ?_,
    burnsideI23x_scalarCompat hS hψfst (burnsideI23x_kappa2 F), hOrth⟩
  intro A' v
  obtain ⟨γ, hπγ, hAγ⟩ := hπΩ A'
  rw [hπγ, hAγ]
  show Multiplicative.ofAdd (burnsideI23x_kappa2 F (Multiplicative.toAdd (ψ ((marking γ : MulAut V) v)))) = _
  rw [hψact]
  rw [burnsideI23x_SD.toAdd_psiTrans, burnsideI23x_SD.phiHom_mulVec]
  rfl
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_case_m2 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    (hL : L = quasithinGenFitting G) (hGT : G = L ⊔ T) (hT : IsSylowTwoOf T G)
    (hGW0 : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) (hW0 : W0 ≤ fixV L) (hcomm : commV L = ⊤)
    (marking : (i23NaturalModel 2 F).Gam →* ↥L)
    (β : V →* ↥(i23NaturalModel 2 F).sec ⧸
      (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec)
    (hsec : I23SectionMap (i23NaturalModel 2 F) L W0 marking β) :
    burnsideI23x_Concl 2 n F V G L T W0 marking β := by
  haveI : Finite (MulAut V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  haveI : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  obtain ⟨c₀, hc0, hc1⟩ := burnsideI23x_exists_ne_zero_one hF hn
  have hLG : L ≤ G := by rw [hL]; exact CFSG.Quasithin.quasithinGenFitting_le G
  have hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have h := CFSG.Quasithin.le_normalizer_quasithinGenFitting G hg
    rw [← hL] at h
    exact (Subgroup.mem_normalizer_iff.1 h l).1 hl
  have hTG : T ≤ G := hT.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht => hnorm t (hTG ht)
  have hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0 := fun t ht => hGW0 t (hTG ht)
  obtain ⟨V1, V2, h1, h2, h12, u1, u2, f1, f2⟩ :=
    burnsideI23x_marked_flags_m2' hn hF hV hsec hW0 hTL hTW0 hP
  have hfixV : fixV L = W0 :=
    burnsideI23x_fixV_eq (burnsideI23x_LM2 F) hsec hW0 (burnsideI23x_nofix2 F hc0 hc1)
  obtain ⟨t1, t2, t3⟩ := burnsideI23x_transfer (burnsideI23x_UCg_two hn) hF hV hLG hnorm hGT hT
    hGW0 hW0 hfixV hcomm hsec h1 h2
  refine ⟨V1, V2, h1, h2, u1, u2, ?_⟩
  intro R
  refine ⟨⊥, fun h => absurd h (by norm_num), fun h => absurd h.2 (by omega),
    fun huniv => ⟨fun _ => burnsideI23x_part1_m2 hn hF hV hsec hT.2.1 h1 f1 ⊥ V2 huniv,
      fun h3 => absurd h3 (by norm_num)⟩,
    ⟨t1, (burnsideI23x_centralCoreCompatibility V hV G V1).2 t2.1,
      (burnsideI23x_centralCoreCompatibility V hV G V2).2 t2.2⟩,
    fun hn' => ⟨by rw [hfixV]; exact h1.1, fun _ => t3 hn' (by norm_num)⟩⟩
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 in
@[expose] noncomputable def burnsideI23x_sd3 (F : Type) [Field F] [CharP F 2] :
    burnsideI23x_SD F (Ix3 → F) :=
  burnsideI23x_hypSD (F := F) (Fin 3)

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_sd3_B (F : Type) [Field F] [CharP F 2] (x y : Ix3 → F) :
    (burnsideI23x_sd3 F).B x y = polarQ x y := by
  show burnsideI23x_hypB (F := F) (Fin 3) x y = _
  rw [burnsideI23x_hypB_apply]
  simp only [Fin.sum_univ_three, polarQ]
  ring

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_sd3_Q0 (F : Type) [Field F] [CharP F 2] (x : Ix3 → F) :
    (burnsideI23x_sd3 F).Q0 x = normQ x := by
  show ∑ i : Fin 3, x (Sum.inl i) * x (Sum.inr i) = _
  simp only [Fin.sum_univ_three, normQ]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 in
@[expose] def burnsideI23x_toCayley {F : Type} [Field F] [CharP F 2]
    (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) : ↥(cayleyGroup F) :=
  ⟨(γ : quasithinZorn F ≃ₗ[F] quasithinZorn F), g2Derived_le γ.2⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_lin3_apply (F : Type) [Field F] [CharP F 2]
    (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F) :
    (burnsideI23x_LM3 F).lin γ x = g2Act (burnsideI23x_toCayley γ) x := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_hsymp3 (F : Type) [Field F] [CharP F 2]
    (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x y : Ix3 → F) :
    (burnsideI23x_sd3 F).B ((burnsideI23x_LM3 F).lin γ x) ((burnsideI23x_LM3 F).lin γ y) =
      (burnsideI23x_sd3 F).B x y := by
  rw [burnsideI23x_sd3_B, burnsideI23x_sd3_B, burnsideI23x_lin3_apply, burnsideI23x_lin3_apply]
  exact polarQ_g2Act _ x y

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_hfaith3 (F : Type) [Field F] [CharP F 2]
    (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (h : ∀ x, (burnsideI23x_LM3 F).lin γ x = x) :
    γ = 1 := by
  have h1 : burnsideI23x_toCayley γ = 1 := cayley_eq_one fun w => by
    rw [← burnsideI23x_lin3_apply]
    exact h w
  apply Subtype.ext
  have h2 := congrArg (fun g : ↥(cayleyGroup F) => (g : quasithinZorn F ≃ₗ[F] quasithinZorn F)) h1
  exact h2

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_hEnd3 (F : Type) [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (T : (Ix3 → F) →+ (Ix3 → F))
    (hT : ∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
      T ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (T x)) :
    ∃ c : F, ∀ x, T x = c • x :=
  commutant_g2Derived hc0 hc1 g2Derived_le T hT
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def burnsideI23x_kappa3 (F : Type) [Field F] [CharP F 2] :
    ((Ix3 → F) × F) ≃ₗ[F] ↥(zornO0F F) where
  toFun w := ⟨zmk w.2 (w.1 (.inl 0)) (w.1 (.inl 1)) (w.1 (.inl 2)) (w.1 (.inr 0))
    (w.1 (.inr 1)) (w.1 (.inr 2)) w.2, by show w.2 + w.2 = 0; exact CharTwo.add_self_eq_zero _⟩
  map_add' w w' := by
    refine Subtype.ext ?_
    show zmk (w.2 + w'.2) ((w.1 + w'.1) (.inl 0)) ((w.1 + w'.1) (.inl 1)) ((w.1 + w'.1) (.inl 2))
      ((w.1 + w'.1) (.inr 0)) ((w.1 + w'.1) (.inr 1)) ((w.1 + w'.1) (.inr 2)) (w.2 + w'.2) =
      zmk w.2 (w.1 (.inl 0)) (w.1 (.inl 1)) (w.1 (.inl 2)) (w.1 (.inr 0)) (w.1 (.inr 1))
        (w.1 (.inr 2)) w.2 + zmk w'.2 (w'.1 (.inl 0)) (w'.1 (.inl 1)) (w'.1 (.inl 2))
        (w'.1 (.inr 0)) (w'.1 (.inr 1)) (w'.1 (.inr 2)) w'.2
    rw [zmk_add]
    rfl
  map_smul' c w := by
    refine Subtype.ext ?_
    show zmk (c * w.2) ((c • w.1) (.inl 0)) ((c • w.1) (.inl 1)) ((c • w.1) (.inl 2))
      ((c • w.1) (.inr 0)) ((c • w.1) (.inr 1)) ((c • w.1) (.inr 2)) (c * w.2) =
      c • zmk w.2 (w.1 (.inl 0)) (w.1 (.inl 1)) (w.1 (.inl 2)) (w.1 (.inr 0)) (w.1 (.inr 1))
        (w.1 (.inr 2)) w.2
    rw [zmk_smul]
    rfl
  invFun y := (zP (y : quasithinZorn F), (y : quasithinZorn F).1)
  left_inv w := by
    refine Prod.ext ?_ rfl
    show zP (zmk w.2 (w.1 (.inl 0)) (w.1 (.inl 1)) (w.1 (.inl 2)) (w.1 (.inr 0))
      (w.1 (.inr 1)) (w.1 (.inr 2)) w.2) = w.1
    rw [zP_zmk]
    exact (q6_eta w.1).symm
  right_inv y := by
    refine Subtype.ext ?_
    obtain ⟨y, hy⟩ := y
    have hs : y.2.2.2 = y.1 := (CharTwo.add_eq_zero.1 hy).symm
    show zmk y.1 (zP y (.inl 0)) (zP y (.inl 1)) (zP y (.inl 2)) (zP y (.inr 0))
      (zP y (.inr 1)) (zP y (.inr 2)) y.1 = y
    conv_rhs => rw [zorn_eta y]
    rw [hs]
    rfl
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_kappa3_coe (F : Type) [Field F] [CharP F 2] (w : (Ix3 → F) × F) :
    ((burnsideI23x_kappa3 F w : ↥(zornO0F F)) : quasithinZorn F) =
      zI w.1 + w.2 • cayleyOne F := by
  show zmk w.2 (w.1 (.inl 0)) (w.1 (.inl 1)) (w.1 (.inl 2)) (w.1 (.inr 0))
    (w.1 (.inr 1)) (w.1 (.inr 2)) w.2 = _
  rw [cayleyOne_eq, zmk_smul, zI, zmk_add]
  apply zmk_congr <;> simp

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_kappa3_norm (F : Type) [Field F] [CharP F 2] (w : (Ix3 → F) × F) :
    CFSG.ASVolI.ChIJK.zornNorm F ((burnsideI23x_kappa3 F w : ↥(zornO0F F)) : quasithinZorn F) =
      (burnsideI23x_sd3 F).Qw w := by
  show w.2 * w.2 - ∑ i : Fin 3, ![w.1 (.inl 0), w.1 (.inl 1), w.1 (.inl 2)] i *
    ![w.1 (.inr 0), w.1 (.inr 1), w.1 (.inr 2)] i = (burnsideI23x_sd3 F).Q0 w.1 + w.2 ^ 2
  rw [burnsideI23x_sd3_Q0, CharTwo.sub_eq_add]
  simp only [Fin.sum_univ_three, normQ]
  simp
  ring

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_lf3 (F : Type) [Field F] [Finite F] [CharP F 2] (g : ↥(cayleyGroup F))
    (x : Ix3 → F) :
    burnsideI23x_sqrt F ((burnsideI23x_sd3 F).Q0 x + (burnsideI23x_sd3 F).Q0 (g2Act g x)) =
      (cgE g (zI x)).1 := by
  have h := normQ_g2Act g x
  have h2 : (burnsideI23x_sd3 F).Q0 x + (burnsideI23x_sd3 F).Q0 (g2Act g x) =
      ((cgE g (zI x)).1) ^ 2 := by
    rw [burnsideI23x_sd3_Q0, burnsideI23x_sd3_Q0]
    linear_combination -h + normQ (g2Act g x) * (CharTwo.two_eq_zero (R := F))
  rw [h2]
  exact burnsideI23x_sqrt_of_sq _
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_kappa3_lift (F : Type) [Field F] [Finite F] [CharP F 2]
    (A : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ((Ix3 → F) ≃ₗ[F] (Ix3 → F)))
    (hA : ∀ γ, (burnsideI23x_sd3 F).Symp (A γ))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM3 F).lin γ x)
    (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (w : (Ix3 → F) × F) :
    ((burnsideI23x_kappa3 F ((burnsideI23x_sd3 F).lift (hA γ) w) : ↥(zornO0F F)) :
        quasithinZorn F) =
      (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
        ((burnsideI23x_kappa3 F w : ↥(zornO0F F)) : quasithinZorn F) := by
  set g : ↥(cayleyGroup F) := burnsideI23x_toCayley γ with hg
  have hAg : ∀ x, A γ x = g2Act g x := fun x => (hAlin γ x).trans (burnsideI23x_lin3_apply F γ x)
  have hlf : (burnsideI23x_sd3 F).lf (A γ) w.1 = (cgE g (zI w.1)).1 := by
    unfold burnsideI23x_SD.lf
    rw [hAg]
    exact burnsideI23x_lf3 F g w.1
  rw [burnsideI23x_kappa3_coe, burnsideI23x_kappa3_coe]
  show zI (A γ w.1) + (w.2 + (burnsideI23x_sd3 F).lf (A γ) w.1) • cayleyOne F = _
  have h1 : (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) (zI w.1) = cgE g (zI w.1) := rfl
  have h2 : (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) (cayleyOne F) = cayleyOne F := cg_one g
  rw [map_add, map_smul, h1, h2, hlf, hAg, add_smul]
  conv_rhs => rw [g2_zI_eq g w.1]
  abel
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.MS93 in
theorem burnsideI23x_genW'3 (F : Type) [Field F] [Finite F] [CharP F 2] {c₀ : F} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) : (burnsideI23x_sd3 F).GenW' (burnsideI23x_LM3 F).lin := by
  classical
  intro w
  set C : AddSubgroup ((Ix3 → F) × F) := AddSubgroup.closure
    {y | ∃ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
      y = ((burnsideI23x_LM3 F).lin γ x - x, burnsideI23x_sqrt F ((burnsideI23x_sd3 F).Q0 x +
        (burnsideI23x_sd3 F).Q0 ((burnsideI23x_LM3 F).lin γ x)))} with hC
  let Θ : ((Ix3 → F) × F) →+ quasithinZorn F :=
    ((zornO0F F).subtype.comp (burnsideI23x_kappa3 F).toLinearMap).toAddMonoidHom
  have hΘ : ∀ w, Θ w = zI w.1 + w.2 • cayleyOne F := fun w => burnsideI23x_kappa3_coe F w
  have hΘinj : Function.Injective Θ := fun a b h =>
    (burnsideI23x_kappa3 F).injective (Subtype.ext h)
  have hA : ∀ a : quasithinZorn F, a.1 + a.2.2.2 = 0 → a ∈ AddSubgroup.closure
      {d | ∃ (γ : ↥(quasithinG2 F)) (y : quasithinZorn F), y.1 + y.2.2.2 = 0 ∧
        d = (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) y - y} := by
    intro a ha
    have hm := zornO0_gen_g2 (F := F) (Multiplicative.ofAdd a) ha
    have key : ∀ m ∈ Subgroup.closure {x | ∃ γ : ↥(quasithinG2 F), ∃ y ∈ zornO0 F,
        x = zornAct (quasithinG2 F) γ y * y⁻¹}, Multiplicative.toAdd m ∈ AddSubgroup.closure
      {d | ∃ (γ : ↥(quasithinG2 F)) (y : quasithinZorn F), y.1 + y.2.2.2 = 0 ∧
        d = (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) y - y} := by
      intro m hm
      induction hm using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨γ, y, hy, rfl⟩ := hx
        apply AddSubgroup.subset_closure
        refine ⟨γ, Multiplicative.toAdd y, hy, ?_⟩
        rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
        rfl
      | one => rw [toAdd_one]; exact AddSubgroup.zero_mem _
      | mul x y _ _ hx hy => rw [toAdd_mul]; exact AddSubgroup.add_mem _ hx hy
      | inv x _ hx => rw [toAdd_inv]; exact AddSubgroup.neg_mem _ hx
    exact key _ hm
  have hB : AddSubgroup.closure
      {d | ∃ (γ : ↥(quasithinG2 F)) (y : quasithinZorn F), y.1 + y.2.2.2 = 0 ∧
        d = (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) y - y} ≤ C.map Θ := by
    rw [AddSubgroup.closure_le]
    rintro d ⟨γ, y, hy, rfl⟩
    have hγ : (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
      rw [g2Derived_eq hc0 hc1, ← CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
      exact γ.2
    set γ' : ↥⁅quasithinG2 F, quasithinG2 F⁆ := ⟨(γ : quasithinZorn F ≃ₗ[F] quasithinZorn F), hγ⟩
      with hγ'
    set g : ↥(cayleyGroup F) := burnsideI23x_toCayley γ' with hg
    set x₀ : Ix3 → F := zP y with hx₀
    have hytr : cayleyTr y = 0 := hy
    have hyeq : y = zI x₀ + y.1 • cayleyOne F := trace_zero_eq hytr
    have h1 : (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) (zI x₀) = cgE g (zI x₀) := rfl
    have h2 : (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) (cayleyOne F) = cayleyOne F := cg_one g
    refine ⟨((burnsideI23x_LM3 F).lin γ' x₀ - x₀, burnsideI23x_sqrt F
      ((burnsideI23x_sd3 F).Q0 x₀ + (burnsideI23x_sd3 F).Q0 ((burnsideI23x_LM3 F).lin γ' x₀))),
      AddSubgroup.subset_closure ⟨γ', x₀, rfl⟩, ?_⟩
    have hlin : (burnsideI23x_LM3 F).lin γ' x₀ = g2Act g x₀ := burnsideI23x_lin3_apply F γ' x₀
    rw [hlin, burnsideI23x_lf3 F g x₀]
    show Θ _ = _
    rw [hΘ]
    conv_rhs => rw [hyeq, map_add, map_smul, h1, h2]
    conv_rhs => rw [g2_zI_eq g x₀]
    have hzI : ∀ a b : Ix3 → F, zI (a - b) = zI a - zI b := fun a b => by
      have := zI_add (a - b) b
      rw [sub_add_cancel] at this
      rw [this]; abel
    show zI (g2Act g x₀ - x₀) + (cgE g (zI x₀)).1 • cayleyOne F = _
    rw [hzI]
    abel
  have hw : (Θ w) ∈ AddSubgroup.closure
      {d | ∃ (γ : ↥(quasithinG2 F)) (y : quasithinZorn F), y.1 + y.2.2.2 = 0 ∧
        d = (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) y - y} :=
    hA _ ((burnsideI23x_kappa3 F w).2)
  obtain ⟨c, hc, hcw⟩ := hB hw
  have : c = w := hΘinj hcw
  rw [← this]
  exact hc
open CFSG.Quasithin in
theorem burnsideI23x_realizes_zorn_congr {F : Type} [Field F]
    {Γ₁ Γ₂ : Subgroup (quasithinZorn F ≃ₗ[F] quasithinZorn F)} (heq : Γ₁ = Γ₂)
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥Γ₁ →* ↥H}
    (h : (FFModel.zornQ Γ₁).RealizesVia H U Z π) :
    ∃ π' : ↥Γ₂ →* ↥H, (FFModel.zornQ Γ₂).RealizesVia H U Z π' := by
  subst heq
  exact ⟨π, h⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK in
theorem burnsideI23x_hbound3 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ n) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut V)) (W0 : Subgroup V)
        (π : (i23NaturalModel 3 F).Gam →* ↥L),
        (i23NaturalModel 3 F).RealizesVia L ⊤ W0 π → W0 = fixV L → commV L = ⊤ →
        Nat.card W0 ≤ Nat.card F := by
  intro V _ _ hV L W0 π hreal hW0 hcomm
  subst hW0
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hF
  have hcommOf : XMod.commOf ↥L (⊤ : Subgroup V) = ⊤ := by
    rw [CFSG.Quasithin.MS93.xmodCommOf_top_eq]
    exact hcomm
  have heq : ⁅quasithinG2 F, quasithinG2 F⁆ = quasithinG2 F := by
    rw [g2Derived_eq hc0 hc1,
      ← CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  obtain ⟨π', hπ'⟩ := burnsideI23x_realizes_zorn_congr heq (π := π) hreal
  have h := card_le_of_zornQ_realizesVia hV L ⊤ (fixV L) le_top
    (fun z hz x hx => hz x hx) (fun _ _ _ _ => Subgroup.mem_top _) hcommOf hn hF hπ'
  rw [← hF] at h
  exact h
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ofCayley {F : Type} [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (u : ↥(cayleyGroup F)) : ↥⁅quasithinG2 F, quasithinG2 F⁆ :=
  ⟨(u : quasithinZorn F ≃ₗ[F] quasithinZorn F), (g2Derived_eq hc0 hc1).ge u.2⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_lin3_ofCayley {F : Type} [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (u : ↥(cayleyGroup F)) (x : Ix3 → F) :
    (burnsideI23x_LM3 F).lin (burnsideI23x_ofCayley hc0 hc1 u) x = g2Act u x := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_stab_gmap {F : Type} [Field F] [CharP F 2] (g : ↥(cayleyGroup F))
    {S : Submodule F (Ix3 → F)} {u : ↥(cayleyGroup F)} (hu : u ∈ stabQ S) (x : Ix3 → F) :
    g2Act (g * u * g⁻¹) x ∈ gmapG g S ↔ x ∈ gmapG g S := by
  rw [mem_gmapG, mem_gmapG, conj_g2Act]
  exact (mem_stabQ.1 hu _).symm

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_irred3_one {F : Type} [Field F] [Finite F] [CharP F 2] {c₀ : F} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) (A : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ((Ix3 → F) ≃ₗ[F] (Ix3 → F)))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM3 F).lin γ x) (g : ↥(cayleyGroup F))
    (C : AddSubgroup (Ix3 → F)) (hC : C ≠ ⊥) (hCℓ : C ≤ (gmapG g (stdF F 1)).toAddSubgroup)
    (hCinv : ∀ γ, (∀ x, A γ x ∈ (gmapG g (stdF F 1)).toAddSubgroup ↔
        x ∈ (gmapG g (stdF F 1)).toAddSubgroup) → ∀ x ∈ C, A γ x ∈ C) :
    (gmapG g (stdF F 1)).toAddSubgroup ≤ C := by
  obtain ⟨⟨x₀, hx₀C⟩, hx₀ne⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
  have hx₀ne' : x₀ ≠ 0 := fun h => hx₀ne (Subtype.ext h)
  obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.1 (hCℓ hx₀C)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hx₀ne' (by rw [ht, zero_smul])
  have hsc : ∀ c : Fˣ, (c : F) • x₀ ∈ C := by
    intro c
    set γ := burnsideI23x_ofCayley hc0 hc1 (g * tG c * g⁻¹) with hγ
    have hstab : ∀ x, A γ x ∈ (gmapG g (stdF F 1)).toAddSubgroup ↔
        x ∈ (gmapG g (stdF F 1)).toAddSubgroup := fun x => by
      rw [hAlin, burnsideI23x_lin3_ofCayley]
      exact (burnsideI23x_stab_gmap g (S := stdF F 1) (u := tG c) (fun w => (tG_mem_stab c w).symm) x)
    have h1 := hCinv γ hstab x₀ hx₀C
    have h2 : A γ x₀ = (c : F) • x₀ := by
      rw [hAlin, burnsideI23x_lin3_ofCayley, ht, CFSG.Quasithin.JonesParshall.g2Act_smul, g2Act_mul_apply, g2Act_mul_apply,
        g2Act_inv_apply, g2Act_tG_eu, mul_one, show (eu 0 (c : F) : Ix3 → F) = (c : F) • eu 0 1 by
          rw [← Pi.single_smul, smul_eq_mul, mul_one], CFSG.Quasithin.JonesParshall.g2Act_smul, smul_smul, smul_smul, mul_comm]
    rw [h2] at h1
    exact h1
  intro x hx
  obtain ⟨s, hs⟩ := mem_gmapG_stdF_one_iff.1 hx
  by_cases hst : s * t⁻¹ = 0
  · have : x = 0 := by
      rw [hs]
      have : s = 0 := by
        have := congrArg (· * t) hst
        simpa [ht0] using this
      rw [this, zero_smul]
    rw [this]
    exact C.zero_mem
  · have := hsc (Units.mk0 (s * t⁻¹) hst)
    convert this using 1
    rw [Units.val_mk0, ht, smul_smul, hs, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_irred3_two {F : Type} [Field F] [Finite F] [CharP F 2] {c₀ : F} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) (A : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ((Ix3 → F) ≃ₗ[F] (Ix3 → F)))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM3 F).lin γ x) (g : ↥(cayleyGroup F))
    (C : AddSubgroup (Ix3 → F)) (hC : C ≠ ⊥) (hCℓ : C ≤ (gmapG g (stdF F 2)).toAddSubgroup)
    (hCinv : ∀ γ, (∀ x, A γ x ∈ (gmapG g (stdF F 2)).toAddSubgroup ↔
        x ∈ (gmapG g (stdF F 2)).toAddSubgroup) → ∀ x ∈ C, A γ x ∈ C) :
    (gmapG g (stdF F 2)).toAddSubgroup ≤ C := by
  set e : F → F → (Ix3 → F) := fun r s => g2Act g (q6 r 0 0 0 0 s) with he
  have hmem2 : ∀ r s : F, q6 r 0 0 0 0 s ∈ stdF F 2 := fun r s => mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩
  have hadd : ∀ r s r' s' : F, e (r + r') (s + s') = e r s + e r' s' := fun r s r' s' => by
    simp only [he]
    rw [← map_add, q6_add]
    simp
  have he0 : e 0 0 = 0 := by
    simp only [he]
    rw [q6_zero, map_zero]
  have heℓ : ∀ r s : F, e r s ∈ (gmapG g (stdF F 2)).toAddSubgroup := fun r s => by
    show e r s ∈ gmapG g (stdF F 2)
    rw [mem_gmapG]
    simp only [he]
    rw [g2Act_inv_apply]
    exact hmem2 r s
  have hrep : ∀ x ∈ (gmapG g (stdF F 2)).toAddSubgroup, ∃ r s : F, x = e r s := by
    intro x hx
    have hx' : g2Act g⁻¹ x ∈ stdF F 2 := mem_gmapG.1 hx
    refine ⟨(g2Act g⁻¹ x) (.inl 0), (g2Act g⁻¹ x) (.inr 2), ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.1 hx'
    have hw' : g2Act g⁻¹ x = q6 ((g2Act g⁻¹ x) (.inl 0)) 0 0 0 0 ((g2Act g⁻¹ x) (.inr 2)) := by
      conv_lhs => rw [q6_eta (g2Act g⁻¹ x)]
      rw [h1, h2, h3, h4]
    simp only [he]
    rw [← hw', g2Act_apply_inv]
  have hx1 : ∀ t r s : F, A (burnsideI23x_ofCayley hc0 hc1 (g * g2X ![0, t, 0] * g⁻¹)) (e r s) =
      e r (s + t * r) := by
    intro t r s
    rw [hAlin, burnsideI23x_lin3_ofCayley]
    simp only [he]
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply, g2Act_x1q]
    simp
  have hy1 : ∀ t r s : F, A (burnsideI23x_ofCayley hc0 hc1 (g * g2Y ![0, t, 0] * g⁻¹)) (e r s) =
      e (r + t * s) s := by
    intro t r s
    rw [hAlin, burnsideI23x_lin3_ofCayley]
    simp only [he]
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply, g2Act_y1q]
    simp
  have hstabX : ∀ t : F, ∀ x, A (burnsideI23x_ofCayley hc0 hc1 (g * g2X ![0, t, 0] * g⁻¹)) x ∈
      (gmapG g (stdF F 2)).toAddSubgroup ↔ x ∈ (gmapG g (stdF F 2)).toAddSubgroup := fun t x => by
    rw [hAlin, burnsideI23x_lin3_ofCayley]
    exact burnsideI23x_stab_gmap g (S := stdF F 2) (u := g2X ![0, t, 0])
      (sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inl rfl⟩)) x
  have hstabY : ∀ t : F, ∀ x, A (burnsideI23x_ofCayley hc0 hc1 (g * g2Y ![0, t, 0] * g⁻¹)) x ∈
      (gmapG g (stdF F 2)).toAddSubgroup ↔ x ∈ (gmapG g (stdF F 2)).toAddSubgroup := fun t x => by
    rw [hAlin, burnsideI23x_lin3_ofCayley]
    exact burnsideI23x_stab_gmap g (S := stdF F 2) (u := g2Y ![0, t, 0])
      (sl2E1_le_stabQ (Subgroup.subset_closure ⟨t, Or.inr rfl⟩)) x
  have hkey : ∀ r s : F, e r s ∈ C → r ≠ 0 → ∀ r' s' : F, e r' s' ∈ C := by
    intro r s hrs hr r' s'
    have hA1 : ∀ t : F, e 0 (t * r) ∈ C := fun t => by
      have h1 := hCinv _ (hstabX t) _ hrs
      rw [hx1] at h1
      have h2 : e r (s + t * r) = e r s + e 0 (t * r) := by simpa using hadd r s 0 (t * r)
      have h3 : e 0 (t * r) = e r (s + t * r) - e r s := by rw [h2]; abel
      rw [h3]
      exact C.sub_mem h1 hrs
    have hB0 : ∀ s'' : F, e 0 s'' ∈ C := fun s'' => by
      have := hA1 (s'' * r⁻¹)
      rwa [mul_assoc, inv_mul_cancel₀ hr, mul_one] at this
    have hr0 : ∀ r'' : F, e r'' 0 ∈ C := fun r'' => by
      have h1 := hCinv _ (hstabY r'') _ (hB0 1)
      rw [hy1] at h1
      have h2 : e (0 + r'' * 1) 1 = e 0 1 + e r'' 0 := by simpa using hadd 0 1 r'' 0
      have h3 : e r'' 0 = e (0 + r'' * 1) 1 - e 0 1 := by rw [h2]; abel
      rw [h3]
      exact C.sub_mem h1 (hB0 1)
    have := C.add_mem (hr0 r') (hB0 s')
    rwa [← hadd, add_zero, zero_add] at this
  obtain ⟨⟨x₀, hx₀C⟩, hx₀ne⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
  have hx₀ne' : x₀ ≠ 0 := fun h => hx₀ne (Subtype.ext h)
  obtain ⟨r₀, s₀, hrs⟩ := hrep x₀ (hCℓ hx₀C)
  intro x hx
  obtain ⟨r', s', rfl⟩ := hrep x hx
  by_cases hr₀ : r₀ = 0
  · have hs₀ : s₀ ≠ 0 := by
      rintro rfl
      apply hx₀ne'
      rw [hrs, hr₀, he0]
    have h1 := hCinv _ (hstabY 1) _ hx₀C
    rw [hrs, hr₀, hy1] at h1
    have h2 : e (0 + 1 * s₀) s₀ = e 0 s₀ + e s₀ 0 := by simpa using hadd 0 s₀ s₀ 0
    have h4 : e 0 s₀ ∈ C := by
      have := hx₀C
      rwa [hrs, hr₀] at this
    have h3 : e s₀ 0 ∈ C := by
      have h5 : e s₀ 0 = e (0 + 1 * s₀) s₀ - e 0 s₀ := by rw [h2]; abel
      rw [h5]
      exact C.sub_mem h1 h4
    exact hkey s₀ 0 h3 hs₀ r' s'
  · have := hx₀C
    rw [hrs] at this
    exact hkey r₀ s₀ this hr₀ r' s'
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_UCg_three {n : ℕ} (hn : 2 ≤ n) : burnsideI23x_UCg 3 n := by
  intro F _ _ hF U _ _ hU G L T K hLG hnorm hGT hT hGK huniv marking β hsec U1 U2 h1 h2
  haveI : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  haveI : Finite (MulAut U) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hS := burnsideI23x_scalarAgree3 F
  obtain ⟨a, ha0, ha1⟩ := burnsideI23x_exists_ne_zero_one hF hn
  have hEndLin : ∀ φ : (Ix3 → F) →+ (Ix3 → F),
      (∀ γ x, φ ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (φ x)) →
      ∃ c : F, ∀ x, φ x = c • x := fun φ hφ => burnsideI23x_hEnd3 F ha0 ha1 φ hφ
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM3 F) (burnsideI23x_sd3 F) (burnsideI23x_hsymp3 F) (burnsideI23x_hfaith3 F)
    (burnsideI23x_genW'3 F ha0 ha1) (burnsideI23x_hbound3 hn hF) hU huniv hsec
  have hEnd : ∀ φ : (Ix3 → F) →+ (Ix3 → F),
      (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x := fun φ hφ =>
    hEndLin φ (fun γ x => by simpa only [hAlin] using hφ γ x)
  have hf := burnsideI23x_isCoord (burnsideI23x_LM3 F) hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  obtain ⟨hU2i, hU2F, hU2c⟩ := burnsideI23x_marked_ell hS hsec h2
  have hU1' : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hU2' : ∀ u, u ∈ U2 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U2 := fun u => by
    rw [hψfst]; exact hU2i u
  have hcard1 : Nat.card (hf.img U1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img U1) hU1F hcard1
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht => hnorm t (hTG ht)
  have hTW0 : ∀ t ∈ T, ∀ w ∈ K, t w ∈ K := fun t ht => hGK t (hTG ht)
  have hfl1 : IsFlagW L (T ⊓ L) K (2 ^ n) 1 U1 :=
    burnsideI23x_marked_imp_flag hS hU hsec (fun T' hT' => hEndLin T' hT') h1
  have hfl2 : IsFlagW L (T ⊓ L) K (2 ^ n) 2 U2 :=
    burnsideI23x_marked_imp_flag hS hU hsec (fun T' hT' => hEndLin T' hT') h2
  have hFc : Nat.card F = 2 ^ n := hF
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hF (by omega) hf ha0 ha1 hP
  rw [← hFc] at hfl1 hfl2
  obtain ⟨S1, hS1, hS1c, hU1pre⟩ := exists_eq_preG_of_isFlagW hU hf ha0 ha1 hg hfl1
  obtain ⟨S2, hS2, hS2c, hU2pre⟩ := exists_eq_preG_of_isFlagW hU hf ha0 ha1 hg hfl2
  rw [eq_stdF_of_card hS1 hS1c] at hU1pre
  rw [eq_stdF_of_card hS2 hS2c] at hU2pre
  have himg1 : hf.img U1 = (gmapG g (stdF F 1)).toAddSubgroup :=
    (congrArg hf.img hU1pre).trans (hf.img_pre (gmapG g (stdF F 1)).toAddSubgroup)
  have himg2 : hf.img U2 = (gmapG g (stdF F 2)).toAddSubgroup :=
    (congrArg hf.img hU2pre).trans (hf.img_pre (gmapG g (stdF F 2)).toAddSubgroup)
  have hirr1 : ∀ C : AddSubgroup (Ix3 → F), C ≠ ⊥ → C ≤ hf.img U1 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U1 ↔ x ∈ hf.img U1) → ∀ x ∈ C, A γ x ∈ C) → hf.img U1 ≤ C := by
    intro C hC hCℓ hCinv
    rw [himg1] at hCℓ hCinv ⊢
    exact burnsideI23x_irred3_one ha0 ha1 A hAlin g C hC hCℓ hCinv
  have hirr2 : ∀ C : AddSubgroup (Ix3 → F), C ≠ ⊥ → C ≤ hf.img U2 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U2 ↔ x ∈ hf.img U2) → ∀ x ∈ C, A γ x ∈ C) → hf.img U2 ≤ C := by
    intro C hC hCℓ hCinv
    rw [himg2] at hCℓ hCinv ⊢
    exact burnsideI23x_irred3_two ha0 ha1 A hAlin g C hC hCℓ hCinv
  have he₀ℓ : e₀ ∈ hf.img U1 := (hℓ₁ e₀).2 ⟨1, (one_smul F e₀).symm⟩
  have hcardF2 : Nat.card (hf.img U2) = Nat.card F ^ 2 := by rw [hU2c, hF]
  have he₂ : ∃ e₂ ∈ hf.img U2, e₂ ≠ 0 := by
    have hlt : 1 < Nat.card (hf.img U2) := by
      rw [hcardF2]
      have : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    haveI : Nontrivial (hf.img U2) := Finite.one_lt_card_iff_nontrivial.1 hlt
    obtain ⟨⟨e₂, he₂⟩, hne⟩ := exists_ne (0 : hf.img U2)
    exact ⟨e₂, he₂, fun h => hne (Subtype.ext h)⟩
  obtain ⟨e₂, he₂ℓ, he₂0⟩ := he₂
  refine ⟨?_, ⟨?_, ?_⟩, fun _ hm3 => absurd rfl hm3⟩
  · exact burnsideI23x_SD.exists_T_fixed ψ marking hπs hψact hEnd hgenW hTG hnorm hT2 he₀ hℓ₁
      hU1' (fun t ht u hu => h1.2.1 t ht u hu)
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU1F hU1' he₀ℓ he₀
      hirr1
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU2F hU2' he₂ℓ
      he₂0 hirr2
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_g2Act_u0 {F : Type} [Field F] [CharP F 2] (α β γ a b c : F) (w : Ix3 → F) :
    g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL a b c)) w =
      q6 (w (.inl 0) + a * w (.inl 1) + b * w (.inl 2) + (γ + β * c) * w (.inr 1) +
          (γ * a + β * b + β * a * c + α ^ 2) * w (.inr 0) + β * w (.inr 2))
        (w (.inl 1) + c * w (.inl 2) + γ * w (.inr 0))
        (w (.inl 2) + β * w (.inr 0))
        (w (.inr 0))
        (w (.inr 1) + (a + α * β) * w (.inr 0) + (β * γ + β ^ 2 * c + α) * w (.inl 2) +
          β ^ 2 * w (.inl 1))
        (w (.inr 2) + c * w (.inr 1) + (b + a * c + α * γ) * w (.inr 0) +
          (γ ^ 2 + β * γ * c + α * c) * w (.inl 2) + (β * γ + α) * w (.inl 1)) := by
  rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_g2A_uSL, g2Act_g2Y_e12, g2Act_g2X_e0]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> simp <;> ring
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model in
theorem burnsideI23x_U0_decomp {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (u : ↥(cayleyGroup F)) (hu : u ∈ U0 F) :
    ∃ α β γ a b c : F, u = g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL a b c) := by
  have := finite_cayleyGroup (F := F)
  let φ : (F × F × F × F × F × F) → ↥(U0 F) := fun p =>
    ⟨g2X ![p.1, 0, 0] * g2Y ![0, p.2.1, p.2.2.1] * g2A (uSL p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2),
      stabElt_mem_U0 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2⟩
  have hφ : Function.Injective φ := by
    intro p q h
    have h1 := congrArg Subtype.val h
    have h2 : stabElt (p.1, p.2.1, p.2.2.1, (⟨uSL p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2,
        uSL_mem_S0 _ _ _⟩ : ↥(S0 F))) =
        stabElt (q.1, q.2.1, q.2.2.1, (⟨uSL q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2,
        uSL_mem_S0 _ _ _⟩ : ↥(S0 F))) := h1
    have h3 := stabElt_injective h2
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h3
    obtain ⟨e1, e2, e3, e4⟩ := h3
    obtain ⟨f1, f2, f3⟩ := uSL_injective e4
    exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 (Prod.ext f1 (Prod.ext f2 f3))))
  have hcard : Nat.card ↥(U0 F) ≤ Nat.card (F × F × F × F × F × F) := by
    rw [card_U0 hF]
    simp only [Nat.card_prod]
    exact le_of_eq (by ring)
  have hbij := hφ.bijective_of_nat_card_le hcard
  obtain ⟨p, hp⟩ := hbij.2 ⟨u, hu⟩
  refine ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, ?_⟩
  exact (congrArg Subtype.val hp).symm

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model in
theorem burnsideI23x_g2Act_u0_q6 {F : Type} [Field F] [CharP F 2] (α β γ a b c : F)
    (x0 x1 x2 y0 y1 y2 : F) :
    g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL a b c)) (q6 x0 x1 x2 y0 y1 y2) =
      q6 (x0 + a * x1 + b * x2 + (γ + β * c) * y1 + (γ * a + β * b + β * a * c + α ^ 2) * y0 +
          β * y2)
        (x1 + c * x2 + γ * y0) (x2 + β * y0) y0
        (y1 + (a + α * β) * y0 + (β * γ + β ^ 2 * c + α) * x2 + β ^ 2 * x1)
        (y2 + c * y1 + (b + a * c + α * γ) * y0 + (γ ^ 2 + β * γ * c + α * c) * x2 +
          (β * γ + α) * x1) := by
  rw [burnsideI23x_g2Act_u0]
  simp [q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model in
theorem burnsideI23x_center_U0 {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (z : ↥(cayleyGroup F)) (hz : z ∈ U0 F) :
    (∀ u ∈ U0 F, u * z = z * u) ↔ ∃ s : F, z = tL s := by
  constructor
  · intro hcomm
    obtain ⟨α, β, γ, a, b, c, rfl⟩ := burnsideI23x_U0_decomp hF z hz
    have key : ∀ u ∈ U0 F, ∀ w : Ix3 → F,
        g2Act u (g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL a b c)) w) =
          g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL a b c)) (g2Act u w) := by
      intro u hu w
      have := congrArg (fun g => g2Act g w) (hcomm u hu)
      simpa [g2Act_mul_apply] using this
    have hβ : β = 0 := by
      have h := congrFun (key _ (g2X_mem_U0 1) (q6 0 1 0 0 0 0)) (.inl 0)
      rw [burnsideI23x_g2Act_u0_q6, g2Act_x0q, g2Act_x0q, burnsideI23x_g2Act_u0_q6] at h
      simp [q6] at h
      linear_combination h
    subst hβ
    have hγ : γ = 0 := by
      have h := congrFun (key _ (g2X_mem_U0 1) (q6 0 0 1 0 0 0)) (.inl 0)
      rw [burnsideI23x_g2Act_u0_q6, g2Act_x0q, g2Act_x0q, burnsideI23x_g2Act_u0_q6] at h
      simp [q6] at h
      linear_combination h
    subst hγ
    have hc : c = 0 := by
      have h := congrFun (key _ (g2A_mem_U0 1 0 0) (q6 0 0 1 0 0 0)) (.inl 0)
      rw [burnsideI23x_g2Act_u0_q6, g2Act_g2A_uSL, g2Act_g2A_uSL, burnsideI23x_g2Act_u0_q6] at h
      simp [q6] at h
      linear_combination h
    subst hc
    have ha : a = 0 := by
      have h := congrFun (key _ (g2A_mem_U0 0 0 1) (q6 0 0 1 0 0 0)) (.inl 0)
      rw [burnsideI23x_g2Act_u0_q6, g2Act_g2A_uSL, g2Act_g2A_uSL, burnsideI23x_g2Act_u0_q6] at h
      simp [q6] at h
      linear_combination h
    subst ha
    have hα : α = 0 := by
      have h := congrFun (key _ (g2Y_mem_U0 1 0) (q6 0 0 0 1 0 0)) (.inr 1)
      rw [burnsideI23x_g2Act_u0_q6, g2Act_y1q, g2Act_y1q, burnsideI23x_g2Act_u0_q6] at h
      simp [q6] at h
      linear_combination -h
    subst hα
    refine ⟨b, ?_⟩
    apply cayley_ext
    intro w
    rw [q6_eta w, burnsideI23x_g2Act_u0_q6, g2Act_tL]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · rintro ⟨s, rfl⟩ u hu
    obtain ⟨α, β, γ, a, b, c, hu'⟩ := burnsideI23x_U0_decomp hF u hu
    apply cayley_ext
    intro w
    rw [g2Act_mul_apply, g2Act_mul_apply, hu', q6_eta w, g2Act_tL, burnsideI23x_g2Act_u0_q6,
      burnsideI23x_g2Act_u0_q6, g2Act_tL]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_tL_eq {F : Type} [Field F] [CharP F 2] (s : F) :
    tL s = g2A (uSL 0 s 0) := by
  apply cayley_ext
  intro w
  rw [q6_eta w, g2Act_tL, g2Act_g2A_uSL]
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> (try simp [q6]) <;> try ring

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_tL_mem_U0 {F : Type} [Field F] [CharP F 2] (s : F) : tL s ∈ U0 F := by
  rw [burnsideI23x_tL_eq]
  exact g2A_mem_U0 0 s 0

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_tL_zero {F : Type} [Field F] [CharP F 2] : tL (0 : F) = 1 := by
  apply cayley_ext
  intro w
  rw [q6_eta w, g2Act_tL, map_one]
  simp [q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_tL_sq {F : Type} [Field F] [CharP F 2] (s : F) : tL s * tL s = 1 := by
  rw [tL_mul, CharTwo.add_self_eq_zero, burnsideI23x_tL_zero]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_center_P {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {c₀ : F} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} {Z : Subgroup V}
    {marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L} {f : V → (Ix3 → F)}
    (hf : IsCoord (lmG F) L Z marking f) {P : Subgroup (MulAut V)} {g : ↥(cayleyGroup F)}
    (hg : ∀ x : MulAut V, x ∈ P ↔
      ∃ u ∈ U0 F, x = ((rhoG hc0 hc1 marking (g * u * g⁻¹) : ↥L) : MulAut V))
    (x : MulAut V) :
    x ∈ CFSG.ASVolI.ChIJK.centerOf P ↔ ∃ s : F, x = ((rhoG hc0 hc1 marking (g * tL s * g⁻¹) : ↥L) : MulAut V) := by
  have hinj : Function.Injective (fun u : ↥(cayleyGroup F) =>
      ((rhoG hc0 hc1 marking u : ↥L) : MulAut V)) := fun u u' h =>
    (rhoG_bijective hf hc0 hc1).1 (Subtype.ext h)
  have hmul : ∀ u u' : ↥(cayleyGroup F), ((rhoG hc0 hc1 marking (u * u') : ↥L) : MulAut V) =
      ((rhoG hc0 hc1 marking u : ↥L) : MulAut V) * ((rhoG hc0 hc1 marking u' : ↥L) : MulAut V) :=
    fun u u' => by rw [map_mul]; rfl
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    have hzP : (z : MulAut V) ∈ P := z.2
    obtain ⟨u, hu, hzu⟩ := (hg _).1 hzP
    have hcent : ∀ u' ∈ U0 F, u' * u = u * u' := by
      intro u' hu'
      have hy : ((rhoG hc0 hc1 marking (g * u' * g⁻¹) : ↥L) : MulAut V) ∈ P := (hg _).2 ⟨u', hu', rfl⟩
      have h1 := Subgroup.mem_center_iff.1 hz ⟨_, hy⟩
      have h2 : ((rhoG hc0 hc1 marking (g * u' * g⁻¹) : ↥L) : MulAut V) * (z : MulAut V) =
          (z : MulAut V) * ((rhoG hc0 hc1 marking (g * u' * g⁻¹) : ↥L) : MulAut V) :=
        congrArg Subtype.val h1
      rw [hzu, ← hmul, ← hmul] at h2
      have h3 := hinj h2
      have h4 : g * (u' * u) * g⁻¹ = g * (u * u') * g⁻¹ := by
        simpa only [mul_assoc, inv_mul_cancel_left] using h3
      exact mul_right_cancel (mul_left_cancel h4)
    obtain ⟨s, hs⟩ := (burnsideI23x_center_U0 hF u hu).1 hcent
    exact ⟨s, by show (z : MulAut V) = _; rw [hzu, hs]⟩
  · rintro ⟨s, rfl⟩
    have hmem : ((rhoG hc0 hc1 marking (g * tL s * g⁻¹) : ↥L) : MulAut V) ∈ P :=
      (hg _).2 ⟨tL s, burnsideI23x_tL_mem_U0 s, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨_, hmem⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨u, hu, hyu⟩ := (hg _).1 y.2
    apply Subtype.ext
    show (y : MulAut V) * _ = _ * (y : MulAut V)
    rw [hyu, ← hmul, ← hmul]
    have := (burnsideI23x_center_U0 hF (tL s) (burnsideI23x_tL_mem_U0 s)).2 ⟨s, rfl⟩ u hu
    have hEq : g * u * g⁻¹ * (g * tL s * g⁻¹) = g * tL s * g⁻¹ * (g * u * g⁻¹) :=
      calc g * u * g⁻¹ * (g * tL s * g⁻¹) = g * (u * tL s) * g⁻¹ := by group
        _ = g * (tL s * u) * g⁻¹ := by rw [this]
        _ = g * tL s * g⁻¹ * (g * u * g⁻¹) := by group
    rw [hEq]
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_ofCayley_mul {F : Type} [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (u v : ↥(cayleyGroup F)) :
    burnsideI23x_ofCayley hc0 hc1 (u * v) =
      burnsideI23x_ofCayley hc0 hc1 u * burnsideI23x_ofCayley hc0 hc1 v := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_ofCayley_inv {F : Type} [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (u : ↥(cayleyGroup F)) :
    burnsideI23x_ofCayley hc0 hc1 u⁻¹ = (burnsideI23x_ofCayley hc0 hc1 u)⁻¹ := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_ofCayley_one {F : Type} [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) : burnsideI23x_ofCayley hc0 hc1 (1 : ↥(cayleyGroup F)) = 1 := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_rhoG_ofCayley {F : Type} [Field F] [CharP F 2] {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L) (u : ↥(cayleyGroup F)) :
    rhoG hc0 hc1 marking u = marking (burnsideI23x_ofCayley hc0 hc1 u) := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2A_E12_apply {F : Type} [Field F] [CharP F 2] (c : F) (x : quasithinZorn F) :
    (g2A (uSL 0 0 c) : quasithinZorn F ≃ₗ[F] quasithinZorn F) x =
      (x.1, (fun i => x.2.1 i + if i = 1 then c * x.2.1 2 else 0),
        (fun i => x.2.2.1 i - if i = 2 then c * x.2.2.1 1 else 0), x.2.2.2) := by
  rw [g2A_apply, gAFun]
  have hA : ((uSL (0 : F) 0 c : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, c; 0, 0, 1] := rfl
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    rw [hA]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · funext i
    rw [adjugate_uSL]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
      CharTwo.neg_eq, CharTwo.sub_eq_add] <;> try ring
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_mem_highestLongRoot {F : Type} [Field F] [CharP F 2] {c₀ : F} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) (y : ↥⁅quasithinG2 F, quasithinG2 F⁆) :
    y ∈ i23G2HighestLongRoot F ↔
      ∃ c : F, y = burnsideI23x_ofCayley hc0 hc1 (g2A (uSL 0 0 c)) := by
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc⟩ := hy
      refine ⟨c, Subtype.ext (LinearEquiv.ext fun x => ?_)⟩
      rw [hc x]
      exact (burnsideI23x_g2A_E12_apply c x).symm
    | one => exact ⟨0, by rw [uSL_zero, map_one]; rfl⟩
    | mul y z _ _ hy hz =>
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨c', rfl⟩ := hz
      refine ⟨c + c', ?_⟩
      rw [← burnsideI23x_ofCayley_mul, ← map_mul, uSL_mul]
      simp
    | inv y _ hy =>
      obtain ⟨c, rfl⟩ := hy
      refine ⟨-c, ?_⟩
      rw [← burnsideI23x_ofCayley_inv, ← map_inv, uSL_inv]
      simp
  · rintro ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨c, fun x => burnsideI23x_g2A_E12_apply c x⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_swap01_conj {F : Type} [Field F] [CharP F 2] (c : F) :
    g2A swap01 * g2A (uSL 0 0 c) * (g2A swap01)⁻¹ = tL c := by
  rw [burnsideI23x_tL_eq, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_swap01]
  have h1 : ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := rfl
  have h2 : ((uSL (0 : F) 0 c : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, c; 0, 0, 1] := rfl
  have h3 : ((uSL (0 : F) c 0 : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, c; 0, 1, 0; 0, 0, 1] := rfl
  rw [h1, h2, h3]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_longroot {F : Type} [Field F] [CharP F 2] {c₀ : F} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L) (g : ↥(cayleyGroup F)) (x : MulAut V) :
    x ∈ (CFSG.conjugate (i23G2HighestLongRoot F)
        (burnsideI23x_ofCayley hc0 hc1 (g * g2A swap01)⁻¹)).map (L.subtype.comp marking) ↔
      ∃ s : F, x = ((rhoG hc0 hc1 marking (g * tL s * g⁻¹) : ↥L) : MulAut V) := by
  set a := burnsideI23x_ofCayley hc0 hc1 (g * g2A swap01)⁻¹ with ha
  have hconj : ∀ c : F, a⁻¹ * burnsideI23x_ofCayley hc0 hc1 (g2A (uSL 0 0 c)) * a =
      burnsideI23x_ofCayley hc0 hc1 (g * tL c * g⁻¹) := by
    intro c
    rw [← burnsideI23x_swap01_conj c, ha, ← burnsideI23x_ofCayley_inv, inv_inv,
      ← burnsideI23x_ofCayley_mul, ← burnsideI23x_ofCayley_mul]
    have hh : g * g2A swap01 * g2A (uSL 0 0 c) * (g * g2A swap01)⁻¹ =
        g * (g2A swap01 * g2A (uSL 0 0 c) * (g2A swap01)⁻¹) * g⁻¹ := by group
    rw [hh]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨c, rfl⟩ := (burnsideI23x_mem_highestLongRoot hc0 hc1 y').1 hy'
    refine ⟨c, ?_⟩
    have := hconj c
    show (L.subtype.comp marking) ((MulAut.conj a⁻¹).toMonoidHom _) = _
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, this]
    rfl
  · rintro ⟨s, rfl⟩
    refine Subgroup.mem_map.2 ⟨a⁻¹ * burnsideI23x_ofCayley hc0 hc1 (g2A (uSL 0 0 s)) * a, ?_, ?_⟩
    · refine Subgroup.mem_map.2 ⟨burnsideI23x_ofCayley hc0 hc1 (g2A (uSL 0 0 s)),
        (burnsideI23x_mem_highestLongRoot hc0 hc1 _).2 ⟨s, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    · rw [hconj s]
      rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_omegaOne_center {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {c₀ : F} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} {Z : Subgroup V}
    {marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L} {f : V → (Ix3 → F)}
    (hf : IsCoord (lmG F) L Z marking f) {P : Subgroup (MulAut V)} {g : ↥(cayleyGroup F)}
    (hg : ∀ x : MulAut V, x ∈ P ↔
      ∃ u ∈ U0 F, x = ((rhoG hc0 hc1 marking (g * u * g⁻¹) : ↥L) : MulAut V)) :
    CFSG.ASVolI.ChIJK.omegaOne (CFSG.ASVolI.ChIJK.centerOf P) = CFSG.ASVolI.ChIJK.centerOf P := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun x hx => hx.1
  · intro x hx
    apply Subgroup.subset_closure
    refine ⟨hx, ?_⟩
    obtain ⟨s, rfl⟩ := (burnsideI23x_center_P hF hc0 hc1 hf hg x).1 hx
    rw [pow_two, ← Subgroup.coe_mul, ← map_mul]
    have : g * tL s * g⁻¹ * (g * tL s * g⁻¹) = 1 := by
      calc g * tL s * g⁻¹ * (g * tL s * g⁻¹) = g * (tL s * tL s) * g⁻¹ := by group
        _ = 1 := by rw [burnsideI23x_tL_sq]; group
    rw [this, map_one]
    rfl
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_normQ_tL {F : Type} [Field F] [CharP F 2] (s : F) (x : Ix3 → F) :
    normQ (g2Act (tL s) x) = normQ x := by
  rw [q6_eta x, g2Act_tL]
  simp only [normQ, q6, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (s * x (.inl 2) * x (.inr 0)) * (CharTwo.two_eq_zero (R := F))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_lift_tL {F : Type} [Field F] [Finite F] [CharP F 2] {c₀ : F} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) (A : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ((Ix3 → F) ≃ₗ[F] (Ix3 → F)))
    (hA : ∀ γ, (burnsideI23x_sd3 F).Symp (A γ))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM3 F).lin γ x) (s : F) (w : (Ix3 → F) × F) :
    (burnsideI23x_sd3 F).lift (hA (burnsideI23x_ofCayley hc0 hc1 (tL s))) w - w =
      (q6 (s * w.1 (.inl 2)) 0 0 0 0 (s * w.1 (.inr 0)), 0) := by
  have hAt : ∀ x, A (burnsideI23x_ofCayley hc0 hc1 (tL s)) x = g2Act (tL s) x := fun x =>
    (hAlin _ x).trans (burnsideI23x_lin3_ofCayley hc0 hc1 _ x)
  rw [burnsideI23x_SD.lift_apply]
  refine Prod.ext ?_ ?_
  · show A (burnsideI23x_ofCayley hc0 hc1 (tL s)) w.1 - w.1 = _
    rw [hAt]
    conv_lhs => rw [q6_eta w.1, g2Act_tL, q6_sub]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · show w.2 + (burnsideI23x_sd3 F).lf (A (burnsideI23x_ofCayley hc0 hc1 (tL s))) w.1 - w.2 = 0
    have h0 : (burnsideI23x_sd3 F).Q0 w.1 +
        (burnsideI23x_sd3 F).Q0 (A (burnsideI23x_ofCayley hc0 hc1 (tL s)) w.1) = 0 := by
      rw [hAt, burnsideI23x_sd3_Q0, burnsideI23x_sd3_Q0, burnsideI23x_normQ_tL]
      exact CharTwo.add_self_eq_zero _
    unfold burnsideI23x_SD.lf
    rw [h0, map_zero]
    ring
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_commV_S3 {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {c₀ : F} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {U : Type} [CommGroup U]
    {L : Subgroup (MulAut U)} {Z : Subgroup U}
    {marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L} {f : U → (Ix3 → F)}
    (hf : IsCoord (lmG F) L Z marking f) {P : Subgroup (MulAut U)} {g : ↥(cayleyGroup F)}
    (hg : ∀ x : MulAut U, x ∈ P ↔
      ∃ u ∈ U0 F, x = ((rhoG hc0 hc1 marking (g * u * g⁻¹) : ↥L) : MulAut U))
    (A : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ((Ix3 → F) ≃ₗ[F] (Ix3 → F)))
    (hA : ∀ γ, (burnsideI23x_sd3 F).Symp (A γ))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM3 F).lin γ x)
    (ψ : U ≃* Multiplicative ((Ix3 → F) × F))
    (hψact : ∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (u : U),
      ψ ((marking γ : MulAut U) u) = (burnsideI23x_sd3 F).liftHom A hA γ (ψ u)) (u : U) :
    u ∈ commV (CFSG.ASVolI.ChIJK.centerOf P) ↔ ∃ p ∈ stdF F 2, Multiplicative.toAdd (ψ u) =
      (burnsideI23x_sd3 F).lift (hA (burnsideI23x_ofCayley hc0 hc1 g)) (p, 0) := by
  classical
  set γg := burnsideI23x_ofCayley hc0 hc1 g with hγg
  have hψ' : ∀ γ u, Multiplicative.toAdd (ψ ((marking γ : MulAut U) u)) =
      (burnsideI23x_sd3 F).lift (hA γ) (Multiplicative.toAdd (ψ u)) := fun γ u => by
    rw [hψact]; rfl
  have hxS := burnsideI23x_center_P hF hc0 hc1 hf hg
  have hxmark : ∀ s : F, ((rhoG hc0 hc1 marking (g * tL s * g⁻¹) : ↥L) : MulAut U) =
      (marking (γg * burnsideI23x_ofCayley hc0 hc1 (tL s) * γg⁻¹) : MulAut U) := fun s => by
    rw [burnsideI23x_rhoG_ofCayley, burnsideI23x_ofCayley_mul, burnsideI23x_ofCayley_mul,
      burnsideI23x_ofCayley_inv]
  have hgen : ∀ (s : F) (u' : U),
      ((rhoG hc0 hc1 marking (g * tL s * g⁻¹) : ↥L) : MulAut U) ((marking γg : MulAut U) u') *
        ((marking γg : MulAut U) u')⁻¹ =
      (marking γg : MulAut U) ((marking (burnsideI23x_ofCayley hc0 hc1 (tL s)) : MulAut U) u' *
        u'⁻¹) := by
    intro s u'
    have hinv : ((marking γg⁻¹ : ↥L) : MulAut U) ((marking γg : MulAut U) u') = u' := by
      have h1 : marking γg⁻¹ * marking γg = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      have h2 := congrArg (fun x : ↥L => ((x : MulAut U) : U ≃* U) u') h1
      simpa using h2
    have e1 : ((marking (γg * burnsideI23x_ofCayley hc0 hc1 (tL s) * γg⁻¹) : ↥L) : MulAut U)
        ((marking γg : MulAut U) u') =
        (marking γg : MulAut U) ((marking (burnsideI23x_ofCayley hc0 hc1 (tL s)) : MulAut U) u') := by
      rw [map_mul, map_mul]
      show (marking γg : MulAut U) ((marking (burnsideI23x_ofCayley hc0 hc1 (tL s)) : MulAut U)
        (((marking γg⁻¹ : ↥L) : MulAut U) ((marking γg : MulAut U) u'))) = _
      rw [hinv]
    rw [hxmark, e1, map_mul, map_inv]
  have hcoord : ∀ (s : F) (u' : U), Multiplicative.toAdd (ψ ((marking γg : MulAut U)
      ((marking (burnsideI23x_ofCayley hc0 hc1 (tL s)) : MulAut U) u' * u'⁻¹))) =
      (burnsideI23x_sd3 F).lift (hA γg)
        (q6 (s * (Multiplicative.toAdd (ψ u')).1 (.inl 2)) 0 0 0 0
          (s * (Multiplicative.toAdd (ψ u')).1 (.inr 0)), 0) := by
    intro s u'
    rw [hψ', map_mul, map_inv, toAdd_mul, toAdd_inv, hψ', ← sub_eq_add_neg,
      burnsideI23x_lift_tL hc0 hc1 A hA hAlin]
  have hmemS : ∀ (p : Ix3 → F), p ∈ stdF F 2 → ∃ s u', s = 1 ∧
      Multiplicative.toAdd (ψ ((marking γg : MulAut U)
        ((marking (burnsideI23x_ofCayley hc0 hc1 (tL s)) : MulAut U) u' * u'⁻¹))) =
        (burnsideI23x_sd3 F).lift (hA γg) (p, 0) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.1 hp
    refine ⟨1, ψ.symm (Multiplicative.ofAdd (q6 0 0 (p (.inl 0)) (p (.inr 2)) 0 0, 0)), rfl, ?_⟩
    rw [hcoord, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    congr 1
    refine Prod.ext ?_ rfl
    show q6 (1 * (q6 0 0 (p (.inl 0)) (p (.inr 2)) 0 0 (.inl 2))) 0 0 0 0
      (1 * (q6 0 0 (p (.inl 0)) (p (.inr 2)) 0 0 (.inr 0))) = p
    conv_rhs => rw [q6_eta p]
    rw [h1, h2, h3, h4]
    simp [q6]
  constructor
  · intro hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, v, rfl⟩ := hx
      obtain ⟨s, rfl⟩ := (hxS y).1 hy
      obtain ⟨u', rfl⟩ := (marking γg : MulAut U).surjective v
      rw [hgen, hcoord]
      refine ⟨q6 (s * (Multiplicative.toAdd (ψ u')).1 (.inl 2)) 0 0 0 0
        (s * (Multiplicative.toAdd (ψ u')).1 (.inr 0)), ?_, rfl⟩
      exact mem_stdF_two.2 ⟨rfl, rfl, rfl, rfl⟩
    | one =>
      exact ⟨0, (stdF F 2).zero_mem, by rw [map_one, toAdd_one, Prod.mk_zero_zero, map_zero]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, hp, hpx⟩ := hx
      obtain ⟨p', hp', hpy⟩ := hy
      refine ⟨p + p', (stdF F 2).add_mem hp hp', ?_⟩
      rw [map_mul, toAdd_mul, hpx, hpy, ← map_add]
      congr 1
      simp
    | inv x _ hx =>
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨-p, (stdF F 2).neg_mem hp, ?_⟩
      rw [map_inv, toAdd_inv, hpx, ← map_neg]
      congr 1
      simp
  · rintro ⟨p, hp, hpu⟩
    obtain ⟨s, u', rfl, hu'⟩ := hmemS p hp
    have hu : u = (marking γg : MulAut U)
        ((marking (burnsideI23x_ofCayley hc0 hc1 (tL 1)) : MulAut U) u' * u'⁻¹) := by
      apply ψ.injective
      apply Multiplicative.toAdd.injective
      rw [hpu, hu']
    rw [hu, ← hgen]
    exact Subgroup.subset_closure ⟨_, (hxS _).2 ⟨1, rfl⟩, _, rfl⟩
namespace burnsideI23x_SD

section SClause

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  (S : burnsideI23x_SD F N) {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem sclause (ψ : U ≃* Multiplicative (N × F)) (Lg : (N × F) ≃ₗ[F] (N × F))
    (Ag : N ≃ₗ[F] N) (hLg1 : ∀ w, (Lg w).1 = Ag w.1) (hLgQ : ∀ w, S.Qw (Lg w) = S.Qw w)
    (Sp : Submodule F N) (hSp0 : ∀ p ∈ Sp, S.Q0 p = 0) (hSpdim : Module.finrank F Sp = 2)
    {C K V2 : Subgroup U}
    (hC : ∀ u, u ∈ C ↔ ∃ p ∈ Sp, Multiplicative.toAdd (ψ u) = Lg (p, 0))
    (hK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0)
    (hV2 : ∀ u, u ∈ V2 ↔ ∃ p ∈ Sp, (Multiplicative.toAdd (ψ u)).1 = Ag p) :
    IsFSubspaceVia (F := F) ψ C 2 ∧ (∀ v ∈ C, S.Qw (Multiplicative.toAdd (ψ v)) = 0) ∧
      C ⊓ K = ⊥ ∧ C ⊔ K = V2 := by
  classical
  have hinj : Function.Injective (Lg.toLinearMap ∘ₗ LinearMap.inl F N F) := fun a b h => by
    have := Lg.injective h
    exact congrArg Prod.fst this
  refine ⟨⟨Sp.map (Lg.toLinearMap ∘ₗ LinearMap.inl F N F), ?_, fun v => ?_⟩, ?_, ?_, ?_⟩
  · rw [← hSpdim]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj Sp)).symm
  · rw [hC]
    constructor
    · rintro ⟨p, hp, h⟩
      exact ⟨p, hp, h.symm⟩
    · rintro ⟨p, hp, h⟩
      exact ⟨p, hp, h.symm⟩
  · intro v hv
    obtain ⟨p, hp, h⟩ := (hC v).1 hv
    rw [h, hLgQ]
    show S.Q0 p + (0 : F) ^ 2 = 0
    rw [hSp0 p hp]
    ring
  · rw [eq_bot_iff]
    intro u hu
    obtain ⟨p, hp, h⟩ := (hC u).1 hu.1
    have h1 := (hK u).1 hu.2
    rw [h, hLg1] at h1
    have hp0 : p = 0 := Ag.injective (by rw [h1, map_zero])
    rw [Subgroup.mem_bot]
    apply ψ.injective
    apply Multiplicative.toAdd.injective
    rw [h, hp0, Prod.mk_zero_zero, map_zero, map_one, toAdd_one]
  · apply le_antisymm
    · refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · obtain ⟨p, hp, h⟩ := (hC u).1 hu
        rw [hV2]
        exact ⟨p, hp, by rw [h, hLg1]⟩
      · rw [hV2]
        exact ⟨0, Sp.zero_mem, by rw [(hK u).1 hu, map_zero]⟩
    · intro u hu
      obtain ⟨p, hp, h⟩ := (hV2 u).1 hu
      set c : U := ψ.symm (Multiplicative.ofAdd (Lg (p, 0))) with hc
      have hcC : c ∈ C := (hC c).2 ⟨p, hp, by rw [hc, MulEquiv.apply_symm_apply, toAdd_ofAdd]⟩
      have hk : u * c⁻¹ ∈ K := by
        rw [hK, map_mul, map_inv, toAdd_mul, toAdd_inv, hc, MulEquiv.apply_symm_apply, toAdd_ofAdd,
          Prod.fst_add, Prod.fst_neg, hLg1, h]
        simp
      have : u = c * (u * c⁻¹) := by rw [mul_comm u c⁻¹, mul_inv_cancel_left]
      rw [this]
      exact Subgroup.mul_mem_sup hcC hk

end SClause

end burnsideI23x_SD
namespace burnsideI23x_SD

section OrthCommon

variable {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type} [AddCommGroup N] [Module F N]
  {S : burnsideI23x_SD F N} {U : Type} [CommGroup U]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem orth_common {n : ℕ} (hF : Nat.card F = 2 ^ n) {W' : Type} [AddCommGroup W']
    [Module F W'] (Q' : W' → F) (κ : (N × F) ≃ₗ[F] W') (hκ : ∀ w, Q' (κ w) = S.Qw w)
    (ψ : U ≃* Multiplicative (N × F)) {L : Subgroup (MulAut U)} {K : Subgroup U}
    (hψK : ∀ u, u ∈ K ↔ (Multiplicative.toAdd (ψ u)).1 = 0) (hfixV : fixV L = K)
    {e₀ : N} (he₀ : e₀ ≠ 0) {ℓ : AddSubgroup N} (hℓ : ∀ x, x ∈ ℓ ↔ ∃ a : F, x = a • e₀)
    {U1 : Subgroup U} (hU1 : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ ℓ)
    {T : Subgroup (MulAut U)} (hfixP : U1 = fixV (T ⊓ L)) :
    ((∀ v : U, v ∈ fixV L ↔
        ∀ w : W', polarOf Q' (Multiplicative.toAdd (psiTrans ψ κ v)) w = 0) ∧
      Nat.card ↥(fixV L) = 2 ^ n) ∧
    (U1 = fixV (T ⊓ L) ∧
      ∃! P : Subgroup U, IsFSubspaceVia (F := F) (psiTrans ψ κ) P 1 ∧
        (∀ v ∈ P, Q' (Multiplicative.toAdd (psiTrans ψ κ v)) = 0) ∧ U1 = P ⊔ fixV L ∧
        P ⊓ fixV L = ⊥) := by
  have hQ : ∀ v, Q' (Multiplicative.toAdd (psiTrans ψ κ v)) =
      S.Qw (Multiplicative.toAdd (ψ v)) := fun v => by rw [toAdd_psiTrans, hκ]
  refine ⟨?_, hfixP, ?_⟩
  · obtain ⟨h1, h2⟩ := S.orth_radical ψ hψK hfixV
    refine ⟨fun v => ?_, by rw [h2, hF]⟩
    rw [h1 v]
    constructor
    · intro h w'
      obtain ⟨w, rfl⟩ := κ.surjective w'
      rw [toAdd_psiTrans, polarOf_transport S.Qw Q' κ hκ]
      exact h w
    · intro h w
      have := h (κ w)
      rwa [toAdd_psiTrans, polarOf_transport S.Qw Q' κ hκ] at this
  · obtain ⟨P, hP, hPu⟩ := S.orth_point ψ hψK he₀ hℓ hU1
    rw [← hfixV] at hP hPu
    refine ⟨P, ⟨(isFSubspaceVia_transport ψ κ P 1).1 hP.1, fun v hv => by
      rw [hQ]; exact hP.2.1 v hv, hP.2.2.1, hP.2.2.2⟩, fun P' hP' => hPu P' ⟨
        (isFSubspaceVia_transport ψ κ P' 1).2 hP'.1, fun v hv => by
        rw [← hQ]; exact hP'.2.1 v hv, hP'.2.2.1, hP'.2.2.2⟩⟩

end OrthCommon

end burnsideI23x_SD
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_part1_m3 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 3 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 3 F).sec ⧸
      (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec}
    (hsec : I23SectionMap (i23NaturalModel 3 F) L W0 marking β)
    (hT2 : IsPGroup 2 T) (hP : IsSylowTwoOf (T ⊓ L) L)
    {V1 V2 : Subgroup V} (h1 : IsI23MarkedSubspace 3 n 1 F T W0 V1 β)
    (h2 : IsI23MarkedSubspace 3 n 2 F T W0 V2 β)
    (hflag1 : ∀ U', IsFlagW L (T ⊓ L) W0 (2 ^ n) 1 U' → U' = V1)
    (huniv : IsUniversalCovering L W0) :
    ∃ (ψ : V ≃* Multiplicative ↥(zornO0F F)) (π : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L),
      Function.Surjective π ∧
      (∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (v : V),
        ((Multiplicative.toAdd (ψ ((π γ : MulAut V) v)) : ↥(zornO0F F)) : quasithinZorn F) =
          (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
            ((Multiplicative.toAdd (ψ v) : ↥(zornO0F F)) : quasithinZorn F)) ∧
      I23ScalarCompatibility 3 F ψ β ∧
      OrthConclMarked (fun x : ↥(zornO0F F) =>
        CFSG.ASVolI.ChIJK.zornNorm F (x : quasithinZorn F)) 3 n ψ L T
        (i23TransvectionRoot L W0 V1) (CFSG.ASVolI.ChIJK.centerOf (T ⊓ L)) V1 V2 := by
  haveI : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have hS := burnsideI23x_scalarAgree3 F
  obtain ⟨a, ha0, ha1⟩ := burnsideI23x_exists_ne_zero_one hF hn
  have hEndLin : ∀ φ : (Ix3 → F) →+ (Ix3 → F),
      (∀ γ x, φ ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (φ x)) →
      ∃ c : F, ∀ x, φ x = c • x := fun φ hφ => burnsideI23x_hEnd3 F ha0 ha1 φ hφ
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM3 F) (burnsideI23x_sd3 F) (burnsideI23x_hsymp3 F) (burnsideI23x_hfaith3 F)
    (burnsideI23x_genW'3 F ha0 ha1) (burnsideI23x_hbound3 hn hF) hV huniv hsec
  have hf := burnsideI23x_isCoord (burnsideI23x_LM3 F) hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  obtain ⟨hU2i, hU2F, hU2c⟩ := burnsideI23x_marked_ell hS hsec h2
  have hU1' : ∀ u, u ∈ V1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img V1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hU2' : ∀ u, u ∈ V2 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img V2 := fun u => by
    rw [hψfst]; exact hU2i u
  have hcard1 : Nat.card (hf.img V1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img V1) hU1F hcard1
  have hψK : ∀ u, u ∈ W0 ↔ (Multiplicative.toAdd (ψ u)).1 = 0 := fun u => by
    rw [hψfst]
    exact (hf.ker u).symm
  have hfixP : V1 = fixV (T ⊓ L) :=
    le_antisymm (burnsideI23x_SD.line_le_fixV_P ψ marking hπs hψact hT2 he₀ hℓ₁ hU1' h1.2.1)
      (burnsideI23x_fixV_P_le hEndLin hF hV hsec huniv.1 h1.1 hflag1)
  have hfl2 : IsFlagW L (T ⊓ L) W0 (2 ^ n) 2 V2 :=
    burnsideI23x_marked_imp_flag hS hV hsec (fun T' hT' => hEndLin T' hT') h2
  have hFc : Nat.card F = 2 ^ n := hF
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hF (by omega) hf ha0 ha1 hP
  rw [← hFc] at hfl2
  obtain ⟨S2, hS2, hS2c, hV2pre⟩ := exists_eq_preG_of_isFlagW hV hf ha0 ha1 hg hfl2
  rw [eq_stdF_of_card hS2 hS2c] at hV2pre
  have himg2 : hf.img V2 = (gmapG g (stdF F 2)).toAddSubgroup :=
    (congrArg hf.img hV2pre).trans (hf.img_pre (gmapG g (stdF F 2)).toAddSubgroup)
  set γg := burnsideI23x_ofCayley ha0 ha1 g with hγg
  have hcommV := burnsideI23x_commV_S3 hF ha0 ha1 hf hg A hA hAlin ψ hψact
  have hSp0 : ∀ p ∈ stdF F 2, (burnsideI23x_sd3 F).Q0 p = 0 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.1 hp
    rw [burnsideI23x_sd3_Q0]
    simp [normQ, h1, h2, h3, h4]
  have hSpdim : Module.finrank F (stdF F 2) = 2 := by
    have hc := card_stdF (F := F) (h := 2) (by norm_num)
    have hc2 := Module.natCard_eq_pow_finrank (K := F) (V := ↥(stdF F 2))
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    exact Nat.pow_right_injective hq (hc2.symm.trans hc)
  have hAg : ∀ x, A γg x = g2Act g x := fun x =>
    (hAlin γg x).trans (burnsideI23x_lin3_ofCayley ha0 ha1 g x)
  have hV2' : ∀ u, u ∈ V2 ↔ ∃ p ∈ stdF F 2, (Multiplicative.toAdd (ψ u)).1 = A γg p := by
    intro u
    rw [hU2', himg2]
    show _ ∈ gmapG g (stdF F 2) ↔ _
    rw [mem_gmapG]
    constructor
    · intro hx
      refine ⟨g2Act g⁻¹ (Multiplicative.toAdd (ψ u)).1, hx, ?_⟩
      rw [hAg, g2Act_apply_inv]
    · rintro ⟨p, hp, hpx⟩
      rw [hpx, hAg, g2Act_inv_apply]
      exact hp
  have hscl := burnsideI23x_SD.sclause (burnsideI23x_sd3 F) ψ
    ((burnsideI23x_sd3 F).lift (hA γg)) (A γg) (fun w => rfl)
    (fun w => (burnsideI23x_sd3 F).Qw_lift (hA γg) w) (stdF F 2) hSp0 hSpdim
    (C := commV (CFSG.ASVolI.ChIJK.centerOf (T ⊓ L))) (K := fixV L) (V2 := V2)
    (fun u => hcommV u) (fun u => by rw [hfixV]; exact hψK u) hV2'
  have hκ := burnsideI23x_kappa3_norm F
  have hcommon := burnsideI23x_SD.orth_common hF
    (fun x : ↥(zornO0F F) => CFSG.ASVolI.ChIJK.zornNorm F (x : quasithinZorn F))
    (burnsideI23x_kappa3 F) hκ ψ hψK hfixV he₀ hℓ₁ hU1' hfixP
  refine ⟨burnsideI23x_SD.psiTrans ψ (burnsideI23x_kappa3 F), marking, hπs, ?_,
    burnsideI23x_scalarCompat hS hψfst (burnsideI23x_kappa3 F), ?_⟩
  · intro γ v
    have h := burnsideI23x_kappa3_lift F A hA hAlin γ (Multiplicative.toAdd (ψ v))
    have h2 : Multiplicative.toAdd (ψ ((marking γ : MulAut V) v)) =
        (burnsideI23x_sd3 F).lift (hA γ) (Multiplicative.toAdd (ψ v)) :=
      congrArg Multiplicative.toAdd (hψact γ v)
    show ((burnsideI23x_kappa3 F (Multiplicative.toAdd (ψ ((marking γ : MulAut V) v))) :
      ↥(zornO0F F)) : quasithinZorn F) = _
    rw [h2]
    exact h
  · refine ⟨hcommon.1, hcommon.2, fun h => absurd rfl h.1, fun h => absurd h.1 (by norm_num),
      fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact (burnsideI23x_SD.isFSubspaceVia_transport ψ (burnsideI23x_kappa3 F) _ 2).1 hscl.1
    · intro v hv
      rw [burnsideI23x_SD.toAdd_psiTrans]
      exact (hκ _).trans (hscl.2.1 v hv)
    · exact hscl.2.2.1
    · exact hscl.2.2.2
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.Explicit
  CFSG.Quasithin.JonesParshall CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model in
theorem burnsideI23x_case_m3 {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    (hL : L = quasithinGenFitting G) (hGT : G = L ⊔ T) (hT : IsSylowTwoOf T G)
    (hGW0 : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) (hW0 : W0 ≤ fixV L) (hcomm : commV L = ⊤)
    (marking : (i23NaturalModel 3 F).Gam →* ↥L)
    (β : V →* ↥(i23NaturalModel 3 F).sec ⧸
      (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec)
    (hsec : I23SectionMap (i23NaturalModel 3 F) L W0 marking β) :
    burnsideI23x_Concl 3 n F V G L T W0 marking β := by
  haveI : Finite (MulAut V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  haveI : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  obtain ⟨c₀, hc0, hc1⟩ := burnsideI23x_exists_ne_zero_one hF hn
  have hLG : L ≤ G := by rw [hL]; exact CFSG.Quasithin.quasithinGenFitting_le G
  have hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have h := CFSG.Quasithin.le_normalizer_quasithinGenFitting G hg
    rw [← hL] at h
    exact (Subgroup.mem_normalizer_iff.1 h l).1 hl
  have hTG : T ≤ G := hT.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht => hnorm t (hTG ht)
  have hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0 := fun t ht => hGW0 t (hTG ht)
  obtain ⟨V1, V2, h1, h2, h12, u1, u2, f1, f2⟩ :=
    burnsideI23x_marked_flags_m3' hn hF hV hsec hW0 hTL hTW0 hP
  have hfixV : fixV L = W0 :=
    burnsideI23x_fixV_eq (burnsideI23x_LM3 F) hsec hW0
      (fun x hx => burnsideI23x_nofix3 F hc0 hc1 x hx)
  obtain ⟨t1, t2, t3⟩ := burnsideI23x_transfer (burnsideI23x_UCg_three hn) hF hV hLG hnorm hGT hT
    hGW0 hW0 hfixV hcomm hsec h1 h2
  have hf := burnsideI23x_isCoord (burnsideI23x_LM3 F) hsec
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hF (by omega) hf hc0 hc1 hP
  refine ⟨V1, V2, h1, h2, u1, u2, ?_⟩
  intro R
  refine ⟨CFSG.ASVolI.ChIJK.centerOf (T ⊓ L), fun _ => ⟨⟨burnsideI23x_ofCayley hc0 hc1
      (g * g2A swap01)⁻¹, ?_⟩, (burnsideI23x_omegaOne_center hF hc0 hc1 hf hg).symm,
      fun _ => rfl⟩, fun h => absurd h.1 (by norm_num),
    fun huniv => ⟨fun h => absurd h (by omega),
      fun _ => burnsideI23x_part1_m3 hn hF hV hsec hT.2.1 hP h1 h2 f1 huniv⟩,
    ⟨t1, (burnsideI23x_centralCoreCompatibility V hV G V1).2 t2.1,
      (burnsideI23x_centralCoreCompatibility V hV G V2).2 t2.2⟩,
    fun hn' => ⟨by rw [hfixV]; exact h1.1, fun hm => absurd rfl hm⟩⟩
  ext x
  exact (burnsideI23x_center_P hF hc0 hc1 hf hg x).trans
    (burnsideI23x_longroot hc0 hc1 marking g x).symm
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_MarkedStmt : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (G L T : Subgroup (MulAut V)) (W0 : Subgroup V) (m n : ℕ),
    L = quasithinGenFitting G → G = L ⊔ T → IsSylowTwoOf T G →
    (∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) → W0 ≤ fixV L → commV L = ⊤ →
    ((m = 1 ∧ 1 < n) ∨ (m = 2 ∧ 0 < n) ∨ (m = 3 ∧ 0 < n)) →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
    ∀ (marking : (i23NaturalModel m F).Gam →* ↥L)
      (β : V →* ↥(i23NaturalModel m F).sec ⧸
        (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec),
      I23SectionMap (i23NaturalModel m F) L W0 marking β →
      burnsideI23x_Concl m n F V G L T W0 marking β

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK in
theorem burnsideI23x_assembly
    (h21 : ∀ {F : Type} [Field F] [Finite F], Nat.card F = 2 ^ 1 →
      ∀ {V : Type} [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ {G L T : Subgroup (MulAut V)} {W0 : Subgroup V},
        L = quasithinGenFitting G → G = L ⊔ T → IsSylowTwoOf T G →
        (∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) → W0 ≤ fixV L → commV L = ⊤ →
        ∀ (marking : (i23NaturalModel 2 F).Gam →* ↥L)
          (β : V →* ↥(i23NaturalModel 2 F).sec ⧸
            (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec),
          I23SectionMap (i23NaturalModel 2 F) L W0 marking β →
          burnsideI23x_Concl 2 1 F V G L T W0 marking β)
    (h31 : ∀ {F : Type} [Field F] [Finite F], Nat.card F = 2 ^ 1 →
      ∀ {V : Type} [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ {G L T : Subgroup (MulAut V)} {W0 : Subgroup V},
        L = quasithinGenFitting G → G = L ⊔ T → IsSylowTwoOf T G →
        (∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) → W0 ≤ fixV L → commV L = ⊤ →
        ∀ (marking : (i23NaturalModel 3 F).Gam →* ↥L)
          (β : V →* ↥(i23NaturalModel 3 F).sec ⧸
            (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec),
          I23SectionMap (i23NaturalModel 3 F) L W0 marking β →
          burnsideI23x_Concl 3 1 F V G L T W0 marking β) :
    burnsideI23x_MarkedStmt := by
  intro V _ _ hV G L T W0 m n hL hGT hT hGW0 hW0 hcomm hcase F _ _ hF marking β hsec
  rcases hcase with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · exact burnsideI23x_case_m1 (by omega) hF hV hL hGT hT hGW0 hW0 hcomm marking β hsec
  · by_cases h1 : n = 1
    · subst h1
      exact h21 hF hV hL hGT hT hGW0 hW0 hcomm marking β hsec
    · exact burnsideI23x_case_m2 (by omega) hF hV hL hGT hT hGW0 hW0 hcomm marking β hsec
  · by_cases h1 : n = 1
    · subst h1
      exact h31 hF hV hL hGT hT hGW0 hW0 hcomm marking β hsec
    · exact burnsideI23x_case_m3 (by omega) hF hV hL hGT hT hGW0 hW0 hcomm marking β hsec
open CFSG.Quasithin CFSG.QuasithinUnique in
open scoped Pointwise in
theorem burnsideI23x_sylow_conj {Y : Type*} [Group Y] [Finite Y] {H A B : Subgroup Y}
    (hA : IsSylowTwoOf A H) (hB : IsSylowTwoOf B H) :
    ∃ g ∈ H, ∀ y : Y, y ∈ B ↔ g⁻¹ * y * g ∈ A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : IsSylowIn 2 A H := hA
  have hB' : IsSylowIn 2 B H := hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H hA'.toSylow hB'.toSylow
  have hcoe : (hB'.toSylow : Subgroup H) = MulAut.conj g • (hA'.toSylow : Subgroup H) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  refine ⟨g.1, g.2, fun y => ?_⟩
  constructor
  · intro hy
    have hyH := hB'.le hy
    have h1 : (⟨y, hyH⟩ : H) ∈ (hB'.toSylow : Subgroup H) := hy
    rw [hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : g⁻¹ * (⟨y, hyH⟩ : H) * g ∈ (hA'.toSylow : Subgroup H) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using h1
    exact h2
  · intro hy
    have hyA : g.1⁻¹ * y * g.1 ∈ H := hA'.le hy
    have hyH : y ∈ H := by
      have := H.mul_mem (H.mul_mem g.2 hyA) (H.inv_mem g.2)
      simpa [mul_assoc] using this
    have h1 : g⁻¹ * (⟨y, hyH⟩ : H) * g ∈ (hA'.toSylow : Subgroup H) := hy
    have h2 : (⟨y, hyH⟩ : H) ∈ (hB'.toSylow : Subgroup H) := by
      rw [hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, MulAut.conj_apply] using h1
    exact h2
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_charP2_of_card {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [hF', pow_one])

noncomputable def burnsideI23x_cF (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2) :
    ZMod 2 ≃+* F :=
  have : Fintype F := Fintype.ofFinite F
  ZMod.ringEquivOfPrime F Nat.prime_two (by rw [← Nat.card_eq_fintype_card, hF])

theorem burnsideI23x_h01 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) (a : F) :
    a = 0 ∨ a = 1 := by
  obtain ⟨x, rfl⟩ := (burnsideI23x_cF F hF).surjective a
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_emb {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    Ix3 → F := fun i => c (w i)

theorem burnsideI23x_emb_bij {F : Type} [Field F] (c : ZMod 2 ≃+* F) :
    Function.Bijective (burnsideI23x_emb c) := by
  refine ⟨fun a b h => ?_, fun v => ⟨fun i => c.symm (v i), ?_⟩⟩
  · funext i
    exact c.injective (congrFun h i)
  · funext i
    simp [burnsideI23x_emb]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_q6 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (a b c' d e f : ZMod 2) :
    burnsideI23x_emb c (q6 a b c' d e f) = q6 (c a) (c b) (c c') (c d) (c e) (c f) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_rx0 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0) + w (.inr 0)) (w (.inl 1)) (w (.inl 2)) (w (.inr 0))
    (w (.inr 1) + w (.inl 2)) (w (.inr 2) + w (.inl 1))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_rx1 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0)) (w (.inl 1) + w (.inr 1)) (w (.inl 2)) (w (.inr 0) + w (.inl 2))
    (w (.inr 1)) (w (.inr 2) + w (.inl 0))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_rx2 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0)) (w (.inl 1)) (w (.inl 2) + w (.inr 2)) (w (.inr 0) + w (.inl 1))
    (w (.inr 1) + w (.inl 0)) (w (.inr 2))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ry0 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0)) (w (.inl 1) + w (.inr 2)) (w (.inl 2) + w (.inr 1)) (w (.inr 0) + w (.inl 0))
    (w (.inr 1)) (w (.inr 2))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ry1 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0) + w (.inr 2)) (w (.inl 1)) (w (.inl 2) + w (.inr 0)) (w (.inr 0))
    (w (.inr 1) + w (.inl 1)) (w (.inr 2))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ry2 {R : Type} [CommRing R] (w : Ix3 → R) : Ix3 → R :=
  q6 (w (.inl 0) + w (.inr 1)) (w (.inl 1) + w (.inr 0)) (w (.inl 2)) (w (.inr 0))
    (w (.inr 1)) (w (.inr 2) + w (.inl 2))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_rtv {R : Type} [CommRing R] (i j : Fin 3) (w : Ix3 → R) : Ix3 → R :=
  w + Pi.single (Sum.inl i) (w (.inl j)) + Pi.single (Sum.inr j) (w (.inr i))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_rx0 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2X ![1, 0, 0]) w = burnsideI23x_rx0 w := by
  rw [g2Act_x0]; rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_rx1 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2X ![0, 1, 0]) w = burnsideI23x_rx1 w := by
  rw [q6_eta w, g2Act_x1q]
  simp [burnsideI23x_rx1, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_rx2 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2X ![0, 0, 1]) w = burnsideI23x_rx2 w := by
  rw [q6_eta w, g2Act_x2q]
  simp [burnsideI23x_rx2, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_ry0 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2Y ![1, 0, 0]) w = burnsideI23x_ry0 w := by
  rw [q6_eta w, g2Act_y0q]
  simp [burnsideI23x_ry0, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_ry1 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2Y ![0, 1, 0]) w = burnsideI23x_ry1 w := by
  rw [q6_eta w, g2Act_y1q]
  simp [burnsideI23x_ry1, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_ry2 {F : Type} [Field F] [CharP F 2] (w : Ix3 → F) :
    g2Act (g2Y ![0, 0, 1]) w = burnsideI23x_ry2 w := by
  rw [q6_eta w, g2Act_y2q]
  simp [burnsideI23x_ry2, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_g2Act_rtv {F : Type} [Field F] [CharP F 2] (i j : Fin 3) (hij : i ≠ j)
    (w : Ix3 → F) : g2Act (g2A (tv i j hij 1)) w = burnsideI23x_rtv i j w := by
  rw [g2Act_tv]
  simp [burnsideI23x_rtv]
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_rx0 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_rx0 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_rx0 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_rx0, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_rx1 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_rx1 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_rx1 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_rx1, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_rx2 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_rx2 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_rx2 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_rx2, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_ry0 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_ry0 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_ry0 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_ry0, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_ry1 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_ry1 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_ry1 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_ry1, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_ry2 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    burnsideI23x_ry2 (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_ry2 w) := by
  funext i; rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_ry2, burnsideI23x_emb, q6]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_rtv {F : Type} [Field F] (c : ZMod 2 ≃+* F) (i j : Fin 3)
    (w : Ix3 → ZMod 2) :
    burnsideI23x_rtv i j (burnsideI23x_emb c w) = burnsideI23x_emb c (burnsideI23x_rtv i j w) := by
  funext k
  rcases k with k | k <;> simp [burnsideI23x_rtv, burnsideI23x_emb, Pi.single_apply] <;>
    split_ifs <;> simp
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_x0y1 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    g2X (![0, 0, 1] : Fin 3 → F) * (g2X (![1, 0, 0] : Fin 3 → F) * g2A (tv 0 2 (by decide) 1)) =
      (g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F)) *
        (g2X (![1, 0, 0] : Fin 3 → F) * g2A (tv 0 2 (by decide) 1)) *
        g2X (![0, 0, 1] : Fin 3 → F) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [g2Act_mul_apply, burnsideI23x_g2Act_rx0, burnsideI23x_g2Act_rx2,
    burnsideI23x_g2Act_ry1, burnsideI23x_g2Act_rtv, burnsideI23x_emb_rx0, burnsideI23x_emb_rx2,
    burnsideI23x_emb_ry1, burnsideI23x_emb_rtv]
  congr 1
  revert w'
  decide
open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideI23x_sylow_desc {Y : Type*} [Group Y] [Finite Y] {G Γ U : Subgroup Y}
    (hΓG : Γ ≤ G) (hnorm : ∀ g ∈ G, ∀ l ∈ Γ, g * l * g⁻¹ ∈ Γ) (hU : IsSylowTwoOf U G)
    {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} (ρ : ↥Γ →* ↥H)
    (hρ : Function.Bijective ρ) {P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) :
    ∃ g : ↥Γ, ∀ x : MulAut V, x ∈ P ↔
      ∃ u : ↥Γ, (u : Y) ∈ U ∧ x = ((ρ (g * u * g⁻¹) : ↥H) : MulAut V) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsSylowTwoOf (U ⊓ Γ) Γ := burnsideI23x_sylow_inf_normal hΓG hnorm hU
  obtain ⟨hPH, hP2, hPi⟩ := hP
  set P' : Subgroup Y := ((P.subgroupOf H).comap ρ).map Γ.subtype with hP'
  have hP'Γ : P' ≤ Γ := Subgroup.map_subtype_le _
  have hP'2 : IsPGroup 2 P' := by
    have h1 : IsPGroup 2 (P.subgroupOf H) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
    exact (h1.comap_of_injective ρ hρ.1).map Γ.subtype
  have hsub : P'.subgroupOf Γ = (P.subgroupOf H).comap ρ := by
    ext x
    simp only [hP', Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_comap,
      Subgroup.subtype_apply]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hP'i : ¬ 2 ∣ (P'.subgroupOf Γ).index := by
    rw [hsub, Subgroup.index_comap_of_surjective _ hρ.2]
    exact hPi
  have hP' : IsSylowTwoOf P' Γ := ⟨hP'Γ, hP'2, hP'i⟩
  obtain ⟨g, hgΓ, hg⟩ := burnsideI23x_sylow_conj hA hP'
  refine ⟨⟨g, hgΓ⟩, fun x => ?_⟩
  constructor
  · intro hx
    have hxH : x ∈ H := hPH hx
    obtain ⟨y, hy⟩ := hρ.2 ⟨x, hxH⟩
    have hyP' : (y : Y) ∈ P' := by
      refine ⟨y, ?_, rfl⟩
      show ρ y ∈ P.subgroupOf H
      rw [hy]
      exact hx
    have hyg := (hg _).1 hyP'
    refine ⟨⟨g⁻¹ * y * g, hyg.2⟩, hyg.1, ?_⟩
    have e : (⟨g, hgΓ⟩ : ↥Γ) * ⟨g⁻¹ * y * g, hyg.2⟩ * (⟨g, hgΓ⟩ : ↥Γ)⁻¹ = y := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [e, hy]
  · rintro ⟨u, hu, rfl⟩
    have hyP' : g * (u : Y) * g⁻¹ ∈ P' := by
      rw [hg]
      simpa [mul_assoc] using (⟨hu, u.2⟩ : (u : Y) ∈ U ⊓ Γ)
    obtain ⟨y, hy, hyx⟩ := hyP'
    have hy' : y = ⟨g, hgΓ⟩ * u * ⟨g, hgΓ⟩⁻¹ := Subtype.ext (by simpa using hyx)
    have h1 : ρ y ∈ P.subgroupOf H := hy
    rw [hy'] at h1
    exact h1
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gam_of_comm {F : Type} [Field F] [CharP F 2] {g h t : ↥(cayleyGroup F)}
    (hgh : g * h = t * h * g) :
    (t : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
  have ht : t = g * h * g⁻¹ * h⁻¹ := by
    rw [hgh]; group
  have hg : (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ quasithinG2 F := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]; exact g.2
  have hh : (h : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ quasithinG2 F := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]; exact h.2
  have := Subgroup.commutator_mem_commutator hg hh
  rw [commutatorElement_def] at this
  rw [ht]
  simpa using this

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gam_mul {F : Type} [Field F] [CharP F 2] {a b : ↥(cayleyGroup F)}
    (ha : (a : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆)
    (hb : (b : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    ((a * b : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      ⁅quasithinG2 F, quasithinG2 F⁆ := Subgroup.mul_mem _ ha hb
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def burnsideI23x_eE {F : Type} [Field F] [CharP F 2] (i j : Fin 3)
    (hij : i ≠ j) : ↥(cayleyGroup F) := g2A (tv i j hij 1)

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_E01 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    burnsideI23x_eE (F := F) 0 2 (by decide) * burnsideI23x_eE 2 1 (by decide) =
      burnsideI23x_eE 0 1 (by decide) * burnsideI23x_eE 2 1 (by decide) *
        burnsideI23x_eE 0 2 (by decide) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [burnsideI23x_eE, g2Act_mul_apply, burnsideI23x_g2Act_rtv, burnsideI23x_emb_rtv]
  congr 1
  revert w'
  decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_E12 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    burnsideI23x_eE (F := F) 1 0 (by decide) * burnsideI23x_eE 0 2 (by decide) =
      burnsideI23x_eE 1 2 (by decide) * burnsideI23x_eE 0 2 (by decide) *
        burnsideI23x_eE 1 0 (by decide) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [burnsideI23x_eE, g2Act_mul_apply, burnsideI23x_g2Act_rtv, burnsideI23x_emb_rtv]
  congr 1
  revert w'
  decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_E02 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    burnsideI23x_eE (F := F) 0 1 (by decide) * burnsideI23x_eE 1 2 (by decide) =
      burnsideI23x_eE 0 2 (by decide) * burnsideI23x_eE 1 2 (by decide) *
        burnsideI23x_eE 0 1 (by decide) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [burnsideI23x_eE, g2Act_mul_apply, burnsideI23x_g2Act_rtv, burnsideI23x_emb_rtv]
  congr 1
  revert w'
  decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_E10 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    burnsideI23x_eE (F := F) 1 2 (by decide) * burnsideI23x_eE 2 0 (by decide) =
      burnsideI23x_eE 1 0 (by decide) * burnsideI23x_eE 2 0 (by decide) *
        burnsideI23x_eE 1 2 (by decide) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [burnsideI23x_eE, g2Act_mul_apply, burnsideI23x_g2Act_rtv, burnsideI23x_emb_rtv]
  congr 1
  revert w'
  decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_E20 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    burnsideI23x_eE (F := F) 2 1 (by decide) * burnsideI23x_eE 1 0 (by decide) =
      burnsideI23x_eE 2 0 (by decide) * burnsideI23x_eE 1 0 (by decide) *
        burnsideI23x_eE 2 1 (by decide) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [burnsideI23x_eE, g2Act_mul_apply, burnsideI23x_g2Act_rtv, burnsideI23x_emb_rtv]
  congr 1
  revert w'
  decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_x0x1 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    g2X (![1, 0, 0] : Fin 3 → F) *
        (burnsideI23x_eE 0 1 (by decide) * burnsideI23x_eE 1 0 (by decide)) =
      (g2X (![1, 0, 0] : Fin 3 → F) * g2X (![0, 1, 0] : Fin 3 → F)) *
        (burnsideI23x_eE 0 1 (by decide) * burnsideI23x_eE 1 0 (by decide)) *
        g2X (![1, 0, 0] : Fin 3 → F) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [burnsideI23x_eE, g2Act_mul_apply, burnsideI23x_g2Act_rx0, burnsideI23x_g2Act_rx1,
    burnsideI23x_g2Act_rtv, burnsideI23x_emb_rx0, burnsideI23x_emb_rx1, burnsideI23x_emb_rtv]
  congr 1
  revert w'
  decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_x0x2 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    g2X (![1, 0, 0] : Fin 3 → F) *
        (burnsideI23x_eE 0 2 (by decide) * burnsideI23x_eE 2 0 (by decide)) =
      (g2X (![1, 0, 0] : Fin 3 → F) * g2X (![0, 0, 1] : Fin 3 → F)) *
        (burnsideI23x_eE 0 2 (by decide) * burnsideI23x_eE 2 0 (by decide)) *
        g2X (![1, 0, 0] : Fin 3 → F) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [burnsideI23x_eE, g2Act_mul_apply, burnsideI23x_g2Act_rx0, burnsideI23x_g2Act_rx2,
    burnsideI23x_g2Act_rtv, burnsideI23x_emb_rx0, burnsideI23x_emb_rx2, burnsideI23x_emb_rtv]
  congr 1
  revert w'
  decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_x0y0 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    g2X (![1, 0, 0] : Fin 3 → F) * (g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![1, 0, 0] : Fin 3 → F)) =
      (g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![1, 0, 0] : Fin 3 → F)) *
        (g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![1, 0, 0] : Fin 3 → F)) *
        g2X (![1, 0, 0] : Fin 3 → F) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [g2Act_mul_apply, burnsideI23x_g2Act_rx0, burnsideI23x_g2Act_ry0,
    burnsideI23x_emb_rx0, burnsideI23x_emb_ry0]
  congr 1
  revert w'
  decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_id_x1y1 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    g2X (![0, 1, 0] : Fin 3 → F) * (g2X (![0, 1, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F)) =
      (g2X (![0, 1, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F)) *
        (g2X (![0, 1, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F)) *
        g2X (![0, 1, 0] : Fin 3 → F) := by
  apply cayley_ext
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 w
  simp only [g2Act_mul_apply, burnsideI23x_g2Act_rx1, burnsideI23x_g2Act_ry1,
    burnsideI23x_emb_rx1, burnsideI23x_emb_ry1]
  congr 1
  revert w'
  decide
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_marking_bij3 {F : Type} [Field F] [CharP F 2] {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 3 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 3 F).sec ⧸
      (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec}
    (hsec : I23SectionMap (i23NaturalModel 3 F) L W0 marking β) :
    Function.Bijective marking := by
  have hf := burnsideI23x_isCoord (burnsideI23x_LM3 F) hsec
  refine ⟨?_, hsec.1⟩
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply burnsideI23x_hfaith3
  intro x
  obtain ⟨v, rfl⟩ := hf.surj x
  rw [← hf.act, hγ]
  rfl

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.ASVolI.ChIJK in
theorem burnsideI23x_U0_sylow {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    IsSylowTwoOf ((U0 F).map (cayleyGroup F).subtype) (cayleyGroup F) := by
  refine ⟨Subgroup.map_subtype_le _, (isPGroup_U0 (F := F)).map _, ?_⟩
  have h := not_two_dvd_index_U0 hF hn
  have e : ((U0 F).map (cayleyGroup F).subtype).subgroupOf (cayleyGroup F) = U0 F := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.subtype_apply]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [e]
  exact h

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
open scoped commutatorElement in
theorem burnsideI23x_gam_norm {F : Type} [Field F] [CharP F 2] :
    ∀ g ∈ cayleyGroup F, ∀ l ∈ ⁅quasithinG2 F, quasithinG2 F⁆,
      g * l * g⁻¹ ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
  intro g hg l hl
  have hq : quasithinG2 F = cayleyGroup F :=
    CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup
  have hgq : g ∈ quasithinG2 F := by rw [hq]; exact hg
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have := Subgroup.commutator_mem_commutator (H₁ := quasithinG2 F) (H₂ := quasithinG2 F)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgq ha) (Subgroup.inv_mem _ hgq))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgq hb) (Subgroup.inv_mem _ hgq))
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact this
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx
theorem burnsideI23x_card_four {N : Type*} [AddCommGroup N] (h2 : ∀ x : N, x + x = 0)
    (X : AddSubgroup N) (hX : Nat.card ↥X = 4) :
    ∃ a b : N, a ∈ X ∧ b ∈ X ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      ∀ x : N, x ∈ X ↔ (x = 0 ∨ x = a ∨ x = b ∨ x = a + b) := by
  classical
  haveI : Finite ↥X := Nat.finite_of_card_ne_zero (by omega)
  have hXfin : (X : Set N).Finite := Set.toFinite _
  have hcard : (X : Set N).ncard = 4 := by
    rw [← hX]; exact (Nat.card_coe_set_eq _).symm
  obtain ⟨⟨a, ha⟩, hane⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1
    (show X ≠ ⊥ by
      intro h; rw [h] at hX; simp at hX)
  have ha0 : a ≠ 0 := fun h => hane (Subtype.ext h)
  have hb : ∃ b ∈ X, b ≠ 0 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (X : Set N) ⊆ {0, a} := by
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · by_cases hxa : x = a
        · simp [hxa]
        · exact absurd (hcon x hx hx0) hxa
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2le : ({0, a} : Set N).ncard ≤ 2 := by
      have := Set.ncard_insert_le (0 : N) ({a} : Set N)
      rw [Set.ncard_singleton] at this
      exact this
    omega
  obtain ⟨b, hbX, hb0, hba⟩ := hb
  have hab : a + b ≠ 0 := by
    intro h
    apply hba
    have h1 : b = a := by
      have := h2 a
      calc b = (a + b) - a := by abel
        _ = 0 - a := by rw [h]
        _ = a := by rw [zero_sub, neg_eq_of_add_eq_zero_right this]
    exact h1
  have hab1 : a + b ≠ a := fun h => hb0 (by simpa using h)
  have hab2 : a + b ≠ b := fun h => ha0 (by simpa using h)
  refine ⟨a, b, ha, hbX, ha0, hb0, hba.symm, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨hx0, hxa, hxb, hxab⟩ := hcon
    have hsub : ({x, a + b, b, a, 0} : Set N) ⊆ X := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact hx
      · exact X.add_mem ha hbX
      · exact hbX
      · exact ha
      · exact X.zero_mem
    have h5 : ({x, a + b, b, a, 0} : Set N).ncard = 5 := by
      rw [Set.ncard_insert_of_notMem (by simp; tauto) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp; tauto) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp; tauto) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp; tauto) (Set.toFinite _), Set.ncard_singleton]
    have := Set.ncard_le_ncard hsub hXfin
    omega
  · rcases hx with rfl | rfl | rfl | rfl
    · exact X.zero_mem
    · exact ha
    · exact hbX
    · exact X.add_mem ha hbX
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_eu0 : Ix3 → ZMod 2 := q6 1 0 0 0 0 0

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_eu0 {F : Type} [Field F] (c : ZMod 2 ≃+* F) :
    burnsideI23x_emb c burnsideI23x_eu0 = eu 0 1 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [burnsideI23x_emb, burnsideI23x_eu0, q6, eu,
    Pi.single_apply]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_fix_P1 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) (x : Ix3 → F)
    (h1 : burnsideI23x_rtv 0 1 x = x) (h2 : burnsideI23x_rtv 1 2 x = x)
    (h3 : burnsideI23x_rx0 (burnsideI23x_ry1 x) = x) : x = 0 ∨ x = eu 0 1 := by
  obtain ⟨w, rfl⟩ := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).2 x
  rw [burnsideI23x_emb_rtv] at h1 h2
  rw [burnsideI23x_emb_ry1, burnsideI23x_emb_rx0] at h3
  have e1 := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).1 h1
  have e2 := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).1 h2
  have e3 := (burnsideI23x_emb_bij (burnsideI23x_cF F hF)).1 h3
  have key : ∀ w : Ix3 → ZMod 2, burnsideI23x_rtv 0 1 w = w → burnsideI23x_rtv 1 2 w = w →
      burnsideI23x_rx0 (burnsideI23x_ry1 w) = w → w = 0 ∨ w = burnsideI23x_eu0 := by decide
  rcases key w e1 e2 e3 with rfl | rfl
  · left; funext i; simp [burnsideI23x_emb]
  · right; exact burnsideI23x_emb_eu0 _
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ev2 : Ix3 → ZMod 2 := q6 0 0 0 0 0 1

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
abbrev burnsideI23x_inSpan (a b x : Ix3 → ZMod 2) : Prop := x = 0 ∨ x = a ∨ x = b ∨ x = a + b

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
abbrev burnsideI23x_PlaneInv (a b : Ix3 → ZMod 2) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
    burnsideI23x_inSpan a b (burnsideI23x_rtv 0 1 a) ∧
    burnsideI23x_inSpan a b (burnsideI23x_rtv 0 1 b) ∧
    burnsideI23x_inSpan a b (burnsideI23x_rtv 1 2 a) ∧
    burnsideI23x_inSpan a b (burnsideI23x_rtv 1 2 b) ∧
    burnsideI23x_inSpan a b (burnsideI23x_rx0 (burnsideI23x_ry1 a)) ∧
    burnsideI23x_inSpan a b (burnsideI23x_rx0 (burnsideI23x_ry1 b))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
set_option synthInstance.maxSize 4096 in
theorem burnsideI23x_plane_P1 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (X : AddSubgroup (Ix3 → F)) (hX : Nat.card ↥X = 4)
    (h1 : ∀ x ∈ X, burnsideI23x_rtv 0 1 x ∈ X) (h2 : ∀ x ∈ X, burnsideI23x_rtv 1 2 x ∈ X)
    (h3 : ∀ x ∈ X, burnsideI23x_rx0 (burnsideI23x_ry1 x) ∈ X) :
    X = (stdF F 2).toAddSubgroup := by
  have hdbl : ∀ x : Ix3 → F, x + x = 0 := fun x => by
    funext i; exact CharTwo.add_self_eq_zero _
  obtain ⟨a, b, ha, hb, ha0, hb0, hab, hmem⟩ := burnsideI23x_card_four hdbl X hX
  have hc := burnsideI23x_cF F hF
  obtain ⟨a', rfl⟩ := (burnsideI23x_emb_bij hc).2 a
  obtain ⟨b', rfl⟩ := (burnsideI23x_emb_bij hc).2 b
  have hemb : ∀ w w' : Ix3 → ZMod 2, burnsideI23x_emb hc w + burnsideI23x_emb hc w' =
      burnsideI23x_emb hc (w + w') := fun w w' => by
    funext i; simp [burnsideI23x_emb]
  have hemb0 : burnsideI23x_emb hc 0 = 0 := by funext i; simp [burnsideI23x_emb]
  have hinj := (burnsideI23x_emb_bij hc).1
  have tr : ∀ (p : (Ix3 → F) → (Ix3 → F)) (p' : (Ix3 → ZMod 2) → (Ix3 → ZMod 2)),
      (∀ w, p (burnsideI23x_emb hc w) = burnsideI23x_emb hc (p' w)) →
      (∀ x ∈ X, p x ∈ X) →
      ∀ w, burnsideI23x_emb hc w ∈ X → p' w = 0 ∨ p' w = a' ∨ p' w = b' ∨ p' w = a' + b' := by
    intro p p' hp hpX w hw
    have := hpX _ hw
    rw [hp, hmem] at this
    rcases this with h | h | h | h
    · left; exact hinj (by rw [h, hemb0])
    · right; left; exact hinj h
    · right; right; left; exact hinj h
    · right; right; right; exact hinj (by rw [h, ← hemb])
  have ha' : burnsideI23x_emb hc a' ∈ X := ha
  have hb' : burnsideI23x_emb hc b' ∈ X := hb
  have t1a := tr _ _ (fun w => burnsideI23x_emb_rtv hc 0 1 w) h1 a' ha'
  have t1b := tr _ _ (fun w => burnsideI23x_emb_rtv hc 0 1 w) h1 b' hb'
  have t2a := tr _ _ (fun w => burnsideI23x_emb_rtv hc 1 2 w) h2 a' ha'
  have t2b := tr _ _ (fun w => burnsideI23x_emb_rtv hc 1 2 w) h2 b' hb'
  have t3a := tr (fun x => burnsideI23x_rx0 (burnsideI23x_ry1 x))
    (fun w => burnsideI23x_rx0 (burnsideI23x_ry1 w))
    (fun w => by rw [burnsideI23x_emb_ry1, burnsideI23x_emb_rx0]) h3 a' ha'
  have t3b := tr (fun x => burnsideI23x_rx0 (burnsideI23x_ry1 x))
    (fun w => burnsideI23x_rx0 (burnsideI23x_ry1 w))
    (fun w => by rw [burnsideI23x_emb_ry1, burnsideI23x_emb_rx0]) h3 b' hb'
  have a0' : a' ≠ 0 := fun h => ha0 (by rw [h, hemb0])
  have b0' : b' ≠ 0 := fun h => hb0 (by rw [h, hemb0])
  have ab' : a' ≠ b' := fun h => hab (by rw [h])
  have key : ∀ a b : Ix3 → ZMod 2, burnsideI23x_PlaneInv a b →
      ∀ x : Ix3 → ZMod 2, burnsideI23x_inSpan a b x ↔
        burnsideI23x_inSpan burnsideI23x_eu0 burnsideI23x_ev2 x := by decide +kernel
  have hk := key a' b' ⟨a0', b0', ab', t1a, t1b, t2a, t2b, t3a, t3b⟩
  ext x
  obtain ⟨x', rfl⟩ := (burnsideI23x_emb_bij hc).2 x
  rw [hmem]
  have hspan : ∀ y : Ix3 → ZMod 2, burnsideI23x_inSpan burnsideI23x_eu0 burnsideI23x_ev2 y ↔
      (y (.inl 1) = 0 ∧ y (.inl 2) = 0 ∧ y (.inr 0) = 0 ∧ y (.inr 1) = 0) := by decide
  have hc0 : ∀ y : ZMod 2, hc y = 0 ↔ y = 0 := fun y => by
    rw [← map_zero hc]; exact hc.injective.eq_iff
  have h1 : (burnsideI23x_emb hc x' = 0 ∨ burnsideI23x_emb hc x' = burnsideI23x_emb hc a' ∨
      burnsideI23x_emb hc x' = burnsideI23x_emb hc b' ∨
      burnsideI23x_emb hc x' = burnsideI23x_emb hc a' + burnsideI23x_emb hc b') ↔
      burnsideI23x_inSpan a' b' x' := by
    rw [hemb]
    rw [← hemb0]
    simp only [hinj.eq_iff]
  rw [h1, hk x', hspan]
  show _ ↔ burnsideI23x_emb hc x' ∈ stdF F 2
  rw [mem_stdF_two]
  simp only [burnsideI23x_emb, hc0]
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
structure burnsideI23x_ZE {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) where
  g : ↥(cayleyGroup F)
  f : (Ix3 → ZMod 2) → (Ix3 → ZMod 2)
  hf : ∀ w, g2Act g (burnsideI23x_emb c w) = burnsideI23x_emb c (f w)

namespace burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def mul {F : Type} [Field F] [CharP F 2] {c : ZMod 2 ≃+* F} (A B : burnsideI23x_ZE c) :
    burnsideI23x_ZE c where
  g := A.g * B.g
  f := fun w => A.f (B.f w)
  hf := fun w => by rw [g2Act_mul_apply, B.hf, A.hf]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem g_eq_iff {F : Type} [Field F] [CharP F 2] {c : ZMod 2 ≃+* F} (A B : burnsideI23x_ZE c) :
    A.g = B.g ↔ ∀ w, A.f w = B.f w := by
  constructor
  · intro h w
    have h1 := A.hf w
    rw [h] at h1
    rw [B.hf] at h1
    exact ((burnsideI23x_emb_bij c).1 h1).symm
  · intro h
    apply cayley_ext
    intro w
    obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij c).2 w
    rw [A.hf, B.hf, h]

end burnsideI23x_ZE
namespace burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def x0 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2X (![1, 0, 0] : Fin 3 → F)
  f := burnsideI23x_rx0
  hf := fun w => by rw [burnsideI23x_g2Act_rx0, burnsideI23x_emb_rx0]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def x1 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2X (![0, 1, 0] : Fin 3 → F)
  f := burnsideI23x_rx1
  hf := fun w => by rw [burnsideI23x_g2Act_rx1, burnsideI23x_emb_rx1]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def x2 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2X (![0, 0, 1] : Fin 3 → F)
  f := burnsideI23x_rx2
  hf := fun w => by rw [burnsideI23x_g2Act_rx2, burnsideI23x_emb_rx2]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def y0 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2Y (![1, 0, 0] : Fin 3 → F)
  f := burnsideI23x_ry0
  hf := fun w => by rw [burnsideI23x_g2Act_ry0, burnsideI23x_emb_ry0]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def y1 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2Y (![0, 1, 0] : Fin 3 → F)
  f := burnsideI23x_ry1
  hf := fun w => by rw [burnsideI23x_g2Act_ry1, burnsideI23x_emb_ry1]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def y2 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) : burnsideI23x_ZE c where
  g := g2Y (![0, 0, 1] : Fin 3 → F)
  f := burnsideI23x_ry2
  hf := fun w => by rw [burnsideI23x_g2Act_ry2, burnsideI23x_emb_ry2]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def tvE {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) (i j : Fin 3)
    (hij : i ≠ j) : burnsideI23x_ZE c where
  g := g2A (tv i j hij 1)
  f := burnsideI23x_rtv i j
  hf := fun w => by rw [burnsideI23x_g2Act_rtv, burnsideI23x_emb_rtv]

end burnsideI23x_ZE
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_zact {R : Type} [CommRing R] (α β γ a b c : R) (w : Ix3 → R) :
    Ix3 → R :=
  q6 (w (.inl 0) + a * w (.inl 1) + b * w (.inl 2) + (γ + β * c) * w (.inr 1) +
      (γ * a + β * b + β * a * c + α ^ 2) * w (.inr 0) + β * w (.inr 2))
    (w (.inl 1) + c * w (.inl 2) + γ * w (.inr 0))
    (w (.inl 2) + β * w (.inr 0))
    (w (.inr 0))
    (w (.inr 1) + (a + α * β) * w (.inr 0) + (β * γ + β ^ 2 * c + α) * w (.inl 2) +
      β ^ 2 * w (.inl 1))
    (w (.inr 2) + c * w (.inr 1) + (b + a * c + α * γ) * w (.inr 0) +
      (γ ^ 2 + β * γ * c + α * c) * w (.inl 2) + (β * γ + α) * w (.inl 1))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_g2Act_zact {F : Type} [Field F] [CharP F 2] (α β γ a b c : F)
    (w : Ix3 → F) :
    g2Act (g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A (uSL a b c)) w =
      burnsideI23x_zact α β γ a b c w := burnsideI23x_g2Act_u0 α β γ a b c w

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_emb_zact {F : Type} [Field F] (c : ZMod 2 ≃+* F) (α β γ a b c' : ZMod 2)
    (w : Ix3 → ZMod 2) :
    burnsideI23x_zact (c α) (c β) (c γ) (c a) (c b) (c c') (burnsideI23x_emb c w) =
      burnsideI23x_emb c (burnsideI23x_zact α β γ a b c' w) := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp only [burnsideI23x_zact, burnsideI23x_emb, q6, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, map_add, map_mul, map_pow]

namespace burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
@[expose] noncomputable def stab {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (α β γ a b c' : ZMod 2) : burnsideI23x_ZE c where
  g := g2X ![c α, 0, 0] * g2Y ![0, c β, c γ] * g2A (uSL (c a) (c b) (c c'))
  f := burnsideI23x_zact α β γ a b c'
  hf := fun w => by
    rw [burnsideI23x_g2Act_zact, burnsideI23x_emb_zact]

end burnsideI23x_ZE
namespace burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem gam {F : Type} [Field F] [CharP F 2] {c : ZMod 2 ≃+* F} (A B T : burnsideI23x_ZE c)
    (h : ∀ w, A.f (B.f w) = T.f (B.f (A.f w))) :
    (T.g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
  apply burnsideI23x_gam_of_comm (g := A.g) (h := B.g)
  have := (g_eq_iff (mul A B) (mul (mul T B) A)).2 (fun w => h w)
  exact this

end burnsideI23x_ZE

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gam_tvE {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) (i j : Fin 3)
    (hij : i ≠ j) :
    ((burnsideI23x_ZE.tvE c i j hij).g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      ⁅quasithinG2 F, quasithinG2 F⁆ := by
  obtain ⟨k, hki, hkj⟩ := exists_third i j
  apply burnsideI23x_ZE.gam (burnsideI23x_ZE.tvE c i k (Ne.symm hki))
    (burnsideI23x_ZE.tvE c k j hkj)
  intro w
  have key : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j → ∀ w : Ix3 → ZMod 2,
      burnsideI23x_rtv i k (burnsideI23x_rtv k j w) =
        burnsideI23x_rtv i j (burnsideI23x_rtv k j (burnsideI23x_rtv i k w)) := by
    decide +kernel
  exact key i j k hij hki hkj w

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gam_x0y1 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) :
    ((burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.y1 c)).g :
      quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
  apply burnsideI23x_ZE.gam (burnsideI23x_ZE.x2 c)
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.tvE c 0 2 (by decide)))
  intro w
  have key : ∀ w : Ix3 → ZMod 2,
      burnsideI23x_rx2 (burnsideI23x_rx0 (burnsideI23x_rtv 0 2 w)) =
        burnsideI23x_rx0 (burnsideI23x_ry1 (burnsideI23x_rx0 (burnsideI23x_rtv 0 2
          (burnsideI23x_rx2 w)))) := by decide +kernel
  exact key w
open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gam_x0x1 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) :
    ((burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.x1 c)).g :
      quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
  apply burnsideI23x_ZE.gam (burnsideI23x_ZE.x0 c)
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.tvE c 0 1 (by decide))
      (burnsideI23x_ZE.tvE c 1 0 (by decide)))
  intro w
  have key : ∀ w : Ix3 → ZMod 2,
      burnsideI23x_rx0 (burnsideI23x_rtv 0 1 (burnsideI23x_rtv 1 0 w)) =
        burnsideI23x_rx0 (burnsideI23x_rx1 (burnsideI23x_rtv 0 1 (burnsideI23x_rtv 1 0
          (burnsideI23x_rx0 w)))) := by decide +kernel
  exact key w

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gam_x0x2 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) :
    ((burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.x2 c)).g :
      quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
  apply burnsideI23x_ZE.gam (burnsideI23x_ZE.x0 c)
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.tvE c 0 2 (by decide))
      (burnsideI23x_ZE.tvE c 2 0 (by decide)))
  intro w
  have key : ∀ w : Ix3 → ZMod 2,
      burnsideI23x_rx0 (burnsideI23x_rtv 0 2 (burnsideI23x_rtv 2 0 w)) =
        burnsideI23x_rx0 (burnsideI23x_rx2 (burnsideI23x_rtv 0 2 (burnsideI23x_rtv 2 0
          (burnsideI23x_rx0 w)))) := by decide +kernel
  exact key w

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gam_x0y0 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) :
    ((burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.y0 c)).g :
      quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
  apply burnsideI23x_ZE.gam (burnsideI23x_ZE.x0 c)
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.y0 c))
  intro w
  have key : ∀ w : Ix3 → ZMod 2,
      burnsideI23x_rx0 (burnsideI23x_rx0 (burnsideI23x_ry0 w)) =
        burnsideI23x_rx0 (burnsideI23x_ry0 (burnsideI23x_rx0 (burnsideI23x_ry0
          (burnsideI23x_rx0 w)))) := by decide +kernel
  exact key w

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gam_x1y1 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F) :
    ((burnsideI23x_ZE.mul (burnsideI23x_ZE.x1 c) (burnsideI23x_ZE.y1 c)).g :
      quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆ := by
  apply burnsideI23x_ZE.gam (burnsideI23x_ZE.x1 c)
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.x1 c) (burnsideI23x_ZE.y1 c))
  intro w
  have key : ∀ w : Ix3 → ZMod 2,
      burnsideI23x_rx1 (burnsideI23x_rx1 (burnsideI23x_ry1 w)) =
        burnsideI23x_rx1 (burnsideI23x_ry1 (burnsideI23x_rx1 (burnsideI23x_ry1
          (burnsideI23x_rx1 w)))) := by decide +kernel
  exact key w

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_toGam {F : Type} [Field F] [CharP F 2] (g : ↥(cayleyGroup F))
    (h : (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    ↥⁅quasithinG2 F, quasithinG2 F⁆ := ⟨g, h⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_toCayley_toGam {F : Type} [Field F] [CharP F 2] (g : ↥(cayleyGroup F))
    (h : (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    burnsideI23x_toCayley (burnsideI23x_toGam g h) = g := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_lin_toGam {F : Type} [Field F] [CharP F 2] (g : ↥(cayleyGroup F))
    (h : (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆)
    (x : Ix3 → F) : (burnsideI23x_LM3 F).lin (burnsideI23x_toGam g h) x = g2Act g x := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_swap01_eq {F : Type} [Field F] [CharP F 2] :
    (swap01 : SL3 F) = tv 0 1 (by decide) 1 * tv 1 0 (by decide) 1 * tv 0 1 (by decide) 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have h1 : ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := rfl
  have hA : ∀ i j (hij : i ≠ j), ((tv i j hij 1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      1 + Matrix.single i j 1 := fun i j hij => rfl
  rw [h1]
  simp only [hA]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      CharTwo.two_eq_zero] <;>
    first | exact CharTwo.two_eq_zero | exact CharTwo.two_eq_zero.symm |
      exact CharTwo.add_self_eq_zero (1 : F) | exact (CharTwo.add_self_eq_zero (1 : F)).symm

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_embHom {F : Type} [Field F] (c : ZMod 2 ≃+* F) :
    (Ix3 → ZMod 2) →+ (Ix3 → F) where
  toFun := burnsideI23x_emb c
  map_zero' := by funext i; simp [burnsideI23x_emb]
  map_add' a b := by funext i; simp [burnsideI23x_emb]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_lin3_one {F : Type} [Field F] [CharP F 2] (x : Ix3 → F) :
    (burnsideI23x_LM3 F).lin (1 : (i23NaturalModel 3 F).Gam) x = x := by
  show g2Act (1 : ↥(cayleyGroup F)) x = x
  rw [map_one]
  rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_vspan : Fin 6 → (Ix3 → ZMod 2) :=
  ![q6 1 0 0 0 0 0, q6 1 1 0 0 0 0, q6 1 0 1 0 0 0, q6 1 0 0 0 0 1, q6 1 0 0 0 1 0,
    q6 0 0 0 1 0 0]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_vspan_span : ∀ w : Ix3 → ZMod 2, ∃ s : Fin 6 → Bool,
    w = ∑ i, if s i then burnsideI23x_vspan i else 0 := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_orbit_u0 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (i : Fin 6) : ∃ γ : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      (burnsideI23x_LM3 F).lin γ (burnsideI23x_emb (burnsideI23x_cF F hF) burnsideI23x_eu0) =
        burnsideI23x_emb (burnsideI23x_cF F hF) (burnsideI23x_vspan i) := by
  set c := burnsideI23x_cF F hF with hc
  fin_cases i
  · exact ⟨1, burnsideI23x_lin3_one _⟩
  · refine ⟨burnsideI23x_toGam (burnsideI23x_ZE.tvE c 1 0 (by decide)).g
      (burnsideI23x_gam_tvE c 1 0 (by decide)), ?_⟩
    have e : burnsideI23x_rtv 1 0 burnsideI23x_eu0 = burnsideI23x_vspan 1 := by decide
    rw [burnsideI23x_lin_toGam, (burnsideI23x_ZE.tvE c 1 0 (by decide)).hf]
    exact congrArg _ e
  · refine ⟨burnsideI23x_toGam (burnsideI23x_ZE.tvE c 2 0 (by decide)).g
      (burnsideI23x_gam_tvE c 2 0 (by decide)), ?_⟩
    have e : burnsideI23x_rtv 2 0 burnsideI23x_eu0 = burnsideI23x_vspan 2 := by decide
    rw [burnsideI23x_lin_toGam, (burnsideI23x_ZE.tvE c 2 0 (by decide)).hf]
    exact congrArg _ e
  · refine ⟨burnsideI23x_toGam (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
      (burnsideI23x_ZE.x1 c)).g (burnsideI23x_gam_x0x1 c), ?_⟩
    have e : burnsideI23x_rx0 (burnsideI23x_rx1 burnsideI23x_eu0) = burnsideI23x_vspan 3 := by
      decide
    rw [burnsideI23x_lin_toGam, (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
      (burnsideI23x_ZE.x1 c)).hf]
    exact congrArg _ e
  · refine ⟨burnsideI23x_toGam (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
      (burnsideI23x_ZE.x2 c)).g (burnsideI23x_gam_x0x2 c), ?_⟩
    have e : burnsideI23x_rx0 (burnsideI23x_rx2 burnsideI23x_eu0) = burnsideI23x_vspan 4 := by
      decide
    rw [burnsideI23x_lin_toGam, (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
      (burnsideI23x_ZE.x2 c)).hf]
    exact congrArg _ e
  · refine ⟨burnsideI23x_toGam (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
      (burnsideI23x_ZE.y0 c)).g (burnsideI23x_gam_x0y0 c), ?_⟩
    have e : burnsideI23x_rx0 (burnsideI23x_ry0 burnsideI23x_eu0) = burnsideI23x_vspan 5 := by
      decide
    rw [burnsideI23x_lin_toGam, (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
      (burnsideI23x_ZE.y0 c)).hf]
    exact congrArg _ e

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_fix_gens {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (x : Ix3 → F)
    (h1 : (burnsideI23x_LM3 F).lin (burnsideI23x_toGam
      (burnsideI23x_ZE.tvE (burnsideI23x_cF F hF) 0 1 (by decide)).g
      (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 0 1 (by decide))) x = x)
    (h2 : (burnsideI23x_LM3 F).lin (burnsideI23x_toGam
      (burnsideI23x_ZE.tvE (burnsideI23x_cF F hF) 1 2 (by decide)).g
      (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 1 2 (by decide))) x = x)
    (h3 : (burnsideI23x_LM3 F).lin (burnsideI23x_toGam
      (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 (burnsideI23x_cF F hF))
        (burnsideI23x_ZE.y1 (burnsideI23x_cF F hF))).g
      (burnsideI23x_gam_x0y1 (burnsideI23x_cF F hF))) x = x) :
    x = 0 ∨ x = eu 0 1 := by
  rw [burnsideI23x_lin_toGam] at h1 h2 h3
  refine burnsideI23x_fix_P1 hF x ?_ ?_ ?_
  · rw [← burnsideI23x_g2Act_rtv 0 1 (by decide) x]; exact h1
  · rw [← burnsideI23x_g2Act_rtv 1 2 (by decide) x]; exact h2
  · rw [← burnsideI23x_g2Act_rx0 (burnsideI23x_ry1 x), ← burnsideI23x_g2Act_ry1 x,
      ← g2Act_mul_apply]
    exact h3

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_hEnd3_one {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (T : (Ix3 → F) →+ (Ix3 → F))
    (hT : ∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
      T ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (T x)) :
    ∃ c : F, ∀ x, T x = c • x := by
  set c := burnsideI23x_cF F hF with hc
  have hu0 : burnsideI23x_emb c burnsideI23x_eu0 = eu 0 1 := burnsideI23x_emb_eu0 c
  have hfixu : ∀ A : burnsideI23x_ZE c, ∀ h : (A.g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      ⁅quasithinG2 F, quasithinG2 F⁆, A.f burnsideI23x_eu0 = burnsideI23x_eu0 →
      (burnsideI23x_LM3 F).lin (burnsideI23x_toGam A.g h) (T (eu 0 1)) = T (eu 0 1) := by
    intro A h hA
    rw [← hT, burnsideI23x_lin_toGam, ← hu0, A.hf, hA]
  have k1 : burnsideI23x_rtv 0 1 burnsideI23x_eu0 = burnsideI23x_eu0 := by decide
  have k2 : burnsideI23x_rtv 1 2 burnsideI23x_eu0 = burnsideI23x_eu0 := by decide
  have k3 : burnsideI23x_rx0 (burnsideI23x_ry1 burnsideI23x_eu0) = burnsideI23x_eu0 := by decide
  have hz := burnsideI23x_fix_gens hF (T (eu 0 1))
    (hfixu (burnsideI23x_ZE.tvE c 0 1 (by decide)) _ k1)
    (hfixu (burnsideI23x_ZE.tvE c 1 2 (by decide)) _ k2)
    (hfixu (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.y1 c)) _ k3)
  obtain ⟨c0, hc0⟩ : ∃ c0 : F, T (eu 0 1) = c0 • eu 0 1 := by
    rcases hz with h | h
    · exact ⟨0, by rw [h, zero_smul]⟩
    · exact ⟨1, by rw [h, one_smul]⟩
  have hc0' : T (burnsideI23x_emb c burnsideI23x_eu0) = c0 • burnsideI23x_emb c burnsideI23x_eu0 := by
    rw [hu0]; exact hc0
  have horb : ∀ i : Fin 6, T (burnsideI23x_emb c (burnsideI23x_vspan i)) =
      c0 • burnsideI23x_emb c (burnsideI23x_vspan i) := by
    intro i
    obtain ⟨γ, hγ⟩ := burnsideI23x_orbit_u0 hF i
    rw [← hγ, hT, hc0', map_smul]
  let K0 : AddSubgroup (Ix3 → F) :=
    { carrier := {x | T x = c0 • x}
      add_mem' := fun {x y} hx hy => by
        show T (x + y) = c0 • (x + y)
        rw [map_add, show T x = c0 • x from hx, show T y = c0 • y from hy, smul_add]
      zero_mem' := by
        show T 0 = c0 • (0 : Ix3 → F)
        rw [map_zero, smul_zero]
      neg_mem' := fun {x} hx => by
        show T (-x) = c0 • (-x)
        rw [map_neg, show T x = c0 • x from hx, smul_neg] }
  let K : AddSubgroup (Ix3 → ZMod 2) := K0.comap (burnsideI23x_embHom c)
  have hK : ∀ i, burnsideI23x_vspan i ∈ K := fun i => horb i
  have hKall : ∀ w : Ix3 → ZMod 2, w ∈ K := by
    intro w
    obtain ⟨s, rfl⟩ := burnsideI23x_vspan_span w
    refine AddSubgroup.sum_mem K (fun i _ => ?_)
    split_ifs
    · exact hK i
    · exact K.zero_mem
  refine ⟨c0, fun x => ?_⟩
  obtain ⟨w, rfl⟩ := (burnsideI23x_emb_bij c).2 x
  exact hKall w

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_nofix3_one {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (x : Ix3 → F) (hx : ∀ γ : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      (burnsideI23x_LM3 F).lin γ x = x) : x = 0 := by
  set c := burnsideI23x_cF F hF with hc
  rcases burnsideI23x_fix_gens hF x (hx _) (hx _) (hx _) with h | h
  · exact h
  · exfalso
    obtain ⟨γ, hγ⟩ := burnsideI23x_orbit_u0 hF 1
    have h1 := hx γ
    rw [h, ← burnsideI23x_emb_eu0 c, hγ] at h1
    have h2 := (burnsideI23x_emb_bij c).1 h1
    revert h2
    decide

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_isFlagW_pre1 {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1) {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 3 F).Gam →* ↥L} {f : V → (Ix3 → F)}
    (hf : IsCoord (burnsideI23x_LM3 F) L W0 marking f)
    (hcomm : ∀ T : (Ix3 → F) →+ (Ix3 → F),
      (∀ (γ : (i23NaturalModel 3 F).Gam) (x : Ix3 → F),
        T ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    {P : Subgroup (MulAut V)} {g : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      burnsideI23x_toCayley u ∈ U0 F ∧ x = ((marking (g * u * g⁻¹) : ↥L) : MulAut V))
    {S : Submodule F (Ix3 → F)} (hS : U0Stable S) {i : ℕ} (hcard : Nat.card S = Nat.card F ^ i) :
    IsFlagW L P W0 (Nat.card F) i
      (hf.pre (gmapG (burnsideI23x_toCayley g) S).toAddSubgroup) := by
  refine ⟨hf.le_pre _, ?_, ?_, fun x hx => ?_⟩
  · rw [hf.endStableW_iff hV hcomm (hf.le_pre _), hf.img_pre]
    exact fun c x hx => (gmapG (burnsideI23x_toCayley g) S).smul_mem c hx
  · rw [← hf.card_img, hf.img_pre, ← hcard, ← card_gmapG (burnsideI23x_toCayley g) S]
    rfl
  · obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
    rw [IsCoord.mem_stabW_iff hf (hf.le_pre _) (g * u * g⁻¹), hf.img_pre]
    intro y
    change y ∈ gmapG (burnsideI23x_toCayley g) S ↔
      g2Act (burnsideI23x_toCayley (g * u * g⁻¹)) y ∈ gmapG (burnsideI23x_toCayley g) S
    rw [mem_gmapG, mem_gmapG]
    have e : burnsideI23x_toCayley (g * u * g⁻¹) =
        burnsideI23x_toCayley g * burnsideI23x_toCayley u * (burnsideI23x_toCayley g)⁻¹ := rfl
    rw [e, conj_g2Act, hS.mem_iff hu]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_exists_eq_pre1 {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1) {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 3 F).Gam →* ↥L} {f : V → (Ix3 → F)}
    (hf : IsCoord (burnsideI23x_LM3 F) L W0 marking f)
    (hcomm : ∀ T : (Ix3 → F) →+ (Ix3 → F),
      (∀ (γ : (i23NaturalModel 3 F).Gam) (x : Ix3 → F),
        T ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    {P : Subgroup (MulAut V)} {g : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      burnsideI23x_toCayley u ∈ U0 F ∧ x = ((marking (g * u * g⁻¹) : ↥L) : MulAut V))
    {i : ℕ} {U : Subgroup V} (hU : IsFlagW L P W0 (Nat.card F) i U) :
    ∃ S : Submodule F (Ix3 → F),
      (∀ u : ↥⁅quasithinG2 F, quasithinG2 F⁆, burnsideI23x_toCayley u ∈ U0 F →
        ∀ x ∈ S, g2Act (burnsideI23x_toCayley u) x ∈ S) ∧
      Nat.card S = Nat.card F ^ i ∧
      U = hf.pre (gmapG (burnsideI23x_toCayley g) S).toAddSubgroup := by
  obtain ⟨hZU, hst, hidx, hPU⟩ := hU
  have hsc := (hf.endStableW_iff hV hcomm hZU).mp hst
  let T : Submodule F (Ix3 → F) :=
    { carrier := hf.img U
      add_mem' := (hf.img U).add_mem
      zero_mem' := (hf.img U).zero_mem
      smul_mem' := fun c x hx => hsc c x hx }
  have hTcard : Nat.card T = Nat.card F ^ i := by
    rw [← hidx, ← hf.card_img]
    rfl
  refine ⟨gmapG (burnsideI23x_toCayley g)⁻¹ T, fun u hu x hx => ?_, by rw [card_gmapG, hTcard], ?_⟩
  · rw [mem_gmapG, inv_inv] at hx ⊢
    have hp : ((marking (g * u * g⁻¹) : ↥L) : MulAut V) ∈ stabW U :=
      hPU ((hg _).mpr ⟨u, hu, rfl⟩)
    have h1 := ((IsCoord.mem_stabW_iff hf hZU (g * u * g⁻¹)).mp hp _).mp hx
    change g2Act (burnsideI23x_toCayley (g * u * g⁻¹)) (g2Act (burnsideI23x_toCayley g) x) ∈ T
      at h1
    have e : burnsideI23x_toCayley (g * u * g⁻¹) =
        burnsideI23x_toCayley g * burnsideI23x_toCayley u * (burnsideI23x_toCayley g)⁻¹ := rfl
    rw [e, ← g2Act_mul_apply, show burnsideI23x_toCayley g * burnsideI23x_toCayley u *
      (burnsideI23x_toCayley g)⁻¹ * burnsideI23x_toCayley g =
        burnsideI23x_toCayley g * burnsideI23x_toCayley u by group, g2Act_mul_apply] at h1
    exact h1
  · rw [gmapG_gmapG_inv]
    exact (hf.pre_img hZU).symm

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_E01_mem_U0 {F : Type} [Field F] [CharP F 2] :
    burnsideI23x_eE (F := F) 0 1 (by decide) ∈ U0 F := by
  have : (tv 0 1 (by decide) 1 : SL3 F) = uSL 1 0 0 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have hA : ((tv 0 1 (by decide) 1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
        1 + Matrix.single 0 1 1 := rfl
    rw [hA]
    show _ = !![1, 1, 0; 0, 1, 0; 0, 0, 1] i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, Matrix.one_apply]
  unfold burnsideI23x_eE
  rw [this]
  exact g2A_mem_U0 1 0 0

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_E12_mem_U0 {F : Type} [Field F] [CharP F 2] :
    burnsideI23x_eE (F := F) 1 2 (by decide) ∈ U0 F := by
  have : (tv 1 2 (by decide) 1 : SL3 F) = uSL 0 0 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have hA : ((tv 1 2 (by decide) 1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
        1 + Matrix.single 1 2 1 := rfl
    rw [hA]
    show _ = !![1, 0, 0; 0, 1, 1; 0, 0, 1] i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, Matrix.one_apply]
  unfold burnsideI23x_eE
  rw [this]
  exact g2A_mem_U0 0 0 1

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_x0y1_mem_U0 {F : Type} [Field F] [CharP F 2] :
    g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F) ∈ U0 F :=
  (U0 F).mul_mem (g2X_mem_U0 1) (g2Y_mem_U0 1 0)

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_stable_gens {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (S : AddSubgroup (Ix3 → F))
    (hS : ∀ u : ↥⁅quasithinG2 F, quasithinG2 F⁆, burnsideI23x_toCayley u ∈ U0 F →
      ∀ x ∈ S, g2Act (burnsideI23x_toCayley u) x ∈ S) :
    (∀ x ∈ S, burnsideI23x_rtv 0 1 x ∈ S) ∧ (∀ x ∈ S, burnsideI23x_rtv 1 2 x ∈ S) ∧
      (∀ x ∈ S, burnsideI23x_rx0 (burnsideI23x_ry1 x) ∈ S) := by
  set c := burnsideI23x_cF F hF with hc
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have := hS (burnsideI23x_toGam (burnsideI23x_ZE.tvE c 0 1 (by decide)).g
      (burnsideI23x_gam_tvE c 0 1 (by decide))) burnsideI23x_E01_mem_U0 x hx
    rwa [show burnsideI23x_toCayley (burnsideI23x_toGam (burnsideI23x_ZE.tvE c 0 1 (by decide)).g
      (burnsideI23x_gam_tvE c 0 1 (by decide))) = g2A (tv 0 1 (by decide) 1) from rfl,
      burnsideI23x_g2Act_rtv] at this
  · have := hS (burnsideI23x_toGam (burnsideI23x_ZE.tvE c 1 2 (by decide)).g
      (burnsideI23x_gam_tvE c 1 2 (by decide))) burnsideI23x_E12_mem_U0 x hx
    rwa [show burnsideI23x_toCayley (burnsideI23x_toGam (burnsideI23x_ZE.tvE c 1 2 (by decide)).g
      (burnsideI23x_gam_tvE c 1 2 (by decide))) = g2A (tv 1 2 (by decide) 1) from rfl,
      burnsideI23x_g2Act_rtv] at this
  · have := hS (burnsideI23x_toGam (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
      (burnsideI23x_ZE.y1 c)).g (burnsideI23x_gam_x0y1 c)) burnsideI23x_x0y1_mem_U0 x hx
    rwa [show burnsideI23x_toCayley (burnsideI23x_toGam (burnsideI23x_ZE.mul
      (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.y1 c)).g (burnsideI23x_gam_x0y1 c)) =
        g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F) from rfl, g2Act_mul_apply,
      burnsideI23x_g2Act_rx0, burnsideI23x_g2Act_ry1] at this

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_eq_std1 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (S : Submodule F (Ix3 → F))
    (hS : ∀ u : ↥⁅quasithinG2 F, quasithinG2 F⁆, burnsideI23x_toCayley u ∈ U0 F →
      ∀ x ∈ S, g2Act (burnsideI23x_toCayley u) x ∈ S)
    (hcard : Nat.card S = Nat.card F ^ 1) : S = stdF F 1 := by
  obtain ⟨h1, h2, h3⟩ := burnsideI23x_stable_gens hF S.toAddSubgroup hS
  obtain ⟨e₀, he₀, hℓ⟩ := burnsideI23x_line_of_card S.toAddSubgroup
    (fun c x hx => S.smul_mem c hx)
    (by rw [show Nat.card S.toAddSubgroup = Nat.card S from rfl, hcard, pow_one])
  have hfix : ∀ p : (Ix3 → F) → (Ix3 → F), (∀ x, p x = 0 → x = 0) → (∀ x ∈ S, p x ∈ S) →
      p e₀ = e₀ := by
    intro p hp0 hpS
    obtain ⟨a, ha⟩ := (hℓ (p e₀)).1 (hpS e₀ ((hℓ e₀).2 ⟨1, (one_smul F e₀).symm⟩))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact he₀ (hp0 e₀ ha)
    rcases burnsideI23x_h01 hF a with rfl | rfl
    · exact absurd rfl ha0
    · rw [ha, one_smul]
  have hinj : ∀ (u : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
      g2Act (burnsideI23x_toCayley u) x = 0 → x = 0 := by
    intro u x hx
    have := congrArg (g2Act (burnsideI23x_toCayley u)⁻¹) hx
    rwa [g2Act_inv_apply, map_zero] at this
  have p1 := hfix (burnsideI23x_rtv 0 1) (fun x hx => by
    have := hinj (burnsideI23x_toGam (burnsideI23x_ZE.tvE (burnsideI23x_cF F hF) 0 1 (by decide)).g
      (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 0 1 (by decide))) x
    rw [show burnsideI23x_toCayley (burnsideI23x_toGam (burnsideI23x_ZE.tvE
      (burnsideI23x_cF F hF) 0 1 (by decide)).g (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 0 1
        (by decide))) = g2A (tv 0 1 (by decide) 1) from rfl, burnsideI23x_g2Act_rtv] at this
    exact this hx) h1
  have p2 := hfix (burnsideI23x_rtv 1 2) (fun x hx => by
    have := hinj (burnsideI23x_toGam (burnsideI23x_ZE.tvE (burnsideI23x_cF F hF) 1 2 (by decide)).g
      (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 1 2 (by decide))) x
    rw [show burnsideI23x_toCayley (burnsideI23x_toGam (burnsideI23x_ZE.tvE
      (burnsideI23x_cF F hF) 1 2 (by decide)).g (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 1 2
        (by decide))) = g2A (tv 1 2 (by decide) 1) from rfl, burnsideI23x_g2Act_rtv] at this
    exact this hx) h2
  have p3 := hfix (fun x => burnsideI23x_rx0 (burnsideI23x_ry1 x)) (fun x hx => by
    have := hinj (burnsideI23x_toGam (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0
      (burnsideI23x_cF F hF)) (burnsideI23x_ZE.y1 (burnsideI23x_cF F hF))).g
      (burnsideI23x_gam_x0y1 (burnsideI23x_cF F hF))) x
    rw [show burnsideI23x_toCayley (burnsideI23x_toGam (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0
      (burnsideI23x_cF F hF)) (burnsideI23x_ZE.y1 (burnsideI23x_cF F hF))).g
      (burnsideI23x_gam_x0y1 (burnsideI23x_cF F hF))) =
        g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F) from rfl, g2Act_mul_apply,
      burnsideI23x_g2Act_rx0, burnsideI23x_g2Act_ry1] at this
    exact this hx) h3
  have hu0 : e₀ = eu 0 1 := by
    rcases burnsideI23x_fix_P1 hF e₀ p1 p2 p3 with h | h
    · exact absurd h he₀
    · exact h
  ext x
  rw [mem_stdF_one_iff]
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (hℓ x).1 hx
    exact ⟨a, by rw [ha, hu0]⟩
  · rintro ⟨a, rfl⟩
    have := (hℓ (a • eu 0 1)).2 ⟨a, by rw [hu0]⟩
    exact this

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_eq_std2 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (S : Submodule F (Ix3 → F))
    (hS : ∀ u : ↥⁅quasithinG2 F, quasithinG2 F⁆, burnsideI23x_toCayley u ∈ U0 F →
      ∀ x ∈ S, g2Act (burnsideI23x_toCayley u) x ∈ S)
    (hcard : Nat.card S = Nat.card F ^ 2) : S = stdF F 2 := by
  obtain ⟨h1, h2, h3⟩ := burnsideI23x_stable_gens hF S.toAddSubgroup hS
  have h4 : Nat.card S.toAddSubgroup = 4 := by
    rw [show Nat.card S.toAddSubgroup = Nat.card S from rfl, hcard, hF]
    norm_num
  have hSeq := burnsideI23x_plane_P1 hF S.toAddSubgroup h4 h1 h2 h3
  ext x
  constructor
  · intro hx
    have hx' : x ∈ S.toAddSubgroup := hx
    rw [hSeq] at hx'
    exact hx'
  · intro hx
    have hx' : x ∈ (stdF F 2).toAddSubgroup := hx
    rw [← hSeq] at hx'
    exact hx'

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.QuasithinUnique in
theorem burnsideI23x_sylow_desc1 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (marking : (i23NaturalModel 3 F).Gam →* ↥L) (hmb : Function.Bijective marking)
    {P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P L) :
    ∃ g : ↥⁅quasithinG2 F, quasithinG2 F⁆, ∀ x : MulAut V, x ∈ P ↔
      ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆, burnsideI23x_toCayley u ∈ U0 F ∧
        x = ((marking (g * u * g⁻¹) : ↥L) : MulAut V) := by
  haveI : Finite (quasithinZorn F) := by
    unfold quasithinZorn
    infer_instance
  haveI : Finite (quasithinZorn F ≃ₗ[F] quasithinZorn F) :=
    Finite.of_injective (fun e : quasithinZorn F ≃ₗ[F] quasithinZorn F =>
      (e : quasithinZorn F → quasithinZorn F)) (fun a b h => LinearEquiv.ext fun x => congrFun h x)
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_desc (G := cayleyGroup F) (Γ := ⁅quasithinG2 F, quasithinG2 F⁆)
    (U := (U0 F).map (cayleyGroup F).subtype) g2Derived_le burnsideI23x_gam_norm
    (burnsideI23x_U0_sylow hF le_rfl) marking hmb hP
  refine ⟨g, fun x => ?_⟩
  rw [hg]
  refine exists_congr fun u => and_congr_left fun _ => ?_
  constructor
  · rintro ⟨y, hy, hyu⟩
    have : y = burnsideI23x_toCayley u := Subtype.ext hyu
    rwa [← this]
  · intro hu
    exact ⟨burnsideI23x_toCayley u, hu, rfl⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_flag1_eq {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {V : Type} [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1) {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {marking : (i23NaturalModel 3 F).Gam →* ↥L} {f : V → (Ix3 → F)}
    (hf : IsCoord (burnsideI23x_LM3 F) L W0 marking f)
    (hcomm : ∀ T : (Ix3 → F) →+ (Ix3 → F),
      (∀ (γ : (i23NaturalModel 3 F).Gam) (x : Ix3 → F),
        T ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    {P : Subgroup (MulAut V)} {g : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      burnsideI23x_toCayley u ∈ U0 F ∧ x = ((marking (g * u * g⁻¹) : ↥L) : MulAut V))
    {U : Subgroup V} (hU : IsFlagW L P W0 (Nat.card F) 1 U) :
    U = hf.pre (gmapG (burnsideI23x_toCayley g) (stdF F 1)).toAddSubgroup := by
  obtain ⟨S, hS, hc, rfl⟩ := burnsideI23x_exists_eq_pre1 hV hf hcomm hg hU
  rw [burnsideI23x_eq_std1 hF S hS hc]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_flag2_eq {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {V : Type} [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1) {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {marking : (i23NaturalModel 3 F).Gam →* ↥L} {f : V → (Ix3 → F)}
    (hf : IsCoord (burnsideI23x_LM3 F) L W0 marking f)
    (hcomm : ∀ T : (Ix3 → F) →+ (Ix3 → F),
      (∀ (γ : (i23NaturalModel 3 F).Gam) (x : Ix3 → F),
        T ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    {P : Subgroup (MulAut V)} {g : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      burnsideI23x_toCayley u ∈ U0 F ∧ x = ((marking (g * u * g⁻¹) : ↥L) : MulAut V))
    {U : Subgroup V} (hU : IsFlagW L P W0 (Nat.card F) 2 U) :
    U = hf.pre (gmapG (burnsideI23x_toCayley g) (stdF F 2)).toAddSubgroup := by
  obtain ⟨S, hS, hc, rfl⟩ := burnsideI23x_exists_eq_pre1 hV hf hcomm hg hU
  rw [burnsideI23x_eq_std2 hF S hS hc]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_flags_one {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {V : Type} [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1) {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {marking : (i23NaturalModel 3 F).Gam →* ↥L} {f : V → (Ix3 → F)}
    (hf : IsCoord (burnsideI23x_LM3 F) L W0 marking f)
    (hcomm : ∀ T : (Ix3 → F) →+ (Ix3 → F),
      (∀ (γ : (i23NaturalModel 3 F).Gam) (x : Ix3 → F),
        T ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    {P : Subgroup (MulAut V)} {g : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      burnsideI23x_toCayley u ∈ U0 F ∧ x = ((marking (g * u * g⁻¹) : ↥L) : MulAut V)) :
    ∃ U₁ U₂ : Subgroup V, IsFlagW L P W0 (2 ^ 1) 1 U₁ ∧ IsFlagW L P W0 (2 ^ 1) 2 U₂ ∧ U₁ ≤ U₂ ∧
      (∀ U, IsFlagW L P W0 (2 ^ 1) 1 U → U = U₁) ∧
      (∀ U, IsFlagW L P W0 (2 ^ 1) 2 U → U = U₂) := by
  have h2 : (2 : ℕ) ^ 1 = Nat.card F := by rw [hF, pow_one]
  rw [h2]
  refine ⟨_, _, burnsideI23x_isFlagW_pre1 hV hf hcomm hg (stdF_stable 1)
      (card_stdF (by norm_num)),
    burnsideI23x_isFlagW_pre1 hV hf hcomm hg (stdF_stable 2) (card_stdF (by norm_num)),
    fun w hw => Submodule.map_mono (stdF_mono (by norm_num)) hw,
    fun U hU => burnsideI23x_flag1_eq hF hV hf hcomm hg hU,
    fun U hU => burnsideI23x_flag2_eq hF hV hf hcomm hg hU⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
abbrev burnsideI23x_v6 (a b c d e f : ZMod 2) : Ix3 → ZMod 2 := q6 a b c d e f

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_sqrt_zmod2 {F : Type} [Field F] [Finite F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (a : ZMod 2) : burnsideI23x_sqrt F (c a) = c a := by
  have hsq : (c a) ^ 2 = c a := by
    rw [← map_pow]
    congr 1
    revert a
    decide
  conv_lhs => rw [← hsq]
  exact burnsideI23x_sqrt_of_sq _

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_normQ_emb {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Ix3 → ZMod 2) :
    normQ (burnsideI23x_emb c w) = c (normQ w) := by
  simp only [normQ, burnsideI23x_emb, map_add, map_mul]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_gen_pair {F : Type} [Field F] [Finite F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (A : burnsideI23x_ZE c)
    (h : (A.g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆)
    (x : Ix3 → ZMod 2) :
    (burnsideI23x_emb c (A.f x + x), c (normQ x + normQ (A.f x))) ∈ AddSubgroup.closure
      {y | ∃ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
        y = ((burnsideI23x_LM3 F).lin γ x - x, burnsideI23x_sqrt F ((burnsideI23x_sd3 F).Q0 x +
          (burnsideI23x_sd3 F).Q0 ((burnsideI23x_LM3 F).lin γ x)))} := by
  apply AddSubgroup.subset_closure
  refine ⟨burnsideI23x_toGam A.g h, burnsideI23x_emb c x, ?_⟩
  rw [burnsideI23x_lin_toGam, A.hf, burnsideI23x_sd3_Q0, burnsideI23x_sd3_Q0,
    burnsideI23x_normQ_emb, burnsideI23x_normQ_emb, ← map_add, burnsideI23x_sqrt_zmod2]
  refine Prod.ext ?_ rfl
  show burnsideI23x_emb c (A.f x + x) = burnsideI23x_emb c (A.f x) - burnsideI23x_emb c x
  rw [CharTwo.sub_eq_add]
  funext i
  simp [burnsideI23x_emb]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_pair_mem {F : Type} [Field F] [Finite F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (A : burnsideI23x_ZE c)
    (h : (A.g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆)
    (x a : Ix3 → ZMod 2) (z : ZMod 2) (ha : A.f x + x = a) (hz : normQ x + normQ (A.f x) = z) :
    (burnsideI23x_emb c a, c z) ∈ AddSubgroup.closure
      {y | ∃ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
        y = ((burnsideI23x_LM3 F).lin γ x - x, burnsideI23x_sqrt F ((burnsideI23x_sd3 F).Q0 x +
          (burnsideI23x_sd3 F).Q0 ((burnsideI23x_LM3 F).lin γ x)))} := by
  have := burnsideI23x_gen_pair c A h x
  rwa [ha, hz] at this

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ypair : Fin 7 → (Ix3 → ZMod 2) × ZMod 2 :=
  ![(q6 0 0 0 0 1 0, 0), (q6 1 0 0 0 0 0, 0), (q6 0 0 0 0 0 1, 0), (q6 0 0 0 1 0 0, 0),
    (q6 0 1 0 0 0 0, 0), (q6 0 0 1 0 0 0, 0), (q6 0 1 0 0 0 1, 1)]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_ypair_span : ∀ p : (Ix3 → ZMod 2) × ZMod 2, ∃ s : Fin 7 → Bool,
    p = ∑ i, if s i then burnsideI23x_ypair i else 0 := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_genW'3_one (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    (burnsideI23x_sd3 F).GenW' (burnsideI23x_LM3 F).lin := by
  classical
  set c := burnsideI23x_cF F hF with hc
  set C : AddSubgroup ((Ix3 → F) × F) := AddSubgroup.closure
    {y | ∃ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
      y = ((burnsideI23x_LM3 F).lin γ x - x, burnsideI23x_sqrt F ((burnsideI23x_sd3 F).Q0 x +
        (burnsideI23x_sd3 F).Q0 ((burnsideI23x_LM3 F).lin γ x)))} with hC
  let Φ : (Ix3 → ZMod 2) × ZMod 2 →+ (Ix3 → F) × F :=
    AddMonoidHom.prodMap (burnsideI23x_embHom c) c.toAddMonoidHom
  let K : AddSubgroup ((Ix3 → ZMod 2) × ZMod 2) := C.comap Φ
  have hK : ∀ i, burnsideI23x_ypair i ∈ K := by
    intro i
    show Φ (burnsideI23x_ypair i) ∈ C
    fin_cases i
    · have e1 : burnsideI23x_rtv 0 1 (burnsideI23x_v6 0 0 0 1 0 0) + burnsideI23x_v6 0 0 0 1 0 0 = burnsideI23x_v6 0 0 0 0 1 0 := by
        decide
      have e2 : normQ (burnsideI23x_v6 0 0 0 1 0 0) +
          normQ (burnsideI23x_rtv 0 1 (burnsideI23x_v6 0 0 0 1 0 0)) = 0 := by decide
      exact burnsideI23x_pair_mem c (burnsideI23x_ZE.tvE c 0 1 (by decide))
        (burnsideI23x_gam_tvE c 0 1 (by decide)) _ _ _ e1 e2
    · have e1 : burnsideI23x_rtv 0 1 (burnsideI23x_v6 0 1 0 0 0 0) + burnsideI23x_v6 0 1 0 0 0 0 = burnsideI23x_v6 1 0 0 0 0 0 := by
        decide
      have e2 : normQ (burnsideI23x_v6 0 1 0 0 0 0) +
          normQ (burnsideI23x_rtv 0 1 (burnsideI23x_v6 0 1 0 0 0 0)) = 0 := by decide
      exact burnsideI23x_pair_mem c (burnsideI23x_ZE.tvE c 0 1 (by decide))
        (burnsideI23x_gam_tvE c 0 1 (by decide)) _ _ _ e1 e2
    · have e1 : burnsideI23x_rtv 0 2 (burnsideI23x_v6 0 0 0 1 0 0) + burnsideI23x_v6 0 0 0 1 0 0 = burnsideI23x_v6 0 0 0 0 0 1 := by
        decide
      have e2 : normQ (burnsideI23x_v6 0 0 0 1 0 0) +
          normQ (burnsideI23x_rtv 0 2 (burnsideI23x_v6 0 0 0 1 0 0)) = 0 := by decide
      exact burnsideI23x_pair_mem c (burnsideI23x_ZE.tvE c 0 2 (by decide))
        (burnsideI23x_gam_tvE c 0 2 (by decide)) _ _ _ e1 e2
    · have e1 : burnsideI23x_rtv 1 0 (burnsideI23x_v6 0 0 0 0 1 0) + burnsideI23x_v6 0 0 0 0 1 0 = burnsideI23x_v6 0 0 0 1 0 0 := by
        decide
      have e2 : normQ (burnsideI23x_v6 0 0 0 0 1 0) +
          normQ (burnsideI23x_rtv 1 0 (burnsideI23x_v6 0 0 0 0 1 0)) = 0 := by decide
      exact burnsideI23x_pair_mem c (burnsideI23x_ZE.tvE c 1 0 (by decide))
        (burnsideI23x_gam_tvE c 1 0 (by decide)) _ _ _ e1 e2
    · have e1 : burnsideI23x_rtv 1 0 (burnsideI23x_v6 1 0 0 0 0 0) + burnsideI23x_v6 1 0 0 0 0 0 = burnsideI23x_v6 0 1 0 0 0 0 := by
        decide
      have e2 : normQ (burnsideI23x_v6 1 0 0 0 0 0) +
          normQ (burnsideI23x_rtv 1 0 (burnsideI23x_v6 1 0 0 0 0 0)) = 0 := by decide
      exact burnsideI23x_pair_mem c (burnsideI23x_ZE.tvE c 1 0 (by decide))
        (burnsideI23x_gam_tvE c 1 0 (by decide)) _ _ _ e1 e2
    · have e1 : burnsideI23x_rtv 2 0 (burnsideI23x_v6 1 0 0 0 0 0) + burnsideI23x_v6 1 0 0 0 0 0 = burnsideI23x_v6 0 0 1 0 0 0 := by
        decide
      have e2 : normQ (burnsideI23x_v6 1 0 0 0 0 0) +
          normQ (burnsideI23x_rtv 2 0 (burnsideI23x_v6 1 0 0 0 0 0)) = 0 := by decide
      exact burnsideI23x_pair_mem c (burnsideI23x_ZE.tvE c 2 0 (by decide))
        (burnsideI23x_gam_tvE c 2 0 (by decide)) _ _ _ e1 e2
    · have e1 : burnsideI23x_rx0 (burnsideI23x_rx1 (burnsideI23x_v6 0 0 0 0 1 0)) + burnsideI23x_v6 0 0 0 0 1 0 =
          burnsideI23x_v6 0 1 0 0 0 1 := by decide
      have e2 : normQ (burnsideI23x_v6 0 0 0 0 1 0) +
          normQ (burnsideI23x_rx0 (burnsideI23x_rx1 (burnsideI23x_v6 0 0 0 0 1 0))) = 1 := by decide
      exact burnsideI23x_pair_mem c (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
        (burnsideI23x_ZE.x1 c)) (burnsideI23x_gam_x0x1 c) _ _ _ e1 e2
  have hKall : ∀ p : (Ix3 → ZMod 2) × ZMod 2, p ∈ K := by
    intro p
    obtain ⟨s, rfl⟩ := burnsideI23x_ypair_span p
    refine AddSubgroup.sum_mem K (fun i _ => ?_)
    split_ifs
    · exact hK i
    · exact K.zero_mem
  intro w
  obtain ⟨x', hx'⟩ := (burnsideI23x_emb_bij c).2 w.1
  obtain ⟨z', hz'⟩ := c.surjective w.2
  have := hKall (x', z')
  have hw : Φ (x', z') = w := Prod.ext hx' hz'
  rw [← hw]
  exact this

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK in
theorem burnsideI23x_hbound3_one {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut V)) (W0 : Subgroup V)
        (π : (i23NaturalModel 3 F).Gam →* ↥L),
        (i23NaturalModel 3 F).RealizesVia L ⊤ W0 π → W0 = fixV L → commV L = ⊤ →
        Nat.card W0 ≤ Nat.card F := by
  intro V _ _ hV L W0 π hreal hW0 hcomm
  have h := CFSG.Quasithin.H13.VolI.g2NaturalCover_holds V hV L W0 (le_of_eq hW0) hcomm
    ⟨F, inferInstance, inferInstance, by rw [hF, pow_one], π, hreal⟩
  rcases h with h | ⟨h2, -, -⟩
  · rw [h, hF]
    simp
  · rw [h2, hF]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_x1y1_stab {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    g2X (![0, 1, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F) ∈ stabQ (stdF F 2) := by
  set c := burnsideI23x_cF F hF with hc
  have hc0 : ∀ y : ZMod 2, c y = 0 ↔ y = 0 := fun y => by
    rw [← map_zero c]; exact c.injective.eq_iff
  intro w
  obtain ⟨w', rfl⟩ := (burnsideI23x_emb_bij c).2 w
  rw [g2Act_mul_apply, burnsideI23x_g2Act_ry1, burnsideI23x_g2Act_rx1, burnsideI23x_emb_ry1,
    burnsideI23x_emb_rx1, mem_stdF_two, mem_stdF_two]
  have key : ∀ w' : Ix3 → ZMod 2,
      (w' (.inl 1) = 0 ∧ w' (.inl 2) = 0 ∧ w' (.inr 0) = 0 ∧ w' (.inr 1) = 0) ↔
      ((burnsideI23x_rx1 (burnsideI23x_ry1 w')) (.inl 1) = 0 ∧
        (burnsideI23x_rx1 (burnsideI23x_ry1 w')) (.inl 2) = 0 ∧
        (burnsideI23x_rx1 (burnsideI23x_ry1 w')) (.inr 0) = 0 ∧
        (burnsideI23x_rx1 (burnsideI23x_ry1 w')) (.inr 1) = 0) := by decide
  have := key w'
  simp only [burnsideI23x_emb, hc0]
  exact this

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_irred3_one_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) (g : ↥⁅quasithinG2 F, quasithinG2 F⁆)
    (C : AddSubgroup (Ix3 → F)) (hC : C ≠ ⊥)
    (hCℓ : C ≤ (gmapG (burnsideI23x_toCayley g) (stdF F 1)).toAddSubgroup) :
    (gmapG (burnsideI23x_toCayley g) (stdF F 1)).toAddSubgroup ≤ C := by
  obtain ⟨⟨x₀, hx₀C⟩, hx₀ne⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
  have hx₀ne' : x₀ ≠ 0 := fun h => hx₀ne (Subtype.ext h)
  obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.1 (hCℓ hx₀C)
  intro x hx
  obtain ⟨s, hs⟩ := mem_gmapG_stdF_one_iff.1 hx
  rcases burnsideI23x_h01 hF t with rfl | rfl
  · exact absurd (by rw [ht, zero_smul]) hx₀ne'
  · rcases burnsideI23x_h01 hF s with rfl | rfl
    · rw [hs, zero_smul]; exact C.zero_mem
    · rw [hs, one_smul]
      rw [ht, one_smul] at hx₀C
      exact hx₀C

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_x1y1_plane {F : Type} [Field F] [CharP F 2] (r s : F) :
    burnsideI23x_rx1 (burnsideI23x_ry1 (q6 r 0 0 0 0 s)) = q6 (r + s) 0 0 0 0 r := by
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [burnsideI23x_rx1, burnsideI23x_ry1, q6] <;>
    linear_combination s * (CharTwo.two_eq_zero (R := F))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_irred3_two_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2)
    (A : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ((Ix3 → F) ≃ₗ[F] (Ix3 → F)))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM3 F).lin γ x) (g : ↥⁅quasithinG2 F, quasithinG2 F⁆)
    (C : AddSubgroup (Ix3 → F)) (hC : C ≠ ⊥)
    (hCℓ : C ≤ (gmapG (burnsideI23x_toCayley g) (stdF F 2)).toAddSubgroup)
    (hCinv : ∀ γ, (∀ x, A γ x ∈ (gmapG (burnsideI23x_toCayley g) (stdF F 2)).toAddSubgroup ↔
        x ∈ (gmapG (burnsideI23x_toCayley g) (stdF F 2)).toAddSubgroup) → ∀ x ∈ C, A γ x ∈ C) :
    (gmapG (burnsideI23x_toCayley g) (stdF F 2)).toAddSubgroup ≤ C := by
  set c := burnsideI23x_cF F hF with hc
  set gc := burnsideI23x_toCayley g with hgc
  set e : F → F → (Ix3 → F) := fun r s => g2Act gc (q6 r 0 0 0 0 s) with he
  have hmem2 : ∀ r s : F, q6 r 0 0 0 0 s ∈ stdF F 2 :=
    fun r s => mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩
  have hadd : ∀ r s r' s' : F, e (r + r') (s + s') = e r s + e r' s' := fun r s r' s' => by
    simp only [he]
    rw [← map_add, q6_add]
    simp
  have he0 : e 0 0 = 0 := by
    simp only [he]
    rw [q6_zero, map_zero]
  have hrep : ∀ x ∈ (gmapG gc (stdF F 2)).toAddSubgroup, ∃ r s : F, x = e r s := by
    intro x hx
    have hx' : g2Act gc⁻¹ x ∈ stdF F 2 := mem_gmapG.1 hx
    refine ⟨(g2Act gc⁻¹ x) (.inl 0), (g2Act gc⁻¹ x) (.inr 2), ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.1 hx'
    have hw' : g2Act gc⁻¹ x = q6 ((g2Act gc⁻¹ x) (.inl 0)) 0 0 0 0 ((g2Act gc⁻¹ x) (.inr 2)) := by
      conv_lhs => rw [q6_eta (g2Act gc⁻¹ x)]
      rw [h1, h2, h3, h4]
    simp only [he]
    rw [← hw', g2Act_apply_inv]
  set hΓ : ↥⁅quasithinG2 F, quasithinG2 F⁆ := burnsideI23x_toGam
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.x1 c) (burnsideI23x_ZE.y1 c)).g
    (burnsideI23x_gam_x1y1 c) with hhΓ
  have hhc : burnsideI23x_toCayley hΓ = g2X (![0, 1, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F) :=
    rfl
  have hstab : ∀ x, A (g * hΓ * g⁻¹) x ∈ (gmapG gc (stdF F 2)).toAddSubgroup ↔
      x ∈ (gmapG gc (stdF F 2)).toAddSubgroup := fun x => by
    rw [hAlin, burnsideI23x_lin3_apply]
    have e1 : burnsideI23x_toCayley (g * hΓ * g⁻¹) = gc * burnsideI23x_toCayley hΓ * gc⁻¹ := rfl
    rw [e1, hhc]
    exact burnsideI23x_stab_gmap gc (S := stdF F 2) (burnsideI23x_x1y1_stab hF) x
  have hh : ∀ r s : F, A (g * hΓ * g⁻¹) (e r s) = e (r + s) r := by
    intro r s
    rw [hAlin, burnsideI23x_lin3_apply]
    have e1 : burnsideI23x_toCayley (g * hΓ * g⁻¹) = gc * burnsideI23x_toCayley hΓ * gc⁻¹ := rfl
    simp only [he]
    rw [e1, hhc, ← g2Act_mul_apply, show gc * (g2X (![0, 1, 0] : Fin 3 → F) *
      g2Y (![0, 1, 0] : Fin 3 → F)) * gc⁻¹ * gc = gc * (g2X (![0, 1, 0] : Fin 3 → F) *
      g2Y (![0, 1, 0] : Fin 3 → F)) by group, g2Act_mul_apply, g2Act_mul_apply,
      burnsideI23x_g2Act_ry1, burnsideI23x_g2Act_rx1]
    congr 1
    exact burnsideI23x_x1y1_plane r s
  have hall : e 1 0 ∈ C ∧ e 0 1 ∈ C ∧ e 1 1 ∈ C := by
    obtain ⟨⟨x₀, hx₀C⟩, hx₀ne⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
    have hx₀ne' : x₀ ≠ 0 := fun h => hx₀ne (Subtype.ext h)
    obtain ⟨r₀, s₀, hrs⟩ := hrep x₀ (hCℓ hx₀C)
    have h1 := hCinv _ hstab _ hx₀C
    rw [hrs, hh] at h1
    rw [hrs] at hx₀C
    have h11 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rcases burnsideI23x_h01 hF r₀ with rfl | rfl <;> rcases burnsideI23x_h01 hF s₀ with rfl | rfl
    · exact absurd (by rw [hrs, he0]) hx₀ne'
    · have hq : e 1 0 ∈ C := by simpa using h1
      have hs : e 1 1 ∈ C := by
        have := C.add_mem hx₀C hq
        rwa [← hadd, zero_add, add_zero] at this
      exact ⟨hq, hx₀C, hs⟩
    · have hq : e 1 1 ∈ C := by simpa using h1
      have h0 : e 0 1 ∈ C := by
        have := C.add_mem hx₀C hq
        rwa [← hadd, h11, zero_add] at this
      exact ⟨hx₀C, h0, hq⟩
    · have hq : e 0 1 ∈ C := by rw [h11] at h1; exact h1
      have h0 : e 1 0 ∈ C := by
        have := C.add_mem hx₀C hq
        rwa [← hadd, add_zero, h11] at this
      exact ⟨h0, hq, hx₀C⟩
  intro x hx
  obtain ⟨r', s', rfl⟩ := hrep x hx
  rcases burnsideI23x_h01 hF r' with rfl | rfl <;> rcases burnsideI23x_h01 hF s' with rfl | rfl
  · rw [he0]; exact C.zero_mem
  · exact hall.2.1
  · exact hall.1
  · exact hall.2.2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem burnsideI23x_UCg_three_one :
    burnsideI23x_UCg 3 1 := by
  intro F _ _ hF U _ _ hU G L T K hLG hnorm hGT hT hGK huniv marking β hsec U1 U2 h1 h2
  have hF1 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : CharP F 2 := burnsideI23x_charP2_of_card hF1
  haveI : Finite (MulAut U) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hS := burnsideI23x_scalarAgree3 F
  have hEndLin : ∀ φ : (Ix3 → F) →+ (Ix3 → F),
      (∀ γ x, φ ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (φ x)) →
      ∃ c : F, ∀ x, φ x = c • x := fun φ hφ => burnsideI23x_hEnd3_one hF1 φ hφ
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM3 F) (burnsideI23x_sd3 F) (burnsideI23x_hsymp3 F) (burnsideI23x_hfaith3 F)
    (burnsideI23x_genW'3_one F hF1) (burnsideI23x_hbound3_one hF1) hU huniv hsec
  have hEnd : ∀ φ : (Ix3 → F) →+ (Ix3 → F),
      (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x := fun φ hφ =>
    hEndLin φ (fun γ x => by simpa only [hAlin] using hφ γ x)
  have hf := burnsideI23x_isCoord (burnsideI23x_LM3 F) hsec
  have hmb := burnsideI23x_marking_bij3 hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  obtain ⟨hU2i, hU2F, hU2c⟩ := burnsideI23x_marked_ell hS hsec h2
  have hU1' : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hU2' : ∀ u, u ∈ U2 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U2 := fun u => by
    rw [hψfst]; exact hU2i u
  have hcard1 : Nat.card (hf.img U1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img U1) hU1F hcard1
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hfl1 : IsFlagW L (T ⊓ L) K (2 ^ 1) 1 U1 :=
    burnsideI23x_marked_imp_flag hS hU hsec (fun T' hT' => hEndLin T' hT') h1
  have hfl2 : IsFlagW L (T ⊓ L) K (2 ^ 1) 2 U2 :=
    burnsideI23x_marked_imp_flag hS hU hsec (fun T' hT' => hEndLin T' hT') h2
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_desc1 hF1 marking hmb hP
  rw [← hF] at hfl1 hfl2
  have hU1pre := burnsideI23x_flag1_eq hF1 hU hf hEndLin hg hfl1
  have hU2pre := burnsideI23x_flag2_eq hF1 hU hf hEndLin hg hfl2
  have himg1 : hf.img U1 = (gmapG (burnsideI23x_toCayley g) (stdF F 1)).toAddSubgroup :=
    (congrArg hf.img hU1pre).trans (hf.img_pre _)
  have himg2 : hf.img U2 = (gmapG (burnsideI23x_toCayley g) (stdF F 2)).toAddSubgroup :=
    (congrArg hf.img hU2pre).trans (hf.img_pre _)
  have hirr1 : ∀ C : AddSubgroup (Ix3 → F), C ≠ ⊥ → C ≤ hf.img U1 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U1 ↔ x ∈ hf.img U1) → ∀ x ∈ C, A γ x ∈ C) → hf.img U1 ≤ C := by
    intro C hC hCℓ hCinv
    rw [himg1] at hCℓ hCinv ⊢
    exact burnsideI23x_irred3_one_one hF1 g C hC hCℓ
  have hirr2 : ∀ C : AddSubgroup (Ix3 → F), C ≠ ⊥ → C ≤ hf.img U2 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U2 ↔ x ∈ hf.img U2) → ∀ x ∈ C, A γ x ∈ C) → hf.img U2 ≤ C := by
    intro C hC hCℓ hCinv
    rw [himg2] at hCℓ hCinv ⊢
    exact burnsideI23x_irred3_two_one hF1 A hAlin g C hC hCℓ hCinv
  have he₀ℓ : e₀ ∈ hf.img U1 := (hℓ₁ e₀).2 ⟨1, (one_smul F e₀).symm⟩
  have hcardF2 : Nat.card (hf.img U2) = Nat.card F ^ 2 := by rw [hU2c, hF]
  have he₂ : ∃ e₂ ∈ hf.img U2, e₂ ≠ 0 := by
    have hlt : 1 < Nat.card (hf.img U2) := by
      rw [hcardF2]
      have : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    haveI : Nontrivial (hf.img U2) := Finite.one_lt_card_iff_nontrivial.1 hlt
    obtain ⟨⟨e₂, he₂⟩, hne⟩ := exists_ne (0 : hf.img U2)
    exact ⟨e₂, he₂, fun h => hne (Subtype.ext h)⟩
  obtain ⟨e₂, he₂ℓ, he₂0⟩ := he₂
  refine ⟨?_, ⟨?_, ?_⟩, fun h => absurd h (by norm_num)⟩
  · exact burnsideI23x_SD.exists_T_fixed ψ marking hπs hψact hEnd hgenW hTG hnorm hT2 he₀ hℓ₁
      hU1' (fun t ht u hu => h1.2.1 t ht u hu)
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU1F hU1' he₀ℓ he₀
      hirr1
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU2F hU2' he₂ℓ
      he₂0 hirr2

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
set_option synthInstance.maxSize 4096 in
theorem burnsideI23x_cent_decide : ∀ α β γ a b c : ZMod 2,
    (∀ w, burnsideI23x_zact α β γ a b c (burnsideI23x_rtv 0 1 w) =
      burnsideI23x_rtv 0 1 (burnsideI23x_zact α β γ a b c w)) →
    (∀ w, burnsideI23x_zact α β γ a b c (burnsideI23x_rtv 1 2 w) =
      burnsideI23x_rtv 1 2 (burnsideI23x_zact α β γ a b c w)) →
    (∀ w, burnsideI23x_zact α β γ a b c (burnsideI23x_rx0 (burnsideI23x_ry1 w)) =
      burnsideI23x_rx0 (burnsideI23x_ry1 (burnsideI23x_zact α β γ a b c w))) →
    (∀ w, burnsideI23x_zact α β γ a b c (burnsideI23x_zact α β γ a b c w) = w) →
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ a = 0 ∧ c = 0 := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_cent_P1 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (u : ↥(cayleyGroup F)) (hu : u ∈ U0 F)
    (h1 : u * burnsideI23x_eE (F := F) 0 1 (by decide) =
      burnsideI23x_eE (F := F) 0 1 (by decide) * u)
    (h2 : u * burnsideI23x_eE (F := F) 1 2 (by decide) =
      burnsideI23x_eE (F := F) 1 2 (by decide) * u)
    (h3 : u * (g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F)) =
      (g2X (![1, 0, 0] : Fin 3 → F) * g2Y (![0, 1, 0] : Fin 3 → F)) * u)
    (h4 : u * u = 1) : u = 1 ∨ u = tL 1 := by
  set c := burnsideI23x_cF F hF with hc
  obtain ⟨α, β, γ, a, b, c', rfl⟩ := burnsideI23x_U0_decomp (n := 1) (by rw [hF, pow_one]) u hu
  obtain ⟨α', rfl⟩ := c.surjective α
  obtain ⟨β', rfl⟩ := c.surjective β
  obtain ⟨γ', rfl⟩ := c.surjective γ
  obtain ⟨a', rfl⟩ := c.surjective a
  obtain ⟨b', rfl⟩ := c.surjective b
  obtain ⟨d', rfl⟩ := c.surjective c'
  set S := burnsideI23x_ZE.stab c α' β' γ' a' b' d' with hS
  have e1 := (burnsideI23x_ZE.g_eq_iff (burnsideI23x_ZE.mul S (burnsideI23x_ZE.tvE c 0 1 (by decide)))
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.tvE c 0 1 (by decide)) S)).1 h1
  have e2 := (burnsideI23x_ZE.g_eq_iff (burnsideI23x_ZE.mul S (burnsideI23x_ZE.tvE c 1 2 (by decide)))
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.tvE c 1 2 (by decide)) S)).1 h2
  have e3 := (burnsideI23x_ZE.g_eq_iff (burnsideI23x_ZE.mul S (burnsideI23x_ZE.mul
      (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.y1 c)))
    (burnsideI23x_ZE.mul (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c) (burnsideI23x_ZE.y1 c)) S)).1 h3
  have e4 : ∀ w, S.f (S.f w) = w := by
    intro w
    have h5 := (burnsideI23x_ZE.mul S S).hf w
    have h6 : (burnsideI23x_ZE.mul S S).g = 1 := h4
    rw [h6, map_one] at h5
    exact ((burnsideI23x_emb_bij c).1 h5).symm
  obtain ⟨hα, hβ, hγ, ha, hd⟩ := burnsideI23x_cent_decide α' β' γ' a' b' d' e1 e2 e3 e4
  subst hα hβ hγ ha hd
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b' with rfl | rfl
  · left
    apply cayley_ext
    intro w
    rw [q6_eta w, burnsideI23x_g2Act_u0_q6, map_one]
    simp only [map_zero]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  · right
    apply cayley_ext
    intro w
    rw [q6_eta w, burnsideI23x_g2Act_u0_q6, g2Act_tL]
    simp only [map_zero, map_one]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_toCayley_inj {F : Type} [Field F] [CharP F 2]
    {u v : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (h : burnsideI23x_toCayley u = burnsideI23x_toCayley v) : u = v :=
  Subtype.ext (congrArg (fun x : ↥(cayleyGroup F) => (x : quasithinZorn F ≃ₗ[F] quasithinZorn F)) h)

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
@[expose] noncomputable def burnsideI23x_tLG {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) : ↥⁅quasithinG2 F, quasithinG2 F⁆ :=
  burnsideI23x_toGam (tL 1) (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 0 2 (by decide))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_toCayley_tLG {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) : burnsideI23x_toCayley (burnsideI23x_tLG hF) = tL 1 := rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model in
theorem burnsideI23x_tLG_sq {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    burnsideI23x_tLG hF * burnsideI23x_tLG hF = 1 := by
  apply burnsideI23x_toCayley_inj
  exact burnsideI23x_tL_sq 1

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_center_P_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L} (hmb : Function.Bijective marking)
    {P : Subgroup (MulAut V)} {g : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      burnsideI23x_toCayley u ∈ U0 F ∧ x = ((marking (g * u * g⁻¹) : ↥L) : MulAut V))
    (x : MulAut V) :
    (x ∈ CFSG.ASVolI.ChIJK.centerOf P ∧ x ^ 2 = 1) ↔
      (x = 1 ∨ x = ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut V)) := by
  set c := burnsideI23x_cF F hF with hc
  have hmul : ∀ u u' : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      ((marking (u * u') : ↥L) : MulAut V) =
        ((marking u : ↥L) : MulAut V) * ((marking u' : ↥L) : MulAut V) :=
    fun u u' => congrArg Subtype.val (map_mul marking u u')
  have hinj : ∀ u u' : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      ((marking u : ↥L) : MulAut V) = ((marking u' : ↥L) : MulAut V) → u = u' :=
    fun u u' h => hmb.1 (Subtype.ext h)
  have hone : ((marking 1 : ↥L) : MulAut V) = 1 := congrArg Subtype.val (map_one marking)
  set z0 : MulAut V := ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut V) with hz0
  have hz0P : z0 ∈ P := (hg _).2 ⟨burnsideI23x_tLG hF, burnsideI23x_tL_mem_U0 1, rfl⟩
  have hz0sq : z0 ^ 2 = 1 := by
    rw [pow_two, hz0, ← hmul]
    have : g * burnsideI23x_tLG hF * g⁻¹ * (g * burnsideI23x_tLG hF * g⁻¹) = 1 := by
      calc g * burnsideI23x_tLG hF * g⁻¹ * (g * burnsideI23x_tLG hF * g⁻¹) =
          g * (burnsideI23x_tLG hF * burnsideI23x_tLG hF) * g⁻¹ := by group
        _ = 1 := by rw [burnsideI23x_tLG_sq]; group
    rw [this, hone]
  have hcentral : ∀ u : ↥⁅quasithinG2 F, quasithinG2 F⁆, burnsideI23x_toCayley u ∈ U0 F →
      u * burnsideI23x_tLG hF = burnsideI23x_tLG hF * u := by
    intro u hu
    apply burnsideI23x_toCayley_inj
    have := (burnsideI23x_center_U0 (n := 1) (by rw [hF, pow_one]) (tL (1 : F))
      (burnsideI23x_tL_mem_U0 1)).2 ⟨1, rfl⟩ _ hu
    exact this
  constructor
  · rintro ⟨hx, hx2⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    have hzP : (z : MulAut V) ∈ P := z.2
    obtain ⟨u, hu, hzu⟩ := (hg _).1 hzP
    have hcent : ∀ u' : ↥⁅quasithinG2 F, quasithinG2 F⁆, burnsideI23x_toCayley u' ∈ U0 F →
        u' * u = u * u' := by
      intro u' hu'
      have hy : ((marking (g * u' * g⁻¹) : ↥L) : MulAut V) ∈ P := (hg _).2 ⟨u', hu', rfl⟩
      have h1 := Subgroup.mem_center_iff.1 hz ⟨_, hy⟩
      have h2 : ((marking (g * u' * g⁻¹) : ↥L) : MulAut V) * (z : MulAut V) =
          (z : MulAut V) * ((marking (g * u' * g⁻¹) : ↥L) : MulAut V) := congrArg Subtype.val h1
      rw [hzu, ← hmul, ← hmul] at h2
      have h3 := hinj _ _ h2
      have h4 : g * (u' * u) * g⁻¹ = g * (u * u') * g⁻¹ := by
        simpa only [mul_assoc, inv_mul_cancel_left] using h3
      exact mul_right_cancel (mul_left_cancel h4)
    have hu2 : u * u = 1 := by
      have h5 : (z : MulAut V) ^ 2 = 1 := hx2
      rw [pow_two, hzu, ← hmul] at h5
      have h6 : ((marking (g * u * g⁻¹ * (g * u * g⁻¹)) : ↥L) : MulAut V) =
          ((marking 1 : ↥L) : MulAut V) := by rw [hone]; exact h5
      have h7 := hinj _ _ h6
      have h8 : g * (u * u) * g⁻¹ = 1 := by
        calc g * (u * u) * g⁻¹ = g * u * g⁻¹ * (g * u * g⁻¹) := by group
          _ = 1 := h7
      have h9 : g * (u * u) = g := by simpa using congrArg (· * g) h8
      exact mul_left_cancel (h9.trans (mul_one g).symm)
    have hE01 := hcent (burnsideI23x_toGam (burnsideI23x_ZE.tvE c 0 1 (by decide)).g
      (burnsideI23x_gam_tvE c 0 1 (by decide))) burnsideI23x_E01_mem_U0
    have hE12 := hcent (burnsideI23x_toGam (burnsideI23x_ZE.tvE c 1 2 (by decide)).g
      (burnsideI23x_gam_tvE c 1 2 (by decide))) burnsideI23x_E12_mem_U0
    have hX := hcent (burnsideI23x_toGam (burnsideI23x_ZE.mul (burnsideI23x_ZE.x0 c)
      (burnsideI23x_ZE.y1 c)).g (burnsideI23x_gam_x0y1 c)) burnsideI23x_x0y1_mem_U0
    have key := burnsideI23x_cent_P1 hF (burnsideI23x_toCayley u) hu
      (congrArg burnsideI23x_toCayley hE01).symm (congrArg burnsideI23x_toCayley hE12).symm
      (congrArg burnsideI23x_toCayley hX).symm
      (congrArg burnsideI23x_toCayley hu2)
    rcases key with h | h
    · left
      have : u = 1 := burnsideI23x_toCayley_inj h
      show (z : MulAut V) = 1
      rw [hzu, this, mul_one, mul_inv_cancel, hone]
    · right
      have : u = burnsideI23x_tLG hF := burnsideI23x_toCayley_inj h
      show (z : MulAut V) = _
      rw [hzu, this]
  · rintro (rfl | rfl)
    · exact ⟨Subgroup.one_mem _, one_pow 2⟩
    · refine ⟨?_, hz0sq⟩
      refine Subgroup.mem_map.2 ⟨⟨_, hz0P⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨u, hu, hyu⟩ := (hg y.1).1 y.2
      apply Subtype.ext
      show (y : MulAut V) * z0 = z0 * (y : MulAut V)
      rw [hyu]
      show ((marking (g * u * g⁻¹) : ↥L) : MulAut V) *
          ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut V) =
        ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut V) *
          ((marking (g * u * g⁻¹) : ↥L) : MulAut V)
      rw [← hmul, ← hmul]
      have hEq : g * u * g⁻¹ * (g * burnsideI23x_tLG hF * g⁻¹) =
          g * burnsideI23x_tLG hF * g⁻¹ * (g * u * g⁻¹) :=
        calc g * u * g⁻¹ * (g * burnsideI23x_tLG hF * g⁻¹) =
            g * (u * burnsideI23x_tLG hF) * g⁻¹ := by group
          _ = g * (burnsideI23x_tLG hF * u) * g⁻¹ := by rw [hcentral u hu]
          _ = g * burnsideI23x_tLG hF * g⁻¹ * (g * u * g⁻¹) := by group
      rw [hEq]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK in
theorem burnsideI23x_omega_center_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L} (hmb : Function.Bijective marking)
    {P : Subgroup (MulAut V)} {g : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      burnsideI23x_toCayley u ∈ U0 F ∧ x = ((marking (g * u * g⁻¹) : ↥L) : MulAut V))
    (x : MulAut V) :
    x ∈ CFSG.ASVolI.ChIJK.omegaOne (CFSG.ASVolI.ChIJK.centerOf P) ↔
      (x = 1 ∨ x = ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut V)) := by
  set z0 : MulAut V := ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut V) with hz0
  have hz0sq : z0 ^ 2 = 1 := ((burnsideI23x_center_P_one hF hmb hg z0).2 (Or.inr rfl)).2
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      exact (burnsideI23x_center_P_one hF hmb hg y).1 ⟨hy.1, hy.2⟩
    | one => exact Or.inl rfl
    | mul y y' _ _ hy hy' =>
      rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
      · left; exact mul_one _
      · right; exact one_mul _
      · right; exact mul_one _
      · left; rw [← pow_two]; exact hz0sq
    | inv y _ hy =>
      rcases hy with rfl | rfl
      · left; exact inv_one
      · right
        have : z0 * z0 = 1 := by rw [← pow_two]; exact hz0sq
        exact inv_eq_of_mul_eq_one_right this
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ((burnsideI23x_center_P_one hF hmb hg z0).2 (Or.inr rfl))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_tv12_eq {F : Type} [Field F] [CharP F 2] :
    (tv 1 2 (by decide) 1 : SL3 F) = uSL 0 0 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hA : ((tv 1 2 (by decide) 1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      1 + Matrix.single 1 2 1 := rfl
  rw [hA]
  show _ = !![1, 0, 0; 0, 1, 1; 0, 0, 1] i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, Matrix.one_apply]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
@[expose] noncomputable def burnsideI23x_E12G {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) : ↥⁅quasithinG2 F, quasithinG2 F⁆ :=
  burnsideI23x_toGam (g2A (uSL 0 0 1)) (by
    rw [← burnsideI23x_tv12_eq]
    exact burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 1 2 (by decide))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
@[expose] noncomputable def burnsideI23x_swapG {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) : ↥⁅quasithinG2 F, quasithinG2 F⁆ :=
  burnsideI23x_toGam (g2A swap01) (by
    rw [burnsideI23x_swap01_eq, map_mul, map_mul]
    exact burnsideI23x_gam_mul (burnsideI23x_gam_mul
      (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 0 1 (by decide))
      (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 1 0 (by decide)))
      (burnsideI23x_gam_tvE (burnsideI23x_cF F hF) 0 1 (by decide)))

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_E12G_sq {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    burnsideI23x_E12G hF * burnsideI23x_E12G hF = 1 := by
  apply burnsideI23x_toCayley_inj
  show g2A (uSL (0 : F) 0 1) * g2A (uSL 0 0 1) = 1
  rw [← map_mul, uSL_mul]
  have h11 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [h11, uSL_zero]

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_mem_highestLongRoot_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) (y : ↥⁅quasithinG2 F, quasithinG2 F⁆) :
    y ∈ i23G2HighestLongRoot F ↔ (y = 1 ∨ y = burnsideI23x_E12G hF) := by
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc⟩ := hy
      rcases burnsideI23x_h01 hF c with rfl | rfl
      · left
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        rw [hc x]
        refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
        · funext i; simp
        · funext i; simp
      · right
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        rw [hc x]
        exact (burnsideI23x_g2A_E12_apply 1 x).symm
    | one => exact Or.inl rfl
    | mul y y' _ _ hy hy' =>
      have hsq := burnsideI23x_E12G_sq hF
      rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
      · left; exact mul_one _
      · right; exact one_mul _
      · right; exact mul_one _
      · left; exact hsq
    | inv y _ hy =>
      rcases hy with rfl | rfl
      · left; exact inv_one
      · right
        exact inv_eq_of_mul_eq_one_right (burnsideI23x_E12G_sq hF)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨1, fun x => burnsideI23x_g2A_E12_apply 1 x⟩

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_swapG_conj {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    burnsideI23x_swapG hF * burnsideI23x_E12G hF * (burnsideI23x_swapG hF)⁻¹ =
      burnsideI23x_tLG hF := by
  apply burnsideI23x_toCayley_inj
  exact burnsideI23x_swap01_conj 1

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ASVolI.ChIJK CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_longroot_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L) (g : ↥⁅quasithinG2 F, quasithinG2 F⁆)
    (x : MulAut V) :
    x ∈ (CFSG.conjugate (i23G2HighestLongRoot F) (g * burnsideI23x_swapG hF)⁻¹).map
        (L.subtype.comp marking) ↔
      (x = 1 ∨ x = ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut V)) := by
  have hconj : g * burnsideI23x_swapG hF * burnsideI23x_E12G hF * (g * burnsideI23x_swapG hF)⁻¹ =
      g * burnsideI23x_tLG hF * g⁻¹ := by
    rw [← burnsideI23x_swapG_conj hF]
    group
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    rcases (burnsideI23x_mem_highestLongRoot_one hF y').1 hy' with rfl | rfl
    · left
      show (L.subtype.comp marking) ((MulAut.conj (g * burnsideI23x_swapG hF)⁻¹⁻¹).toMonoidHom 1) = 1
      rw [map_one, map_one]
    · right
      show (L.subtype.comp marking) ((MulAut.conj (g * burnsideI23x_swapG hF)⁻¹⁻¹).toMonoidHom _) = _
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hconj]
      rfl
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · refine Subgroup.mem_map.2 ⟨g * burnsideI23x_swapG hF * burnsideI23x_E12G hF *
        (g * burnsideI23x_swapG hF)⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_map.2 ⟨burnsideI23x_E12G hF,
          (burnsideI23x_mem_highestLongRoot_one hF _).2 (Or.inr rfl), by
            rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      · rw [hconj]
        rfl

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_lift_tL1 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (A : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ((Ix3 → F) ≃ₗ[F] (Ix3 → F)))
    (hA : ∀ γ, (burnsideI23x_sd3 F).Symp (A γ))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM3 F).lin γ x) (w : (Ix3 → F) × F) :
    (burnsideI23x_sd3 F).lift (hA (burnsideI23x_tLG hF)) w - w =
      (q6 (w.1 (.inl 2)) 0 0 0 0 (w.1 (.inr 0)), 0) := by
  have hAt : ∀ x, A (burnsideI23x_tLG hF) x = g2Act (tL 1) x := fun x =>
    (hAlin _ x).trans (burnsideI23x_lin3_apply F _ x)
  rw [burnsideI23x_SD.lift_apply]
  refine Prod.ext ?_ ?_
  · show A (burnsideI23x_tLG hF) w.1 - w.1 = _
    rw [hAt]
    conv_lhs => rw [q6_eta w.1, g2Act_tL, q6_sub]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · show w.2 + (burnsideI23x_sd3 F).lf (A (burnsideI23x_tLG hF)) w.1 - w.2 = 0
    have h0 : (burnsideI23x_sd3 F).Q0 w.1 +
        (burnsideI23x_sd3 F).Q0 (A (burnsideI23x_tLG hF) w.1) = 0 := by
      rw [hAt, burnsideI23x_sd3_Q0, burnsideI23x_sd3_Q0, burnsideI23x_normQ_tL]
      exact CharTwo.add_self_eq_zero _
    unfold burnsideI23x_SD.lf
    rw [h0, map_zero]
    ring

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Quasithin.Vol2.KGNat CFSG.ASVolI.ChIJK in
theorem burnsideI23x_commV_S3_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {U : Type} [CommGroup U] {L : Subgroup (MulAut U)}
    {marking : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L} (hmb : Function.Bijective marking)
    {P : Subgroup (MulAut U)} {g : ↥⁅quasithinG2 F, quasithinG2 F⁆}
    (hg : ∀ x : MulAut U, x ∈ P ↔ ∃ u : ↥⁅quasithinG2 F, quasithinG2 F⁆,
      burnsideI23x_toCayley u ∈ U0 F ∧ x = ((marking (g * u * g⁻¹) : ↥L) : MulAut U))
    (A : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ((Ix3 → F) ≃ₗ[F] (Ix3 → F)))
    (hA : ∀ γ, (burnsideI23x_sd3 F).Symp (A γ))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM3 F).lin γ x)
    (ψ : U ≃* Multiplicative ((Ix3 → F) × F))
    (hψact : ∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (u : U),
      ψ ((marking γ : MulAut U) u) = (burnsideI23x_sd3 F).liftHom A hA γ (ψ u)) (u : U) :
    u ∈ commV (CFSG.ASVolI.ChIJK.omegaOne (CFSG.ASVolI.ChIJK.centerOf P)) ↔
      ∃ p ∈ stdF F 2, Multiplicative.toAdd (ψ u) =
        (burnsideI23x_sd3 F).lift (hA g) (p, 0) := by
  classical
  have hψ' : ∀ γ u, Multiplicative.toAdd (ψ ((marking γ : MulAut U) u)) =
      (burnsideI23x_sd3 F).lift (hA γ) (Multiplicative.toAdd (ψ u)) := fun γ u => by
    rw [hψact]; rfl
  have hxS := burnsideI23x_omega_center_one hF hmb hg
  have hinv : ∀ u' : U, ((marking g⁻¹ : ↥L) : MulAut U) ((marking g : MulAut U) u') = u' := by
    intro u'
    have h1 : marking g⁻¹ * marking g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 := congrArg (fun x : ↥L => ((x : MulAut U) : U ≃* U) u') h1
    simpa using h2
  have hgen : ∀ u' : U,
      ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut U) ((marking g : MulAut U) u') *
        ((marking g : MulAut U) u')⁻¹ =
      (marking g : MulAut U) ((marking (burnsideI23x_tLG hF) : MulAut U) u' * u'⁻¹) := by
    intro u'
    have e1 : ((marking (g * burnsideI23x_tLG hF * g⁻¹) : ↥L) : MulAut U)
        ((marking g : MulAut U) u') =
        (marking g : MulAut U) ((marking (burnsideI23x_tLG hF) : MulAut U) u') := by
      rw [map_mul, map_mul]
      show (marking g : MulAut U) ((marking (burnsideI23x_tLG hF) : MulAut U)
        (((marking g⁻¹ : ↥L) : MulAut U) ((marking g : MulAut U) u'))) = _
      rw [hinv]
    rw [e1, map_mul, map_inv]
  have hcoord : ∀ u' : U, Multiplicative.toAdd (ψ ((marking g : MulAut U)
      ((marking (burnsideI23x_tLG hF) : MulAut U) u' * u'⁻¹))) =
      (burnsideI23x_sd3 F).lift (hA g)
        (q6 ((Multiplicative.toAdd (ψ u')).1 (.inl 2)) 0 0 0 0
          ((Multiplicative.toAdd (ψ u')).1 (.inr 0)), 0) := by
    intro u'
    rw [hψ', map_mul, map_inv, toAdd_mul, toAdd_inv, hψ', ← sub_eq_add_neg,
      burnsideI23x_lift_tL1 hF A hA hAlin]
  have hmemS : ∀ (p : Ix3 → F), p ∈ stdF F 2 → ∃ u' : U,
      Multiplicative.toAdd (ψ ((marking g : MulAut U)
        ((marking (burnsideI23x_tLG hF) : MulAut U) u' * u'⁻¹))) =
        (burnsideI23x_sd3 F).lift (hA g) (p, 0) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.1 hp
    refine ⟨ψ.symm (Multiplicative.ofAdd (q6 0 0 (p (.inl 0)) (p (.inr 2)) 0 0, 0)), ?_⟩
    rw [hcoord, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    congr 1
    refine Prod.ext ?_ rfl
    show q6 ((q6 0 0 (p (.inl 0)) (p (.inr 2)) 0 0 : Ix3 → F) (.inl 2)) 0 0 0 0
      ((q6 0 0 (p (.inl 0)) (p (.inr 2)) 0 0 : Ix3 → F) (.inr 0)) = p
    conv_rhs => rw [q6_eta p]
    rw [h1, h2, h3, h4]
    simp [q6]
  constructor
  · intro hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, v, rfl⟩ := hx
      obtain ⟨u', rfl⟩ := (marking g : MulAut U).surjective v
      rcases (hxS y).1 hy with rfl | rfl
      · refine ⟨0, (stdF F 2).zero_mem, ?_⟩
        show Multiplicative.toAdd (ψ ((1 : MulAut U) ((marking g : MulAut U) u') *
          ((marking g : MulAut U) u')⁻¹)) = _
        rw [MulAut.one_apply, mul_inv_cancel, map_one, toAdd_one, Prod.mk_zero_zero, map_zero]
      · rw [hgen, hcoord]
        refine ⟨q6 ((Multiplicative.toAdd (ψ u')).1 (.inl 2)) 0 0 0 0
          ((Multiplicative.toAdd (ψ u')).1 (.inr 0)), ?_, rfl⟩
        exact mem_stdF_two.2 ⟨rfl, rfl, rfl, rfl⟩
    | one =>
      exact ⟨0, (stdF F 2).zero_mem, by rw [map_one, toAdd_one, Prod.mk_zero_zero, map_zero]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, hp, hpx⟩ := hx
      obtain ⟨p', hp', hpy⟩ := hy
      refine ⟨p + p', (stdF F 2).add_mem hp hp', ?_⟩
      rw [map_mul, toAdd_mul, hpx, hpy, ← map_add]
      congr 1
      simp
    | inv x _ hx =>
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨-p, (stdF F 2).neg_mem hp, ?_⟩
      rw [map_inv, toAdd_inv, hpx, ← map_neg]
      congr 1
      simp
  · rintro ⟨p, hp, hpu⟩
    obtain ⟨u', hu'⟩ := hmemS p hp
    have hu : u = (marking g : MulAut U)
        ((marking (burnsideI23x_tLG hF) : MulAut U) u' * u'⁻¹) := by
      apply ψ.injective
      apply Multiplicative.toAdd.injective
      rw [hpu, hu']
    rw [hu, ← hgen]
    exact Subgroup.subset_closure ⟨_, (hxS _).2 (Or.inr rfl), _, rfl⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.ClassicalInvolution.ModelFacts.OddCover in
theorem burnsideI23x_part1_m3_one
    {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 1) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 3 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 3 F).sec ⧸
      (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec}
    (hsec : I23SectionMap (i23NaturalModel 3 F) L W0 marking β)
    (hT2 : IsPGroup 2 T) (hP : IsSylowTwoOf (T ⊓ L) L)
    {V1 V2 : Subgroup V} (h1 : IsI23MarkedSubspace 3 1 1 F T W0 V1 β)
    (h2 : IsI23MarkedSubspace 3 1 2 F T W0 V2 β)
    (huniv : IsUniversalCovering L W0) :
    ∃ (ψ : V ≃* Multiplicative ↥(zornO0F F)) (π : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L),
      Function.Surjective π ∧
      (∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (v : V),
        ((Multiplicative.toAdd (ψ ((π γ : MulAut V) v)) : ↥(zornO0F F)) : quasithinZorn F) =
          (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
            ((Multiplicative.toAdd (ψ v) : ↥(zornO0F F)) : quasithinZorn F)) ∧
      I23ScalarCompatibility 3 F ψ β ∧
      OrthConclMarked (fun x : ↥(zornO0F F) =>
        CFSG.ASVolI.ChIJK.zornNorm F (x : quasithinZorn F)) 3 1 ψ L T
        (i23TransvectionRoot L W0 V1)
        (CFSG.ASVolI.ChIJK.omegaOne (CFSG.ASVolI.ChIJK.centerOf (T ⊓ L))) V1 V2 := by
  have hF1 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : CharP F 2 := burnsideI23x_charP2_of_card hF1
  have hS := burnsideI23x_scalarAgree3 F
  have hmb := burnsideI23x_marking_bij3 hsec
  have hEndLin : ∀ φ : (Ix3 → F) →+ (Ix3 → F),
      (∀ γ x, φ ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (φ x)) →
      ∃ c : F, ∀ x, φ x = c • x := fun φ hφ => burnsideI23x_hEnd3_one hF1 φ hφ
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM3 F) (burnsideI23x_sd3 F) (burnsideI23x_hsymp3 F) (burnsideI23x_hfaith3 F)
    (burnsideI23x_genW'3_one F hF1) (burnsideI23x_hbound3_one hF1) hV huniv hsec
  have hf := burnsideI23x_isCoord (burnsideI23x_LM3 F) hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  obtain ⟨hU2i, hU2F, hU2c⟩ := burnsideI23x_marked_ell hS hsec h2
  have hU1' : ∀ u, u ∈ V1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img V1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hU2' : ∀ u, u ∈ V2 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img V2 := fun u => by
    rw [hψfst]; exact hU2i u
  have hcard1 : Nat.card (hf.img V1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img V1) hU1F hcard1
  have hψK : ∀ u, u ∈ W0 ↔ (Multiplicative.toAdd (ψ u)).1 = 0 := fun u => by
    rw [hψfst]
    exact (hf.ker u).symm
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_desc1 hF1 marking hmb hP
  have hfl1 : IsFlagW L (T ⊓ L) W0 (2 ^ 1) 1 V1 :=
    burnsideI23x_marked_imp_flag hS hV hsec (fun T' hT' => hEndLin T' hT') h1
  have hfl2 : IsFlagW L (T ⊓ L) W0 (2 ^ 1) 2 V2 :=
    burnsideI23x_marked_imp_flag hS hV hsec (fun T' hT' => hEndLin T' hT') h2
  rw [← hF] at hfl1 hfl2
  have hflag1 : ∀ U', IsFlagW L (T ⊓ L) W0 (2 ^ 1) 1 U' → U' = V1 := by
    intro U' hU'
    rw [← hF] at hU'
    exact (burnsideI23x_flag1_eq hF1 hV hf hEndLin hg hU').trans
      (burnsideI23x_flag1_eq hF1 hV hf hEndLin hg hfl1).symm
  have hfixP : V1 = fixV (T ⊓ L) :=
    le_antisymm (burnsideI23x_SD.line_le_fixV_P ψ marking hπs hψact hT2 he₀ hℓ₁ hU1' h1.2.1)
      (burnsideI23x_fixV_P_le hEndLin hF hV hsec huniv.1 h1.1 hflag1)
  have hV2pre := burnsideI23x_flag2_eq hF1 hV hf hEndLin hg hfl2
  have himg2 : hf.img V2 = (gmapG (burnsideI23x_toCayley g) (stdF F 2)).toAddSubgroup :=
    (congrArg hf.img hV2pre).trans (hf.img_pre _)
  have hcommV := burnsideI23x_commV_S3_one hF1 hmb hg A hA hAlin ψ hψact
  have hSp0 : ∀ p ∈ stdF F 2, (burnsideI23x_sd3 F).Q0 p = 0 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_stdF_two.1 hp
    rw [burnsideI23x_sd3_Q0]
    simp [normQ, h1, h2, h3, h4]
  have hSpdim : Module.finrank F (stdF F 2) = 2 := by
    have hc := card_stdF (F := F) (h := 2) (by norm_num)
    have hc2 := Module.natCard_eq_pow_finrank (K := F) (V := ↥(stdF F 2))
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    exact Nat.pow_right_injective hq (hc2.symm.trans hc)
  have hAg : ∀ x, A g x = g2Act (burnsideI23x_toCayley g) x := fun x =>
    (hAlin g x).trans (burnsideI23x_lin3_apply F g x)
  have hV2' : ∀ u, u ∈ V2 ↔ ∃ p ∈ stdF F 2, (Multiplicative.toAdd (ψ u)).1 = A g p := by
    intro u
    rw [hU2', himg2]
    show _ ∈ gmapG (burnsideI23x_toCayley g) (stdF F 2) ↔ _
    rw [mem_gmapG]
    constructor
    · intro hx
      refine ⟨g2Act (burnsideI23x_toCayley g)⁻¹ (Multiplicative.toAdd (ψ u)).1, hx, ?_⟩
      rw [hAg, g2Act_apply_inv]
    · rintro ⟨p, hp, hpx⟩
      rw [hpx, hAg, g2Act_inv_apply]
      exact hp
  have hscl := burnsideI23x_SD.sclause (burnsideI23x_sd3 F) ψ
    ((burnsideI23x_sd3 F).lift (hA g)) (A g) (fun w => rfl)
    (fun w => (burnsideI23x_sd3 F).Qw_lift (hA g) w) (stdF F 2) hSp0 hSpdim
    (C := commV (CFSG.ASVolI.ChIJK.omegaOne (CFSG.ASVolI.ChIJK.centerOf (T ⊓ L))))
    (K := fixV L) (V2 := V2)
    (fun u => hcommV u) (fun u => by rw [hfixV]; exact hψK u) hV2'
  have hκ := burnsideI23x_kappa3_norm F
  have hcommon := burnsideI23x_SD.orth_common hF
    (fun x : ↥(zornO0F F) => CFSG.ASVolI.ChIJK.zornNorm F (x : quasithinZorn F))
    (burnsideI23x_kappa3 F) hκ ψ hψK hfixV he₀ hℓ₁ hU1' hfixP
  refine ⟨burnsideI23x_SD.psiTrans ψ (burnsideI23x_kappa3 F), marking, hπs, ?_,
    burnsideI23x_scalarCompat hS hψfst (burnsideI23x_kappa3 F), ?_⟩
  · intro γ v
    have h := burnsideI23x_kappa3_lift F A hA hAlin γ (Multiplicative.toAdd (ψ v))
    have h2 : Multiplicative.toAdd (ψ ((marking γ : MulAut V) v)) =
        (burnsideI23x_sd3 F).lift (hA γ) (Multiplicative.toAdd (ψ v)) :=
      congrArg Multiplicative.toAdd (hψact γ v)
    show ((burnsideI23x_kappa3 F (Multiplicative.toAdd (ψ ((marking γ : MulAut V) v))) :
      ↥(zornO0F F)) : quasithinZorn F) = _
    rw [h2]
    exact h
  · refine ⟨hcommon.1, hcommon.2, fun h => absurd rfl h.1, fun h => absurd h.1 (by norm_num),
      fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact (burnsideI23x_SD.isFSubspaceVia_transport ψ (burnsideI23x_kappa3 F) _ 2).1 hscl.1
    · intro v hv
      rw [burnsideI23x_SD.toAdd_psiTrans]
      exact (hκ _).trans (hscl.2.1 v hv)
    · exact hscl.2.2.1
    · exact hscl.2.2.2
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.Explicit
  CFSG.Quasithin.JonesParshall CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model in
theorem burnsideI23x_case_m3_one
    {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 1) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    (hL : L = quasithinGenFitting G) (hGT : G = L ⊔ T) (hT : IsSylowTwoOf T G)
    (hGW0 : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) (hW0 : W0 ≤ fixV L) (hcomm : commV L = ⊤)
    (marking : (i23NaturalModel 3 F).Gam →* ↥L)
    (β : V →* ↥(i23NaturalModel 3 F).sec ⧸
      (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec)
    (hsec : I23SectionMap (i23NaturalModel 3 F) L W0 marking β) :
    burnsideI23x_Concl 3 1 F V G L T W0 marking β := by
  have hF1 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : Finite (MulAut V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  haveI : CharP F 2 := burnsideI23x_charP2_of_card hF1
  have hLG : L ≤ G := by rw [hL]; exact CFSG.Quasithin.quasithinGenFitting_le G
  have hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have h := CFSG.Quasithin.le_normalizer_quasithinGenFitting G hg
    rw [← hL] at h
    exact (Subgroup.mem_normalizer_iff.1 h l).1 hl
  have hTG : T ≤ G := hT.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht => hnorm t (hTG ht)
  have hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0 := fun t ht => hGW0 t (hTG ht)
  have hEndLin : ∀ φ : (Ix3 → F) →+ (Ix3 → F),
      (∀ γ x, φ ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (φ x)) →
      ∃ c : F, ∀ x, φ x = c • x := fun φ hφ => burnsideI23x_hEnd3_one hF1 φ hφ
  have hf := burnsideI23x_isCoord (burnsideI23x_LM3 F) hsec
  have hmb := burnsideI23x_marking_bij3 hsec
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_desc1 hF1 marking hmb hP
  have hflag := burnsideI23x_flags_one hF1 hV hf hEndLin hg
  obtain ⟨V1, V2, h1, h2, h12, u1, u2, f1, f2⟩ :=
    burnsideI23x_marked_flags' (burnsideI23x_scalarAgree3 F) hV hsec hEndLin hTL hTW0 hflag
  have hfixV : fixV L = W0 :=
    burnsideI23x_fixV_eq (burnsideI23x_LM3 F) hsec hW0
      (fun x hx => burnsideI23x_nofix3_one hF1 x hx)
  obtain ⟨t1, t2, t3⟩ := burnsideI23x_transfer burnsideI23x_UCg_three_one hF hV hLG hnorm hGT hT
    hGW0 hW0 hfixV hcomm hsec h1 h2
  refine ⟨V1, V2, h1, h2, u1, u2, ?_⟩
  intro R
  refine ⟨CFSG.ASVolI.ChIJK.omegaOne (CFSG.ASVolI.ChIJK.centerOf (T ⊓ L)),
    fun _ => ⟨⟨(g * burnsideI23x_swapG hF1)⁻¹, ?_⟩, rfl, fun h => absurd h (by norm_num)⟩,
    fun h => absurd h.1 (by norm_num),
    fun huniv => ⟨fun h => absurd h (by omega),
      fun _ => burnsideI23x_part1_m3_one hF hV hsec hT.2.1 hP h1 h2 huniv⟩,
    ⟨t1, (burnsideI23x_centralCoreCompatibility V hV G V1).2 t2.1,
      (burnsideI23x_centralCoreCompatibility V hV G V2).2 t2.2⟩,
    fun hn' => absurd hn' (by norm_num)⟩
  ext x
  exact (burnsideI23x_omega_center_one hF1 hmb hg x).trans
    (burnsideI23x_longroot_one hF1 marking g x).symm

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
@[expose] def burnsideI23x_a6act (σ : Equiv.Perm (Fin 6)) (v : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  B5FinSp.chi (fun i => B5FinSp.phi v (σ⁻¹ i))

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.PresentationLocal Matrix in
theorem burnsideI23x_a6_theta_lfun {F : Type} [Field F] (c : ZMod 2 ≃+* F)
    (σ : Equiv.Perm (Fin 6)) (v : Fin 4 → ZMod 2) :
    (((B5FinSp.theta c σ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ B5FinSp.lfun c v =
      B5FinSp.lfun c (burnsideI23x_a6act σ v) := by
  rw [B5FinSp.theta_mulVec_lfun]
  congr 1
  have h := B5FinSp.chi_permute (omegaEquiv.symm σ) (B5FinSp.phi v) (B5FinSp.sum_phi v)
  have hσ : omegaPerm (omegaEquiv.symm σ) = σ := omegaEquiv.apply_symm_apply σ
  rw [hσ, B5FinSp.chi_phi] at h
  exact h.symm

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_theta_mem_comm {F : Type} [Field F] (c : ZMod 2 ≃+* F)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)) :
    (((B5FinSp.theta c σ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F)) ∈
      ⁅StatedSp 2 F, StatedSp 2 F⁆ := by
  have hcomm : σ ∈ commutator (Equiv.Perm (Fin 6)) := by
    rw [alternatingGroup.commutator_perm_eq (by simp)]
    exact hσ
  clear hσ
  rw [commutator_def, Subgroup.commutator_def] at hcomm
  induction hcomm using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, -, b, -, rfl⟩ := hx
    have h1 := Subgroup.commutator_mem_commutator
      (H₁ := StatedSp 2 F) (H₂ := StatedSp 2 F) (B5FinSp.theta c a).2 (B5FinSp.theta c b).2
    rw [map_commutatorElement]
    exact h1
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
open scoped commutatorElement in
theorem burnsideI23x_comm_mem_theta {F : Type} [Field F] (c : ZMod 2 ≃+* F)
    (γ : GL (Fin 2 ⊕ Fin 2) F) (hγ : γ ∈ ⁅StatedSp 2 F, StatedSp 2 F⁆) :
    ∃ σ : Equiv.Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧
      ((B5FinSp.theta c σ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) = γ := by
  rw [Subgroup.commutator_def] at hγ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨s, hs⟩ := (B5FinSp.theta c).surjective ⟨a, ha⟩
    obtain ⟨t, ht⟩ := (B5FinSp.theta c).surjective ⟨b, hb⟩
    refine ⟨⁅s, t⁆, ?_, ?_⟩
    · rw [← alternatingGroup.commutator_perm_eq (by simp : 5 ≤ Nat.card (Fin 6)), commutator_def,
        Subgroup.commutator_def]
      exact Subgroup.subset_closure ⟨s, Subgroup.mem_top _, t, Subgroup.mem_top _, rfl⟩
    · rw [map_commutatorElement, hs, ht]
      rfl
  | one => exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s * t, Subgroup.mul_mem _ hs ht, by rw [map_mul]; rfl⟩
  | inv x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨s⁻¹, Subgroup.inv_mem _ hs, by rw [map_inv]; rfl⟩

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
@[expose] noncomputable def burnsideI23x_a6ι {F : Type} [Field F] (c : ZMod 2 ≃+* F) :
    ↥(alternatingGroup (Fin 6)) →* ↥⁅StatedSp 2 F, StatedSp 2 F⁆ where
  toFun σ := ⟨((B5FinSp.theta c (σ : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 F)) :
    GL (Fin 2 ⊕ Fin 2) F), burnsideI23x_theta_mem_comm c σ σ.2⟩
  map_one' := by
    apply Subtype.ext
    show ((B5FinSp.theta c (1 : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) = 1
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply Subtype.ext
    show ((B5FinSp.theta c ((σ : Equiv.Perm (Fin 6)) * τ) : ↥(StatedSp 2 F)) :
      GL (Fin 2 ⊕ Fin 2) F) = _
    rw [map_mul]
    rfl

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_a6ι_bijective {F : Type} [Field F] (c : ZMod 2 ≃+* F) :
    Function.Bijective (burnsideI23x_a6ι c) := by
  constructor
  · intro σ τ h
    have h1 := congrArg (fun g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆ => (g : GL (Fin 2 ⊕ Fin 2) F)) h
    have h2 : (B5FinSp.theta c (σ : Equiv.Perm (Fin 6))) = B5FinSp.theta c (τ : Equiv.Perm (Fin 6)) :=
      Subtype.ext h1
    exact Subtype.ext ((B5FinSp.theta c).injective h2)
  · intro γ
    obtain ⟨σ, hσ, hθ⟩ := burnsideI23x_comm_mem_theta c γ.1 γ.2
    exact ⟨⟨σ, hσ⟩, Subtype.ext hθ⟩

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_a6ι_lin {F : Type} [Field F] (c : ZMod 2 ≃+* F)
    (σ : ↥(alternatingGroup (Fin 6))) (v : Fin 4 → ZMod 2) :
    (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c σ) (B5FinSp.lfun c v) =
      B5FinSp.lfun c (burnsideI23x_a6act (σ : Equiv.Perm (Fin 6)) v) := by
  rw [show (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c σ) (B5FinSp.lfun c v) =
    (((burnsideI23x_a6ι c σ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec (B5FinSp.lfun c v) from
    linModelNat_lin _ _ _]
  exact burnsideI23x_a6_theta_lfun c σ v

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
@[expose] def burnsideI23x_pa : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 4 5

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
@[expose] def burnsideI23x_pb : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 3

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
@[expose] def burnsideI23x_pv1 : Fin 4 → ZMod 2 := ![1, 1, 0, 0]

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
theorem burnsideI23x_a6_fix_P1 : ∀ v : Fin 4 → ZMod 2,
    burnsideI23x_a6act burnsideI23x_pa v = v → burnsideI23x_a6act burnsideI23x_pb v = v →
      v = 0 ∨ v = burnsideI23x_pv1 := by
  decide

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
abbrev burnsideI23x_inSpan4 (a b x : Fin 4 → ZMod 2) : Prop := x = 0 ∨ x = a ∨ x = b ∨ x = a + b

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
abbrev burnsideI23x_PlaneInv4 (a b : Fin 4 → ZMod 2) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
    burnsideI23x_inSpan4 a b (burnsideI23x_a6act burnsideI23x_pa a) ∧
    burnsideI23x_inSpan4 a b (burnsideI23x_a6act burnsideI23x_pa b) ∧
    burnsideI23x_inSpan4 a b (burnsideI23x_a6act burnsideI23x_pb a) ∧
    burnsideI23x_inSpan4 a b (burnsideI23x_a6act burnsideI23x_pb b)

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
set_option synthInstance.maxSize 4096 in
theorem burnsideI23x_a6_plane_P1 : ∀ a b : Fin 4 → ZMod 2, burnsideI23x_PlaneInv4 a b →
    ∀ x : Fin 4 → ZMod 2, burnsideI23x_inSpan4 a b x ↔
      burnsideI23x_inSpan4 ![1, 0, 0, 0] ![0, 1, 0, 0] x := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_lfunHom {F : Type} [Field F] (c : ZMod 2 ≃+* F) :
    (Fin 4 → ZMod 2) →+ (Fin 2 ⊕ Fin 2 → F) where
  toFun := B5FinSp.lfun c
  map_zero' := by funext a; simp [B5FinSp.lfun]
  map_add' a b := B5FinSp.lfun_add c a b

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK in
theorem burnsideI23x_a6act_fixes {F : Type} [Field F] (c : ZMod 2 ≃+* F) (σ : Equiv.Perm (Fin 6))
    (hσ : σ ∈ alternatingGroup (Fin 6)) (v : Fin 4 → ZMod 2)
    (h : burnsideI23x_a6act σ v = v) :
    (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨σ, hσ⟩) (B5FinSp.lfun c v) = B5FinSp.lfun c v := by
  rw [burnsideI23x_a6ι_lin]
  exact congrArg _ h

theorem burnsideI23x_pa_even : burnsideI23x_pa ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold burnsideI23x_pa
  decide

theorem burnsideI23x_pb_even : burnsideI23x_pb ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  unfold burnsideI23x_pb
  decide

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_ps1 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def burnsideI23x_ps2 : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 3 4

@[expose] def burnsideI23x_ps3 : Equiv.Perm (Fin 6) :=
  Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def burnsideI23x_ps4 : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 2 3

@[expose] def burnsideI23x_ps5 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem burnsideI23x_ps1_even : burnsideI23x_ps1 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; unfold burnsideI23x_ps1; decide
theorem burnsideI23x_ps2_even : burnsideI23x_ps2 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; unfold burnsideI23x_ps2; decide
theorem burnsideI23x_ps3_even : burnsideI23x_ps3 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; unfold burnsideI23x_ps3; decide
theorem burnsideI23x_ps4_even : burnsideI23x_ps4 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; unfold burnsideI23x_ps4; decide
theorem burnsideI23x_ps5_even : burnsideI23x_ps5 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; unfold burnsideI23x_ps5; decide

@[expose] def burnsideI23x_wvec : Fin 4 → (Fin 4 → ZMod 2) :=
  ![![1, 1, 0, 0], ![1, 0, 1, 0], ![1, 1, 1, 0], ![1, 0, 0, 1]]

theorem burnsideI23x_wvec_span : ∀ x : Fin 4 → ZMod 2, ∃ s : Fin 4 → Bool,
    x = ∑ i, if s i then burnsideI23x_wvec i else 0 := by
  decide +kernel

theorem burnsideI23x_wvec_orbit : ∀ i : Fin 4, ∃ (σ : Equiv.Perm (Fin 6)),
    σ ∈ alternatingGroup (Fin 6) ∧ burnsideI23x_a6act σ burnsideI23x_pv1 = burnsideI23x_wvec i := by
  intro i
  fin_cases i
  · exact ⟨1, Subgroup.one_mem _, by decide +kernel⟩
  · exact ⟨burnsideI23x_ps1, burnsideI23x_ps1_even, by unfold burnsideI23x_ps1; decide +kernel⟩
  · exact ⟨burnsideI23x_ps2, burnsideI23x_ps2_even, by unfold burnsideI23x_ps2; decide +kernel⟩
  · exact ⟨burnsideI23x_ps3, burnsideI23x_ps3_even, by unfold burnsideI23x_ps3; decide +kernel⟩

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_hEnd2_one {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F))
    (hT : ∀ (γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) (x : Fin 2 ⊕ Fin 2 → F),
      T ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (T x)) :
    ∃ c : F, ∀ x, T x = c • x := by
  set c := burnsideI23x_cF F hF with hc
  have hsurj := B5FinSp.lfun_surjective c
  have hinj := B5FinSp.lfun_injective c
  obtain ⟨w, hw⟩ := hsurj (T (B5FinSp.lfun c burnsideI23x_pv1))
  have hfix : ∀ (σ : Equiv.Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)),
      burnsideI23x_a6act σ burnsideI23x_pv1 = burnsideI23x_pv1 →
      burnsideI23x_a6act σ w = w := by
    intro σ hσ h
    have h1 := burnsideI23x_a6act_fixes c σ hσ _ h
    have h2 := hT (burnsideI23x_a6ι c ⟨σ, hσ⟩) (B5FinSp.lfun c burnsideI23x_pv1)
    rw [h1, ← hw, burnsideI23x_a6ι_lin] at h2
    exact hinj h2.symm
  have hw0 := burnsideI23x_a6_fix_P1 w (hfix _ burnsideI23x_pa_even (by decide +kernel))
    (hfix _ burnsideI23x_pb_even (by decide +kernel))
  obtain ⟨c0, hc0⟩ : ∃ c0 : F, T (B5FinSp.lfun c burnsideI23x_pv1) =
      c0 • B5FinSp.lfun c burnsideI23x_pv1 := by
    rcases hw0 with rfl | rfl
    · refine ⟨0, ?_⟩
      rw [zero_smul, ← hw]
      funext a
      simp [B5FinSp.lfun]
    · exact ⟨1, by rw [one_smul, ← hw]⟩
  have horb : ∀ i : Fin 4, T (B5FinSp.lfun c (burnsideI23x_wvec i)) =
      c0 • B5FinSp.lfun c (burnsideI23x_wvec i) := by
    intro i
    obtain ⟨σ, hσ, hσv⟩ := burnsideI23x_wvec_orbit i
    have h1 := burnsideI23x_a6ι_lin c ⟨σ, hσ⟩ burnsideI23x_pv1
    rw [hσv] at h1
    rw [← h1, hT, hc0, map_smul]
  let K0 : AddSubgroup (Fin 2 ⊕ Fin 2 → F) :=
    { carrier := {x | T x = c0 • x}
      add_mem' := fun {x y} hx hy => by
        show T (x + y) = c0 • (x + y)
        rw [map_add, show T x = c0 • x from hx, show T y = c0 • y from hy, smul_add]
      zero_mem' := by
        show T 0 = c0 • (0 : Fin 2 ⊕ Fin 2 → F)
        rw [map_zero, smul_zero]
      neg_mem' := fun {x} hx => by
        show T (-x) = c0 • (-x)
        rw [map_neg, show T x = c0 • x from hx, smul_neg] }
  let K : AddSubgroup (Fin 4 → ZMod 2) := K0.comap (burnsideI23x_lfunHom c)
  have hKall : ∀ v : Fin 4 → ZMod 2, v ∈ K := by
    intro v
    obtain ⟨s, rfl⟩ := burnsideI23x_wvec_span v
    refine AddSubgroup.sum_mem K (fun i _ => ?_)
    split_ifs
    · exact horb i
    · exact K.zero_mem
  refine ⟨c0, fun x => ?_⟩
  obtain ⟨v, rfl⟩ := hsurj x
  exact hKall v

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_nofix2_one {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (x : Fin 2 ⊕ Fin 2 → F) (hx : ∀ γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆,
      (burnsideI23x_LM2 F).lin γ x = x) : x = 0 := by
  set c := burnsideI23x_cF F hF with hc
  have hsurj := B5FinSp.lfun_surjective c
  have hinj := B5FinSp.lfun_injective c
  obtain ⟨w, rfl⟩ := hsurj x
  have hfix : ∀ (σ : Equiv.Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)),
      burnsideI23x_a6act σ w = w := by
    intro σ hσ
    have h2 := hx (burnsideI23x_a6ι c ⟨σ, hσ⟩)
    rw [burnsideI23x_a6ι_lin] at h2
    exact hinj h2
  rcases burnsideI23x_a6_fix_P1 w (hfix _ burnsideI23x_pa_even) (hfix _ burnsideI23x_pb_even)
    with rfl | rfl
  · funext a
    simp [B5FinSp.lfun]
  · exfalso
    have h := hfix _ burnsideI23x_ps1_even
    revert h
    unfold burnsideI23x_ps1
    decide +kernel

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_comm_le_sp (F : Type) [Field F] :
    ⁅StatedSp 2 F, StatedSp 2 F⁆ ≤ StatedSp 2 F := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact (StatedSp 2 F).mul_mem ((StatedSp 2 F).mul_mem ((StatedSp 2 F).mul_mem ha hb)
    ((StatedSp 2 F).inv_mem ha)) ((StatedSp 2 F).inv_mem hb)

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_hsymp2_any (F : Type) [Field F] [CharP F 2]
    (γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) (x y : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_sd2 F).B ((burnsideI23x_LM2 F).lin γ x) ((burnsideI23x_LM2 F).lin γ y) =
      (burnsideI23x_sd2 F).B x y := by
  have hγ : (γ : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := burnsideI23x_comm_le_sp F γ.2
  show bil (((γ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ x)
    (((γ : GL (Fin 2 ⊕ Fin 2) F) : Matrix _ _ F) *ᵥ y) = _
  exact bil_statedSp ⟨(γ : GL (Fin 2 ⊕ Fin 2) F), hγ⟩ x y

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK in
@[expose] def burnsideI23x_q4 (v : Fin 4 → ZMod 2) : ZMod 2 := v 0 * v 3 + v 1 * v 2

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Quasithin.MS93 in
theorem burnsideI23x_sp4Quad_lfun {F : Type} [Field F] (c : ZMod 2 ≃+* F) (v : Fin 4 → ZMod 2) :
    sp4Quad F (B5FinSp.lfun c v) = c (burnsideI23x_q4 v) := by
  simp only [sp4Quad, burnsideI23x_q4, B5FinSp.lfun, map_add, map_mul]
  rfl

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Quasithin.MS93 in
theorem burnsideI23x_a6_pair_mem {F : Type} [Field F] [Finite F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)) (x a : Fin 4 → ZMod 2)
    (z : ZMod 2) (ha : burnsideI23x_a6act σ x + x = a)
    (hz : burnsideI23x_q4 x + burnsideI23x_q4 (burnsideI23x_a6act σ x) = z) :
    (B5FinSp.lfun c a, c z) ∈ AddSubgroup.closure
      {y | ∃ (γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) (x : Fin 2 ⊕ Fin 2 → F),
        y = ((burnsideI23x_LM2 F).lin γ x - x, burnsideI23x_sqrt F ((burnsideI23x_sd2 F).Q0 x +
          (burnsideI23x_sd2 F).Q0 ((burnsideI23x_LM2 F).lin γ x)))} := by
  apply AddSubgroup.subset_closure
  refine ⟨burnsideI23x_a6ι c ⟨σ, hσ⟩, B5FinSp.lfun c x, ?_⟩
  rw [burnsideI23x_a6ι_lin]
  have hQ : ∀ w, (burnsideI23x_sd2 F).Q0 (B5FinSp.lfun c w) = c (burnsideI23x_q4 w) := fun w =>
    burnsideI23x_sp4Quad_lfun c w
  rw [hQ, hQ, ← map_add, hz, burnsideI23x_sqrt_zmod2]
  refine Prod.ext ?_ rfl
  show B5FinSp.lfun c a = B5FinSp.lfun c (burnsideI23x_a6act σ x) - B5FinSp.lfun c x
  rw [← ha, CharTwo.sub_eq_add]
  exact B5FinSp.lfun_add c _ _

@[expose] def burnsideI23x_ypair4 : Fin 5 → (Fin 4 → ZMod 2) × ZMod 2 :=
  ![(![1, 0, 1, 0], 1), (![1, 1, 0, 0], 1), (![0, 0, 1, 0], 1), (![0, 1, 1, 1], 0),
    (![1, 0, 0, 0], 1)]

theorem burnsideI23x_ypair4_span : ∀ p : (Fin 4 → ZMod 2) × ZMod 2, ∃ s : Fin 5 → Bool,
    p = ∑ i, if s i then burnsideI23x_ypair4 i else 0 := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Quasithin.MS93 in
theorem burnsideI23x_genW'2_one (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) :
    (burnsideI23x_sd2 F).GenW' (burnsideI23x_LM2 F).lin := by
  classical
  set c := burnsideI23x_cF F hF with hc
  set C : AddSubgroup ((Fin 2 ⊕ Fin 2 → F) × F) := AddSubgroup.closure
    {y | ∃ (γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) (x : Fin 2 ⊕ Fin 2 → F),
      y = ((burnsideI23x_LM2 F).lin γ x - x, burnsideI23x_sqrt F ((burnsideI23x_sd2 F).Q0 x +
        (burnsideI23x_sd2 F).Q0 ((burnsideI23x_LM2 F).lin γ x)))} with hC
  let Φ : (Fin 4 → ZMod 2) × ZMod 2 →+ (Fin 2 ⊕ Fin 2 → F) × F :=
    AddMonoidHom.prodMap (burnsideI23x_lfunHom c) c.toAddMonoidHom
  let K : AddSubgroup ((Fin 4 → ZMod 2) × ZMod 2) := C.comap Φ
  have hK : ∀ i, burnsideI23x_ypair4 i ∈ K := by
    intro i
    show Φ (burnsideI23x_ypair4 i) ∈ C
    fin_cases i
    · have e1 : burnsideI23x_a6act burnsideI23x_ps1 ![0, 0, 0, 1] + ![0, 0, 0, 1] = ![1, 0, 1, 0] := by
        unfold burnsideI23x_ps1; decide +kernel
      have e2 : burnsideI23x_q4 ![0, 0, 0, 1] +
          burnsideI23x_q4 (burnsideI23x_a6act burnsideI23x_ps1 ![0, 0, 0, 1]) = 1 := by
        unfold burnsideI23x_ps1; decide +kernel
      exact burnsideI23x_a6_pair_mem c _ burnsideI23x_ps1_even _ _ _ e1 e2
    · have e1 : burnsideI23x_a6act burnsideI23x_ps1 ![0, 0, 1, 0] + ![0, 0, 1, 0] = ![1, 1, 0, 0] := by
        unfold burnsideI23x_ps1; decide +kernel
      have e2 : burnsideI23x_q4 ![0, 0, 1, 0] +
          burnsideI23x_q4 (burnsideI23x_a6act burnsideI23x_ps1 ![0, 0, 1, 0]) = 1 := by
        unfold burnsideI23x_ps1; decide +kernel
      exact burnsideI23x_a6_pair_mem c _ burnsideI23x_ps1_even _ _ _ e1 e2
    · have e1 : burnsideI23x_a6act burnsideI23x_ps2 ![0, 1, 0, 0] + ![0, 1, 0, 0] = ![0, 0, 1, 0] := by
        unfold burnsideI23x_ps2; decide +kernel
      have e2 : burnsideI23x_q4 ![0, 1, 0, 0] +
          burnsideI23x_q4 (burnsideI23x_a6act burnsideI23x_ps2 ![0, 1, 0, 0]) = 1 := by
        unfold burnsideI23x_ps2; decide +kernel
      exact burnsideI23x_a6_pair_mem c _ burnsideI23x_ps2_even _ _ _ e1 e2
    · have e1 : burnsideI23x_a6act burnsideI23x_ps4 ![0, 1, 0, 0] + ![0, 1, 0, 0] = ![0, 1, 1, 1] := by
        unfold burnsideI23x_ps4; decide +kernel
      have e2 : burnsideI23x_q4 ![0, 1, 0, 0] +
          burnsideI23x_q4 (burnsideI23x_a6act burnsideI23x_ps4 ![0, 1, 0, 0]) = 0 := by
        unfold burnsideI23x_ps4; decide +kernel
      exact burnsideI23x_a6_pair_mem c _ burnsideI23x_ps4_even _ _ _ e1 e2
    · have e1 : burnsideI23x_a6act burnsideI23x_ps5 ![0, 0, 0, 1] + ![0, 0, 0, 1] = ![1, 0, 0, 0] := by
        unfold burnsideI23x_ps5; decide +kernel
      have e2 : burnsideI23x_q4 ![0, 0, 0, 1] +
          burnsideI23x_q4 (burnsideI23x_a6act burnsideI23x_ps5 ![0, 0, 0, 1]) = 1 := by
        unfold burnsideI23x_ps5; decide +kernel
      exact burnsideI23x_a6_pair_mem c _ burnsideI23x_ps5_even _ _ _ e1 e2
  have hKall : ∀ p : (Fin 4 → ZMod 2) × ZMod 2, p ∈ K := by
    intro p
    obtain ⟨s, rfl⟩ := burnsideI23x_ypair4_span p
    refine AddSubgroup.sum_mem K (fun i _ => ?_)
    split_ifs
    · exact hK i
    · exact K.zero_mem
  intro w
  obtain ⟨x', hx'⟩ := (B5FinSp.lfun_surjective c) w.1
  obtain ⟨z', hz'⟩ := c.surjective w.2
  have := hKall (x', z')
  have hw : Φ (x', z') = w := Prod.ext hx' hz'
  rw [← hw]
  exact this

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_a6act_chi (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    B5FinSp.chi (fun i => x (σ⁻¹ i)) = burnsideI23x_a6act σ (B5FinSp.chi x) := by
  obtain ⟨v, c, rfl⟩ := B5FinSp.exists_phi_of_sum_zero x hx
  have h1 : (fun i => (B5FinSp.phi v + fun _ => c : Fin 6 → ZMod 2) (σ⁻¹ i)) =
      (fun i => B5FinSp.phi v (σ⁻¹ i)) + fun _ => c := by
    funext i
    simp
  rw [h1, B5FinSp.chi_add, B5FinSp.chi_add, B5FinSp.chi_phi, B5FinSp.chi_const, add_zero, add_zero]
  rfl

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_hbound2_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut V)) (W0 : Subgroup V)
        (π : (i23NaturalModel 2 F).Gam →* ↥L),
        (i23NaturalModel 2 F).RealizesVia L ⊤ W0 π → W0 = fixV L → commV L = ⊤ →
        Nat.card W0 ≤ Nat.card F := by
  intro V _ _ hV L W0 π hreal hW0 hcomm
  set c := burnsideI23x_cF F hF with hc
  have hreal' : (FFModel.nat ⁅StatedSp 2 F, StatedSp 2 F⁆).RealizesVia L ⊤ W0 π := hreal
  have hAlt : (FFModel.altDn 6).RealizesVia L ⊤ W0 (π.comp (burnsideI23x_a6ι c)) := by
    refine FFModel.RealizesVia.of_surjHom (FFModel.altDn_isActionModel 6) hreal'
      (burnsideI23x_a6ι c) (burnsideI23x_a6ι_bijective c).2 (B5FinSp.ehat c)
      (B5FinSp.ehat_surjective c) ?_ ?_
    · intro σ₀ m hm
      let σ : ↥(alternatingGroup (Fin 6)) := σ₀
      have hmc : m.1 ∈ G6.coreMod 6 := m.2
      have hx : ∑ i, Multiplicative.toAdd m.1 i = 0 := hmc
      have h2 := burnsideI23x_a6act_chi (σ : Equiv.Perm (Fin 6)) (Multiplicative.toAdd m.1) hx
      have h1 := burnsideI23x_a6_theta_lfun c (σ : Equiv.Perm (Fin 6))
        (B5FinSp.chi (Multiplicative.toAdd m.1))
      apply Multiplicative.toAdd.injective
      show B5FinSp.lfun c (B5FinSp.chi (fun i => Multiplicative.toAdd m.1
        ((σ : Equiv.Perm (Fin 6))⁻¹ i))) =
        (((burnsideI23x_a6ι c σ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
          B5FinSp.lfun c (B5FinSp.chi (Multiplicative.toAdd m.1))
      exact (congrArg (B5FinSp.lfun c) h2).trans h1.symm
    · intro m
      change B5FinSp.lhom c (B5FinSp.chiHom m.1) ∈ (⊥ : Subgroup _) ↔ _
      rw [Subgroup.mem_bot, ← map_one (B5FinSp.lhom c), (B5FinSp.lhom_injective c).eq_iff]
      exact B5FinSp.chiHom_eq_one_iff m.2
  have h := CFSG.Quasithin.H13.VolI.altNaturalCoverSix_holds V hV L W0 (le_of_eq hW0) hcomm
    ⟨π.comp (burnsideI23x_a6ι c), hAlt⟩
  rcases h with h | ⟨h2, -, -⟩
  · rw [h, hF]
    simp
  · rw [h2, hF]

@[expose] def burnsideI23x_P1list : List (Equiv.Perm (Fin 6)) :=
  [1, burnsideI23x_pa, burnsideI23x_pb, burnsideI23x_pa * burnsideI23x_pb,
    burnsideI23x_pb * burnsideI23x_pa, burnsideI23x_pa * burnsideI23x_pb * burnsideI23x_pa,
    burnsideI23x_pb * burnsideI23x_pa * burnsideI23x_pb,
    burnsideI23x_pa * burnsideI23x_pb * burnsideI23x_pa * burnsideI23x_pb]

theorem burnsideI23x_P1list_mul : ∀ x ∈ burnsideI23x_P1list, ∀ y ∈ burnsideI23x_P1list,
    x * y ∈ burnsideI23x_P1list := by
  unfold burnsideI23x_P1list burnsideI23x_pa burnsideI23x_pb
  decide +kernel

theorem burnsideI23x_P1list_inv : ∀ x ∈ burnsideI23x_P1list, x⁻¹ ∈ burnsideI23x_P1list := by
  unfold burnsideI23x_P1list burnsideI23x_pa burnsideI23x_pb
  decide +kernel

theorem burnsideI23x_P1list_nodup : burnsideI23x_P1list.Nodup := by
  unfold burnsideI23x_P1list burnsideI23x_pa burnsideI23x_pb
  decide +kernel

theorem burnsideI23x_P1list_even : ∀ x ∈ burnsideI23x_P1list, x ∈ alternatingGroup (Fin 6) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  unfold burnsideI23x_P1list burnsideI23x_pa burnsideI23x_pb
  decide +kernel

@[expose] def burnsideI23x_P1 : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | σ ∈ burnsideI23x_P1list}
  one_mem' := by
    show (1 : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1list
    unfold burnsideI23x_P1list
    simp
  mul_mem' := fun {a b} ha hb => burnsideI23x_P1list_mul a ha b hb
  inv_mem' := fun {a} ha => burnsideI23x_P1list_inv a ha

theorem burnsideI23x_mem_P1 {σ : Equiv.Perm (Fin 6)} :
    σ ∈ burnsideI23x_P1 ↔ σ ∈ burnsideI23x_P1list := Iff.rfl

theorem burnsideI23x_card_P1 : Nat.card burnsideI23x_P1 = 8 := by
  have hset : ((burnsideI23x_P1 : Subgroup (Equiv.Perm (Fin 6))) : Set (Equiv.Perm (Fin 6))) =
      ↑(burnsideI23x_P1list.toFinset) := by
    ext σ
    simp only [SetLike.mem_coe, burnsideI23x_mem_P1, Finset.mem_coe, List.mem_toFinset]
  calc Nat.card burnsideI23x_P1 = Nat.card ↥((burnsideI23x_P1 : Subgroup (Equiv.Perm (Fin 6))) :
        Set (Equiv.Perm (Fin 6))) := rfl
    _ = Nat.card ↥(↑(burnsideI23x_P1list.toFinset) : Set (Equiv.Perm (Fin 6))) := by rw [hset]
    _ = burnsideI23x_P1list.toFinset.card := Nat.card_eq_finsetCard _
    _ = burnsideI23x_P1list.length := List.toFinset_card_of_nodup burnsideI23x_P1list_nodup
    _ = 8 := rfl

open CFSG.QuasithinUnique in
theorem burnsideI23x_P1_sylow : IsSylowTwoOf burnsideI23x_P1 (alternatingGroup (Fin 6)) := by
  have hle : burnsideI23x_P1 ≤ alternatingGroup (Fin 6) :=
    fun σ hσ => burnsideI23x_P1list_even σ hσ
  refine ⟨hle, IsPGroup.of_card (n := 3) (by rw [burnsideI23x_card_P1]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index (burnsideI23x_P1.subgroupOf (alternatingGroup (Fin 6)))
  have h2 : Nat.card ↥(burnsideI23x_P1.subgroupOf (alternatingGroup (Fin 6))) = 8 := by
    rw [← burnsideI23x_card_P1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h3 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  rw [h2, h3] at h1
  intro hdvd
  omega

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_marking_bij2 {F : Type} [Field F] [CharP F 2] {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 2 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 2 F).sec ⧸
      (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec}
    (hsec : I23SectionMap (i23NaturalModel 2 F) L W0 marking β) :
    Function.Bijective marking := by
  have hf := burnsideI23x_isCoord (burnsideI23x_LM2 F) hsec
  refine ⟨?_, hsec.1⟩
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply burnsideI23x_hfaith2
  intro x
  obtain ⟨v, rfl⟩ := hf.surj x
  rw [← hf.act, hγ]
  rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique in
theorem burnsideI23x_sylow_desc2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (marking : ↥⁅StatedSp 2 F, StatedSp 2 F⁆ →* ↥L) (hmb : Function.Bijective marking)
    {P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P L) :
    ∃ g : ↥(alternatingGroup (Fin 6)), ∀ x : MulAut V, x ∈ P ↔
      ∃ u : ↥(alternatingGroup (Fin 6)), (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧
        x = ((marking (burnsideI23x_a6ι (burnsideI23x_cF F hF) (g * u * g⁻¹)) : ↥L) :
          MulAut V) := by
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_desc (G := alternatingGroup (Fin 6))
    (Γ := alternatingGroup (Fin 6)) (U := burnsideI23x_P1) le_rfl
    (fun g hg l hl => (alternatingGroup (Fin 6)).mul_mem
      ((alternatingGroup (Fin 6)).mul_mem hg hl) ((alternatingGroup (Fin 6)).inv_mem hg))
    burnsideI23x_P1_sylow (marking.comp (burnsideI23x_a6ι (burnsideI23x_cF F hF)))
    (hmb.comp (burnsideI23x_a6ι_bijective _)) hP
  exact ⟨g, hg⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_lin2_mul {F : Type} [Field F] (a b : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin (a * b) x =
      (burnsideI23x_LM2 F).lin a ((burnsideI23x_LM2 F).lin b x) := by
  show (linModelNat ⁅StatedSp 2 F, StatedSp 2 F⁆).lin (a * b) x = (linModelNat _).lin a
    ((linModelNat _).lin b x)
  rw [linModelNat_lin, linModelNat_lin, linModelNat_lin, Subgroup.coe_mul, Units.val_mul,
    Matrix.mulVec_mulVec]

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_lin2_one {F : Type} [Field F] (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin (1 : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) x = x := by
  have h : (linModelNat ⁅StatedSp 2 F, StatedSp 2 F⁆).lin 1 x =
      (((1 : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec x := linModelNat_lin _ _ _
  exact h.trans (by simp)

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_lin2_inv_lin {F : Type} [Field F] (a : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin a ((burnsideI23x_LM2 F).lin a⁻¹ x) = x := by
  have h := (burnsideI23x_lin2_mul a a⁻¹ x).symm
  rw [mul_inv_cancel] at h
  exact h.trans (burnsideI23x_lin2_one x)

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_lin2_lin_inv {F : Type} [Field F] (a : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin a⁻¹ ((burnsideI23x_LM2 F).lin a x) = x := by
  have h := (burnsideI23x_lin2_mul a⁻¹ a x).symm
  rw [inv_mul_cancel] at h
  exact h.trans (burnsideI23x_lin2_one x)

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
@[expose] noncomputable def burnsideI23x_gm2 {F : Type} [Field F] (g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)) : AddSubgroup (Fin 2 ⊕ Fin 2 → F) :=
  S.comap ((burnsideI23x_LM2 F).lin g⁻¹).toAddMonoidHom

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_mem_gm2 {F : Type} [Field F] {g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆}
    {S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)} {x : Fin 2 ⊕ Fin 2 → F} :
    x ∈ burnsideI23x_gm2 g S ↔ (burnsideI23x_LM2 F).lin g⁻¹ x ∈ S := Iff.rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_gm2_gm2_inv {F : Type} [Field F] (g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)) :
    burnsideI23x_gm2 g (burnsideI23x_gm2 g⁻¹ S) = S := by
  ext x
  exact iff_of_eq (congrArg (· ∈ S) (burnsideI23x_lin2_lin_inv g⁻¹ x))

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_card_gm2 {F : Type} [Field F] (g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)) :
    Nat.card (burnsideI23x_gm2 g S) = Nat.card S := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(burnsideI23x_LM2 F).lin g⁻¹ x.1, x.2⟩
      invFun := fun y => ⟨(burnsideI23x_LM2 F).lin g y.1, by
        show (burnsideI23x_LM2 F).lin g⁻¹ ((burnsideI23x_LM2 F).lin g y.1) ∈ S
        rw [burnsideI23x_lin2_lin_inv]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (burnsideI23x_lin2_inv_lin g x.1)
      right_inv := fun y => Subtype.ext (burnsideI23x_lin2_lin_inv g y.1) }

@[expose] def burnsideI23x_aL2 (F : Type) [Field F] : AddSubgroup (Fin 2 ⊕ Fin 2 → F) where
  carrier := {x | x (.inr 0) = 0 ∧ x (.inr 1) = 0}
  add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  neg_mem' := fun {x} hx => ⟨by simp [hx.1], by simp [hx.2]⟩

@[expose] def burnsideI23x_aL1 (F : Type) [Field F] : AddSubgroup (Fin 2 ⊕ Fin 2 → F) where
  carrier := {x | x (.inr 0) = 0 ∧ x (.inr 1) = 0 ∧ x (.inl 0) = x (.inl 1)}
  add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2.1, hy.2.1],
    by simp [hx.2.2, hy.2.2]⟩
  zero_mem' := ⟨rfl, rfl, rfl⟩
  neg_mem' := fun {x} hx => ⟨by simp [hx.1], by simp [hx.2.1], by simp [hx.2.2]⟩

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
theorem burnsideI23x_mem_aL2_lfun {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Fin 4 → ZMod 2) :
    B5FinSp.lfun c w ∈ burnsideI23x_aL2 F ↔ w 2 = 0 ∧ w 3 = 0 := by
  show (B5FinSp.lfun c w (.inr 0) = 0 ∧ B5FinSp.lfun c w (.inr 1) = 0) ↔ _
  have h0 : ∀ y : ZMod 2, c y = 0 ↔ y = 0 := fun y => by
    rw [← map_zero c]; exact c.injective.eq_iff
  simp only [B5FinSp.lfun, h0]
  exact and_comm.trans Iff.rfl

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
theorem burnsideI23x_mem_aL1_lfun {F : Type} [Field F] (c : ZMod 2 ≃+* F) (w : Fin 4 → ZMod 2) :
    B5FinSp.lfun c w ∈ burnsideI23x_aL1 F ↔ w 2 = 0 ∧ w 3 = 0 ∧ w 0 = w 1 := by
  show (B5FinSp.lfun c w (.inr 0) = 0 ∧ B5FinSp.lfun c w (.inr 1) = 0 ∧
    B5FinSp.lfun c w (.inl 0) = B5FinSp.lfun c w (.inl 1)) ↔ _
  have h0 : ∀ y : ZMod 2, c y = 0 ↔ y = 0 := fun y => by
    rw [← map_zero c]; exact c.injective.eq_iff
  simp only [B5FinSp.lfun, h0, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, h3⟩

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
theorem burnsideI23x_card_aL2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (burnsideI23x_aL2 F) = 4 := by
  set c := burnsideI23x_cF F hF
  have hbij : Function.Bijective (fun w : {w : Fin 4 → ZMod 2 // w 2 = 0 ∧ w 3 = 0} =>
      (⟨B5FinSp.lfun c w.1, (burnsideI23x_mem_aL2_lfun c w.1).2 w.2⟩ : ↥(burnsideI23x_aL2 F))) := by
    constructor
    · intro w w' h
      exact Subtype.ext (B5FinSp.lfun_injective c (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      obtain ⟨w, rfl⟩ := B5FinSp.lfun_surjective c x
      exact ⟨⟨w, (burnsideI23x_mem_aL2_lfun c w).1 hx⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  decide

open CFSG.Quasithin CFSG.Quasithin.B5FinSp in
theorem burnsideI23x_card_aL1 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (burnsideI23x_aL1 F) = 2 := by
  set c := burnsideI23x_cF F hF
  have hbij : Function.Bijective (fun w : {w : Fin 4 → ZMod 2 // w 2 = 0 ∧ w 3 = 0 ∧ w 0 = w 1} =>
      (⟨B5FinSp.lfun c w.1, (burnsideI23x_mem_aL1_lfun c w.1).2 w.2⟩ : ↥(burnsideI23x_aL1 F))) := by
    constructor
    · intro w w' h
      exact Subtype.ext (B5FinSp.lfun_injective c (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      obtain ⟨w, rfl⟩ := B5FinSp.lfun_surjective c x
      exact ⟨⟨w, (burnsideI23x_mem_aL1_lfun c w).1 hx⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
  decide

theorem burnsideI23x_aL2_smul {F : Type} [Field F] (a : F) (x : Fin 2 ⊕ Fin 2 → F)
    (hx : x ∈ burnsideI23x_aL2 F) : a • x ∈ burnsideI23x_aL2 F :=
  ⟨by simp [hx.1], by simp [hx.2]⟩

theorem burnsideI23x_aL1_smul {F : Type} [Field F] (a : F) (x : Fin 2 ⊕ Fin 2 → F)
    (hx : x ∈ burnsideI23x_aL1 F) : a • x ∈ burnsideI23x_aL1 F :=
  ⟨by simp [hx.1], by simp [hx.2.1], by simp [hx.2.2]⟩

theorem burnsideI23x_P1_stab_L2 : ∀ σ ∈ burnsideI23x_P1list, ∀ w : Fin 4 → ZMod 2,
    ((w 2 = 0 ∧ w 3 = 0) ↔ ((burnsideI23x_a6act σ w) 2 = 0 ∧ (burnsideI23x_a6act σ w) 3 = 0)) := by
  unfold burnsideI23x_P1list burnsideI23x_pa burnsideI23x_pb
  decide +kernel

theorem burnsideI23x_P1_stab_L1 : ∀ σ ∈ burnsideI23x_P1list, ∀ w : Fin 4 → ZMod 2,
    ((w 2 = 0 ∧ w 3 = 0 ∧ w 0 = w 1) ↔
      ((burnsideI23x_a6act σ w) 2 = 0 ∧ (burnsideI23x_a6act σ w) 3 = 0 ∧
        (burnsideI23x_a6act σ w) 0 = (burnsideI23x_a6act σ w) 1)) := by
  unfold burnsideI23x_P1list burnsideI23x_pa burnsideI23x_pb
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_P1_stab_aL2 {F : Type} [Field F] (c : ZMod 2 ≃+* F)
    (u : ↥(alternatingGroup (Fin 6))) (hu : (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1)
    (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c u) x ∈ burnsideI23x_aL2 F ↔
      x ∈ burnsideI23x_aL2 F := by
  obtain ⟨w, rfl⟩ := B5FinSp.lfun_surjective c x
  rw [burnsideI23x_a6ι_lin, burnsideI23x_mem_aL2_lfun, burnsideI23x_mem_aL2_lfun]
  exact (burnsideI23x_P1_stab_L2 _ hu w).symm

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_P1_stab_aL1 {F : Type} [Field F] (c : ZMod 2 ≃+* F)
    (u : ↥(alternatingGroup (Fin 6))) (hu : (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1)
    (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c u) x ∈ burnsideI23x_aL1 F ↔
      x ∈ burnsideI23x_aL1 F := by
  obtain ⟨w, rfl⟩ := B5FinSp.lfun_surjective c x
  rw [burnsideI23x_a6ι_lin, burnsideI23x_mem_aL1_lfun, burnsideI23x_mem_aL1_lfun]
  exact (burnsideI23x_P1_stab_L1 _ hu w).symm

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_lin2_conj {F : Type} [Field F] (a b : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin a⁻¹ ((burnsideI23x_LM2 F).lin (a * b * a⁻¹) x) =
      (burnsideI23x_LM2 F).lin b ((burnsideI23x_LM2 F).lin a⁻¹ x) := by
  have e : a⁻¹ * (a * b * a⁻¹) = b * a⁻¹ := by group
  exact (burnsideI23x_lin2_mul a⁻¹ (a * b * a⁻¹) x).symm.trans
    ((congrArg (fun t => (burnsideI23x_LM2 F).lin t x) e).trans (burnsideI23x_lin2_mul b a⁻¹ x))

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_lin2_conj' {F : Type} [Field F] (a b : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin (a * b * a⁻¹) ((burnsideI23x_LM2 F).lin a x) =
      (burnsideI23x_LM2 F).lin a ((burnsideI23x_LM2 F).lin b x) := by
  have e : a * b * a⁻¹ * a = a * b := by group
  exact (burnsideI23x_lin2_mul (a * b * a⁻¹) a x).symm.trans
    ((congrArg (fun t => (burnsideI23x_LM2 F).lin t x) e).trans (burnsideI23x_lin2_mul a b x))

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_isFlagW_pre_a6 {F : Type} [Field F] [Finite F] [CharP F 2]
    (c : ZMod 2 ≃+* F) {V : Type} [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1)
    {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 2 F).Gam →* ↥L} {f : V → (Fin 2 ⊕ Fin 2 → F)}
    (hf : IsCoord (burnsideI23x_LM2 F) L W0 marking f)
    (hcomm : ∀ T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ (γ : (i23NaturalModel 2 F).Gam) (x : Fin 2 ⊕ Fin 2 → F),
        T ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (T x)) →
      ∃ a : F, ∀ x, T x = a • x)
    {P : Subgroup (MulAut V)} {g : ↥(alternatingGroup (Fin 6))}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥(alternatingGroup (Fin 6)),
      (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧
        x = ((marking (burnsideI23x_a6ι c (g * u * g⁻¹)) : ↥L) : MulAut V))
    {S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)} (hSsmul : ∀ (a : F) (x : Fin 2 ⊕ Fin 2 → F),
      x ∈ S → a • x ∈ S)
    (hS : ∀ u : ↥(alternatingGroup (Fin 6)), (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 →
      ∀ x, (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c u) x ∈ S ↔ x ∈ S)
    {i : ℕ} (hcard : Nat.card S = Nat.card F ^ i) :
    IsFlagW L P W0 (Nat.card F) i
      (hf.pre (burnsideI23x_gm2 (burnsideI23x_a6ι c g) S)) := by
  refine ⟨hf.le_pre _, ?_, ?_, fun x hx => ?_⟩
  · rw [hf.endStableW_iff hV hcomm (hf.le_pre _), hf.img_pre]
    intro a x hx
    rw [burnsideI23x_mem_gm2] at hx ⊢
    have : (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c g)⁻¹ (a • x) =
        a • (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c g)⁻¹ x := map_smul _ _ _
    rw [this]
    exact hSsmul a _ hx
  · rw [← hf.card_img, hf.img_pre, ← hcard, burnsideI23x_card_gm2]
  · obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
    rw [IsCoord.mem_stabW_iff hf (hf.le_pre _) (burnsideI23x_a6ι c (g * u * g⁻¹)), hf.img_pre]
    intro y
    rw [burnsideI23x_mem_gm2, burnsideI23x_mem_gm2]
    have e1 : burnsideI23x_a6ι c (g * u * g⁻¹) = burnsideI23x_a6ι c g * burnsideI23x_a6ι c u *
        (burnsideI23x_a6ι c g)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rw [e1]
    rw [burnsideI23x_lin2_conj]
    exact (hS u hu _).symm

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
@[expose] noncomputable def burnsideI23x_cm2 {F : Type} [Field F] (g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)) : AddSubgroup (Fin 2 ⊕ Fin 2 → F) :=
  S.comap ((burnsideI23x_LM2 F).lin g).toAddMonoidHom

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_mem_cm2 {F : Type} [Field F] {g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆}
    {S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)} {x : Fin 2 ⊕ Fin 2 → F} :
    x ∈ burnsideI23x_cm2 g S ↔ (burnsideI23x_LM2 F).lin g x ∈ S := Iff.rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_gm2_cm2 {F : Type} [Field F] (g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)) :
    burnsideI23x_gm2 g (burnsideI23x_cm2 g S) = S := by
  ext x
  exact iff_of_eq (congrArg (· ∈ S) (burnsideI23x_lin2_inv_lin g x))

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_card_cm2 {F : Type} [Field F] (g : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (S : AddSubgroup (Fin 2 ⊕ Fin 2 → F)) :
    Nat.card (burnsideI23x_cm2 g S) = Nat.card S := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(burnsideI23x_LM2 F).lin g x.1, x.2⟩
      invFun := fun y => ⟨(burnsideI23x_LM2 F).lin g⁻¹ y.1, by
        show (burnsideI23x_LM2 F).lin g ((burnsideI23x_LM2 F).lin g⁻¹ y.1) ∈ S
        rw [burnsideI23x_lin2_inv_lin]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (burnsideI23x_lin2_lin_inv g x.1)
      right_inv := fun y => Subtype.ext (burnsideI23x_lin2_inv_lin g y.1) }

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_exists_eq_pre_a6 {F : Type} [Field F] [Finite F] [CharP F 2]
    (c : ZMod 2 ≃+* F) {V : Type} [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1)
    {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 2 F).Gam →* ↥L} {f : V → (Fin 2 ⊕ Fin 2 → F)}
    (hf : IsCoord (burnsideI23x_LM2 F) L W0 marking f)
    (hcomm : ∀ T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ (γ : (i23NaturalModel 2 F).Gam) (x : Fin 2 ⊕ Fin 2 → F),
        T ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (T x)) →
      ∃ a : F, ∀ x, T x = a • x)
    {P : Subgroup (MulAut V)} {g : ↥(alternatingGroup (Fin 6))}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥(alternatingGroup (Fin 6)),
      (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧
        x = ((marking (burnsideI23x_a6ι c (g * u * g⁻¹)) : ↥L) : MulAut V))
    {i : ℕ} {U : Subgroup V} (hU : IsFlagW L P W0 (Nat.card F) i U) :
    ∃ S : AddSubgroup (Fin 2 ⊕ Fin 2 → F),
      (∀ (a : F) (x : Fin 2 ⊕ Fin 2 → F), x ∈ S → a • x ∈ S) ∧
      (∀ u : ↥(alternatingGroup (Fin 6)), (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 →
        ∀ x, (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c u) x ∈ S ↔ x ∈ S) ∧
      Nat.card S = Nat.card F ^ i ∧
      U = hf.pre (burnsideI23x_gm2 (burnsideI23x_a6ι c g) S) := by
  obtain ⟨hZU, hst, hidx, hPU⟩ := hU
  have hsc := (hf.endStableW_iff hV hcomm hZU).mp hst
  refine ⟨burnsideI23x_cm2 (burnsideI23x_a6ι c g) (hf.img U), ?_, ?_, ?_, ?_⟩
  · intro a x hx
    rw [burnsideI23x_mem_cm2] at hx ⊢
    have : (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c g) (a • x) =
        a • (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c g) x := map_smul _ _ _
    rw [this]
    exact hsc a _ hx
  · intro u hu x
    have hp : ((marking (burnsideI23x_a6ι c (g * u * g⁻¹)) : ↥L) : MulAut V) ∈ stabW U :=
      hPU ((hg _).mpr ⟨u, hu, rfl⟩)
    have h1 := (IsCoord.mem_stabW_iff hf hZU _).mp hp ((burnsideI23x_LM2 F).lin
      (burnsideI23x_a6ι c g) x)
    have e1 : burnsideI23x_a6ι c (g * u * g⁻¹) = burnsideI23x_a6ι c g * burnsideI23x_a6ι c u *
        (burnsideI23x_a6ι c g)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rw [e1] at h1
    rw [burnsideI23x_lin2_conj'] at h1
    rw [burnsideI23x_mem_cm2, burnsideI23x_mem_cm2]
    exact h1.symm
  · rw [burnsideI23x_card_cm2, ← hidx, ← hf.card_img]
  · rw [burnsideI23x_gm2_cm2]
    exact (hf.pre_img hZU).symm

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_lin2_inj_zero {F : Type} [Field F] (γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆)
    (x : Fin 2 ⊕ Fin 2 → F) (h : (burnsideI23x_LM2 F).lin γ x = 0) : x = 0 := by
  have := burnsideI23x_lin2_lin_inv γ x
  rw [h, map_zero] at this
  exact this.symm

theorem burnsideI23x_pa_mem_P1 : burnsideI23x_pa ∈ burnsideI23x_P1 := by
  show burnsideI23x_pa ∈ burnsideI23x_P1list
  unfold burnsideI23x_P1list
  simp

theorem burnsideI23x_pb_mem_P1 : burnsideI23x_pb ∈ burnsideI23x_P1 := by
  show burnsideI23x_pb ∈ burnsideI23x_P1list
  unfold burnsideI23x_P1list
  simp

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_eq_aL1_a6 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (S : AddSubgroup (Fin 2 ⊕ Fin 2 → F))
    (hSsmul : ∀ (a : F) (x : Fin 2 ⊕ Fin 2 → F), x ∈ S → a • x ∈ S)
    (hS : ∀ u : ↥(alternatingGroup (Fin 6)), (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 →
      ∀ x, (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι (burnsideI23x_cF F hF) u) x ∈ S ↔ x ∈ S)
    (hcard : Nat.card S = Nat.card F ^ 1) : S = burnsideI23x_aL1 F := by
  set c := burnsideI23x_cF F hF with hc
  obtain ⟨e₀, he₀, hℓ⟩ := burnsideI23x_line_of_card S hSsmul (by rw [hcard, pow_one])
  obtain ⟨w, rfl⟩ := B5FinSp.lfun_surjective c e₀
  have hfix : ∀ (σ : Equiv.Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)),
      (σ ∈ burnsideI23x_P1) → burnsideI23x_a6act σ w = w := by
    intro σ hσ hP1
    have h1 := (hS ⟨σ, hσ⟩ hP1 (B5FinSp.lfun c w)).2 ((hℓ _).2 ⟨1, (one_smul F _).symm⟩)
    obtain ⟨a, ha⟩ := (hℓ _).1 h1
    rw [burnsideI23x_a6ι_lin] at ha
    rcases burnsideI23x_h01 hF a with rfl | rfl
    · rw [zero_smul] at ha
      exfalso
      apply he₀
      have h2 : (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨σ, hσ⟩) (B5FinSp.lfun c w) = 0 := by
        rw [burnsideI23x_a6ι_lin]; exact ha
      exact burnsideI23x_lin2_inj_zero _ _ h2
    · rw [one_smul] at ha
      exact B5FinSp.lfun_injective c ha
  have hw := burnsideI23x_a6_fix_P1 w (hfix _ burnsideI23x_pa_even burnsideI23x_pa_mem_P1)
    (hfix _ burnsideI23x_pb_even burnsideI23x_pb_mem_P1)
  have hw0 : w = burnsideI23x_pv1 := by
    rcases hw with h | h
    · exfalso
      apply he₀
      rw [h]
      funext a
      simp [B5FinSp.lfun]
    · exact h
  subst hw0
  have hsp : ∀ w' : Fin 4 → ZMod 2, (w' 2 = 0 ∧ w' 3 = 0 ∧ w' 0 = w' 1) →
      w' = 0 ∨ w' = burnsideI23x_pv1 := by
    unfold burnsideI23x_pv1
    decide
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := (hℓ x).1 hx
    rcases burnsideI23x_h01 hF a with rfl | rfl
    · rw [zero_smul]; exact (burnsideI23x_aL1 F).zero_mem
    · rw [one_smul]
      exact (burnsideI23x_mem_aL1_lfun c _).2 (by unfold burnsideI23x_pv1; decide)
  · intro hx
    obtain ⟨w', rfl⟩ := B5FinSp.lfun_surjective c x
    rcases hsp w' ((burnsideI23x_mem_aL1_lfun c w').1 hx) with rfl | rfl
    · have : B5FinSp.lfun c (0 : Fin 4 → ZMod 2) = 0 := by
        funext a; simp [B5FinSp.lfun]
      rw [this]; exact S.zero_mem
    · exact (hℓ _).2 ⟨1, (one_smul F _).symm⟩

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_eq_aL2_a6 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (S : AddSubgroup (Fin 2 ⊕ Fin 2 → F))
    (hS : ∀ u : ↥(alternatingGroup (Fin 6)), (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 →
      ∀ x, (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι (burnsideI23x_cF F hF) u) x ∈ S ↔ x ∈ S)
    (hcard : Nat.card S = Nat.card F ^ 2) : S = burnsideI23x_aL2 F := by
  set c := burnsideI23x_cF F hF with hc
  have h4 : Nat.card S = 4 := by rw [hcard, hF]; norm_num
  have hdbl : ∀ x : Fin 2 ⊕ Fin 2 → F, x + x = 0 := fun x => by
    funext i; exact CharTwo.add_self_eq_zero _
  obtain ⟨a, b, ha, hb, ha0, hb0, hab, hmem⟩ := burnsideI23x_card_four hdbl S h4
  obtain ⟨a', rfl⟩ := B5FinSp.lfun_surjective c a
  obtain ⟨b', rfl⟩ := B5FinSp.lfun_surjective c b
  have hemb : ∀ w w' : Fin 4 → ZMod 2, B5FinSp.lfun c w + B5FinSp.lfun c w' =
      B5FinSp.lfun c (w + w') := fun w w' => (B5FinSp.lfun_add c w w').symm
  have hemb0 : B5FinSp.lfun c (0 : Fin 4 → ZMod 2) = 0 := by
    funext i; simp [B5FinSp.lfun]
  have hinj := B5FinSp.lfun_injective c
  have tr : ∀ (σ : Equiv.Perm (Fin 6)) (hσ : σ ∈ alternatingGroup (Fin 6)),
      σ ∈ burnsideI23x_P1 → ∀ w, B5FinSp.lfun c w ∈ S →
        burnsideI23x_a6act σ w = 0 ∨ burnsideI23x_a6act σ w = a' ∨ burnsideI23x_a6act σ w = b' ∨
          burnsideI23x_a6act σ w = a' + b' := by
    intro σ hσ hP1 w hw
    have h1 := (hS ⟨σ, hσ⟩ hP1 _).2 hw
    rw [burnsideI23x_a6ι_lin, hmem] at h1
    rcases h1 with h | h | h | h
    · left; exact hinj (by rw [h, hemb0])
    · right; left; exact hinj h
    · right; right; left; exact hinj h
    · right; right; right; exact hinj (by rw [h, ← hemb])
  have a0' : a' ≠ 0 := fun h => ha0 (by rw [h, hemb0])
  have b0' : b' ≠ 0 := fun h => hb0 (by rw [h, hemb0])
  have ab' : a' ≠ b' := fun h => hab (by rw [h])
  have t1a := tr _ burnsideI23x_pa_even burnsideI23x_pa_mem_P1 a' ha
  have t1b := tr _ burnsideI23x_pa_even burnsideI23x_pa_mem_P1 b' hb
  have t2a := tr _ burnsideI23x_pb_even burnsideI23x_pb_mem_P1 a' ha
  have t2b := tr _ burnsideI23x_pb_even burnsideI23x_pb_mem_P1 b' hb
  have hk := burnsideI23x_a6_plane_P1 a' b' ⟨a0', b0', ab', t1a, t1b, t2a, t2b⟩
  have hspan : ∀ y : Fin 4 → ZMod 2, burnsideI23x_inSpan4 ![1, 0, 0, 0] ![0, 1, 0, 0] y ↔
      (y 2 = 0 ∧ y 3 = 0) := by decide
  ext x
  obtain ⟨x', rfl⟩ := B5FinSp.lfun_surjective c x
  rw [hmem]
  have h1 : (B5FinSp.lfun c x' = 0 ∨ B5FinSp.lfun c x' = B5FinSp.lfun c a' ∨
      B5FinSp.lfun c x' = B5FinSp.lfun c b' ∨
      B5FinSp.lfun c x' = B5FinSp.lfun c a' + B5FinSp.lfun c b') ↔
      burnsideI23x_inSpan4 a' b' x' := by
    rw [hemb, ← hemb0]
    simp only [hinj.eq_iff]
  rw [h1, hk x', hspan, burnsideI23x_mem_aL2_lfun]

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_flag1_eq_a6 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {V : Type} [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1) {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {marking : (i23NaturalModel 2 F).Gam →* ↥L} {f : V → (Fin 2 ⊕ Fin 2 → F)}
    (hf : IsCoord (burnsideI23x_LM2 F) L W0 marking f)
    (hcomm : ∀ T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ (γ : (i23NaturalModel 2 F).Gam) (x : Fin 2 ⊕ Fin 2 → F),
        T ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (T x)) →
      ∃ a : F, ∀ x, T x = a • x)
    {P : Subgroup (MulAut V)} {g : ↥(alternatingGroup (Fin 6))}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥(alternatingGroup (Fin 6)),
      (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧
        x = ((marking (burnsideI23x_a6ι (burnsideI23x_cF F hF) (g * u * g⁻¹)) : ↥L) : MulAut V))
    {U : Subgroup V} (hU : IsFlagW L P W0 (Nat.card F) 1 U) :
    U = hf.pre (burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF) g)
      (burnsideI23x_aL1 F)) := by
  obtain ⟨S, hSs, hSst, hc, rfl⟩ := burnsideI23x_exists_eq_pre_a6 (burnsideI23x_cF F hF) hV hf
    hcomm hg hU
  rw [burnsideI23x_eq_aL1_a6 hF S hSs hSst hc]

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_flag2_eq_a6 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {V : Type} [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1) {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {marking : (i23NaturalModel 2 F).Gam →* ↥L} {f : V → (Fin 2 ⊕ Fin 2 → F)}
    (hf : IsCoord (burnsideI23x_LM2 F) L W0 marking f)
    (hcomm : ∀ T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ (γ : (i23NaturalModel 2 F).Gam) (x : Fin 2 ⊕ Fin 2 → F),
        T ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (T x)) →
      ∃ a : F, ∀ x, T x = a • x)
    {P : Subgroup (MulAut V)} {g : ↥(alternatingGroup (Fin 6))}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥(alternatingGroup (Fin 6)),
      (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧
        x = ((marking (burnsideI23x_a6ι (burnsideI23x_cF F hF) (g * u * g⁻¹)) : ↥L) : MulAut V))
    {U : Subgroup V} (hU : IsFlagW L P W0 (Nat.card F) 2 U) :
    U = hf.pre (burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF) g)
      (burnsideI23x_aL2 F)) := by
  obtain ⟨S, hSs, hSst, hc, rfl⟩ := burnsideI23x_exists_eq_pre_a6 (burnsideI23x_cF F hF) hV hf
    hcomm hg hU
  rw [burnsideI23x_eq_aL2_a6 hF S hSst hc]

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA in
theorem burnsideI23x_flags_two_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {V : Type} [CommGroup V] (hV : ∀ w : V, w ^ 2 = 1)
    {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 2 F).Gam →* ↥L} {f : V → (Fin 2 ⊕ Fin 2 → F)}
    (hf : IsCoord (burnsideI23x_LM2 F) L W0 marking f)
    (hcomm : ∀ T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ (γ : (i23NaturalModel 2 F).Gam) (x : Fin 2 ⊕ Fin 2 → F),
        T ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (T x)) →
      ∃ a : F, ∀ x, T x = a • x)
    {P : Subgroup (MulAut V)} {g : ↥(alternatingGroup (Fin 6))}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥(alternatingGroup (Fin 6)),
      (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧
        x = ((marking (burnsideI23x_a6ι (burnsideI23x_cF F hF) (g * u * g⁻¹)) : ↥L) : MulAut V)) :
    ∃ U₁ U₂ : Subgroup V, IsFlagW L P W0 (2 ^ 1) 1 U₁ ∧ IsFlagW L P W0 (2 ^ 1) 2 U₂ ∧
      U₁ ≤ U₂ ∧ (∀ U, IsFlagW L P W0 (2 ^ 1) 1 U → U = U₁) ∧
      (∀ U, IsFlagW L P W0 (2 ^ 1) 2 U → U = U₂) := by
  have h2 : (2 : ℕ) ^ 1 = Nat.card F := by rw [hF, pow_one]
  rw [h2]
  have hL12 : burnsideI23x_aL1 F ≤ burnsideI23x_aL2 F := fun x hx => ⟨hx.1, hx.2.1⟩
  refine ⟨_, _,
    burnsideI23x_isFlagW_pre_a6 (burnsideI23x_cF F hF) hV hf hcomm hg
      (burnsideI23x_aL1_smul) (fun u hu x => burnsideI23x_P1_stab_aL1 _ u hu x)
      (by rw [burnsideI23x_card_aL1 hF, hF, pow_one]),
    burnsideI23x_isFlagW_pre_a6 (burnsideI23x_cF F hF) hV hf hcomm hg
      (burnsideI23x_aL2_smul) (fun u hu x => burnsideI23x_P1_stab_aL2 _ u hu x)
      (by rw [burnsideI23x_card_aL2 hF, hF]; norm_num),
    fun w hw => ?_, fun U hU => burnsideI23x_flag1_eq_a6 hF hV hf hcomm hg hU,
    fun U hU => burnsideI23x_flag2_eq_a6 hF hV hf hcomm hg hU⟩
  change f w ∈ burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF) g)
    (burnsideI23x_aL1 F) at hw
  change f w ∈ burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF) g)
    (burnsideI23x_aL2 F)
  rw [burnsideI23x_mem_gm2] at hw ⊢
  exact hL12 hw

theorem burnsideI23x_irred_line_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {N : Type} [AddCommGroup N] [Module F N] [Finite N] (ℓ : AddSubgroup N)
    (hℓsmul : ∀ (a : F) (x : N), x ∈ ℓ → a • x ∈ ℓ) (hcard : Nat.card ℓ = Nat.card F)
    (C : AddSubgroup N) (hC : C ≠ ⊥) (hCℓ : C ≤ ℓ) : ℓ ≤ C := by
  obtain ⟨e₀, he₀, hℓ⟩ := burnsideI23x_line_of_card ℓ hℓsmul hcard
  obtain ⟨⟨x₀, hx₀C⟩, hx₀ne⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
  have hx₀ne' : x₀ ≠ 0 := fun h => hx₀ne (Subtype.ext h)
  obtain ⟨t, ht⟩ := (hℓ x₀).1 (hCℓ hx₀C)
  intro x hx
  obtain ⟨s, hs⟩ := (hℓ x).1 hx
  rcases burnsideI23x_h01 hF t with rfl | rfl
  · exact absurd (by rw [ht, zero_smul]) hx₀ne'
  · rcases burnsideI23x_h01 hF s with rfl | rfl
    · rw [hs, zero_smul]; exact C.zero_mem
    · rw [hs, one_smul]
      rw [ht, one_smul] at hx₀C
      exact hx₀C

@[expose] def burnsideI23x_pr : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 3 * Equiv.swap 3 5

theorem burnsideI23x_pr_even : burnsideI23x_pr ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; unfold burnsideI23x_pr; decide

theorem burnsideI23x_pr_stab_L2 : ∀ w : Fin 4 → ZMod 2,
    ((w 2 = 0 ∧ w 3 = 0) ↔ ((burnsideI23x_a6act burnsideI23x_pr w) 2 = 0 ∧
      (burnsideI23x_a6act burnsideI23x_pr w) 3 = 0)) := by
  unfold burnsideI23x_pr
  decide +kernel

theorem burnsideI23x_pr_irred : ∀ x₀ y : Fin 4 → ZMod 2, x₀ ≠ 0 → (x₀ 2 = 0 ∧ x₀ 3 = 0) →
    (y 2 = 0 ∧ y 3 = 0) → (y = 0 ∨ y = x₀ ∨ y = burnsideI23x_a6act burnsideI23x_pr x₀ ∨
      y = x₀ + burnsideI23x_a6act burnsideI23x_pr x₀) := by
  unfold burnsideI23x_pr
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_pr_stab_aL2 {F : Type} [Field F] (c : ZMod 2 ≃+* F) (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨burnsideI23x_pr, burnsideI23x_pr_even⟩) x ∈
        burnsideI23x_aL2 F ↔ x ∈ burnsideI23x_aL2 F := by
  obtain ⟨w, rfl⟩ := B5FinSp.lfun_surjective c x
  rw [burnsideI23x_a6ι_lin, burnsideI23x_mem_aL2_lfun, burnsideI23x_mem_aL2_lfun]
  exact (burnsideI23x_pr_stab_L2 w).symm

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_irred2_two_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2)
    (A : ↥⁅StatedSp 2 F, StatedSp 2 F⁆ →* ((Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM2 F).lin γ x)
    (g : ↥(alternatingGroup (Fin 6)))
    (C : AddSubgroup (Fin 2 ⊕ Fin 2 → F)) (hC : C ≠ ⊥)
    (hCℓ : C ≤ burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF) g)
      (burnsideI23x_aL2 F))
    (hCinv : ∀ γ, (∀ x, A γ x ∈ burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF) g)
        (burnsideI23x_aL2 F) ↔ x ∈ burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF) g)
          (burnsideI23x_aL2 F)) → ∀ x ∈ C, A γ x ∈ C) :
    burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF) g) (burnsideI23x_aL2 F) ≤ C := by
  set c := burnsideI23x_cF F hF with hc
  set γg := burnsideI23x_a6ι c g with hγg
  set ρ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆ :=
    burnsideI23x_a6ι c ⟨burnsideI23x_pr, burnsideI23x_pr_even⟩ with hρ
  have hstab : ∀ x, A (γg * ρ * γg⁻¹) x ∈ burnsideI23x_gm2 γg (burnsideI23x_aL2 F) ↔
      x ∈ burnsideI23x_gm2 γg (burnsideI23x_aL2 F) := fun x => by
    rw [hAlin, burnsideI23x_mem_gm2, burnsideI23x_mem_gm2, burnsideI23x_lin2_conj]
    exact burnsideI23x_pr_stab_aL2 c _
  obtain ⟨⟨x₀, hx₀C⟩, hx₀ne⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hC
  have hx₀ne' : x₀ ≠ 0 := fun h => hx₀ne (Subtype.ext h)
  have hx₀ℓ : (burnsideI23x_LM2 F).lin γg⁻¹ x₀ ∈ burnsideI23x_aL2 F := hCℓ hx₀C
  have h1 := hCinv _ hstab x₀ hx₀C
  rw [hAlin] at h1
  have hz0 : (burnsideI23x_LM2 F).lin γg ((burnsideI23x_LM2 F).lin γg⁻¹ x₀) = x₀ :=
    burnsideI23x_lin2_inv_lin γg x₀
  obtain ⟨z', hz'⟩ := B5FinSp.lfun_surjective c ((burnsideI23x_LM2 F).lin γg⁻¹ x₀)
  have hz'mem := (burnsideI23x_mem_aL2_lfun c z').1 (hz' ▸ hx₀ℓ)
  have hlfun0 : B5FinSp.lfun c (0 : Fin 4 → ZMod 2) = 0 := by
    funext a; simp [B5FinSp.lfun]
  have hz'ne : z' ≠ 0 := by
    rintro rfl
    apply hx₀ne'
    rw [← hz0, ← hz', hlfun0, map_zero]
  have hρz : (burnsideI23x_LM2 F).lin ρ (B5FinSp.lfun c z') = B5FinSp.lfun c (burnsideI23x_a6act
      burnsideI23x_pr z') := burnsideI23x_a6ι_lin c ⟨burnsideI23x_pr, burnsideI23x_pr_even⟩ z'
  have h1' : (burnsideI23x_LM2 F).lin γg (B5FinSp.lfun c (burnsideI23x_a6act burnsideI23x_pr z')) ∈ C := by
    have e : (burnsideI23x_LM2 F).lin (γg * ρ * γg⁻¹) x₀ =
        (burnsideI23x_LM2 F).lin γg ((burnsideI23x_LM2 F).lin ρ (B5FinSp.lfun c z')) :=
      (((congrArg (fun t => (burnsideI23x_LM2 F).lin (γg * ρ * γg⁻¹) t) hz0).symm.trans
        (burnsideI23x_lin2_conj' γg ρ ((burnsideI23x_LM2 F).lin γg⁻¹ x₀))).trans
        (congrArg (fun t => (burnsideI23x_LM2 F).lin γg ((burnsideI23x_LM2 F).lin ρ t)) hz'.symm))
    rw [e, hρz] at h1
    exact h1
  have hx₀' : (burnsideI23x_LM2 F).lin γg (B5FinSp.lfun c z') ∈ C := by
    rw [hz', hz0]; exact hx₀C
  intro x hx
  have hxℓ : (burnsideI23x_LM2 F).lin γg⁻¹ x ∈ burnsideI23x_aL2 F := hx
  obtain ⟨y', hy'⟩ := B5FinSp.lfun_surjective c ((burnsideI23x_LM2 F).lin γg⁻¹ x)
  have hy'mem := (burnsideI23x_mem_aL2_lfun c y').1 (hy' ▸ hxℓ)
  have hxe : x = (burnsideI23x_LM2 F).lin γg (B5FinSp.lfun c y') := by
    rw [hy', burnsideI23x_lin2_inv_lin]
  rw [hxe]
  rcases burnsideI23x_pr_irred z' y' hz'ne hz'mem hy'mem with h | h | h | h
  · rw [h, hlfun0, map_zero]; exact C.zero_mem
  · rw [h]; exact hx₀'
  · rw [h]; exact h1'
  · rw [h, B5FinSp.lfun_add, map_add]
    exact C.add_mem hx₀' h1'

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_UCg_two_one : burnsideI23x_UCg 2 1 := by
  intro F _ _ hF U _ _ hU G L T K hLG hnorm hGT hT hGK huniv marking β hsec U1 U2 h1 h2
  have hF1 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : CharP F 2 := burnsideI23x_charP2_of_card hF1
  haveI : Finite (MulAut U) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hS := burnsideI23x_scalarAgree2 F
  have hEndLin : ∀ φ : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ γ x, φ ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (φ x)) →
      ∃ c : F, ∀ x, φ x = c • x := fun φ hφ => burnsideI23x_hEnd2_one hF1 φ hφ
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM2 F) (burnsideI23x_sd2 F) (burnsideI23x_hsymp2_any F)
    (burnsideI23x_hfaith2 F) (burnsideI23x_genW'2_one F hF1) (burnsideI23x_hbound2_one hF1) hU
    huniv hsec
  have hEnd : ∀ φ : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ γ x, φ (A γ x) = A γ (φ x)) → ∃ c : F, ∀ x, φ x = c • x := fun φ hφ =>
    hEndLin φ (fun γ x => by simpa only [hAlin] using hφ γ x)
  have hf := burnsideI23x_isCoord (burnsideI23x_LM2 F) hsec
  have hmb := burnsideI23x_marking_bij2 hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  obtain ⟨hU2i, hU2F, hU2c⟩ := burnsideI23x_marked_ell hS hsec h2
  have hU1' : ∀ u, u ∈ U1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hU2' : ∀ u, u ∈ U2 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img U2 := fun u => by
    rw [hψfst]; exact hU2i u
  have hcard1 : Nat.card (hf.img U1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ₁⟩ := burnsideI23x_line_of_card (hf.img U1) hU1F hcard1
  have hTG : T ≤ G := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hfl1 : IsFlagW L (T ⊓ L) K (2 ^ 1) 1 U1 :=
    burnsideI23x_marked_imp_flag hS hU hsec (fun T' hT' => hEndLin T' hT') h1
  have hfl2 : IsFlagW L (T ⊓ L) K (2 ^ 1) 2 U2 :=
    burnsideI23x_marked_imp_flag hS hU hsec (fun T' hT' => hEndLin T' hT') h2
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_desc2 hF1 marking hmb hP
  rw [← hF] at hfl1 hfl2
  have hU2pre := burnsideI23x_flag2_eq_a6 hF1 hU hf hEndLin hg hfl2
  have himg2 : hf.img U2 = burnsideI23x_gm2 (burnsideI23x_a6ι (burnsideI23x_cF F hF1) g)
      (burnsideI23x_aL2 F) := (congrArg hf.img hU2pre).trans (hf.img_pre _)
  have hirr1 : ∀ C : AddSubgroup (Fin 2 ⊕ Fin 2 → F), C ≠ ⊥ → C ≤ hf.img U1 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U1 ↔ x ∈ hf.img U1) → ∀ x ∈ C, A γ x ∈ C) → hf.img U1 ≤ C :=
    fun C hC hCℓ _ => burnsideI23x_irred_line_two hF1 (hf.img U1) hU1F hcard1 C hC hCℓ
  have hirr2 : ∀ C : AddSubgroup (Fin 2 ⊕ Fin 2 → F), C ≠ ⊥ → C ≤ hf.img U2 →
      (∀ γ, (∀ x, A γ x ∈ hf.img U2 ↔ x ∈ hf.img U2) → ∀ x ∈ C, A γ x ∈ C) → hf.img U2 ≤ C := by
    intro C hC hCℓ hCinv
    rw [himg2] at hCℓ hCinv ⊢
    exact burnsideI23x_irred2_two_one hF1 A hAlin g C hC hCℓ hCinv
  have he₀ℓ : e₀ ∈ hf.img U1 := (hℓ₁ e₀).2 ⟨1, (one_smul F e₀).symm⟩
  have hcardF2 : Nat.card (hf.img U2) = Nat.card F ^ 2 := by rw [hU2c, hF]
  have he₂ : ∃ e₂ ∈ hf.img U2, e₂ ≠ 0 := by
    have hlt : 1 < Nat.card (hf.img U2) := by
      rw [hcardF2]
      have : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    haveI : Nontrivial (hf.img U2) := Finite.one_lt_card_iff_nontrivial.1 hlt
    obtain ⟨⟨e₂, he₂⟩, hne⟩ := exists_ne (0 : hf.img U2)
    exact ⟨e₂, he₂, fun h => hne (Subtype.ext h)⟩
  obtain ⟨e₂, he₂ℓ, he₂0⟩ := he₂
  refine ⟨?_, ⟨?_, ?_⟩, fun h => absurd h (by norm_num)⟩
  · exact burnsideI23x_SD.exists_T_fixed ψ marking hπs hψact hEnd hgenW hTG hnorm hT2 he₀ hℓ₁
      hU1' (fun t ht u hu => h1.2.1 t ht u hu)
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU1F hU1' he₀ℓ he₀
      hirr1
  · exact burnsideI23x_SD.central_core ψ marking hπs hψact hEnd hgenW hLG hnorm hU2F hU2' he₂ℓ
      he₂0 hirr2

set_option synthInstance.maxSize 4096 in
theorem burnsideI23x_no_transv : ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 →
    ∀ e : Fin 4 → ZMod 2, (∀ v, burnsideI23x_a6act σ v + v = 0 ∨ burnsideI23x_a6act σ v + v = e) →
      ∀ v, burnsideI23x_a6act σ v = v := by
  decide +kernel

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_root_bot_a6 {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 2 F).Gam →* ↥L} {f : V → (Fin 2 ⊕ Fin 2 → F)}
    (hf : IsCoord (burnsideI23x_LM2 F) L W0 marking f) {V1 : Subgroup V} (hWV1 : W0 ≤ V1)
    (hsc : ∀ (a : F) (x : Fin 2 ⊕ Fin 2 → F), x ∈ hf.img V1 → a • x ∈ hf.img V1)
    (hcard : Nat.card (hf.img V1) = Nat.card F) :
    i23TransvectionRoot L W0 V1 = ⊥ := by
  set c := burnsideI23x_cF F hF with hc
  obtain ⟨e₀, he₀, hℓ⟩ := burnsideI23x_line_of_card (hf.img V1) hsc hcard
  obtain ⟨e', he'⟩ := B5FinSp.lfun_surjective c e₀
  have hempty : {root | root ∈ L ∧ (∀ vector : V, root vector * vector⁻¹ ∈ V1) ∧
      (∀ vector ∈ V1, root vector * vector⁻¹ ∈ W0) ∧ ∃ vector : V, root vector * vector⁻¹ ∉ W0} =
      (∅ : Set (MulAut V)) := by
    ext root
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hrL, hV1', hW0', v, hv⟩
    obtain ⟨γ, hγ⟩ := hf.onto ⟨root, hrL⟩
    have hγr : ((marking γ : ↥L) : MulAut V) = root := congrArg Subtype.val hγ
    obtain ⟨σ, hσ⟩ := (burnsideI23x_a6ι_bijective c).2 γ
    have hlin : ∀ w : V, f (root w * w⁻¹) = (burnsideI23x_LM2 F).lin γ (f w) - f w := by
      intro w
      rw [hf.map_mul_inv, ← hγr, hf.act]
    have hmem : ∀ x : Fin 2 ⊕ Fin 2 → F, (burnsideI23x_LM2 F).lin γ x - x ∈ hf.img V1 := by
      intro x
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [← hlin]
      exact ⟨_, hV1' w, rfl⟩
    have hfix : ∀ v' : Fin 4 → ZMod 2, burnsideI23x_a6act (σ : Equiv.Perm (Fin 6)) v' = v' := by
      refine burnsideI23x_no_transv _ (Equiv.Perm.mem_alternatingGroup.1 σ.2) e' ?_
      intro v'
      have h1 := hmem (B5FinSp.lfun c v')
      rw [← hσ, burnsideI23x_a6ι_lin] at h1
      obtain ⟨a, ha⟩ := (hℓ _).1 h1
      have h2 : B5FinSp.lfun c (burnsideI23x_a6act (σ : Equiv.Perm (Fin 6)) v' + v') =
          B5FinSp.lfun c (burnsideI23x_a6act (σ : Equiv.Perm (Fin 6)) v') - B5FinSp.lfun c v' := by
        rw [CharTwo.sub_eq_add]; exact B5FinSp.lfun_add c _ _
      rcases burnsideI23x_h01 hF a with rfl | rfl
      · left
        rw [zero_smul] at ha
        exact B5FinSp.lfun_injective c (by rw [h2, ha]; funext i; simp [B5FinSp.lfun])
      · right
        rw [one_smul] at ha
        exact B5FinSp.lfun_injective c (by rw [h2, ha, ← he'])
    apply hv
    rw [← hf.ker, hlin]
    have : (burnsideI23x_LM2 F).lin γ (f v) = f v := by
      obtain ⟨v', hv'⟩ := B5FinSp.lfun_surjective c (f v)
      rw [← hv', ← hσ, burnsideI23x_a6ι_lin, hfix]
    rw [this, sub_self]
  unfold i23TransvectionRoot
  rw [hempty, Subgroup.closure_empty]

@[expose] def burnsideI23x_pz : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem burnsideI23x_pz_even : burnsideI23x_pz ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]; unfold burnsideI23x_pz; decide

theorem burnsideI23x_pz_mem_P1 : burnsideI23x_pz ∈ burnsideI23x_P1 := by
  show burnsideI23x_pz ∈ burnsideI23x_P1list
  unfold burnsideI23x_P1list burnsideI23x_pz burnsideI23x_pa burnsideI23x_pb
  decide +kernel

theorem burnsideI23x_pz_sq : burnsideI23x_pz * burnsideI23x_pz = 1 := by
  unfold burnsideI23x_pz; decide

theorem burnsideI23x_pz_ne : burnsideI23x_pz ≠ 1 := by
  unfold burnsideI23x_pz; decide

theorem burnsideI23x_pz_central : ∀ u ∈ burnsideI23x_P1list, burnsideI23x_pz * u = u * burnsideI23x_pz := by
  unfold burnsideI23x_P1list burnsideI23x_pz burnsideI23x_pa burnsideI23x_pb
  decide +kernel

theorem burnsideI23x_P1_center : ∀ u ∈ burnsideI23x_P1list,
    (∀ p ∈ burnsideI23x_P1list, u * p = p * u) → u * u = 1 → u = 1 ∨ u = burnsideI23x_pz := by
  unfold burnsideI23x_P1list burnsideI23x_pz burnsideI23x_pa burnsideI23x_pb
  decide +kernel

open CFSG.ASVolI.ChIJK in
theorem burnsideI23x_center_P_a6 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (ρ : ↥(alternatingGroup (Fin 6)) →* ↥L) (hρ : Function.Bijective ρ)
    {P : Subgroup (MulAut V)}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥(alternatingGroup (Fin 6)),
      (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧ x = ((ρ u : ↥L) : MulAut V))
    (x : MulAut V) :
    (x ∈ CFSG.ASVolI.ChIJK.centerOf P ∧ x ^ 2 = 1) ↔
      (x = 1 ∨ x = ((ρ ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩ : ↥L) : MulAut V)) := by
  have hmul : ∀ u u' : ↥(alternatingGroup (Fin 6)),
      ((ρ (u * u') : ↥L) : MulAut V) = ((ρ u : ↥L) : MulAut V) * ((ρ u' : ↥L) : MulAut V) :=
    fun u u' => by rw [map_mul]; rfl
  have hinj : ∀ u u' : ↥(alternatingGroup (Fin 6)),
      ((ρ u : ↥L) : MulAut V) = ((ρ u' : ↥L) : MulAut V) → u = u' :=
    fun u u' h => hρ.1 (Subtype.ext h)
  have hone : ((ρ 1 : ↥L) : MulAut V) = 1 := by rw [map_one]; rfl
  set zz : ↥(alternatingGroup (Fin 6)) := ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩ with hzz
  set z0 : MulAut V := ((ρ zz : ↥L) : MulAut V) with hz0
  have hz0P : z0 ∈ P := (hg _).2 ⟨zz, burnsideI23x_pz_mem_P1, rfl⟩
  have hz0sq : z0 ^ 2 = 1 := by
    rw [pow_two, hz0, ← hmul]
    have : zz * zz = 1 := Subtype.ext burnsideI23x_pz_sq
    rw [this, hone]
  constructor
  · rintro ⟨hx, hx2⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    have hzP : (z : MulAut V) ∈ P := z.2
    obtain ⟨u, hu, hzu⟩ := (hg _).1 hzP
    have hcent : ∀ p ∈ burnsideI23x_P1list, (u : Equiv.Perm (Fin 6)) * p = p * u := by
      intro p hp
      have hpA : p ∈ alternatingGroup (Fin 6) := burnsideI23x_P1list_even p hp
      have hy : ((ρ ⟨p, hpA⟩ : ↥L) : MulAut V) ∈ P := (hg _).2 ⟨⟨p, hpA⟩, hp, rfl⟩
      have h1 := Subgroup.mem_center_iff.1 hz ⟨_, hy⟩
      have h2 : ((ρ ⟨p, hpA⟩ : ↥L) : MulAut V) * (z : MulAut V) =
          (z : MulAut V) * ((ρ ⟨p, hpA⟩ : ↥L) : MulAut V) := congrArg Subtype.val h1
      rw [hzu, ← hmul, ← hmul] at h2
      have h3 := hinj _ _ h2
      have h4 := congrArg Subtype.val h3
      exact h4.symm
    have hu2 : (u : Equiv.Perm (Fin 6)) * u = 1 := by
      have h5 : (z : MulAut V) ^ 2 = 1 := hx2
      rw [pow_two, hzu, ← hmul] at h5
      have h6 : ((ρ (u * u) : ↥L) : MulAut V) = ((ρ 1 : ↥L) : MulAut V) := by rw [hone]; exact h5
      have h7 := hinj _ _ h6
      exact congrArg Subtype.val h7
    rcases burnsideI23x_P1_center _ hu hcent hu2 with h | h
    · left
      have : u = 1 := Subtype.ext h
      show (z : MulAut V) = 1
      rw [hzu, this, hone]
    · right
      have : u = zz := Subtype.ext h
      show (z : MulAut V) = _
      rw [hzu, this]
  · rintro (rfl | rfl)
    · exact ⟨Subgroup.one_mem _, one_pow 2⟩
    · refine ⟨?_, hz0sq⟩
      refine Subgroup.mem_map.2 ⟨⟨_, hz0P⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨u, hu, hyu⟩ := (hg y.1).1 y.2
      apply Subtype.ext
      show (y : MulAut V) * z0 = z0 * (y : MulAut V)
      rw [hyu, hz0, ← hmul, ← hmul]
      have : (u : Equiv.Perm (Fin 6)) * burnsideI23x_pz = burnsideI23x_pz * u :=
        (burnsideI23x_pz_central u hu).symm
      rw [show u * zz = zz * u from Subtype.ext this]

open CFSG.ASVolI.ChIJK in
theorem burnsideI23x_omega_center_a6 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (ρ : ↥(alternatingGroup (Fin 6)) →* ↥L) (hρ : Function.Bijective ρ)
    {P : Subgroup (MulAut V)}
    (hg : ∀ x : MulAut V, x ∈ P ↔ ∃ u : ↥(alternatingGroup (Fin 6)),
      (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧ x = ((ρ u : ↥L) : MulAut V))
    (x : MulAut V) :
    x ∈ CFSG.ASVolI.ChIJK.omegaOne (CFSG.ASVolI.ChIJK.centerOf P) ↔
      (x = 1 ∨ x = ((ρ ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩ : ↥L) : MulAut V)) := by
  set z0 : MulAut V := ((ρ ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩ : ↥L) : MulAut V) with hz0
  have hz0sq : z0 ^ 2 = 1 := ((burnsideI23x_center_P_a6 ρ hρ hg z0).2 (Or.inr rfl)).2
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      exact (burnsideI23x_center_P_a6 ρ hρ hg y).1 ⟨hy.1, hy.2⟩
    | one => exact Or.inl rfl
    | mul y y' _ _ hy hy' =>
      rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
      · left; exact mul_one _
      · right; exact one_mul _
      · right; exact mul_one _
      · left; rw [← pow_two]; exact hz0sq
    | inv y _ hy =>
      rcases hy with rfl | rfl
      · left; exact inv_one
      · right
        have : z0 * z0 = 1 := by rw [← pow_two]; exact hz0sq
        exact inv_eq_of_mul_eq_one_right this
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ((burnsideI23x_center_P_a6 ρ hρ hg z0).2 (Or.inr rfl))

theorem burnsideI23x_pz_M1 : ∀ w : Fin 4 → ZMod 2, w 2 = 0 → w 3 = 0 →
    burnsideI23x_a6act burnsideI23x_pz w = w := by
  unfold burnsideI23x_pz; decide +kernel

theorem burnsideI23x_pz_M2 : ∀ v : Fin 4 → ZMod 2,
    (burnsideI23x_a6act burnsideI23x_pz v + v) 2 = 0 ∧
      (burnsideI23x_a6act burnsideI23x_pz v + v) 3 = 0 := by
  unfold burnsideI23x_pz; decide +kernel

theorem burnsideI23x_pz_M3 : ∀ v : Fin 4 → ZMod 2,
    burnsideI23x_q4 v + burnsideI23x_q4 (burnsideI23x_a6act burnsideI23x_pz v) =
      (burnsideI23x_a6act burnsideI23x_pz v + v) 0 + (burnsideI23x_a6act burnsideI23x_pz v + v) 1 := by
  unfold burnsideI23x_pz burnsideI23x_q4; decide +kernel

theorem burnsideI23x_pz_M4 : ∀ y : Fin 4 → ZMod 2, y 2 = 0 → y 3 = 0 →
    ∃ v : Fin 4 → ZMod 2, burnsideI23x_a6act burnsideI23x_pz v + v = y := by
  unfold burnsideI23x_pz; decide +kernel

open CFSG.Quasithin in
theorem burnsideI23x_zpow_invol {V : Type} [CommGroup V] (z0 : MulAut V) (hz : z0 * z0 = 1) :
    ∀ k : ℤ, z0 ^ k = 1 ∨ z0 ^ k = z0 := by
  have hinv : z0⁻¹ = z0 := inv_eq_of_mul_eq_one_right hz
  intro k
  induction k using Int.induction_on with
  | zero => left; simp
  | succ k ih =>
    rcases ih with h | h
    · right; rw [zpow_add_one, h, one_mul]
    · left; rw [zpow_add_one, h, hz]
  | pred k ih =>
    rcases ih with h | h
    · right; rw [zpow_sub_one, h, one_mul, hinv]
    · left; rw [zpow_sub_one, h, hinv, hz]

open CFSG.Quasithin in
theorem burnsideI23x_mem_commV_zpowers {V : Type} [CommGroup V] (z0 : MulAut V)
    (hz : z0 * z0 = 1) (u : V) :
    u ∈ commV (Subgroup.zpowers z0) ↔ ∃ v : V, z0 v * v⁻¹ = u := by
  constructor
  · intro hu
    induction hu using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, v, rfl⟩ := hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rcases burnsideI23x_zpow_invol z0 hz k with h | h
      · exact ⟨1, by rw [h, MulAut.one_apply, mul_inv_cancel, map_one, inv_one, mul_one]⟩
      · exact ⟨v, by rw [h]⟩
    | one => exact ⟨1, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨v, hv⟩ := hx
      obtain ⟨v', hv'⟩ := hy
      refine ⟨v * v', ?_⟩
      rw [map_mul, mul_inv_rev, ← hv, ← hv']
      simp only [mul_comm, mul_left_comm, mul_assoc]
    | inv x _ hx =>
      obtain ⟨v, hv⟩ := hx
      refine ⟨v⁻¹, ?_⟩
      rw [map_inv, inv_inv, ← hv, mul_inv_rev, inv_inv, mul_comm]
  · rintro ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨z0, Subgroup.mem_zpowers z0, v, rfl⟩

@[expose] def burnsideI23x_Dsub (F : Type) [Field F] : Submodule F ((Fin 2 ⊕ Fin 2 → F) × F) where
  carrier := {w | w.1 ∈ burnsideI23x_aL2 F ∧ w.2 = w.1 (.inl 0) + w.1 (.inl 1)}
  add_mem' := fun {w w'} hw hw' => ⟨(burnsideI23x_aL2 F).add_mem hw.1 hw'.1, by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, hw.2, hw'.2]; ring⟩
  zero_mem' := ⟨(burnsideI23x_aL2 F).zero_mem, by simp⟩
  smul_mem' := fun c w hw => ⟨burnsideI23x_aL2_smul c _ hw.1, by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hw.2]; ring⟩

@[expose] def burnsideI23x_D1sub (F : Type) [Field F] : Submodule F ((Fin 2 ⊕ Fin 2 → F) × F) where
  carrier := {w | w.1 ∈ burnsideI23x_aL1 F ∧ w.2 = 0}
  add_mem' := fun {w w'} hw hw' => ⟨(burnsideI23x_aL1 F).add_mem hw.1 hw'.1, by
    simp only [Prod.snd_add, hw.2, hw'.2, add_zero]⟩
  zero_mem' := ⟨(burnsideI23x_aL1 F).zero_mem, rfl⟩
  smul_mem' := fun c w hw => ⟨burnsideI23x_aL1_smul c _ hw.1, by
    simp only [Prod.smul_snd, hw.2, smul_zero]⟩

theorem burnsideI23x_card_Dsub {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (burnsideI23x_Dsub F) = Nat.card F ^ 2 := by
  have h : Nat.card (burnsideI23x_Dsub F) = Nat.card (burnsideI23x_aL2 F) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1.1, w.2.1⟩
        invFun := fun x => ⟨(x.1, x.1 (.inl 0) + x.1 (.inl 1)), x.2, rfl⟩
        left_inv := fun w => Subtype.ext (Prod.ext rfl w.2.2.symm)
        right_inv := fun x => rfl }
  rw [h, burnsideI23x_card_aL2 hF, hF]
  norm_num

theorem burnsideI23x_card_D1sub {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (burnsideI23x_D1sub F) = Nat.card F ^ 1 := by
  have h : Nat.card (burnsideI23x_D1sub F) = Nat.card (burnsideI23x_aL1 F) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1.1, w.2.1⟩
        invFun := fun x => ⟨(x.1, 0), x.2, rfl⟩
        left_inv := fun w => Subtype.ext (Prod.ext rfl w.2.2.symm)
        right_inv := fun x => rfl }
  rw [h, burnsideI23x_card_aL1 hF, hF]
  norm_num

theorem burnsideI23x_finrank_of_card {F : Type} [Field F] [Finite F] {M : Type} [AddCommGroup M]
    [Module F M] [Finite M] (S : Submodule F M) (k : ℕ) (hcard : Nat.card S = Nat.card F ^ k) :
    Module.finrank F S = k := by
  haveI : Module.Finite F M := Module.Finite.of_finite
  have hc2 := Module.natCard_eq_pow_finrank (K := F) (V := ↥S)
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  exact (Nat.pow_right_injective hq (hc2.symm.trans hcard))

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_smallSymp_std {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {V : Type} [CommGroup V] [Finite V] {L T : Subgroup (MulAut V)}
    {V1 V2 : Subgroup V} (Ψ : V ≃* Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F))
    (z0 : MulAut V) (hz0sq : z0 * z0 = 1) (hz0ne : z0 ≠ 1)
    (M : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) (hM : (burnsideI23x_sd2 F).Symp M)
    (hΨz0 : ∀ u, Multiplicative.toAdd (Ψ (z0 u)) =
      (burnsideI23x_sd2 F).lift hM (Multiplicative.toAdd (Ψ u)))
    (hM1 : ∀ x ∈ burnsideI23x_aL2 F, M x = x)
    (hM2 : ∀ x, M x - x ∈ burnsideI23x_aL2 F)
    (hM3 : ∀ x, burnsideI23x_sqrt F ((burnsideI23x_sd2 F).Q0 x + (burnsideI23x_sd2 F).Q0 (M x)) =
      (M x - x) (.inl 0) + (M x - x) (.inl 1))
    (hM4 : ∀ y ∈ burnsideI23x_aL2 F, ∃ x, M x - x = y)
    (hfix : ∀ u, u ∈ fixV L ↔ (Multiplicative.toAdd (Ψ u)).1 = 0)
    (hV1 : ∀ u, u ∈ V1 ↔ (Multiplicative.toAdd (Ψ u)).1 ∈ burnsideI23x_aL1 F)
    (hV2 : ∀ u, u ∈ V2 ↔ (Multiplicative.toAdd (Ψ u)).1 ∈ burnsideI23x_aL2 F)
    (hΩ : ∀ x, x ∈ CFSG.ASVolI.ChIJK.omegaOne (CFSG.ASVolI.ChIJK.centerOf (T ⊓ L)) ↔
      (x = 1 ∨ x = z0)) :
    I23SmallSymplecticConcl (StatedQuadOdd 2 F)
      (burnsideI23x_SD.psiTrans Ψ (burnsideI23x_kappa2 F)) L T V1 V2 := by
  classical
  set S := burnsideI23x_sd2 F with hS
  set κ := burnsideI23x_kappa2 F with hκdef
  have hκ : ∀ w, StatedQuadOdd 2 F (κ w) = S.Qw w := burnsideI23x_kappa2_Q F
  have hlsub : ∀ w : (Fin 2 ⊕ Fin 2 → F) × F,
      S.lift hM w - w = (M w.1 - w.1, (M w.1 - w.1) (.inl 0) + (M w.1 - w.1) (.inl 1)) := by
    intro w
    refine Prod.ext ?_ ?_
    · show M w.1 - w.1 = _
      rfl
    · show w.2 + S.lf M w.1 - w.2 = _
      rw [show S.lf M w.1 = (M w.1 - w.1) (.inl 0) + (M w.1 - w.1) (.inl 1) from hM3 w.1]
      ring
  have hD : ∀ u, u ∈ commV (Subgroup.zpowers z0) ↔
      ((Multiplicative.toAdd (Ψ u)).1 ∈ burnsideI23x_aL2 F ∧
        (Multiplicative.toAdd (Ψ u)).2 = (Multiplicative.toAdd (Ψ u)).1 (.inl 0) +
          (Multiplicative.toAdd (Ψ u)).1 (.inl 1)) := by
    intro u
    rw [burnsideI23x_mem_commV_zpowers z0 hz0sq]
    constructor
    · rintro ⟨v, rfl⟩
      have h1 : Multiplicative.toAdd (Ψ (z0 v * v⁻¹)) =
          S.lift hM (Multiplicative.toAdd (Ψ v)) - Multiplicative.toAdd (Ψ v) := by
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hΨz0, ← sub_eq_add_neg]
      rw [h1, hlsub]
      exact ⟨hM2 _, rfl⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx⟩ := hM4 _ h1
      refine ⟨Ψ.symm (Multiplicative.ofAdd (x, 0)), ?_⟩
      apply Ψ.injective
      apply Multiplicative.toAdd.injective
      have h3 : Multiplicative.toAdd (Ψ (z0 (Ψ.symm (Multiplicative.ofAdd (x, 0))) *
          (Ψ.symm (Multiplicative.ofAdd (x, 0)))⁻¹)) =
          S.lift hM (x, 0) - (x, 0) := by
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hΨz0, MulEquiv.apply_symm_apply,
          toAdd_ofAdd, ← sub_eq_add_neg]
      rw [h3, hlsub]
      refine Prod.ext ?_ ?_
      · exact hx
      · show (M x - x) (.inl 0) + (M x - x) (.inl 1) = _
        rw [hx, h2]
  have hz0fix : ∀ u, (Multiplicative.toAdd (Ψ u)).1 ∈ burnsideI23x_aL2 F → z0 u = u := by
    intro u hu
    apply Ψ.injective
    apply Multiplicative.toAdd.injective
    rw [hΨz0]
    refine Prod.ext ?_ ?_
    · exact hM1 _ hu
    · show (Multiplicative.toAdd (Ψ u)).2 + S.lf M (Multiplicative.toAdd (Ψ u)).1 =
        (Multiplicative.toAdd (Ψ u)).2
      have h0 : S.lf M (Multiplicative.toAdd (Ψ u)).1 = 0 := by
        unfold burnsideI23x_SD.lf
        rw [hM1 _ hu, burnsideI23x_SD.add_self_F, map_zero]
      rw [h0, add_zero]
  refine ⟨?_, fun z hz hz1 => ?_⟩
  · rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨z0, (hΩ z0).2 (Or.inr rfl)⟩, ?_, ?_⟩
    · intro h
      exact hz0ne (congrArg Subtype.val h).symm
    · ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases (hΩ w.1).1 w.2 with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  · have hzz : z = z0 := ((hΩ z).1 hz).resolve_left hz1
    subst hzz
    intro D
    have hΨsymm : ∀ p : (Fin 2 ⊕ Fin 2 → F) × F,
        Multiplicative.toAdd (Ψ (Ψ.symm (Multiplicative.ofAdd p))) = p := fun p => by
      rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hDfix : D ≤ fixV (Subgroup.zpowers z) := by
      intro u hu
      rw [mem_fixV]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      have hu0 : z u = u := hz0fix u ((hD u).1 hu).1
      rcases burnsideI23x_zpow_invol z hz0sq k with h | h
      · rw [h, MulAut.one_apply]
      · rw [h]; exact hu0
    have hsum_D : ∀ u, (Multiplicative.toAdd (Ψ u)).1 ∈ burnsideI23x_aL2 F →
        Ψ.symm (Multiplicative.ofAdd ((Multiplicative.toAdd (Ψ u)).1,
          (Multiplicative.toAdd (Ψ u)).1 (.inl 0) + (Multiplicative.toAdd (Ψ u)).1 (.inl 1))) ∈ D := by
      intro u hu
      rw [hD, hΨsymm]
      exact ⟨hu, rfl⟩
    have hrad : ∀ u u₁ : V, (Multiplicative.toAdd (Ψ u₁)).1 = (Multiplicative.toAdd (Ψ u)).1 →
        u₁⁻¹ * u ∈ fixV L := by
      intro u u₁ h
      rw [hfix, map_mul, map_inv, toAdd_mul, toAdd_inv, Prod.fst_add, Prod.fst_neg, h]
      simp
    have hDsup2 : D ⊔ fixV L = V2 := by
      apply le_antisymm
      · refine sup_le (fun u hu => ?_) (fun u hu => ?_)
        · exact (hV2 u).2 ((hD u).1 hu).1
        · exact (hV2 u).2 (by rw [(hfix u).1 hu]; exact (burnsideI23x_aL2 F).zero_mem)
      · intro u hu
        have hx := (hV2 u).1 hu
        have hu₁D := hsum_D u hx
        set u₁ : V := Ψ.symm (Multiplicative.ofAdd ((Multiplicative.toAdd (Ψ u)).1,
          (Multiplicative.toAdd (Ψ u)).1 (.inl 0) + (Multiplicative.toAdd (Ψ u)).1 (.inl 1)))
          with hu₁
        have hu₂ : u₁⁻¹ * u ∈ fixV L := hrad u u₁ (by rw [hu₁, hΨsymm])
        have : u = u₁ * (u₁⁻¹ * u) := by group
        rw [this]
        exact Subgroup.mul_mem_sup hu₁D hu₂
    have hD1 : ∀ u, u ∈ D ⊓ V1 ↔ ((Multiplicative.toAdd (Ψ u)).1 ∈ burnsideI23x_aL1 F ∧
        (Multiplicative.toAdd (Ψ u)).2 = 0) := by
      intro u
      constructor
      · rintro ⟨hu1, hu2⟩
        obtain ⟨h1, h2⟩ := (hD u).1 hu1
        have h3 := (hV1 u).1 hu2
        refine ⟨h3, ?_⟩
        rw [h2, h3.2.2]
        exact CharTwo.add_self_eq_zero _
      · rintro ⟨h1, h2⟩
        refine ⟨(hD u).2 ⟨⟨h1.1, h1.2.1⟩, ?_⟩, (hV1 u).2 h1⟩
        rw [h2, h1.2.2]
        exact (CharTwo.add_self_eq_zero _).symm
    refine ⟨?_, hDfix, ?_, hDsup2, ?_, ?_, ?_, ?_, ?_⟩
    · refine (burnsideI23x_SD.isFSubspaceVia_transport Ψ κ D 2).1
        ⟨burnsideI23x_Dsub F, burnsideI23x_finrank_of_card _ 2 (burnsideI23x_card_Dsub hF),
          fun v => ?_⟩
      rw [hD v]
      exact Iff.rfl
    · rw [eq_bot_iff]
      rintro u ⟨hu1, hu2⟩
      obtain ⟨h1, h2⟩ := (hD u).1 hu1
      have h0 := (hfix u).1 hu2
      rw [Subgroup.mem_bot]
      apply Ψ.injective
      apply Multiplicative.toAdd.injective
      rw [map_one, toAdd_one]
      refine Prod.ext h0 ?_
      show (Multiplicative.toAdd (Ψ u)).2 = 0
      rw [h2, h0]
      simp
    · intro x hx y hy
      rw [burnsideI23x_SD.toAdd_psiTrans, burnsideI23x_SD.toAdd_psiTrans,
        burnsideI23x_SD.polarOf_transport S.Qw (StatedQuadOdd 2 F) κ hκ,
        burnsideI23x_SD.polar_Qw]
      obtain ⟨hx1, -⟩ := (hD x).1 hx
      obtain ⟨hy1, -⟩ := (hD y).1 hy
      show bil (Multiplicative.toAdd (Ψ x)).1 (Multiplicative.toAdd (Ψ y)).1 = 0
      simp only [bil, hx1.1, hx1.2, hy1.1, hy1.2]
      ring
    · set e : Fin 2 ⊕ Fin 2 → F := Pi.single (.inl 0) 1 with he
      have he2 : e ∈ burnsideI23x_aL2 F := ⟨by simp [he], by simp [he]⟩
      refine ⟨Ψ.symm (Multiplicative.ofAdd (e, 1)), ?_, ?_⟩
      · rw [hD, hΨsymm]
        refine ⟨he2, ?_⟩
        simp [he]
      · rw [burnsideI23x_SD.toAdd_psiTrans, hΨsymm, hκ]
        show sp4Quad F e + (1 : F) ^ 2 ≠ 0
        simp [sp4Quad, he]
    · refine (burnsideI23x_SD.isFSubspaceVia_transport Ψ κ (D ⊓ V1) 1).1
        ⟨burnsideI23x_D1sub F, burnsideI23x_finrank_of_card _ 1 (burnsideI23x_card_D1sub hF),
          fun v => ?_⟩
      rw [hD1 v]
      exact Iff.rfl
    · intro x hx
      obtain ⟨h1, h2⟩ := (hD1 x).1 hx
      rw [burnsideI23x_SD.toAdd_psiTrans, hκ]
      show sp4Quad F (Multiplicative.toAdd (Ψ x)).1 + (Multiplicative.toAdd (Ψ x)).2 ^ 2 = 0
      simp [sp4Quad, h1.1, h1.2.1, h2]
    · apply le_antisymm
      · intro u hu
        have hx := (hV1 u).1 hu
        have hsq : (Multiplicative.toAdd (Ψ u)).1 (.inl 0) + (Multiplicative.toAdd (Ψ u)).1 (.inl 1) = 0 := by
          rw [hx.2.2]; exact CharTwo.add_self_eq_zero _
        set u₁ : V := Ψ.symm (Multiplicative.ofAdd ((Multiplicative.toAdd (Ψ u)).1, 0)) with hu₁
        have hu₁m : u₁ ∈ D ⊓ V1 := by
          rw [hD1, hu₁, hΨsymm]
          exact ⟨hx, rfl⟩
        have hu₂ : u₁⁻¹ * u ∈ fixV L := hrad u u₁ (by rw [hu₁, hΨsymm])
        have : u = u₁ * (u₁⁻¹ * u) := by group
        rw [this]
        exact Subgroup.mul_mem_sup hu₁m hu₂
      · refine sup_le inf_le_right (fun u hu => ?_)
        exact (hV1 u).2 (by rw [(hfix u).1 hu]; exact (burnsideI23x_aL1 F).zero_mem)

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in
theorem burnsideI23x_Mz_sub {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (v : Fin 4 → ZMod 2) :
    (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩)
        (B5FinSp.lfun c v) - B5FinSp.lfun c v =
      B5FinSp.lfun c (burnsideI23x_a6act burnsideI23x_pz v + v) := by
  rw [burnsideI23x_a6ι_lin, CharTwo.sub_eq_add, B5FinSp.lfun_add]

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in
theorem burnsideI23x_Mz_M1 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (x : Fin 2 ⊕ Fin 2 → F) (hx : x ∈ burnsideI23x_aL2 F) :
    (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩) x = x := by
  obtain ⟨v, rfl⟩ := B5FinSp.lfun_surjective c x
  rw [burnsideI23x_a6ι_lin]
  have h := (burnsideI23x_mem_aL2_lfun c v).1 hx
  rw [burnsideI23x_pz_M1 v h.1 h.2]

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in
theorem burnsideI23x_Mz_M2 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (x : Fin 2 ⊕ Fin 2 → F) :
    (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩) x - x ∈
      burnsideI23x_aL2 F := by
  obtain ⟨v, rfl⟩ := B5FinSp.lfun_surjective c x
  rw [burnsideI23x_Mz_sub, burnsideI23x_mem_aL2_lfun]
  exact burnsideI23x_pz_M2 v

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in
theorem burnsideI23x_Mz_M3 {F : Type} [Field F] [Finite F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (x : Fin 2 ⊕ Fin 2 → F) :
    burnsideI23x_sqrt F ((burnsideI23x_sd2 F).Q0 x + (burnsideI23x_sd2 F).Q0
        ((burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩) x)) =
      ((burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩) x - x)
          (.inl 0) +
        ((burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩) x - x)
          (.inl 1) := by
  obtain ⟨v, rfl⟩ := B5FinSp.lfun_surjective c x
  rw [burnsideI23x_Mz_sub, burnsideI23x_a6ι_lin, burnsideI23x_sd2_Q0, burnsideI23x_sd2_Q0,
    burnsideI23x_sp4Quad_lfun, burnsideI23x_sp4Quad_lfun, ← map_add, burnsideI23x_sqrt_zmod2,
    burnsideI23x_pz_M3 v]
  simp only [B5FinSp.lfun, map_add]
  rfl

open CFSG.Quasithin CFSG.Quasithin.B5FinSp CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.MS93 in
theorem burnsideI23x_Mz_M4 {F : Type} [Field F] [CharP F 2] (c : ZMod 2 ≃+* F)
    (y : Fin 2 ⊕ Fin 2 → F) (hy : y ∈ burnsideI23x_aL2 F) :
    ∃ x, (burnsideI23x_LM2 F).lin (burnsideI23x_a6ι c ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩) x -
      x = y := by
  obtain ⟨y', rfl⟩ := B5FinSp.lfun_surjective c y
  have h := (burnsideI23x_mem_aL2_lfun c y').1 hy
  obtain ⟨v, hv⟩ := burnsideI23x_pz_M4 y' h.1 h.2
  exact ⟨B5FinSp.lfun c v, by rw [burnsideI23x_Mz_sub, hv]⟩

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
@[expose] noncomputable def burnsideI23x_Af (F : Type) [Field F] :
    ↥(StatedSp 2 F) →* ((Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) :=
  (burnsideI23x_glEquiv (Fin 2 ⊕ Fin 2) F).toMonoidHom.comp (StatedSp 2 F).subtype

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_Af_apply {F : Type} [Field F] (g : ↥(StatedSp 2 F)) (x : Fin 2 ⊕ Fin 2 → F) :
    burnsideI23x_Af F g x = (((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) *ᵥ x :=
  rfl

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_hAf {F : Type} [Field F] [CharP F 2] (g : ↥(StatedSp 2 F)) :
    (burnsideI23x_sd2 F).Symp (burnsideI23x_Af F g) := fun x y => by
  show bil (burnsideI23x_Af F g x) (burnsideI23x_Af F g y) = bil x y
  exact bil_statedSp g x y

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_hsurjAf (F : Type) [Field F] [CharP F 2]
    (M : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) (hM : (burnsideI23x_sd2 F).Symp M) :
    ∃ γ : ↥(StatedSp 2 F), ∀ x, burnsideI23x_Af F γ x = M x := by
  set Mat := LinearMap.toMatrix' (M : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F)) with hMat
  have hMx : ∀ x, M x = Mat *ᵥ x := fun x => by
    have := congrArg (fun f => f x)
      (Matrix.toLin'_toMatrix' (M : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F)))
    exact this.symm.trans (Matrix.toLin'_apply _ _)
  have hgram : Matᵀ * CFSG.Quasithin.Explicit.spJ F * Mat = CFSG.Quasithin.Explicit.spJ F := by
    apply burnsideI23x_gram_of_bil
    intro x y
    have := hM x y
    rw [hMx, hMx] at this
    exact this
  have hmem : (spUnit Mat hgram : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := by
    rw [statedSp_eq_sp4']
    exact hgram
  refine ⟨⟨spUnit Mat hgram, hmem⟩, fun x => ?_⟩
  rw [hMx]
  rfl

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit in
open scoped Matrix in
theorem burnsideI23x_phiHom_range_full (F : Type) [Field F] [Finite F] [CharP F 2] :
    (burnsideI23x_SD.phiHom (S := burnsideI23x_sd2 F) (A := burnsideI23x_Af F)
      (hA := burnsideI23x_hAf) (burnsideI23x_kappa2 F)).range =
      CFSG.MatrixModel.isometryCore (StatedQuadOdd 2 F) := by
  set κ := burnsideI23x_kappa2 F with hκdef
  set S := burnsideI23x_sd2 F with hS
  have hκ : ∀ w, StatedQuadOdd 2 F (κ w) = S.Qw w := burnsideI23x_kappa2_Q F
  apply le_antisymm
  · rintro _ ⟨γ, rfl⟩
    rw [burnsideI23x_mem_isometryCore]
    intro v
    obtain ⟨w, rfl⟩ := κ.surjective v
    rw [burnsideI23x_SD.phiHom_mulVec, hκ, hκ, S.Qw_lift]
  · intro Am hAm
    have hiso := (burnsideI23x_mem_isometryCore (StatedQuadOdd 2 F) Am).1 hAm
    let g : ((Fin 2 ⊕ Fin 2 → F) × F) ≃ₗ[F] ((Fin 2 ⊕ Fin 2 → F) × F) :=
      (κ.trans (burnsideI23x_glEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) F Am)).trans κ.symm
    have hg : ∀ w, S.Qw (g w) = S.Qw w := by
      intro w
      show S.Qw (κ.symm ((Am : Matrix _ _ F) *ᵥ κ w)) = S.Qw w
      rw [← hκ, LinearEquiv.apply_symm_apply, hiso, hκ]
    obtain ⟨M, hM, hgM⟩ := S.exists_lift_of_isometry hg
    obtain ⟨γ, hγ⟩ := burnsideI23x_hsurjAf F M hM
    refine ⟨γ, ?_⟩
    apply (burnsideI23x_glEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) F).injective
    apply LinearEquiv.ext
    intro v
    obtain ⟨w, rfl⟩ := κ.surjective v
    rw [burnsideI23x_glEquiv_apply, burnsideI23x_glEquiv_apply, burnsideI23x_SD.phiHom_mulVec]
    have h1 : (Am : Matrix _ _ F) *ᵥ κ w = κ (g w) := by
      show _ = κ (κ.symm ((Am : Matrix _ _ F) *ᵥ κ w))
      rw [LinearEquiv.apply_symm_apply]
    rw [h1, hgM]
    congr 1
    refine Prod.ext ?_ ?_
    · exact (hγ w.1)
    · show w.2 + S.lf (burnsideI23x_Af F γ) w.1 = w.2 + S.lf M w.1
      unfold burnsideI23x_SD.lf
      rw [hγ]

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93 CFSG.ASVolI.ChIJK
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat in
open scoped Matrix in
theorem burnsideI23x_phiHom_range_a6 (F : Type) [Field F] [Finite F] [CharP F 2]
    (A : ↥⁅StatedSp 2 F, StatedSp 2 F⁆ →* ((Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)))
    (hA : ∀ γ, (burnsideI23x_sd2 F).Symp (A γ))
    (hAlin : ∀ γ x, A γ x = (burnsideI23x_LM2 F).lin γ x) :
    (burnsideI23x_SD.phiHom (S := burnsideI23x_sd2 F) (A := A) (hA := hA)
      (burnsideI23x_kappa2 F)).range =
      ⁅CFSG.MatrixModel.isometryCore (StatedQuadOdd 2 F),
        CFSG.MatrixModel.isometryCore (StatedQuadOdd 2 F)⁆ := by
  set κ := burnsideI23x_kappa2 F with hκdef
  set S := burnsideI23x_sd2 F with hS
  set Φf := burnsideI23x_SD.phiHom (S := S) (A := burnsideI23x_Af F) (hA := burnsideI23x_hAf) κ
    with hΦf
  have hle : ⁅StatedSp 2 F, StatedSp 2 F⁆ ≤ StatedSp 2 F := burnsideI23x_comm_le_sp F
  let incl : ↥⁅StatedSp 2 F, StatedSp 2 F⁆ →* ↥(StatedSp 2 F) := Subgroup.inclusion hle
  have hAeq : ∀ γ, A γ = burnsideI23x_Af F (incl γ) := fun γ => by
    apply LinearEquiv.ext
    intro x
    rw [hAlin]
    show _ = (((γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ x
    exact linModelNat_lin _ _ _
  have hΦ : burnsideI23x_SD.phiHom (S := S) (A := A) (hA := hA) κ = Φf.comp incl := by
    apply MonoidHom.ext
    intro γ
    show (burnsideI23x_glEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) F).symm
        (κ.symm.trans ((S.lift (hA γ)).trans κ)) =
      (burnsideI23x_glEquiv (Fin 2 ⊕ Fin 2 ⊕ Unit) F).symm
        (κ.symm.trans ((S.lift (burnsideI23x_hAf (incl γ))).trans κ))
    have key : ∀ (M M' : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F)) (h : M = M')
        (hM : S.Symp M) (hM' : S.Symp M'), S.lift hM = S.lift hM' := by
      intro M M' h hM hM'
      subst h
      rfl
    rw [key _ _ (hAeq γ) (hA γ) (burnsideI23x_hAf (incl γ))]
  have hfull := burnsideI23x_phiHom_range_full F
  have hcomm : ⁅(⊤ : Subgroup ↥(StatedSp 2 F)), (⊤ : Subgroup ↥(StatedSp 2 F))⁆ =
      (⁅StatedSp 2 F, StatedSp 2 F⁆).subgroupOf (StatedSp 2 F) := by
    apply Subgroup.map_injective (StatedSp 2 F).subtype_injective
    rw [Subgroup.map_commutator]
    have htop : Subgroup.map (StatedSp 2 F).subtype (⊤ : Subgroup ↥(StatedSp 2 F)) =
        StatedSp 2 F := by
      rw [← MonoidHom.range_eq_map]
      exact (StatedSp 2 F).range_subtype
    rw [htop, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
  rw [hΦ, MonoidHom.range_comp, ← hfull, Subgroup.inclusion_range, ← hcomm,
    MonoidHom.range_eq_map, Subgroup.map_commutator]

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_twist {F : Type} [Field F] [Finite F] [CharP F 2] {N : Type}
    [AddCommGroup N] [Module F N] (S : burnsideI23x_SD F N) {Γ : Type} [Group Γ]
    (A : Γ →* (N ≃ₗ[F] N)) (hA : ∀ γ, S.Symp (A γ)) {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} (marking : Γ →* ↥L) (ψ : V ≃* Multiplicative (N × F))
    (hψact : ∀ γ u, ψ ((marking γ : MulAut V) u) = S.liftHom A hA γ (ψ u)) (γg : Γ) :
    ∃ (ψ₁ : V ≃* Multiplicative (N × F)) (marking₁ : Γ →* ↥L),
      (∀ u, Multiplicative.toAdd (ψ₁ u) = S.lift (hA γg⁻¹) (Multiplicative.toAdd (ψ u))) ∧
      (∀ γ, marking₁ γ = marking (γg * γ * γg⁻¹)) ∧
      (∀ γ u, ψ₁ ((marking₁ γ : MulAut V) u) = S.liftHom A hA γ (ψ₁ u)) := by
  refine ⟨ψ.trans (S.liftMul (hA γg⁻¹)), marking.comp (MulAut.conj γg).toMonoidHom,
    fun u => rfl, fun γ => rfl, fun γ u => ?_⟩
  show S.liftHom A hA γg⁻¹ (ψ ((marking (γg * γ * γg⁻¹) : MulAut V) u)) =
    S.liftHom A hA γ (S.liftHom A hA γg⁻¹ (ψ u))
  rw [hψact, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
  congr 2
  group

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_scalarCompat_twist {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM) {V : Type} [CommGroup V]
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    {ψ₀ : V ≃* Multiplicative (M × F)}
    (hψfst : ∀ u : V, (Multiplicative.toAdd (ψ₀ u)).1 = Multiplicative.toAdd (LM.e (β u)))
    (Φ : (M × F) ≃ₗ[F] (M × F)) {ψ₁ : V ≃* Multiplicative (M × F)}
    (hψ₁ : ∀ u, Multiplicative.toAdd (ψ₁ u) = Φ (Multiplicative.toAdd (ψ₀ u)))
    {W' : Type} [AddCommGroup W'] [Module F W'] (κ : (M × F) ≃ₗ[F] W') :
    I23ScalarCompatibility m F (burnsideI23x_SD.psiTrans ψ₁ κ) β := by
  have h := burnsideI23x_scalarCompat hS hψfst (Φ.trans κ)
  have e : burnsideI23x_SD.psiTrans ψ₁ κ = burnsideI23x_SD.psiTrans ψ₀ (Φ.trans κ) := by
    apply MulEquiv.ext
    intro u
    apply Multiplicative.toAdd.injective
    rw [burnsideI23x_SD.toAdd_psiTrans, burnsideI23x_SD.toAdd_psiTrans, hψ₁]
    rfl
  rw [e]
  exact h

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall CFSG.Quasithin.MS93
  CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_part1_m2_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 1)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {marking : (i23NaturalModel 2 F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel 2 F).sec ⧸
      (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec}
    (hsec : I23SectionMap (i23NaturalModel 2 F) L W0 marking β)
    (hT2 : IsPGroup 2 T) (hP : IsSylowTwoOf (T ⊓ L) L) {V1 V2 : Subgroup V}
    (h1 : IsI23MarkedSubspace 2 1 1 F T W0 V1 β) (h2 : IsI23MarkedSubspace 2 1 2 F T W0 V2 β)
    (S' : Subgroup (MulAut V)) (huniv : IsUniversalCovering L W0) :
    ∃ (ψ : V ≃* Multiplicative (Fin 2 ⊕ Fin 2 ⊕ Unit → F))
      (π : ↥(StatedOmega (StatedQuadOdd 2 F)) →* ↥L),
      Function.Surjective π ∧
      (∀ (γ : ↥(StatedOmega (StatedQuadOdd 2 F))) (v : V), ψ ((π γ : MulAut V) v) =
        Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2 ⊕ Unit) F) :
          Matrix (Fin 2 ⊕ Fin 2 ⊕ Unit) (Fin 2 ⊕ Fin 2 ⊕ Unit) F).mulVec
            (Multiplicative.toAdd (ψ v)))) ∧
      I23ScalarCompatibility 2 F ψ β ∧
      OrthConclMarked (StatedQuadOdd 2 F) 2 1 ψ L T (i23TransvectionRoot L W0 V1) S' V1 V2 := by
  have hF1 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : CharP F 2 := burnsideI23x_charP2_of_card hF1
  have hS := burnsideI23x_scalarAgree2 F
  set c := burnsideI23x_cF F hF1 with hc
  have hEndLin : ∀ φ : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ γ x, φ ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (φ x)) →
      ∃ a : F, ∀ x, φ x = a • x := fun φ hφ => burnsideI23x_hEnd2_one hF1 φ hφ
  obtain ⟨A, hA, ψ, hAlin, hgenW, hπs, hfixV, hψact, hψfst⟩ := burnsideI23x_plumb
    (burnsideI23x_LM2 F) (burnsideI23x_sd2 F) (burnsideI23x_hsymp2_any F)
    (burnsideI23x_hfaith2 F) (burnsideI23x_genW'2_one F hF1) (burnsideI23x_hbound2_one hF1) hV
    huniv hsec
  have hf := burnsideI23x_isCoord (burnsideI23x_LM2 F) hsec
  have hmb := burnsideI23x_marking_bij2 hsec
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell hS hsec h1
  obtain ⟨hU2i, hU2F, hU2c⟩ := burnsideI23x_marked_ell hS hsec h2
  have hfl1 : IsFlagW L (T ⊓ L) W0 (2 ^ 1) 1 V1 :=
    burnsideI23x_marked_imp_flag hS hV hsec (fun T' hT' => hEndLin T' hT') h1
  have hfl2 : IsFlagW L (T ⊓ L) W0 (2 ^ 1) 2 V2 :=
    burnsideI23x_marked_imp_flag hS hV hsec (fun T' hT' => hEndLin T' hT') h2
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_desc2 hF1 marking hmb hP
  rw [← hF] at hfl1 hfl2
  have hV1pre := burnsideI23x_flag1_eq_a6 hF1 hV hf hEndLin hg hfl1
  have hV2pre := burnsideI23x_flag2_eq_a6 hF1 hV hf hEndLin hg hfl2
  have hflag1 : ∀ U', IsFlagW L (T ⊓ L) W0 (2 ^ 1) 1 U' → U' = V1 := by
    intro U' hU'
    rw [← hF] at hU'
    exact (burnsideI23x_flag1_eq_a6 hF1 hV hf hEndLin hg hU').trans hV1pre.symm
  set γg := burnsideI23x_a6ι c g with hγg
  have himg1 : hf.img V1 = burnsideI23x_gm2 γg (burnsideI23x_aL1 F) :=
    (congrArg hf.img hV1pre).trans (hf.img_pre _)
  have himg2 : hf.img V2 = burnsideI23x_gm2 γg (burnsideI23x_aL2 F) :=
    (congrArg hf.img hV2pre).trans (hf.img_pre _)
  obtain ⟨ψ₁, marking₁, hψ₁, hm₁, hψ₁act⟩ :=
    burnsideI23x_twist (burnsideI23x_sd2 F) A hA marking ψ hψact γg
  have hlin1 : ∀ u, (Multiplicative.toAdd (ψ₁ u)).1 =
      (burnsideI23x_LM2 F).lin γg⁻¹ (Multiplicative.toAdd (ψ u)).1 := fun u => by
    rw [hψ₁]
    exact hAlin _ _
  have hmb₁ : Function.Bijective marking₁ := by
    have : (marking₁ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆ → ↥L) =
        marking ∘ (MulAut.conj γg).toMonoidHom := funext fun γ => hm₁ γ
    rw [this]
    exact hmb.comp (MulAut.conj γg).bijective
  have hU1' : ∀ u, u ∈ V1 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img V1 := fun u => by
    rw [hψfst]; exact hU1i u
  have hU2' : ∀ u, u ∈ V2 ↔ (Multiplicative.toAdd (ψ u)).1 ∈ hf.img V2 := fun u => by
    rw [hψfst]; exact hU2i u
  have hU1₁ : ∀ u, u ∈ V1 ↔ (Multiplicative.toAdd (ψ₁ u)).1 ∈ burnsideI23x_aL1 F := fun u => by
    rw [hU1' u, himg1, burnsideI23x_mem_gm2, hlin1]
  have hU2₁ : ∀ u, u ∈ V2 ↔ (Multiplicative.toAdd (ψ₁ u)).1 ∈ burnsideI23x_aL2 F := fun u => by
    rw [hU2' u, himg2, burnsideI23x_mem_gm2, hlin1]
  have hψK : ∀ u, u ∈ W0 ↔ (Multiplicative.toAdd (ψ u)).1 = 0 := fun u => by
    rw [hψfst]
    exact (hf.ker u).symm
  have hψ₁K : ∀ u, u ∈ W0 ↔ (Multiplicative.toAdd (ψ₁ u)).1 = 0 := fun u => by
    rw [hψK, hlin1]
    exact ⟨fun h => by rw [h, map_zero], fun h => burnsideI23x_lin2_inj_zero _ _ h⟩
  have hfix₁ : ∀ u, u ∈ fixV L ↔ (Multiplicative.toAdd (ψ₁ u)).1 = 0 := fun u => by
    rw [hfixV]; exact hψ₁K u
  have hg₁ : ∀ x : MulAut V, x ∈ T ⊓ L ↔ ∃ u : ↥(alternatingGroup (Fin 6)),
      (u : Equiv.Perm (Fin 6)) ∈ burnsideI23x_P1 ∧
        x = (((marking₁.comp (burnsideI23x_a6ι c)) u : ↥L) : MulAut V) := by
    intro x
    rw [hg x]
    refine exists_congr fun u => and_congr_right fun _ => ?_
    have e : burnsideI23x_a6ι c (g * u * g⁻¹) = γg * burnsideI23x_a6ι c u * γg⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have : marking₁ (burnsideI23x_a6ι c u) = marking (burnsideI23x_a6ι c (g * u * g⁻¹)) :=
      (hm₁ _).trans (congrArg (fun t => marking t) e.symm)
    exact iff_of_eq (congrArg (fun t : ↥L => x = (t : MulAut V)) this.symm)
  have hπ₁s : Function.Surjective marking₁ := hmb₁.2
  have hcard1 : Nat.card (hf.img V1) = Nat.card F := by rw [hU1c, hF, pow_one]
  obtain ⟨e₀, he₀, hℓ⟩ := burnsideI23x_line_of_card (burnsideI23x_aL1 F)
    (fun a x hx => burnsideI23x_aL1_smul a x hx) ((burnsideI23x_card_aL1 hF1).trans hF1.symm)
  have hfixP : V1 = fixV (T ⊓ L) :=
    le_antisymm (burnsideI23x_SD.line_le_fixV_P ψ₁ marking₁ hπ₁s hψ₁act hT2 he₀ hℓ hU1₁ h1.2.1)
      (burnsideI23x_fixV_P_le hEndLin hF hV hsec huniv.1 h1.1 hflag1)
  have hκ := burnsideI23x_kappa2_Q F
  have hcommon := burnsideI23x_SD.orth_common hF (StatedQuadOdd 2 F) (burnsideI23x_kappa2 F) hκ
    ψ₁ hψ₁K hfixV he₀ hℓ hU1₁ hfixP
  have hRbot : i23TransvectionRoot L W0 V1 = ⊥ :=
    burnsideI23x_root_bot_a6 hF1 hf h1.1 hU1F hcard1
  set zz : ↥(alternatingGroup (Fin 6)) := ⟨burnsideI23x_pz, burnsideI23x_pz_even⟩ with hzz
  set ρ : ↥(alternatingGroup (Fin 6)) →* ↥L := marking₁.comp (burnsideI23x_a6ι c) with hρdef
  have hρ : Function.Bijective ρ := hmb₁.comp (burnsideI23x_a6ι_bijective c)
  have hΩ := burnsideI23x_omega_center_a6 ρ hρ hg₁
  set z0 : MulAut V := ((ρ zz : ↥L) : MulAut V) with hz0
  have hz0sq : z0 * z0 = 1 := by
    have h : zz * zz = 1 := Subtype.ext burnsideI23x_pz_sq
    have h2 : ρ zz * ρ zz = 1 := by rw [← map_mul, h, map_one]
    exact congrArg Subtype.val h2
  have hz0ne : z0 ≠ 1 := by
    intro h
    have h2 : ρ zz = ρ 1 := by rw [map_one]; exact Subtype.ext h
    have h3 := hρ.1 h2
    exact burnsideI23x_pz_ne (congrArg Subtype.val h3)
  have hΨz0 : ∀ u, Multiplicative.toAdd (ψ₁ (z0 u)) =
      (burnsideI23x_sd2 F).lift (hA (burnsideI23x_a6ι c zz)) (Multiplicative.toAdd (ψ₁ u)) :=
    fun u => congrArg Multiplicative.toAdd (hψ₁act (burnsideI23x_a6ι c zz) u)
  have hSSC := burnsideI23x_smallSymp_std hF1 ψ₁ z0 hz0sq hz0ne (A (burnsideI23x_a6ι c zz))
    (hA _) hΨz0
    (fun x hx => (hAlin _ x).trans (burnsideI23x_Mz_M1 c x hx))
    (fun x => (congrArg (fun t => t - x ∈ burnsideI23x_aL2 F)
      (hAlin (burnsideI23x_a6ι c zz) x)).mpr (burnsideI23x_Mz_M2 c x))
    (fun x => (congrArg (fun t => burnsideI23x_sqrt F ((burnsideI23x_sd2 F).Q0 x +
        (burnsideI23x_sd2 F).Q0 t) = (t - x) (.inl 0) + (t - x) (.inl 1))
      (hAlin (burnsideI23x_a6ι c zz) x)).mpr (burnsideI23x_Mz_M3 c x))
    (fun y hy => by
      obtain ⟨x, hx⟩ := burnsideI23x_Mz_M4 c y hy
      exact ⟨x, (congrArg (fun t => t - x = y) (hAlin (burnsideI23x_a6ι c zz) x)).mpr hx⟩)
    hfix₁ hU1₁ hU2₁ hΩ
  have hfaith : ∀ γ, (∀ x, A γ x = x) → γ = 1 := fun γ h =>
    burnsideI23x_hfaith2 F γ (fun x => (hAlin γ x).symm.trans (h x))
  have hrange := burnsideI23x_phiHom_range_a6 F A hA hAlin
  obtain ⟨π, hπsurj, hπΩ⟩ := burnsideI23x_SD.exists_piOmega (burnsideI23x_kappa2 F)
    (StatedOmega (StatedQuadOdd 2 F)) hrange hfaith marking₁ hπ₁s
  refine ⟨burnsideI23x_SD.psiTrans ψ₁ (burnsideI23x_kappa2 F), π, hπsurj, ?_,
    burnsideI23x_scalarCompat_twist hS hψfst ((burnsideI23x_sd2 F).lift (hA γg⁻¹))
      (ψ₁ := ψ₁) hψ₁ (burnsideI23x_kappa2 F), ?_⟩
  · intro A' v
    obtain ⟨γ, hπγ, hAγ⟩ := hπΩ A'
    rw [hπγ, hAγ]
    show Multiplicative.ofAdd (burnsideI23x_kappa2 F
      (Multiplicative.toAdd (ψ₁ ((marking₁ γ : MulAut V) v)))) = _
    rw [hψ₁act γ v]
    rw [burnsideI23x_SD.toAdd_psiTrans]
    exact congrArg Multiplicative.ofAdd (burnsideI23x_SD.phiHom_mulVec (S := burnsideI23x_sd2 F)
      (A := A) (hA := hA) (burnsideI23x_kappa2 F) γ (Multiplicative.toAdd (ψ₁ v))).symm
  · refine ⟨hcommon.1, hcommon.2, fun h => absurd h.2 (by omega), fun _ => ⟨hRbot, hSSC⟩,
      fun h => absurd h (by norm_num)⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_case_m2_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 1)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    (hL : L = quasithinGenFitting G) (hGT : G = L ⊔ T) (hT : IsSylowTwoOf T G)
    (hGW0 : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) (hW0 : W0 ≤ fixV L) (hcomm : commV L = ⊤)
    (marking : (i23NaturalModel 2 F).Gam →* ↥L)
    (β : V →* ↥(i23NaturalModel 2 F).sec ⧸
      (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec)
    (hsec : I23SectionMap (i23NaturalModel 2 F) L W0 marking β) :
    burnsideI23x_Concl 2 1 F V G L T W0 marking β := by
  have hF1 : Nat.card F = 2 := by rw [hF, pow_one]
  haveI : Finite (MulAut V) := Finite.of_injective _ MulEquiv.toEquiv_injective
  haveI : CharP F 2 := burnsideI23x_charP2_of_card hF1
  have hLG : L ≤ G := by rw [hL]; exact CFSG.Quasithin.quasithinGenFitting_le G
  have hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    have h := CFSG.Quasithin.le_normalizer_quasithinGenFitting G hg
    rw [← hL] at h
    exact (Subgroup.mem_normalizer_iff.1 h l).1 hl
  have hTG : T ≤ G := hT.1
  have hP := burnsideI23x_sylow_inf_normal hLG hnorm hT
  have hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun t ht => hnorm t (hTG ht)
  have hTW0 : ∀ t ∈ T, ∀ w ∈ W0, t w ∈ W0 := fun t ht => hGW0 t (hTG ht)
  have hEndLin : ∀ φ : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F),
      (∀ γ x, φ ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (φ x)) →
      ∃ a : F, ∀ x, φ x = a • x := fun φ hφ => burnsideI23x_hEnd2_one hF1 φ hφ
  have hf := burnsideI23x_isCoord (burnsideI23x_LM2 F) hsec
  have hmb := burnsideI23x_marking_bij2 hsec
  obtain ⟨g, hg⟩ := burnsideI23x_sylow_desc2 hF1 marking hmb hP
  have hflag := burnsideI23x_flags_two_one hF1 hV hf hEndLin hg
  obtain ⟨V1, V2, h1, h2, h12, u1, u2, f1, f2⟩ :=
    burnsideI23x_marked_flags' (burnsideI23x_scalarAgree2 F) hV hsec hEndLin hTL hTW0 hflag
  have hfixV : fixV L = W0 :=
    burnsideI23x_fixV_eq (burnsideI23x_LM2 F) hsec hW0
      (fun x hx => burnsideI23x_nofix2_one hF1 x hx)
  obtain ⟨t1, t2, t3⟩ := burnsideI23x_transfer burnsideI23x_UCg_two_one hF hV hLG hnorm hGT hT
    hGW0 hW0 hfixV hcomm hsec h1 h2
  obtain ⟨hU1i, hU1F, hU1c⟩ := burnsideI23x_marked_ell (burnsideI23x_scalarAgree2 F) hsec h1
  have hRbot : i23TransvectionRoot L W0 V1 = ⊥ :=
    burnsideI23x_root_bot_a6 hF1 hf h1.1 hU1F (by rw [hU1c, hF, pow_one])
  refine ⟨V1, V2, h1, h2, u1, u2, ?_⟩
  intro R
  refine ⟨⊥, fun h => absurd h (by norm_num), fun _ => hRbot,
    fun huniv => ⟨fun _ => burnsideI23x_part1_m2_one hF hV hsec hT.2.1 hP h1 h2 ⊥ huniv,
      fun h3 => absurd h3 (by norm_num)⟩,
    ⟨t1, (burnsideI23x_centralCoreCompatibility V hV G V1).2 t2.1,
      (burnsideI23x_centralCoreCompatibility V hV G V2).2 t2.2⟩,
    fun hn' => absurd hn' (by norm_num)⟩

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_isCoord_map {D D' : FFModel} {K K' M M' : Type} [Field K] [Field K']
    [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K' M']
    {LM : LinModel D K M} {LM' : LinModel D' K' M'}
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : D.Gam →* ↥L} {f : V → M} (hf : IsCoord LM L W0 π f)
    (ge : D.Gam ≃* D'.Gam) (mapM : M ≃+ M')
    (hlin : ∀ (γ : D.Gam) (x : M), LM'.lin (ge γ) (mapM x) = mapM (LM.lin γ x)) :
    IsCoord LM' L W0 (π.comp ge.symm.toMonoidHom) (fun v => mapM (f v)) where
  map_mul u u' := by rw [hf.map_mul, map_add]
  ker u := by
    rw [map_eq_zero_iff _ mapM.injective]
    exact hf.ker u
  surj y := by
    obtain ⟨x, rfl⟩ := mapM.surjective y
    obtain ⟨u, rfl⟩ := hf.surj x
    exact ⟨u, rfl⟩
  act γ u := by
    show mapM (f ((π (ge.symm γ) : MulAut V) u)) = LM'.lin γ (mapM (f u))
    rw [hf.act, ← hlin, MulEquiv.apply_symm_apply]
  onto := hf.onto.comp ge.symm.surjective

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_secMap_of_isCoord {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hD : (i23NaturalModel m F).IsActionModel)
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L} {f : V → M} (hf : IsCoord LM L W0 π f) :
    ∃ β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec,
      I23SectionMap (i23NaturalModel m F) L W0 π β := by
  let φ : V →* Multiplicative M :=
    { toFun := fun v => Multiplicative.ofAdd (f v)
      map_one' := congrArg Multiplicative.ofAdd hf.map_one
      map_mul' := fun u v => congrArg Multiplicative.ofAdd (hf.map_mul u v) }
  let β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec :=
    LM.e.symm.toMonoidHom.comp φ
  have hβ : ∀ v, LM.e (β v) = Multiplicative.ofAdd (f v) := fun v => LM.e.apply_symm_apply _
  refine ⟨β, hf.onto, ?_, ?_, hD.ker_le, hD.sec_inv, hD.ker_inv, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hf.surj (Multiplicative.toAdd (LM.e y))
    refine ⟨x, LM.e.injective ?_⟩
    rw [hβ, hx, ofAdd_toAdd]
  · ext v
    rw [MonoidHom.mem_ker, ← hf.ker]
    constructor
    · intro h
      have h1 := congrArg LM.e h
      rw [hβ, map_one] at h1
      exact congrArg Multiplicative.toAdd h1
    · intro h
      apply LM.e.injective
      rw [hβ, map_one, h]
      rfl
  · intro γ v native hNative hv
    apply LM.e.injective
    rw [hβ]
    have h1 : Multiplicative.toAdd (LM.e (QuotientGroup.mk native)) = f v := by
      rw [← hv, hβ]
      rfl
    have h2 := LM.e_act γ native hNative
    rw [h1] at h2
    rw [← hf.act γ v] at h2
    rw [← h2]
    rfl

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_endStableMod_of_scalars {D : FFModel} {F : Type} [Field F] {M : Type}
    [AddCommGroup M] [Module F M] {LM : LinModel D F M}
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : D.Gam →* ↥L} {f : V → M} (hf : IsCoord LM L W0 π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : F, ∀ x, T x = c • x)
    {U : Subgroup V} (hWU : W0 ≤ U)
    (hsc : ∀ c : F, ∀ x ∈ hf.img U, c • x ∈ hf.img U) : IsEndStableMod L W0 U := by
  intro φ hφ u hu
  let ψ : V →* Multiplicative M :=
    { toFun := fun v => Multiplicative.ofAdd (f v)
      map_one' := congrArg Multiplicative.ofAdd hf.map_one
      map_mul' := fun u v => congrArg Multiplicative.ofAdd (hf.map_mul u v) }
  have hψker : ψ.ker = W0 := by
    ext v
    rw [MonoidHom.mem_ker, ← hf.ker]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨v, hv⟩ := hf.surj (Multiplicative.toAdd y)
    exact ⟨v, by show Multiplicative.ofAdd (f v) = y; rw [hv, ofAdd_toAdd]⟩
  let Φ : V ⧸ W0 ≃* Multiplicative M :=
    (QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  have hΦ : ∀ v : V, Φ (QuotientGroup.mk v) = Multiplicative.ofAdd (f v) := fun v => rfl
  let Tm : Multiplicative M →* Multiplicative M :=
    Φ.toMonoidHom.comp (φ.comp Φ.symm.toMonoidHom)
  let T : M →+ M :=
    { toFun := fun x => Multiplicative.toAdd (Tm (Multiplicative.ofAdd x))
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [ofAdd_add, map_mul, toAdd_mul] }
  have hT : ∀ v w : V, φ (QuotientGroup.mk v) = QuotientGroup.mk w → T (f v) = f w := by
    intro v w h
    show Multiplicative.toAdd (Φ (φ (Φ.symm (Multiplicative.ofAdd (f v))))) = f w
    have h1 : Φ.symm (Multiplicative.ofAdd (f v)) = QuotientGroup.mk v :=
      Φ.symm_apply_eq.2 (hΦ v).symm
    rw [h1, h]
    rfl
  have hTcomm : ∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x) := by
    intro γ x
    obtain ⟨v, rfl⟩ := hf.surj x
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (φ (QuotientGroup.mk v))
    have h1 := hφ ((π γ : ↥L) : MulAut V) (π γ).2 v w hw.symm
    rw [← hf.act γ v, hT _ _ h1, hT v w hw.symm, hf.act γ w]
  obtain ⟨c, hc⟩ := hcomm T hTcomm
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (φ (QuotientGroup.mk u))
  refine ⟨w, ?_, hw.symm⟩
  rw [hf.mem_iff hWU, ← hT u w hw.symm, hc]
  exact hsc c _ ⟨u, hu, rfl⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_marked_imp_tinv {m n i : ℕ} {F : Type} [Field F] {M : Type}
    [AddCommGroup M] [Module F M] {LM : LinModel (i23NaturalModel m F) F M}
    (hS : burnsideI23x_ScalarAgree m F LM)
    {V : Type} [CommGroup V] {L T : Subgroup (MulAut V)} {W0 : Subgroup V}
    {π : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (h : I23SectionMap (i23NaturalModel m F) L W0 π β)
    (hcomm : ∀ T : M →+ M, (∀ (γ : (i23NaturalModel m F).Gam) (x : M),
      T (LM.lin γ x) = LM.lin γ (T x)) → ∃ c : F, ∀ x, T x = c • x)
    {U : Subgroup V} (hM : IsI23MarkedSubspace m n i F T W0 U β) :
    IsTInvFSub L T W0 n i U := by
  obtain ⟨hWU, hT, hcard, hscal⟩ := hM
  exact ⟨hWU, hT, burnsideI23x_endStableMod_of_scalars (burnsideI23x_isCoord LM h) hcomm hWU
    ((burnsideI23x_native_iff_img hS h).1 hscal), hcard⟩

open Matrix in
@[expose] noncomputable def burnsideI23x_glMap {ι : Type} [Fintype ι] [DecidableEq ι]
    {K F : Type} [Field K] [Field F] (e : K ≃+* F) :
    Matrix.GeneralLinearGroup ι K ≃* Matrix.GeneralLinearGroup ι F :=
  Units.mapEquiv e.mapMatrix.toMulEquiv

theorem burnsideI23x_glMap_coe {ι : Type} [Fintype ι] [DecidableEq ι]
    {K F : Type} [Field K] [Field F] (e : K ≃+* F) (g : Matrix.GeneralLinearGroup ι K) :
    ((burnsideI23x_glMap e g : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
      ((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).map e := rfl

theorem burnsideI23x_map_eq_of_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    {K F : Type} [Field K] [Field F] (e : K ≃+* F)
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {Γ' : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (h : ∀ g : Matrix.GeneralLinearGroup ι K, g ∈ Γ ↔ burnsideI23x_glMap e g ∈ Γ') :
    Γ.map (burnsideI23x_glMap e).toMonoidHom = Γ' := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (h g).1 hg
  · intro hy
    refine ⟨(burnsideI23x_glMap e).symm y, (h _).2 ?_, MulEquiv.apply_symm_apply _ y⟩
    rw [MulEquiv.apply_symm_apply]
    exact hy

@[expose] noncomputable def burnsideI23x_natGe {ι : Type} [Fintype ι] [DecidableEq ι]
    {K F : Type} [Field K] [Field F] (e : K ≃+* F)
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (Γ' : Subgroup (Matrix.GeneralLinearGroup ι F))
    (h : Γ.map (burnsideI23x_glMap e).toMonoidHom = Γ') : ↥Γ ≃* ↥Γ' :=
  ((burnsideI23x_glMap e).subgroupMap Γ).trans (MulEquiv.subgroupCongr h)

theorem burnsideI23x_natGe_coe {ι : Type} [Fintype ι] [DecidableEq ι]
    {K F : Type} [Field K] [Field F] (e : K ≃+* F)
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (Γ' : Subgroup (Matrix.GeneralLinearGroup ι F))
    (h : Γ.map (burnsideI23x_glMap e).toMonoidHom = Γ') (γ : ↥Γ) :
    (((burnsideI23x_natGe e Γ Γ' h γ : ↥Γ') : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
      ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).map e := rfl

open CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_natLin {ι : Type} [Fintype ι] [DecidableEq ι]
    {K F : Type} [Field K] [Field F] (e : K ≃+* F)
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (Γ' : Subgroup (Matrix.GeneralLinearGroup ι F))
    (h : Γ.map (burnsideI23x_glMap e).toMonoidHom = Γ') (γ : ↥Γ) (x : ι → K) :
    (linModelNat Γ').lin (burnsideI23x_natGe e Γ Γ' h γ)
        ((AddEquiv.piCongrRight fun _ : ι => e.toAddEquiv) x) =
      (AddEquiv.piCongrRight fun _ : ι => e.toAddEquiv) ((linModelNat Γ).lin γ x) := by
  rw [linModelNat_lin, linModelNat_lin, burnsideI23x_natGe_coe]
  funext i
  exact (RingHom.map_mulVec (e : K →+* F) _ x i).symm

open CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_map_statedSL {K F : Type} [Field K] [Field F] (e : K ≃+* F) :
    (StatedSL 2 K).map (burnsideI23x_glMap (ι := Fin 2) e).toMonoidHom = StatedSL 2 F := by
  refine burnsideI23x_map_eq_of_iff e fun g => ?_
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, CFSG.Open.StatedAPI.mem_statedSL_iff,
    burnsideI23x_glMap_coe]
  have h := RingHom.map_det (e : K →+* F) ((g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K)
  show _ = 1 ↔ _
  rw [show ((g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map e =
    (e : K →+* F).mapMatrix ((g : Matrix.GeneralLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) from rfl, ← h]
  exact (map_eq_one_iff e e.injective).symm

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Assembly.LowTwoRank in
open scoped Matrix in
theorem burnsideI23x_map_statedSp {K F : Type} [Field K] [Field F] [CharP K 2] [CharP F 2]
    (e : K ≃+* F) :
    (StatedSp 2 K).map (burnsideI23x_glMap (ι := Fin 2 ⊕ Fin 2) e).toMonoidHom =
      StatedSp 2 F := by
  refine burnsideI23x_map_eq_of_iff e fun g => ?_
  rw [CFSG.Quasithin.MS93.statedSp_eq_sp4' (F := K), CFSG.Quasithin.MS93.statedSp_eq_sp4' (F := F)]
  have hJ : (spJ K).map e = spJ F := by
    unfold spJ
    rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero e), Matrix.map_one _ (map_zero e)
      (map_one e)]
  have hmul : ∀ (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
      (A * B).map e = A.map e * B.map e := fun A B => Matrix.map_mul (f := (e : K →+* F))
  have htr : ∀ A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, (A.map e)ᵀ = Aᵀ.map e :=
    fun A => Matrix.transpose_map
  show ((g : Matrix.GeneralLinearGroup _ K) : Matrix _ _ K)ᵀ * spJ K *
      ((g : Matrix.GeneralLinearGroup _ K) : Matrix _ _ K) = spJ K ↔
    ((burnsideI23x_glMap e g : Matrix.GeneralLinearGroup _ F) : Matrix _ _ F)ᵀ * spJ F *
      ((burnsideI23x_glMap e g : Matrix.GeneralLinearGroup _ F) : Matrix _ _ F) = spJ F
  rw [burnsideI23x_glMap_coe, ← hJ, htr, ← hmul, ← hmul]
  exact (Matrix.map_injective e.injective).eq_iff.symm

open CFSG.Quasithin CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_map_derivedSp {K F : Type} [Field K] [Field F] [CharP K 2] [CharP F 2]
    (e : K ≃+* F) :
    ⁅StatedSp 2 K, StatedSp 2 K⁆.map (burnsideI23x_glMap (ι := Fin 2 ⊕ Fin 2) e).toMonoidHom =
      ⁅StatedSp 2 F, StatedSp 2 F⁆ := by
  rw [Subgroup.map_commutator, burnsideI23x_map_statedSp]

open CFSG.Quasithin in
theorem burnsideI23x_g2D_le (F : Type) [Field F] :
    ⁅quasithinG2 F, quasithinG2 F⁆ ≤ quasithinG2 F :=
  Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.H13.VolI
  CFSG.Quasithin.Vol2.KGNat in
theorem burnsideI23x_hlin3 {K F : Type} [Field K] [Field F] [CharP K 2] [CharP F 2]
    (e : K ≃+* F) (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) (x : Ix3 → K) :
    (burnsideI23x_LM3 F).lin (g2DerivedFieldEquiv e γ)
        ((AddEquiv.piCongrRight fun _ : Ix3 => e.toAddEquiv) x) =
      (AddEquiv.piCongrRight fun _ : Ix3 => e.toAddEquiv) ((burnsideI23x_LM3 K).lin γ x) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective
    ((zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆).symm (Multiplicative.ofAdd x))
  obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective
    (zornQSecEquiv e (QuotientGroup.mk m : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Sec))
  have hm0 : zornAct _ γ m.1 ∈ zornO0 K := zornAct_mem_O0 _ (burnsideI23x_g2D_le K) γ m.2
  have hm1 : zornAct _ (g2DerivedFieldEquiv e γ) m'.1 ∈ zornO0 F :=
    zornAct_mem_O0 _ (burnsideI23x_g2D_le F) _ m'.2
  have key := zornQSecEquiv_act e γ _ rfl m m' hm'.symm hm0 hm1
  have hcoord : ∀ s : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Sec,
      Multiplicative.toAdd (zornSecEquiv ⁅quasithinG2 F, quasithinG2 F⁆ (zornQSecEquiv e s)) =
        (AddEquiv.piCongrRight fun _ : Ix3 => e.toAddEquiv)
          (Multiplicative.toAdd (zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆ s)) := fun s => by
    simp only [zornQSecEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hx : Multiplicative.toAdd (zornSecEquiv ⁅quasithinG2 K, quasithinG2 K⁆
      (QuotientGroup.mk m)) = x := by
    rw [hm]
    simp
  have h1 := (burnsideI23x_LM3 F).e_act (g2DerivedFieldEquiv e γ) m' hm1
  have h2 := (burnsideI23x_LM3 K).e_act γ m hm0
  have h3 : Multiplicative.toAdd ((burnsideI23x_LM3 F).e (QuotientGroup.mk m')) =
      (AddEquiv.piCongrRight fun _ : Ix3 => e.toAddEquiv) x := by
    show Multiplicative.toAdd (zornSecEquiv ⁅quasithinG2 F, quasithinG2 F⁆ (QuotientGroup.mk m')) = _
    rw [hm', hcoord, hx]
  rw [h3] at h1
  rw [← h1]
  show Multiplicative.toAdd (zornSecEquiv ⁅quasithinG2 F, quasithinG2 F⁆
    (QuotientGroup.mk ⟨zornAct _ (g2DerivedFieldEquiv e γ) m'.1, hm1⟩)) = _
  rw [← key, hcoord]
  congr 1
  rw [← hx]
  exact h2

theorem burnsideI23x_one_le_of_card {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : 1 ≤ n := by
  by_contra h
  have h0 : n = 0 := by omega
  subst h0
  have := Finite.one_lt_card (α := F)
  simp [hF] at this

noncomputable def burnsideI23x_fieldEquiv {K F : Type} [Field K] [Finite K] [Field F] [Finite F]
    (h : Nat.card K = Nat.card F) : K ≃+* F :=
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite F
  FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact h)

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_hasSec_m1 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {n : ℕ} (h : BinaryNaturalSL L ⊤ W0 2 n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) :
    ∃ (marking : (i23NaturalModel 1 F).Gam →* ↥L)
      (β : V →* ↥(i23NaturalModel 1 F).sec ⧸
        (i23NaturalModel 1 F).ker.subgroupOf (i23NaturalModel 1 F).sec),
      I23SectionMap (i23NaturalModel 1 F) L W0 marking β := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  obtain ⟨f, hf⟩ := exists_isCoord (burnsideI23x_LM1 K) hπ
  let e : K ≃+* F := burnsideI23x_fieldEquiv (hK.trans hF.symm)
  have hf' := burnsideI23x_isCoord_map (LM' := burnsideI23x_LM1 F) hf
    (burnsideI23x_natGe e _ _ (burnsideI23x_map_statedSL e))
    (AddEquiv.piCongrRight fun _ : Fin 2 => e.toAddEquiv)
    (fun γ x => burnsideI23x_natLin e _ _ (burnsideI23x_map_statedSL e) γ x)
  obtain ⟨β, hβ⟩ := burnsideI23x_secMap_of_isCoord (LM := burnsideI23x_LM1 F)
    (FFModel.nat_isActionModel (StatedSL 2 F)) hf'
  exact ⟨_, β, hβ⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_hasSec_m2 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {n : ℕ} (h : SpDerivedNatural L ⊤ W0 n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) :
    ∃ (marking : (i23NaturalModel 2 F).Gam →* ↥L)
      (β : V →* ↥(i23NaturalModel 2 F).sec ⧸
        (i23NaturalModel 2 F).ker.subgroupOf (i23NaturalModel 2 F).sec),
      I23SectionMap (i23NaturalModel 2 F) L W0 marking β := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  haveI : CharP K 2 := charP_two_of_card (by have := burnsideI23x_one_le_of_card hK; omega) hK
  haveI : CharP F 2 := charP_two_of_card (by have := burnsideI23x_one_le_of_card hF; omega) hF
  obtain ⟨f, hf⟩ := exists_isCoord (burnsideI23x_LM2 K) hπ
  let e : K ≃+* F := burnsideI23x_fieldEquiv (hK.trans hF.symm)
  have hf' := burnsideI23x_isCoord_map (LM' := burnsideI23x_LM2 F) hf
    (burnsideI23x_natGe e _ _ (burnsideI23x_map_derivedSp e))
    (AddEquiv.piCongrRight fun _ : Fin 2 ⊕ Fin 2 => e.toAddEquiv)
    (fun γ x => burnsideI23x_natLin e _ _ (burnsideI23x_map_derivedSp e) γ x)
  obtain ⟨β, hβ⟩ := burnsideI23x_secMap_of_isCoord (LM := burnsideI23x_LM2 F)
    (FFModel.nat_isActionModel ⁅StatedSp 2 F, StatedSp 2 F⁆) hf'
  exact ⟨_, β, hβ⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.H13.VolI in
theorem burnsideI23x_hasSec_m3 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {W0 : Subgroup V} {n : ℕ} (h : G2NaturalDerived L ⊤ W0 n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) :
    ∃ (marking : (i23NaturalModel 3 F).Gam →* ↥L)
      (β : V →* ↥(i23NaturalModel 3 F).sec ⧸
        (i23NaturalModel 3 F).ker.subgroupOf (i23NaturalModel 3 F).sec),
      I23SectionMap (i23NaturalModel 3 F) L W0 marking β := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  haveI : CharP K 2 := charP_two_of_card (by have := burnsideI23x_one_le_of_card hK; omega) hK
  haveI : CharP F 2 := charP_two_of_card (by have := burnsideI23x_one_le_of_card hF; omega) hF
  obtain ⟨f, hf⟩ := exists_isCoord (burnsideI23x_LM3 K) hπ
  let e : K ≃+* F := burnsideI23x_fieldEquiv (hK.trans hF.symm)
  have hf' := burnsideI23x_isCoord_map (LM' := burnsideI23x_LM3 F) hf
    (g2DerivedFieldEquiv e) (AddEquiv.piCongrRight fun _ : Ix3 => e.toAddEquiv)
    (fun γ x => burnsideI23x_hlin3 e γ x)
  obtain ⟨β, hβ⟩ := burnsideI23x_secMap_of_isCoord (LM := burnsideI23x_LM3 F)
    (FFModel.zornQ_isActionModel _ (burnsideI23x_g2D_le F)) hf'
  exact ⟨_, β, hβ⟩

open CFSG.Quasithin CFSG.ASVolI.ChIJK in
theorem burnsideI23x_orth_of_marked {F : Type} [Field F] {W : Type} [AddCommGroup W]
    [Module F W] {Q : W → F} {m n : ℕ} {V : Type} [CommGroup V] {ψ : V ≃* Multiplicative W}
    {L T R S : Subgroup (MulAut V)} {V1 V2 : Subgroup V}
    (hS : m = 3 → S = ChIJK.omegaOne (ChIJK.centerOf (T ⊓ L)))
    (h : OrthConclMarked Q m n ψ L T R S V1 V2) : OrthConcl Q m n ψ L T R V1 V2 := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨a, b, c, d, fun h3 => ?_⟩
  rw [← hS h3]
  exact e h3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK in
theorem burnsideI23x_legacy_core {m n : ℕ} {F : Type} [Field F] [Finite F] {V : Type}
    [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G L T : Subgroup (MulAut V)}
    {W0 : Subgroup V} {marking : (i23NaturalModel m F).Gam →* ↥L}
    {β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec}
    (hconcl : burnsideI23x_Concl m n F V G L T W0 marking β)
    (hTInv : ∀ (i : ℕ) (U : Subgroup V), IsI23MarkedSubspace m n i F T W0 U β →
      IsTInvFSub L T W0 n i U)
    {V1 V2 : Subgroup V} (hu1 : ∀ U : Subgroup V, IsTInvFSub L T W0 n 1 U → U = V1)
    (hu2 : ∀ U : Subgroup V, IsTInvFSub L T W0 n 2 U → U = V2)
    {R : Subgroup (MulAut V)} (hR : R = i23TransvectionRoot L W0 V1) :
    (IsUniversalCovering L W0 →
        ((m = 1 ∨ m = 2) →
          ∃ (ψ : V ≃* Multiplicative (Fin m ⊕ Fin m ⊕ Unit → F))
            (π : ↥(StatedOmega (StatedQuadOdd m F)) →* ↥L),
            Function.Surjective π ∧
            (∀ (γ : ↥(StatedOmega (StatedQuadOdd m F))) (v : V),
              ψ ((π γ : MulAut V) v) = Multiplicative.ofAdd
                (((γ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m ⊕ Unit) F) :
                  Matrix (Fin m ⊕ Fin m ⊕ Unit) (Fin m ⊕ Fin m ⊕ Unit) F).mulVec
                  (Multiplicative.toAdd (ψ v)))) ∧
            OrthConcl (StatedQuadOdd m F) m n ψ L T R V1 V2) ∧
        (m = 3 →
          ∃ (ψ : V ≃* Multiplicative ↥(zornO0F F))
            (π : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L),
            Function.Surjective π ∧
            (∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (v : V),
              ((Multiplicative.toAdd (ψ ((π γ : MulAut V) v)) : ↥(zornO0F F)) :
                  quasithinZorn F) =
                (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
                  ((Multiplicative.toAdd (ψ v) : ↥(zornO0F F)) : quasithinZorn F)) ∧
            OrthConcl (fun x : ↥(zornO0F F) => zornNorm F (x : quasithinZorn F)) m n ψ L T R
              V1 V2)) ∧
      (¬ (fixV T ⊓ V1 ≤ fixV L) ∧
        pCoreOf 2 (G ⊓ stabSub V1) ≤ centSub V1 ∧ pCoreOf 2 (G ⊓ stabSub V2) ≤ centSub V2) ∧
      (1 < n → fixV L ≤ V1 ∧ (m ≠ 3 → V1 = commV R ∧ commV R ≤ fixV R)) := by
  obtain ⟨V1', V2', h1', h2', -, -, hrest⟩ := hconcl
  have e1 : V1' = V1 := hu1 V1' (hTInv 1 V1' h1')
  have e2 : V2' = V2 := hu2 V2' (hTInv 2 V2' h2')
  subst e1 e2
  subst hR
  dsimp only at hrest
  obtain ⟨S, hS3, hS21, hp1, hp2, hp3⟩ := hrest
  refine ⟨fun huniv => ⟨fun hm12 => ?_, fun hm3 => ?_⟩, ?_, hp3⟩
  · obtain ⟨ψ, π, hs, he, -, hO⟩ := (hp1 huniv).1 hm12
    exact ⟨ψ, π, hs, he, burnsideI23x_orth_of_marked (fun h3 => by omega) hO⟩
  · obtain ⟨ψ, π, hs, he, -, hO⟩ := (hp1 huniv).2 hm3
    exact ⟨ψ, π, hs, he, burnsideI23x_orth_of_marked (fun h3 => (hS3 h3).2.1) hO⟩
  · exact ⟨hp2.1, (burnsideI23x_centralCoreCompatibility V hV G V1').1 hp2.2.1,
      (burnsideI23x_centralCoreCompatibility V hV G V2').1 hp2.2.2⟩

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_hEnd2_all {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (T : (Fin 2 ⊕ Fin 2 → F) →+ (Fin 2 ⊕ Fin 2 → F))
    (hT : ∀ (γ : ↥⁅StatedSp 2 F, StatedSp 2 F⁆) (x : Fin 2 ⊕ Fin 2 → F),
      T ((burnsideI23x_LM2 F).lin γ x) = (burnsideI23x_LM2 F).lin γ (T x)) :
    ∃ c : F, ∀ x, T x = c • x := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by omega
    subst hn1
    exact burnsideI23x_hEnd2_one (by simpa using hF) T hT
  · obtain ⟨c₀, hc0, hc1⟩ := burnsideI23x_exists_ne_zero_one hF h
    have hperf := burnsideI23x_sp_perfect hc0 hc1
    exact commutant_statedSp T (fun γ x => hT ⟨(γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F),
      hperf.ge γ.2⟩ x)

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.JonesParshall in
theorem burnsideI23x_hEnd3_all {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (T : (Ix3 → F) →+ (Ix3 → F))
    (hT : ∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (x : Ix3 → F),
      T ((burnsideI23x_LM3 F).lin γ x) = (burnsideI23x_LM3 F).lin γ (T x)) :
    ∃ c : F, ∀ x, T x = c • x := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by omega
    subst hn1
    exact burnsideI23x_hEnd3_one (by simpa using hF) T hT
  · obtain ⟨c₀, hc0, hc1⟩ := burnsideI23x_exists_ne_zero_one hF h
    exact commutant_g2Derived hc0 hc1 _ T hT

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChIJK CFSG.Quasithin.Vol2.KGNat
  CFSG.Assembly.LowTwoRank in
theorem burnsideI23x_legacy_key (h123 : burnsideI23x_MarkedStmt) {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L T : Subgroup (MulAut V)} {W0 : Subgroup V} {m n : ℕ}
    (hL : L = quasithinGenFitting G) (hGT : G = L ⊔ T) (hT : IsSylowTwoOf T G)
    (hGW0 : ∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) (hW0 : W0 ≤ fixV L) (hcomm : commV L = ⊤)
    (hcase : I23Case m n L W0) {V1 V2 : Subgroup V}
    (hu1 : ∀ U : Subgroup V, IsTInvFSub L T W0 n 1 U → U = V1)
    (hu2 : ∀ U : Subgroup V, IsTInvFSub L T W0 n 2 U → U = V2)
    {R : Subgroup (MulAut V)} (hR : R = i23TransvectionRoot L W0 V1)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) :
    (IsUniversalCovering L W0 →
        ((m = 1 ∨ m = 2) →
          ∃ (ψ : V ≃* Multiplicative (Fin m ⊕ Fin m ⊕ Unit → F))
            (π : ↥(StatedOmega (StatedQuadOdd m F)) →* ↥L),
            Function.Surjective π ∧
            (∀ (γ : ↥(StatedOmega (StatedQuadOdd m F))) (v : V),
              ψ ((π γ : MulAut V) v) = Multiplicative.ofAdd
                (((γ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m ⊕ Unit) F) :
                  Matrix (Fin m ⊕ Fin m ⊕ Unit) (Fin m ⊕ Fin m ⊕ Unit) F).mulVec
                  (Multiplicative.toAdd (ψ v)))) ∧
            OrthConcl (StatedQuadOdd m F) m n ψ L T R V1 V2) ∧
        (m = 3 →
          ∃ (ψ : V ≃* Multiplicative ↥(zornO0F F))
            (π : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L),
            Function.Surjective π ∧
            (∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (v : V),
              ((Multiplicative.toAdd (ψ ((π γ : MulAut V) v)) : ↥(zornO0F F)) :
                  quasithinZorn F) =
                (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
                  ((Multiplicative.toAdd (ψ v) : ↥(zornO0F F)) : quasithinZorn F)) ∧
            OrthConcl (fun x : ↥(zornO0F F) => zornNorm F (x : quasithinZorn F)) m n ψ L T R
              V1 V2)) ∧
      (¬ (fixV T ⊓ V1 ≤ fixV L) ∧
        pCoreOf 2 (G ⊓ stabSub V1) ≤ centSub V1 ∧ pCoreOf 2 (G ⊓ stabSub V2) ≤ centSub V2) ∧
      (1 < n → fixV L ≤ V1 ∧ (m ≠ 3 → V1 = commV R ∧ commV R ≤ fixV R)) := by
  have hn1 : 1 ≤ n := burnsideI23x_one_le_of_card hF
  haveI : CharP F 2 := charP_two_of_card (by omega) hF
  rcases hcase with ⟨rfl, hn, hnat⟩ | ⟨rfl, hnat⟩ | ⟨rfl, hnat⟩
  · obtain ⟨marking, β, hsec⟩ := burnsideI23x_hasSec_m1 hnat F hF
    exact burnsideI23x_legacy_core hV
      (h123 V hV G L T W0 1 n hL hGT hT hGW0 hW0 hcomm (Or.inl ⟨rfl, hn⟩) F hF marking β hsec)
      (fun i U hU => burnsideI23x_marked_imp_tinv (burnsideI23x_scalarAgree1 F) hsec
        (fun T' hT' => commutant_statedSL (by norm_num) T' hT') hU) hu1 hu2 hR
  · obtain ⟨marking, β, hsec⟩ := burnsideI23x_hasSec_m2 hnat F hF
    exact burnsideI23x_legacy_core hV
      (h123 V hV G L T W0 2 n hL hGT hT hGW0 hW0 hcomm (Or.inr (Or.inl ⟨rfl, hn1⟩)) F hF
        marking β hsec)
      (fun i U hU => burnsideI23x_marked_imp_tinv (burnsideI23x_scalarAgree2 F) hsec
        (fun T' hT' => burnsideI23x_hEnd2_all hF hn1 T' hT') hU) hu1 hu2 hR
  · obtain ⟨marking, β, hsec⟩ := burnsideI23x_hasSec_m3 hnat F hF
    exact burnsideI23x_legacy_core hV
      (h123 V hV G L T W0 3 n hL hGT hT hGW0 hW0 hcomm (Or.inr (Or.inr ⟨rfl, hn1⟩)) F hF
        marking β hsec)
      (fun i U hU => burnsideI23x_marked_imp_tinv (burnsideI23x_scalarAgree3 F) hsec
        (fun T' hT' => burnsideI23x_hEnd3_all hF hn1 T' hT') hU) hu1 hu2 hR

theorem burnsideI23x_marked_all :
    burnsideI23x_MarkedStmt := by
  refine burnsideI23x_assembly ?_ ?_
  · intro F _ _ hF V _ _ hV G L T W0 hL hGT hT hGW0 hW0 hcomm marking β hsec
    exact burnsideI23x_case_m2_one hF hV hL hGT hT hGW0 hW0 hcomm marking β hsec
  · intro F _ _ hF V _ _ hV G L T W0 hL hGT hT hGW0 hW0 hcomm marking β hsec
    exact burnsideI23x_case_m3_one hF hV hL hGT hT hGW0 hW0 hcomm marking β hsec

section


theorem as_I_2_3 : I_2_3 := by
  exact burnsideI23x_marked_all

end

section


theorem as_I_2_3_legacyUnmarked : I_2_3_legacyUnmarked := by
  intro V _ _ hV G L T W0 m n hL hGT hT hGW0 hW0 hcomm hcase V1 V2 _ _ hu1 hu2 R hR
  obtain ⟨K, fK, fin, hK⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n := by
    rcases hcase with ⟨_, _, K, fK, fin, hK, _⟩ | ⟨_, K, fK, fin, hK, _⟩ |
      ⟨_, K, fK, fin, hK, _⟩ <;> exact ⟨K, fK, fin, hK⟩
  have key := fun (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) =>
    burnsideI23x_legacy_key burnsideI23x_marked_all hV hL hGT hT hGW0 hW0 hcomm hcase hu1 hu2 hR F hF
  exact ⟨fun huniv F _ _ hF => (key F hF).1 huniv, (key K hK).2⟩

end


end CFSG.ASVolI
