module

public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2A
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316J
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.Quasithin.H13.Ln2

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap
  mem_normalizer_perfectCore exists_inducedAut mem_normalizer_of_map_le mem_pCoreOf_of_ker
  mem_lFamilyOf_of_hom le_sup_liftCore isMaxParabolic2_liftPre)

section Mult

variable {K : Type} [Field K] [Finite K]

theorem lieModel_psl_two (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n) :
    CFSG.Models.LieModel (StatedProj (StatedSL n K)) .PSL n 2 1 := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by
      intro h
      have := congrArg Prod.fst h
      simp only at this
      omega, by
      intro h
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, by rw [hK]; norm_num,
    ⟨MulEquiv.refl _⟩⟩⟩

theorem card_hopfMultiplier_dvd_two (hGA : GriessAllModelsStatement) (hK : Nat.card K = 2)
    {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5) :
    Nat.card ↥(RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSL n K))) ∣ 2 := by
  obtain ⟨-, ⟨e⟩⟩ := hGA _ .PSL n 2 1 (lieModel_psl_two hK (by omega))
  rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr e.toEquiv]
  rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
  · have hgen : Blueprint.Multiplier.genericOrders .PSL 4 2 1 = (1, 1) := by decide
    have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 4 2 1 = (2, 1) := by decide
    unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
    rw [hgen, hexc]
    simp
  · have hgen : Blueprint.Multiplier.genericOrders .PSL 5 2 1 = (1, 1) := by decide
    have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 5 2 1 = (1, 1) := by decide
    unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
    rw [hgen, hexc]
    simp

end Mult

variable {G : Type} [Group G] [Finite G]

theorem exists_modO2Surj {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hGA : GriessAllModelsStatement) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (e : ↥(autOn L (vPlus L T)) ≃* SpecialLinearGroup (Fin n) K) :
    ∃ α : ↥L →* SpecialLinearGroup (Fin n) K, Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥L ∧
      ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  let φ := InternalSec.autOnHom hLV
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hLV
  let α : ↥L →* SpecialLinearGroup (Fin n) K := e.toMonoidHom.comp φ
  have hαφ : ∀ l, α l = 1 ↔ φ l = 1 := fun l => by
    simp only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hαs : Function.Surjective α := e.surjective.comp hφs
  have hNK : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro l hl
    rw [InternalSec.mem_ker_autOnHom]
    exact hQC (hOQ ((Lem3328.mem_pCore_iff l).mp hl))
  have hKN : φ.ker ≤ CFSG.pCore 2 ↥L := by
    set N := CFSG.pCore 2 ↥L with hN
    set Kφ := φ.ker with hKφ
    have hNn : N.Normal := CFSG.pCore_normal
    have hq := h.Lq
    have : Group.IsPerfect (↥L ⧸ N) := hq.1
    let e₂ : ↥(autOn L (vPlus L T)) ≃* StatedProj (StatedSL n K) := e.trans (slEquivStatedProj hK n)
    let q : ↥L ⧸ N →* StatedProj (StatedSL n K) :=
      e₂.toMonoidHom.comp (QuotientGroup.lift N φ hNK)
    have hqmk : ∀ l : ↥L, q (l : ↥L ⧸ N) = e₂ (φ l) := fun l => rfl
    have hqs : Function.Surjective q := by
      intro y
      obtain ⟨l, hl⟩ := hφs (e₂.symm y)
      exact ⟨l, by rw [hqmk, hl, MulEquiv.apply_symm_apply]⟩
    have hker : ∀ l : ↥L, q (l : ↥L ⧸ N) = 1 ↔ l ∈ Kφ := fun l => by
      rw [hqmk, MulEquiv.map_eq_one_iff]
      rfl
    have hqn : q.ker.Normal := MonoidHom.normal_ker q
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq q.ker with hc | htop
    ·
      have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hqs hc
      have hcard : Nat.card ↥q.ker ∣ 2 := by
        have h1 := Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier
          (StatedProj (StatedSL n K))) (RankThree.PerfectCover.hopfLift q hqs hc)
        rw [hmap] at h1
        exact h1.trans (card_hopfMultiplier_dvd_two hGA hK hn4 hn5)
      have hp : IsPGroup 2 ↥q.ker := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h1 | h1
        · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
        · exact IsPGroup.of_card (n := 1) (by rw [h1, pow_one])
      have hK2 : IsPGroup 2 ↥Kφ := by
        rintro ⟨k, hk⟩
        obtain ⟨a, ha⟩ := hp ⟨(k : ↥L ⧸ N), (hker k).mpr hk⟩
        have ha' : ((k ^ 2 ^ a : ↥L) : ↥L ⧸ N) = 1 := by
          have := congrArg Subtype.val ha
          simpa using this
        have hkN : k ^ 2 ^ a ∈ N := (QuotientGroup.eq_one_iff _).mp ha'
        obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hkN⟩
        refine ⟨a + b, Subtype.ext ?_⟩
        have hb' : (k ^ 2 ^ a) ^ 2 ^ b = 1 := by
          have := congrArg Subtype.val hb
          simpa using this
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [pow_add, pow_mul, hb']
      exact le_sSup ⟨MonoidHom.normal_ker φ, hK2⟩
    · exfalso
      have htriv : ∀ l : ↥L, φ l = 1 := by
        intro l
        have hl : (l : ↥L ⧸ N) ∈ q.ker := htop ▸ Subgroup.mem_top _
        exact (hker l).mp hl
      have hS := sl_nonabelian_of_card_two hK (m := n) (by omega)
      obtain ⟨a, b, hab⟩ := hS
      obtain ⟨x, rfl⟩ := hαs a
      obtain ⟨y, rfl⟩ := hαs b
      apply hab
      have hx : α x = 1 := (hαφ x).mpr (htriv x)
      have hy : α y = 1 := (hαφ y).mpr (htriv y)
      rw [hx, hy]
  refine ⟨α, hαs, ?_, fun l => ?_⟩
  · ext l
    rw [MonoidHom.mem_ker, hαφ, ← MonoidHom.mem_ker]
    exact ⟨fun hl => hKN hl, fun hl => hNK hl⟩
  · rw [hαφ, ← MonoidHom.mem_ker, InternalSec.mem_ker_autOnHom]

theorem exists_unitriangular {L T : Subgroup G} (hS₀ : IsSylowTwoOf (T ⊓ L) L) {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) {α : ↥L →* SpecialLinearGroup (Fin n) K}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L) :
    ∃ α₂ : ↥L →* SpecialLinearGroup (Fin n) K, Function.Surjective α₂ ∧
      α₂.ker = CFSG.pCore 2 ↥L ∧ ((T ⊓ L).subgroupOf L).map α₂ = unitriangular n K := by
  have hP₀ : IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
    refine ⟨le_top, hS₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀.1).symm, fun h2 => ?_⟩
    apply hS₀.2.2
    rwa [show (((T ⊓ L).subgroupOf L).subgroupOf ⊤).index = ((T ⊓ L).subgroupOf L).index from
      Subgroup.relIndex_top_right _] at h2
  have hU₁ : IsSylowTwoOf (((T ⊓ L).subgroupOf L).map α) ⊤ := by
    have h1 := L3312.isSylowTwoOf_map_range α hP₀
    rwa [MonoidHom.range_eq_top.mpr hαs] at h1
  have hU₀ : IsSylowTwoOf (unitriangular n K) ⊤ := SzN2.isSylowTwoOf_unitriangular hn
  obtain ⟨k, -, hk⟩ := (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj
    (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₀)
  refine ⟨(MulAut.conj k).toMonoidHom.comp α, ?_, ?_, ?_⟩
  · rw [MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hαs
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hαk]
  · rw [← Subgroup.map_map]
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm

theorem le_normalizer_liftPre {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n)
    {α : ↥L →* SpecialLinearGroup (Fin n) K} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) (hmapU : ((T ⊓ L).subgroupOf L).map α = unitriangular n K)
    (hT1 : T ≤ Subgroup.normalizer (liftPre α (stabilizer (flagSpace n K 1)) : Set G))
    (I : Set ℕ) : T ≤ Subgroup.normalizer (liftPre α (flagStabilizer n K I) : Set G) := by
  intro t ht
  obtain ⟨φ, hφ⟩ := exists_inducedAut hαs hαk (hTL ht)
  have hmem : ∀ l : ↥L, (t * l * t⁻¹ : G) ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp l.2
  have hU : ∀ u ∈ unitriangular n K, φ u ∈ unitriangular n K := by
    intro u hu
    rw [← hmapU] at hu ⊢
    obtain ⟨l, hl, rfl⟩ := hu
    refine ⟨⟨t * l * t⁻¹, hmem l⟩, ?_, (hφ l).symm⟩
    have hl' : (l : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hl
    exact Subgroup.mem_subgroupOf.mpr ⟨T.mul_mem (T.mul_mem ht hl'.1) (T.inv_mem ht), hmem l⟩
  have hQ : ∀ g ∈ stabilizer (flagSpace n K 1), φ g ∈ stabilizer (flagSpace n K 1) := by
    intro g hg
    obtain ⟨l, rfl⟩ := hαs g
    rw [hφ]
    have h1 : (l : G) ∈ liftPre α (stabilizer (flagSpace n K 1)) := ⟨l, hg, rfl⟩
    obtain ⟨l', hl', hl'e⟩ := (Subgroup.mem_normalizer_iff.mp (hT1 ht) _).mp h1
    have : l' = ⟨t * l * t⁻¹, hmem l⟩ := Subtype.ext hl'e
    rw [← this]
    exact hl'
  obtain ⟨u, huU, hφu⟩ := eq_conj_of_mulAut hK hn φ hU hQ
  have huI : u ∈ flagStabilizer n K I :=
    upperTriangular_le_flagStabilizer I (unitriangular_le_upperTriangular (n := n) (K := K) huU)
  apply mem_normalizer_of_map_le
  rintro _ ⟨p, ⟨lp, hlp, rfl⟩, rfl⟩
  refine ⟨⟨t * lp * t⁻¹, hmem lp⟩, ?_, rfl⟩
  show α ⟨t * lp * t⁻¹, hmem lp⟩ ∈ flagStabilizer n K I
  rw [← hφ, hφu]
  exact (flagStabilizer n K I).mul_mem ((flagStabilizer n K I).mul_mem huI hlp)
    ((flagStabilizer n K I).inv_mem huI)

theorem exists_hom_of {L : Subgroup G} {Y : Type} [Group Y] [Finite Y] {φ : ↥L →* Y}
    (hφ : Function.Surjective φ) (hk : IsPGroup 2 ↥φ.ker) {P : Subgroup Y} {S : Type*} [Group S]
    {g : ↥(perfectCore P) →* S} (hg : Function.Surjective g) (hgk : IsPGroup 2 ↥g.ker) :
    ∃ f : ↥(liftCore φ P) →* S, Function.Surjective f ∧ IsPGroup 2 ↥f.ker := by
  let e₀ : ↥(liftCore φ P) ≃* ↥(perfectCore (P.comap φ)) :=
    (MulEquiv.subgroupCongr (liftCore_eq φ P)).trans
      (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm
  let ψ₁ : ↥(perfectCore (P.comap φ)) →* ↥(perfectCore P) :=
    (MulEquiv.subgroupCongr (map_perfectCore_comap hφ P)).toMonoidHom.comp (φ.subgroupMap _)
  have hψ₁ : Function.Surjective ψ₁ :=
    (MulEquiv.subgroupCongr (map_perfectCore_comap hφ P)).surjective.comp
      (φ.subgroupMap_surjective _)
  have hψ₁v : ∀ y, ((ψ₁ y : ↥(perfectCore P)) : Y) = φ (y : ↥L) := fun y => rfl
  refine ⟨(g.comp ψ₁).comp e₀.toMonoidHom, (hg.comp hψ₁).comp e₀.surjective, ?_⟩
  rintro ⟨x, hx⟩
  have h1 : g (ψ₁ (e₀ x)) = 1 := hx
  obtain ⟨a, ha⟩ := hgk ⟨ψ₁ (e₀ x), h1⟩
  have h2 : ψ₁ ((e₀ x) ^ 2 ^ a) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  have h3 : φ (((e₀ x) ^ 2 ^ a : ↥(perfectCore (P.comap φ))) : ↥L) = 1 := by
    rw [← hψ₁v, h2]
    rfl
  obtain ⟨b, hb⟩ := hk ⟨_, h3⟩
  have h4 : ((e₀ x) ^ 2 ^ a) ^ 2 ^ b = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hb
    simpa using this
  refine ⟨a + b, Subtype.ext ?_⟩
  apply e₀.injective
  show e₀ (x ^ 2 ^ (a + b)) = e₀ 1
  rw [show x ^ 2 ^ (a + b) = (x ^ 2 ^ a) ^ 2 ^ b by rw [← pow_mul, ← pow_add], map_pow,
    map_pow, h4, map_one]

theorem exists_hom_big {L : Subgroup G} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {n : ℕ} (hn5 : n ≤ 5) {α : ↥L →* SpecialLinearGroup (Fin n) K} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) :
    ∃ f : ↥(liftCore α (flagStabilizer n K I)) →* SpecialLinearGroup (Fin m) K,
      Function.Surjective f ∧ IsPGroup 2 ↥f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl
    (by rw [hK]; norm_num)
  have hkp : IsPGroup 2 ↥α.ker := by
    rw [hαk]
    exact CFSG.pCore_isPGroup
  exact exists_hom_of hαs hkp (bigBlockHom_surjective hK h hm3 ha hb hno)
    (isPGroup_ker_of_unitriangular (by omega) _ fun x hx =>
      unitriangular_of_bigBlockHom hK hn5 h hm3 ha hb hno x hx)

theorem liftCore_mem_lFamilyOf {L T : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hO : pCoreOf 2 (L ⊔ T) ≠ ⊥) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn5 : n ≤ 5) {α : ↥L →* SpecialLinearGroup (Fin n) K} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m))
    (hTP : T ≤ Subgroup.normalizer (liftPre α (flagStabilizer n K I) : Set G)) :
    liftCore α (flagStabilizer n K I) ∈ lFamilyOf L T := by
  obtain ⟨f, hf, hfk⟩ := exists_hom_big hK hn5 hαs hαk h hm3 ha hb hno
  have : IsSimpleGroup (SpecialLinearGroup (Fin m) K) := sl_isSimple_of_card_two hK hm3
  exact mem_lFamilyOf_of_hom hT hO (liftCore_le _ _) (perfectCore_perfect _)
    (fun t ht => mem_normalizer_perfectCore (hTP ht)) f hf hfk

theorem sup_liftCore_eq {L T : Subgroup G} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5) {α : ↥L →* SpecialLinearGroup (Fin n) K}
    (hαs : Function.Surjective α) (hkT : α.ker.map L.subtype ≤ T)
    (hmapU : ((T ⊓ L).subgroupOf L).map α = unitriangular n K) :
    L ⊔ T = liftCore α (flagStabilizer n K {1}) ⊔ liftCore α (flagStabilizer n K {3}) ⊔ T := by
  have hgen : perfectCore (flagStabilizer n K {1}) ⊔ perfectCore (flagStabilizer n K {3}) ⊔
      (T.subgroupOf L).map α = ⊤ := by
    rw [← Subgroup.inf_subgroupOf_right, hmapU]
    exact sup_perfectCore_eq_top hK hn4 hn5
  exact le_antisymm (sup_le (le_sup_liftCore hαs hkT hgen) le_sup_right)
    (sup_le (sup_le ((liftCore_le _ _).trans le_sup_left) ((liftCore_le _ _).trans le_sup_left))
      le_sup_right)

end CFSG.Quasithin.H13.Ln2
