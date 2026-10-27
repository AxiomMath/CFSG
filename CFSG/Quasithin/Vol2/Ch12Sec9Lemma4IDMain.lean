module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4IDIrr
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep1
public import CFSG.Quasithin.Vol2.Ch12Sec8OneNine
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueIrr
public import CFSG.Quasithin.Vol2.Ch3Sec2IrrPlus
public import CFSG.Quasithin.Vol2.Ch10SecKIK4a
public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenFiveStmt
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIDefs
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13
open IDIrr

@[expose] def Lemma12_9_4Overgroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1291 G T L V 4 →
    ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
      ∃ K' : Subgroup G, K ≤ K' ∧ quasithinIsMaximalLocal T K' ∧ quasithinIsFaithfulLocal T K' ∧
        (K' = K ∨
          Nonempty (↥K' ⧸ CFSG.pCore 2 ↥K' ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
          Nonempty (↥K' ⧸ CFSG.pCore 2 ↥K' ≃* NativeSporadic.M24) ∨
          Nonempty (↥K' ⧸ CFSG.pCore 2 ↥K' ≃* NativeSporadic.J4))

theorem case1294FiveID_of_five (h1222 : Stmt12_2_2) (h1264 : Stmt12_6_34)
    (h12813f : Lemma12_8_13_five) (h1292 : Lemma12_9_2) (hov : Lemma12_9_4Overgroup) :
    Case1294FiveID := by
  intro G _ _ T L V hcx V₁ V₂ K₁ hs hLK hK hK4 D h5 himg
  have hH : Hyp1223 G T L V := hcx.hyp.hyp
  have hO2 : oTwoUpper (p128 T L V) ≤ p128 T L V := by
    unfold oTwoUpper
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  obtain ⟨g, hgmem, hgN⟩ := L128P.exists_not_mem_normalizer h1222 hs
  have hgP : g ∈ p128 T L V := hO2 hgmem
  obtain ⟨-, -, hVle, hVred, hZK, -, hKfaith⟩ :=
    h12813f G T L V V₁ V₂ K₁ hs hLK hK hK4 g hgP hgN D h5 himg
  obtain ⟨K', -, hK'max, hK'faith, hK'cases⟩ := hov G T L V hcx K₁ hKfaith hK4
  have hmax1 : quasithinIsMaximalLocal T K₁ := by
    rcases hK'cases with h | h | h | h
    · rw [h] at hK'max
      exact hK'max
    · exact absurd ⟨K', hK'max, hK'faith, Or.inl h⟩ (h1292 G T L V 4 hcx rfl)
    · exact absurd ⟨K', hK'max, hK'faith, Or.inr (Or.inl h)⟩ (h1292 G T L V 4 hcx rfl)
    · exact absurd ⟨K', hK'max, hK'faith, Or.inr (Or.inr h)⟩ (h1292 G T L V 4 hcx rfl)
  have hfaith1 : quasithinIsFaithfulLocal T K₁ := hKfaith
  have hsimple : IsSimpleGroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := isSimpleGroup_quot hK4
  have hquasi : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
    obtain ⟨e⟩ := id hK4
    exact CFSG.IsQuasisimple.of_mulEquiv e
      (isQuasisimple_sl_zmod_two (m := 4) (by norm_num)).1
  obtain ⟨hTK, -, hirr⟩ :=
    (h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left hH.notAlt K₁ hmax1
      hfaith1 hquasi
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup G,
      Z = quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) := ⟨_, rfl⟩
  rw [← hZdef] at hVle hVred hZK
  obtain ⟨VD, hVDdef⟩ : ∃ VD : Subgroup G, VD = conjClosure Z K₁ := ⟨_, rfl⟩
  rw [← hVDdef] at hVle hVred
  have hVDab : IsElemAbelian 2 VD := hVred.2.2.1
  have hVDcomm : ∀ a ∈ VD, ∀ b ∈ VD, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVDab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVDsq : ∀ a ∈ VD, a ^ 2 = 1 := hVDab.2
  have hK₁VD : K₁ ≤ Subgroup.normalizer (VD : Set G) := fun k hk =>
    hVred.2.1 ((le_sup_left : K₁ ≤ K₁ ⊔ T) hk)
  have hTVD : T ≤ Subgroup.normalizer (VD : Set G) := fun t ht =>
    hVred.2.1 ((le_sup_right : T ≤ K₁ ⊔ T) ht)
  have hVDR : VD ≤ reducedAggregate (K₁ ⊔ T) := IDIrr.le_reducedAggregate_of_isTwoReducedIn hVred
  have hZVD : Z ≤ VD := by
    rw [hVDdef]
    exact le_conjClosure Z K₁
  have hbotVD : ⁅VD, K₁⁆ ≠ ⊥ := by
    intro h
    have hle : ⁅Z, K₁⁆ ≤ ⁅VD, K₁⁆ := Subgroup.commutator_mono hZVD le_rfl
    rw [h] at hle
    exact hZK (le_bot_iff.1 hle)
  have hO2K : ∀ N : Subgroup G, N ≤ K₁ → (N.subgroupOf K₁).Normal →
      (∀ x ∈ K₁, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = K₁ :=
    fun N hNK hN hpow => CFSG.Quasithin.C2Nine.eq_of_perfect_of_pow_mem hK.2.1 hNK hN hpow
  obtain ⟨I, hI⟩ := exists_irrPlusBase hO2K (fun x hx => by
      have h2 := hVDsq x hx
      rw [pow_two] at h2
      exact h2) hK₁VD hbotVD
  haveI : IsMulCommutative ↥VD := hVDab.1
  obtain ⟨V₀, hV₀, -⟩ := exists_isIrrPlusIn_sectionIso hVDsq hK₁VD hTVD hTK hH.sylow.1 hI
  have hV₀VD : V₀ ≤ VD := hV₀.1
  have hirrR : IsIrrPlusIn K₁ (reducedAggregate (K₁ ⊔ T)) T V₀ :=
    IDIrr.isIrrPlusIn_of_le (reducedAggregate_props (K₁ ⊔ T)).2.1 hVDR hK₁VD hTVD hV₀
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := (hirr V₀ hirrR).1.2.1
  have hK₁N : K₁ ≤ Subgroup.normalizer (V₀ : Set G) := hV₀.2.2.1
  have hV₀ne : V₀ ≠ ⊥ := hV₀.2.1
  have hV₀comm : ⁅V₀, K₁⁆ = V₀ := hV₀.2.2.2.1
  have hO2C : pCoreOf 2 K₁ ≤ Subgroup.centralizer (V₀ : Set G) := by
    have h1 : pCoreOf 2 K₁ ≤ Subgroup.centralizer (VD : Set G) :=
      CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.pCoreOf_le_centralizer hVred le_sup_left
        (sup_le (Subgroup.le_normalizer) hTK)
    exact h1.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hV₀VD))
  have hcn : ∀ g ∈ K₁, ∀ c ∈ Subgroup.centralizer (V₀ : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V₀ : Set G) := by
    intro g hg c hc v hv
    have hw : g⁻¹ * v * g ∈ V₀ := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hK₁N (K₁.inv_mem hg)) v).1 hv
      simpa using h1
    have hcw := Subgroup.mem_centralizer_iff.1 hc _ hw
    calc v * (g * c * g⁻¹) = g * (g⁻¹ * v * g * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcw]
      _ = (g * c * g⁻¹) * v := by group
  have hMn : ((K₁ ⊓ Subgroup.centralizer (V₀ : Set G)).subgroupOf K₁).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ K₁ ⊓ Subgroup.centralizer (V₀ : Set G) := Subgroup.mem_subgroupOf.1 hn
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.mem_inf] at hn' ⊢
    exact ⟨K₁.mul_mem (K₁.mul_mem g.2 hn'.1) (K₁.inv_mem g.2), hcn _ g.2 _ hn'.2⟩
  have hsub : K₁ ⊓ Subgroup.centralizer (V₀ : Set G) = pCoreOf 2 K₁ := by
    refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K₁) hO2C)
    have hMsimple := hsimple.eq_bot_or_eq_top_of_normal
      ((((K₁ ⊓ Subgroup.centralizer (V₀ : Set G)).subgroupOf K₁).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))))
    intro x hx
    rcases hMsimple with hbot | htop
    · have hx' : (⟨x, (Subgroup.mem_inf.1 hx).1⟩ : ↥K₁) ∈
          (K₁ ⊓ Subgroup.centralizer (V₀ : Set G)).subgroupOf K₁ :=
        Subgroup.mem_subgroupOf.2 hx
      have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)) hx'
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact Subgroup.mem_map.2 ⟨⟨x, (Subgroup.mem_inf.1 hx).1⟩, hmem, rfl⟩
    · exfalso
      have hK1C : K₁ ≤ Subgroup.centralizer (V₀ : Set G) := by
        intro k hk
        have hmemtop : (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) (⟨k, hk⟩ : ↥K₁)) ∈
            ((((K₁ ⊓ Subgroup.centralizer (V₀ : Set G)).subgroupOf K₁).map
              (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)))) := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.1 hmemtop
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyk
        have hq : (((y⁻¹ * ⟨k, hk⟩ : ↥K₁) : G)) ∈ pCoreOf 2 K₁ :=
          Subgroup.mem_map.2 ⟨_, hyk, rfl⟩
        have hqC := hO2C hq
        have hyC : (y : G) ∈ Subgroup.centralizer (V₀ : Set G) :=
          (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).2
        have hk' : (k : G) = (y : G) * (((y⁻¹ * ⟨k, hk⟩ : ↥K₁) : G)) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [hk']
        exact Subgroup.mul_mem _ hyC hqC
      have hV₀C : V₀ ≤ Subgroup.centralizer (K₁ : Set G) := fun v hv =>
        Subgroup.mem_centralizer_iff.2 fun k hk =>
          ((Subgroup.mem_centralizer_iff.1 (hK1C hk)) v hv).symm
      have hcomm0 : ⁅V₀, K₁⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hV₀C
      exact hV₀ne (hV₀comm.symm.trans hcomm0)
  obtain ⟨e⟩ := id hK4
  let φ : ↥K₁ →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : φ.ker = (Subgroup.centralizer (V₀ : Set G)).subgroupOf K₁ := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : φ k = 1 ↔ k ∈ CFSG.pCore 2 ↥K₁ := by
      show e (QuotientGroup.mk k) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    rw [h1]
    constructor
    · intro hk
      have hmem : (k : G) ∈ pCoreOf 2 K₁ := Subgroup.mem_map.2 ⟨k, hk, rfl⟩
      rw [← hsub] at hmem
      exact (Subgroup.mem_inf.1 hmem).2
    · intro hk
      have hmem : (k : G) ∈ K₁ ⊓ Subgroup.centralizer (V₀ : Set G) := ⟨k.2, hk⟩
      rw [hsub] at hmem
      obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.1 hmem
      have hyk' : y = k := Subtype.ext hyk
      rw [← hyk']
      exact hy
  have hH1 : Hyp1223 G T K₁ V₀ :=
    { simple := hH.simple, nonabelian := hH.nonabelian, qtke := hH.qtke, sylow := hH.sylow,
      notAlt := hH.notAlt, maximal := hmax1, faithful := hfaith1, quasisimple := hquasi,
      normalizes := hTK, irrPlus := hirrR }
  obtain ⟨hcard, -, -, -⟩ := (stmt12_6_34_iff.1 h1264) G T K₁ V₀ hH1 ⟨φ, hφs, hφker⟩
  have hV₀comm' : IsMulCommutative ↥V₀ :=
    ⟨⟨fun a b => Subtype.ext (hVDcomm a.1 (hV₀VD a.2) b.1 (hV₀VD b.2))⟩⟩
  refine ⟨V₀, hV₀VD.trans hVle, hK₁N, hTV₀, ⟨hV₀comm', fun x hx => hVDsq x (hV₀VD hx)⟩, ?_, hsub⟩
  rw [hcard]
  norm_num

end CFSG.Quasithin.H13.C1294
