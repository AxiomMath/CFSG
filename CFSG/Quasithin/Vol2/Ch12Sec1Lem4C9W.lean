module

public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.EmptyFaithful.S152HeProp134
public import CFSG.Quasithin.Vol2.Ch1Sec3Lem139Cases
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4GW
public import CFSG.Quasithin.H13.NQCoreLemma139
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4E
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank EmptyFaithfulMultiple
open scoped IsMulCommutative

namespace Sec1214

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ T₀ : Subgroup G} {v : G}
  (c : Setting T L V V₁ V₂ v T₀)
include c

theorem exists_component_cW (hFF : LemH9FF4) (hA21 : AsA21SQTKSection) (h51 : AsB51)
    (h134 : C134L32CorrM) (hE9 : Prop134E9He) (h128two : Lemma128Two)
    (h128four : Lemma128Four) (hKG1 : Lemma139L42Inner) (hKG2 : Lemma139A5Inner)
    (h38 : Vol2Native.A38ForSQTKCat) (h1001 : Stmt10_0_1) {X : Subgroup G}
    (hX : IsXSub T L V V₁ X) :
    ∃ K : Subgroup G, K ∈ cComp (T₀ ⊔ X ⊔ T) ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K ∧
      T ≤ Subgroup.normalizer (K : Set G) ∧ X ≤ K ∧
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 3 1 ∨
        Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3))) ∨
        (∃ n : ℕ, Even n ∧
          CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 2 n) ∨
        Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 4 2 1 ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 5 2 1 ∨
        Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) := by
  set H := T₀ ⊔ X ⊔ T with hH
  have hTH : T ≤ H := le_sup_right
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo c.S.ctx.hyp.sylow hTH
  have hO2 := c.pCoreOf_ne_bot_H hFF hX
  have hXH : X ≤ H := le_sup_right.trans (le_sup_left : T₀ ⊔ X ≤ H)
  obtain ⟨P, hPX, hP3, hP9⟩ := hX.sylow
  rcases hE9 G H T X P (c.isSQTKCat_H hFF hX) hO2 hsyl hXH hX.xi hX.relIndex hPX hP3 hP9 with
    hN | ⟨K, hK, hq, hXK, hcases⟩
  · exact absurd hN (c.not_le_normalizer_XW hFF hA21 h51 h134 hX)
  have hloc : quasithinIsLocal T K := isLocal_of_mem_cComp_of_sylow hsyl hO2 hK
  have hfaith : quasithinIsFaithfulLocal T K :=
    (NQCore.lemma139Two G c.S.ctx.hyp.qtke c.S.ctx.hyp.simple c.S.ctx.hyp.nonabelian T X K
      c.S.ctx.hyp.sylow ⟨hX.xi, hX.xf⟩ hloc hXK).2
  have hmax : quasithinIsMaximalLocal T K :=
    lemma139One_of_cases h128two h128four hKG1 hKG2 h38 c.S.ctx.hyp.qtke c.S.ctx.hyp.simple
      c.S.ctx.hyp.nonabelian c.S.ctx.hyp.sylow hX.xi hX.relIndex hPX hP3 hP9 hloc hXK hq hcases
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    h1001 G T K c.S.ctx.hyp.simple c.S.ctx.hyp.nonabelian c.S.ctx.hyp.qtke c.S.ctx.hyp.sylow hmax
      hfaith hq
  have hXK' : X ≤ K := hXK.trans (conjClosure_le fun t ht k hk =>
    (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk)
  refine ⟨K, hK, hq, hmax, hfaith, hTK, hXK', ?_⟩
  rcases hcases with ⟨⟨t, ht, htK, -⟩, -⟩ | ⟨-, h2⟩ | ⟨-, h3, -⟩ | ⟨-, h4⟩ | ⟨-, h5⟩
  · exact absurd (hTK ht.1) htK
  · rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h3))
  · rcases h4 with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h5)))))

theorem exists_component_lin_cW
    (hFF : LemH9FF4) (hA21 : AsA21SQTKSection) (h51 : AsB51)
    (h134 : C134L32CorrM) (hE9 : Prop134E9He) (h128two : Lemma128Two)
    (h128four : Lemma128Four) (hKG1 : Lemma139L42Inner) (hKG2 : Lemma139A5Inner)
    (h38 : Vol2Native.A38ForSQTKCat) (h1001 : Stmt10_0_1) (h1101 : Stmt11_0_1) (h323 : Stmt3_2_3)
    (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C) {X : Subgroup G}
    (hX : IsXSub T L V V₁ X) :
    ∃ K : Subgroup G, K ∈ cComp (T₀ ⊔ X ⊔ T) ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K ∧
      T₀ ⊔ X ⊔ T ≤ Subgroup.normalizer (K : Set G) ∧ X ≤ K ∧
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 4 2 1 ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 5 2 1) := by
  obtain ⟨K, hK, hq, hmax, hfaith, hTK, hXK, hcases⟩ :=
    c.exists_component_cW hFF hA21 h51 h134 hE9 h128two h128four hKG1 hKG2 h38 h1001
      hX
  refine ⟨K, hK, hq, hmax, hfaith, c.le_normalizer_K hFF h323 hX hK hq hmax hfaith hTK, hXK, ?_⟩
  have hex : ∀ N : ℕ, IsSimpleGroup (O2Q K) → Nat.card (O2Q K) = N →
      Sec1214Orders.OrderFacts N → False := fun N hs hc hN =>
    false_of_orderFacts c.S.ctx.hyp.simple c.S.ctx.hyp.nonabelian c.S.ctx.hyp.qtke
      c.S.ctx.hyp.sylow hmax hfaith hq hs hTK h323 h325 h328 h329 hc hN
  rcases hcases with h | he | h | he | h | h | he
  · obtain ⟨hs, hc⟩ := Sec1214Orders.simple_card_L33 h
    exact (hex _ hs hc Sec1214Orders.orderFacts_5616).elim
  · obtain ⟨e⟩ := he
    obtain ⟨hs, hc⟩ := Sec1214Orders.simple_card_SL33 e
    exact (hex _ hs hc Sec1214Orders.orderFacts_5616).elim
  · exact (c.not_sp4 h1101 hmax hfaith h).elim
  · obtain ⟨e⟩ := he
    obtain ⟨hs, hc⟩ := Sec1214Orders.simple_card_M11 e
    exact (hex _ hs hc Sec1214Orders.orderFacts_7920).elim
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨e⟩ := he
    obtain ⟨hs, hc⟩ := Sec1214Orders.simple_card_He e
    exact (hex _ hs hc Sec1214Orders.orderFacts_he).elim

end Setting

end Sec1214

theorem lem1214Step_of_inputs_cW
    (h331 : Stmt3_3_1) (h1001 : Stmt10_0_1) (h1101 : Stmt11_0_1) (h323 : Stmt3_2_3)
    (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C) (h134 : C134L32CorrM)
    (h128two : Lemma128Two) (h128four : Lemma128Four) (hKG1 : Lemma139L42Inner)
    (hKG2 : Lemma139A5Inner) (h38 : Vol2Native.A38ForSQTKCat) (hFF : LemH9FF4)
    (hA21 : AsA21SQTKSection) (h51 : AsB51) (hE9 : EmptyFaithfulMultiple.Prop134E9He)
    (hJ4 : LemH9J4) : Lem1214Step := by
  intro G _ _ T L V V₁ V₂ n hyp hn hTL v hv T₀ hT₀ hT₁T₀ hT₀v hT₀N hT₀M
  subst hn
  obtain ⟨C₁, C₂, hd⟩ := KGH91.exists_dualCoord hyp
  have c : Sec1214.Setting T L V V₁ V₂ v T₀ :=
    ⟨⟨C₁, C₂, hd, ⟨hyp, hTL, KGH91.isDualPairing C₁ C₂ hd, hv⟩⟩, h331, hT₀, hT₁T₀, hT₀v, hT₀N,
      hT₀M⟩
  obtain ⟨X, hX⟩ := c.exists_isXSub hJ4
  obtain ⟨K, hK, -, -, -, hHK, hXK, hlin⟩ :=
    c.exists_component_lin_cW hFF hA21 h51 h134 hE9 h128two h128four hKG1 hKG2 h38 h1001
      h1101 h323 h325 h328 h329 hX
  rcases hlin with h4 | h5
  · exact c.false_of_component_linW hFF hA21 h51 h134 hX hX.nonab hK hHK hXK (Or.inl rfl) h4
  · exact c.false_of_component_linW hFF hA21 h51 h134 hX hX.nonab hK hHK hXK (Or.inr rfl) h5

theorem lem1214Step_of_cW
    (h331 : Stmt3_3_1) (h1001 : Stmt10_0_1) (h1101 : Stmt11_0_1) (h323 : Stmt3_2_3)
    (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C) (h134 : C134L32CorrM)
    (h128two : Lemma128Two) (h128four : Lemma128Four) (hKG1 : Lemma139L42Inner)
    (hKG2 : Lemma139A5Inner) (h38 : Vol2Native.A38ForSQTKCat) : Lem1214Step :=
  lem1214Step_of_inputs_cW h331 h1001 h1101 h323 h325 h328 h329 h134 h128two h128four hKG1
    hKG2 h38 H9Four.lemH9FF4_holds asA21SQTKSection B5.asB51_holds prop134E9He_holds lemH9J4_holds

end CFSG.Quasithin.H13
