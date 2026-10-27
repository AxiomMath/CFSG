module

public import CFSG.Quasithin.Vol2.Ch12Sec4L5Aux
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma3
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch12Sec4Cx
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma9

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G]

theorem pCoreOf_sup_eq_of_hyp1223 (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) [Finite G]
    {T L V : Subgroup G} (hyp : Hyp1223 G T L V) :
    pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, hfsu⟩, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨-, -, hO⟩ := h3228 G T L V hfsu
  rwa [hyp.conjClosure_eq, conjClosure_eq_of_le_normalizer hTV] at hO

section L3

variable [Finite G] {T L V : Subgroup G} {z : G} [IsMulCommutative ↥V]

theorem cx_autOn_T_eq (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (hnat : BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1) :
    QuasithinUnique.IsSylowTwoOf (autOn (T ⊓ L) V) (autOn L V) ∧
      autOn T V = autOn (T ⊓ L) V := by
  have hyp := hcx.hyp
  have hsylTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow (le_sup_right : T ≤ L ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hyp.normalizes)
  have hS1 := QuasithinUnique.Setup.isSylowTwoOf_autOn hsylTL hf.normalizes
  obtain ⟨D⟩ := hnat.toL3Coord
  have hcommGr := commV_autOn_eq_top hf.normalizes hf.commutator
  have hSX : autOn T V ≤ autOn L V := fun s hs =>
    Vol2.Ch10.SecD.mem_of_normalizes D hcommGr
      (Subgroup.mem_normalizer_iff.1 (autOn_le_normalizer_autOn_of_le hyp.normalizes hs))
  exact ⟨hS1, eq_of_isSylowTwoOf_le hS1 (A4.autOn_mono inf_le_left) hSX
    (isPGroup_autOn hyp.sylow.1)⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem cx_mem_mul_of_mem_T (hf : CxFacts G T L V z)
    (hT : autOn T V = autOn (T ⊓ L) V) {t : G} (ht : t ∈ T) :
    ∃ l ∈ T ⊓ L, l⁻¹ * t ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
  have hc : conjAct V ⟨t, hf.T_le ht⟩ ∈ autOn (T ⊓ L) V :=
    hT ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
  obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.1 hc
  rw [Subgroup.mem_subgroupOf] at hg
  refine ⟨g, hg, T.mul_mem (T.inv_mem hg.1) ht, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hge
  simp only [A5Mod.conjAct_apply_coe] at h1
  calc v * ((g : G)⁻¹ * t) = (g : G)⁻¹ * ((g : G) * v * (g : G)⁻¹) * t := by group
    _ = (g : G)⁻¹ * (t * v * t⁻¹) * t := by rw [h1]
    _ = (g : G)⁻¹ * t * v := by group

theorem cx_inf_centralizer_T_le (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (hV16 : Nat.card V = 2 ^ 4) (hnat : BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1) :
    V ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨hS1, -⟩ := cx_autOn_T_eq hcx hf hnat
  obtain ⟨D⟩ := hnat.toL3Coord
  have h16 : Nat.card ↥V = 16 := by rw [hV16]; norm_num
  have hcommGr := commV_autOn_eq_top hf.normalizes hf.commutator
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcommGr h16
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  obtain ⟨-, -, h3, -⟩ := B4_8_2 hW h16 hnat hind
  have hfix := h3 _ hS1
  intro v hv
  have hv1 : (⟨v, hv.1⟩ : ↥V) ∈ fixV (autOn (T ⊓ L) V) := by
    rw [fixV_autOn_eq ((inf_le_left : T ⊓ L ≤ T).trans hf.T_le)]
    exact Subgroup.centralizer_le (inf_le_left : ((T ⊓ L : Subgroup G) : Set G) ⊆ T) hv.2
  rw [hfix, fixV_autOn_eq hf.normalizes] at hv1
  exact hv1

theorem lemma12_4_5_three (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (hV16 : Nat.card V = 2 ^ 4) (hGr : Nat.card (autOn L V) = 168)
    (hnat : BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1) {E : Subgroup G} (hEV : E ≤ V)
    (hE4 : Nat.card E = 4) {A : Subgroup G}
    (hA : IsMaxElemAbelian (T ⊓ Subgroup.centralizer (E : Set G)) A)
    (hAQ : ¬ A ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    autOn A V = autOn (T ⊓ Subgroup.centralizer (E : Set G)) V := by
  have hyp := hcx.hyp
  obtain ⟨hS1, hTeq⟩ := cx_autOn_T_eq hcx hf hnat
  obtain ⟨D⟩ := hnat.toL3Coord
  have h16 : Nat.card ↥V = 16 := by rw [hV16]; norm_num
  have hcommGr := commV_autOn_eq_top hf.normalizes hf.commutator
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcommGr h16
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  obtain ⟨-, -, h3, h4⟩ := B4_8_2 hW h16 hnat hind
  set R₁ := T ⊓ Subgroup.centralizer (E : Set G) with hR₁
  have hR₁T : R₁ ≤ T := inf_le_left
  have hAR : A ≤ R₁ := hA.1
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := (hAR.trans hR₁T).trans hf.T_le
  have hR₁N : R₁ ≤ Subgroup.normalizer (V : Set G) := hR₁T.trans hf.T_le
  have hA1 : autOn A V ≠ ⊥ := by
    intro h
    apply hAQ
    intro a ha
    refine ⟨hR₁T (hAR ha), ?_⟩
    have h1 : conjAct V ⟨a, hAN ha⟩ ∈ autOn A V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ha)
    rw [h, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.1 h1
  have hAT : autOn A V ≤ autOn T V := A4.autOn_mono (hAR.trans hR₁T)
  have hTL : autOn T V ≤ autOn L V := hTeq ▸ hS1.1
  have hVR : V ≤ R₁ := le_inf hf.le_T
    (hf.le_centralizer.trans (Subgroup.centralizer_le hEV))
  have hB24 := card_le_relIndex_mul_card hf.isElemAbelian hVR hA
  rw [← card_autOn_eq_relIndex hAN] at hB24
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have hb2 : (b : MulAut ↥V) ^ 2 = 1 :=
    (isElemAbelian2_autOn' (X := A) (V := V) hA.2.1).2 (b : MulAut ↥V) b.2
  have hbne : (b : MulAut ↥V) ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨-, hrk⟩ := h4 b (hTL (hAT b.2)) hbne hb2
  have hfixb : Nat.card (fixV (Subgroup.zpowers (b : MulAut ↥V))) = 4 := by
    rw [card_eq_two_pow hW, hrk]
    norm_num
  have hfixA : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ 4 := by
    rw [← hfixb, ← card_subgroupOf_eq_card_inf, ← fixV_autOn_eq hAN]
    exact Subgroup.card_le_of_le fun v hv x hx =>
      hv x ((Subgroup.zpowers_le.2 b.2) hx)
  have hA4 : 4 ≤ Nat.card (autOn A V) := by
    have h1 := hB24.trans (Nat.mul_le_mul_left _ hfixA)
    rw [h16] at h1
    omega
  have hTp : IsPGroup 2 (autOn T V) := isPGroup_autOn hyp.sylow.1
  have hT8 : Nat.card (autOn T V) ≤ 8 := by
    obtain ⟨k, hk⟩ := hTp.exists_card_eq
    have hdvd : 2 ^ k ∣ 168 := hk ▸ hGr ▸ Subgroup.card_dvd_of_le hTL
    have hk3 : k ≤ 3 := by
      by_contra hk3
      push Not at hk3
      have : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 hk3).trans hdvd
      norm_num at this
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  have hRT : autOn R₁ V ≤ autOn T V := A4.autOn_mono hR₁T
  obtain ⟨e, heE, heL⟩ : ∃ e ∈ E, e ∉ Subgroup.centralizer (L : Set G) := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (le_inf hEV (fun x hx => h x hx) :
      E ≤ V ⊓ Subgroup.centralizer (L : Set G))
    rw [hE4, hf.card_zV] at this
    omega
  have hRne : autOn R₁ V ≠ autOn T V := by
    intro h
    have he1 : (⟨e, hEV heE⟩ : ↥V) ∈ fixV (autOn R₁ V) := by
      rw [fixV_autOn_eq hR₁N]
      exact Subgroup.mem_centralizer_iff.2 fun x hx =>
        (Subgroup.mem_centralizer_iff.1 hx.2 e heE).symm
    rw [h, hTeq, h3 _ hS1, fixV_autOn_eq hf.normalizes] at he1
    exact heL he1
  have hR4 : Nat.card (autOn R₁ V) ≤ 4 := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hRT
    have hm1 : m ≠ 1 := fun h1 => hRne (Subgroup.eq_of_le_of_card_ge hRT (by rw [hm, h1, mul_one]))
    have hm0 : m ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hm
      exact Nat.card_pos.ne' hm
    have h2 : Nat.card (autOn R₁ V) * 2 ≤ Nat.card (autOn T V) := by
      rw [hm]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  exact Subgroup.eq_of_le_of_card_ge (A4.autOn_mono hAR) (hR4.trans hA4)

omit [IsMulCommutative ↥V] in
theorem zQ_le_sup (h51 : AsB51) (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (h3' : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hV16 : Nat.card V = 2 ^ 4) (hGrs : IsSimpleGroup (autOn L V))
    (hGr : Nat.card (autOn L V) = 168)
    (hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G))
    (hTmem : ∀ t ∈ T, ∃ l ∈ T ⊓ L, l⁻¹ * t ∈ T ⊓ Subgroup.centralizer (V : Set G))
    (hJ : L = ⁅L, thompsonJ T⁆) :
    omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤
      V ⊔ omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  have := hyp.simple
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  set W := omegaOneCenterOf Q with hWdef
  have hWQ : W ≤ Q := A4.omegaOneCenterOf_le Q
  have hWC : W ≤ Subgroup.centralizer (Q : Set G) :=
    (A4.omegaOneCenterOf_le_centerOf Q).trans (A4.centerOf_le_centralizer Q)
  have hWel : IsElemAbelian 2 W := B2F.isElemAbelian_omegaOneCenterOf Q
  have hWT : W ≤ T := hWQ.trans (hQ ▸ inf_le_left)
  have hLTW : L ⊔ T ≤ Subgroup.normalizer (W : Set G) :=
    (LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf Q)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hLTW
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := hQ ▸ inf_le_right
  have hVW : V ≤ W := by
    intro v hv
    refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, hf.sq v hv⟩
    · rw [hQ]
      exact ⟨hf.le_T hv, hf.le_centralizer hv⟩
    · exact Subgroup.mem_centralizer_iff.2 fun q hq =>
        (Subgroup.mem_centralizer_iff.1 (hQV hq) v hv).symm
  have : IsMulCommutative ↥W := hWel.1
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hWel.2 w w.2)
  obtain ⟨e⟩ := h3'
  have hs3 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
    exact e.isSimpleGroup
  have h168 := card_quot_of_sl_three ⟨e⟩
  have hO2Q : pCoreOf 2 L ≤ Q :=
    F7.pCoreOf_mono_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hyp.normalizes)
  have hQW : Q ≤ Subgroup.centralizer (W : Set G) := Subgroup.le_centralizer_iff.1 hWC
  have hO2W : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) := hO2Q.trans hQW
  have hCWV : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le hVW
  have hncW : ¬ L ≤ Subgroup.centralizer (W : Set G) := fun h => hf.notCent (h.trans hCWV)
  set K := autOn L W with hKdef
  obtain ⟨eK⟩ := nonempty_autOn_mulEquiv_quotient hLW hO2W hs3 hncW
  have hKs : IsSimpleGroup K := eK.isSimpleGroup
  have hK168 : Nat.card K = 168 := by rw [Nat.card_congr eK.toEquiv, h168]
  have hKq : CFSG.IsQuasisimple ↥K :=
    isQuasisimple_autOn_of_pCoreOf_le hLW hyp.quasisimple hO2W hncW
  have hKnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hKq
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hO2K : pCoreOf 2 K = ⊥ := pCoreOf_eq_bot_of_simple hKs (not_isPGroup_of_card_eq_168 hK168)
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hQne : Q ≠ ⊥ := fun h => hyp.irrPlus.2.1 (le_bot_iff.1 (h ▸ hVW.trans hWQ))
  have hSL : SQTKGroup ↥L :=
    InternalSec.sqtkGroup_mono (InternalSec.sqtkGroup_of_localSQTK hloc hQne) le_sup_left
  have hO2Gr : pCoreOf 2 (autOn L V) = ⊥ :=
    pCoreOf_eq_bot_of_simple hGrs (not_isPGroup_of_card_eq_168 hGr)
  have hkerV := InternalSec.isPGroup_ker_of_simple hf.normalizes hs3 hO2Gr hf.notCent
  have hSQ : SQTKGroup ↥K := InternalSec.sqtkGroup_autOn hLW hSL
    (hkerV.to_le (inf_le_inf_left L hCWV))
  have hautT : ∀ g ∈ T, ∀ hg : g ∈ Subgroup.normalizer (W : Set G), conjAct W ⟨g, hg⟩ ∈ K := by
    intro g hgT hg
    obtain ⟨l, hl, hly⟩ := hTmem g hgT
    have hlyQ : l⁻¹ * g ∈ Q := hQ ▸ hly
    refine Subgroup.mem_map.2 ⟨⟨l, hLW hl.2⟩, Subgroup.mem_subgroupOf.2 hl.2, ?_⟩
    ext w
    simp only [A5Mod.conjAct_apply_coe]
    have h1 := Subgroup.mem_centralizer_iff.1 (hQW hlyQ) (w : G) w.2
    calc (l : G) * w * l⁻¹ = l * ((l⁻¹ * g) * w * (l⁻¹ * g)⁻¹) * l⁻¹ := by
          rw [show (l⁻¹ * g) * (w : G) * (l⁻¹ * g)⁻¹ = w by rw [← h1]; group]
      _ = g * w * g⁻¹ := by group
  obtain ⟨B, hB, hBV⟩ : ∃ B : Subgroup G, IsMaxElemAbelian T B ∧
      ¬ B ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hall
    push Not at hall
    have hJV : thompsonJ T ≤ Subgroup.centralizer (V : Set G) := iSup₂_le fun B hB => hall B hB
    apply hf.notCent
    rw [hJ, Subgroup.commutator_le]
    intro l hl j hj
    have hjN : j ∈ Subgroup.normalizer (V : Set G) :=
      hf.T_le ((iSup₂_le fun B (hB : IsMaxElemAbelian T B) => hB.1 : thompsonJ T ≤ T) hj)
    have hj1 : conjAct V ⟨j, hjN⟩ = 1 := A4.conjAct_eq_one_iff.2 (hJV hj)
    have h1 : conjAct V ⁅(⟨l, hf.normalizes hl⟩ : Subgroup.normalizer (V : Set G)),
        ⟨j, hjN⟩⁆ = 1 := by
      rw [map_commutatorElement, hj1, commutatorElement_one_right]
    exact A4.conjAct_eq_one_iff.1 h1
  have hBT : B ≤ T := hB.1
  have hBN : B ≤ Subgroup.normalizer (W : Set G) := hBT.trans (le_sup_right.trans hLTW)
  have hBK : autOn B W ≤ K := by
    rintro _ ⟨g, hg, rfl⟩
    exact hautT g (hBT (Subgroup.mem_subgroupOf.1 hg)) g.2
  have hB1 : autOn B W ≠ ⊥ := by
    intro h
    apply hBV
    intro b hb
    have h1 : conjAct W ⟨b, hBN hb⟩ ∈ autOn B W :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hb)
    rw [h, Subgroup.mem_bot] at h1
    exact hCWV (A4.conjAct_eq_one_iff.1 h1)
  have hA2 : IsA2 K (autOn B W) := ⟨hBK, hB1, isElemAbelian2_autOn' hB.2.1⟩
  have hr : Nat.card ↥W ≤ Nat.card (autOn B W) * Nat.card (fixV (autOn B W)) := by
    have h1 := card_le_relIndex_mul_card hWel hWT hB
    rwa [← card_autOn_eq_relIndex hBN, ← card_subgroupOf_eq_card_inf,
      ← fixV_autOn_eq hBN] at h1
  obtain ⟨A, hAB, hA, -⟩ := B1_4_4_le hW2 hA2 ((rAV_le_one_iff hW2 hA2).2 hr)
  have hKA : ⁅K, A⁆ = K := commutator_eq_of_simple hKs hKnab (hAB.trans hBK) hA.2.1
  have hb51 := (InternalSec.b51Hyp_ffJ_autOn hLW le_rfl Subgroup.le_normalizer
    (fun y hy => ⟨0, by rw [pow_zero, pow_one]; exact (le_sup_left :
      L ≤ L ⊔ Subgroup.centralizer (W : Set G)) hy⟩) hO2K hKq hSQ hA hKA).1
  have hconc := h51 ↥W hW2 (ffJ K) K hb51
  have hJK : ffJ K = K := le_antisymm (B6.ffJ_le K) hb51.2.2.2.1
  set U := commV K with hUdef
  have hFix : fixV K = (Subgroup.centralizer (L : Set G)).subgroupOf W := fixV_autOn_eq hLW
  have hUmap : U.map W.subtype = ⁅W, L⁆ := map_commV_autOn hLW
  have hVU : V.subgroupOf W ≤ U := by
    intro v hv
    have h1 : (v : G) ∈ U.map W.subtype := by
      rw [hUmap]
      have h2 : (v : G) ∈ V := hv
      rw [← hf.commutator] at h2
      exact Subgroup.commutator_mono hVW le_rfl h2
    obtain ⟨u, hu, hue⟩ := h1
    rwa [show u = v from Subtype.ext hue] at hu
  have hzW : z ∈ W := hVW hf.mem_zV.1
  have hzF : (⟨z, hzW⟩ : ↥W) ∈ fixV K := by
    rw [hFix]
    exact hf.mem_zV.2
  have hzU : (⟨z, hzW⟩ : ↥W) ∈ U := hVU hf.mem_zV.1
  have hz1 : (⟨z, hzW⟩ : ↥W) ≠ 1 := fun h => hf.ne_one (congrArg Subtype.val h)
  have hnotDir : ¬ IsIntDirect U (fixV K) ⊤ := fun h => by
    have h1 : (⟨z, hzW⟩ : ↥W) ∈ U ⊓ fixV K := ⟨hzU, hzF⟩
    rw [h.2, Subgroup.mem_bot] at h1
    exact hz1 h1
  obtain ⟨-, -, -, hirrSec⟩ := (hconc.2.1.2 hnotDir).1
  have hUle : U ≤ V.subgroupOf W ⊔ fixV K := by
    set F := XMod.fixed (↥K) U with hFdef
    have hFK : F ≤ fixV K := fun f hf' a ha => hf'.2 ⟨a, ha⟩
    have hJinv : XMod.IsInv (↥K) (V.subgroupOf W ⊔ F) := by
      intro a x hx
      have hle : (V.subgroupOf W ⊔ F) ≤ (V.subgroupOf W ⊔ F).comap
          ((a : MulAut ↥W) : ↥W →* ↥W) := by
        refine sup_le (fun v hv => ?_) (fun f hf' => ?_)
        · obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.1 a.2
          rw [Subgroup.mem_subgroupOf] at hg
          refine Subgroup.mem_comap.2 (le_sup_left (a := V.subgroupOf W) ?_)
          rw [Subgroup.mem_subgroupOf]
          show (((a : MulAut ↥W) v : ↥W) : G) ∈ V
          rw [← hga, A5Mod.conjAct_apply_coe]
          exact (Subgroup.mem_normalizer_iff.1 (hf.normalizes hg) v).1 hv
        · refine Subgroup.mem_comap.2 (le_sup_right (b := F) ?_)
          show (a : MulAut ↥W) f ∈ F
          have h1 : (a : MulAut ↥W) f = f := hf'.2 a
          rw [h1]
          exact hf'
      exact hle hx
    rcases hirrSec.2 _ hJinv le_sup_right (sup_le hVU hirrSec.1.le) with h | h
    · exfalso
      obtain ⟨v, hvV, hvL⟩ : ∃ v ∈ V, v ∉ Subgroup.centralizer (L : Set G) := by
        by_contra hall
        push Not at hall
        apply hf.notCent
        intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact (Subgroup.mem_centralizer_iff.1 (hall w hw) l hl).symm
      have h1 : (⟨v, hVW hvV⟩ : ↥W) ∈ F := h ▸ le_sup_left (a := V.subgroupOf W) hvV
      have h2 := hFK h1
      rw [hFix] at h2
      exact hvL h2
    · exact (le_of_eq h.symm).trans (sup_le_sup_left hFK _)
  set ZU := fixV K ⊓ U with hZU
  have hUeq : U = V.subgroupOf W ⊔ ZU := by
    refine le_antisymm (fun u hu => ?_) (sup_le hVU inf_le_right)
    obtain ⟨v, hv, f, hfK, rfl⟩ := Subgroup.mem_sup.1 (hUle hu)
    have hfU : f ∈ U := by
      have := U.mul_mem (U.inv_mem (hVU hv)) hu
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem_sup hv ⟨hfK, hfU⟩
  have hVZ : V.subgroupOf W ⊓ ZU = (V ⊓ Subgroup.centralizer (L : Set G)).subgroupOf W := by
    ext w
    simp only [hZU, hFix, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hVU h.1⟩⟩
  have hcardU : Nat.card U * 2 = 16 * Nat.card ZU := by
    have h1 := G64.card_sup_mul_card_inf (V.subgroupOf W) ZU
    rw [← hUeq, hVZ, card_subgroupOf_eq_card_inf, inf_eq_right.2 (inf_le_left.trans hVW),
      hf.card_zV, card_subgroupOf_eq_card_inf, inf_eq_right.2 hVW, hV16] at h1
    rw [h1]
    norm_num
  have hZUne : ZU ≠ ⊥ := fun h => by
    have h1 : (⟨z, hzW⟩ : ↥W) ∈ ZU := ⟨hzF, hzU⟩
    rw [h, Subgroup.mem_bot] at h1
    exact hz1 h1
  have hZUpos : 0 < Nat.card ZU := Nat.card_pos
  have hTop : (⊤ : Subgroup ↥W) ≤ V.subgroupOf W ⊔ fixV K := by
    rcases hconc.2.2.2.2.1 with h | ⟨-, hlist, himp⟩
    · rw [hJK] at h
      rw [← h]
      exact sup_le hUle le_sup_right
    · exfalso
      rcases hlist with ⟨n, F, _, _, hF, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | hnat'
      · have h1 := G64.RealizesVia.card_eq hπ
        rw [← hUdef, ← hZU, card_mod_nat, hF] at h1
        have h2 : (2 ^ n) ^ Fintype.card (Fin 2 ⊕ Fin 2) * 2 = 16 := by
          have := hcardU
          rw [h1] at this
          have h3 : (2 ^ n) ^ Fintype.card (Fin 2 ⊕ Fin 2) * 2 * Nat.card ZU =
              16 * Nat.card ZU := by rw [← this]; ring
          exact Nat.eq_of_mul_eq_mul_right hZUpos h3
        simp only [Fintype.card_sum, Fintype.card_fin, ← pow_mul] at h2
        have h3 : (2 : ℕ) ^ (n * (2 + 2)) * 2 = 2 ^ 4 := by rw [h2]; norm_num
        rw [← pow_succ] at h3
        have := Nat.pow_right_injective (le_refl 2) h3
        omega
      · have h1 := G64.RealizesVia.card_eq hπ
        rw [← hUdef, ← hZU, card_mod_altDn (by decide) (by norm_num)] at h1
        norm_num at h1
        rw [h1] at hcardU
        omega
      · have h1 := G64.RealizesVia.card_eq hπ
        rw [← hUdef, ← hZU, card_mod_altDn (by decide) (by norm_num)] at h1
        norm_num at h1
        rw [h1] at hcardU
        omega
      · exact hZUne (himp hnat')
  intro w hw
  have h1 := hTop (Subgroup.mem_top (⟨w, hw⟩ : ↥W))
  obtain ⟨v, hv, f, hfK, hvf⟩ := Subgroup.mem_sup.1 h1
  have hf' : (f : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [hFix] at hfK
    exact hfK
  have hwe : w = (v : G) * f := (congrArg Subtype.val hvf).symm
  rw [hwe]
  exact Subgroup.mul_mem_sup hv ⟨f.2, hf'⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem omegaOneCenter_pCore_facts (hf : CxFacts G T L V z)
    (hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G)) :
    omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤ T ∧
      IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 (L ⊔ T))) ∧
      V ≤ omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ∧
      quasithinOmegaOneCenter T ≤ omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) := by
  have hWQ := A4.omegaOneCenterOf_le (pCoreOf 2 (L ⊔ T))
  have hQV : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := hQ ▸ inf_le_right
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := hQ ▸ inf_le_left
  refine ⟨hWQ.trans hQT, B2F.isElemAbelian_omegaOneCenterOf _, fun v hv => ?_, ?_⟩
  · refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, hf.sq v hv⟩
    · rw [hQ]
      exact ⟨hf.le_T hv, hf.le_centralizer hv⟩
    · exact Subgroup.mem_centralizer_iff.2 fun q hq =>
        (Subgroup.mem_centralizer_iff.1 (hQV hq) v hv).symm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨⟨hxT, hxC⟩, hx2⟩
    refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, hx2⟩
    · rw [hQ]
      exact ⟨hxT, Subgroup.centralizer_le hf.le_T hxC⟩
    · exact Subgroup.centralizer_le hQT hxC

end L3

theorem lemma12_4_5_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9) (h51 : AsB51) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∀ E : Subgroup G, E ≤ V → Nat.card E = 4 → T ≤ Subgroup.normalizer (E : Set G) →
        ⁅quasithinOmegaOneCenter T, L⁆ = ⊥ ∧
        omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) = quasithinOmegaOneCenter T ⊔ V ∧
        ∀ A : Subgroup G, IsMaxElemAbelian (T ⊓ Subgroup.centralizer (E : Set G)) A →
          ¬ A ≤ pCoreOf 2 (L ⊔ T) → autOn A V = autOn (T ⊓ Subgroup.centralizer (E : Set G)) V := by
  intro G _ _ T L V hcx h3' E hEV hE4 _hTE
  classical
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hcx (Or.inl h3')
  have := hf.comm
  obtain ⟨hV16, hGrs, hGr, hnat⟩ := cx_l3_module h1222 hcx hf h3'
  have hQ := pCoreOf_sup_eq_of_hyp1223 h1222 h3228 hyp
  obtain ⟨-, hTeq⟩ := cx_autOn_T_eq hcx hf hnat
  have hTmem : ∀ t ∈ T, ∃ l ∈ T ⊓ L, l⁻¹ * t ∈ T ⊓ Subgroup.centralizer (V : Set G) :=
    fun t ht => cx_mem_mul_of_mem_T hf hTeq ht
  have hJ : L = ⁅L, thompsonJ T⁆ :=
    lemma12_4_3_two_of h1229 (lemma12_4_3_one_of_pre hpre) G T L V hcx
  have hZQ := zQ_le_sup h51 hcx hf h3' hV16 hGrs hGr hQ hTmem hJ
  obtain ⟨hWT, hWel, hVW, hZW⟩ := omegaOneCenter_pCore_facts hf hQ
  have hQW : pCoreOf 2 (L ⊔ T) ≤
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) : Set G) :=
    Subgroup.le_centralizer_iff.1 ((A4.omegaOneCenterOf_le_centerOf _).trans
      (A4.centerOf_le_centralizer _))
  have hWZ : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.centralizer (L : Set G) ≤
      quasithinOmegaOneCenter T := by
    intro x hx
    refine Subgroup.subset_closure ⟨⟨hWT hx.1, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩,
      hWel.2 x hx.1⟩
    obtain ⟨l, hl, hly⟩ := hTmem t ht
    have hlyQ : l⁻¹ * t ∈ pCoreOf 2 (L ⊔ T) := hQ ▸ hly
    have h1 := Subgroup.mem_centralizer_iff.1 (hQW hlyQ) x hx.1
    have h2 := Subgroup.mem_centralizer_iff.1 hx.2 l hl.2
    calc t * x = l * ((l⁻¹ * t) * x) := by group
      _ = l * (x * (l⁻¹ * t)) := by rw [← h1]
      _ = (l * x) * (l⁻¹ * t) := by group
      _ = (x * l) * (l⁻¹ * t) := by rw [h2]
      _ = x * t := by group
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    ((Subgroup.closure_le _).mpr fun _ hz => hz.1).trans inf_le_right
  refine ⟨?_, ?_, fun A hA hAQ => lemma12_4_5_three hcx hf hV16 hGr hnat hEV hE4 hA (hQ ▸ hAQ)⟩
  ·
    have := hWel.1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    have hxW := hZQ (hZW hx)
    have hVN : V ≤ Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓
        Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (mul_comm' (⟨y, hy.1⟩ : ↥(omegaOneCenterOf (pCoreOf 2 (L ⊔ T))))
        ⟨v, hVW hv⟩)
    have hxmem : x ∈ (V : Set G) * ((omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓
        Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN]
      exact hxW
    obtain ⟨v, hv, c, hc, rfl⟩ := hxmem
    have hcT : c ∈ Subgroup.centralizer (T : Set G) := hZT (hWZ hc)
    have hvT : v ∈ Subgroup.centralizer (T : Set G) := by
      have h1 := (Subgroup.centralizer (T : Set G)).mul_mem (hZT hx)
        ((Subgroup.centralizer (T : Set G)).inv_mem hcT)
      rwa [mul_inv_cancel_right] at h1
    exact Subgroup.mul_mem _ (cx_inf_centralizer_T_le hcx hf hV16 hnat ⟨hv, hvT⟩) hc.2
  ·
    refine le_antisymm (hZQ.trans ?_) (sup_le hZW hVW)
    rw [sup_comm]
    exact sup_le_sup_right hWZ V

end CFSG.Quasithin.H13
