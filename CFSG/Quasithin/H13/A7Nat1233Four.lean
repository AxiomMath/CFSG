module

public import CFSG.Quasithin.H13.A7Nat1233FourInputs
public import CFSG.Quasithin.Background.C2Twelve
public import CFSG.Quasithin.H13.A7NatG10

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inf_center_ne_bot_two {P U : Subgroup G} (hP : IsPGroup 2 P) (hUP : U ≤ P)
    (hUn : P ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (P ⊓ centralizer (P : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (U.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf P ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  apply hy1
  have hmem : (y : G) ∈ U ⊓ (P ⊓ centralizer (P : Set G)) :=
    ⟨hy.1, y.2, hyC⟩
  rw [h, mem_bot] at hmem
  exact Subtype.ext (Subtype.ext hmem)

theorem a7FourExcluded_of_inputs
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1225 : Stmt12_2_5) (h12212 : Stmt12_2_12) (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G)
    (hMod : Insp1233Mod) (hInsK : Insp1233K) : A7FourExcluded := by
  intro G _ _ T L V hyp hA7 ⟨hcard, φ, hφs, hφk⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.simple
  have hS : Setting1233Four hyp := ⟨hA7, hcard, φ, hφs, hφk⟩
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hV1 : V ≠ ⊥ := fun h => by
    rw [h, card_bot] at hcard
    norm_num at hcard
  have hVZ := inf_center_ne_bot_two hyp.sylow.1 hVT hTV hV1
  set W := V ⊓ (T ⊓ centralizer (T : Set G)) with hWdef
  have hW2 : IsPGroup 2 W := hyp.sylow.1.to_le (inf_le_right.trans inf_le_left)
  have hWnt : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hVZ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hW2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.2 hWnt).ne' hn
  obtain ⟨⟨z, hzW⟩, hz2⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  rw [Subgroup.orderOf_mk] at hz2
  have hzV : z ∈ V := hzW.1
  have hz1 : z ≠ 1 := fun h1 => by simp [h1] at hz2
  have hzZ : z ∈ quasithinOmegaOneCenter T :=
    subset_closure ⟨hzW.2, by rw [← hz2]; exact pow_orderOf_eq_one z⟩
  obtain ⟨htrans, hO2, hperf, hVL, hKzF⟩ := hMod G T L V hyp hS z hzV hz1 hzZ
  have hcardL := card_eq_of_quot_center_alternating_seven hA7
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hyp.quasisimple
  have hcpos : 0 < Nat.card (center (↥L ⧸ CFSG.pCore 2 ↥L)) := Nat.card_pos
  have hGz : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
    rcases h12213 G T L V hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hyp.notAlt hyp.maximal
        hyp.faithful hyp.quasisimple hyp.normalizes hyp.irrPlus with
      ⟨v, hv, hv1, hvM⟩ | ⟨m, hm, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · intro hz
      apply hvM
      obtain ⟨l, hl, rfl⟩ := htrans v hv hv1
      exact centralizer_le_of_conj (le_normalizer hl) rfl hz
    · exfalso
      have hc := Nat.card_congr e.toEquiv
      rcases hm with rfl | rfl
      · rw [hcardL, nat_card_SL_three_zmod_two] at hc
        omega
      · rw [hcardL, nat_card_SL_four_zmod_two] at hc
        have h8 : Nat.card (center (↥L ⧸ CFSG.pCore 2 ↥L)) = 8 := by omega
        rw [h8] at hodd
        exact absurd hodd (by decide)
    · exfalso
      have hc := Nat.card_congr e.toEquiv
      rw [hcardL, nat_card_SL_three_zmod_two] at hc
      omega
    · exfalso
      have hc := Nat.card_congr e.toEquiv
      rw [hcardL, nat_card_SL_four_zmod_two] at hc
      have h8 : Nat.card (center (↥L ⧸ CFSG.pCore 2 ↥L)) = 8 := by omega
      rw [h8] at hodd
      exact absurd hodd (by decide)
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTz : T ≤ hyp.Gv z := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hzZ) t ht))
  have hTv : hyp.Tv z = T := inf_eq_left.2 hTz
  have hsylMz : QuasithinUnique.IsSylowTwoOf (hyp.Tv z) (hyp.Mv z) := by
    rw [hTv]
    exact isSylowTwoOf_of_le hyp.sylow (le_inf hyp.normalizes hTz)
  obtain ⟨-, hC28⟩ := h12212 G T L V hyp z hzV hz1 hsylMz hO2
  have hC28' := hC28 hperf hVL
  have hTK : T ≤ normalizer (Kv hyp z : Set G) := T_le_normalizer_Kv hyp h1225 hzV hz1 hzZ
  have hLocal : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hH2 : pCoreOf 2 (hyp.Gv z) ≠ ⊥ :=
    pCoreOf_ne_bot_of_le_centralizer hz2 (mem_centralizer_singleton_iff.2 rfl) le_rfl
  have hSylH : QuasithinUnique.IsSylowTwoOf T (hyp.Gv z) := isSylowTwoOf_of_le hyp.sylow hTz
  have hKzH : Kv hyp z ≤ hyp.Gv z := Kv_le_centralizer hyp z
  have hKzF' : Kv hyp z ∈ lFamily T := hKzF.1.2.1
  obtain ⟨K, ⟨hK, hKzK⟩, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_4_existsUnique hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved h39 hH2 hSylH hKzH hKzF'
  have hKn := QuasithinUnique.Vol2Native.lemma_1_2_4_normal hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds hH2 hSylH hKzF' hKzK hK
    hTK
  have hKz := hInsK G T L V hyp hS z hzV hz1 hzZ hC28' K hK hKzK
  obtain ⟨-, hMzN, -, -, -⟩ := h1225 G T L V hyp z hzV hz1
  have hMzK : hyp.Mv z ≤ normalizer (Kv hyp z : Set G) :=
    hMzN.trans (normalizer_le_normalizer_perfectCore _)
  have hM0 : conjClosure (Kv hyp z) (hyp.Mv z) = Kv hyp z :=
    le_antisymm (conjClosure_le fun m hm k hk => (mem_normalizer_iff.1 (hMzK hm) k).1 hk)
      (le_conjClosure _ _)
  have hKH : K ≤ hyp.Gv z := le_of_mem_cComp hK
  have hGzN : hyp.Gv z ≤ normalizer (conjClosure (Kv hyp z) (hyp.Mv z) : Set G) := by
    rw [hM0, hKz]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).1 hKn
  exact hGz ((C2Twelve.le_of_le_normalizer (hC129 G) (hC111 G) (hC19 G) hC28' hGzN).trans
    inf_le_left)

theorem stmtA7NaturalModuleConfig_of_named_inputs
    (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1)
    (h1225 : Stmt12_2_5) (h12212 : Stmt12_2_12) (h12213 : Stmt12_2_13)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC111 : ∀ (G : Type) [Group G] [Finite G], ASC111Statement G)
    (hC19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G) (hF : A318Facts)
    (hI16 : AsI16AltSevenCover) (hMod : Insp1233Mod) (hInsK : Insp1233K) (hI1 : Insp1236)
    (hI2 : InspSL2NoA6) (hgap : Gap1237KeJ) (hNQ : Insp1238NonQ) (hIQ : Insp1238Q)
    (hIY : Insp1238Y) : StmtA7NaturalModuleConfig :=
  stmtA7NaturalModuleConfig_of_inputs h1222 h331 h1225 h12212 h39 hC27 hC129 hF hI16
    (a7FourExcluded_of_inputs h1222 h12213 h1225 h12212 h39 hC129 hC111 hC19 hMod hInsK) hI1 hI2
    hgap hNQ hIQ hIY

end CFSG.Quasithin.H13.A7
