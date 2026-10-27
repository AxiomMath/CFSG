module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5j
public import CFSG.Quasithin.Vol2.Ch12Sec7L5k
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Aut
public import CFSG.Quasithin.Vol2.Ch12Sec7L5i

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S127

namespace S127.L5

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t : G}

theorem D127.inf_centerOf_le (d : D127 G T L V t) {K : Subgroup G} (hLK : Lt L t ≤ K) :
    V ⊓ centerOf K ≤ Vt L t :=
  (le_inf inf_le_left (inf_le_right.trans (inf_le_right.trans
    (Subgroup.centralizer_le hLK)))).trans d.inf_centralizer_le

theorem D127.centerOf_eq
    (d : D127 G T L V t)
    (hL34 : L34CoverFact) (hV2 : ∀ v ∈ V, v ^ 2 = 1) {K : Subgroup G}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hZ : IsPGroup 2 ↥(Subgroup.center ↥K))
    (hpsl : IsPSL 3 2 2 (↥K ⧸ Subgroup.center ↥K)) (hLK : Lt L t ≤ K)
    (hVt : Vt L t ≤ centerOf K) : centerOf K = Vt L t := by
  have hVK : V ≤ K := d.v_le_lt.trans hLK
  have hVZ : V ⊓ centerOf K = Vt L t := le_antisymm (d.inf_centerOf_le hLK) (le_inf d.vt_le hVt)
  set E : Subgroup ↥K := V.subgroupOf K with hE
  have hEc : Nat.card ↥E = Nat.card ↥V := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hEZ : (E ⊓ Subgroup.center ↥K).map K.subtype = Vt L t := by
    rw [Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hE, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hVK, map_center_eq_centerOf, hVZ]
  have hEZc : Nat.card ↥(E ⊓ Subgroup.center ↥K) = 4 := by
    rw [← d.card_Vt, ← hEZ, Subgroup.card_map_of_injective K.subtype_injective]
  have hZ2 := hL34 ↥K hKq hZ hpsl E
    (fun a ha b hb => Subtype.ext (d.comm _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb)))
    (fun a ha => Subtype.ext (by simpa using hV2 _ (Subgroup.mem_subgroupOf.mp ha)))
    (by rw [hEc, hEZc, d.card_V]; norm_num)
  have hdvd := card_center_dvd_four hKq hZ hpsl hZ2
  refine (Subgroup.eq_of_le_of_card_ge hVt ?_).symm
  rw [← card_center_eq, d.card_Vt]
  exact Nat.le_of_dvd (by norm_num) hdvd

end S127.L5

open S127.L5 in
theorem lemma12_7_5K31_of
    (h71 : Setup1271) (h74 : Lemma12_7_4) (hSp4 : SchurMult2Sp4) (hG24 : SchurMult2G24)
    (hD4 : SchurMult2D4) (hM22 : SchurMult2M22) (hL34 : L34CoverFact) : Lemma12_7_5K31 := by
  intro G _ _ T L V t h ht h18 _ K hK h31
  have d := d127_of h71 h74 h ht h18
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := (h71 G T L V h).1.2
  have hKq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hLK : Lt L t ≤ K := by
    have h1 := h31.2.2.1
    rwa [← h31.1] at h1
  have htZ : t ∈ centerOf K := mem_centerOf hK.1 (hLK (d.v_le_lt d.mem))
  obtain ⟨hpsl, hVt⟩ := d.c31_analysis hSp4 hG24 hD4 hM22 hV2 hKq htZ h31
  have hZ := isPGroup_center h31.2.2.2.2.1
  have h3 : 2 ≤ CFSG.pRank 3 (↥K ⧸ Subgroup.center ↥K) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact QA12.two_le_pRank_psl34 hpsl
  have hN := le_normalizer_of_isComponentOf (d.pRank_le_two (hV2 t ht)) hK hZ h3
  have hKt := d.conjClosure_eq hK hN hLK
  have hZeq := d.centerOf_eq hL34 hV2 hKq hZ hpsl hLK hVt
  change IsComponentOf (conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G)))
      (Subgroup.centralizer ({t} : Set G)) ∧
    (Subgroup.center ↥(conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G)))).map
      (conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G))).subtype = Vt L t ∧
    IsPSL 3 2 2 (↥(conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G))) ⧸
      Subgroup.center ↥(conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G))))
  rw [hKt]
  exact ⟨hK, (map_center_eq_centerOf K).trans hZeq, hpsl⟩

end CFSG.Quasithin.H13
