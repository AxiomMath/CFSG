module

public import CFSG.Quasithin.Vol2.Ch12Sec6L14c
public import CFSG.Quasithin.Vol2.Ch12Sec6L12b
public import CFSG.Quasithin.Vol2.Ch12Sec6L14a
public import CFSG.Quasithin.Vol2.KGFact12614

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem Tv_le_normalizer_Lv (hH : Hyp126 G T L V) (v : G) :
    Tv T v ≤ Subgroup.normalizer (Lv L v : Set G) := fun _t ht =>
  normalizer_le_normalizer_perfectCore _ (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hH.hyp.normalizes ht.1, Subgroup.le_normalizer ht.2⟩)

theorem centralizerSection_ne_bot (hD2 : Lemma12_6_4_5) (hD3 : Lemma12_6_6_9)
    (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hJ : thompsonJ (Tv T v) ≤ Qv T V) :
    centralizerSection (autOn S (Usec Kv S)) (autOn (Lv L v) (Usec Kv S))
      (pCoreOf 2 (autOn (Lv L v) (Usec Kv S))) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hST, hRR, hJ1, -, hNJ⟩ := (hD3 G T L V F v Kv S hC).2.2.2.1 hJ
  have hKM := (hD5 G T L V F v Kv S hC).2
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  obtain ⟨-, -, -, -, -, hOR, -, -, hReq⟩ := hD2 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  set R := Rsec L Kv S v with hR
  have hXU : Kv ⊔ S ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_Usec Kv S)
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := (le_sup_right : S ≤ Kv ⊔ S).trans hXU
  have hRS : R ≤ S := by rw [hReq]; exact centralizerSection_le_left _ _ _
  have hRU : ¬ R ≤ Subgroup.centralizer (U : Set G) := by
    intro hRC
    have hRP : R = pCoreOf 2 (Kv ⊔ S) := by
      refine le_antisymm ?_ hOR
      rw [hO]
      exact le_inf (hRS.trans le_sup_right) hRC
    apply hKM
    intro k hk
    apply hNJ
    have hJR : thompsonJ S = thompsonJ R := by rw [hST, hJ1, hRR]
    rw [hJR]
    refine normalizer_le_normalizer_thompsonJ R ?_
    rw [hRP]
    exact le_normalizer_pCoreOf 2 _ ((le_sup_left : Kv ≤ Kv ⊔ S) hk)
  obtain ⟨r, hrR, hrU⟩ := Set.not_subset.1 hRU
  have hrN : r ∈ Subgroup.normalizer (U : Set G) := hSU (hRS hrR)
  have hrc : r ∈ centralizerSection S (Lv L v) (pCoreOf 2 (Lv L v)) := hReq ▸ hrR
  obtain ⟨-, hrL, -, hrcomm⟩ := hrc
  set ρr := conjAct U ⟨r, hrN⟩ with hρr
  have hρr1 : ρr ≠ 1 := by
    intro h
    apply hrU
    have h1 := (QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (U : Set G))
      le_rfl ⟨r, hrN⟩).1 h
    exact h1
  intro hbot
  apply hρr1
  have hmem : ρr ∈ centralizerSection (autOn S U) (autOn (Lv L v) U)
      (pCoreOf 2 (autOn (Lv L v) U)) := by
    have hρS : ρr ∈ autOn S U := QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨r, hrN⟩, hRS hrR, rfl⟩
    have hρZ : ρr ∈ autOn (Subgroup.zpowers r) U :=
      QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨r, hrN⟩, Subgroup.mem_zpowers r, rfl⟩
    have hρN : ρr ∈ Subgroup.normalizer (autOn (Lv L v) U : Set (MulAut ↥U)) :=
      autOn_le_normalizer ((Subgroup.zpowers_le).2 hrL) hρZ
    refine ⟨hρS, hρN, normalizer_le_normalizer_pCoreOf 2 _ hρN, fun b hb => ?_⟩
    obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hb
    have hlr := hrcomm l hlL
    have hc : l * r * l⁻¹ * r⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hrN)
        (Subgroup.inv_mem _ hlN)) (Subgroup.inv_mem _ hrN)
    have he : conjAct U ⟨l, hlN⟩ * ρr * (conjAct U ⟨l, hlN⟩)⁻¹ * ρr⁻¹ =
        conjAct U ⟨l * r * l⁻¹ * r⁻¹, hc⟩ := by
      rw [hρr, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [he]
    have hOL : pCoreOf 2 (Lv L v) ≤ Lv L v := pCoreOf_le 2 _
    have hO2 : autOn (pCoreOf 2 (Lv L v)) U ≤ pCoreOf 2 (autOn (Lv L v) U) := by
      refine le_pCoreOf_of_le_normalizer 2 (InternalSec.autOn_le_autOn_of_le hOL)
        (autOn_le_normalizer (le_normalizer_pCoreOf 2 _)) ?_
      have hOU : pCoreOf 2 (Lv L v) ≤ Subgroup.normalizer (U : Set G) :=
        hOL.trans (hC.lv_le.trans (Kv_le_normalizer_Usec hC))
      have h1 : IsPGroup 2 ↥((pCoreOf 2 (Lv L v)).subgroupOf (Subgroup.normalizer (U : Set G))) :=
        (pCoreOf_isPGroup 2 _).of_equiv (Subgroup.subgroupOfEquivOfLe hOU).symm
      exact h1.map (conjAct U)
    exact hO2 (QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨_, hc⟩, hlr, rfl⟩)
  rw [hbot] at hmem
  exact hmem

theorem autOn_Lv_lt (hD3 : Lemma12_6_6_9) (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hJ : thompsonJ (Tv T v) ≤ Qv T V) :
    autOn (Lv L v) (Usec Kv S) < autOn Kv (Usec Kv S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hST, -, -, -, -⟩ := (hD3 G T L V F v Kv S hC).2.2.2.1 hJ
  have hKM := (hD5 G T L V F v Kv S hC).2
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  refine lt_of_le_of_ne (InternalSec.autOn_le_autOn_of_le hC.lv_le) fun heq => hKM ?_
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (Usec Kv S : Set G) := Kv_le_normalizer_Usec hC hk
  have hkA : conjAct (Usec Kv S) ⟨k, hkN⟩ ∈ autOn (Lv L v) (Usec Kv S) := by
    rw [heq]
    exact QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, hk, rfl⟩
  obtain ⟨⟨l, hlN⟩, hlL, hlk⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hkA
  have hc : ((⟨l, hlN⟩⁻¹ * ⟨k, hkN⟩ : ↥(Subgroup.normalizer (Usec Kv S : Set G))) : G) ∈
      Subgroup.centralizer (Usec Kv S : Set G) := by
    rw [← QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (Usec Kv S : Set G))
      le_rfl]
    show conjAct (Usec Kv S) (⟨l, hlN⟩⁻¹ * ⟨k, hkN⟩) = 1
    rw [map_mul, map_inv, hlk, inv_mul_cancel]
  have hlK : l ∈ Kv := hC.lv_le hlL
  have hcO : l⁻¹ * k ∈ pCoreOf 2 (Kv ⊔ S) := by
    rw [hO]
    exact ⟨(Kv ⊔ S).mul_mem ((Kv ⊔ S).inv_mem ((le_sup_left : Kv ≤ Kv ⊔ S) hlK))
      ((le_sup_left : Kv ≤ Kv ⊔ S) hk), hc⟩
  have hcT : l⁻¹ * k ∈ T := by
    have := (pCoreOf_KvS_le hC) hcO
    rw [hST] at this
    exact this.1
  have e : k = l * (l⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer (Lv_le_L L v hlL))
    (hC.hyp.hyp.normalizes hcT)

end S126T2

theorem lemma12_6_14_of (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hD2 : Lemma12_6_4_5) (hD3 : Lemma12_6_6_9) (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13)
    (hK1 : FactKv12614) (hK2 : FactM22M23NoFF) : Lemma12_6_14 := by
  intro G _ _ T L V _ F v Kv S hC hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hyp := hH.hyp
  obtain ⟨hST, -, -, -, -⟩ := (hD3 G T L V F v Kv S hC).2.2.2.1 hJ
  set U := Usec Kv S with hU
  set X := Kv ⊔ S with hX
  have hUe := S126T2.isElemAbelian_Usec Kv S
  have : IsMulCommutative ↥U := hUe.1
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (S126T2.normalizer_le_normalizer_Usec Kv S)
  have hKvU : Kv ≤ Subgroup.normalizer (U : Set G) := S126T2.Kv_le_normalizer_Usec hC
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := (le_sup_right : S ≤ X).trans hXU
  have hLvU : S126T2.Lv L v ≤ Subgroup.normalizer (U : Set G) := hC.lv_le.trans hKvU
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hKS : X ≤ S126T2.Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hSX : CFSG.QuasithinUnique.IsSylowTwoOf S X :=
    A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS
  have hred := S126T2.isTwoReducedIn_Usec hD7 hC
  have hO2 : pCoreOf 2 (autOn X U) = ⊥ := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hSLv : S ≤ Subgroup.normalizer (S126T2.Lv L v : Set G) := by
    rw [hST]
    exact S126T2.Tv_le_normalizer_Lv hH v
  have hiso := hK1 (MulAut ↥U) (autOn X U) (autOn Kv U) (autOn S U) (autOn (S126T2.Lv L v) U)
    (InternalSec.autOn_le_autOn_of_le le_sup_left)
    (S126T2.autOn_le_normalizer (sup_le Subgroup.le_normalizer hSK))
    ((MulEquiv.isSimpleGroup_congr (S126T2.autOn_Kv_equiv hD7 hC)).1
      (S126T2.isSimple_Kv h1222 h36 hC))
    (CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv (S126T2.autOn_Kv_equiv hD7 hC).symm
      (S126T2.a23List_Kv h1222 h36 hC))
    (S126T2.isSQTKCat_autOn_Kv h1222 hD7 hC)
    (QuasithinUnique.Setup.isSylowTwoOf_autOn hSX hXU)
    (S126T2.autOn_sup_eq hKvU hSU) hO2 (S126T2.autOn_Lv_lt hD3 hD5 hD7 hC hJ)
    (S126T2.autOn_le_normalizer hSLv)
    (S126T2.autOn_perfect hLvU (perfectCore_perfect _))
    (S126T2.o2Iso_autOn_Lv h1222 hD7 hC)
    (S126T2.centralizerSection_ne_bot hD2 hD3 hD5 hD7 hC hJ)
  have hH2 : pCoreOf 2 (S126T2.Gv v) ≠ ⊥ := S126T2.pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥X := InternalSec.sqtkGroup_mono
    (sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2) hKS
  have hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ Kv := by
    intro x hx
    have hx' : x ∈ (↑(Kv ⊔ S) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Kv S hSK] at hx'
    obtain ⟨y, hy, t, ht, hyt⟩ := hx'
    obtain ⟨j, hj⟩ := hC.sylow.2.1 ⟨t, ht⟩
    have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
    obtain ⟨y', hy', hp⟩ := A4.exists_pow_mul_eq hy (hSK ht) (2 ^ j)
    refine ⟨j, ?_⟩
    rw [← hyt, hp, hj', mul_one]
    exact hy'
  have hnff := hK2 G U X Kv (fun w hw => hUe.2 w hw) hXU hSQ hO2 le_sup_left
    (sup_le Subgroup.le_normalizer hSK) hiso hpow
  exact S126T2.false_of_le_Q_of_not_ff hD3 hD5 hD7 hC hJ hnff

end CFSG.Quasithin.H13
