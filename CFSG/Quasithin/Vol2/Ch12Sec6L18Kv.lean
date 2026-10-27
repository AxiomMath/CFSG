module

public import CFSG.Quasithin.Vol2.Ch12Sec6L18a
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3331S
public import CFSG.Quasithin.Background.C124BlockA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G6 S126
  S126L1a S126P S126E S126F S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

section Odd

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_two_pow_odd (x : G) : ∃ k : ℕ, Odd (orderOf (x ^ 2 ^ k)) := by
  refine ⟨(orderOf x).factorization 2, ?_⟩
  have hpos : 0 < orderOf x := orderOf_pos x
  have hdvd : 2 ^ (orderOf x).factorization 2 ∣ orderOf x := Nat.ordProj_dvd _ _
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd]
  exact Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hpos.ne')

end Odd

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem comm_pCoreOf_zpowers_le (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5) (hD7 : Lemma12_6_13)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hL : IsShort2 L) {y : G} (hy : y ∈ Lv L v) (hodd : Odd (orderOf y)) :
    ⁅pCoreOf 2 (Kv ⊔ S), Subgroup.zpowers y⁆ ≤ ⁅Usec Kv S, Kv⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (Kv ⊔ S) with hP
  set Y := Subgroup.zpowers y with hY
  obtain ⟨-, -, -, -, -, hOR, -, hLR, -⟩ := hD2 G T L V F v Kv S hC
  obtain ⟨-, -, hVU⟩ := hD7 G T L V F v Kv S hC
  have hYL : Y ≤ Lv L v := (Subgroup.zpowers_le).2 hy
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) :=
    hYL.trans (hC.lv_le.trans (le_sup_left.trans (le_normalizer_pCoreOf 2 _)))
  have hP2 : IsPGroup 2 ↥P := pCoreOf_isPGroup 2 _
  have hcop : Nat.Coprime (Nat.card ↥Y) (Nat.card ↥P) := by
    rw [hY, Nat.card_zpowers]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP2
    rw [hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have hsolv : Group.IsSolvable ↥P := by
    have := hP2.isNilpotent
    infer_instance
  have hdc := Lem3331S.double_commutator_eq Y P hYP hcop hsolv
  have h1 : ⁅P, Y⁆ ≤ pCoreOf 2 (Lv L v) :=
    ((Subgroup.commutator_mono hOR hYL).trans (Subgroup.commutator_comm _ _).le).trans hLR
  rw [← hdc]
  calc ⁅⁅P, Y⁆, Y⁆ ≤ ⁅pCoreOf 2 (Lv L v), Lv L v⁆ := Subgroup.commutator_mono h1 hYL
    _ ≤ Vv L V v := comm_pCoreOf_Lv_le_Vv h1222 F hC.hyp hC.mem hC.coord hL
    _ ≤ ⁅Usec Kv S, Kv⁆ := hVU

theorem le_centralizer_or_eq_of_normal (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat) (hD7 : Lemma12_6_13) {F : Frame126 T L V}
    {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) {N : Subgroup G} (hNK : N ≤ Kv)
    (hKN : ∀ k ∈ Kv, ∀ n ∈ N, k * n * k⁻¹ ∈ N) :
    N ≤ Subgroup.centralizer (Usec Kv S : Set G) ∨ Kv ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := Usec Kv S with hU
  set P := pCoreOf 2 (Kv ⊔ S) with hP
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  have hKU : Kv ≤ Subgroup.normalizer (U : Set G) := Kv_le_normalizer_Usec hC
  have hKs : IsSimpleGroup ↥(autOn Kv U) :=
    (MulEquiv.isSimpleGroup_congr (autOn_Kv_equiv hD7 hC)).1 (isSimple_Kv h1222 h36 hC)
  have hle1 : autOn N U ≤ autOn Kv U := InternalSec.autOn_le_autOn_of_le hNK
  have hnorm : ((autOn N U).subgroupOf (autOn Kv U)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact InternalSec.autOn_normal_of (U := U) (fun k hk =>
      Subgroup.mem_normalizer_fintype fun c hc => hKN k hk c hc) _ g.2 _ hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((autOn N U).subgroupOf (autOn Kv U)) with
    hbot | htop
  · left
    intro n hn
    have hnN : n ∈ Subgroup.normalizer (U : Set G) := hKU (hNK hn)
    have h1 : (⟨conjAct U ⟨n, hnN⟩, hle1 (QuasithinUnique.Setup.mem_autOn_iff.2
        ⟨⟨n, hnN⟩, hn, rfl⟩)⟩ : ↥(autOn Kv U)) ∈ (autOn N U).subgroupOf (autOn Kv U) :=
      QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨n, hnN⟩, hn, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (U : Set G)) le_rfl
      _).1 (congrArg Subtype.val h1)
  · right
    have hKle : Kv ≤ N ⊔ (Kv ⊓ P) := by
      intro k hk
      have hkN : k ∈ Subgroup.normalizer (U : Set G) := hKU hk
      have hkA : conjAct U ⟨k, hkN⟩ ∈ autOn N U := by
        have hmem : (⟨conjAct U ⟨k, hkN⟩, QuasithinUnique.Setup.mem_autOn_iff.2
            ⟨⟨k, hkN⟩, hk, rfl⟩⟩ : ↥(autOn Kv U)) ∈ (autOn N U).subgroupOf (autOn Kv U) :=
          htop ▸ Subgroup.mem_top _
        exact hmem
      obtain ⟨⟨c, hcN⟩, hcC, hck⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hkA
      have hc : ((⟨c, hcN⟩⁻¹ * ⟨k, hkN⟩ : ↥(Subgroup.normalizer (U : Set G))) : G) ∈
          Subgroup.centralizer (U : Set G) := by
        rw [← QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (U : Set G)) le_rfl]
        show conjAct U (⟨c, hcN⟩⁻¹ * ⟨k, hkN⟩) = 1
        rw [map_mul, map_inv, hck, inv_mul_cancel]
      have hcK : c ∈ Kv := hNK hcC
      have hcP : c⁻¹ * k ∈ Kv ⊓ P := ⟨Kv.mul_mem (Kv.inv_mem hcK) hk, by
        rw [hP, hO]
        exact ⟨(Kv ⊔ S).mul_mem ((Kv ⊔ S).inv_mem ((le_sup_left : Kv ≤ Kv ⊔ S) hcK))
          ((le_sup_left : Kv ≤ Kv ⊔ S) hk), hc⟩⟩
      have e : k = c * (c⁻¹ * k) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcC) (Subgroup.mem_sup_right hcP)
    exact perfect_le_of_le_sup_pGroup (perfect_of_mem_cComp hC.cComp) hNK hKN
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right) inf_le_left hKle

theorem comm_pCoreOf_Kv_le (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hD2 : Lemma12_6_4_5) (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hL : IsShort2 L) :
    ⁅pCoreOf 2 (Kv ⊔ S), Kv⁆ ≤ ⁅Usec Kv S, Kv⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (Kv ⊔ S) with hP
  set U := Usec Kv S with hU
  obtain ⟨⟨-, hO⟩, -, -⟩ := hD7 G T L V F v Kv S hC
  have hKP : Kv ≤ Subgroup.normalizer (P : Set G) := le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  have hKU : Kv ≤ Subgroup.normalizer (U : Set G) := Kv_le_normalizer_Usec hC
  have hKW : Kv ≤ Subgroup.normalizer ((⁅U, Kv⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le hKU Subgroup.le_normalizer
  set C := C124.cqSub Kv P ⁅U, Kv⁆ hKP hKW with hCdef
  have hCK : C ≤ Kv := fun x hx => hx.1
  have hCn : ∀ k ∈ Kv, ∀ c ∈ C, k * c * k⁻¹ ∈ C := fun k hk c hc => C124.cqSub_conj hc hk
  have hodd : ∀ y ∈ Lv L v, Odd (orderOf y) → y ∈ C := by
    intro y hy hy2
    refine ⟨hC.lv_le hy, fun q hq => ?_⟩
    exact comm_pCoreOf_zpowers_le h1222 hD2 hD7 hC hL hy hy2
      (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers y))
  have hLvC : Lv L v ≤ C := by
    have hLp : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
    have hN : ((C ⊓ Lv L v).subgroupOf (Lv L v)).Normal := ⟨fun n hn l => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hCn _ (hC.lv_le l.2) _ hn.1,
        (Lv L v).mul_mem ((Lv L v).mul_mem l.2 hn.2) ((Lv L v).inv_mem l.2)⟩⟩
    have h2 : IsPGroup 2 (↥(Lv L v) ⧸ (C ⊓ Lv L v).subgroupOf (Lv L v)) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := exists_pow_two_pow_odd (x : G)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hxk : ((x ^ 2 ^ k : ↥(Lv L v)) : G) = (x : G) ^ 2 ^ k := by simp
      rw [hxk]
      exact ⟨hodd _ ((Lv L v).pow_mem x.2 _) hk, (Lv L v).pow_mem x.2 _⟩
    have htop := C124.noTwoQuot_of_perfect hLp _ h2
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥(Lv L v)) ∈ (C ⊓ Lv L v).subgroupOf (Lv L v) :=
      htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 hx').1
  have hKC : Kv ≤ C := by
    rcases le_centralizer_or_eq_of_normal h1222 h36 hD7 hC hCK hCn with h | h
    · exfalso
      obtain ⟨φ, hφs, -⟩ := o2Iso_autOn_Lv h1222 hD7 hC
      have hLv1 : autOn (Lv L v) U = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 ha
        rw [Subgroup.mem_bot]
        exact (QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (U : Set G)) le_rfl
          _).2 (h (hLvC hlL))
      have h1 : Nat.card ↥(alternatingGroup (Fin 6)) ≤ Nat.card ↥(autOn (Lv L v) U) :=
        Nat.card_le_card_of_surjective φ hφs
      rw [hLv1, Subgroup.card_bot, Nat.card_eq_fintype_card, card_alternatingGroup] at h1
      exact absurd h1 (by decide)
    · exact h
  rw [Subgroup.commutator_le]
  intro q hq k hk
  exact (hKC hk).2 q hq

theorem blockU_Kv_eq (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hD2 : Lemma12_6_4_5) (hD7 : Lemma12_6_13) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hL : IsShort2 L) : blockU Kv = ⁅Usec Kv S, Kv⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := Usec Kv S with hU
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hXK : Kv ⊔ S ≤ Subgroup.normalizer (Kv : Set G) := sup_le Subgroup.le_normalizer hSK
  have hKU : Kv ≤ Subgroup.normalizer (U : Set G) := Kv_le_normalizer_Usec hC
  have hUK : U ≤ Subgroup.normalizer (Kv : Set G) :=
    ((Usec_le Kv S).trans (pCoreOf_le 2 _)).trans hXK
  have hKp : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  apply le_antisymm
  · have hQP : blockQ Kv ≤ pCoreOf 2 (Kv ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
        (hXK.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    exact (Subgroup.commutator_mono hQP le_rfl).trans (comm_pCoreOf_Kv_le h1222 h36 hD2 hD7 hC hL)
  · have hWK : ⁅U, Kv⁆ ≤ Kv := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      have h1 : u * k * u⁻¹ ∈ Kv := (Subgroup.mem_normalizer_iff.1 (hUK hu) k).1 hk
      rw [commutatorElement_def]
      exact Kv.mul_mem h1 (Kv.inv_mem hk)
    have hWU : ⁅U, Kv⁆ ≤ U := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      have h1 : k * u⁻¹ * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hKU hk) _).1 (U.inv_mem hu)
      have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
      rw [commutatorElement_def, e]
      exact U.mul_mem hu h1
    have hWQ : ⁅U, Kv⁆ ≤ blockQ Kv :=
      le_pCoreOf_of_le_normalizer 2 hWK (le_normalizer_commutator_of_le hKU Subgroup.le_normalizer)
        ((pCoreOf_isPGroup 2 (Kv ⊔ S)).to_le (hWU.trans (Usec_le Kv S)))
    calc ⁅U, Kv⁆ ≤ ⁅⁅U, Kv⁆, Kv⁆ := le_comm_comm_of_perfect hKp hUK hKU
      _ ≤ blockU Kv := Subgroup.commutator_mono hWQ le_rfl

end S126T2

end CFSG.Quasithin.H13
