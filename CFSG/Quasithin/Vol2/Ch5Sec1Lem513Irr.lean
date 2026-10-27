module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Sub
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513D3
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QTail
public import CFSG.Quasithin.Vol2.Ch3Sec2IrrPlus
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueIrr
public import CFSG.Quasithin.Vol2.Ch6Remark612
public import CFSG.Quasithin.Vol2.Ch5ModulesFFOrd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem eq_of_isPGroup_quot (h : Hyp5_0_1 G T M L n) {N : Subgroup G} (hNL : N ≤ L)
    (hN : (N.subgroupOf L).Normal) (h2 : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : N = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h.le_pCoreOf_or_eq hNL ((Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hN) with
    hle | heq
  · exfalso
    have hp : IsPGroup 2 (↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨k, hk⟩ := h2 x x.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        obtain ⟨y, hy, hyx⟩ := hle hk
        have hyx' : y = x ^ 2 ^ k := Subtype.ext (by simpa using hyx)
        rw [← hyx']
        exact hy
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [h.card_quot] at hk
    have hn1 : 1 ≤ n := by have := h.two_le; omega
    obtain ⟨-, h1⟩ := two_pow_mul_odd_inj (odd_two_pow_pow_sub_one hn1 (by norm_num)) odd_one
      (hk.trans (mul_one _).symm)
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
    have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  · exact heq

theorem exists_irrPlusIn_le_normalizer (hD : D310L2Fact) (h : Hyp5_0_1 G T M L n)
    (hV : IsCh5Module T L V) (hC : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hq : qhatInt (L ⊔ T) V hV.isTwoReducedIn.2.2.1 ≤ 2) :
    ∃ I : Subgroup G, IsIrrPlusIn L V T I ∧ T ≤ Subgroup.normalizer (I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hVel : IsElemAbelian 2 V := hred.2.2.1
  have hYV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hYV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hYV
  let _ : IsMulCommutative ↥V := hVel.1
  obtain ⟨I₀, hI₀⟩ := exists_irrPlusBase (L := L)
    (fun N hNL hN h2 => h.eq_of_isPGroup_quot hNL hN h2)
    (fun x hx => by simpa [pow_two] using hVel.2 x hx) hLV hV.2.2
  obtain ⟨I, hI, -⟩ := exists_isIrrPlusIn_sectionIso (A := V) (X := L) (T := T)
    (fun a ha => hVel.2 a ha) hLV hTV h.T_le_normalizer h.sylow.1 hI₀
  refine ⟨I, hI, ?_⟩
  set VT := conjClosure I T with hVTdef
  have hIV : I ≤ V := hI.1
  have hVTV : VT ≤ V := conjClosure_le fun t ht z hz =>
    (Subgroup.mem_normalizer_iff.mp (hTV ht) z).mp (hIV hz)
  have hLI : L ≤ Subgroup.normalizer (I : Set G) := hI.2.2.1
  have hTVT : T ≤ Subgroup.normalizer (VT : Set G) := le_normalizer_conjClosure I T
  have hLVT : L ≤ Subgroup.normalizer (VT : Set G) :=
    le_normalizer_conjClosure_of_le h.T_le_normalizer hLI
  have hYVT : L ⊔ T ≤ Subgroup.normalizer (VT : Set G) := sup_le hLVT hTVT
  have hVTL : ⁅VT, L⁆ ≠ ⊥ := by
    intro hb
    apply hI.2.1
    rw [← hI.2.2.2.1, eq_bot_iff, ← hb]
    exact Subgroup.commutator_mono (le_conjClosure I T) le_rfl
  have hVTel : IsElemAbelian 2 VT := isElemAbelian_mono hVel hVTV
  have hCT : VT ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    le_bot_iff.mp (hC ▸ inf_le_inf_right _ hVTV)
  have hIVT : IsIrrPlusIn L VT T I := by
    obtain ⟨-, hI1, hI2, hI3, hI4, hI5, hI6⟩ := hI
    refine ⟨le_conjClosure I T, hI1, hI2, hI3, hI4, hI5, ?_⟩
    rw [hCT]
    rw [hC] at hI6
    exact hI6
  have hO2 := h.pCoreOf_autOn_eq_bot_of_le hV hVTV hYVT hVTL
  have hlie := h.lieModel_autOn_of_le hV hVTV hYVT hVTL
  have hfaith : (L ⊔ T) ⊓ Subgroup.centralizer (VT : Set G) ≤
      Subgroup.centralizer (V : Set G) := by
    rw [h.sup_inf_centralizer_eq_of_le hV hVTV hYVT hVTL]
    exact inf_le_right
  have hqVT : qhatInt (L ⊔ T) VT hVTel ≤ 2 :=
    (qhatInt_le_qhatInt_of_le hVel hVTV hYVT hfaith hq).trans hq
  have heq := hD G (L ⊔ T) L T I n h.sqtkGroup_sup (h.isSylowTwoOf le_sup_right) le_sup_left
    h.sup_le_normalizer rfl hIVT hVTel hO2 hlie hqVT
  rw [heq]
  exact hTVT

end Hyp5_0_1

end CFSG.Quasithin.H13
