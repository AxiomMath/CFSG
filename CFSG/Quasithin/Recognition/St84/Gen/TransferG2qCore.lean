module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferG2qData
public import CFSG.Quasithin.Recognition.St84.Gen.TransferLeftData

import CFSG.Quasithin.Recognition.St84.Gen.TransferLeftCore
import CFSG.Quasithin.Recognition.St84.TransferVertex
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.Quasithin.Recognition.St84.Gen.NatSecModule

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem g2q_centralizer_pCoreOfRight {L1 L2 S : Subgroup H} {f : ℕ}
    (hd : G2qEdgeData L1 L2 S f) :
    ∀ k ∈ oTwoPrime (f112saP2' L1 L2 S), Odd (orderOf k) → k ≠ 1 →
      pCoreOf 2 (f112saP2' L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set H) ≤
        pCoreOf 2 (f112saP1' L1 L2 S) := by
  classical
  let Eβ := f112saP2' L1 L2 S
  let Lβ := oTwoPrime Eβ
  let Qβ := pCoreOf 2 Eβ
  let Zβ := centerOf Qβ
  obtain ⟨F, hFld, hFintype, hFcard, α, hα, hker, _, W, _, hWQ, _, hcommW, hWnat⟩ :=
    hd.local_.nat_right
  letI := hFld
  letI := hFintype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) hFcard
  have hQeq : pCoreOf 2 Lβ = Qβ := pCoreOf_oTwoPrime Eβ
  have hZeq : centerOf (pCoreOf 2 Lβ) = Zβ := by rw [hQeq]
  have hWcomm : ⁅W, Lβ⁆ ≤ Zβ := by
    rw [← hZeq]
    exact hcommW
  intro k hk hkodd hk1
  let kk : ↥Lβ := ⟨k, hk⟩
  have hkodd' : Odd (orderOf kk) := by
    rw [Subgroup.orderOf_mk]
    exact hkodd
  have hαk1 : α kk ≠ 1 := by
    intro hα1
    have hmem : kk ∈ CFSG.pCore 2 ↥Lβ := by
      rw [← hker, MonoidHom.mem_ker]
      exact hα1
    obtain ⟨j, hj⟩ :=
      (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Lβ))) ⟨kk, hmem⟩
    have hj' : orderOf (⟨kk, hmem⟩ : ↥(CFSG.pCore 2 ↥Lβ)) = 2 ^ j := hj
    rw [Subgroup.orderOf_mk] at hj
    have hodd : Odd (2 ^ j) := by rwa [← hj]
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.mpr hodd) (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two hj0)
    rw [hj0, pow_zero] at hj'
    have hkk1 : kk = 1 := by
      simpa using congrArg (fun x : ↥(CFSG.pCore 2 ↥Lβ) => (x : ↥Lβ))
        (orderOf_eq_one_iff.mp hj')
    exact hk1 (Subtype.ext_iff.mp hkk1)
  intro x hx
  obtain ⟨hxQβ, hxCent⟩ := Subgroup.mem_inf.mp hx
  have hxE : x ∈ pCoreOf 2 Lβ := by
    rw [hQeq]
    exact hxQβ
  have hkx : (kk : H) * x = x * (kk : H) :=
    Subgroup.mem_centralizer_iff.mp hxCent k (Set.mem_singleton k)
  have hxW : x ∈ W := hWnat.mem_of_commute_of_odd hkodd' hαk1 hxE hkx
  refine hd.relCent_left x hxQβ ?_
  intro l hl
  exact hWcomm (Subgroup.commutator_mem_commutator hxW hl)

private theorem g2q_centerRight_le_pCoreOfLeft {L1 L2 S : Subgroup H} {f : ℕ}
    (hd : G2qEdgeData L1 L2 S f) :
    centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) ≤
      pCoreOf 2 (f112saP1' L1 L2 S) := by
  intro x hx
  have hxQβ : x ∈ pCoreOf 2 (f112saP2' L1 L2 S) := hx.1
  refine hd.relCent_left x hxQβ ?_
  intro l hl
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  have hLβ_N : Lβ ≤ Subgroup.normalizer
      (centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) : Set H) := by
    have h : Lβ ≤ Subgroup.normalizer (centerOf (pCoreOf 2 Lβ) : Set H) := by
      intro g hg
      have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 Lβ : Set H) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Lβ hg
      have hgC : g ∈ Subgroup.normalizer
          (Subgroup.centralizer (pCoreOf 2 Lβ : Set H) : Set H) :=
        CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (pCoreOf 2 Lβ) hgQ
      change g ∈ Subgroup.normalizer
        ((pCoreOf 2 Lβ ⊓ Subgroup.centralizer (pCoreOf 2 Lβ : Set H) : Subgroup H) : Set H)
      exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨hgQ, hgC⟩)
    rwa [pCoreOf_oTwoPrime] at h
  have hl' : l ∈ Lβ := hl
  have hconj : l * x * l⁻¹ ∈ centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) :=
    (Subgroup.mem_normalizer_iff.mp (hLβ_N hl') x).mp hx
  have e : ⁅x, l⁆ = x * (l * x * l⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hconj)

private theorem g2q_commutator_pCoreOf_le_center {L1 L2 S : Subgroup H} {f : ℕ}
    (hd : G2qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) :
    ⁅pCoreOf 2 (f112saP1' L1 L2 S), pCoreOf 2 (f112saP1' L1 L2 S)⁆ ≤
      centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  let Eα := f112saP1' L1 L2 S
  have hspec : IsSpecialPGroup 2 ↥(pCoreOf 2 Eα) := by
    have h := hd.special_left.1
    rwa [pCoreOf_oTwoPrime] at h
  rcases hspec.2 with ⟨hab, -⟩ | ⟨hcomm, -, -⟩
  · rw [Subgroup.commutator_self_eq_bot_iff.mpr hab]
    exact bot_le
  · rw [← Subgroup.map_subtype_commutator (pCoreOf 2 Eα), hcomm]
    rintro x ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : ↥(pCoreOf 2 Eα)))

theorem f112ll_g2q_eq_of_localData {L1 L2 S : Subgroup H} {m n f : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : G2qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f) :
    f = m ∧ f = n := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hcardα : Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (5 * f + m) := by
    rw [(f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR).card_eq,
      twoPart_of_isL2Quot (a := 5 * f) (by omega)
        (f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2) hd.card_left]
  have hcardβ : Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ (5 * f + n) := by
    rw [(f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR).card_eq,
      twoPart_of_isL2Quot (a := 5 * f) (by omega)
        (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2) hd.card_right]
  have hmul : 6 * f = 5 * f + m :=
    Nat.pow_right_injective (a := 2) (by norm_num) (hd.card_S.symm.trans hcardα)
  have hnul : 6 * f = 5 * f + n :=
    Nat.pow_right_injective (a := 2) (by norm_num) (hd.card_S.symm.trans hcardβ)
  omega

private theorem g2q_false_of_Qβ_le_Qα {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : G2qEdgeData L1 L2 S f)
    (hQβ_le_Qα : pCoreOf 2 (f112saP2' L1 L2 S) ≤ pCoreOf 2 (f112saP1' L1 L2 S)) :
    False := by
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let Qα := pCoreOf 2 Eα
  let Qβ := pCoreOf 2 Eβ
  have hf2 : 2 ≤ f := by
    have hfm := (f112ll_g2q_eq_of_localData hF hm hn h1 h2 hd.local_).1
    omega
  have hinf_eq : Qα ⊓ Qβ = Qβ :=
    le_antisymm inf_le_right (le_inf hQβ_le_Qα le_rfl)
  have hcardβ : Nat.card ↥Qβ = 2 ^ (5 * f) := by
    change Nat.card ↥(pCoreOf 2 Eβ) = 2 ^ (5 * f)
    rw [← pCoreOf_oTwoPrime Eβ]
    exact hd.local_.card_right
  have hcardinf : Nat.card ↥(Qα ⊓ Qβ) = 2 ^ (4 * f) := by
    change Nat.card ↥(pCoreOf 2 Eα ⊓ pCoreOf 2 Eβ) = 2 ^ (4 * f)
    rw [← pCoreOf_oTwoPrime Eα, ← pCoreOf_oTwoPrime Eβ]
    exact hd.local_.card_inf
  have hcardeq : 2 ^ (5 * f) = 2 ^ (4 * f) := by
    rw [← hcardβ, ← hinf_eq, hcardinf]
  have h5 : 5 * f = 4 * f := Nat.pow_right_injective (a := 2) (by norm_num) hcardeq
  omega

theorem G2qEdgeData.transferLeftData {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hd : G2qEdgeData L1 L2 S f) :
    TransferLeftData L1 L2 S where
  nat_right := by
    obtain ⟨F, hFld, hFintype, hFcard, α, hα, hker, hnat, -⟩ := hd.local_.nat_right
    letI := hFld
    letI := hFintype
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) hFcard
    exact ⟨F, hFld, inferInstance, α, hα, hker, hnat⟩
  centerRight_le := g2q_centerRight_le_pCoreOfLeft hd
  commutator_le := g2q_commutator_pCoreOf_le_center hd.local_
  centerLeft_le := by
    have h := hd.local_.center_left
    rw [pCoreOf_oTwoPrime] at h
    rw [h]
    exact inf_le_right
  gen_left := fun N _ hZβ hN hnorm => hd.gen_left N hZβ hN hnorm
  torus_left := hd.torus_left
  indec_left := hd.indec_left
  eq_one_of_mem_trivOTwoQuot := fun k hk hkodd hktriv =>
    f112ll_eq_one_of_mem_trivOTwoQuot_of_centralizer_le hF hm hn h1 h2
      (g2q_centralizer_pCoreOfRight hd) (fun h => g2q_false_of_Qβ_le_Qα hF hm hn h1 h2 hd h)
      hk hkodd hktriv

end CFSG.Quasithin.F112R.St84

end
