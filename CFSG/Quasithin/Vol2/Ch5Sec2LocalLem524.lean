module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

@[expose] def Stmt5_2_L2Lie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsL2Choice T H L₂ →
      IsRankOneListed (oTwoQuot ↥L₂) ∧ borelOf L₂ T ≤ M ∧
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (oTwoUpper H : Set G) →
        X ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        Odd (Nat.card X) → X ≤ Subgroup.normalizer (L₂ : Set G)

section General

variable {G : Type} [Group G]

theorem odd_card_sup [Finite G] {D B : Subgroup G} (hBD : B ≤ Subgroup.normalizer (D : Set G))
    (hD : Odd (Nat.card D)) (hB : Odd (Nat.card B)) : Odd (Nat.card ↥(D ⊔ B)) := by
  have hDX : D ≤ D ⊔ B := le_sup_left
  have hBX : B ≤ D ⊔ B := le_sup_right
  have : (D.subgroupOf (D ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr (sup_le Subgroup.le_normalizer hBD)
  have htop : B.subgroupOf (D ⊔ B) ⊔ D.subgroupOf (D ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBX hDX, sup_comm, Subgroup.subgroupOf_self]
  have h1 := Subgroup.card_mul_index (D.subgroupOf (D ⊔ B))
  have h2 : (D.subgroupOf (D ⊔ B)).index =
      (D.subgroupOf (D ⊔ B)).relIndex (B.subgroupOf (D ⊔ B)) := by
    rw [← Subgroup.relIndex_sup_right, htop, Subgroup.relIndex_top_right]
  have hcD : Nat.card ↥(D.subgroupOf (D ⊔ B)) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv
  have hcB : Nat.card ↥(B.subgroupOf (D ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  have h3 : (D.subgroupOf (D ⊔ B)).relIndex (B.subgroupOf (D ⊔ B)) ∣ Nat.card B := by
    rw [← hcB]
    exact Subgroup.relIndex_dvd_card _ _
  rw [← h1, hcD, h2]
  exact hD.mul (Odd.of_dvd_nat hB h3)

theorem le_normalizer_of_isHall [Finite G] {D B Y : Subgroup G}
    (hB : Lin2.IsHallTwoPrimeOf B Y) (hD : Odd (Nat.card D))
    (hBD : B ≤ Subgroup.normalizer (D : Set G)) (hDY : D ≤ Subgroup.normalizer (Y : Set G)) :
    D ≤ Subgroup.normalizer (B : Set G) := by
  set W := (D ⊔ B) ⊓ Y with hW
  have hBW : B ≤ W := le_inf le_sup_right hB.1
  have hWY : W ≤ Y := inf_le_right
  have hWodd : Odd (Nat.card W) := by
    have hodd := odd_card_sup hBD hD hB.2.1
    have hdvd : Nat.card W ∣ Nat.card ↥(D ⊔ B) := Subgroup.card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨k, hk⟩ := hB.2.2
  have hmul := Subgroup.relIndex_mul_relIndex B W Y hBW hWY
  have hdvd2 : B.relIndex W ∣ 2 ^ k := by
    rw [← hk, ← hmul]
    exact Dvd.intro _ rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hdvdW : B.relIndex W ∣ Nat.card W := by
    rw [Subgroup.relIndex]
    have := Subgroup.index_dvd_card (B.subgroupOf W)
    exact this
  have hj0 : j = 0 := by
    by_contra hj0
    have h2 : 2 ∣ Nat.card W := by
      rw [hj] at hdvdW
      exact (dvd_pow_self 2 hj0).trans hdvdW
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)
  rw [hj0, pow_zero] at hj
  have hWB : W = B := le_antisymm (Subgroup.relIndex_eq_one.mp hj) hBW
  have hDW : D ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf (le_sup_left.trans Subgroup.le_normalizer) hDY).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rw [hWB] at hDW
  exact hDW

theorem mem_normalizer_of_map_conj_eq {R : Subgroup G} {g : G}
    (h : R.map (MulAut.conj g).toMonoidHom = R) : g ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have hyeq : y = x := by simpa using hyx'
    rw [← hyeq]
    exact hy

theorem mem_normalizer_inf_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ Subgroup.normalizer (B : Set G) : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_inf_eq A (Subgroup.normalizer (B : Set G)) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective, map_conj_eq_of_mem_normalizer hA]
  congr 1
  have hN : (Subgroup.normalizer (B : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq B (MulAut.conj g)
  rw [hN, map_conj_eq_of_mem_normalizer hB]

theorem IsL2Choice.le_oTwoUpper {T H L₂ : Subgroup G} (h : IsL2Choice T H L₂) :
    L₂ ≤ oTwoUpper H := by
  obtain ⟨K₁, -, hKeq, hcase⟩ := h
  rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, hP, hL₂P⟩
  · rw [hKeq]
    exact le_conjClosure L₂ T
  · exact (A3.subnormal_le hL₂P.2.2.1).trans hP.1

end General

namespace Hyp5_1_8

variable {G : Type} [Group G] [Finite G] {T M L H : Subgroup G} {n : ℕ}

theorem pCoreOf_inf_oTwoUpper_eq (hyp : Hyp5_1_8 G T M L H n)
    (hBorel : E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H)) :
    pCoreOf 2 (M ⊓ oTwoUpper H) = T ⊓ oTwoUpper H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hMK := hyp.borel_eq hBorel
  have hTKM : T ⊓ oTwoUpper H ≤ M ⊓ oTwoUpper H := inf_le_inf_right _ h.T_le
  have hMKN :
      M ⊓ oTwoUpper H ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [hMK]
    exact inf_le_right
  have hTsyl : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
    A4.isSylowTwoOf_mono hTK hTKM inf_le_right
  exact le_antisymm (F7.isSylowTwoOf_pCoreOf_le hTsyl)
    (le_pCoreOf_of_le_normalizer 2 hTKM hMKN hTK.2.1)

end Hyp5_1_8

theorem stmt5_2_4_of (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (h510 : Stmt5_1_10)
    (h521 : Stmt5_2_1) (hLie : Stmt5_2_L2Lie) : Stmt5_2_4 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  obtain ⟨k, -, hBorel, hBK, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  obtain ⟨-, -, hX⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice
  have hS : sec52S M H ≤ Subgroup.normalizer (L₂ : Set G) :=
    h521 G T M L H B D L₂ n hyp.toHyp5_1_8 hN hyp.choice hyp.notL34
  have hDL : D ≤ L := hN.2.1.1.trans inf_le_left
  have hDM : D ≤ M := hDL.trans h.L_le
  have hDK : D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hyp.D_le
  have hDMK : D ≤ Subgroup.normalizer ((M ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    (le_inf (hDM.trans Subgroup.le_normalizer) hDK).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hO := hyp.toHyp5_1_8.pCoreOf_inf_oTwoUpper_eq hBorel
  have hDTK : D ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [← hO]
    exact hDMK.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hDodd : Odd (Nat.card D) := hN.2.1.2.1
  have hDL₂ : D ≤ Subgroup.normalizer (L₂ : Set G) := hX D hDK hDTK hDodd
  have hBH : B ≤ H := hN.1.1.trans inf_le_right
  have hBKn : B ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hBH.trans (le_normalizer_oTwoUpper H)
  have hMK := hyp.toHyp5_1_8.borel_eq hBorel
  have hBTK : B ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    have := hBK.1
    rw [hMK] at this
    exact this.trans inf_le_right
  have hBL₂ : B ≤ Subgroup.normalizer (L₂ : Set G) := hX B hBKn hBTK hBK.2.1
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := hN.2.2
  have hDB : D ≤ Subgroup.normalizer (B : Set G) := le_normalizer_of_isHall hBK hDodd hBD hDMK
  refine ⟨hDK, ⟨hDB, hBD⟩, ⟨?_, ?_, ?_⟩, sup_le (sup_le hDL₂ hS) hBL₂⟩
  ·
    exact hN.1.1.trans (le_normalizer_pCoreOf 2 _)
  ·
    have hSK : sec52S M H ⊓ oTwoUpper H = T ⊓ oTwoUpper H :=
      hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
    have hL₂K := hyp.choice.le_oTwoUpper
    have hSL₂ : sec52S M H ⊓ L₂ = (T ⊓ oTwoUpper H) ⊓ L₂ := by
      rw [← hSK, inf_assoc, inf_eq_right.mpr hL₂K]
    rw [hSL₂]
    exact (le_inf hDTK hDL₂).trans Subgroup.inf_normalizer_le_normalizer_inf
  ·
    set S := sec52S M H with hSdef
    have hSL : S ⊓ L = T ⊓ L := h.inf_L_eq h331 hR hyp.hStar
    have hTLS : T ⊓ L ≤ S := hSL ▸ inf_le_left
    have hSM : S ≤ M := (pCoreOf_le 2 _).trans inf_le_left
    have hSLn : S ≤ Subgroup.normalizer (L : Set G) := hSM.trans h.normal
    have hSTL : S ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [← hSL]
      exact (le_inf Subgroup.le_normalizer hSLn).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hSX : S ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := fun s hs =>
      mem_normalizer_inf_normalizer (hSLn hs) (hSTL hs)
    have hXeq : D ⊔ (T ⊓ L) = borelL T L := h.borelL_eq_sup hN.2.1
    have hDTL : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      hN.2.1.1.trans inf_le_right
    have hX1 : ((borelL T L : Subgroup G) : Set G) =
        (D : Set G) * ((T ⊓ L : Subgroup G) : Set G) := by
      rw [← hXeq]
      exact Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L) hDTL
    have hX2 : ((borelL T L : Subgroup G) : Set G) =
        ((T ⊓ L : Subgroup G) : Set G) * (D : Set G) := by
      rw [← hXeq, sup_comm]
      exact Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ L) D hDTL
    have hSXc : (S : Set G) * ((borelL T L : Subgroup G) : Set G) =
        ((borelL T L : Subgroup G) : Set G) * (S : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (borelL T L) hSX,
        ← Subgroup.coe_mul_of_right_le_normalizer_left (borelL T L) S hSX, sup_comm]
    have hS1 : (S : Set G) * ((T ⊓ L : Subgroup G) : Set G) = (S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left S (T ⊓ L)
        (hTLS.trans Subgroup.le_normalizer), sup_eq_left.mpr hTLS]
    have hS2 : ((T ⊓ L : Subgroup G) : Set G) * (S : Set G) = (S : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (T ⊓ L) S
        (hTLS.trans Subgroup.le_normalizer), sup_eq_right.mpr hTLS]
    calc (D : Set G) * (S : Set G) = (D : Set G) * (((T ⊓ L : Subgroup G) : Set G) * S) := by
          rw [hS2]
      _ = ((borelL T L : Subgroup G) : Set G) * S := by rw [hX1, mul_assoc]
      _ = (S : Set G) * ((borelL T L : Subgroup G) : Set G) := hSXc.symm
      _ = (S : Set G) * (((T ⊓ L : Subgroup G) : Set G) * D) := by rw [hX2]
      _ = (S : Set G) * D := by rw [← mul_assoc, hS1]

end CFSG.Quasithin.H13
