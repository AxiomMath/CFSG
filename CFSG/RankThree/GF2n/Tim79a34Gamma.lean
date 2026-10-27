module

public import CFSG.RankThree.GF2n.Tim79a34GammaComm
public import CFSG.RankThree.GF2n.Tim79a34Twisted
public import CFSG.RankThree.GF2n.Tim79a34QIndex
public import CFSG.RankThree.GF2n.Tim79a34MemberUnique
public import CFSG.RankThree.GF2n.Tim79a34IW
public import CFSG.RankThree.GF2n.Tim79a34Lemma11a
public import CFSG.RankThree.GF2n.Tim79a34Lemma11c

public section

namespace CFSG.RankThree.GF2n.Tim79a.Gamma

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic CFSG.RankThree.GF2n.Tim79a
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_or_inv_mul_mem_of_relIndex_le_two {P Q : Subgroup G} (hidx : P.relIndex Q ≤ 2)
    {g : G} (hgQ : g ∈ Q) (hgP : g ∉ P) {q : G} (hq : q ∈ Q) : q ∈ P ∨ g⁻¹ * q ∈ P := by
  have hne1 : (P.subgroupOf Q).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hgP
    have hg : (⟨g, hgQ⟩ : Q) ∈ P.subgroupOf Q := by
      rw [h1]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hg
  have hne0 : (P.subgroupOf Q).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (P.subgroupOf Q).index ≤ 2 := hidx
  have h2 : (P.subgroupOf Q).index = 2 := by omega
  by_cases hqP : q ∈ P
  · exact Or.inl hqP
  · right
    have ha : (⟨g, hgQ⟩ : Q)⁻¹ ∉ P.subgroupOf Q := by
      rw [Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]
      exact hgP
    have hb : (⟨q, hq⟩ : Q) ∉ P.subgroupOf Q := by
      rw [Subgroup.mem_subgroupOf]
      exact hqP
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mul_mem_iff_of_index_two h2).mpr (iff_of_false ha hb))

theorem sec34GammaStatement_holds : Sec34GammaStatement := by
  intro G _ _ M V Q P H hH hZ
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have hIW : Sec34IWStatement :=
    sec34IW_holds hN spRadFactsStatement_holds commPairingStatement_holds
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  have h11b : Lemma11bStatement := lemma11b_holds hN h11a spRadFactsStatement_holds
  have h11c : Lemma11cStatement := lemma11c_holds spRadFactsStatement_holds h11a
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hZ
  obtain ⟨n, Φ, ψ, hn2, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hZ
  have cfg : GCfg M V Q P H Φ ψ a T :=
    { hyp := hH, centre := hZ, iw := hcP, nat := ⟨hequiv, hpoint⟩, ne := ha, trans := hT,
      point := hTV, two_le := hn2 }
  have hidx : P.relIndex Q ≤ 2 := relIndex_P_Q_le_two hc (card_V cfg)
  have hPQ : P ≤ Q := hc.P_le_Q
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, ∀ c, c ∈ C ↔ c ∈ Q ∧ (∀ w ∈ wOf V H, c * w = w * c) ∧
      (∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) ∧ (∀ p ∈ P, ⁅p, c⁆ ∈ V ⊓ wOf V H) := by
    refine ⟨⟨⟨⟨setOf fun c => c ∈ Q ∧ (∀ w ∈ wOf V H, c * w = w * c) ∧
        (∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H) ∧ (∀ p ∈ P, ⁅p, c⁆ ∈ V ⊓ wOf V H), ?_⟩, ?_⟩, ?_⟩,
      fun c => Iff.rfl⟩
    · rintro c d ⟨hcQ, hcW, hcX, hcA⟩ ⟨hdQ, hdW, hdX, hdA⟩
      refine ⟨Q.mul_mem hcQ hdQ, fun w hw => ?_, fun x hx => ?_, fun p hp => ?_⟩
      · rw [mul_assoc, hdW w hw, ← mul_assoc, hcW w hw, mul_assoc]
      · have e : ⁅x, c * d⁆ = ⁅x, c⁆ * (c * ⁅x, d⁆ * c⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hcW _ (hdX x hx), mul_inv_cancel_right]
        exact (wOf V H).mul_mem (hcX x hx) (hdX x hx)
      · have e : ⁅p, c * d⁆ = ⁅p, c⁆ * (c * ⁅p, d⁆ * c⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hcW _ (Subgroup.mem_inf.mp (hdA p hp)).2, mul_inv_cancel_right]
        exact (V ⊓ wOf V H).mul_mem (hcA p hp) (hdA p hp)
    · refine ⟨Q.one_mem, fun w _ => by rw [one_mul, mul_one], fun x _ => ?_, fun p _ => ?_⟩
      · rw [commutatorElement_one_right]
        exact Subgroup.one_mem _
      · rw [commutatorElement_one_right]
        exact Subgroup.one_mem _
    · rintro c ⟨hcQ, hcW, hcX, hcA⟩
      have hcW' : ∀ w ∈ wOf V H, c⁻¹ * w * c = w := fun w hw => by
        rw [mul_assoc, ← hcW w hw, inv_mul_cancel_left]
      refine ⟨Q.inv_mem hcQ, fun w hw => ?_, fun x hx => ?_, fun p hp => ?_⟩
      · calc c⁻¹ * w = c⁻¹ * w * c * c⁻¹ := by group
          _ = w * c⁻¹ := by rw [hcW' w hw]
      · have e : ⁅x, c⁻¹⁆ = c⁻¹ * ⁅x, c⁆⁻¹ * c := by
          simp only [commutatorElement_def]
          group
        rw [e, hcW' _ ((wOf V H).inv_mem (hcX x hx))]
        exact (wOf V H).inv_mem (hcX x hx)
      · have e : ⁅p, c⁻¹⁆ = c⁻¹ * ⁅p, c⁆⁻¹ * c := by
          simp only [commutatorElement_def]
          group
        rw [e, hcW' _ ((wOf V H).inv_mem (Subgroup.mem_inf.mp (hcA p hp)).2)]
        exact (V ⊓ wOf V H).inv_mem (hcA p hp)
  refine ⟨C, fun c hc' => ((hC c).mp hc').1, ?_, fun p hp c hc' => ((hC c).mp hc').2.2.2 p hp,
    fun c hc' => ((hC c).mp hc').2.1, fun c hc' => ((hC c).mp hc').2.2.1, hidx⟩
  refine le_antisymm (sup_le hPQ fun c hc' => ((hC c).mp hc').1) ?_
  intro q hq
  by_cases hQP : ∀ y ∈ Q, y ∈ P
  · exact Subgroup.mem_sup_left (hQP q hq)
  push_neg at hQP
  obtain ⟨x, hxQ, hxP⟩ := hQP
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  obtain ⟨r, hrP, hr⟩ := exists_P_conj_of_comm_mem h11a h11b h11c cfg hb
    (comm_mem_P_of_mem_W h11b cfg (Additive.toMul (ψ b)).2 hxQ)
  obtain ⟨bG, hbG⟩ : ∃ g : G, g = ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) := ⟨_, rfl⟩
  rw [← hbG] at hr
  have hc₀Q : r⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem (hPQ hrP)) hxQ
  have hc₀P : r⁻¹ * x ∉ P := fun h => hxP (by
    have e : x = r * (r⁻¹ * x) := by group
    rw [e]
    exact P.mul_mem hrP h)
  have hc₀b : r⁻¹ * x * bG = bG * (r⁻¹ * x) := by
    calc r⁻¹ * x * bG = r⁻¹ * (x * bG * x⁻¹) * x := by group
      _ = r⁻¹ * (r * bG * r⁻¹) * x := by rw [hr]
      _ = bG * (r⁻¹ * x) := by group
  rw [hbG] at hc₀b
  have hcW : ∀ w ∈ wOf V H, r⁻¹ * x * w = w * (r⁻¹ * x) := fun w hw =>
    centralizes_W_of_commute h11a h11b h11c cfg hb hc₀Q hc₀b hw
  have hcXle : conjSubgroup (r⁻¹ * x) (xOf V H) ≤ xOf V H :=
    conjSubgroup_xOf_le h11a cfg (mem_M_of_mem_Q cfg hc₀Q) fun w hw => by
      rw [hcW w hw, mul_inv_cancel_right]
      exact hw
  have hcX : ∀ y ∈ xOf V H, ⁅y, r⁻¹ * x⁆ ∈ wOf V H := fun y hy =>
    comm_mem_W_of_centralizes_W cfg hcXle hcW hy
  have hQ' : ∀ y ∈ Q, y ∈ P ∨ (r⁻¹ * x)⁻¹ * y ∈ P := fun y hy =>
    mem_or_inv_mul_mem_of_relIndex_le_two hidx hc₀Q hc₀P hy
  have hc₀C : r⁻¹ * x ∈ C := (hC _).mpr ⟨hc₀Q, hcW, hcX, fun p hp =>
    comm_mem_VW_of_centralizes h11a h11b h11c cfg hb hc₀Q hcW hcX hQ' hp⟩
  rcases hQ' q hq with h | h
  · exact Subgroup.mem_sup_left h
  · have e : q = (r⁻¹ * x) * ((r⁻¹ * x)⁻¹ * q) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc₀C) (Subgroup.mem_sup_left h)

end CFSG.RankThree.GF2n.Tim79a.Gamma
