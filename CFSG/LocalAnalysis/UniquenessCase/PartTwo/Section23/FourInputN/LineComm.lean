module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SUFixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGenO6p.FixedLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC

open CFSG.Open CFSG.Quasithin Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem commute_on_fixedPointSubgroup_of_sylowFixedLine [Finite W] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
      ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
        ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
          ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  classical
  let : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  obtain ⟨π, e, he⟩ := KTabC.exists_natEquiv hreal
  obtain ⟨x₀, hx₀⟩ := hline (S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective)
  set w₀ : ι → K := ((x₀ : GL ι K) : Matrix ι ι K) *ᵥ e₀ with hw₀
  have hS : ∀ v : ι → K,
      (∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • w₀ :=
    fun v => (KTabC.fixed_iff_fixed_sylowMap π S v).trans (hx₀ v)
  have hpoint : KTabD.pointStab H S = (KTabD.lineStab Γ w₀).map π.toMonoidHom :=
    KTabD.pointStab_eq_map_lineStab π e he S hS
  intro x hx y hy v hv
  rw [hpoint] at hx hy
  obtain ⟨γx, hγx, hxeq⟩ := Subgroup.mem_map.mp hx
  obtain ⟨γy, hγy, hyeq⟩ := Subgroup.mem_map.mp hy
  have hxeq' : π γx = x := hxeq
  have hyeq' : π γy = y := hyeq
  rw [← hxeq', ← hyeq']
  obtain ⟨cx, hcx⟩ := (KTabD.mem_lineStab (Γ := Γ) (w₀ := w₀)).mp hγx
  obtain ⟨cy, hcy⟩ := (KTabD.mem_lineStab (Γ := Γ) (w₀ := w₀)).mp hγy
  have hvS : ∀ s ∈ (S : Subgroup ↥H), ((s : ↥H) : MulAut W) v = v := by
    intro s hs
    have h := hv
    rw [FixedPoints.mem_subgroup] at h
    exact h ⟨s, hs⟩
  obtain ⟨t, ht⟩ : ∃ t : K, Multiplicative.toAdd (e v) = t • w₀ := by
    refine (hS (Multiplicative.toAdd (e v))).1 ?_
    intro s hs
    have h := he (π.symm s) v
    rw [MulEquiv.apply_symm_apply, hvS s hs] at h
    exact h.symm
  have h1 : Multiplicative.toAdd
        (e (((π γx : ↥H) : MulAut W) (((π γy : ↥H) : MulAut W) v)))
      = (t * cy * cx) • w₀ := by
    rw [he γx (((π γy : ↥H) : MulAut W) v), he γy v, ht, Matrix.mulVec_smul,
      hcy, smul_smul, Matrix.mulVec_smul, hcx, smul_smul]
  have h2 : Multiplicative.toAdd
        (e (((π γy : ↥H) : MulAut W) (((π γx : ↥H) : MulAut W) v)))
      = (t * cx * cy) • w₀ := by
    rw [he γy (((π γx : ↥H) : MulAut W) v), he γx v, ht, Matrix.mulVec_smul,
      hcx, smul_smul, Matrix.mulVec_smul, hcy, smul_smul]
  have hcomm : t * cy * cx = t * cx * cy := by
    calc t * cy * cx = t * (cy * cx) := mul_assoc t cy cx
      _ = t * (cx * cy) := by rw [mul_comm cy cx]
      _ = t * cx * cy := (mul_assoc t cx cy).symm
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [h1, h2, hcomm]

private lemma lineComm_of_card_le_two {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (S : Sylow 2 ↥H)
    (hcard : letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 ^ n) (hn : n ≤ 1) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
      ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
        ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
          ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  let : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  let : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  let : MulAction ↥H W := MulAction.compHom W H.subtype
  let : MulAction ↥H (Set W) := Set.mulActionSet
  have htwo : ∀ v w : W, v ∈ CFSG.fixedPointSubgroup ↥S W →
      w ∈ CFSG.fixedPointSubgroup ↥S W → v ≠ 1 → w ≠ 1 → v = w := by
    intro v w hv hw hv1 hw1
    have hne : Nat.card (CFSG.fixedPointSubgroup ↥S W) ≠ 1 := by
      intro h1
      have hbot : CFSG.fixedPointSubgroup ↥S W = ⊥ := Subgroup.card_eq_one.mp h1
      rw [hbot] at hv
      exact hv1 (Subgroup.mem_bot.mp hv)
    have hn1 : n = 1 := by
      rcases n with _ | m
      · simp only [pow_zero] at hcard
        exact absurd hcard hne
      · omega
    have h2 : Nat.card (CFSG.fixedPointSubgroup ↥S W) = 2 := by
      rw [hn1] at hcard
      simpa using hcard
    obtain ⟨z, -, huniq⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥(CFSG.fixedPointSubgroup ↥S W))).mp h2
    have hv' : (⟨v, hv⟩ : ↥(CFSG.fixedPointSubgroup ↥S W)) ≠ 1 :=
      fun hc => hv1 (congrArg Subtype.val hc)
    have hw' : (⟨w, hw⟩ : ↥(CFSG.fixedPointSubgroup ↥S W)) ≠ 1 :=
      fun hc => hw1 (congrArg Subtype.val hc)
    exact congrArg Subtype.val ((huniq ⟨v, hv⟩ hv').trans (huniq ⟨w, hw⟩ hw').symm)
  have hfix : ∀ a ∈ KTabD.pointStab H S, ∀ w ∈ CFSG.fixedPointSubgroup ↥S W,
      a • w = w := by
    intro a ha w hw
    by_cases hw1 : w = 1
    · subst hw1
      exact MulDistribMulAction.smul_one a
    · have ha' : a ∈ MulAction.stabilizer ↥H
          ((CFSG.fixedPointSubgroup ↥S W : Subgroup W) : Set W) := ha
      have hw' : a • w ∈ CFSG.fixedPointSubgroup ↥S W :=
        (MulAction.mem_stabilizer_set.mp ha' w).2 hw
      have hne : a • w ≠ 1 := by
        intro h0
        exact hw1 (smul_left_cancel a (h0.trans (MulDistribMulAction.smul_one a).symm))
      exact htwo _ _ hw' hw hne hw1
  intro x hx y hy v hv
  change x • (y • v) = y • (x • v)
  rw [hfix y hy v hv, hfix x hx v hv, hfix y hy v hv]

private lemma lineComm_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n d : ℕ} (hd : 2 ≤ d)
    (h : BinaryNaturalSL H ⊤ ⊥ d n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
      ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
        ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
          ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have : NeZero d := ⟨by omega⟩
  exact commute_on_fixedPointSubgroup_of_sylowFixedLine (K := K) hR
    (KTabD.sylowFixedLine_statedSL (K := K) hd) S

private lemma lineComm_of_natSpn {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hN : 0 < N / 2)
    (h : NatSpn H ⊤ ⊥ N n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
      ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
        ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
          ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have : NeZero (N / 2) := ⟨by omega⟩
  exact commute_on_fixedPointSubgroup_of_sylowFixedLine (K := K) hR
    (KTabD.sylowFixedLine_statedSp (K := K) (N / 2)) S

private lemma lineComm_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n N : ℕ} (hm : 2 ≤ N / 2)
    (h : NatOmegaMinus H ⊤ ⊥ N n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
      ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
        ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
          ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  exact commute_on_fixedPointSubgroup_of_sylowFixedLine (K := K) hR
    (KTabD.sylowFixedLine_omegaMinus (K := K) (m := N / 2) hm hirr) S

private lemma lineComm_of_natOmegaPlusFour {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hn : 2 ≤ n)
    (h : NatOmegaPlus H ⊤ ⊥ 4 n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
      ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
        ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
          ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [show 4 / 2 = 2 by norm_num] at hR
  exact commute_on_fixedPointSubgroup_of_sylowFixedLine (K := K) hR
    (KTabC.sylowFixedLine_plus (K := K) hK4) S

private lemma lineComm_of_natOmegaPlusSix {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (h : NatOmegaPlus H ⊤ ⊥ 6 n) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
      ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
        ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
          ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 6 / 2 = 3 by norm_num] at hR
  exact commute_on_fixedPointSubgroup_of_sylowFixedLine (K := K) hR
    (KGenO6pProof.sylowFixedLine_omegaPlusSix K) S

private lemma lineComm_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
      ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
        ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
          ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (hK.trans (pow_mul 2 a 2).symm)
  exact commute_on_fixedPointSubgroup_of_sylowFixedLine (K := K) hR
    (KGenProof.sylowFixedLine_statedSU_four (K := K) hK) S

theorem kLineComm_holds :
    ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      IsNaturalClassicalModule H n → ⁅H, H⁆ = H → ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        ∀ x ∈ KTabD.pointStab H S, ∀ y ∈ KTabD.pointStab H S,
          ∀ v ∈ CFSG.fixedPointSubgroup ↥S W,
            ((x : ↥H) : MulAut W) (((y : ↥H) : MulAut W) v) =
              ((y : ↥H) : MulAut W) (((x : ↥H) : MulAut W) v) := by
  intro W _ _ H n hN hperf S
  obtain ⟨hcard, -, -⟩ := kTab23a_holds W H n hN hperf S
  by_cases hn : n ≤ 1
  · exact lineComm_of_card_le_two S hcard hn
  · have hn2 : 2 ≤ n := by omega
    rcases hN with h | h | h | h | h | h | h | h | h | h | h
    · exact lineComm_of_binaryNaturalSL (d := 2) (by norm_num) h.2 S
    · exact lineComm_of_natOmegaMinus (N := 4) (by norm_num) h.2 S
    · exact lineComm_of_natOmegaPlusFour hn2 h.2 S
    · exact lineComm_of_natSpn (N := 4) (by norm_num) h.2 S
    · exact lineComm_of_binaryNaturalSL (d := 3) (by norm_num) h.2 S
    · obtain ⟨a, -, -, hNat⟩ := h
      exact lineComm_of_natSUn hNat S
    · exact lineComm_of_natOmegaMinus (N := 6) (by norm_num) h.2 S
    · exact lineComm_of_binaryNaturalSL (d := 4) (by norm_num) h.2 S
    · exact lineComm_of_natOmegaPlusSix h.2 S
    · exact lineComm_of_natSpn (N := 6) (by norm_num) h.2 S
    · exact lineComm_of_natOmegaMinus (N := 8) (by norm_num) h.2 S

end CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC
