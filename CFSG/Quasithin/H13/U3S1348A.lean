module

public import CFSG.Quasithin.H13.A6S13227
public import CFSG.Quasithin.H13.U3S1344A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem inf_eq_pCoreOf_of_sylow {H C Lp R : Subgroup G} (hCH : C ≤ H)
    (hCn : H ≤ normalizer (C : Set G)) (hLpH : Lp ≤ H) (hHLp : H ≤ normalizer (Lp : Set G))
    (hLp : oTwoRes C ≤ Lp) (hOLp : pCoreOf 2 Lp ≤ pCoreOf 2 H) (hOC : pCoreOf 2 H ≤ C)
    (hR : IsSylowTwoOf R (centralizerMod (pCoreOf 2 Lp) H Lp)) :
    R ⊓ C = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₁ := centralizerMod (pCoreOf 2 Lp) H Lp with hH₁def
  have hH₁H : H₁ ≤ H := fun x hx => hx.1
  have hOLpn : H ≤ normalizer (pCoreOf 2 Lp : Set G) :=
    hHLp.trans (normalizer_le_normalizer_pCoreOf 2 Lp)
  have hH₁n : H ≤ normalizer (H₁ : Set G) :=
    le_normalizer_centralizerMod hOLpn le_normalizer hHLp
  have hOH₁ : pCoreOf 2 H ≤ H₁ := by
    intro x hx
    have hxH := pCoreOf_le 2 H hx
    refine ⟨hxH, hOLpn hxH, fun y hy => ?_⟩
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ Lp := by
      have := (mem_normalizer_iff.mp (hHLp hxH) y).mp hy
      exact mul_mem this (inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H := by
      have := (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hLpH hy)) x⁻¹).mp (inv_mem hx)
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hx this
    exact le_pCoreOf_of_le_normalizer 2 (inf_le_left : Lp ⊓ pCoreOf 2 H ≤ Lp)
      (fun l hl => mem_normalizer_inf_of (le_normalizer hl)
        (le_normalizer_pCoreOf 2 H (hLpH hl)))
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right) ⟨h1, h2⟩
  have hOR : pCoreOf 2 H ≤ R := by
    refine le_trans ?_ (pCoreOf_two_le_of_isSylowTwoOf hR)
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hOH₁
      ((normal_subgroupOf_iff_le_normalizer hOH₁).2 (hH₁H.trans
        (le_normalizer_pCoreOf 2 H))) (pCoreOf_isPGroup 2 H)
  apply le_antisymm _ (le_inf hOR hOC)
  set S₀ := R ⊓ C with hS₀
  have hS₀le : S₀ ≤ C ⊓ H₁ := le_inf inf_le_right (inf_le_left.trans hR.1)
  have hsyl : IsSylowTwoOf S₀ (C ⊓ H₁) := by
    have h := A4.isSylowTwoOf_inf_normal hR (inf_le_right : C ⊓ H₁ ≤ H₁)
      (fun x hx => mem_normalizer_inf_of (hCn (hH₁H hx)) (le_normalizer hx))
    have e : R ⊓ (C ⊓ H₁) = S₀ := by
      rw [hS₀, inf_comm C H₁, ← inf_assoc, inf_eq_left.2 hR.1]
    rwa [e] at h
  have hOS₀ : pCoreOf 2 Lp ≤ S₀ := le_inf (hOLp.trans hOR) (hOLp.trans hOC)
  have hNS : C ⊓ H₁ ≤ normalizer (S₀ : Set G) := by
    have hsup := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
    refine hsup.symm.le.trans (sup_le ?_ le_normalizer)
    rw [← oTwoRes_eq_oTwoUpper]
    have hle : oTwoRes (C ⊓ H₁) ≤ Lp := (oTwoRes_mono inf_le_left).trans hLp
    refine A5.le_normalizer_of_forall_conj_mem fun y hy s hs => ?_
    have hyLp := hle hy
    have hsH₁ : s ∈ H₁ := hS₀le hs |>.2
    have h1 := hsH₁.2.2 y hyLp
    have e : y * s * y⁻¹ = (s * y * s⁻¹ * y⁻¹)⁻¹ * s := by group
    rw [e]
    exact mul_mem (inv_mem (hOS₀ h1)) hs
  have hS₀O : S₀ ≤ pCoreOf 2 (C ⊓ H₁) :=
    le_pCoreOf_of_le_normalizer 2 hS₀le hNS hsyl.2.1
  refine hS₀O.trans ?_
  refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
    ((pCoreOf_le 2 _).trans (inf_le_left.trans hCH)) ?_ (pCoreOf_isPGroup 2 _)
  refine (normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 2 _).trans
    (inf_le_left.trans hCH))).2 ?_
  have hHN : H ≤ normalizer ((C ⊓ H₁ : Subgroup G) : Set G) := fun h hh =>
    mem_normalizer_inf_of (hCn hh) (hH₁n hh)
  exact hHN.trans (normalizer_le_normalizer_pCoreOf 2 _)

variable {T L V : Subgroup G}

theorem s134_inHz_facts (S : A6.Setting134 G T L V) {z : G} {H : Subgroup G}
    (hHz : InHz T L V z H) :
    IsSylowTwoOf T H ∧ L₁Of L (fsuV1 T V) ⊔ T ≤ H ∧ H ≤ centralizer ({z} : Set G) ∧
      pCoreOf 2 H ≠ ⊥ ∧ ¬ H ≤ normalizer (L : Set G) := by
  obtain ⟨⟨hL1TH, hO2H⟩, hHzC, hHM⟩ := hHz
  exact ⟨A5.isSylowTwoOf_of_le S.h13.sylow (le_sup_right.trans hL1TH), hL1TH, hHzC, hO2H, hHM⟩

omit [Finite G] in
theorem le_pCoreOf_of_reduced {H VH : Subgroup G} (hred : IsTwoReducedIn H VH) :
    VH ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1
    (B2F.isPGroup_of_isElemAbelian hred.2.2.1)

theorem pCoreOf_le_centralizer_of_reduced' {H VH : Subgroup G} (hred : IsTwoReducedIn H VH) :
    pCoreOf 2 H ≤ centralizer (VH : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hred.2.2.2 _ (pCoreOf_le 2 H) (le_normalizer_pCoreOf 2 H) fun d hd => ?_
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact one_mem _

theorem s134_r1Of_inf_centralizer (S : A6.Setting134 G T L V) {z : G} {H VH : Subgroup G}
    (hHz : InHz T L V z H) (hred : IsTwoReducedIn H VH)
    (h44 : (oTwoRes (H ⊓ centralizer (VH : Set G)) = ⊥ ∧
        H ⊓ centralizer (VH : Set G) = pCoreOf 2 H ∧
        pCoreOf 2 H ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧
        pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ r1Of T L V) ∨
      ∃ Lp : Subgroup G,
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
          Lp = L₁Of L (fsuV1 T V)) ∧
        (IsHatA6 L → Lp = l1plus T L V) ∧
        Lp = oTwoRes (H ⊓ centralizer (VH : Set G)) ∧ H ≤ normalizer (Lp : Set G) ∧
        (centralizerMod (pCoreOf 2 Lp) H Lp).relIndex H = 2 ∧
        IsSylowTwoOf (r1Of T L V) (centralizerMod (pCoreOf 2 Lp) H Lp)) :
    r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTsyl, hL1TH, -, -, -⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hRH : r1Of T L V ≤ H := (r1Of_le_T T L V).trans hTH
  have hOC : pCoreOf 2 H ≤ H ⊓ centralizer (VH : Set G) :=
    le_inf (pCoreOf_le 2 H) (pCoreOf_le_centralizer_of_reduced' hred)
  have hCn : H ≤ normalizer ((H ⊓ centralizer (VH : Set G) : Subgroup G) : Set G) :=
    fun h hh => mem_normalizer_inf_of (le_normalizer hh)
      (mem_normalizer_centralizer_of_mem (hred.2.1 hh))
  have e : r1Of T L V ⊓ centralizer (VH : Set G) =
      r1Of T L V ⊓ (H ⊓ centralizer (VH : Set G)) := by
    rw [← inf_assoc, inf_eq_left.2 hRH]
  rw [e]
  rcases h44 with ⟨-, hC, hOL, hLR⟩ | ⟨Lp, -, -, hLp, hHLp, -, hsyl⟩
  · rw [hC]
    exact inf_eq_right.2 (hOL.trans hLR)
  · have hLpH : Lp ≤ H := by rw [hLp]; exact (oTwoRes_le _).trans inf_le_left
    have hOLp : pCoreOf 2 Lp ≤ pCoreOf 2 H :=
      CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
        ((pCoreOf_le 2 Lp).trans hLpH)
        ((normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 2 Lp).trans hLpH)).2
          (hHLp.trans (normalizer_le_normalizer_pCoreOf 2 Lp))) (pCoreOf_isPGroup 2 Lp)
    exact inf_eq_pCoreOf_of_sylow inf_le_left hCn hLpH hHLp hLp.symm.le hOLp hOC hsyl

omit [Finite G] in
theorem s134_VH_le_r1Of {H VH : Subgroup G} (hred : IsTwoReducedIn H VH)
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H) :
    VH ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ r1Of T L V :=
  ⟨le_pCoreOf_of_reduced hred, hcR.symm.le.trans inf_le_left⟩

end CFSG.Quasithin.H13.U3
