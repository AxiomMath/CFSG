module

public import CFSG.Quasithin.Recognition.SzR1Kernel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F112W
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace SzR1

section Aux

variable {Ω : Type}

theorem exists_two_ne [Fintype Ω] [DecidableEq Ω] (hΩ : 4 ≤ Fintype.card Ω) (pt i : Ω) :
    ∃ j k : Ω, j ≠ pt ∧ k ≠ pt ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  set t : Finset Ω := (Finset.univ.erase pt).erase i with ht
  have h1 : 1 < t.card := by
    have a1 : (Finset.univ.erase pt).card = Fintype.card Ω - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have a2 : (Finset.univ.erase pt).card - 1 ≤ t.card := Finset.pred_card_le_card_erase
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp h1
  simp only [ht, Finset.mem_erase, Finset.mem_univ, and_true] at hj hk
  exact ⟨j, k, hj.2, hk.2, fun h => hj.1 h.symm, fun h => hk.1 h.symm, hjk⟩

theorem exists_triple [Fintype Ω] [DecidableEq Ω] (hΩ : 4 ≤ Fintype.card Ω) (pt : Ω) :
    ∃ i j k : Ω, i ≠ pt ∧ j ≠ pt ∧ k ≠ pt ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (by omega) pt
  obtain ⟨j, k, hj, hk, hij, hik, hjk⟩ := exists_two_ne hΩ pt i
  exact ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩

end Aux

namespace FamCtx

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω)

include C

theorem amalgamHypV :
    AmalgamHypV (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) S (conjClosure Zs L2) := by
  have := F112J2.amalgamHypV_thesis C.hR (F112J2.zs_le_omegaOneCenter C.h) C.h.s3
    C.h.Z_not_norm
  rwa [F112J2.conjClosure_sup_S C.h.hyp.h2.normalizes (F112J2.S_le_centralizer_Z C.h)] at this

theorem isNaturalS3 : IsNaturalS3 (L2 ⊔ S) (conjClosure Zs L2) := by
  have hc := F112J2.conjClosure_sup_S C.h.hyp.h2.normalizes (F112J2.S_le_centralizer_Z C.h)
  have := F112J2.isNaturalS3_thesis C.hR (F112J2.zs_le_omegaOneCenter C.h) C.h.s3
    C.h.Z_not_norm (by rw [hc]; exact C.h.V_card)
  rwa [hc] at this

theorem pCore_eq :
    pCoreOf 2 (L2 ⊔ S) = S ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) :=
  pCoreOf_eq_inf_centralizer C.amalgamHypV

theorem mem_pCore_iff {x : G} :
    x ∈ pCoreOf 2 (L2 ⊔ S) ↔ x ∈ S ∧ ∀ v ∈ conjClosure Zs L2, v * x = x * v := by
  rw [C.pCore_eq, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem pCore_le_S : pCoreOf 2 (L2 ⊔ S) ≤ S := isSylowTwoOf_pCoreOf_le C.amalgamHypV.sylow₁

theorem vBeta_le_S : vBeta K1 L2 S Zs ≤ S := by
  have h1 : conjClosure (conjClosure Zs L2) (K1 ⊔ S) ≤ pCoreOf 2 (K1 ⊔ S) :=
    conjClosure_le_pCoreOf_G₂ C.h.V_le
  exact h1.trans (isSylowTwoOf_pCoreOf_le C.amalgamHypV.sylow₂)

theorem zf_mul_zf_comm_pt {i j : Ω} (hi : i ≠ C.D.pt) (hj : j ≠ C.D.pt) :
    (C.zf i * C.zf j) * C.zf C.D.pt = C.zf C.D.pt * (C.zf i * C.zf j) := by
  set p := C.D.pt with hp
  have e1 : C.zf i * C.zf p = C.cm i p * (C.zf p * C.zf i) := by
    unfold FamCtx.cm
    group
  have e2 : C.zf j * C.zf p = C.cm j p * (C.zf p * C.zf j) := by
    unfold FamCtx.cm
    group
  have hcc : C.cm j p = C.cm i p := C.cm_const hi hj
  have hcz : C.zf i * C.cm i p = C.cm i p * C.zf i := C.Zs_central (C.zf_mem_U i) (C.cm_mem i p)
  have hcsq : C.cm i p * C.cm i p = 1 := C.Zs_sq (C.cm_mem i p)
  calc (C.zf i * C.zf j) * C.zf p = C.zf i * (C.zf j * C.zf p) := by rw [mul_assoc]
    _ = C.zf i * (C.cm i p * (C.zf p * C.zf j)) := by rw [e2, hcc]
    _ = C.cm i p * (C.zf i * (C.zf p * C.zf j)) := by rw [← mul_assoc, hcz, mul_assoc]
    _ = C.cm i p * ((C.cm i p * (C.zf p * C.zf i)) * C.zf j) := by
        rw [← mul_assoc (C.zf i), e1]
    _ = (C.cm i p * C.cm i p) * (C.zf p * (C.zf i * C.zf j)) := by group
    _ = C.zf p * (C.zf i * C.zf j) := by rw [hcsq, one_mul]

theorem zf_mul_mem_pCore {i j : Ω} (hi : i ≠ C.D.pt) (hj : j ≠ C.D.pt) :
    C.zf i * C.zf j ∈ pCoreOf 2 (L2 ⊔ S) := by
  rw [C.mem_pCore_iff]
  have hW : C.zf i * C.zf j ∈ vBeta K1 L2 S Zs :=
    (vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U j)
  refine ⟨C.vBeta_le_S hW, fun v hv => ?_⟩
  rw [← C.Vf_pt] at hv
  rcases C.Vf_eq hv with h1 | h1
  · exact (C.Zs_central hW h1).symm
  · have hc := (C.Zs_central hW h1).symm
    have hcomm := C.zf_mul_zf_comm_pt hi hj
    have hv' : v = C.zf C.D.pt * ((C.zf C.D.pt)⁻¹ * v) := by group
    rw [hv']
    calc C.zf C.D.pt * ((C.zf C.D.pt)⁻¹ * v) * (C.zf i * C.zf j)
        = C.zf C.D.pt * (((C.zf C.D.pt)⁻¹ * v) * (C.zf i * C.zf j)) := by rw [mul_assoc]
      _ = C.zf C.D.pt * ((C.zf i * C.zf j) * ((C.zf C.D.pt)⁻¹ * v)) := by rw [hc]
      _ = (C.zf C.D.pt * (C.zf i * C.zf j)) * ((C.zf C.D.pt)⁻¹ * v) := by rw [← mul_assoc]
      _ = ((C.zf i * C.zf j) * C.zf C.D.pt) * ((C.zf C.D.pt)⁻¹ * v) := by rw [hcomm]
      _ = (C.zf i * C.zf j) * (C.zf C.D.pt * ((C.zf C.D.pt)⁻¹ * v)) := by rw [mul_assoc]

theorem not_zf_mem_pCore {j : Ω} (hj : j ≠ C.D.pt) : C.zf j ∉ pCoreOf 2 (L2 ⊔ S) := by
  intro h
  rw [C.mem_pCore_iff] at h
  have hv : C.zf C.D.pt ∈ conjClosure Zs L2 := by
    rw [← C.Vf_pt]
    exact C.zf_mem C.D.pt
  have h1 := h.2 _ hv
  apply C.cm_ne_one hj
  calc C.cm j C.D.pt = (C.zf j * C.zf C.D.pt) * (C.zf j)⁻¹ * (C.zf C.D.pt)⁻¹ := rfl
    _ = (C.zf C.D.pt * C.zf j) * (C.zf j)⁻¹ * (C.zf C.D.pt)⁻¹ := by rw [h1]
    _ = 1 := by group

theorem not_vBeta_le_pCore [Fintype Ω] [DecidableEq Ω] (hΩ : 4 ≤ Fintype.card Ω) :
    ¬ vBeta K1 L2 S Zs ≤ pCoreOf 2 (L2 ⊔ S) := by
  obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card (by omega) C.D.pt
  exact fun h => C.not_zf_mem_pCore hi (h (C.zf_mem_U i))

theorem commutator_vBeta_inf_pCore_ne_bot [Fintype Ω] [DecidableEq Ω] (hΩ : 4 ≤ Fintype.card Ω)
    {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) :
    ⁅vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S), vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S)⁆ ≠ ⊥ := by
  obtain ⟨i, j, k, hi, hj, hk, hij', hik, hjk⟩ := exists_triple hΩ C.D.pt
  have ha : C.zf i * C.zf j ∈ vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S) :=
    ⟨(vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U j), C.zf_mul_mem_pCore hi hj⟩
  have hb : C.zf i * C.zf k ∈ vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S) :=
    ⟨(vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U k), C.zf_mul_mem_pCore hi hk⟩
  intro hbot
  have hmem := Subgroup.commutator_mem_commutator ha hb
  rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
  have hG := C.gramRel hij
  have hcomm : (C.zf i * C.zf j) * (C.zf i * C.zf k) =
      C.cm i₀ j₀ * ((C.zf i * C.zf k) * (C.zf i * C.zf j)) :=
    congrArg Subtype.val (hG.pair_comm_ne hij' hik hjk)
  apply C.cm_ne_one hij
  calc C.cm i₀ j₀ = ((C.zf i * C.zf j) * (C.zf i * C.zf k)) *
        ((C.zf i * C.zf k) * (C.zf i * C.zf j))⁻¹ := by rw [hcomm]; group
    _ = (C.zf i * C.zf j) * (C.zf i * C.zf k) * (C.zf i * C.zf j)⁻¹ * (C.zf i * C.zf k)⁻¹ := by
        group
    _ = 1 := hmem

theorem mem_kerM_of_mem_pCore [Fintype Ω] [DecidableEq Ω] (hΩ : 4 ≤ Fintype.card Ω)
    {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) {s : G} (hs : s ∈ pCoreOf 2 (L2 ⊔ S))
    (hfix : ∀ w ∈ vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S), s * w * s⁻¹ * w⁻¹ ∈ Zs) :
    s ∈ C.kerM := by
  refine C.mem_kerM_of_fix hij (fun i _ => exists_two_ne hΩ C.D.pt i) (C.pCore_le_S hs) ?_
  intro i j hi hj _
  have hW : C.zf i * C.zf j ∈ vBeta K1 L2 S Zs :=
    (vBeta K1 L2 S Zs).mul_mem (C.zf_mem_U i) (C.zf_mem_U j)
  refine ⟨_, hfix _ ⟨hW, C.zf_mul_mem_pCore hi hj⟩, ?_⟩
  group

section Center

variable [Fintype Ω] [DecidableEq Ω]

theorem K1_centralizes_center (hodd : Odd (Fintype.card Ω)) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀)
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀) {x : G}
    (hxW : x ∈ vBeta K1 L2 S Zs) (hxc : ∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) :
    ∀ k ∈ K1, k * x = x * k := by
  intro k hk
  have hzpow : ∀ b : ℕ, (C.cm i₀ j₀) ^ b ∈ Zs := fun b => Zs.pow_mem (C.cm_mem i₀ j₀) b
  have hkz : ∀ b : ℕ, k * (C.cm i₀ j₀) ^ b = (C.cm i₀ j₀) ^ b * k := fun b =>
    (Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) _ (hzpow b)).symm
  rcases C.center_dichotomy hij l₀ hl₀ hall hxW hxc with ⟨b, hb⟩ | ⟨b, hb⟩
  · rw [hb]
    exact hkz b
  · by_cases hyZ : ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ∈ Zs
    · have hx : x ∈ Zs := by
        rw [hb]
        exact Zs.mul_mem (hzpow b) hyZ
      exact (Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) x hx).symm
    · have hKy := C.centralizes_y hodd hij l₀ hl₀ hall hyZ k hk
      rw [hb]
      calc k * ((C.cm i₀ j₀) ^ b * ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G))
          = (k * (C.cm i₀ j₀) ^ b) * ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) := by
            rw [mul_assoc]
        _ = ((C.cm i₀ j₀) ^ b * k) * ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) := by
            rw [hkz b]
        _ = (C.cm i₀ j₀) ^ b * (k * ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G)) := by
            rw [mul_assoc]
        _ = (C.cm i₀ j₀) ^ b * (((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) * k) := by
            rw [hKy]
        _ = ((C.cm i₀ j₀) ^ b * ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G)) * k := by
            rw [mul_assoc]

end Center

end FamCtx

end SzR1

end CFSG.Quasithin
