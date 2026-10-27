module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318H

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_mulSingle_mem {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (S : Subgroup (ι → Multiplicative (κ → ZMod 2)))
    (h : ∀ (i : ι) (j : κ),
      Pi.mulSingle i (Multiplicative.ofAdd (Pi.single j (1 : ZMod 2) : κ → ZMod 2)) ∈ S) :
    S = ⊤ := by
  let e : Multiplicative (ι → κ → ZMod 2) →* (ι → Multiplicative (κ → ZMod 2)) :=
    { toFun := fun x i => Multiplicative.ofAdd (Multiplicative.toAdd x i)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Function.Surjective e := fun c =>
    ⟨Multiplicative.ofAdd fun i => Multiplicative.toAdd (c i), rfl⟩
  have h1 := eq_top_of_single_mem (S.comap e) fun i j => by
    show e (Multiplicative.ofAdd (Pi.single i (Pi.single j 1))) ∈ S
    have : e (Multiplicative.ofAdd (Pi.single i (Pi.single j 1))) =
        Pi.mulSingle i (Multiplicative.ofAdd (Pi.single j 1)) := by
      funext i'
      by_cases hi : i' = i
      · subst hi
        simp [e]
      · simp [e, Pi.single_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
    rw [this]
    exact h i j
  rw [eq_top_iff]
  intro c _
  obtain ⟨x, rfl⟩ := he c
  have : x ∈ S.comap e := h1 ▸ Subgroup.mem_top x
  exact this

namespace Data

variable {T M L D : Subgroup G} {n k : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)}
  {Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)}

theorem comm_transvection (hD : Data G T M L D n k α Φ) {l : ↥L} {a b : Fin n} (hab : a ≠ b)
    (hl : α l = SpecialLinearGroup.transvection hab (1 : ZMod 2)) (i : Fin k) :
    ⁅(l : G), (Φ (Pi.mulSingle i (Multiplicative.ofAdd (Pi.single b 1))) : G)⁆ =
      (Φ (Pi.mulSingle i (Multiplicative.ofAdd (Pi.single a 1))) : G) := by
  classical
  set c : Fin k → Multiplicative (Fin n → ZMod 2) :=
    Pi.mulSingle i (Multiplicative.ofAdd (Pi.single b 1)) with hc
  set ca : Fin k → Multiplicative (Fin n → ZMod 2) :=
    Pi.mulSingle i (Multiplicative.ofAdd (Pi.single a 1)) with hca
  have hconj : (l : G) * (Φ c : G) * (l : G)⁻¹ = (Φ c : G) * (Φ ca : G) := by
    rw [hD.equiv, hl, ← Subgroup.coe_mul, ← map_mul]
    congr 2
    rw [hc, vecAct_mulSingle, hca, ← Pi.mulSingle_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
    have := SpecialLinearGroup.transvection_smul_single_snd hab (1 : ZMod 2)
    rw [Matrix.SpecialLinearGroup.smul_def, one_smul] at this
    exact this
  rw [commutatorElement_def, hconj]
  have hab' := (Hyp331.vPlus_reduced hD.hyp.toSetup331).2.1
  have := congrArg Subtype.val (hab'.1.is_comm.comm (Φ c) (Φ ca))
  simp only [Subgroup.coe_mul] at this
  rw [this]
  group

theorem commV_le_commutator (hD : Data G T M L D n k α Φ) :
    ⁅vPlus L T, L⁆ ≤ ⁅⁅vPlus L T, L⁆, liftCore α (flagStabilizer n (ZMod 2) {1})⁆ := by
  classical
  have hn := hD.n4
  set S := (⁅⁅vPlus L T, L⁆, liftCore α (flagStabilizer n (ZMod 2) {1})⁆).comap
    ((vPlus L T).subtype.comp Φ) with hS
  have hS' : S = ⊤ := by
    refine eq_top_of_mulSingle_mem S fun i a => ?_
    show (Φ (Pi.mulSingle i (Multiplicative.ofAdd (Pi.single a 1))) : G) ∈
      ⁅⁅vPlus L T, L⁆, liftCore α (flagStabilizer n (ZMod 2) {1})⁆
    obtain ⟨b, hb, hab⟩ : ∃ b : Fin n, (if (a : ℕ) = 0 then (b : ℕ) = 1 else
        (1 ≤ (b : ℕ) ∧ b ≠ a)) ∧ a ≠ b := by
      by_cases ha : (a : ℕ) = 0
      · refine ⟨⟨1, by omega⟩, by simp [ha], fun e => ?_⟩
        have := congrArg Fin.val e
        simp at this
        omega
      · by_cases ha1 : (a : ℕ) = 1
        · refine ⟨⟨2, by omega⟩, ?_, fun e => ?_⟩
          · rw [ite_eq_right ha]
            refine ⟨by simp, fun e => ?_⟩
            have := congrArg Fin.val e
            simp at this
            omega
          · have := congrArg Fin.val e
            simp at this
            omega
        · refine ⟨⟨1, by omega⟩, ?_, fun e => ?_⟩
          · rw [ite_eq_right ha]
            refine ⟨by simp, fun e => ?_⟩
            have := congrArg Fin.val e
            simp at this
            omega
          · have := congrArg Fin.val e
            simp at this
            omega
    have hmem : SpecialLinearGroup.transvection hab (1 : ZMod 2) ∈
        perfectCore (flagStabilizer n (ZMod 2) {1}) := by
      by_cases ha : (a : ℕ) = 0
      · rw [ite_eq_left ha] at hb
        exact transvection_mem_perfectCore_one hn ha (by omega) hab
      · rw [ite_eq_right ha] at hb
        exact transvection_mem_perfectCore_levi_one hn (by omega) hb.1 hab
    obtain ⟨y, hyY, hye⟩ := exists_mem_liftCore hD.surj hmem
    rw [← hD.comm_transvection hab hye i, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hyY (hD.mem_commV _)
  intro x hx
  obtain ⟨c, rfl⟩ := hD.exists_eq hx
  have : c ∈ S := hS' ▸ Subgroup.mem_top c
  exact this

theorem le_normalizer_commV (hD : Data G T M L D n k α Φ) :
    L ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun _ hl =>
  Ch1Sec3.commutator_le_normalizer
    ((le_sup_left.trans (Hyp331.vPlus_reduced hD.hyp.toSetup331).2.2.2.1) hl)
    (Subgroup.le_normalizer hl)

theorem le_C (hD : Data G T M L D n k α Φ)
    (hY₂ : ⁅pCoreOf 2 L, liftCore α (flagStabilizer n (ZMod 2) {3})⁆ ≤ ⁅vPlus L T, L⁆) :
    ⁅pCoreOf 2 L, liftCore α (flagStabilizer n (ZMod 2) {1})⁆ ≤ ⁅vPlus L T, L⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hD.n4
  set W := ⁅vPlus L T, L⁆ with hW
  set O := pCoreOf 2 L with hO
  have hWN := hD.le_normalizer_commV
  have hON : L ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  let C : Subgroup G :=
    { carrier := {l | l ∈ L ∧ ∀ x ∈ O, x * l * x⁻¹ * l⁻¹ ∈ W}
      one_mem' := ⟨L.one_mem, fun x _ => by simp⟩
      mul_mem' := fun {l l'} hl hl' => ⟨L.mul_mem hl.1 hl'.1, fun x hx => by
        have h1 := hl.2 x hx
        have h2 := hl'.2 x hx
        have h3 := (Subgroup.mem_normalizer_iff.mp (hWN hl.1) _).mp h2
        have : x * (l * l') * x⁻¹ * (l * l')⁻¹ =
            (x * l * x⁻¹ * l⁻¹) * (l * (x * l' * x⁻¹ * l'⁻¹) * l⁻¹) := by group
        rw [this]
        exact W.mul_mem h1 h3⟩
      inv_mem' := fun {l} hl => ⟨L.inv_mem hl.1, fun x hx => by
        have h1 := hl.2 x hx
        have h2 := (Subgroup.mem_normalizer_iff.mp (hWN (L.inv_mem hl.1)) _).mp (W.inv_mem h1)
        have : x * l⁻¹ * x⁻¹ * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹ * l⁻¹)⁻¹ * l⁻¹⁻¹ := by group
        rw [this]
        exact h2⟩ }
  have hCL : C ≤ L := fun l hl => hl.1
  have hCN : (C.subgroupOf L).Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨L.mul_mem (L.mul_mem g.2 hc.1) (L.inv_mem g.2), fun x hx => ?_⟩
    have hx' : (g : G)⁻¹ * x * g ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hON (L.inv_mem g.2)) x).mp hx
      simpa using this
    have h1 := hc.2 _ hx'
    have h2 := (Subgroup.mem_normalizer_iff.mp (hWN g.2) _).mp h1
    have : x * ((g : G) * c * (g : G)⁻¹) * x⁻¹ * ((g : G) * c * (g : G)⁻¹)⁻¹ =
        (g : G) * (((g : G)⁻¹ * x * g) * c * ((g : G)⁻¹ * x * g)⁻¹ * (c : G)⁻¹) *
          (g : G)⁻¹ := by
      group
    rw [this]
    exact h2
  have hY₂C : liftCore α (flagStabilizer n (ZMod 2) {3}) ≤ C := fun y hy =>
    ⟨liftCore_le α _ hy, fun x hx => hY₂ (by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hx hy)⟩
  have hαC : (C.subgroupOf L).map α = ⊤ := by
    have hS := sl_isSimple_of_card_two (Nat.card_zmod 2) (m := n) (by omega)
    have hnorm : ((C.subgroupOf L).map α).Normal := hCN.map α hD.surj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C.subgroupOf L).map α) with h | h
    · exfalso
      have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun e => by
        have := congrArg Fin.val e
        simp at this
      have hmem : SpecialLinearGroup.transvection hab (1 : ZMod 2) ∈
          perfectCore (flagStabilizer n (ZMod 2) {3}) := by
        rw [transvection_eq_liftT (by omega) (by simp) (by simp) hab]
        exact Ln2.liftT_mem_perfectCore (by omega) le_rfl (by
          intro c hc
          rw [Set.mem_singleton_iff] at hc
          omega) _
      obtain ⟨y, hyY, hye⟩ := exists_mem_liftCore hD.surj hmem
      have h1 : α ⟨y, liftCore_le α _ hyY⟩ ∈ (C.subgroupOf L).map α :=
        ⟨⟨y, liftCore_le α _ hyY⟩, Subgroup.mem_subgroupOf.mpr (hY₂C hyY), rfl⟩
      rw [h, Subgroup.mem_bot, hye] at h1
      have h2 := congrFun (congrFun (congrArg Subtype.val h1) ⟨0, by omega⟩) ⟨1, by omega⟩
      simp [SpecialLinearGroup.transvection_coe] at h2
    · exact h
  set P := liftPre α (flagStabilizer n (ZMod 2) {1}) with hP
  have hOP : O ≤ P := by
    intro x hx
    have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ α.ker := by
      rw [hD.ker]
      exact (Lem3328.mem_pCore_iff _).mpr hx
    exact ⟨⟨x, hxL⟩, by
      show α ⟨x, hxL⟩ ∈ flagStabilizer n (ZMod 2) {1}
      rw [show α ⟨x, hxL⟩ = 1 from h1]
      exact Subgroup.one_mem _, rfl⟩
  have hPL : P ≤ L := L3316.liftPre_le α _
  have hPeq : P = (P ⊓ C) ⊔ O := by
    refine le_antisymm (fun y hy => ?_) (sup_le inf_le_left hOP)
    have hyL := hPL hy
    have : α ⟨y, hyL⟩ ∈ (C.subgroupOf L).map α := hαC ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hce⟩ := this
    have hc' : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
    have ho : c⁻¹ * ⟨y, hyL⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
    rw [hD.ker] at ho
    have ho' : (c : G)⁻¹ * y ∈ O := (Lem3328.mem_pCore_iff _).mp ho
    have hcP : (c : G) ∈ P := by
      have := P.mul_mem hy (P.inv_mem (hOP ho'))
      simpa using this
    have : y = (c : G) * ((c : G)⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ⟨hcP, hc'⟩ ho'
  have hY₁C : liftCore α (flagStabilizer n (ZMod 2) {1}) ≤ C := by
    have hnormal : ((P ⊓ C).subgroupOf P).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨P.mul_mem (P.mul_mem g.2 hx.1) (P.inv_mem g.2), ?_⟩
      have := hCN.conj_mem ⟨x, hCL hx.2⟩ (Subgroup.mem_subgroupOf.mpr hx.2) ⟨g, hPL g.2⟩
      exact Subgroup.mem_subgroupOf.mp this
    have hsolv : Group.IsSolvable ↥O := by
      have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).isNilpotent
      infer_instance
    exact (perfectCore_le_of_sup_solvable inf_le_left hnormal hPeq hsolv).trans inf_le_right
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact (hY₁C hy).2 x hx

end Data

end CFSG.Quasithin.H13.L3318
