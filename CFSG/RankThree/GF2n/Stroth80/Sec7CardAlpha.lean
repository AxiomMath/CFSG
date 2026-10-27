module

public import CFSG.RankThree.GF2n.Stroth80.Sec7AddFilt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux
public import CFSG.RankThree.GF2n.Stroth80.Sec78CardUt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_Wt_mul_le_card_inf_Q1 (hc : Ctx M Q Z B) {α : G} (hαM : α ∈ M) {W T : Subgroup G}
    (hZW : Z ≤ W) (hWQ : W ≤ Q) (hZT : Z ≤ T) (hTQ : T ≤ Q)
    (hmap : ∀ w ∈ W, ⁅α, w⁆ ∈ T) :
    Nat.card ↥W * Nat.card ↥Z ≤ Nat.card ↥(W ⊓ Q1 hc α) * Nat.card ↥T := by
  have hZQ : Z ≤ Q := hc.Z_le_Q
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule (sec7ctr_secHyp hc (le_refl M))
  haveI : Finite Md := hκ.finite
  let α' : ↥M := ⟨α, hαM⟩
  let ε : Md →+ Md :=
    AddMonoidHom.mk' (fun a => α' • a - a) (fun a b => by rw [smul_add]; abel)
  have hεdef : ∀ a : Md, ε a = α' • a - a := fun a => rfl
  have hyQ : ∀ x : ↥Q, α * (x : G) * α⁻¹ ∈ Q := fun x =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hαM) (x : G)).mp x.2
  have hcomm : ∀ x : ↥Q, ⁅α, (x : G)⁆ ∈ Q := fun x => by
    rw [commutatorElement_def]
    exact Q.mul_mem (hyQ x) (Q.inv_mem x.2)
  have hεapp : ∀ x : ↥Q, ε (Multiplicative.toAdd (κ x)) =
      Multiplicative.toAdd (κ ⟨⁅α, (x : G)⁆, hcomm x⟩) := by
    intro x
    have hy1 : κ ⟨α * (x : G) * α⁻¹, hyQ x⟩ =
        Multiplicative.ofAdd (α' • Multiplicative.toAdd (κ x)) :=
      hκ.act α' x ⟨α * (x : G) * α⁻¹, hyQ x⟩ rfl
    have h2 : (⟨⁅α, (x : G)⁆, hcomm x⟩ : ↥Q) = ⟨α * (x : G) * α⁻¹, hyQ x⟩ * x⁻¹ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2, map_mul, map_inv, hy1, toAdd_mul, toAdd_inv, toAdd_ofAdd, hεdef, sub_eq_add_neg]
  have hZQ1 : Z ≤ Q1 hc α := by
    intro z hz
    rw [hc.mem_Q1_iff hαM]
    refine ⟨hZQ hz, ?_⟩
    have h1 : α * z * α⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hαM) z).mp hz
    rw [commutatorElement_def]
    exact Z.mul_mem h1 (Z.inv_mem hz)
  have hmem : ∀ a ∈ secSub κ W, ε a ∈ secSub κ T := by
    intro a ha
    obtain ⟨x, hxW, hxa⟩ := mem_secSub.mp ha
    have ha' : Multiplicative.toAdd (κ x) = a := by rw [hxa, toAdd_ofAdd]
    rw [← ha', hεapp x]
    exact (toAdd_mem_secSub_iff hκ hZT ⟨⁅α, (x : G)⁆, hcomm x⟩).mpr (hmap _ hxW)
  have hεker : ε.ker = secSub κ (Q1 hc α) := by
    ext a
    obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
    have ha : Multiplicative.toAdd (κ x) = a := by rw [hx, toAdd_ofAdd]
    rw [← ha, AddMonoidHom.mem_ker, hεapp x, toAdd_eq_zero, hκ.ker,
      toAdd_mem_secSub_iff hκ hZQ1 x, hc.mem_Q1_iff hαM]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hker_eq : secSub κ W ⊓ ε.ker = secSub κ (W ⊓ Q1 hc α) := by
    rw [secSub_inf hκ hZW, hεker]
  have hk := card_le_card_inf_ker_mul ε (secSub κ W) (secSub κ T) hmem
  rw [hker_eq] at hk
  have hZWQ1 : Z ≤ W ⊓ Q1 hc α := le_inf hZW hZQ1
  have hWQ1 : W ⊓ Q1 hc α ≤ Q := le_trans inf_le_left hWQ
  have hA : Nat.card ↥(secSub κ W) * Nat.card ↥Z = Nat.card ↥W :=
    natCard_secSub_mul hZQ hκ hZW hWQ
  have hB : Nat.card ↥(secSub κ (W ⊓ Q1 hc α)) * Nat.card ↥Z = Nat.card ↥(W ⊓ Q1 hc α) :=
    natCard_secSub_mul hZQ hκ hZWQ1 hWQ1
  have hC : Nat.card ↥(secSub κ T) * Nat.card ↥Z = Nat.card ↥T :=
    natCard_secSub_mul hZQ hκ hZT hTQ
  calc Nat.card ↥W * Nat.card ↥Z
      = (Nat.card ↥(secSub κ W) * Nat.card ↥Z) * Nat.card ↥Z := by rw [hA]
    _ ≤ ((Nat.card ↥(secSub κ (W ⊓ Q1 hc α)) * Nat.card ↥(secSub κ T)) * Nat.card ↥Z) *
          Nat.card ↥Z := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk)
    _ = (Nat.card ↥(secSub κ (W ⊓ Q1 hc α)) * Nat.card ↥Z) *
          (Nat.card ↥(secSub κ T) * Nat.card ↥Z) := by ring
    _ = Nat.card ↥(W ⊓ Q1 hc α) * Nat.card ↥T := by rw [hB, hC]


theorem sec73CardAlpha_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (h310chi : Stroth310ChiStatement) :
    Sec73CardAlphaStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom α hα
  obtain ⟨hαL, hαN⟩ := Subgroup.mem_inf.mp hα
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hαM : α ∈ M := hc.LB_le_M hαL
  have hWN := sec7_N_comm_W_le_V h52a hA hc hs
  obtain ⟨hVU, hWQ1⟩ := h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := hZV.trans hVW
  have hQ1Q : ∀ s : G, Q1 hc s ≤ Q := fun s x hx => hx.1
  have hUt : ∀ {s : G}, s ∈ LB M Q B →
      Nat.card Q * Nat.card Z = Nat.card ↥(Q1 hc s) * Nat.card ↥(Ut Q Z s) := by
    intro s hsL
    have hsM : s ∈ M := hc.LB_le_M hsL
    haveI : (Z.subgroupOf (Ut Q Z s)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
        hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Ut_le_Q hsM hv)))
    exact card_mul_card_of_isChiIso (hc.isChiIso_Q1_Ut hsL) (hQ1Q s) (le_sup_right : Z ≤ Ut Q Z s)
  have hA1 := hUt hαL
  have hA2 := hUt ht
  rw [← hWQ1, ← hVU] at hA2
  have hV := card_Vt_orthogonal hc (le_refl 2) (Or.inr hom)
  have hQB := card_Vt_inf_QB_omegaMinus h34 hRoot hc hs (le_refl 2) hom
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hcnt := card_Wt_mul_le_card_inf_Q1 hc hαM hZW hWQ (le_inf hZV hc.Z_le_QB.1)
    (inf_le_left.trans hVQ)
    (fun w hw => Subgroup.mem_inf.mpr ⟨hWN α hαN w hw, comm_LB_Wt_mem_QB hc hBV hαL hw⟩)
  have hD : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t) ⊓ Q1 hc α) ≤ Nat.card ↥(Q1 hc α) :=
    Subgroup.card_le_of_le inf_le_right
  have hcpos : 0 < Nat.card ↥(Q1 hc α) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hcpos
  rw [hQB] at hcnt
  norm_num at hV hcnt
  calc Nat.card ↥(Q1 hc α) * Nat.card ↥(Ut Q Z α) = Nat.card Q * Nat.card Z := hA1.symm
    _ = Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) *
          Nat.card ↥(Vt M (LB M Q B) B Z t) := hA2
    _ = Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * (Nat.card Z * Nat.card Z ^ 4) := by rw [hV]
    _ = (Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z) * Nat.card Z ^ 4 := by ring
    _ ≤ (Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t) ⊓ Q1 hc α) * Nat.card Z ^ 4) *
          Nat.card Z ^ 4 := Nat.mul_le_mul_right _ hcnt
    _ ≤ (Nat.card ↥(Q1 hc α) * Nat.card Z ^ 4) * Nat.card Z ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hD)
    _ = Nat.card ↥(Q1 hc α) * Nat.card Z ^ 8 := by ring

