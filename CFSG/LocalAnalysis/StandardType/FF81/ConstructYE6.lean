module

public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYFive
public import CFSG.LocalAnalysis.StandardType.FF81.E6Position
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLabel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoOrder3
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Cent
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoSTheta
import CFSG.LocalAnalysis.StandardType.GGSixE6A24Centre
import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
import CFSG.LieType.Chevalley.PosUnipotentSylow
import CFSG.LocalAnalysis.SeitzReduction.LongRootPairs
import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
import CFSG.SignalizerFunctorTheorem.NonLocalExc.ChevalleyPerm

public section

namespace CFSG.StandardType.FF81.Blocks

open Matrix CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

abbrev swE : SL(2, ZMod 2) := tvU * tvD * tvU

abbrev rhoE : SL(2, ZMod 2) := tvU * tvD

abbrev w31 : SL(6, ZMod 2) :=
  rev6 * blockSL2 (ZMod 2) 5 4 swE * rev6 * blockSL2 (ZMod 2) 5 2 swE *
    blockSL2 (ZMod 2) 5 3 swE * blockSL2 (ZMod 2) 5 4 rhoE

theorem w31_pow : w31 ^ 31 = 1 := by decide +kernel

theorem w31_ne_one : w31 ≠ 1 := by decide +kernel

theorem orderOf_w31 : orderOf w31 = 31 :=
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  orderOf_eq_prime w31_pow w31_ne_one

theorem tr45_pow : tr6 4 5 ^ 2 = 1 := by decide

theorem tr45_ne_one : tr6 4 5 ≠ 1 := by decide

theorem orderOf_tr45 : orderOf (tr6 4 5) = 2 :=
  orderOf_eq_prime tr45_pow tr45_ne_one

theorem sw0345_mul_self : sw0345 * sw0345 = 1 := permSL_mul_self sw0345Perm_symm

theorem rev6_conj_block2 : ∀ A : SL(2, ZMod 2), ∃ B : SL(2, ZMod 2),
    rev6 * blockSL2 (ZMod 2) 5 2 A * rev6 = blockSL2 (ZMod 2) 5 1 B := by decide

theorem sw0345_conj_block3 : ∀ A : SL(2, ZMod 2), ∃ B : SL(2, ZMod 2),
    sw0345 * blockSL2 (ZMod 2) 5 3 A * sw0345 = rev6 * blockSL2 (ZMod 2) 5 4 B * rev6 := by decide

theorem sw0345_conj_block3' : ∀ B : SL(2, ZMod 2), ∃ A : SL(2, ZMod 2),
    sw0345 * blockSL2 (ZMod 2) 5 3 A * sw0345 = rev6 * blockSL2 (ZMod 2) 5 4 B * rev6 := by decide

theorem sw0345_conj_block4 : ∀ A : SL(2, ZMod 2), ∃ B : SL(2, ZMod 2),
    sw0345 * blockSL2 (ZMod 2) 5 4 A * sw0345 = blockSL2 (ZMod 2) 5 4 B := by decide

theorem sw0345_conj_block4' : ∀ B : SL(2, ZMod 2), ∃ A : SL(2, ZMod 2),
    sw0345 * blockSL2 (ZMod 2) 5 4 A * sw0345 = blockSL2 (ZMod 2) 5 4 B := by decide

theorem map_conj_range_eq {H : Type} [Group H] {f g : SL(2, ZMod 2) →* H} {c d : H}
    (hc : c * c = 1) (hd : d * d = 1) (h1 : ∀ A, ∃ B, c * f A * c = d * g B * d)
    (h2 : ∀ B, ∃ A, c * f A * c = d * g B * d) :
    f.range.map (MulAut.conj c).toMonoidHom = g.range.map (MulAut.conj d).toMonoidHom := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    hci, hdi]
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    obtain ⟨B, hB⟩ := h1 A
    exact ⟨_, ⟨B, rfl⟩, hB.symm⟩
  · rintro ⟨_, ⟨B, rfl⟩, rfl⟩
    obtain ⟨A, hA⟩ := h2 B
    exact ⟨_, ⟨A, rfl⟩, hA⟩

end CFSG.StandardType.FF81.Blocks

namespace CFSG.ClassicalInvolution.WeakCT

theorem LinearBlockStandardPair.map_conj {K : Type} [Field K] {X : Type} [Group X]
    {W U V : Subgroup X} (h : LinearBlockStandardPair K W U V) (x : X) :
    LinearBlockStandardPair K (W.map (MulAut.conj x).toMonoidHom)
      (U.map (MulAut.conj x).toMonoidHom) (V.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨θ, c, hθ, hker, himg⟩ := h
  refine ⟨(MulAut.conj x).toMonoidHom.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hθ]
  · intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (MulAut.conj x).injective (by rw [map_one]; exact hy)
  · rcases himg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← Subgroup.map_map, h1], by rw [← Subgroup.map_map, h2]⟩
    · exact Or.inr ⟨by rw [← Subgroup.map_map, h1], by rw [← Subgroup.map_map, h2]⟩

end CFSG.ClassicalInvolution.WeakCT

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)
open Blocks
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G} {K : ℕ → Subgroup G} {t : G}

abbrev e6Nodes (K : ℕ → Subgroup G) (Kα : Subgroup G) : Fin 6 → Subgroup G :=
  ![K 2, Kα, K 3, K 4, K 5, K 6]

omit [Finite G] in
theorem map_map_conj_eq {H : Type} [Group H] (ψ : H →* G) (c : H) (S : Subgroup H) :
    (S.map ψ).map (MulAut.conj (ψ c)).toMonoidHom = (S.map (MulAut.conj c).toMonoidHom).map ψ := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext1 x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem FrameSystem.a2System_e6 (hF : FrameSystem 5 b L K t) {ψg : SL(5 + 1, ZMod 2) →* G}
    (hψgrange : ψg.range = ⨆ i : Fin 5, K (i : ℕ))
    (hψgblk : ∀ i : Fin 5, (blockSL2 (ZMod 2) 5 i).range.map ψg = K (i : ℕ))
    (hcomm : ∀ a ∈ (K 4).map (MulAut.conj (ψg rev6)).toMonoidHom, ∀ c ∈ K 5, a * c = c * a) :
    A2System adjE6 (e6Nodes K ((K 4).map (MulAut.conj (ψg rev6)).toMonoidHom))
      (⨆ i, e6Nodes K ((K 4).map (MulAut.conj (ψg rev6)).toMonoidHom) i) := by
  obtain ⟨g, -, hgL, hgc⟩ := hF.tau
  set α : G := ψg rev6 with hαdef
  set Kα : Subgroup G := (K 4).map (MulAut.conj α).toMonoidHom with hKα
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, rev6_mul_self, map_one]
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hconjg : ∀ x, α * ψg x * α⁻¹ = ψg (rev6 * x * rev6) := by
    intro x
    rw [hαinv, hαdef, map_mul, map_mul]
  have hmemg : ∀ (i : Fin 5) (A : SL(2, ZMod 2)), ψg (blockSL2 (ZMod 2) 5 i A) ∈ K (i : ℕ) := by
    intro i A
    rw [← hψgblk i]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have hexg : ∀ (i : Fin 5), ∀ x ∈ K (i : ℕ), ∃ A, ψg (blockSL2 (ZMod 2) 5 i A) = x := by
    intro i x hx
    rw [← hψgblk i] at hx
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
    exact ⟨A, rfl⟩
  have hLg : ∀ x, ψg x ∈ L.map (MulAut.conj g).toMonoidHom := fun x => hgL ▸ hψgrange ▸ ⟨x, rfl⟩
  have hcL' : ∀ i j : Fin 5, i ≠ j → ¬ adjA i j → ∀ a ∈ K (i : ℕ), ∀ c ∈ K (j : ℕ), a * c = c * a :=
    hF.sysL'.2.2.1
  have hα2 : ∀ a ∈ Kα, ∀ c ∈ K 2, a * c = c * a := by
    rintro _ ⟨k, hk, rfl⟩ c hc
    obtain ⟨A, rfl⟩ := hexg 2 c hc
    obtain ⟨B, hB⟩ := rev6_conj_block2 A
    have hc' : ψg (blockSL2 (ZMod 2) 5 2 A) = α * ψg (blockSL2 (ZMod 2) 5 1 B) * α⁻¹ := by
      rw [hconjg, ← hB, ← mul_assoc, ← mul_assoc, rev6_mul_self, one_mul, mul_assoc,
        rev6_mul_self, mul_one]
    rw [hc']
    have h := hcL' 4 1 (by decide) (by unfold adjA; decide) k hk _ (hmemg 1 B)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc α * k * α⁻¹ * (α * ψg (blockSL2 (ZMod 2) 5 1 B) * α⁻¹)
        = α * (k * ψg (blockSL2 (ZMod 2) 5 1 B)) * α⁻¹ := by group
      _ = α * (ψg (blockSL2 (ZMod 2) 5 1 B) * k) * α⁻¹ := by rw [h]
      _ = α * ψg (blockSL2 (ZMod 2) 5 1 B) * α⁻¹ * (α * k * α⁻¹) := by group
  have hα3 : ∀ a ∈ Kα, ∀ c ∈ K 3, a * c = c * a := by
    rintro _ ⟨k, hk, rfl⟩ c hc
    obtain ⟨A, rfl⟩ := hexg 3 c hc
    obtain ⟨B, hB⟩ := rev6_conj_block3 A
    have hc' : ψg (blockSL2 (ZMod 2) 5 3 A) = α * ψg (blockSL2 (ZMod 2) 5 0 B) * α⁻¹ := by
      rw [hconjg, ← hB, ← mul_assoc, ← mul_assoc, rev6_mul_self, one_mul, mul_assoc,
        rev6_mul_self, mul_one]
    rw [hc']
    have h := hcL' 4 0 (by decide) (by unfold adjA; decide) k hk _ (hmemg 0 B)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc α * k * α⁻¹ * (α * ψg (blockSL2 (ZMod 2) 5 0 B) * α⁻¹)
        = α * (k * ψg (blockSL2 (ZMod 2) 5 0 B)) * α⁻¹ := by group
      _ = α * (ψg (blockSL2 (ZMod 2) 5 0 B) * k) * α⁻¹ := by rw [h]
      _ = α * ψg (blockSL2 (ZMod 2) 5 0 B) * α⁻¹ * (α * k * α⁻¹) := by group
  have hα6 : ∀ a ∈ Kα, ∀ c ∈ K 6, a * c = c * a := by
    rintro _ ⟨k, hk, rfl⟩ c hc
    obtain ⟨A, rfl⟩ := hexg 4 k hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hconjg]
    exact (hgc c hc _ (hLg _)).symm
  have hcL : ∀ i j : Fin 5, i ≠ j → ¬ adjA i j →
      ∀ a ∈ K ((i : ℕ) + 2), ∀ c ∈ K ((j : ℕ) + 2), a * c = c * a := hF.sysL.2.2.1
  have hsymm : ∀ X Y : Subgroup G, (∀ a ∈ X, ∀ c ∈ Y, a * c = c * a) →
      ∀ a ∈ Y, ∀ c ∈ X, a * c = c * a := fun X Y h a ha c hc => (h c hc a ha).symm
  have hpairα : ∃ W : Subgroup G, LinearBlockStandardPair (ZMod 2) W Kα (K 4) := by
    obtain ⟨W, hW⟩ := hF.sysL'.2.2.2 (3 : Fin 5) (4 : Fin 5) (Or.inl rfl)
    have hW' := hW.map_conj (ψg sw0345)
    have hb3 : (blockSL2 (ZMod 2) 5 3).range.map ψg = K 3 := hψgblk 3
    have hb4 : (blockSL2 (ZMod 2) 5 4).range.map ψg = K 4 := hψgblk 4
    have h3 : (K 3).map (MulAut.conj (ψg sw0345)).toMonoidHom = Kα := by
      rw [hKα, ← hb3, ← hb4, map_map_conj_eq, map_map_conj_eq,
        map_conj_range_eq sw0345_mul_self rev6_mul_self sw0345_conj_block3 sw0345_conj_block3']
    have h4 : (K 4).map (MulAut.conj (ψg sw0345)).toMonoidHom = K 4 := by
      rw [← hb4, map_map_conj_eq]
      congr 1
      have hsi : sw0345⁻¹ = sw0345 := inv_eq_of_mul_eq_one_right sw0345_mul_self
      ext x
      simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, hsi]
      constructor
      · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
        obtain ⟨B, hB⟩ := sw0345_conj_block4 A
        exact ⟨B, hB.symm⟩
      · rintro ⟨B, rfl⟩
        obtain ⟨A, hA⟩ := sw0345_conj_block4' B
        exact ⟨_, ⟨A, rfl⟩, hA⟩
    exact ⟨_, h3 ▸ h4 ▸ hW'⟩
  refine ⟨fun i => ?_, rfl, fun i j hij hadj => ?_, fun i j hadj => ?_⟩
  · fin_cases i
    · exact hF.sysL.1 0
    · obtain ⟨e⟩ := hF.sysL.1 2
      exact ⟨e.trans ((K 4).equivMapOfInjective (MulAut.conj α).toMonoidHom
        (MulAut.conj α).injective)⟩
    · exact hF.sysL.1 1
    · exact hF.sysL.1 2
    · exact hF.sysL.1 3
    · exact hF.sysL.1 4
  · fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact absurd (by unfold adjE6 CFSG.Timmesfeld.edgeE; decide) hadj
      | exact hsymm _ _ hα2
      | exact hα2
      | exact hsymm _ _ hα3
      | exact hα3
      | exact hsymm _ _ hcomm
      | exact hcomm
      | exact hsymm _ _ hα6
      | exact hα6
      | exact hcL 0 2 (by decide) (by unfold adjA; decide)
      | exact hcL 2 0 (by decide) (by unfold adjA; decide)
      | exact hcL 0 3 (by decide) (by unfold adjA; decide)
      | exact hcL 3 0 (by decide) (by unfold adjA; decide)
      | exact hcL 0 4 (by decide) (by unfold adjA; decide)
      | exact hcL 4 0 (by decide) (by unfold adjA; decide)
      | exact hcL 1 3 (by decide) (by unfold adjA; decide)
      | exact hcL 3 1 (by decide) (by unfold adjA; decide)
      | exact hcL 1 4 (by decide) (by unfold adjA; decide)
      | exact hcL 4 1 (by decide) (by unfold adjA; decide)
      | exact hcL 2 4 (by decide) (by unfold adjA; decide)
      | exact hcL 4 2 (by decide) (by unfold adjA; decide)
  · fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hadj (by unfold adjE6 CFSG.Timmesfeld.edgeE; decide)
      | exact hpairα
      | exact (let ⟨W, hW⟩ := hpairα; ⟨W, hW.symm⟩)
      | exact hF.sysL.2.2.2 0 1 (Or.inl rfl)
      | exact hF.sysL.2.2.2 1 0 (Or.inr rfl)
      | exact hF.sysL.2.2.2 1 2 (Or.inl rfl)
      | exact hF.sysL.2.2.2 2 1 (Or.inr rfl)
      | exact hF.sysL.2.2.2 2 3 (Or.inl rfl)
      | exact hF.sysL.2.2.2 3 2 (Or.inr rfl)
      | exact hF.sysL.2.2.2 3 4 (Or.inl rfl)
      | exact hF.sysL.2.2.2 4 3 (Or.inr rfl)


section E6

open CFSG.StandardType.GGSixE6Two
open CFSG.SeitzReduction (highRoot)
open CFSG.StandardType.FrameRoute.FS81 (IsSylow2In)

theorem ggHasLabel_E6_of_a2System (hC : CurtisA2) {U : Fin 6 → Subgroup G} {Y : Subgroup G}
    (h : A2System adjE6 U Y) : GGHasLabel ⟨.E6, 0, 1⟩ ↥Y := by
  obtain ⟨hq, hL⟩ := hC.2 ↥Y _ h.subgroupOf
  have hZ : Subgroup.center ↥Y = ⊥ := ggSixE6A24_center_eq_bot ↥Y hq.1.commutator_eq_top hL
  have hlab := (TableCRes.ggCompLabelAt_E6 (X := Y) 1 le_rfl hL).2.2.1
  let e : ↥Y ⧸ Subgroup.center ↥Y ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨g'⟩ => ⟨e.symm.trans g'⟩) hlab

theorem mem_lE_of_mem_sup_of_sq {x : EC} (hx : x ∈ Subgroup.zpowers zE ⊔ lE) (h2 : x ^ 2 = 1) :
    x ∈ lE := by
  have hN : Subgroup.zpowers zE ≤ Subgroup.normalizer (lE : Set EC) :=
    centralizer_zE.2.2.trans (Subgroup.centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hx
  obtain ⟨z, hz, l, hl, rfl⟩ := hx
  have hzl : l * z = z * l := Subgroup.mem_centralizer_iff.1 (centralizer_zE.2.2 hz) l hl
  have h2' : z ^ 2 * l ^ 2 = 1 := by
    rw [← h2, pow_two, pow_two, pow_two, mul_assoc, mul_assoc, ← mul_assoc z l, ← hzl]
    group
  have hz2 : z ^ 2 = 1 := by
    have hmem : z ^ 2 ∈ lE := by
      rw [eq_inv_of_mul_eq_one_left h2']
      exact inv_mem (pow_mem hl 2)
    exact Subgroup.disjoint_def.1 centralizer_zE.2.1 (pow_mem hz 2) hmem
  have hz3 : z ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_zE]
    exact orderOf_dvd_of_mem_zpowers hz
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2, inv_one, one_mul]
  subst hz1
  simpa using hl

theorem le_of_ggHasLabel_E6 {Y M : Subgroup G} {b' w u : G} (hY : GGHasLabel ⟨.E6, 0, 1⟩ ↥Y)
    (hbY : b' ∈ Y) (hb : orderOf b' = 3) (hwY : w ∈ Y) (hwb : w * b' = b' * w)
    (hw : orderOf w = 31)
    (hN : Subgroup.centralizer ({b'} : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hM : Nat.card M = Nat.card lE) (huM : u ∈ M) (huY : u ∈ Y) (hub : u * b' = b' * u)
    (hu : orderOf u = 2) : M ≤ Y := by
  obtain ⟨ψ⟩ := nonempty_mulEquiv_EC_of_ggHasLabel hY
  have hcommY : ∀ {x : G} (hx : x ∈ Y), x * b' = b' * x →
      (⟨x, hx⟩ : ↥Y) * ⟨b', hbY⟩ = ⟨b', hbY⟩ * ⟨x, hx⟩ := fun _ h => Subtype.ext h
  have hxord : orderOf (ψ ⟨b', hbY⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe (⟨b', hbY⟩ : ↥Y)]
    exact hb
  have h31 : 31 ∣ Nat.card (Subgroup.centralizer ({ψ ⟨b', hbY⟩} : Set EC)) := by
    have hmem : ψ ⟨w, hwY⟩ ∈ Subgroup.centralizer ({ψ ⟨b', hbY⟩} : Set EC) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcommY hwY hwb]
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe (⟨w, hwY⟩ : ↥Y), hw] at h
  obtain ⟨h, hh⟩ := e6Two_order3Conj e6TwoCentT31_holds _ hxord h31
  set χ : ↥Y ≃* EC := ψ.trans (MulAut.conj h) with hχ
  have hχv : ∀ y : ↥Y, χ y = h * ψ y * h⁻¹ := fun y => by
    rw [hχ, MulEquiv.trans_apply, MulAut.conj_apply]
  have hCχ : Subgroup.centralizer ({χ ⟨b', hbY⟩} : Set EC) = Subgroup.zpowers zE ⊔ lE := by
    rw [hχv]
    rcases hh with hh | hh <;> rw [hh]
    · exact centralizer_zE.1
    · rw [centralizer_zE_inv]
      exact centralizer_zE.1
  have hCY : ∀ {x : G} (hx : x ∈ Y), x * b' = b' * x →
      χ ⟨x, hx⟩ ∈ Subgroup.zpowers zE ⊔ lE := by
    intro x hx hxb
    rw [← hCχ, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcommY hx hxb]
  set M' : Subgroup G := (lE.map χ.symm.toMonoidHom).map Y.subtype with hM'
  have hM'Y : M' ≤ Y := by
    rw [hM']
    exact Subgroup.map_subtype_le _
  have hM'C : M' ≤ Subgroup.centralizer ({b'} : Set G) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyc : y ∈ Subgroup.centralizer ({χ ⟨b', hbY⟩} : Set EC) :=
      hCχ ▸ Subgroup.mem_sup_right hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
    have h' := congrArg (fun v : EC => ((χ.symm v : ↥Y) : G)) hyc
    simpa [map_mul] using h'
  have hM'card : Nat.card M' = Nat.card lE := by
    rw [hM', Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective χ.symm.injective]
  have hM'simple : IsSimpleGroup ↥M' := by
    have := isSimpleGroup_lE
    exact ((lE.equivMapOfInjective χ.symm.toMonoidHom χ.symm.injective).trans
      ((lE.map χ.symm.toMonoidHom).equivMapOfInjective Y.subtype Y.subtype_injective)).symm.isSimpleGroup
  have huM' : u ∈ M' := by
    have hsq : (χ ⟨u, huY⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨u, huY⟩ : ↥Y) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hu, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [this, map_one]
    refine ⟨_, ⟨χ ⟨u, huY⟩, mem_lE_of_mem_sup_of_sq (hCY huY hub) hsq, rfl⟩, ?_⟩
    simp
  have hnorm : (M.subgroupOf M').Normal := by
    constructor
    intro x hx g
    have hg : (g : G) ∈ Subgroup.normalizer (M : Set G) := hN (hM'C g.2)
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 hg _).1 hx
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hM'simple _ hnorm with hbot | htop
  · exfalso
    have hmem : (⟨u, huM'⟩ : ↥M') ∈ M.subgroupOf M' := by
      rw [Subgroup.mem_subgroupOf]
      exact huM
    rw [hbot, Subgroup.mem_bot] at hmem
    have hu1 : u = 1 := congrArg Subtype.val hmem
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · have hle : M' ≤ M := Subgroup.subgroupOf_eq_top.1 htop
    have heq : M' = M := Subgroup.eq_of_le_of_card_ge hle (by rw [hM, hM'card])
    rw [← heq]
    exact hM'Y

end E6


section E6Main


open CFSG.StandardType.GGSixE6Two
open CFSG.SeitzReduction (highRoot)
open CFSG.Blueprint.Chevalley (posUnipotent rootSubgroup pinnedX ModGL adjointGroup IsRoot height)
open CFSG.SeitzReduction (posUnipotent_le_centralizer_highRoot isRoot_highRoot)
open CFSG.StandardType.GGHalf (F2)
open CFSG.StandardType.FrameRoute.FS81 (IsSylow2In)

theorem FrameSystem.yData_e6 (hC : CurtisA2) (hA : HypA G 5 b L) (hF : FrameSystem 5 b L K t)
    {ψg : SL(5 + 1, ZMod 2) →* G} (hψginj : Function.Injective ψg)
    (hψgrange : ψg.range = ⨆ i : Fin 5, K (i : ℕ))
    (hψgblk : ∀ i : Fin 5, (blockSL2 (ZMod 2) 5 i).range.map ψg = K (i : ℕ))
    (hcomm : ∀ a ∈ (K 4).map (MulAut.conj (ψg rev6)).toMonoidHom, ∀ c ∈ K 5, a * c = c * a) :
    GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (5 + 2), K (i : ℕ)) ∧
      Subgroup.centralizer ({b} : Set G) ⊓ (⨆ i : Fin (5 + 2), K (i : ℕ)) =
        Subgroup.zpowers b ⊔ L ∧
      ∃ S : Subgroup G, IsSylow2In S (⨆ i : Fin (5 + 2), K (i : ℕ)) ∧ t ∈ S ∧ orderOf t = 2 ∧
        ∀ s ∈ S, s * t = t * s := by
  obtain ⟨g, hgb, hgL, hgc⟩ := hF.tau
  set α : G := ψg rev6 with hαdef
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, rev6_mul_self, map_one]
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  set Kα : Subgroup G := (K 4).map (MulAut.conj α).toMonoidHom with hKα
  set U := e6Nodes K Kα with hU
  set Y0 : Subgroup G := ⨆ i, U i with hY0
  set Y : Subgroup G := ⨆ i : Fin (5 + 2), K (i : ℕ) with hY
  have hsys : A2System adjE6 U Y0 := hF.a2System_e6 hψgrange hψgblk hcomm
  have hY0lab : GGHasLabel ⟨.E6, 0, 1⟩ ↥Y0 := ggHasLabel_E6_of_a2System hC hsys
  have hmemg : ∀ (i : Fin 5) (A : SL(2, ZMod 2)), ψg (blockSL2 (ZMod 2) 5 i A) ∈ K (i : ℕ) := by
    intro i A
    rw [← hψgblk i]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have hLg : ∀ x, ψg x ∈ L.map (MulAut.conj g).toMonoidHom := fun x => hgL ▸ hψgrange ▸ ⟨x, rfl⟩
  have hU0 : ∀ i, U i ≤ Y0 := le_iSup U
  have hLgY0 : L.map (MulAut.conj g).toMonoidHom ≤ Y0 := by
    have hbY : g * b * g⁻¹ ∈ Y0 := hU0 5 hgb
    have hb : orderOf (g * b * g⁻¹) = 3 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hA.ord]
    have hwY : ψg w31 ∈ Y0 := by
      have h1 : ψg rev6 * ψg (blockSL2 (ZMod 2) 5 4 swE) * ψg rev6 ∈ Y0 := by
        refine hU0 1 ⟨ψg (blockSL2 (ZMod 2) 5 4 swE), hmemg 4 swE, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hαinv]
      rw [show w31 = rev6 * blockSL2 (ZMod 2) 5 4 swE * rev6 * blockSL2 (ZMod 2) 5 2 swE *
          blockSL2 (ZMod 2) 5 3 swE * blockSL2 (ZMod 2) 5 4 rhoE from rfl,
        map_mul ψg, map_mul ψg, map_mul ψg, map_mul ψg, map_mul ψg]
      exact Y0.mul_mem (Y0.mul_mem (Y0.mul_mem h1 (hU0 0 (hmemg 2 swE))) (hU0 2 (hmemg 3 swE)))
        (hU0 3 (hmemg 4 rhoE))
    have hcb : ∀ x, ψg x * (g * b * g⁻¹) = g * b * g⁻¹ * ψg x := fun x =>
      (hgc _ hgb _ (hLg x)).symm
    have hcard : Nat.card ↥(L.map (MulAut.conj g).toMonoidHom) = Nat.card lE := by
      rw [← hgL, ← hψgrange, card_lE_eq_card_specialLinearGroup]
      exact Nat.card_congr (MonoidHom.ofInjective hψginj).toEquiv.symm
    have huY : ψg (tr6 4 5) ∈ Y0 := by
      rw [← block4_tvU]
      exact hU0 3 (hmemg 4 tvU)
    exact le_of_ggHasLabel_E6 hY0lab hbY hb hwY (hcb w31)
      (by rw [orderOf_injective ψg hψginj, orderOf_w31]) (hA.centralizer_conj_le_normalizer g) hcard
      (hLg _) huY (hcb _) (by rw [orderOf_injective ψg hψginj, orderOf_tr45])
  have hLgY : L.map (MulAut.conj g).toMonoidHom ≤ Y := by
    rw [← hgL]
    exact iSup_le fun i => le_iSup (fun j : Fin (5 + 2) => K (j : ℕ)) ⟨i, by omega⟩
  have hY0Y : Y0 = Y := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_iSup (fun j : Fin (5 + 2) => K (j : ℕ)) 2
      · rintro _ ⟨k, hk, rfl⟩
        apply hLgY
        have hkg : k ∈ L.map (MulAut.conj g).toMonoidHom :=
          hgL ▸ le_iSup (fun j : Fin 5 => K (j : ℕ)) 4 hk
        have hαg : α ∈ L.map (MulAut.conj g).toMonoidHom := hLg rev6
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hαg hkg) (Subgroup.inv_mem _ hαg)
      · exact le_iSup (fun j : Fin (5 + 2) => K (j : ℕ)) 3
      · exact le_iSup (fun j : Fin (5 + 2) => K (j : ℕ)) 4
      · exact le_iSup (fun j : Fin (5 + 2) => K (j : ℕ)) 5
      · exact le_iSup (fun j : Fin (5 + 2) => K (j : ℕ)) 6
    · refine iSup_le fun i => ?_
      have hKg : ∀ j : Fin 5, K (j : ℕ) ≤ Y0 := fun j =>
        (hgL ▸ le_iSup (fun j : Fin 5 => K (j : ℕ)) j).trans hLgY0
      fin_cases i
      · exact hKg 0
      · exact hKg 1
      · exact hU0 0
      · exact hU0 2
      · exact hU0 3
      · exact hU0 4
      · exact hU0 5
  have hYlab : GGHasLabel ⟨.E6, 0, 1⟩ ↥Y := hY0Y ▸ hY0lab
  have hbK0 : b ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have htK0 : t ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hbY : b ∈ Y := le_iSup (fun j : Fin (5 + 2) => K (j : ℕ)) 0 hbK0
  have htY : t ∈ Y := le_iSup (fun j : Fin (5 + 2) => K (j : ℕ)) 0 htK0
  obtain ⟨φ, hφinj, hφrange, hφx, hφz, hφL⟩ :=
    exists_e6Position_of_le hYlab hbY hA.ord hF.L_le_join hA.le hA.model htY hF.ord_t
      (fun y hy => hF.comm_L t htK0 y hy)
  refine ⟨hYlab, centralizer_inf_eq_of_e6Position hφinj hφrange hφz hφL, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUC, hUp, hUi⟩ := CFSG.LieType.Chevalley.isSylowTwoOf_posUnipotent (K := F2) .E6
  have hU0p : IsPGroup 2 ↥((posUnipotent .E6 F2).subgroupOf (adjointGroup .E6 F2)) :=
    hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUC).symm
  set S0 : Sylow 2 EC := hU0p.toSylow hUi with hS0def
  have hS0 : ∀ x : EC, x ∈ (S0 : Subgroup EC) ↔ (x : ModGL .E6 F2) ∈ posUnipotent .E6 F2 :=
    fun x => by simp only [hS0def, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf]
  have hθroot : pinnedX .E6 F2 (highRoot .E6) 1 ∈ rootSubgroup .E6 F2 (highRoot .E6) :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have hθU : (xr (highRoot .E6) : ModGL .E6 F2) ∈ posUnipotent .E6 F2 := by
    have hle : rootSubgroup .E6 F2 (highRoot .E6) ≤ posUnipotent .E6 F2 :=
      le_iSup₂ (f := fun α (_ : α ∈ {α | IsRoot .E6 α ∧ 0 < height α}) =>
        rootSubgroup .E6 F2 α) (highRoot .E6) ⟨isRoot_highRoot .E6, by decide⟩
    exact hle hθroot
  have hθc : ∀ s ∈ (S0 : Subgroup EC), s * xr (highRoot .E6) = xr (highRoot .E6) * s := by
    intro s hs
    apply Subtype.ext
    have h := posUnipotent_le_centralizer_highRoot (τ := .E6) F2 ((hS0 s).1 hs)
    exact (Subgroup.mem_centralizer_iff.1 h _ hθroot).symm
  refine ⟨(S0 : Subgroup EC).map φ, ⟨?_, S0.isPGroup'.map φ, fun T' hT'Y hT'p hle => ?_⟩,
    ⟨_, (hS0 _).2 hθU, hφx⟩, hF.ord_t, ?_⟩
  · rw [← hφrange]
    exact Subgroup.map_le_range φ _
  · have hle0 : (S0 : Subgroup EC) ≤ T'.comap φ := fun x hx => hle ⟨x, hx, rfl⟩
    have heq := S0.is_maximal' (hT'p.comap_of_injective φ hφinj) hle0
    rw [← heq, Subgroup.map_comap_eq, inf_of_le_right (hφrange ▸ hT'Y)]
  · rintro _ ⟨s, hs, rfl⟩
    rw [← hφx, ← map_mul, ← map_mul, hθc s hs]

end E6Main

end CFSG.StandardType.FF81
