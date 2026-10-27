module

public import CFSG.Quasithin.MS93.S4A441X
import CFSG.Quasithin.MS93.S4A441XE
import CFSG.Quasithin.MS93.S4A441EBP
import CFSG.Quasithin.MS93.S46TypeLin
import CFSG.Quasithin.MS93.S4A44Base
import CFSG.Quasithin.MS93.S4ABasic
import CFSG.Quasithin.MS93.S4A432F

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace X441

section Lin

variable {F : Type} [Field F]

private theorem exists_mulVec_e0_e1' {u w : Fin 3 → F} (hu : u ≠ 0) (hw : ∀ t : F, w ≠ t • u) :
    ∃ x : SL3 F, ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = u ∧
      ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] = w := by
  obtain ⟨x₁, hx₁⟩ := exists_mulVec_e0_eq hu
  set w' := ((x₁⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w with hw'
  have hx₁w : ((x₁ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w' = w := by
    rw [hw', Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]
  have h12 : w' 1 ≠ 0 ∨ w' 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw (w' 0)
    have e : w' = w' 0 • ![1, 0, 0] := by
      funext k; fin_cases k <;> simp [hcon.1, hcon.2]
    rw [← hx₁w]
    nth_rewrite 1 [e]
    rw [Matrix.mulVec_smul, hx₁]
  obtain ⟨x₂, hx₂0, hx₂1⟩ : ∃ x₂ : SL3 F,
      ((x₂ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧
      ((x₂ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] = w' := by
    rcases h12 with h1 | h2
    · refine ⟨⟨!![1, w' 0, 0; 0, w' 1, 0; 0, w' 2, (w' 1)⁻¹], ?_⟩, ?_, ?_⟩
      · rw [Matrix.det_fin_three]; simp [h1]
      · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · by_cases h1 : w' 1 = 0
      · refine ⟨⟨!![1, w' 0, 0; 0, 0, -(w' 2)⁻¹; 0, w' 2, 0], ?_⟩, ?_, ?_⟩
        · rw [Matrix.det_fin_three]; simp [h2]
        · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1]
      · refine ⟨⟨!![1, w' 0, 0; 0, w' 1, 0; 0, w' 2, (w' 1)⁻¹], ?_⟩, ?_, ?_⟩
        · rw [Matrix.det_fin_three]; simp [h1]
        · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨x₁ * x₂, ?_, ?_⟩
  · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hx₂0, hx₁]
  · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hx₂1, hx₁w]

private theorem dualMat_transposeInv (g : SL3 F) :
    dualMat (transposeInv g) = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [← coe_transposeInv, transposeInv_transposeInv]

private theorem inv_mulVec_mulVec (a : SL3 F) (x : Fin 3 → F) :
    ((a⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (((a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) =
      x := by
  rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]

private theorem exists_dualMat_mulVec_eq {d v : Fin 3 → F} (hd : d ≠ 0) (hv : v ≠ 0) :
    ∃ g : SL3 F, dualMat g *ᵥ d = v := by
  obtain ⟨a, ha⟩ := exists_mulVec_e0_eq hd
  obtain ⟨b, hb⟩ := exists_mulVec_e0_eq hv
  refine ⟨transposeInv (b * a⁻¹), ?_⟩
  rw [dualMat_transposeInv, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← ha, inv_mulVec_mulVec, hb]

private theorem exists_dualMat_pair {u w u' w' : Fin 3 → F} (hu : u ≠ 0)
    (hw : ∀ t : F, w ≠ t • u) (hu' : u' ≠ 0) (hw' : ∀ t : F, w' ≠ t • u') :
    ∃ g : SL3 F, dualMat g *ᵥ u = u' ∧ dualMat g *ᵥ w = w' := by
  obtain ⟨a, ha₀, ha₁⟩ := exists_mulVec_e0_e1' hu hw
  obtain ⟨b, hb₀, hb₁⟩ := exists_mulVec_e0_e1' hu' hw'
  refine ⟨transposeInv (b * a⁻¹), ?_, ?_⟩
  · rw [dualMat_transposeInv, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← ha₀, inv_mulVec_mulVec, hb₀]
  · rw [dualMat_transposeInv, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← ha₁, inv_mulVec_mulVec, hb₁]

private theorem eq_zero_of_dualMat_mulVec_eq_zero (g : SL3 F) {d : Fin 3 → F}
    (h : dualMat g *ᵥ d = 0) : d = 0 := by
  have e : dualMat g⁻¹ * dualMat g = 1 := by
    rw [← dualMat_mul, inv_mul_cancel, dualMat_one]
  rw [← Matrix.one_mulVec d, ← e, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

private theorem exists_dotProduct_ne_zero {y : Fin 3 → F} (hy : y ≠ 0) :
    ∃ w : Fin 3 → F, w ⬝ᵥ y ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy (funext hcon)
  exact ⟨Pi.single i 1, by rw [single_dotProduct, one_mul]; exact hi⟩

private theorem ne_smul_of_dotProduct {u w y : Fin 3 → F} (hw : w ≠ 0) (hwy : w ⬝ᵥ y = 0)
    (huy : u ⬝ᵥ y ≠ 0) (t : F) : w ≠ t • u := by
  intro ht
  rw [ht, smul_dotProduct, smul_eq_mul] at hwy
  rcases mul_eq_zero.mp hwy with h0 | h0
  · exact hw (by rw [ht, h0, zero_smul])
  · exact huy h0

end Lin

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem exists_good_of_isSecD (hb : 4 < critDist 𝔛) {α β γ ε α' : Vtx 𝔛} (hα : IsMVtx 𝔛 α)
    (hγM : IsMVtx 𝔛 γ) (hαβ : 𝔄 α β) (hβγ : 𝔄 β γ) (hγε : 𝔄 γ ε)
    (hdγ : (puAmalgam h.le).treeGraph.dist γ α' < critDist 𝔛)
    (hdε : (puAmalgam h.le).treeGraph.dist ε α' + 1 < critDist 𝔛)
    (hZ : ¬ ZM 𝔛 α ≤ Qv 𝔛 α') (hH : ¬ ⁅ZM 𝔛 α, Qv 𝔛 γ⁆ ≤ Dloc h.le L γ)
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {C : Subgroup 𝔘}
    (hs : L441.IsSecD h.le L γ ψ true (conjCl (stab 𝔛 γ) (ZM 𝔛 α)) C) :
    ∃ k ∈ stab 𝔛 γ, ¬ ZM 𝔛 (k • α) ≤ Qv 𝔛 α' ∧
      Qv 𝔛 ε ⊓ Subgroup.centralizer (Usup 𝔛 (k • α) (k • β) : Set 𝔘) ≤ Qv 𝔛 γ := by
  classical
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  obtain ⟨n, hn⟩ := hφ.1
  have : CharP F 2 := FFC.charP_two_of_card_pow (by rw [Nat.card_eq_fintype_card, hn])
  have hex₁ := commutator_zm_qv_eq_usup h hb hφ hα hγM hαβ hβγ hH hψs hψ hs
  have hex₂ := usup_eq_of_isSecD h hb hφ hα hγM hαβ hβγ hH hψs hψ hs
  obtain ⟨hUC, hCG, -, hsum, -⟩ := hs
  set V := conjCl (stab 𝔛 γ) (ZM 𝔛 α) with hVdef
  set N := NatSec.ofIsSum hsum with hNdef
  have hZγQ : ZM 𝔛 γ ≤ Qv 𝔛 α' := zm_le_qv_of_dist_lt _ hγM hdγ
  have hUγQ : Uloc h.le L γ ≤ Qv 𝔛 α' := (uloc_le_zm h hfull hγM).trans hZγQ
  have hkγ : ∀ k ∈ stab 𝔛 γ, k • γ = γ := fun k hk => (mem_stab _).mp hk
  have hkαM : ∀ k : 𝔘, IsMVtx 𝔛 (k • α) := fun k => (isMVtx_smul _ k α).mpr hα
  have hkβ : ∀ k ∈ stab 𝔛 γ, 𝔄 γ (k • β) := fun k hk => by
    have := (adj_smul _ k β γ).mpr hβγ
    rw [hkγ k hk] at this
    exact this.symm
  have hex : ∀ g : 𝔘, ⁅ZM 𝔛 (g • α), Qv 𝔛 (g • γ)⁆ = Usup 𝔛 (g • α) (g • β) ∧
      Usup 𝔛 (g • α) (g • β) = Usup 𝔛 (g • γ) (g • β) := by
    intro g
    rw [zm_smul, qv_smul, usup_smul, usup_smul, ← Subgroup.map_commutator, hex₁, hex₂]
    exact ⟨rfl, rfl⟩
  have hUk : ∀ k ∈ stab 𝔛 γ, Usup 𝔛 (k • α) (k • β) = Usup 𝔛 γ (k • β) := fun k hk => by
    have := (hex k).2
    rwa [hkγ k hk] at this
  have hZT : ∀ k ∈ stab 𝔛 γ, ⁅ZM 𝔛 (k • α), Qv 𝔛 (k • β)⁆ ≤ Uloc h.le L γ := fun k hk => by
    have e : ⁅ZM 𝔛 (k • α), Qv 𝔛 (k • β)⁆ = Usup 𝔛 (k • α) (k • β) := by
      rw [Usup, zv_of_isMVtx _ (hkαM k)]
    rw [e, hUk k hk]
    exact usup_le_uloc h hφ hγM (hkβ k hk)
  have hZαs : ZM 𝔛 α ≤ stab 𝔛 γ :=
    ((zm_le_qv_self _ hα hb0).trans (qv_le_qv _ h20 hα hαβ)).trans (qv_le_stab_of_adj _ hβγ)
  have hZαV : ∀ k ∈ stab 𝔛 γ, ZM 𝔛 (k • α) ≤ V := fun k hk => by
    rw [zm_smul]
    exact le_iSup₂_of_le (f := fun g (_ : g ∈ stab 𝔛 γ) => (ZM 𝔛 α).map
      (MulAut.conj g).toMonoidHom) k hk le_rfl
  have hVs : V ≤ stab 𝔛 γ := by
    refine iSup₂_le fun k hk => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (stab 𝔛 γ).mul_mem ((stab 𝔛 γ).mul_mem hk (hZαs hx)) ((stab 𝔛 γ).inv_mem hk)
  have hCV : C ≤ V := hsum.2.1
  have hVn : stab 𝔛 γ ≤ Subgroup.normalizer (V : Set 𝔘) := hsum.1
  have hconjV : ∀ k ∈ stab 𝔛 γ, ∀ v ∈ V, k * v * k⁻¹ ∈ V := fun k hk v hv =>
    (Subgroup.mem_normalizer_iff.mp (hVn hk) v).mp hv
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    have hdαγ : (puAmalgam h.le).treeGraph.dist α γ ≤ 2 := by
      have := dist_triangle 𝔛 α β γ
      rwa [dist_eq_one_of_adj _ hαβ, dist_eq_one_of_adj _ hβγ] at this
    have hVV : V ≤ Vv 𝔛 γ := by
      refine iSup₂_le fun k hk => ?_
      rw [← zm_smul]
      have hdk : (puAmalgam h.le).treeGraph.dist γ (k • α) ≤ 2 := by
        have e := dist_smul _ k γ α
        rw [hkγ k hk] at e
        rw [e, tdist_comm]
        exact hdαγ
      have := zv_le_vv h (α := γ) (ρ := k • α) hdk
      rwa [zv_of_isMVtx _ (hkαM k)] at this
    intro a ha b' hb'
    have hm := Subgroup.commutator_mem_commutator (hVV ha) (hVV hb')
    rw [vv_comm_eq_bot h hb hγM, Subgroup.mem_bot] at hm
    exact commutatorElement_eq_one_iff_mul_comm.mp hm
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := by
    let S : Subgroup 𝔘 :=
      { carrier := {v | v ∈ V ∧ v ^ 2 = 1}
        mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by
          rw [(Commute.mul_pow (hVab a ha.1 b hb.1) 2), ha.2, hb.2, one_mul]⟩
        one_mem' := ⟨V.one_mem, one_pow 2⟩
        inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    have hVS : V ≤ S := by
      refine iSup₂_le fun k hk => ?_
      rw [← zm_smul]
      intro x hx
      refine ⟨hZαV k hk hx, ?_⟩
      rw [← xm_eq_zm h hfull (hkαM k)] at hx
      exact sq_eq_one_of_mem_omegaOneCenterOf hx
    exact fun v hv => (hVS hv).2
  have hVQ : ∀ v ∈ V, ∀ y ∈ Qv 𝔛 γ, ⁅v, y⁆ ∈ Uloc h.le L γ := by
    have hUn := stab_le_normalizer_uloc h γ
    let S : Subgroup 𝔘 :=
      { carrier := {v | v ∈ stab 𝔛 γ ∧ ∀ y ∈ Qv 𝔛 γ, ⁅v, y⁆ ∈ Uloc h.le L γ}
        mul_mem' := fun {a b} ha hb => ⟨(stab 𝔛 γ).mul_mem ha.1 hb.1, fun y hy => by
          have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (Uloc h.le L γ).mul_mem
            ((Subgroup.mem_normalizer_iff.mp (hUn ha.1) _).mp (hb.2 y hy)) (ha.2 y hy)⟩
        one_mem' := ⟨(stab 𝔛 γ).one_mem, fun y _ => by simp⟩
        inv_mem' := fun {a} ha => ⟨(stab 𝔛 γ).inv_mem ha.1, fun y hy => by
          have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (Subgroup.mem_normalizer_iff.mp (hUn ((stab 𝔛 γ).inv_mem ha.1)) _).mp
            ((Uloc h.le L γ).inv_mem (ha.2 y hy))⟩ }
    have hVS : V ≤ S := by
      refine iSup₂_le fun k hk => ?_
      rw [← zm_smul]
      intro x hx
      refine ⟨hVs (hZαV k hk hx), fun y hy => hZT k hk
        (Subgroup.commutator_mem_commutator hx (qv_le_qv _ h20 hγM (hkβ k hk) hy))⟩
    exact fun v hv => (hVS hv).2
  have hCQ : ∀ c ∈ C, ∀ g ∈ stab 𝔛 γ, c⁻¹ * (g * c * g⁻¹) ∈ Qv 𝔛 α' := by
    intro c hc g hg
    have hw : c⁻¹ * (g * c * g⁻¹) ∈ Uloc h.le L γ ⊔ Dloc h.le L γ := by
      have hm : ⁅c⁻¹, g⁆ ∈ ⁅C, stab 𝔛 γ⁆ :=
        Subgroup.commutator_mem_commutator (C.inv_mem hc) hg
      have e : ⁅c⁻¹, g⁆ = c⁻¹ * (g * c * g⁻¹) := by
        rw [commutatorElement_def, inv_inv]; group
      rw [← e]
      exact hCG hm
    have hwV : c⁻¹ * (g * c * g⁻¹) ∈ V :=
      V.mul_mem (V.inv_mem (hCV hc)) (hconjV g hg c (hCV hc))
    have hDU : Dloc h.le L γ ≤ Subgroup.normalizer (Uloc h.le L γ : Set 𝔘) :=
      ((dloc_le_qv h hγM).trans (qv_le_stab _ γ)).trans (stab_le_normalizer_uloc h γ)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDU] at hw
    obtain ⟨u, hu, e, he, hue⟩ := hw
    have heV : e ∈ V := by
      have e1 : e = u⁻¹ * (c⁻¹ * (g * c * g⁻¹)) := by rw [← hue]; group
      rw [e1]
      exact V.mul_mem (V.inv_mem (hCV (hUC hu))) hwV
    have heQ : e ∈ Qv 𝔛 γ := dloc_le_qv h hγM he
    have hecen : e ∈ Subgroup.centralizer (Qv 𝔛 γ : Set 𝔘) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : ⁅e, y⁆ ∈ Uloc h.le L γ := hVQ e heV y hy
      have h2 : ⁅e, y⁆ ∈ Dloc h.le L γ := by
        rw [commutatorElement_def, mul_assoc, mul_assoc]
        refine (Dloc h.le L γ).mul_mem he ?_
        rw [← mul_assoc]
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_dloc h γ
          (qv_le_stab _ γ hy)) _).mp ((Dloc h.le L γ).inv_mem he)
      have h3 : ⁅e, y⁆ ∈ Uloc h.le L γ ⊓ Dloc h.le L γ := ⟨h1, h2⟩
      rw [uloc_inf_dloc h hφ γ, Subgroup.mem_bot] at h3
      exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    have heX : e ∈ XM 𝔛 γ :=
      Subgroup.subset_closure ⟨⟨heQ, hecen⟩, hV2 e heV⟩
    rw [xm_eq_zm h hfull hγM] at heX
    rw [← hue]
    exact (Qv 𝔛 α').mul_mem (hUγQ hu) (hZγQ heX)
  have hεs : Qv 𝔛 ε ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hγε.symm
  have hεH : ¬ IsMVtx 𝔛 ε := by
    rw [← isMVtx_iff_of_adj _ hγε]
    exact hγM
  have hPε : IsPGroup 2 ↥(natImage ψ (Qv 𝔛 ε)) :=
    ((isPGroup_qv _ h20 hεH).of_equiv (Subgroup.subgroupOfEquivOfLe hεs).symm).map (toSL3 ψ)
  have h2ε : Module.finrank F (commN (natImage ψ (Qv 𝔛 ε))) = 2 :=
    finrank_commN_qv h hφ hC hb hγM hγε hψ
  obtain ⟨y₀, hy₀f, hy₀⟩ : ∃ y₀ ∈ fixN (natImage ψ (Qv 𝔛 ε)), y₀ ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun hbot => ?_
    have hpos := S46.finrank_fixN_pos hPε
    rw [hbot, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  have hy₀c : y₀ ∈ commN (natImage ψ (Qv 𝔛 ε)) := fixN_le_commN_of_finrank_eq_two hPε h2ε hy₀f
  have hann : ∀ k ∈ stab 𝔛 γ, ∀ x ∈ ZM 𝔛 (k • α),
      commN (natImage ψ (Qv 𝔛 (k • β))) ≤ orthN (N.coord x) := by
    intro k hk x hx
    refine commN_le_orthN fun g hg => ?_
    obtain ⟨t, ht, rfl⟩ := mem_natImage.mp hg
    have hxV : x ∈ V := hZαV k hk hx
    have hcm : ⁅x⁻¹, (t : 𝔘)⁆ ∈ C :=
      hUC (hZT k hk (Subgroup.commutator_mem_commutator ((ZM 𝔛 (k • α)).inv_mem hx) ht))
    have e1 := N.coord_conj t hxV
    rw [natAct_true] at e1
    rw [← e1]
    have e2 : (t : 𝔘) * x * (t : 𝔘)⁻¹ = x * ⁅x⁻¹, (t : 𝔘)⁆ := by
      rw [commutatorElement_def]; group
    rw [e2, N.coord_mul hxV (hCV hcm), (N.coord_eq_zero_iff (hCV hcm)).mpr hcm, add_zero]
  have hcrit : ∀ k ∈ stab 𝔛 γ, ∀ x ∈ ZM 𝔛 (k • α), N.coord x ⬝ᵥ y₀ ≠ 0 →
      Qv 𝔛 ε ⊓ Subgroup.centralizer (Usup 𝔛 (k • α) (k • β) : Set 𝔘) ≤ Qv 𝔛 γ := by
    intro k hk x hx hxy
    have hXs : Qv 𝔛 ε ⊓ Subgroup.centralizer (Usup 𝔛 (k • α) (k • β) : Set 𝔘) ≤ stab 𝔛 γ :=
      inf_le_left.trans hεs
    have hXc : Qv 𝔛 ε ⊓ Subgroup.centralizer (Usup 𝔛 (k • α) (k • β) : Set 𝔘) ≤
        Subgroup.centralizer (Usup 𝔛 γ (k • β) : Set 𝔘) := by
      rw [← hUk k hk]
      exact inf_le_right
    have h1 := commN_le_fixN_of_le_centralizer h hφ hγM (hkβ k hk) hψ hXs
      (Subgroup.le_centralizer_iff.mp hXc)
    have h2 : y₀ ∈ fixN (natImage ψ (Qv 𝔛 ε ⊓
        Subgroup.centralizer (Usup 𝔛 (k • α) (k • β) : Set 𝔘))) :=
      fixN_anti (natImage_mono inf_le_left) hy₀f
    have h3 : ¬ Submodule.span F {y₀} ≤ commN (natImage ψ (Qv 𝔛 (k • β))) := by
      intro hle
      exact hxy (hann k hk x hx (hle (Submodule.mem_span_singleton_self y₀)))
    have htop := sup_eq_top_of_not_le (finrank_commN_qv h hφ hC hb hγM (hkβ k hk) hψ) h3
    refine le_qv_of_fixN_eq_top h hφ hγM hψ hXs (eq_top_iff.mpr ?_)
    rw [← htop]
    exact sup_le h1 ((Submodule.span_singleton_le_iff_mem _ _).mpr h2)
  obtain ⟨k₃, hk₃, hk₃β⟩ := exists_mem_stab_smul _ hβγ.symm hγε
  have hk₃Q : ZM 𝔛 (k₃ • α) ≤ Qv 𝔛 α' := by
    refine zm_le_qv_of_dist_lt _ (hkαM k₃) ?_
    have hadj : 𝔄 (k₃ • α) ε := by
      rw [← hk₃β]
      exact (adj_smul _ k₃ α β).mpr hαβ
    have := dist_triangle 𝔛 (k₃ • α) ε α'
    rw [dist_eq_one_of_adj _ hadj] at this
    omega
  have hk₃y : ∀ x ∈ ZM 𝔛 (k₃ • α), N.coord x ⬝ᵥ y₀ = 0 := by
    intro x hx
    have := hann k₃ hk₃ x hx
    rw [hk₃β] at this
    exact this hy₀c
  by_contra hall
  have hgoodQ : ∀ k ∈ stab 𝔛 γ, ∀ x ∈ ZM 𝔛 (k • α), N.coord x ⬝ᵥ y₀ ≠ 0 →
      ZM 𝔛 (k • α) ≤ Qv 𝔛 α' := by
    intro k hk x hx hxy
    by_contra hn
    exact hall ⟨k, hk, hn, hcrit k hk x hx hxy⟩
  apply hZ
  intro z hz
  have hzV : z ∈ V := le_conjCl _ _ hz
  have hzk : ∀ k ∈ stab 𝔛 γ, k * z * k⁻¹ ∈ ZM 𝔛 (k • α) := fun k _ => by
    rw [zm_smul]
    exact ⟨z, hz, rfl⟩
  have hcz : ∀ k : ↥(stab 𝔛 γ), N.coord ((k : 𝔘) * z * (k : 𝔘)⁻¹) =
      dualMat (toSL3 ψ k) *ᵥ N.coord z := fun k => by
    rw [N.coord_conj k hzV, natAct_true]
  have hψ3 := toSL3_surjective hψs
  have hE : ∀ k : ↥(stab 𝔛 γ), (dualMat (toSL3 ψ k) *ᵥ N.coord z) ⬝ᵥ y₀ ≠ 0 →
      (k : 𝔘) * z * (k : 𝔘)⁻¹ ∈ Qv 𝔛 α' := fun k hk =>
    hgoodQ k k.2 _ (hzk k k.2) (by rw [hcz k]; exact hk) (hzk k k.2)
  obtain ⟨v₀, hv₀⟩ := exists_dotProduct_ne_zero hy₀
  have hv₀0 : v₀ ≠ 0 := fun h0 => hv₀ (by rw [h0, zero_dotProduct])
  by_cases hd0 : N.coord z = 0
  ·
    have hzC : z ∈ C := (N.coord_eq_zero_iff hzV).mp hd0
    obtain ⟨k, hk, x, hx, hxy⟩ : ∃ k ∈ stab 𝔛 γ, ∃ x ∈ ZM 𝔛 (k • α), N.coord x ⬝ᵥ y₀ ≠ 0 := by
      by_contra hno
      push Not at hno
      let S : Subgroup 𝔘 :=
        { carrier := {v | v ∈ V ∧ N.coord v ⬝ᵥ y₀ = 0}
          mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by
            rw [N.coord_mul ha.1 hb.1, add_dotProduct, ha.2, hb.2, add_zero]⟩
          one_mem' := ⟨V.one_mem, by rw [N.coord_one, zero_dotProduct]⟩
          inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by
            rw [N.coord_inv ha.1, neg_dotProduct, ha.2, neg_zero]⟩ }
      have hVS : V ≤ S := by
        refine iSup₂_le fun k hk => ?_
        rw [← zm_smul]
        intro x hx
        exact ⟨hZαV k hk hx, hno k hk x hx⟩
      obtain ⟨v, hvV, hv⟩ := N.exists_coord_eq v₀
      exact hv₀ (hv ▸ (hVS hvV).2)
    have h1 : k * z * k⁻¹ ∈ Qv 𝔛 α' := hgoodQ k hk x hx hxy (hzk k hk)
    have h2 := hCQ z hzC k hk
    have e : z = (k * z * k⁻¹) * (z⁻¹ * (k * z * k⁻¹))⁻¹ := by group
    rw [e]
    exact (Qv 𝔛 α').mul_mem h1 ((Qv 𝔛 α').inv_mem h2)
  by_cases hdy : N.coord z ⬝ᵥ y₀ ≠ 0
  ·
    have := hgoodQ 1 (stab 𝔛 γ).one_mem z (by rw [one_smul]; exact hz) hdy
    rw [one_smul] at this
    exact this hz
  push Not at hdy
  have hθ : ∀ h' : ↥(stab 𝔛 γ), dualMat (toSL3 ψ h') *ᵥ N.coord z = N.coord z →
      z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹) ∈ Qv 𝔛 α' := by
    intro h' hh'
    obtain ⟨g, hg⟩ := exists_dualMat_mulVec_eq hd0 hv₀0
    obtain ⟨k, rfl⟩ := hψ3 g
    have hk1 : (dualMat (toSL3 ψ k) *ᵥ N.coord z) ⬝ᵥ y₀ ≠ 0 := by rw [hg]; exact hv₀
    have hk2 : (dualMat (toSL3 ψ (k * h')) *ᵥ N.coord z) ⬝ᵥ y₀ ≠ 0 := by
      rw [map_mul, dualMat_mul, ← Matrix.mulVec_mulVec, hh']
      exact hk1
    have e1 := hE k hk1
    have e2 := hE (k * h') hk2
    have hθV : z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹) ∈ V :=
      V.mul_mem (V.inv_mem hzV) (hconjV h' h'.2 z hzV)
    have hθC : z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹) ∈ C := by
      rw [← N.coord_eq_zero_iff hθV, N.coord_mul (V.inv_mem hzV) (hconjV h' h'.2 z hzV),
        N.coord_inv hzV, hcz h', hh', neg_add_cancel]
    have e3 : ((k * h' : ↥(stab 𝔛 γ)) : 𝔘) * z * ((k * h' : ↥(stab 𝔛 γ)) : 𝔘)⁻¹ =
        ((k : 𝔘) * z * (k : 𝔘)⁻¹) *
          ((k : 𝔘) * (z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹)) * (k : 𝔘)⁻¹) := by
      rw [Subgroup.coe_mul]; group
    rw [e3] at e2
    have h4 : (k : 𝔘) * (z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹)) * (k : 𝔘)⁻¹ ∈ Qv 𝔛 α' := by
      have := (Qv 𝔛 α').mul_mem ((Qv 𝔛 α').inv_mem e1) e2
      rwa [inv_mul_cancel_left] at this
    have h5 := hCQ _ hθC k k.2
    have e4 : z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹) =
        ((k : 𝔘) * (z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹)) * (k : 𝔘)⁻¹) *
          ((z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹))⁻¹ *
            ((k : 𝔘) * (z⁻¹ * ((h' : 𝔘) * z * (h' : 𝔘)⁻¹)) * (k : 𝔘)⁻¹))⁻¹ := by
      group
    rw [e4]
    exact (Qv 𝔛 α').mul_mem h4 ((Qv 𝔛 α').inv_mem h5)
  set k₃' : ↥(stab 𝔛 γ) := ⟨k₃, hk₃⟩ with hk₃'
  have hd₃y : (dualMat (toSL3 ψ k₃') *ᵥ N.coord z) ⬝ᵥ y₀ = 0 := by
    rw [← hcz k₃']
    exact hk₃y _ (hzk k₃ hk₃)
  have hd₃0 : dualMat (toSL3 ψ k₃') *ᵥ N.coord z ≠ 0 := fun h0 =>
    hd0 (eq_zero_of_dualMat_mulVec_eq_zero _ h0)
  have hv₀d₃ : v₀ + dualMat (toSL3 ψ k₃') *ᵥ N.coord z ≠ 0 := fun h0 =>
    hv₀ (by
      have := congrArg (· ⬝ᵥ y₀) h0
      simp only [add_dotProduct, hd₃y, add_zero, zero_dotProduct] at this
      exact this)
  obtain ⟨ga, hga⟩ := exists_dualMat_mulVec_eq hd0 hv₀0
  obtain ⟨gb, hgb⟩ := exists_dualMat_mulVec_eq hd0 hv₀d₃
  obtain ⟨gg, hgg₁, hgg₂⟩ := exists_dualMat_pair hv₀0
    (ne_smul_of_dotProduct hd₃0 hd₃y hv₀) hv₀0 (ne_smul_of_dotProduct hd0 hdy hv₀)
  obtain ⟨a, rfl⟩ := hψ3 ga
  obtain ⟨b, rfl⟩ := hψ3 gb
  obtain ⟨g, rfl⟩ := hψ3 gg
  have hea := hE a (by rw [hga]; exact hv₀)
  have heb := hE b (by rw [hgb, add_dotProduct, hd₃y, add_zero]; exact hv₀)
  have hek₃ : (k₃ : 𝔘) * z * (k₃ : 𝔘)⁻¹ ∈ Qv 𝔛 α' := hk₃Q (hzk k₃ hk₃)
  have hza := hconjV a a.2 z hzV
  have hzb := hconjV b b.2 z hzV
  have hz₃ := hconjV k₃ hk₃ z hzV
  have hx₁C : ((a : 𝔘) * z * (a : 𝔘)⁻¹) * ((k₃ : 𝔘) * z * (k₃ : 𝔘)⁻¹) *
      ((b : 𝔘) * z * (b : 𝔘)⁻¹) ∈ C := by
    rw [← N.coord_eq_zero_iff (V.mul_mem (V.mul_mem hza hz₃) hzb),
      N.coord_mul (V.mul_mem hza hz₃) hzb, N.coord_mul hza hz₃, hcz a, hcz b,
      show N.coord ((k₃ : 𝔘) * z * (k₃ : 𝔘)⁻¹) = dualMat (toSL3 ψ k₃') *ᵥ N.coord z from hcz k₃',
      hga, hgb, ← two_smul F, CharTwo.two_eq_zero, zero_smul]
  have hx₁Q : ((a : 𝔘) * z * (a : 𝔘)⁻¹) * ((k₃ : 𝔘) * z * (k₃ : 𝔘)⁻¹) *
      ((b : 𝔘) * z * (b : 𝔘)⁻¹) ∈ Qv 𝔛 α' :=
    (Qv 𝔛 α').mul_mem ((Qv 𝔛 α').mul_mem hea hek₃) heb
  have hgx : (g : 𝔘) * (((a : 𝔘) * z * (a : 𝔘)⁻¹) * ((k₃ : 𝔘) * z * (k₃ : 𝔘)⁻¹) *
      ((b : 𝔘) * z * (b : 𝔘)⁻¹)) * (g : 𝔘)⁻¹ ∈ Qv 𝔛 α' := by
    have h1 := hCQ _ hx₁C g g.2
    have := (Qv 𝔛 α').mul_mem hx₁Q h1
    rwa [mul_inv_cancel_left] at this
  have hga' := hE (g * a) (by
    rw [map_mul, dualMat_mul, ← Matrix.mulVec_mulVec, hga, hgg₁]
    exact hv₀)
  have hgb' := hE (g * b) (by
    rw [map_mul, dualMat_mul, ← Matrix.mulVec_mulVec, hgb, Matrix.mulVec_add, hgg₁, hgg₂,
      add_dotProduct, hdy, add_zero]
    exact hv₀)
  have hgk₃ : ((g * k₃' : ↥(stab 𝔛 γ)) : 𝔘) * z * ((g * k₃' : ↥(stab 𝔛 γ)) : 𝔘)⁻¹ ∈
      Qv 𝔛 α' := by
    have e : ((g * k₃' : ↥(stab 𝔛 γ)) : 𝔘) * z * ((g * k₃' : ↥(stab 𝔛 γ)) : 𝔘)⁻¹ =
        (((g * a : ↥(stab 𝔛 γ)) : 𝔘) * z * ((g * a : ↥(stab 𝔛 γ)) : 𝔘)⁻¹)⁻¹ *
          ((g : 𝔘) * (((a : 𝔘) * z * (a : 𝔘)⁻¹) * ((k₃ : 𝔘) * z * (k₃ : 𝔘)⁻¹) *
            ((b : 𝔘) * z * (b : 𝔘)⁻¹)) * (g : 𝔘)⁻¹) *
          (((g * b : ↥(stab 𝔛 γ)) : 𝔘) * z * ((g * b : ↥(stab 𝔛 γ)) : 𝔘)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, hk₃']
      group
    rw [e]
    exact (Qv 𝔛 α').mul_mem ((Qv 𝔛 α').mul_mem ((Qv 𝔛 α').inv_mem hga') hgx)
      ((Qv 𝔛 α').inv_mem hgb')
  have hfix : dualMat (toSL3 ψ (g * k₃')) *ᵥ N.coord z = N.coord z := by
    rw [map_mul, dualMat_mul, ← Matrix.mulVec_mulVec, hgg₂]
  have h6 := hθ (g * k₃') hfix
  have e : z = (((g * k₃' : ↥(stab 𝔛 γ)) : 𝔘) * z * ((g * k₃' : ↥(stab 𝔛 γ)) : 𝔘)⁻¹) *
      (z⁻¹ * (((g * k₃' : ↥(stab 𝔛 γ)) : 𝔘) * z *
        ((g * k₃' : ↥(stab 𝔛 γ)) : 𝔘)⁻¹))⁻¹ := by
    group
  rw [e]
  exact (Qv 𝔛 α').mul_mem hgk₃ ((Qv 𝔛 α').inv_mem h6)

end Vertex

end X441

theorem s441C1Good_holds : S441C1Good := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc hfail ψ hψs hψ C hs
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hH' : ¬ ⁅ZM (puAmalgam h.le) α, Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2)⁆ ≤
      Dloc h.le L (geo (puAmalgam h.le) α α' 2) := by
    intro hle
    apply hfail 1
    rw [one_smul, one_smul]
    intro hn
    exact absurd hle hn
  refine X441.exists_good_of_isSecD h hH.2.2 hb hc.1 (isMVtx_geo_two _ h20 hb0 hc)
    (adj_geo_one_of_isCritical _ hb0 hc) (adj_geo _ (i := 1) (by omega))
    (adj_geo _ (i := 2) (by omega)) ?_ ?_ hc.2.2 hH' hψs hψ hs
  · rw [dist_geo_right _ (by omega), hd]
    omega
  · rw [dist_geo_right _ (by omega), hd]
    omega

theorem s441C1Dual_of_s43 (h43 : S43) : S441C1Dual :=
  s441C1Dual_of h43 s441C1Good_holds

end CFSG.Quasithin.MS93.S4A
