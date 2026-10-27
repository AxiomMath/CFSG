module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSuppliers
import CFSG.LocalAnalysis.StandardType.GGQTwoPThree
import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfType
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
public import CFSG.LocalAnalysis.StandardType.GGQ2NoWeylA3Holds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
import CFSG.LocalAnalysis.StandardType.GGQTwoPhanDM4Model

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.PhanDn.QTwo

theorem ggQTwoM4_automizer_fix {G : Type} [Group G] {L Bs : Subgroup G} {x : G} (hxB : x ∈ Bs)
    (hxC : x ∈ Subgroup.centralizer (L : Set G)) :
    ∀ φ ∈ ggAutomizer L Bs, φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
  intro φ hφ
  induction hφ using Subgroup.closure_induction with
  | mem φ hφ =>
    obtain ⟨g, hg, -, hgφ⟩ := hφ
    apply Subtype.ext
    rw [hgφ]
    have hc : g * x = x * g := Subgroup.mem_centralizer_iff.mp hxC g hg
    simp [mul_assoc, hc]
  | one => rfl
  | mul φ ψ _ _ hφ hψ =>
    change φ (ψ ⟨x, hxB⟩) = ⟨x, hxB⟩
    rw [hψ, hφ]
  | inv φ _ hφ =>
    have h : φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := hφ
    change φ.symm ⟨x, hxB⟩ = ⟨x, hxB⟩
    exact (MulEquiv.symm_apply_eq φ).mpr h.symm


theorem ggQTwoM4_card_bstar {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {e' : Fin 4 ≃ ι}
    (hM : M = (ggCoxeterMatrixD 4).reindex e') : Nat.card Bs = p ^ 4 := by
  refine le_antisymm ?_ (ggDk_card_bstar_ge hcfg hpres (k := 4) (by norm_num) hM)
  have hW : GGWeylOfType p (ggCoxeterMatrixD 4) (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  simpa using hcfg.card_le_pow_of_weylOfType hTBF hWI (le_refl _) hW

theorem ggQTwoM4_card_automizer_le {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) {e' : Fin 4 ≃ ι}
    (hM : M = (ggCoxeterMatrixD 4).reindex e') (hcard : Nat.card Bs = 3 ^ 4) :
    Nat.card ↥(ggAutomizer L Bs) ≤ 24 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := hcfg.1.1.2.1.2.1
  have hW : GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hind : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ ∈ ggInduced ⊤ Bs := fun φ hφ =>
    mem_ggInduced_top_of_mem_ggAutomizer (ggAutomizerJoin_le_top L Bs 𝒦 hφ)
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := 3) hBs
  obtain ⟨e₂, h, α, hα, hrefl, hC⟩ := SpJoinRefl.exists_cartan_reflections_D
    (by norm_num : (3 : ℕ) ≠ 2) (ggRouteCfg_noTransvection hcfg) (le_refl 4) hW hind ιV
  have hV : Nat.card V = 3 ^ 4 := (card_eq_of_ggLin ιV).symm.trans hcard
  obtain ⟨hxB, hxC⟩ := hcfg.1.1.x_facts
  have hfix := ggQTwoM4_automizer_fix hxB hxC
  have hx1 : x ≠ 1 := by
    intro hx
    have hord := hcfg.1.1.orderOf_x
    rw [hx, orderOf_one] at hord
    exact absurd hord.symm (by norm_num)
  have hv : ιV (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) ≠ 0 := by
    intro h0
    have h1 := ιV.injective (h0.trans (map_zero ιV).symm)
    exact hx1 (congrArg Subtype.val (Additive.ofMul.injective h1))
  let ψ₀ : (ggCoxeterMatrixD 4).Group →* (V ≃ₗ[ZMod 3] V) :=
    (ggLin (p := 3) ιV).comp
      ((Subgroup.subtype (ggAutomizerJoin L Bs 𝒦)).comp e₂.toMonoidHom)
  have hgen : Subgroup.closure (Set.range (ggCoxeterMatrixD 4).simple) = ⊤ :=
    PresentedGroup.closure_range_of _
  have hψ₀ : ∀ w : (ggCoxeterMatrixD 4).Group,
      ψ₀ w ∈ Subgroup.closure (Set.range fun i => Module.reflection (hα i)) := by
    intro w
    have hw : w ∈ Subgroup.closure (Set.range (ggCoxeterMatrixD 4).simple) := by
      rw [hgen]
      trivial
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      have h1 : ψ₀ ((ggCoxeterMatrixD 4).simple i) = Module.reflection (hα i) := hrefl i
      rw [h1]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    | one => simpa using Subgroup.one_mem _
    | mul x y _ _ hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa using Subgroup.inv_mem _ hx
  have hmem : ∀ φ ∈ ggAutomizer L Bs,
      ggLin (p := 3) ιV φ ∈ Subgroup.closure (Set.range fun i => Module.reflection (hα i)) := by
    intro φ hφ
    have hφA : φ ∈ ggAutomizerJoin L Bs 𝒦 := ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hφ
    obtain ⟨w, hw⟩ := e₂.surjective ⟨φ, hφA⟩
    have : ψ₀ w = ggLin (p := 3) ιV φ := by
      simp [ψ₀, hw]
    rw [← this]
    exact hψ₀ w
  let f : ↥(ggAutomizer L Bs) →
      {g : ↥(Subgroup.closure (Set.range fun i => Module.reflection (hα i))) //
        (g : V ≃ₗ[ZMod 3] V) (ιV (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) =
          ιV (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))} :=
    fun φ => ⟨⟨ggLin (p := 3) ιV φ.1, hmem φ.1 φ.2⟩,
      (ggLin_fix_iff ιV φ.1 ⟨x, hxB⟩).mp (hfix φ.1 φ.2)⟩
  have hf : Function.Injective f := by
    intro φ₁ φ₂ h12
    apply Subtype.ext
    exact ggLin_injective (p := 3) ιV (congrArg (fun g => (g.1 : V ≃ₗ[ZMod 3] V)) h12)
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  haveI : Finite {g : ↥(Subgroup.closure (Set.range fun i => Module.reflection (hα i))) //
      (g : V ≃ₗ[ZMod 3] V) (ιV (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) =
        ιV (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))} :=
    Finite.of_injective (fun g => ((g.1 : V ≃ₗ[ZMod 3] V) : V → V))
      fun g₁ g₂ h12 => Subtype.ext (Subtype.ext (DFunLike.coe_injective h12))
  exact (Nat.card_le_card_of_injective f hf).trans
    (M4Model.d4Mod3_stab_card_le hV h α hα hC hv)


theorem ggQTwoM4_card_automizer_ge (hRk1 : GGSecFiveRk1PhanInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hns : ¬ GGSplitLie 3 L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) {e' : Fin 4 ≃ ι}
    (hM : M = (ggCoxeterMatrixD 4).reindex e')
    (h6 : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6)
    (hcard : Nat.card Bs = 3 ^ 4) : 48 ≤ Nat.card ↥(ggAutomizer L Bs) := by
  obtain ⟨r, hrA, hrC, hr6⟩ := h6
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 :=
    GGIsWeylMatrixAD.le_three (Or.inr ⟨4, e', le_refl _, hM⟩)
  have hlab := ggL_baseLabel_qTwo_of_rk1 hRk1 hcfg hns hpres hle3 hrA hrC hr6
  have hlabQ : GGInnerDiagOnLabel GGLabQTwo 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by unfold GGLabQTwo; have := h.1; omega) hlab
  exact ggQ2_rankFour_automizer_ge hcfg.1.1 hlabQ hcard

theorem ggSecFivePhanDQTwo_m4 (hRk1 : GGSecFiveRk1PhanInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hNotReg : ¬ GGSecFiveTier1Region p B Bs x L D J) (hns : ¬ GGSplitLie p L)
    {ι : Type} (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (e' : Fin 4 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 4).reindex e')
    (h6 : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6) :
    GGSecFiveData p B x L D J ∨
      ∃ (U : Fin 4 → Subgroup G) (W : Fin 4 → Fin 4 → Subgroup G),
        QTwoWeakPhanSystemD (GaloisField 2 2) 4 (ggG0 p B x L D J) U W := by
  left
  exfalso
  obtain ⟨r, hrA, hrC, h6'⟩ := h6
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg M e hpres hrA hrC h6'
  subst hp3
  have hcard : Nat.card Bs = 3 ^ 4 := ggQTwoM4_card_bstar hTBF hWI hcfg hpres hM
  have h24 := ggQTwoM4_card_automizer_le hcfg hpres hM hcard
  have h48 := ggQTwoM4_card_automizer_ge hRk1 hcfg hns hpres hM ⟨r, hrA, hrC, h6'⟩ hcard
  omega

theorem ggSecFivePhanDQTwoFour_of_inputs (hRk1 : GGSecFiveRk1PhanInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGSecFivePhanDQTwoFour := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hNotReg hns ι M e hpres m e' hm hM h6
  have hm4 : m = 4 := hm
  subst hm4
  exact ggSecFivePhanDQTwo_m4 hRk1 hTBF hWI hcfg hNotReg hns M e hpres e' hM h6

end CFSG.StandardType.QTwo

end
