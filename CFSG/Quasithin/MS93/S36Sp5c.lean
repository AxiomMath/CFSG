module

public import CFSG.Quasithin.MS93.S36SpY

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}

namespace PairHyp

variable {d : SpFrame h} {χ : MulAut ↥T} (hp : PairHyp d χ)
include hp

theorem not_le_normalClosure {v : V4 d.F} (hx : XData d (tImage χ (Z0q M T)) v) :
    ¬ ⁅normalClosureIn M (tImage χ⁻¹ (Yc d χ v)), L⁆ ≤ Z0q M T := by
  intro hRL
  set Y := tImage χ⁻¹ (Yc d χ v) with hYdef
  set R := normalClosureIn M Y with hRdef
  set Z := Z0q M T with hZdef
  have hE := hp.actsMat_E
  have hP := actsMat_P hx
  have hPM : tImage χ (pCoreOf 2 M) ≤ M := tImage_le_M h χ _
  obtain ⟨l, hl, hlY, -⟩ := hp.exists_pre_le_Yc hx
  have hYcT : Yc d χ v ≤ T := Yc_le.trans (inf_le_right.trans (tImage_le _ _))
  have hYT : Y ≤ T := tImage_le _ _
  have hYM : Y ≤ M := tImage_le_M h _ _
  have hYle : Y ≤ tImage χ⁻¹ Z ⊓ pCoreOf 2 M := by
    have := S36SP.tImage_mono χ⁻¹ (Yc_le (d := d) (χ := χ) (v := v))
    rwa [tImage_inf, tImage_inv_tImage χ h.pCore_le] at this
  have hYn : T ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_tImage χ⁻¹ (le_normalizer_Yc hx hE)
  have hZn : M ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_Z0q M T
  have hZM : Z ≤ M := Z0q_le M T
  have hRn : M ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosureIn_le M Y)).1
      (normalClosureIn_normal M Y)
  have hYR : Y ≤ R := le_normalClosureIn hYM
  have hcZ : ∀ g ∈ M, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z :=
    fun g hg z hz => (Subgroup.mem_normalizer_iff.1 (hZn hg) z).1 hz
  set A := Y ⊔ Z with hAdef
  have hAL : ∀ a ∈ A, ∀ l ∈ L, ⁅a, l⁆ ∈ Z := by
    let K : Subgroup G :=
      { carrier := {a | a ∈ M ∧ ∀ l ∈ L, ⁅a, l⁆ ∈ Z}
        one_mem' := ⟨M.one_mem, fun l _ => by
          rw [commutatorElement_one_left]
          exact Z.one_mem⟩
        mul_mem' := by
          rintro a₁ a₂ ⟨ha₁, h₁⟩ ⟨ha₂, h₂⟩
          refine ⟨M.mul_mem ha₁ ha₂, fun l hl => ?_⟩
          have e : ⁅a₁ * a₂, l⁆ = (a₁ * ⁅a₂, l⁆ * a₁⁻¹) * ⁅a₁, l⁆ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact Z.mul_mem (hcZ _ ha₁ _ (h₂ l hl)) (h₁ l hl)
        inv_mem' := by
          rintro a ⟨ha, h₁⟩
          refine ⟨M.inv_mem ha, fun l hl => ?_⟩
          have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact hcZ _ (M.inv_mem ha) _ (Z.inv_mem (h₁ l hl)) }
    have hRK : R ≤ K := fun r hr => ⟨normalClosureIn_le M Y hr, fun l hl =>
      hRL (Subgroup.commutator_mem_commutator hr hl)⟩
    have hZK : Z ≤ K := fun z hz => ⟨hZM hz, fun l hl =>
      Uq_le_Z0q h.L_le (Subgroup.commutator_mem_commutator hz hl)⟩
    exact fun a ha => (sup_le (hYR.trans hRK) hZK ha).2
  have hAM : A ≤ M := sup_le hYM hZM
  have hAn : M ≤ Subgroup.normalizer (A : Set G) := by
    have hTA : T ≤ Subgroup.normalizer (A : Set G) := le_normalizer_sup hYn (h.le.trans hZn)
    have key : ∀ l ∈ L, ∀ a ∈ A, l * a * l⁻¹ ∈ A := by
      intro l hl a ha
      have e : l * a * l⁻¹ = ⁅a, l⁆⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact A.mul_mem (Subgroup.mem_sup_right (Z.inv_mem (hAL a ha l hl))) ha
    have hLA : L ≤ Subgroup.normalizer (A : Set G) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro a
      refine ⟨key l hl a, fun ha => ?_⟩
      have := key l⁻¹ (L.inv_mem hl) _ ha
      simpa [mul_assoc] using this
    rw [h.eq_sup]
    exact sup_le hLA hTA
  set N := normalClosureIn M (tImage χ⁻¹ Z ⊓ pCoreOf 2 M) with hNdef
  have hNn : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosureIn_le M _)).1
      (normalClosureIn_normal M _)
  have hNQ : N ≤ pCoreOf 2 M :=
    normalClosureIn_le_of (pCoreOf_le' M)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le' M)).2 (le_normalizer_pCoreOf M))
      (inf_le_left.trans inf_le_right)
  have hNA : N ≤ Subgroup.centralizer (A : Set G) := by
    have hCn : M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :
        Set G) :=
      le_normalizer_inf (fun _ hm => (Subgroup.mem_normalizer_iff.2 fun x =>
        ⟨fun hx => M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm), fun hx => by
          simpa [mul_assoc] using M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm⟩))
        (le_normalizer_centralizer hAn)
    refine (normalClosureIn_le_of inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hCn) ?_).trans inf_le_right
    rintro n ⟨⟨hnZ, hnQ⟩, hnM⟩
    have hcent : A ≤ Subgroup.centralizer ({n} : Set G) := by
      refine sup_le (fun y hy => ?_) (fun z hz => ?_) <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      ·
        obtain ⟨t₁, ht₁, rfl⟩ := mem_tImage.1 (hYle hy).1
        obtain ⟨t₂, ht₂, rfl⟩ := mem_tImage.1 hnZ
        have h1 : (t₂ : G) * t₁ = t₁ * t₂ :=
          A4.mul_comm_of_mem_omegaOneCenterOf (h.Z0q_le_Xq ht₂) (h.Z0q_le_Xq ht₁)
        have h2 : t₂ * t₁ = t₁ * t₂ := Subtype.ext h1
        have h3 := congrArg (fun t => ((χ⁻¹ t : ↥T) : G)) h2
        simp only [map_mul, Subgroup.coe_mul] at h3
        exact h3.symm
      · exact Subgroup.mem_centralizer_iff.1 (h.pCoreOf_le_centralizer_Z0q hnQ) z hz
    exact ⟨hnM, Subgroup.mem_centralizer_iff.2 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.1 (hcent ha)⟩
  have hχN : tImage χ N ≤ T ⊓ Subgroup.centralizer (Yc d χ v : Set G) := by
    have h1 : N ≤ T ⊓ Subgroup.centralizer (Y : Set G) :=
      le_inf (hNQ.trans h.pCore_le) (hNA.trans (Subgroup.centralizer_le
        (show (Y : Set G) ⊆ (A : Set G) from fun y hy => Subgroup.mem_sup_left hy)))
    have h2 := S36SP.tImage_mono χ h1
    rwa [← tImage_centralizer χ hYT, hYdef, tImage_tImage_inv χ hYcT] at h2
  have hUN : ⁅Uq M T L, tImage χ N⁆ ≤ Yc d χ v := by
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have hxP : x ∈ tImage χ (pCoreOf 2 M) := S36SP.tImage_mono χ hNQ hx
    obtain ⟨g, hg⟩ := hP x hxP
    have hxM := hPM hxP
    have hgl : g ∈ fixer l := by
      rw [mem_fixer]
      intro w hw
      obtain ⟨uw, huw⟩ := d.surj (Multiplicative.ofAdd w)
      have huwY : (uw : G) ∈ Yc d χ v := hlY ((d.mem_pre_coe uw).2 (by rw [huw]; exact hw))
      have hc := Subgroup.mem_centralizer_iff.1 (hχN hx).2 _ huwY
      have h1 := hg uw uw (by rw [← hc, mul_inv_cancel_right])
      rw [huw, toAdd_ofAdd] at h1
      exact h1.symm
    have h1 : x * u⁻¹ * x⁻¹ ∈ Uq M T L := conj_mem (d.normU hxM) ⟨u⁻¹, inv_mem hu⟩
    have hwU : ⁅u, x⁆ ∈ Uq M T L := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact mul_mem hu (by simpa [mul_assoc] using h1)
    refine hlY (d.mem_pre.2 ⟨hwU, ?_⟩)
    have e1 : (⟨⁅u, x⁆, hwU⟩ : ↥(Uq M T L)) = ⟨u, hu⟩ * ⟨x * u⁻¹ * x⁻¹, h1⟩ :=
      Subtype.ext (by simp [commutatorElement_def, mul_assoc])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : ↥(Uq M T L)) = (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ := rfl
    rw [e1, map_mul, toAdd_mul, hg ⟨u⁻¹, inv_mem hu⟩ ⟨_, h1⟩ rfl, e2, map_inv, toAdd_inv,
      Matrix.mulVec_neg, ← sub_eq_add_neg, ← neg_sub]
    have := sub_mem_perp_of_mem_fixer hgl (Multiplicative.toAdd (d.vec ⟨u, hu⟩))
    rw [hl.perp_eq] at this
    exact Submodule.neg_mem _ this
  have hNT : N ≤ T := hNQ.trans h.pCore_le
  have hZN : ⁅tImage χ⁻¹ Z, N⁆ ≤ Y := by
    have hKT : ⁅tImage χ⁻¹ Z, N⁆ ≤ T := commutator_le_of_le (tImage_le _ _) hNT
    refine (tImage_le_iff χ hKT hYcT).1 ?_
    rw [tImage_commutator χ (tImage_le _ _) hNT, tImage_tImage_inv χ (Z0q_le_T h),
      S33.commutator_Z0q_eq h (tImage_le _ _)]
    exact hUN
  have hNL : ⁅N, L⁆ ≤ R :=
    comm_le_of_comm_le h (tImage_le _ _) hp.not_tImage_inv_le hNn hRn
      (by rw [Subgroup.commutator_comm]; exact hZN.trans hYR)
  have hRA : R ≤ A :=
    normalClosureIn_le_of hAM ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).2 hAn)
      (inf_le_left.trans le_sup_left)
  have hQZ : ⁅pCoreOf 2 M, tImage χ⁻¹ Z⁆ ≤ N := by
    refine le_trans ?_ (le_normalClosureIn (inf_le_right.trans (pCoreOf_le' M)))
    refine le_inf ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_right.1
        (h.pCore_le.trans (le_normalizer_tImage χ⁻¹ (h.le.trans (le_normalizer_Z0q M T))))
    · exact commutator_le_left_of_le_normalizer
        ((tImage_le _ _).trans (h.le.trans (le_normalizer_pCoreOf M)))
  have hQN : ⁅pCoreOf 2 M, L⁆ ≤ N :=
    comm_le_of_comm_le h (tImage_le _ _) hp.not_tImage_inv_le (le_normalizer_pCoreOf M) hNn hQZ
  have hV : Vq M L = ⁅Vq M L, L⁆ :=
    commutator_eq_commutator_commutator (pCoreOf_le' M) h.L_le (le_normalizer_pCoreOf M)
      h.le_normalizer h.perfect
  have hAZ : ⁅A, L⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    exact hAL
  have hVZ : Vq M L ≤ Z := by
    rw [hV, hV]
    exact (Subgroup.commutator_mono ((Subgroup.commutator_mono hQN le_rfl).trans
      (hNL.trans hRA)) le_rfl).trans hAZ
  apply hp.hV
  refine le_antisymm ?_ (Subgroup.commutator_mono h.Z0q_le_pCoreOf le_rfl)
  rw [hV]
  exact Subgroup.commutator_mono hVZ le_rfl

end PairHyp

end CFSG.Quasithin.MS93.S36SP
