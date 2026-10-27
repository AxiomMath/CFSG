module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4IMod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Cen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4USyl2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P P₁ P₂ : Subgroup (MulAut V)}

theorem card_stabilizer_singular (h : E9Z4Str X Tb P) (hp : PlanePair Tb P P₁ P₂) {k : V}
    (hk₁ : k ∉ commV P₁) (hk₂ : k ∉ commV P₂) : Nat.card ↥(MulAction.stabilizer ↥X k) = 4 := by
  have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥X k)
  rw [Nat.card_prod, h.card_X] at h1
  have hk1 : k ≠ 1 := fun e => hk₁ (e ▸ (commV P₁).one_mem)
  have horb : Nat.card ↥(MulAction.orbit ↥X k) = 9 := by
    have e : (MulAction.orbit ↥X k : Set V) = {v : V | v ∉ commV P₁ ∧ v ∉ commV P₂} := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        have hx : (x : MulAut V) k ≠ 1 := fun e => hk1 (x.1.injective (by rw [map_one]; exact e))
        constructor
        · intro hv
          have hns : (x : MulAut V) k ∈ Nonsingular P := by
            rw [h.nonsingular_eq hp]
            exact ⟨hx, Or.inl hv⟩
          have := h.nonsingular_stable (X.inv_mem x.2) hns
          rw [show (x : MulAut V)⁻¹ ((x : MulAut V) k) = k by simp, h.nonsingular_eq hp] at this
          exact hk₁ (this.2.resolve_right hk₂)
        · intro hv
          have hns : (x : MulAut V) k ∈ Nonsingular P := by
            rw [h.nonsingular_eq hp]
            exact ⟨hx, Or.inr hv⟩
          have := h.nonsingular_stable (X.inv_mem x.2) hns
          rw [show (x : MulAut V)⁻¹ ((x : MulAut V) k) = k by simp, h.nonsingular_eq hp] at this
          exact hk₂ (this.2.resolve_left hk₁)
      · rintro ⟨hv₁, hv₂⟩
        obtain ⟨a, ha, hav⟩ := h.singular_transitive hp hk₁ hk₂ hv₁ hv₂
        exact ⟨⟨a, h.P_le_X ha⟩, hav⟩
    rw [e]
    exact h.card_singular hp
  rw [horb] at h1
  omega

end E9Z4Str

section Group

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem card_centralizerMod_le_two_mul (S : Setting146 G T M) (hH : IsHTM T M H) (w : G) :
    Nat.card ↥(centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers w)) ≤
      2 * Nat.card ↥(H ⊓ Subgroup.centralizer ({w} : Set G)) := by
  classical
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hKA := (centralizer_le_centralizerMod S hH w).1
  set A := centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers w) with hA
  set K' := H ⊓ Subgroup.centralizer ({w} : Set G) with hK'
  have hcz : ∀ g ∈ A, g * w * g⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T := fun g hg =>
    hg.2.2 w (Subgroup.mem_zpowers w)
  have hc1 : ∀ g ∈ A, g * w * g⁻¹ * w⁻¹ = 1 → g ∈ K' := by
    intro g hg h1
    refine ⟨hg.1, ?_⟩
    show g ∈ Subgroup.centralizer ({w} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h2 : ⁅g, w⁆ = 1 := by
      rw [commutatorElement_def]
      exact h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hmul : ∀ g ∈ H, ∀ h ∈ H, h * w * h⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T →
      (g * h) * w * (g * h)⁻¹ * w⁻¹ = (h * w * h⁻¹ * w⁻¹) * (g * w * g⁻¹ * w⁻¹) := by
    intro g hg h hh hz
    have e : (g * h) * w * (g * h)⁻¹ * w⁻¹ =
        (g * (h * w * h⁻¹ * w⁻¹) * g⁻¹) * (g * w * g⁻¹ * w⁻¹) := by group
    rw [e, S146T.conj_Z (hHG hg) hz]
  have hdvd : K'.relIndex A ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hall : ∀ b ∈ A, b ∈ K'
    · exact ⟨1, A.one_mem, fun b hb => Or.inr (hall b hb)⟩
    · push Not at hall
      obtain ⟨x, hx, hxK⟩ := hall
      refine ⟨x⁻¹, A.inv_mem hx, fun b hb => ?_⟩
      by_cases hbK : b ∈ K'
      · exact Or.inr hbK
      refine Or.inl (hc1 _ (A.mul_mem hb (A.inv_mem hx)) ?_)
      have hx1 : x * w * x⁻¹ * w⁻¹ ≠ 1 := fun e => hxK (hc1 x hx e)
      have hb1 : b * w * b⁻¹ * w⁻¹ ≠ 1 := fun e => hbK (hc1 b hb e)
      have hbx : b * w * b⁻¹ * w⁻¹ = x * w * x⁻¹ * w⁻¹ :=
        eq_of_card_two_subgroup S.card_Z (hcz b hb) (hcz x hx) hb1 hx1
      have h1 := hmul x hx.1 x⁻¹ (H.inv_mem hx.1) (hcz x⁻¹ (A.inv_mem hx))
      rw [mul_inv_cancel, show (1 : G) * w * 1⁻¹ * w⁻¹ = 1 by group] at h1
      have h2 : x⁻¹ * w * x⁻¹⁻¹ * w⁻¹ = (x * w * x⁻¹ * w⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      rw [hmul b hb.1 x⁻¹ (H.inv_mem hx.1) (hcz x⁻¹ (A.inv_mem hx)), h2, hbx]
      exact inv_mul_cancel _
  have hcard := Subgroup.relIndex_mul_card K' A
  rw [inf_eq_left.mpr hKA] at hcard
  have hle : K'.relIndex A ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  rw [← hcard]
  exact Nat.mul_le_mul_right _ hle

theorem e9_exists_twoGroup_of_singular (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P Q₁ Q₂ : Subgroup (MulAut ↥(kOf (rhoH h)))}
    (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P) (hp : PlanePair Tb P Q₁ Q₂)
    (hT4 : (pCoreOf 2 H).relIndex T = 4) {w : G} (hwK : w ∈ uK T M H)
    (hw₁ : w ∉ uHi T M H (HLb (resBeta (rhoH h)) Q₁))
    (hw₂ : w ∉ uHi T M H (HLb (resBeta (rhoH h)) Q₂)) :
    ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
      Nat.card T ≤ 2 * Nat.card S' := by
  classical
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hHZ : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hHG.trans S.normalizer_Z.ge
  have hUK : uK T M H ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _)
  have hwU : w ∈ conjClosure (VZ T M) H := hUK hwK
  have hwH : w ∈ H := pCoreOf_le 2 H (h.conjClosure_Vp_le_pCoreOf hwU)
  have hw' : w ∈ uHi T M H (HLb (resBeta (rhoH h)) (resBeta (rhoH h)).range) := by
    rw [HLb_range_eq]
    exact Subgroup.mem_sup_left hwK
  obtain ⟨k, -, hkc⟩ := exists_mem_commV_of_mem_uHi h hsplit (le_refl _) hwU hw'
  have hsing : ∀ {Q : Subgroup (MulAut ↥(kOf (rhoH h)))}, Q ≤ (resBeta (rhoH h)).range →
      w ∉ uHi T M H (HLb (resBeta (rhoH h)) Q) → k ∉ commV Q := by
    intro Q hQ hwQ hk
    obtain ⟨u₁, hu₁U, hu₁, hc₁⟩ := exists_mem_uHi_of_mem_commV h hsplit hQ hk
    have hz : u₁⁻¹ * w ∈ quasithinOmegaOneCenter T :=
      (clsU_eq_iff h hu₁U hwU).mp (hc₁.trans hkc)
    have e : w = u₁ * (u₁⁻¹ * w) := by group
    exact hwQ (by rw [e]; exact Subgroup.mul_mem _ hu₁ (Z_le_uHi _ _ _ _ hz))
  have hk₁ := hsing (hp.1.trans hstr.P_le_X) hw₁
  have hk₂ := hsing (hp.2.1.trans hstr.P_le_X) hw₂
  have hstab4 := hstr.card_stabilizer_singular hp hk₁ hk₂
  let Stab : Subgroup (MulAut ↥(kOf (rhoH h))) :=
    (MulAction.stabilizer ↥(resBeta (rhoH h)).range k).map (resBeta (rhoH h)).range.subtype
  have hStabr : Stab ≤ (resBeta (rhoH h)).range := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hcardStab : Nat.card Stab = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hstab4
  have hAeq : centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers w) =
      HLb (resBeta (rhoH h)) Stab := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxH, -, hx⟩
      have h1 := (rhoH_clsU_eq_iff h ⟨x, hxH⟩ hwU).mpr (hx w (Subgroup.mem_zpowers w))
      have hfix : resBeta (rhoH h) ⟨x, hxH⟩ k = k := by
        refine Subtype.ext ((resBeta_apply _ _ _).trans ?_)
        rw [hkc]
        exact h1
      exact (mem_HLb_iff hxH).mpr (Subgroup.mem_map.mpr
        ⟨⟨resBeta (rhoH h) ⟨x, hxH⟩, ⟨⟨x, hxH⟩, rfl⟩⟩, (MulAction.mem_stabilizer_iff).mpr hfix,
          rfl⟩)
    · intro x hx
      have hxH : x ∈ H := HLb_le _ hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp ((mem_HLb_iff hxH).mp hx)
      have hfix : resBeta (rhoH h) ⟨x, hxH⟩ k = k := by
        rw [← hzx]
        exact (MulAction.mem_stabilizer_iff).mp hz
      have hρ : rhoH h ⟨x, hxH⟩ (clsU h hwU) = clsU h hwU := by
        rw [← hkc]
        exact (resBeta_apply _ _ k).symm.trans (congrArg Subtype.val hfix)
      exact mem_centralizerMod_zpowers_of_comm hxH (hHZ hxH)
        (fun z hz => S146T.comm_Z (hHG hwH) hz) ((rhoH_clsU_eq_iff h ⟨x, hxH⟩ hwU).mp hρ)
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQA : pCoreOf 2 H ≤ HLb (resBeta (rhoH h)) Stab := pCoreOf_le_HLb h hsplit Stab
  have hAcard : Nat.card (HLb (resBeta (rhoH h)) Stab) = 4 * Nat.card (pCoreOf 2 H) := by
    have := Subgroup.relIndex_mul_card (pCoreOf 2 H) (HLb (resBeta (rhoH h)) Stab)
    rw [inf_eq_left.mpr hQA, relIndex_pCoreOf_HLb h hsplit hStabr, hcardStab] at this
    exact this.symm
  have hTcard : Nat.card T = 4 * Nat.card (pCoreOf 2 H) := by
    have := Subgroup.relIndex_mul_card (pCoreOf 2 H) T
    rw [inf_eq_left.mpr hTsyl.pCoreOf_le, hT4] at this
    exact this.symm
  obtain ⟨n, hn⟩ := S.hyp.sylow.1.exists_card_eq
  have hA2 : IsPGroup 2 ↥(HLb (resBeta (rhoH h)) Stab) :=
    IsPGroup.of_card (hAcard.trans (hTcard.symm.trans hn))
  refine ⟨H ⊓ Subgroup.centralizer ({w} : Set G), le_rfl, ?_, ?_⟩
  · refine hA2.to_le ?_
    rw [← hAeq]
    exact (centralizer_le_centralizerMod S hH w).1
  · have := card_centralizerMod_le_two_mul S hH w
    rw [hAeq, hAcard, ← hTcard] at this
    exact this

end Group

end CFSG.Quasithin
