module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c_mQuot_zpowers_bot {H : Type*} [Group H] {a : H} (ha : a ^ 2 = 1) :
    E3.mQuot (Subgroup.zpowers a) ⊥ ≤ 1 := by
  unfold E3.mQuot
  rw [Subgroup.relIndex_bot_left, Nat.card_zpowers]
  have hd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h <;> simp [h]

theorem c8_mQuot_barSub_le_one (D : Data G) (h274 : R16_27_4 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_8 D V₀ V hV L)
    {B : Subgroup G} (hBM : B ≤ D.M) (hB : IsElemAbelian 2 B) :
    E3.mQuot (barSub V₀ V hV B) ⊥ ≤ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hmM, hm⟩ := UC6.exists_conj_le_of_isSylowOf D.sylowM hBM hB.isPGroup
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hms : m ∈ stabTil V₀ V := (le_stabTil hP.le_normalizer hP.le_normalizer₀) hmM
  have hB'T : conjSubgroup B m ≤ D.T := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have h := hm (m * y * m⁻¹) hy
    rwa [show m⁻¹ * (m * y * m⁻¹) * m = y by group] at h
  have hB'el : IsElemAbelian 2 (conjSubgroup B m) := E3.isElemAbelian_conjSubgroup hB m
  have hres : E3.mQuot (barSub V₀ V hV (conjSubgroup B m)) ⊥ ≤ 1 := by
    rcases h274 V₀ V L hV hS hc (conjSubgroup B m) hB'T hB'el with h0 | ⟨a, -, ha⟩
    · rw [h0, E3.mQuot_self]
      omega
    · have ha2 : (a : MulAut (Vtil V₀ V hV)) ^ 2 = 1 :=
        (isElemAbelian2_barSub hV hB'el).2 _ (ha ▸ Subgroup.mem_zpowers _)
      rw [ha]
      exact s16c_mQuot_zpowers_bot ha2
  have hcard : Nat.card (barSub V₀ V hV (conjSubgroup B m)) =
      Nat.card (barSub V₀ V hV B) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hms B]
    exact Subgroup.card_map_of_injective
      (f := (MulAut.conj (actTil V₀ V hV ⟨m, hms⟩)⁻¹).toMonoidHom)
      (MulAut.conj (actTil V₀ V hV ⟨m, hms⟩)⁻¹).injective
  have hmQbar : E3.mQuot (barSub V₀ V hV B) ⊥ =
      E3.mQuot (barSub V₀ V hV (conjSubgroup B m)) ⊥ := by
    unfold E3.mQuot
    simp only [Subgroup.relIndex_bot_left, hcard]
  rw [hmQbar]
  exact hres

theorem r16_30_of (D : Data G) (h22 : R1622 D) (h274 : R16_27_4 D) (h28 : R16_28 D) :
    R16_30 D := by
  intro V₀ V L hV hS hc
  rw [Set.eq_empty_iff_forall_notMem]
  intro X hX
  obtain ⟨g, -, hIn⟩ := hX
  have hVM : ¬ V ≤ conjSubgroup D.M g := hIn.2.1
  have hq : E3.mQuot (conjSubgroup V g) D.M ≤ 1 := hIn.2.2.1
  have hP := hS.setting.hyp16.hyp125.pairFacts
  set B : Subgroup G := conjSubgroup V g ⊓ D.M with hBdef
  have hBM : B ≤ D.M := by rw [hBdef]; exact inf_le_right
  have hBVg : B ≤ conjSubgroup V g := by rw [hBdef]; exact inf_le_left
  have hBel : IsElemAbelian 2 B :=
    B2F.isElemAbelian_mono hBVg (E3.isElemAbelian_conjSubgroup hV g)
  have hBst : B ≤ stabTil V₀ V :=
    hBM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hq' : E3.mQuot (conjSubgroup V g) B ≤ 1 := by
    rw [hBdef, mQuot_inf_left]
    exact hq
  set B₀ : Subgroup G := preBarSub B V₀ V hV ⊥ with hB₀def
  have hB₀B : B₀ ≤ B := by rw [hB₀def]; exact inf_le_left
  have hB₀M : B₀ ≤ D.M := hB₀B.trans hBM
  have hbarDk : barSub V₀ V hV B₀ = ⊥ := by
    rw [hB₀def, barSub_preBarSub]
    exact bot_inf_eq _
  have hBB₀le : E3.mQuot B B₀ ≤ 1 := by
    rw [← mQuot_barSub_preBarSub_gen hV hBst bot_le]
    exact c8_mQuot_barSub_le_one D h274 hS hc hBM hBel
  have hB₀Vg : B₀ ≤ conjSubgroup V g := hB₀B.trans hBVg
  set j : ℕ := E3.mQuot (conjSubgroup V g) B₀ with hjdef
  have hj2 : j ≤ 2 := by
    rw [hjdef, E3.mQuot_add hB₀B hBVg]
    omega
  have hA : B₀ ∈ E3.gammaSet V j D.M := ⟨hB₀M, g, hB₀Vg, hjdef.symm⟩
  have hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V := (h28 V₀ V L hV hS hc).1
  have hi : ((j + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : j + mSub V₀ < mSub V₀ + 4)) hr
  obtain ⟨-, hc2, hc3⟩ := sixteen_twentyThree_one D h22 hS.setting.hyp16 hA hB₀Vg hi
  have hB₀Ct : B₀ ≤ F11.CTilde D.M V₀ V :=
    (barSub_eq_bot_iff hV hP.le_normalizer hP.le_normalizer₀ hB₀M).1 hbarDk
  have hVc : V ≤ centralizer (B₀ : Set G) := fun v hv => hc2 v hv fun a ha => by
    have hcm := centralizesMod_of_mem_cTilde hV hP.le_normalizer hP.le_normalizer₀
      (hB₀Ct ha) v hv
    have e : ⁅v, a⁆ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact V₀.inv_mem hcm
  exact hVM (le_trans (le_inf le_rfl hVc) hc3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
