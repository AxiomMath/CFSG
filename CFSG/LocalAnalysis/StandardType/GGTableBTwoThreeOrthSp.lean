module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSpTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeNode
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp

public section

namespace CFSG.StandardType

open Matrix Module CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

namespace TwoThreeOrth

variable {K : Type} [Field K]

section Transport

variable {R : Type} [Group R] {n : ℕ}

theorem endNode_of_model (Φ : R ≃* StatedSp n K) (h : StatedSp n K) {A : Subgroup R}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {t : R} (ht : t ∈ A)
    {S : Set (Fin n ⊕ Fin n)} {D : Subgroup (StatedSp n K)}
    (hg : h⁻¹ * Φ t * h ∈ suppGroup S) (hD : D ≤ suppGroup Sᶜ)
    (hlay : LargeEvenLayer (Subgroup.centralizer {h⁻¹ * Φ t * h}) = D ∧
      IsComponentOf D (Subgroup.centralizer {h⁻¹ * Φ t * h}))
    (hcent : ∀ x ∈ Subgroup.centralizer {h⁻¹ * Φ t * h}, (∀ j ∈ D, x * j = j * x) →
      x ∈ suppGroup S)
    (hfix : ∀ v, mat n K (h⁻¹ * Φ t * h) *ᵥ v = v → ∀ r ∈ S, v r = 0)
    (hnode : ∀ s ∈ A, (∀ w, mat n K (Φ t) *ᵥ w = w → mat n K (Φ s) *ᵥ w = w) →
      s ∈ Subgroup.zpowers t) :
    IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set R)))
        (Subgroup.centralizer ({t} : Set R)) ∧
      ∀ s ∈ A, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set R)), s * j = j * s) ↔
        s ∈ Subgroup.zpowers t) := by
  set Ψ : R ≃* StatedSp n K := Φ.trans (MulAut.conj h⁻¹) with hΨ
  have hΨapp : ∀ x, Ψ x = h⁻¹ * Φ x * h := fun x => by
    rw [hΨ, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  rw [← hΨapp] at hg hlay hcent hfix
  have hC : Subgroup.centralizer ({t} : Set R) =
      (Subgroup.centralizer {Ψ t}).map Ψ.symm.toMonoidHom := by
    rw [TableBSymp.map_centralizer_singleton, MulEquiv.symm_apply_apply]
  have hL : LargeEvenLayer (Subgroup.centralizer ({t} : Set R)) = D.map Ψ.symm.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective _ Ψ.symm.injective, hlay.1]
  refine ⟨?_, fun s hs => ⟨fun hsj => ?_, fun hst => ?_⟩⟩
  · rw [hL, hC]
    exact isComponentOf_map_of_injective _ Ψ.symm.injective hlay.2
  ·
    have hsD : ∀ j ∈ D, Ψ s * j = j * Ψ s := by
      intro j hj
      have h1 := hsj (Ψ.symm j) (by rw [hL]; exact ⟨j, hj, rfl⟩)
      have h2 := congrArg Ψ h1
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    have hsC : Ψ s ∈ Subgroup.centralizer {Ψ t} := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hAc s hs t ht]
    have hsS := hcent _ hsC hsD
    refine hnode s hs fun w hw => ?_
    have hw' : mat n K (Ψ t) *ᵥ (mat n K h⁻¹ *ᵥ w) = mat n K h⁻¹ *ᵥ w := by
      rw [hΨapp, map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec_inv, hw]
    have h1 := mulVec_eq_self_of_isSupp hsS (hfix _ hw')
    rw [hΨapp, map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec_inv] at h1
    have h2 := congrArg (fun x => mat n K h *ᵥ x) h1
    simp only [mulVec_mulVec_inv] at h2
    exact h2
  · intro j hj
    rw [hL] at hj
    obtain ⟨j', hj', rfl⟩ := hj
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hst
    have hc := commute_suppGroup_compl (Subgroup.zpow_mem _ hg k) (hD hj')
    apply Ψ.injective
    simp only [map_mul, map_zpow, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hc.eq

end Transport

section Node

variable [Finite K] [CharP K 2] {n : ℕ}

theorem exists_minimal_node_sp (hK : Nat.card K = 2) {A₁ : Subgroup (StatedSp n K)}
    (hA₁ : IsElemAbelian 3 A₁) (hne : A₁ ≠ ⊥) :
    ∃ g ∈ A₁, g ≠ 1 ∧
      (∀ x ∈ A₁, (∀ w, mat n K g *ᵥ w = w → mat n K x *ᵥ w = w) → x ∈ Subgroup.zpowers g) ∧
      Nat.card A₁ ^ 2 * 3 ^ finrank K (LinearMap.range (Matrix.toLin' (mat n K g) - 1)) ≤
        9 * 3 ^ (2 * n) ∧
      Even (finrank K (LinearMap.range (Matrix.toLin' (mat n K g) - 1))) := by
  set ι : StatedSp n K →* (Module.End K (Fin n ⊕ Fin n → K))ˣ :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (StatedSp n K).subtype with hι
  have hιinj : Function.Injective ι :=
    Matrix.GeneralLinearGroup.toLin.injective.comp (StatedSp n K).subtype_injective
  set X := A₁.map ι with hX
  have hcardX : Nat.card X = Nat.card A₁ :=
    (Nat.card_congr (A₁.equivMapOfInjective ι hιinj).toEquiv).symm
  have hXa := TableB.isElemAbelian_map hA₁ ι
  have hXne : X ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : ι x ∈ X := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (hιinj (by rw [this, map_one]))
  obtain ⟨_, ⟨g, hg, rfl⟩, hg1, hcent, hcard, heven, -⟩ := TwoThree.exists_minimal_node hK X
    (fun x hx y hy => TableB.IsElemAbelian.comm hXa hx hy) hXa.2 hXne
  have hrk : ((ι g : Module.End K (Fin n ⊕ Fin n → K)) - 1) = Matrix.toLin' (mat n K g) - 1 :=
    rfl
  refine ⟨g, hg, fun h => hg1 (by rw [h, map_one]), fun x hx hfix => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcent (ι x) ⟨x, hx, rfl⟩ fun w hw => hfix w hw)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hιinj (by rw [map_zpow]; exact hk)⟩
  · rw [hrk, hcardX] at hcard
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, ← two_mul]
      at hcard
  · rwa [hrk] at heven

end Node

section EndNode

variable [Finite K] [CharP K 2]

theorem ggEndNodeElt_of_mulEquiv (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) {R : Type}
    [Group R] (Φ : R ≃* StatedSp m K) : GGEndNodeElt 3 (m - 1) R := by
  intro A hA hr h27
  have hA₁ : IsElemAbelian 3 (A.map Φ.toMonoidHom) := TableB.isElemAbelian_map hA _
  have hcard₁ : Nat.card (A.map Φ.toMonoidHom) = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ Φ.injective).toEquiv).symm
  have hne : A.map Φ.toMonoidHom ≠ ⊥ := by
    intro h
    have h1 : Nat.card (A.map Φ.toMonoidHom) = 1 := by rw [h, Subgroup.card_bot]
    rw [hcard₁] at h1
    rw [h1] at h27
    norm_num at h27
  obtain ⟨g, hgA, hg1, hcent, hcard, heven⟩ := exists_minimal_node_sp hK hA₁ hne
  obtain ⟨t, ht, htg⟩ := hgA
  have htg' : Φ t = g := htg
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    fun a ha b hb => TableB.IsElemAbelian.comm hA ha hb
  have hg3 : g ^ 3 = 1 := by rw [← htg', ← map_pow, hA.2 t ht, map_one]
  have ht1 : t ≠ 1 := fun h => hg1 (by rw [← htg', h, map_one])
  have hnode : ∀ s ∈ A, (∀ w, mat m K (Φ t) *ᵥ w = w → mat m K (Φ s) *ᵥ w = w) →
      s ∈ Subgroup.zpowers t := by
    intro s hs hfix
    rw [htg'] at hfix
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcent (Φ s) ⟨s, hs, rfl⟩ hfix)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Φ.injective (by rw [map_zpow, htg']; exact hk)⟩
  obtain ⟨u, hu⟩ : ∃ u, u = finrank K (LinearMap.range (Matrix.toLin' (mat m K g) - 1)) :=
    ⟨_, rfl⟩
  rw [← hu, hcard₁] at hcard
  rw [← hu] at heven
  have h9 : 9 * 3 ^ (2 * m) = 3 ^ (2 * m + 2) := by rw [pow_add]; ring
  have hu4 : u ≤ 4 := by
    have h1 : 3 ^ (2 * (m - 1) + u) ≤ 3 ^ (2 * m + 2) :=
      calc 3 ^ (2 * (m - 1) + u) = (3 ^ (m - 1)) ^ 2 * 3 ^ u := by ring
        _ ≤ Nat.card A ^ 2 * 3 ^ u := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hr 2)
        _ ≤ 9 * 3 ^ (2 * m) := hcard
        _ = 3 ^ (2 * m + 2) := h9
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    omega
  have hu3 : m = 3 → u ≤ 2 := by
    rintro rfl
    have h1 : 3 ^ (6 + u) ≤ 3 ^ 8 :=
      calc 3 ^ (6 + u) = (3 ^ 3) ^ 2 * 3 ^ u := by rw [pow_add]; ring
        _ ≤ Nat.card A ^ 2 * 3 ^ u := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h27 2)
        _ ≤ 9 * 3 ^ (2 * 3) := hcard
        _ = 3 ^ 8 := by norm_num
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
    omega
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0] at hu
    have hbot := Submodule.finrank_eq_zero.mp hu.symm
    rw [LinearMap.range_eq_bot, sub_eq_zero] at hbot
    have hbot' : Matrix.toLin' (mat m K g) = Matrix.toLin' 1 := by
      rw [Matrix.toLin'_one]
      exact hbot
    apply hg1
    exact mat_injective (by rw [map_one]; exact Matrix.toLin'.injective hbot')
  obtain ⟨c, hc⟩ := heven
  rcases (show u = 2 ∨ u = 4 by omega) with h2 | h4
  ·
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hr2 : finrank K (LinearMap.range (Matrix.toLin' (mat (m' + 1) K g) - 1)) ≤ 2 := by
      rw [← hu]
      omega
    obtain ⟨h, hh⟩ := exists_conj_eq_nsElt_zero hK hg3 hg1 hr2
    have key := endNode_of_model Φ h hAc ht (S := coords 0)
      (D := ⁅complSp K (0 : Fin (m' + 1)), complSp K 0⁆)
      (by rw [htg', hh]; exact isSupp_longBlock (K := K) 0 zThreeSL)
      (Subgroup.commutator_le_self _)
      (by rw [htg', hh]; exact layer_centralizer_nsElt_zero hK (by omega))
      (by
        rw [htg', hh]
        exact fun x hx hxD => mem_suppGroup_of_commute_nsElt_zero hK (by omega) hx hxD)
      (by
        rw [htg', hh]
        intro v hv r hr
        obtain ⟨h1, h2⟩ := eq_zero_of_mulVec_eq_self 0 (mat_nsElt_mulVec_inl 0)
          (mat_nsElt_mulVec_inr 0) hv
        rcases mem_coords.1 hr with rfl | rfl
        · exact h1
        · exact h2)
      hnode
    exact ⟨t, ht, ht1, key.1, key.2⟩
  ·
    have hm4 : 4 ≤ m := by
      by_contra hlt
      have := hu3 (by omega)
      omega
    obtain ⟨m'', rfl⟩ : ∃ m'', m = m'' + 2 := ⟨m - 2, by omega⟩
    have hr4 : finrank K (LinearMap.range (Matrix.toLin' (mat (m'' + 2) K g) - 1)) ≤ 4 := by
      rw [← hu]
      omega
    have hr3 : 3 ≤ finrank K (LinearMap.range (Matrix.toLin' (mat (m'' + 2) K g) - 1)) := by
      rw [← hu]
      omega
    obtain ⟨h, hh⟩ := exists_conj_eq_nsElt_zero_mul_one hK hg3 hr3 hr4
    have key := endNode_of_model Φ h hAc ht (S := coords 0 ∪ coords 1)
      (D := ⁅complSp K (0 : Fin (m'' + 2)) ⊓ complSp K 1,
        complSp K (0 : Fin (m'' + 2)) ⊓ complSp K 1⁆)
      (by rw [htg', hh]; exact nsElt_zero_mul_one_mem_suppGroup)
      ((Subgroup.commutator_le_self _).trans inf_complSp_le_suppGroup)
      (by rw [htg', hh]; exact layer_centralizer_nsElt_zero_mul_one hK (by omega))
      (by
        rw [htg', hh]
        exact fun x hx hxD => mem_suppGroup_of_commute_nsElt_zero_mul_one hK (by omega) hx hxD)
      (by rw [htg', hh]; exact fun v hv => eq_zero_of_mulVec_nsElt_zero_mul_one hv)
      hnode
    exact ⟨t, ht, ht1, key.1, key.2⟩

theorem ggEndNodeElt_spTwo (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) :
    GGEndNodeElt 3 (m - 1) (LargeEvenProj (LargeEvenSpGroup K m)) := by
  have : NeZero m := ⟨by omega⟩
  exact ggEndNodeElt_of_mulEquiv hK hm (TableBSymp.spProjEquivSp.trans
    (MulEquiv.subgroupCongr (show LargeEvenSpGroup K m = StatedSp m K from rfl)))

theorem ggEndNode_spTwo (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) :
    GGEndNode 3 (m - 1) (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  exact ggEndNode_of_elt TableBSymp.sp_I_subset_inn TableBSymp.center_spProj_eq_bot
    (ggEndNodeElt_spTwo hK hm)

end EndNode

end TwoThreeOrth

open TwoThreeOrth

theorem recipeSymplectic_tableB_three_endNode {m N : ℕ} (hm : 3 ≤ m) (hN : N = 2)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic m N false Q) :
    LargeEvenRecipeSymplectic m N false fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift 3 r R ∧ GGEndNode 3 r R I := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨k, TwoThree.ggTorusLift_sp_two hK, ?_⟩
  have h := ggEndNode_spTwo (K := K) hK hm
  rwa [Nat.add_sub_cancel] at h

theorem largeEvenLabelAll_spTwoThree_endNode {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGSpTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  have hl : 3 ≤ l := by
    have h1 := hlab.2
    dsimp only at h1
    rcases ht with rfl | rfl <;> omega
  rcases ht with rfl | rfl
  · exact recipeSymplectic_tableB_three_endNode hl (by norm_num) hQ
  · exact recipeSymplectic_tableB_three_endNode hl (by norm_num) hQ

theorem ggStdSubPreInputOn_spTwoThree : GGStdSubPreInputOn GGSpTwoThreeLabel :=
  ggStdSubPreInputOn_of_labels fun _ _ _ hlab h => largeEvenLabelAll_spTwoThree_endNode hlab h

end CFSG.StandardType
