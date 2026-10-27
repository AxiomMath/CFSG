module

public import CFSG.LocalAnalysis.WeakClosure81.W172Invol
public import CFSG.LocalAnalysis.WeakClosure81.W18PackRank
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem w172_modd_eq_one_or_eq {K : Type*} [Group K] {e a : K} (he : e * e = 1)
    (ha : a ∈ Subgroup.zpowers e) : a = 1 ∨ a = e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have he2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact he
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, add_zero, zpow_mul, he2, one_zpow]
  · right
    rw [hk, h, zpow_add, zpow_mul, he2, one_zpow, one_mul, zpow_one]

private theorem w172_modd_eq_of_zpowers_eq {K : Type*} [Group K] {e f : K} (he : e * e = 1)
    (hf : f * f = 1) (he1 : e ≠ 1) (h : Subgroup.zpowers e = Subgroup.zpowers f) : e = f := by
  have hmem : e ∈ Subgroup.zpowers f := h ▸ Subgroup.mem_zpowers e
  rcases w172_modd_eq_one_or_eq hf hmem with h1 | h1
  · exact absurd h1 he1
  · exact h1

private theorem w172_modd_cj_zpowers {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (g e : LGL 2 W) : cj g (Subgroup.zpowers e) = Subgroup.zpowers (g * e * g⁻¹) := by
  unfold cj
  rw [MonoidHom.map_zpowers]
  rfl

theorem w172_mem_normalizer_zpowers_iff {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {e h : LGL 2 W} (he : e * e = 1) (he1 : e ≠ 1) :
    h ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup (LGL 2 W)) : Set (LGL 2 W)) ↔
      h * e = e * h := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change cj h (Subgroup.zpowers e) = Subgroup.zpowers e ↔ _
  rw [w172_modd_cj_zpowers]
  have hhe : (h * e * h⁻¹) * (h * e * h⁻¹) = 1 := by
    calc (h * e * h⁻¹) * (h * e * h⁻¹) = h * (e * e) * h⁻¹ := by group
      _ = 1 := by rw [he]; group
  constructor
  · intro hz
    have h1 : h * e * h⁻¹ = e := by
      have hmem : h * e * h⁻¹ ∈ Subgroup.zpowers e := hz ▸ Subgroup.mem_zpowers _
      rcases w172_modd_eq_one_or_eq he hmem with h1 | h1
      · exfalso
        apply he1
        have : e = h⁻¹ * (h * e * h⁻¹) * h := by group
        rw [this, h1]
        group
      · exact h1
    calc h * e = (h * e * h⁻¹) * h := by group
      _ = e * h := by rw [h1]
  · intro hc
    have h1 : h * e * h⁻¹ = e := by
      calc h * e * h⁻¹ = (e * h) * h⁻¹ := by rw [hc]
        _ = e := by group
    rw [h1]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

@[expose] def w172D (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    Set (LGL 2 M.W) :=
  {e | e ≠ 1 ∧ Subgroup.zpowers e ∈ x.packFamily M}

@[expose] noncomputable def w172Vd (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (e : LGL 2 M.W) : Submodule (ZMod 2) M.W :=
  x.packSpace M (Subgroup.zpowers e)

private theorem w172_fix_sp (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) {g : G}
    {r : LGL 2 M.W} (hr : r ∈ M.img (vInH V H g)) {w : M.W}
    (hw : w ∈ M.sp (conjSubgroup V₀ g)) : r w = w := by
  obtain ⟨y, hyA, rfl⟩ := M.mem_img.1 hr
  obtain ⟨z, hz, rfl⟩ := hw
  rw [M.ρ_ι y z hz.2]
  congr 1
  have hVg : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g
  have hz' : z ∈ conjSubgroup V g := E3.conjSubgroup_mono_left g x.hyp.setting.pair.le hz.1
  have hcomm : (y : G) * z = z * (y : G) := hVg.comm hyA.1 hz'
  rw [hcomm]
  group

theorem w172_invSys (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) :
    W172InvSys (M.img H) (x.w172D M) (x.w172Vd M) := by
  classical
  have hA := x.assumption131 M
  have hsq : ∀ e ∈ x.w172D M, e * e = 1 := fun e he => by
    have := (hA.isElemAb _ he.2).2 e (Subgroup.mem_zpowers e)
    rwa [pow_two] at this
  have hmemD : ∀ e ∈ x.w172D M, ∀ h ∈ M.img H,
      h * e * h⁻¹ ∈ x.w172D M := by
    intro e he h hh
    refine ⟨?_, ?_⟩
    · intro h1
      apply he.1
      have : e = h⁻¹ * (h * e * h⁻¹) * h := by group
      rw [this, h1]
      group
    · rw [← w172_modd_cj_zpowers]
      exact hA.invariant _ he.2 h hh
  refine
    { mem := ?_
      sq := hsq
      ne_one := fun e he => he.1
      conj_mem := hmemD
      comm_le := ?_
      fix := ?_
      ne_bot := ?_
      disjoint := ?_
      equivariant := ?_
      cent_iff_stab := ?_
      fix_le_cent := ?_ }
  · intro e he
    exact hA.le_G _ he.2 (Subgroup.mem_zpowers e)
  · intro e he w
    have hrank : mRank (Subgroup.zpowers e) ≤ x.iStar := x.mRank_le_iStar M he.2
    exact commSub_le_VA_of_mRank_le hA he.2 hrank (sub_mem_commSub _ (Subgroup.mem_zpowers e) w)
  · intro e he v hv
    obtain ⟨g, hg, hgA⟩ := he.2
    unfold w172Vd packSpace at hv
    have hle : (⨆ g' : {g' : G // Gam188 V H (eOmegaZ H D.T) i x.iStar g' ∧
        M.img (vInH V H g') = Subgroup.zpowers e}, M.sp (conjSubgroup V₀ g'.1)) ≤
        LinearMap.eqLocus (e : M.W →ₗ[ZMod 2] M.W) LinearMap.id := by
      refine iSup_le fun g' w hw => ?_
      have hr : e ∈ M.img (vInH V H g'.1) := by
        rw [g'.2.2]
        exact Subgroup.mem_zpowers e
      exact w172_fix_sp x M hr hw
    exact hle hv
  · intro e he hbot
    have hrank : mRank (Subgroup.zpowers e) ≤ x.iStar := x.mRank_le_iStar M he.2
    have h1 := commSub_le_VA_of_mRank_le hA he.2 hrank
    have h2 : x.packSpace M (Subgroup.zpowers e) = ⊥ := hbot
    rw [h2, le_bot_iff] at h1
    exact commSub_ne_bot_of_mem hA he.2 h1
  · intro e he f hf hne
    refine hA.disjoint _ he.2 _ hf.2 fun h => hne ?_
    exact w172_modd_eq_of_zpowers_eq (hsq e he) (hsq f hf) he.1 h
  · intro e he h hh
    unfold w172Vd
    rw [← w172_modd_cj_zpowers]
    exact hA.equivariant _ he.2 h hh
  · intro e he h hh
    rw [← w172_mem_normalizer_zpowers_iff (hsq e he) he.1]
    have h1 := hA.normalizer_eq _ he.2
    constructor
    · intro hn
      have hmem : h ∈ (M.img H) ⊓ Subgroup.normalizer
          ((Subgroup.zpowers e : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := ⟨hh, hn⟩
      rw [h1] at hmem
      exact hmem.2
    · intro hs
      have hmem : h ∈ stabilizerOf (M.img H) (x.packSpace M (Subgroup.zpowers e)) :=
        ⟨hh, hs⟩
      rw [← h1] at hmem
      exact hmem.2
  · intro e he w hw hw0 h hh hhw
    by_contra hnc
    have hne : cj h (Subgroup.zpowers e) ≠ Subgroup.zpowers e := by
      intro heq
      apply hnc
      rw [← w172_mem_normalizer_zpowers_iff (hsq e he) he.1,
        Subgroup.mem_normalizer_iff_map_conj_eq]
      exact heq
    have hΓ' : cj h (Subgroup.zpowers e) ∈ x.packFamily M := hA.invariant _ he.2 h hh
    have hdis := hA.disjoint _ he.2 _ hΓ' (Ne.symm hne)
    have heqv := hA.equivariant _ he.2 h hh
    have hw' : w ∈ x.packSpace M (cj h (Subgroup.zpowers e)) := by
      rw [heqv]
      exact ⟨w, hw, hhw⟩
    have hmem : w ∈ x.packSpace M (Subgroup.zpowers e) ⊓
        x.packSpace M (cj h (Subgroup.zpowers e)) := ⟨hw, hw'⟩
    rw [hdis, Submodule.mem_bot] at hmem
    exact hw0 hmem

theorem w172_exists_mem_D (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T)) {g : G}
    (hg : Gam188 V H (eOmegaZ H D.T) i x.iStar g)
    (hm : E3.mQuot (vInH V H g)
      (vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) ≤ 1) :
    ∃ e ∈ x.w172D M, M.img (vInH V H g) = Subgroup.zpowers e := by
  classical
  set A := vInH V H g with hAdef
  have hAH : A ≤ H := inf_le_right
  have hAab : IsElemAbelian 2 A :=
    (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g).mono inf_le_left
  have hp : IsPGroup 2 A := hAab.isPGroup
  have hAab' : IsElemAbelian 2 (M.img A) := M.isElemAbelian_img hAab
  have hcard : Nat.card (M.img A) =
      2 ^ E3.mQuot A (A ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) := by
    rw [M.card_img hAH, ← Subgroup.inf_relIndex_left (H := A), E3.relIndex_eq_two_pow hp]
  obtain ⟨a, haA, haC⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
    by_contra hcon
    exact hg.1.2 fun a ha => by
      by_contra h
      exact hcon ⟨a, ha, h⟩
  have haH : a ∈ H := hAH haA
  have hrA : M.ρ ⟨a, haH⟩ ∈ M.img A := M.mem_img.2 ⟨⟨a, haH⟩, haA, rfl⟩
  have hr1 : M.ρ ⟨a, haH⟩ ≠ 1 := fun h1 => haC ((M.ρ_eq_one_iff ⟨a, haH⟩).1 h1)
  have hr2 : M.ρ ⟨a, haH⟩ ^ 2 = 1 := hAab'.2 _ hrA
  have hord : orderOf (M.ρ ⟨a, haH⟩) = 2 := orderOf_eq_prime hr2 hr1
  have hzcard : Nat.card (Subgroup.zpowers (M.ρ ⟨a, haH⟩)) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers (M.ρ ⟨a, haH⟩) ≤ M.img A := Subgroup.zpowers_le.mpr hrA
  have hcard2 : Nat.card (M.img A) ≤ 2 := by
    rw [hcard]
    calc 2 ^ E3.mQuot A _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm
      _ = 2 := by norm_num
  have hEq : Subgroup.zpowers (M.ρ ⟨a, haH⟩) = M.img A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hzcard]; exact hcard2)
  exact ⟨M.ρ ⟨a, haH⟩, ⟨hr1, g, hg, hEq⟩, hEq.symm⟩

theorem w172_comm_of_mem_img (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {T : Subgroup G} (hT : IsPGroup 2 T) {e f : LGL 2 M.W} (he : e ∈ x.w172D M)
    (hf : f ∈ x.w172D M) (heT : e ∈ M.img T) (hfT : f ∈ M.img T) : e * f = f * e := by
  have hI := x.w172_invSys M
  rcases w172_comm_or_odd hI he hf with h | hodd
  · exact h
  · have hmem : e * f ∈ M.img T := (M.img T).mul_mem heT hfT
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (M.isPGroup_img hT) ⟨e * f, hmem⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k = 0 := by
      by_contra hk0
      have heven : Even (2 ^ k) := (Nat.even_pow.mpr ⟨even_two, hk0⟩)
      rw [← hk] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    have hfe : f = e⁻¹ := eq_inv_of_mul_eq_one_right hk
    have hee : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hI.sq e he)
    rw [hfe, hee]

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
