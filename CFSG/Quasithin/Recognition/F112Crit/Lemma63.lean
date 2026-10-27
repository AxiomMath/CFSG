module

public import CFSG.Quasithin.Recognition.F112Crit.Setting

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G} [Finite G]

namespace CritAmalgam

theorem stab_γ₀_eq (hc : CritAmalgam G₀ G₁ G₂ T Z) : stab (γ₀ G₀ G₁ G₂) = G₁ :=
  CosetGeom.stab_γ₀ hc.amalgam.le₁

theorem stab_γ₁_eq (hc : CritAmalgam G₀ G₁ G₂ T Z) : stab (γ₁ G₀ G₁ G₂) = G₂ :=
  CosetGeom.stab_γ₁ hc.amalgam.le₂

theorem pCoreOf_right_le_centralizer (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    pCoreOf 2 G₂ ≤ Subgroup.centralizer (Z : Set G) :=
  ((F7.isSylowTwoOf_pCoreOf_le hc.amalgam.sylow₂).trans
    (hc.amalgam.T_le.trans inf_le_left)).trans hc.centralizes

theorem le_centralizer_pCoreOf_right (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    Z ≤ Subgroup.centralizer (pCoreOf 2 G₂ : Set G) :=
  Subgroup.le_centralizer_iff.mp hc.pCoreOf_right_le_centralizer

theorem le_pCoreOf_right (hc : CritAmalgam G₀ G₁ G₂ T Z) : Z ≤ pCoreOf 2 G₂ :=
  (le_inf hc.le_right hc.le_centralizer_pCoreOf_right).trans hc.charTwo₂

theorem right_le_normalizer_center (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    G₂ ≤ Subgroup.normalizer
      ((pCoreOf 2 G₂ ⊓ Subgroup.centralizer (pCoreOf 2 G₂ : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf (le_normalizer_pCoreOf 2 G₂)
    ((le_normalizer_pCoreOf 2 G₂).trans (F7.normalizer_le_normalizer_centralizer _))

theorem conjClosure_le_center (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    conjClosure Z G₂ ≤ pCoreOf 2 G₂ ⊓ Subgroup.centralizer (pCoreOf 2 G₂ : Set G) := by
  refine conjClosure_le fun h hh z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hc.right_le_normalizer_center hh) z).mp
    ⟨hc.le_pCoreOf_right hz, hc.le_centralizer_pCoreOf_right hz⟩

theorem isElemAbelian_conjClosure (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    IsElemAbelian 2 (conjClosure Z G₂) := by
  unfold conjClosure
  refine F7.isElemAbelian_closure _ ?_ ?_
  · rintro x ⟨h, hh, z, hz, rfl⟩ y ⟨h', hh', z', hz', rfl⟩
    have h1 := hc.conjClosure_le_center (mem_conjClosure hh hz)
    have h2 := hc.conjClosure_le_center (mem_conjClosure hh' hz')
    exact (Subgroup.mem_centralizer_iff.mp h2.2) _ h1.1
  · rintro x ⟨h, hh, z, hz, rfl⟩
    have : z ^ 2 = 1 := F7.isElemAbelian_pow_eq_one hc.isElemAbelian hz
    rw [conj_pow, this]
    group

theorem not_right_le_centralizer (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    ¬ G₂ ≤ Subgroup.centralizer (Z : Set G) := by
  intro h
  have hN : G₀ ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hc.amalgam.gen]
    exact sup_le hc.normalizes (h.trans (Subgroup.centralizer_le_normalizer (Z : Set G)))
  have hZ0 : Z ≤ pCoreOf 2 G₀ :=
    le_pCoreOf_of_le_normalizer 2 (hc.le_left.trans hc.amalgam.le₁) hN hc.isPGroup
  rw [hc.amalgam.o2_trivial] at hZ0
  exact hc.ne_bot (le_bot_iff.mp hZ0)

theorem right_inf_centralizer (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    G₂ ⊓ Subgroup.centralizer (Z : Set G) = G₁ ⊓ G₂ := by
  have hle : G₁ ⊓ G₂ ≤ G₂ ⊓ Subgroup.centralizer (Z : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hc.centralizes)
  have hle2 : G₂ ⊓ Subgroup.centralizer (Z : Set G) ≤ G₂ := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (G₁ ⊓ G₂) (G₂ ⊓ Subgroup.centralizer (Z : Set G))
    G₂ hle hle2
  rw [Subgroup.inf_relIndex_right] at hmul
  rcases hc.prime.eq_one_or_self_of_dvd _ (Dvd.intro _ hmul) with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hle
  · exfalso
    rw [h] at hmul
    have h1 : (G₂ ⊓ Subgroup.centralizer (Z : Set G)).relIndex G₂ = 1 :=
      Nat.eq_of_mul_eq_mul_left hc.prime.pos (by rw [hmul, mul_one])
    exact hc.not_right_le_centralizer (inf_le_right.trans' (Subgroup.relIndex_eq_one.mp h1))

end CritAmalgam

theorem lemma63_1 (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) :
    Vv Z γ ≤ pCoreOf 2 (stab γ) ∧ pCoreOf 2 (stab γ) ≤ ballStab 1 γ := by
  refine ⟨?_, CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam γ⟩
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hγ
  rw [Zv_smul_γ₀ hc, CosetGeom.stab_smul, pCoreOf_conjSub, hc.stab_γ₀_eq]
  exact conjSub_mono _ hc.le_pCoreOf

theorem lemma63_2 (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ δ : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) (hδ : δ ∈ nbrs γ) :
    Vv Z γ ≤ pCoreOf 2 (stab δ) ∧ Vv Z γ ≤ Subgroup.centralizer (pCoreOf 2 (stab δ) : Set G) := by
  obtain ⟨g, rfl, rfl⟩ := exists_edge_conj hγ hδ
  rw [Zv_smul_γ₀ hc, CosetGeom.stab_smul, hc.stab_γ₁_eq, pCoreOf_conjSub, conjSub_centralizer]
  exact ⟨conjSub_mono _ hc.le_pCoreOf_right, conjSub_mono _ hc.le_centralizer_pCoreOf_right⟩

theorem lemma63_2' (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂}
    (hδ : vtype δ = true) :
    IsElemAbelian 2 (Vv Z δ) ∧ Vv Z δ ≤ pCoreOf 2 (stab δ) ∧
      Vv Z δ ≤ Subgroup.centralizer (pCoreOf 2 (stab δ) : Set G) ∧
      Vv Z δ ≤ quasithinOmegaOneCenter (pCoreOf 2 (stab δ)) ∧
      stab δ ≤ Subgroup.normalizer (Vv Z δ : Set G) := by
  have hel : IsElemAbelian 2 (Vv Z δ) ∧ Vv Z δ ≤ pCoreOf 2 (stab δ) ∧
      Vv Z δ ≤ Subgroup.centralizer (pCoreOf 2 (stab δ) : Set G) := by
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hδ
    rw [CosetGeom.Vv_smul hc.normalizes, CosetGeom.Vv_γ₁ hc.amalgam.le₂ hc.normalizes,
      CosetGeom.stab_smul, hc.stab_γ₁_eq, pCoreOf_conjSub, conjSub_centralizer]
    refine ⟨isElemAbelian_conjSub hc.isElemAbelian_conjClosure,
      conjSub_mono _ (hc.conjClosure_le_center.trans inf_le_left),
      conjSub_mono _ (hc.conjClosure_le_center.trans inf_le_right)⟩
  refine ⟨hel.1, hel.2.1, hel.2.2, ?_, CosetGeom.stab_le_normalizer_Vv hc.normalizes δ⟩
  intro x hx
  exact Subgroup.subset_closure ⟨⟨hel.2.1 hx, hel.2.2 hx⟩,
    F7.isElemAbelian_pow_eq_one hel.1 hx⟩

theorem lemma63_3 (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ δ : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) (hδ : δ ∈ nbrs γ) :
    stab δ ⊓ Subgroup.centralizer (Vv Z γ : Set G) = stab γ ⊓ stab δ := by
  obtain ⟨g, rfl, rfl⟩ := exists_edge_conj hγ hδ
  rw [Zv_smul_γ₀ hc, CosetGeom.stab_smul, CosetGeom.stab_smul, hc.stab_γ₀_eq, hc.stab_γ₁_eq,
    conjSub_centralizer, ← conjSub_inf, ← conjSub_inf, hc.right_inf_centralizer]

theorem two_le_critB (hc : CritAmalgam G₀ G₁ G₂ T Z) : 2 ≤ critB G₀ G₁ G₂ Z := by
  rw [le_critB_iff hc]
  intro μ hμ
  rcases (CosetGeom.dist_le_one_iff hc.amalgam.gen).mp (Nat.lt_succ_iff.mp hμ) with rfl | hadj
  · have h := (lemma63_1 hc (CosetGeom.vtype_γ₀ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂))).1
    rw [CosetGeom.Vv_γ₀ hc.normalizes] at h
    exact h.trans (CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam _)
  · have h := (lemma63_2 hc (CosetGeom.vtype_γ₀ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂))
      (show μ ∈ nbrs (γ₀ G₀ G₁ G₂) from hadj)).1
    rw [CosetGeom.Vv_γ₀ hc.normalizes] at h
    exact h.trans (CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam _)

end CFSG.Quasithin.F112Crit
