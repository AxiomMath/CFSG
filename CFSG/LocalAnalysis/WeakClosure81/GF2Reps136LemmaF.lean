module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136T
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136S
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_commSub_iSup {ι : Sort*} (U : ι → Subgroup W)
    (X : Subgroup (MulAut W)) :
    commSub (⨆ i, U i) X = ⨆ i, commSub (U i) X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    refine Subgroup.iSup_induction U hw (C := fun w => x w * w⁻¹ ∈ ⨆ i, commSub (U i) X)
      ?_ ?_ ?_
    · intro i w hw
      exact le_iSup (fun i => commSub (U i) X) i
        (Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩)
    · simp
    · intro a b ha hb
      have heq : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [heq]
      exact Subgroup.mul_mem _ ha hb
  · exact iSup_le fun i => commSub_mono (le_iSup U i) le_rfl

private theorem w1369_commSub_map_conj (U : Subgroup W) (X : Subgroup (MulAut W))
    (g : MulAut W) :
    commSub (U.map g.toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) =
      (commSub U X).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    refine ⟨x₀ w₀ * w₀⁻¹, ⟨x₀, hx₀, w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, w₀, hw₀, rfl⟩ := hs
    refine ⟨MulAut.conj g x₀, ⟨x₀, hx₀, rfl⟩, g w₀, ⟨w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]

private theorem w1369_map_conj_conj (X : Subgroup (MulAut W)) (g : MulAut W) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext x
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, hcomp, Subgroup.map_id]

private theorem w1369_stableUnder_sup {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊔ B) := by
  intro x hx u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA x hx a ha) (hB x hx b hb)

private theorem w1369_commSub_sup (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have h1 : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv_rev]
      ac_rfl
    rw [h1]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
      (Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

private theorem w1369_commSub_ne_bot {L : Subgroup (MulAut W)}
    {M : Subgroup W} (hCM : Cd L ≤ M) (hMW : M ≤ Wd L) (hCm : Cd L < M) :
    commSub M L ≠ ⊥ := by
  intro hbot
  have hMfix : M ≤ fixV L := commSub_eq_bot_iff.mp hbot
  have hEq : M = Cd L := le_antisymm (le_inf hMW hMfix) hCM
  rw [hEq] at hCm
  exact (lt_irrefl (Cd L)) hCm

private def w1369_Vgen (Y : Subgroup (MulAut W)) (M : Subgroup W) : Subgroup W :=
  ⨆ g : Y, M.map (g : MulAut W).toMonoidHom

private theorem w1369_Vgen_sup (Y : Subgroup (MulAut W)) (A B : Subgroup W) :
    w1369_Vgen Y (A ⊔ B) = w1369_Vgen Y A ⊔ w1369_Vgen Y B := by
  change (⨆ g : Y, (A ⊔ B).map (g : MulAut W).toMonoidHom) =
    (⨆ g : Y, A.map (g : MulAut W).toMonoidHom) ⊔
      ⨆ g : Y, B.map (g : MulAut W).toMonoidHom
  simp only [Subgroup.map_sup, iSup_sup_eq]

private theorem w1369_stableUnder_Vgen (Y : Subgroup (MulAut W)) (M : Subgroup W) :
    StableUnder Y (w1369_Vgen Y M) := by
  intro a ha s hs
  have hmap : (w1369_Vgen Y M).map a.toMonoidHom ≤ w1369_Vgen Y M := by
    change (⨆ g : Y, M.map (g : MulAut W).toMonoidHom).map a.toMonoidHom ≤
      ⨆ g : Y, M.map (g : MulAut W).toMonoidHom
    rw [Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_map]
    exact le_iSup (fun g : Y => M.map (g : MulAut W).toMonoidHom)
      ⟨a * g, Y.mul_mem ha g.2⟩
  exact hmap (Subgroup.mem_map_of_mem a.toMonoidHom hs)

private theorem w1369_commSub_Vgen_eq {Y : Subgroup (MulAut W)} {L : Subgroup (MulAut W)}
    {M : Subgroup W} (hT : Tcl Y L)
    (hMstab : StableUnder (Y ⊓ Subgroup.normalizer (L : Set (MulAut W))) M)
    (hMW : M ≤ Wd L) :
    commSub (w1369_Vgen Y M) L = commSub M L := by
  change commSub (⨆ g : Y, M.map (g : MulAut W).toMonoidHom) L = commSub M L
  rw [w1369_commSub_iSup]
  apply le_antisymm
  · refine iSup_le fun g => ?_
    by_cases hgN : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W))
    · have hXeq : M.map (g : MulAut W).toMonoidHom = M := by
        apply le_antisymm
        · rintro _ ⟨m, hm, rfl⟩
          exact hMstab (g : MulAut W) (Subgroup.mem_inf.mpr ⟨g.2, hgN⟩) m hm
        · intro m hm
          refine Subgroup.mem_map.mpr ⟨(g : MulAut W)⁻¹ m, ?_, by simp⟩
          exact hMstab (g : MulAut W)⁻¹
            (Subgroup.mem_inf.mpr ⟨Y.inv_mem g.2, Subgroup.inv_mem _ hgN⟩) m hm
      rw [hXeq]
    · have hTinv : commSub (Wd L)
          (L.map (MulAut.conj (g : MulAut W)⁻¹).toMonoidHom) = ⊥ :=
        hT (g : MulAut W)⁻¹ (Y.inv_mem g.2)
          (fun h => hgN (by simpa using Subgroup.inv_mem _ h))
      have hWd : commSub ((Wd L).map (g : MulAut W).toMonoidHom) L = ⊥ := by
        have h := w1369_commSub_map_conj (Wd L)
          (L.map (MulAut.conj (g : MulAut W)⁻¹).toMonoidHom) (g : MulAut W)
        have hLmap : (L.map (MulAut.conj (g : MulAut W)⁻¹).toMonoidHom).map
            (MulAut.conj (g : MulAut W)).toMonoidHom = L := by
          have := w1369_map_conj_conj L (g : MulAut W)⁻¹
          simpa using this
        rw [hTinv, Subgroup.map_bot, hLmap] at h
        exact h
      have hle : commSub (M.map (g : MulAut W).toMonoidHom) L ≤
          commSub ((Wd L).map (g : MulAut W).toMonoidHom) L :=
        commSub_mono (Subgroup.map_mono hMW) le_rfl
      rw [hWd] at hle
      exact hle.trans bot_le
  · refine le_iSup_of_le (⟨1, Y.one_mem⟩ : Y) ?_
    have h1 : M.map (1 : MulAut W).toMonoidHom = M := by ext x; simp
    rw [h1]

private theorem w1369_dichotomy {K : Subgroup (MulAut W)} (hKne : K ≠ ⊥)
    (hO2 : pCoreOf 2 K = ⊥) :
    (∃ X : Subgroup (MulAut W), IsComponentOf X K) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ pCoreOf p K ≠ ⊥ := by
  classical
  have hO2' : pCore 2 ↥K = ⊥ := by
    have h : (pCore 2 ↥K).map K.subtype = ⊥ := by simpa [CFSG.Open.pCoreOf] using hO2
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h
  have hFstar : genFittingFStar ↥K ≠ ⊥ := by
    intro hbot
    have hle := CFSG.Adapters.generalized_fitting_self_centralizing ↥K
    rw [hbot] at hle
    apply hKne
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    have hmem : (⟨k, hk⟩ : ↥K) ∈
        Subgroup.centralizer ((⊥ : Subgroup ↥K) : Set ↥K) := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      change y ∈ (⊥ : Subgroup ↥K) at hy
      rw [Subgroup.mem_bot] at hy
      subst hy
      simp
    have h1 := hle hmem
    rw [Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hdec : genFittingFitting ↥K ≠ ⊥ ∨ genFittingLayer ↥K ≠ ⊥ := by
    by_contra h
    rw [not_or] at h
    exact hFstar (by
      rw [CFSG.Open.genFittingFStar.eq_sup]
      exact sup_eq_bot_iff.mpr ⟨not_ne_iff.mp h.1, not_ne_iff.mp h.2⟩)
  rcases hdec with hfit | hlayer
  · right
    have hfit' : CFSG.fittingSubgroup ↥K ≠ ⊥ := by
      rwa [CFSG.Adapters.genFittingFitting_eq_foundations] at hfit
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore] at hfit'
    have hne : ∃ p : (Nat.card ↥K).primeFactors, pCore (p : ℕ) ↥K ≠ ⊥ := by
      by_contra h
      apply hfit'
      rw [iSup_eq_bot]
      intro p
      by_contra hp
      exact h ⟨p, hp⟩
    obtain ⟨p, hpne⟩ := hne
    have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hp2 : (p : ℕ) ≠ 2 := fun hp => hpne (by rw [hp, hO2'])
    refine ⟨(p : ℕ), hpp, hp2, ?_⟩
    show (pCore (p : ℕ) ↥K).map K.subtype ≠ ⊥
    intro hpbot
    exact hpne ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hpbot)
  · left
    have hne : ({A : Subgroup ↥K | IsComponentOf A ⊤}).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      apply hlayer
      rw [CFSG.Open.genFittingLayer.eq_sSup, hempty, sSup_empty]
    obtain ⟨A, hA⟩ := hne
    refine ⟨A.map K.subtype, ?_⟩
    exact (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf
      (Subgroup.map_subtype_le A)).mpr (by
        have hsub : (A.map K.subtype).subgroupOf K = A :=
          Subgroup.comap_map_eq_self_of_injective K.subtype_injective A
        rw [hsub]
        exact hA)

private theorem w1369_perfect_of_isQuasisimple {X : Subgroup (MulAut W)}
    (hX : CFSG.Open.IsQuasisimple X) : ⁅X, X⁆ = X := by
  rw [← Subgroup.map_subtype_commutator, hX.1, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

private theorem w1369_map_eq_self_of_stable {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hU : StableUnder X U) {x : MulAut W} (hx : x ∈ X) : U.map x.toMonoidHom = U := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact hU x hx u hu
  · intro u hu
    exact Subgroup.mem_map.mpr ⟨x⁻¹ u, hU x⁻¹ (X.inv_mem hx) u hu, by simp⟩

private theorem w1369_stableUnder_commSub {L : Subgroup (MulAut W)} {M : Subgroup W}
    (hM : StableUnder L M) : StableUnder L (commSub M L) := by
  intro l hl u hu
  have hMmap : M.map l.toMonoidHom = M := w1369_map_eq_self_of_stable hM hl
  have hLmap : L.map (MulAut.conj l).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hl)
  have h := w1369_commSub_map_conj M L l
  rw [hMmap, hLmap] at h
  have : l u ∈ (commSub M L).map l.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  rwa [← h] at this

private theorem w1369_stableUnder_inf {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊓ B) := by
  intro x hx u hu
  obtain ⟨huA, huB⟩ := Subgroup.mem_inf.mp hu
  exact Subgroup.mem_inf.mpr ⟨hA x hx u huA, hB x hx u huB⟩

private theorem w1369_map_conj_eq_self_of_comm {R L : Subgroup (MulAut W)}
    (hRL : ⁅R, L⁆ = ⊥) {g : MulAut W} (hg : g ∈ R) :
    L.map (MulAut.conj g).toMonoidHom = L := by
  have hcom : ∀ l ∈ L, g * l = l * g := by
    intro l hl
    have hmem : ⁅g, l⁆ ∈ ⁅R, L⁆ := Subgroup.commutator_mem_commutator hg hl
    rw [hRL, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    change g * l * g⁻¹ ∈ L
    rw [hcom l hl, mul_assoc, mul_inv_cancel, mul_one]
    exact hl
  · intro l hl
    refine Subgroup.mem_map.mpr ⟨l, hl, ?_⟩
    change g * l * g⁻¹ = l
    rw [hcom l hl, mul_assoc, mul_inv_cancel, mul_one]

private theorem w1369_map_conj_eq_self_of_normal {Y K : Subgroup (MulAut W)}
    (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal) {g : MulAut W} (hg : g ∈ Y) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  apply le_antisymm
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    exact (Subgroup.normal_subgroupOf_iff hKY).mp hKn k g hk hg
  · intro z hz
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * z * g, ?_, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff hKY).mp hKn z g⁻¹ hz (Y.inv_mem hg)
    · show g * (g⁻¹ * z * g) * g⁻¹ = z
      group

private theorem w1369_commSub_idem {L : Subgroup (MulAut W)} {M : Subgroup W}
    (hLp : ⁅L, L⁆ = L) (hM : StableUnder L M) :
    commSub (commSub M L) L = commSub M L := by
  apply le_antisymm
  · exact commSub_le_of_invariant (w1369_stableUnder_commSub hM)
  · exact s13_perfect_chain L hLp (commSub (commSub M L) L) (commSub M L) M le_rfl le_rfl

private theorem w1369_isComponentOf_map_conj {Y K X : Subgroup (MulAut W)}
    (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal) (hX : IsComponentOf X K) {g : MulAut W}
    (hg : g ∈ Y) : IsComponentOf (X.map (MulAut.conj g).toMonoidHom) K := by
  have hKmap := w1369_map_conj_eq_self_of_normal hKY hKn hg
  refine ⟨?_, ?_, ?_⟩
  · rw [← hKmap]
    exact Subgroup.map_mono hX.1
  · have := hX.2.1.map (MulAut.conj g).toMonoidHom
    rwa [hKmap] at this
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (X.equivMapOfInjective _ (MulAut.conj g).injective).symm hX.2.2

private theorem w1369_pCoreOf_subgroupOf_normal {H K : Subgroup (MulAut W)} (hKH : K ≤ H)
    (hHn : (K.subgroupOf H).Normal) (p : ℕ) :
    ((pCoreOf p K).subgroupOf H).Normal := by
  have hN : pCoreOf p K ≤ H := (Subgroup.map_subtype_le _).trans hKH
  have hHX : H ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hHn
  have hHN : H ≤ Subgroup.normalizer (pCoreOf p K : Set (MulAut W)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map ((MulAut.conj h).toMonoidHom) ((CFSG.pCore p ↥K).map K.subtype) =
      (CFSG.pCore p ↥K).map K.subtype
    let α : MulAut ↥K := K.normalizerMonoidHom ⟨h, hHX hh⟩
    have hcomp : K.subtype.comp α.toMonoidHom = (MulAut.conj h).toMonoidHom.comp K.subtype := by
      ext y
      simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map]
    rw [(Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore p ↥K).Characteristic)) α]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hHN

private theorem w1369_Vgen_top (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) :
    w1369_Vgen Y (Wd L) = ⊤ := by
  have h := lemmaS c.comp.1 (comm_top_of_component c.std hw2 c.comp)
  have hrange : conjSubs Y (Wd L) =
      Set.range (fun g : Y => (Wd L).map (g : MulAut W).toMonoidHom) := by
    ext X
    constructor
    · rintro ⟨g, hgY, rfl⟩
      exact ⟨⟨g, hgY⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
  rw [hrange, iSup_range] at h
  exact h

private theorem w1369_mem_fixV_Vgen {Y R : Subgroup (MulAut W)} {U : Subgroup W}
    (hRn : (R.subgroupOf Y).Normal) (hRY : R ≤ Y) (hfix : U ≤ fixV R) :
    w1369_Vgen Y U ≤ fixV R := by
  intro w hw
  rw [mem_fixV]
  intro r hr
  change w ∈ (⨆ g : Y, U.map (g : MulAut W).toMonoidHom) at hw
  refine Subgroup.iSup_induction (fun g : Y => U.map (g : MulAut W).toMonoidHom) hw
    (C := fun w => r w = w) ?_ ?_ ?_
  · intro g w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    have hconj : (g : MulAut W)⁻¹ * r * (g : MulAut W) ∈ R :=
      (Subgroup.normal_subgroupOf_iff hRY).mp hRn r (g : MulAut W)⁻¹ hr (Y.inv_mem g.2)
    have h1 : ((g : MulAut W)⁻¹ * r * (g : MulAut W)) u = u := mem_fixV.mp (hfix hu) _ hconj
    calc r ((g : MulAut W) u) = (g : MulAut W) (((g : MulAut W)⁻¹ * r * (g : MulAut W)) u) := by
          simp [mul_assoc]
      _ = (g : MulAut W) u := by rw [h1]
  · simp
  · intro a b ha hb
    rw [map_mul, ha, hb]

private theorem w1369_component_comm (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    (c : Ctx136 Y t L) (hPC : PerfCentTriv Y L)
    {K X : Subgroup (MulAut W)} {M : Subgroup W}
    (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hKcent : K ≤ centSub (w1369_Vgen Y M)) (hXK : IsComponentOf X K)
    (hMstabL : StableUnder L M) (hMW : M ≤ Wd L) (hCM : Cd L ≤ M) (hCm : Cd L < M) :
    commSub (Wd L) X = ⊥ := by
  have hLp : ⁅L, L⁆ = L := w1369_perfect_of_isQuasisimple c.comp.2.2
  have hMc : commSub M L ≠ ⊥ := w1369_commSub_ne_bot hCM hMW hCm
  have hMV : M ≤ w1369_Vgen Y M := by
    change M ≤ ⨆ g : Y, M.map (g : MulAut W).toMonoidHom
    have h1 : M.map (1 : MulAut W).toMonoidHom = M := by ext x; simp
    exact (le_of_eq h1.symm).trans
      (le_iSup (fun g : Y => M.map (g : MulAut W).toMonoidHom) ⟨1, Y.one_mem⟩)
  have hXleY : X ≤ Y := hXK.1.trans hKY
  have hXperf : ⁅X, X⁆ = X := w1369_perfect_of_isQuasisimple hXK.2.2
  have hXnot : ∀ g : MulAut W, g ∈ Y → X ≠ L.map (MulAut.conj g).toMonoidHom := by
    intro g hgY hEq
    exact hMc (by
      rw [commSub_eq_bot_iff]
      intro m hm
      rw [mem_fixV]
      intro l hl
      have hx' : MulAut.conj g l ∈ X := by
        rw [hEq]
        exact Subgroup.mem_map_of_mem _ hl
      have hgm : g m ∈ w1369_Vgen Y M := w1369_stableUnder_Vgen Y M g hgY m (hMV hm)
      have hfix := (mem_centSub.mp (hKcent (hXK.1 hx'))) (g m) hgm
      have h1 : g (l m) = g m := by simpa [MulAut.conj_apply, mul_assoc] using hfix
      exact g.injective h1)
  have hKYsn : IsSubnormal K Y := IsSubnormal.step hKY hKn (IsSubnormal.refl Y)
  have hXcompY : IsComponentOf X Y := ⟨hXleY, IsSubnormal.trans hXK.2.1 hKYsn, hXK.2.2⟩
  have hXneL : X ≠ L := by
    intro hXL
    refine hXnot 1 Y.one_mem ?_
    rw [hXL]
    ext z
    simp [MulAut.conj_apply]
  have hXLcomm : ⁅X, L⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hXcompY c.comp hXneL
  have hXfixM : commSub M X = ⊥ := by
    rw [commSub_eq_bot_iff]
    intro m hm
    rw [mem_fixV]
    intro x hx
    exact (mem_centSub.mp (hKcent (hXK.1 hx))) m (hMV hm)
  have hLXcomm : ⁅L, X⁆ = ⊥ := by rwa [Subgroup.commutator_comm] at hXLcomm
  refine lemmaT (fun w => by simpa [pow_two] using hw2 w) hLp hXperf hLXcomm ?_
  exact (hPC X hXleY hXperf hXLcomm M hCm hMW hMstabL (hXfixM.le.trans bot_le)).trans
    inf_le_right

private theorem w1369_odd_contra (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    (c : Ctx136 Y t L) (hT : Tcl Y L)
    {K : Subgroup (MulAut W)} {M : Subgroup W}
    (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hKcent : K ≤ centSub (w1369_Vgen Y M))
    (hMW : M ≤ Wd L) (hCM : Cd L ≤ M) (hCm : Cd L < M)
    {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) (hpK : pCoreOf p K ≠ ⊥) : False := by
  classical
  let R : Subgroup (MulAut W) := pCoreOf p K
  have hRK : R ≤ K := Subgroup.map_subtype_le _
  have hRY : R ≤ Y := hRK.trans hKY
  have hRn : (R.subgroupOf Y).Normal := w1369_pCoreOf_subgroupOf_normal hKY hKn p
  have hRp : IsPGroup p R := (CFSG.pCore_isPGroup (p := p) (G := ↥K)).map K.subtype
  have hRodd : Odd (Nat.card R) := by
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact Odd.pow (hpp.odd_of_ne_two hp2)
  have hRne : R ≠ ⊥ := hpK
  have hLp : ⁅L, L⁆ = L := w1369_perfect_of_isQuasisimple c.comp.2.2
  have hMc : commSub M L ≠ ⊥ := w1369_commSub_ne_bot hCM hMW hCm
  have hMV : M ≤ w1369_Vgen Y M := by
    change M ≤ ⨆ g : Y, M.map (g : MulAut W).toMonoidHom
    have h1 : M.map (1 : MulAut W).toMonoidHom = M := by ext x; simp
    exact (le_of_eq h1.symm).trans
      (le_iSup (fun g : Y => M.map (g : MulAut W).toMonoidHom) ⟨1, Y.one_mem⟩)
  have hLcomp : CFSG.IsComponent (L.subgroupOf Y) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      c.comp.1).mp ((CFSG.Assembly.isComponentOf_iff_open).mpr c.comp)
  have hRL' : ⁅L, R⁆ = ⊥ := by
    rcases CFSG.LocalCores.component_normal_subgroup hLcomp hRn with hle | hcomm
    · exfalso
      have hLR : L ≤ R := by
        have h : (L.subgroupOf Y).map Y.subtype ≤ (R.subgroupOf Y).map Y.subtype :=
          Subgroup.map_mono hle
        rwa [Subgroup.map_subgroupOf_eq_of_le c.comp.1,
          Subgroup.map_subgroupOf_eq_of_le hRY] at h
      exact hMc (by
        rw [commSub_eq_bot_iff]
        intro m hm
        rw [mem_fixV]
        intro l hl
        exact (mem_centSub.mp (hKcent (hRK (hLR hl)))) m (hMV hm))
    · have h := congrArg (Subgroup.map Y.subtype) hcomm
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le c.comp.1,
        Subgroup.map_subgroupOf_eq_of_le hRY, Subgroup.map_bot] at h
  have hRL : ⁅R, L⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hRL'
  have hWdstab : StableUnder L (Wd L) :=
    w1369_stableUnder_commSub (M := ⊤) (by intro x hx u hu; trivial)
  have hfixRstab : StableUnder L (fixV R) := by
    intro l hl v hv
    rw [mem_fixV]
    intro r hr
    have hcomm : r * l = l * r := by
      have hmem : ⁅r, l⁆ ∈ ⁅R, L⁆ := Subgroup.commutator_mem_commutator hr hl
      rw [hRL, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    calc r (l v) = (r * l) v := rfl
      _ = (l * r) v := by rw [hcomm]
      _ = l (r v) := rfl
      _ = l v := by rw [mem_fixV.mp hv r hr]
  have hWd_inv : StableUnder R (Wd L) := by
    intro g hgR w hw
    have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
      w1369_map_conj_eq_self_of_comm hRL hgR
    have hmap : (Wd L).map g.toMonoidHom = Wd L := by
      have h := w1369_commSub_map_conj (⊤ : Subgroup W) L g
      rw [Subgroup.map_top_of_surjective _ g.surjective, hLmap] at h
      exact h.symm
    rw [← hmap]
    exact Subgroup.mem_map_of_mem g.toMonoidHom hw
  have hWdL : commSub (Wd L) L = Wd L := by
    apply le_antisymm
    · exact commSub_le_of_invariant hWdstab
    · exact s13_perfect_chain L hLp (commSub (Wd L) L) (Wd L) ⊤ le_rfl le_rfl
  obtain ⟨hcop_sup, hcop_inf⟩ :=
    coprime_decomp hRodd (fun w => by simpa [pow_two] using hw2 w) hWd_inv
  let D0 : Subgroup W := commSub (Wd L) R
  let C0 : Subgroup W := Wd L ⊓ fixV R
  let W₁ : Subgroup W := commSub D0 L
  let W₀ : Subgroup W := commSub C0 L
  have h1 : D0 ⊔ C0 = Wd L := hcop_sup
  have hD0C0 : D0 ⊓ C0 = ⊥ := hcop_inf
  have hC0stab : StableUnder L C0 := w1369_stableUnder_inf hWdstab hfixRstab
  have hD0stab : StableUnder L D0 := by
    intro l hl u hu
    have hLmap : L.map (MulAut.conj l).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)
    have hWdmap : (Wd L).map l.toMonoidHom = Wd L := w1369_map_eq_self_of_stable hWdstab hl
    have hLRcomm : ⁅L, R⁆ = ⊥ := hRL'
    have hRmap : R.map (MulAut.conj l).toMonoidHom = R :=
      w1369_map_conj_eq_self_of_comm hLRcomm hl
    have hmap : D0.map l.toMonoidHom = D0 := by
      show (commSub (Wd L) R).map l.toMonoidHom = commSub (Wd L) R
      rw [← w1369_commSub_map_conj, hWdmap, hRmap]
    rw [← hmap]
    exact Subgroup.mem_map_of_mem l.toMonoidHom hu
  have hWd_split : Wd L = W₀ ⊔ W₁ := by
    have h2 : Wd L = W₁ ⊔ W₀ := by
      rw [← hWdL, ← h1, w1369_commSub_sup]
    rw [h2, sup_comm]
  have hW0Wd : W₀ ≤ Wd L :=
    (commSub_mono inf_le_left le_rfl).trans (le_of_eq hWdL)
  have hW1Wd : W₁ ≤ Wd L :=
    (commSub_mono (commSub_le_of_invariant hWd_inv) le_rfl).trans (le_of_eq hWdL)
  have hW0stab : StableUnder (Y ⊓ Subgroup.normalizer (L : Set (MulAut W))) W₀ := by
    intro g hg w hw
    have hgY : g ∈ Y := (Subgroup.mem_inf.mp hg).1
    have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hg).2
    have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    have hRmap : R.map (MulAut.conj g).toMonoidHom = R :=
      w1369_map_conj_eq_self_of_normal hRY hRn hgY
    have hWdmap : (Wd L).map g.toMonoidHom = Wd L := by
      have h := w1369_commSub_map_conj (⊤ : Subgroup W) L g
      rw [Subgroup.map_top_of_surjective _ g.surjective, hLmap] at h
      exact h.symm
    have hC0map : C0.map g.toMonoidHom = C0 := by
      show (Wd L ⊓ fixV R).map g.toMonoidHom = Wd L ⊓ fixV R
      rw [Subgroup.map_inf _ _ g.toMonoidHom g.injective, hWdmap, ← fixV_map_conj_eq R g, hRmap]
    have hW0map : W₀.map g.toMonoidHom = W₀ := by
      show (commSub C0 L).map g.toMonoidHom = commSub C0 L
      rw [← w1369_commSub_map_conj, hC0map, hLmap]
    rw [← hW0map]
    exact Subgroup.mem_map_of_mem g.toMonoidHom hw
  have hW1stab : StableUnder (Y ⊓ Subgroup.normalizer (L : Set (MulAut W))) W₁ := by
    intro g hg w hw
    have hgY : g ∈ Y := (Subgroup.mem_inf.mp hg).1
    have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hg).2
    have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    have hRmap : R.map (MulAut.conj g).toMonoidHom = R :=
      w1369_map_conj_eq_self_of_normal hRY hRn hgY
    have hWdmap : (Wd L).map g.toMonoidHom = Wd L := by
      have h := w1369_commSub_map_conj (⊤ : Subgroup W) L g
      rw [Subgroup.map_top_of_surjective _ g.surjective, hLmap] at h
      exact h.symm
    have hD0map : D0.map g.toMonoidHom = D0 := by
      show (commSub (Wd L) R).map g.toMonoidHom = commSub (Wd L) R
      rw [← w1369_commSub_map_conj, hWdmap, hRmap]
    have hW1map : W₁.map g.toMonoidHom = W₁ := by
      show (commSub D0 L).map g.toMonoidHom = commSub D0 L
      rw [← w1369_commSub_map_conj, hD0map, hLmap]
    rw [← hW1map]
    exact Subgroup.mem_map_of_mem g.toMonoidHom hw
  have hVdecomp : w1369_Vgen Y (Wd L) = w1369_Vgen Y W₀ ⊔ w1369_Vgen Y W₁ := by
    rw [hWd_split, w1369_Vgen_sup]
  have hVtop : w1369_Vgen Y (Wd L) = ⊤ := w1369_Vgen_top hw2 c
  have hsup : w1369_Vgen Y W₀ ⊔ w1369_Vgen Y W₁ = ⊤ := by
    rw [← hVdecomp, hVtop]
  rcases c.std.basic.1 _ _ (w1369_stableUnder_Vgen Y W₀) (w1369_stableUnder_Vgen Y W₁) hsup
    with hV0 | hV1
  · have hWd_eq : Wd L = W₀ := by
      rw [show Wd L = commSub ⊤ L from rfl, ← hV0,
        w1369_commSub_Vgen_eq hT hW0stab hW0Wd, w1369_commSub_idem hLp hC0stab]
    have hRfixWd : Wd L ≤ fixV R := by
      rw [hWd_eq]
      exact (commSub_le_of_invariant hC0stab).trans inf_le_right
    have hfixRtop : (⊤ : Subgroup W) ≤ fixV R := by
      rw [← hVtop]
      exact w1369_mem_fixV_Vgen hRn hRY hRfixWd
    have hRbot : R = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro r hr
      exact MulEquiv.ext fun v => by
        simpa using mem_fixV.mp (hfixRtop trivial) r hr
    exact hRne hRbot
  · have hWd_eq : Wd L = W₁ := by
      rw [show Wd L = commSub ⊤ L from rfl, ← hV1,
        w1369_commSub_Vgen_eq hT hW1stab hW1Wd, w1369_commSub_idem hLp hD0stab]
    have hM_D0 : M ≤ D0 := hMW.trans (hWd_eq.symm ▸ commSub_le_of_invariant hD0stab)
    have hMfixR : M ≤ fixV R := by
      intro m hm
      rw [mem_fixV]
      intro r hr
      exact (mem_centSub.mp (hKcent (hRK hr))) m (hMV hm)
    have hMle : M ≤ D0 ⊓ C0 := le_inf hM_D0 (le_inf hMW hMfixR)
    rw [hD0C0, le_bot_iff] at hMle
    exact absurd (hMle ▸ hCm) not_lt_bot

theorem lemmaF (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) (hT : Tcl Y L) (hPC : PerfCentTriv Y L) :
    ∀ M : Subgroup W, Cd L ≤ M → M ≤ Wd L →
      StableUnder (Y ⊓ Subgroup.normalizer (L : Set (MulAut W))) M → M = Cd L ∨ M = Wd L := by
  intro M hCM hMW hMstab
  by_cases hMC : M = Cd L
  · exact Or.inl hMC
  right
  have hMstabL : StableUnder L M := fun l hl =>
    hMstab l (Subgroup.mem_inf.mpr ⟨c.comp.1 hl, Subgroup.le_normalizer hl⟩)
  by_cases hfaith : ∀ y ∈ Y, (∀ v ∈ w1369_Vgen Y M, y v = v) → y = 1
  · have hVtop : w1369_Vgen Y M = ⊤ :=
      c.std.basic.2 _ (w1369_stableUnder_Vgen Y M) hfaith
    have hWd : Wd L = commSub M L := by
      rw [show Wd L = commSub ⊤ L from rfl, ← hVtop, w1369_commSub_Vgen_eq hT hMstab hMW]
    exact le_antisymm hMW (by rw [hWd]; exact commSub_le_of_invariant hMstabL)
  · obtain ⟨y0, hy0Y, hy0fix, hy0ne⟩ : ∃ y : MulAut W, y ∈ Y ∧
        (∀ v ∈ w1369_Vgen Y M, y v = v) ∧ y ≠ 1 := by
      by_contra h
      apply hfaith
      intro y hyY hyfix
      by_contra hyne
      exact h ⟨y, hyY, hyfix, hyne⟩
    let K : Subgroup (MulAut W) := Y ⊓ centSub (w1369_Vgen Y M)
    have hKY : K ≤ Y := inf_le_left
    have hKcent : K ≤ centSub (w1369_Vgen Y M) := inf_le_right
    have hKn : (K.subgroupOf Y).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hKY]
      intro a k ha hk
      obtain ⟨haY, hafix⟩ := Subgroup.mem_inf.mp ha
      refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem hk haY) (Y.inv_mem hk), ?_⟩
      rw [mem_centSub]
      intro v hv
      have hv' : k⁻¹ v ∈ w1369_Vgen Y M :=
        w1369_stableUnder_Vgen Y M k⁻¹ (Y.inv_mem hk) v hv
      have hk' := (mem_centSub.mp hafix) (k⁻¹ v) hv'
      calc (k * a * k⁻¹) v = k (a (k⁻¹ v)) := rfl
        _ = k (k⁻¹ v) := by rw [hk']
        _ = v := by simp
    have hKne : K ≠ ⊥ := by
      intro hbot
      have hyK : y0 ∈ K := Subgroup.mem_inf.mpr ⟨hy0Y, mem_centSub.mpr hy0fix⟩
      rw [hbot] at hyK
      exact hy0ne (Subgroup.mem_bot.mp hyK)
    have hO2K : pCoreOf 2 K = ⊥ :=
      c.std.o2 (pCoreOf 2 K) ((Subgroup.map_subtype_le _).trans hKY)
        (w1369_pCoreOf_subgroupOf_normal hKY hKn 2)
        ((CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype)
    have hlt : Cd L < M := lt_of_le_of_ne hCM (Ne.symm hMC)
    have hLp : ⁅L, L⁆ = L := w1369_perfect_of_isQuasisimple c.comp.2.2
    rcases w1369_dichotomy hKne hO2K with ⟨X, hXK⟩ | ⟨p, hpp, hp2, hpK⟩
    · exfalso
      have hkey : ∀ g : Y, commSub ((Wd L).map (g : MulAut W).toMonoidHom) X = ⊥ := by
        intro g
        let Xg : Subgroup (MulAut W) :=
          X.map (MulAut.conj ((g : MulAut W)⁻¹)).toMonoidHom
        have hXgK : IsComponentOf Xg K :=
          w1369_isComponentOf_map_conj hKY hKn hXK (Y.inv_mem g.2)
        have hWdXg : commSub (Wd L) Xg = ⊥ :=
          w1369_component_comm hw2 c hPC hKY hKn hKcent hXgK hMstabL hMW hCM hlt
        have h := w1369_commSub_map_conj (Wd L) Xg (g : MulAut W)
        have hXgmap : Xg.map (MulAut.conj (g : MulAut W)).toMonoidHom = X := by
          show (X.map (MulAut.conj ((g : MulAut W)⁻¹)).toMonoidHom).map
            (MulAut.conj (g : MulAut W)).toMonoidHom = X
          have := w1369_map_conj_conj X ((g : MulAut W)⁻¹)
          simpa using this
        rw [hWdXg, Subgroup.map_bot, hXgmap] at h
        exact h
      have hVtopWd : w1369_Vgen Y (Wd L) = ⊤ := w1369_Vgen_top hw2 c
      have hfixall : ∀ v : W, ∀ x ∈ X, x v = v := by
        intro v x hx
        have hv : v ∈ w1369_Vgen Y (Wd L) := by rw [hVtopWd]; trivial
        change v ∈ (⨆ g : Y, (Wd L).map (g : MulAut W).toMonoidHom) at hv
        refine Subgroup.iSup_induction
          (fun g : Y => (Wd L).map (g : MulAut W).toMonoidHom) hv (C := fun v => x v = v)
          ?_ ?_ ?_
        · intro g v hv
          have h0 := hkey g
          have hmem : x v * v⁻¹ ∈ commSub ((Wd L).map (g : MulAut W).toMonoidHom) X :=
            Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩
          rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at hmem
          exact hmem
        · simp
        · intro a b ha hb
          rw [map_mul, ha, hb]
      have hXbot : X = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        exact MulEquiv.ext fun v => hfixall v x hx
      have hXne : X ≠ ⊥ := by
        haveI : Nontrivial ↥X := CFSG.ComponentClassification.Quasisimple.nontrivial hXK.2.2
        exact (Subgroup.nontrivial_iff_ne_bot X).mp inferInstance
      exact hXne hXbot
    · exfalso
      exact w1369_odd_contra hw2 c hT hKY hKn hKcent hMW hCM hlt hpp hp2 hpK

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
