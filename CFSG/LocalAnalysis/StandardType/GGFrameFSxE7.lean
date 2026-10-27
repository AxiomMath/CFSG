module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperE7Levi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFusion
import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFacts

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)

theorem autThreePowInner_of_E7Two
    {K : Type} [Field K] (hK : Nat.card K = 2)
    {G : Type} [Group G] {L : Subgroup G} (φ : ↥L ≃* ↥(adjointGroup .E7 K)) :
    AutThreePowInner ↥L := by
  intro ψ k _
  obtain ⟨a, ha⟩ :=
    CFSG.SeitzReduction.E7Pilot.forall_mem_range_conj_of_mulEquiv_E7_two hK φ ψ
  exact ⟨a, fun x => by rw [← ha]; exact MulAut.conj_apply a x⟩

theorem le_centralizer_of_E7Two
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {G : Type} [Group G] [Finite G] {L E T : Subgroup G} (φ : ↥L ≃* ↥(adjointGroup .E7 K))
    (hZ : Subgroup.center ↥L = ⊥) (hEL : E ≤ L) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 7 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.centralizer (L : Set G) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (L : Set G)
  set c : ↥N →* MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) with hcdef
  have hNinj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    intro a b hab
    have hmem : b⁻¹ * a ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun f : MulAut ↥L => f x) hab
      simp only [MulAut.conj_apply] at h
      calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
        _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [h]
        _ = (b⁻¹ * a) * x := by group
    have h1 : b⁻¹ * a = 1 := by
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  have hNsurj : Function.Surjective (MulAut.conj : ↥L →* MulAut ↥L) := fun ψ =>
    CFSG.SeitzReduction.E7Pilot.forall_mem_range_conj_of_mulEquiv_E7_two hK φ ψ
  set e : ↥L ≃* MulAut ↥L := MulEquiv.ofBijective _ ⟨hNinj, hNsurj⟩ with hedef
  set lam : ↥N →* ↥L := e.symm.toMonoidHom.comp c with hlamdef
  have hlam_l : ∀ l : ↥L, lam ⟨l, Subgroup.le_normalizer l.2⟩ = l := by
    intro l
    have hc : c ⟨l, Subgroup.le_normalizer l.2⟩ = MulAut.conj l := by
      ext x
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    change e.symm (c ⟨l, Subgroup.le_normalizer l.2⟩) = l
    rw [hc]
    exact e.symm_apply_apply l
  set R : Subgroup ↥(adjointGroup .E7 K) := ((T.subgroupOf N).map lam).map φ.toMonoidHom
  set E2 : Subgroup ↥(adjointGroup .E7 K) := (E.subgroupOf L).map φ.toMonoidHom
  have hTsub : IsPGroup 2 ↥(T.subgroupOf N) := by
    rw [Subgroup.subgroupOf]
    exact hT.comap_of_injective N.subtype N.subtype_injective
  have hR2 : IsPGroup 2 R := (hTsub.map lam).map φ.toMonoidHom
  have hEsub : IsElemAbelian 3 (E.subgroupOf L) := hE.subgroupOf L
  have hE2el : IsElemAbelian 3 E2 := hEsub.map φ.toMonoidHom
  have hcardE2 : Nat.card E2 = Nat.card E := by
    have h1 : Nat.card ↥((E.subgroupOf L).map φ.toMonoidHom) =
        Nat.card ↥(E.subgroupOf L) := Subgroup.card_map_of_injective φ.injective
    have h2 : Nat.card ↥(E.subgroupOf L) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
    exact h1.trans h2
  have hER : E2 ≤ Subgroup.normalizer (R : Set ↥(adjointGroup .E7 K)) := by
    rw [Subgroup.le_normalizer_iff]
    intro e2 he2 r hr
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he2
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    let n : ↥N := ⟨(x : G), Subgroup.le_normalizer x.2⟩
    have hlam_n : lam n = x := hlam_l x
    have hmemT : (n * t * n⁻¹ : ↥N) ∈ T.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      have h := (Subgroup.mem_normalizer_iff.mp (hET hxE)) (t : G)
      exact h.mp htT
    refine Subgroup.mem_map.mpr ⟨lam (n * t * n⁻¹),
      Subgroup.mem_map.mpr ⟨n * t * n⁻¹, hmemT, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, hlam_n]
  have hd : 3 ∣ Nat.card K + 1 := by norm_num [hK]
  have hpq : ¬ 3 ∣ Nat.card K - 1 := by norm_num [hK]
  have hL : ∀ (J : Set (Fin Tag.E7.rank)), J ≠ Set.univ →
      ∀ F : Subgroup (ModGL Tag.E7 K), F ≤ subsystemGroup Tag.E7 K J →
        IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 6 :=
    fun J hJ F hF hFel => CFSG.LocalAnalysis.GLTheoremA.levi_card_le_six_explicit
      Nat.prime_three (by norm_num) hd
      (CFSG.LocalAnalysis.GLTheoremA.rk2_levi_explicit 3 Nat.prime_three (by norm_num))
      hJ hF hFel
  have hRbot : R = ⊥ := by
    by_contra hRne
    have hbound : Nat.card E2 ≤ 3 ^ 6 :=
      CFSG.LocalAnalysis.GLTheoremA.twoLocal_card_le_of_levi' (p := 3) (k := 6)
        Nat.prime_three (by norm_num) hpq hL hRne hR2 hER hE2el
    rw [hcardE2] at hbound
    omega
  intro t ht
  have htn : (⟨t, hTN ht⟩ : ↥N) ∈ T.subgroupOf N := Subgroup.mem_subgroupOf.mpr ht
  have hmemR : φ (lam ⟨t, hTN ht⟩) ∈ R :=
    Subgroup.mem_map.mpr ⟨lam ⟨t, hTN ht⟩,
      Subgroup.mem_map.mpr ⟨⟨t, hTN ht⟩, htn, rfl⟩, rfl⟩
  rw [hRbot, Subgroup.mem_bot] at hmemR
  have hlam1 : lam ⟨t, hTN ht⟩ = 1 := φ.injective (by rw [hmemR, map_one])
  have hc1 : c ⟨t, hTN ht⟩ = 1 := by
    have h2 : e (lam ⟨t, hTN ht⟩) = c ⟨t, hTN ht⟩ := by
      rw [hlamdef]
      exact e.apply_symm_apply (c ⟨t, hTN ht⟩)
    rw [hlam1, map_one] at h2
    exact h2.symm
  have hker : (⟨t, hTN ht⟩ : ↥N) ∈ (Subgroup.normalizerMonoidHom (H := L)).ker := by
    rw [MonoidHom.mem_ker]
    exact hc1
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  have htC : t ∈ Subgroup.centralizer (L : Set G) := Subgroup.mem_subgroupOf.mp hker
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp htC) l hl

end CFSG.StandardType.FrameRoute

end
