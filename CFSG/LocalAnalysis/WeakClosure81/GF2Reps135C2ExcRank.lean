module

public import CFSG.Quasithin.Background.SmithCurtisBasic
import CFSG.GroupTheory.E3Params
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeSetup
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcCommon
import CFSG.Quasithin.H13.A5M22HatRow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.SmithCurtis
open scoped commutatorElement

theorem w135c2_periodic_fix_entries {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} (hirr : X1.IsIrrOn L) {S : Type}
    [Group S] (ι : S ≃* ↥L) {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    ∃ (δ m : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra K k)
      (ρ : Representation k S (Fin m → k)),
      1 ≤ δ ∧ IsSimpleRep ρ ∧ Function.Injective ρ ∧
      (∀ g : S, E3.mQuot ⊤ (fixV (Subgroup.zpowers ((ι g : ↥L) : MulAut W))) =
        δ * Module.finrank k (LinearMap.range (ρ g - 1))) ∧
      ∀ (s : S) (i j : Fin m), (ρ s (Pi.single j 1)) i ^ (2 ^ δ) = ρ s (Pi.single j 1) i := by
  obtain ⟨δ, m, k, hkField, hkFinite, hkChar, hAlg, ρ, ν, hδ, hm, hsimple, hρinj, hνinj,
    hWcard, hνeq, hrank, hfrob⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4.exists_periodic_rep (G := S) hW hirr ι hn hK
  let : Field k := hkField
  let : Finite k := hkFinite
  let : CharP k 2 := hkChar
  let : Algebra K k := hAlg
  refine ⟨δ, m, k, inferInstance, inferInstance, inferInstance, inferInstance, ρ, hδ, hsimple,
    hρinj, fun g => ?_, hfrob⟩
  set F : Subgroup W := fixV (Subgroup.zpowers ((ι g : ↥L) : MulAut W)) with hF
  have hcardF : Nat.card {v : W // (ι g : MulAut W) v = v} = Nat.card F := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    exact (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).symm
  have hcard : Nat.card W =
      2 ^ (δ * Module.finrank k (LinearMap.range (ρ g - 1))) * Nat.card F := by
    rw [hrank g, hcardF]
  have hidx : F.index = 2 ^ (δ * Module.finrank k (LinearMap.range (ρ g - 1))) := by
    have hpos : 0 < Nat.card F := Nat.card_pos
    have hmul : Nat.card F * F.index = Nat.card F *
        2 ^ (δ * Module.finrank k (LinearMap.range (ρ g - 1))) := by
      calc Nat.card F * F.index = Nat.card W := F.card_mul_index
        _ = 2 ^ (δ * Module.finrank k (LinearMap.range (ρ g - 1))) * Nat.card F := hcard
        _ = Nat.card F * 2 ^ (δ * Module.finrank k (LinearMap.range (ρ g - 1))) :=
            Nat.mul_comm _ _
    exact Nat.eq_of_mul_eq_mul_left hpos hmul
  rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx, CFSG.Quasithin.rkIdx, hidx,
    padicValNat.prime_pow]

theorem w135c2_periodic_fix {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} (hirr : X1.IsIrrOn L) {S : Type} [Group S] (ι : S ≃* ↥L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ (δ m : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra K k)
      (ρ : Representation k S (Fin m → k)),
      1 ≤ δ ∧ IsSimpleRep ρ ∧ Function.Injective ρ ∧
      ∀ g : S, E3.mQuot ⊤ (fixV (Subgroup.zpowers ((ι g : ↥L) : MulAut W))) =
        δ * Module.finrank k (LinearMap.range (ρ g - 1)) := by
  obtain ⟨δ, m, k, hkField, hkFinite, hkChar, hAlg, ρ, hδ, hsimple, hρinj, hfix, -⟩ :=
    w135c2_periodic_fix_entries hW hirr ι hn hK
  exact ⟨δ, m, k, hkField, hkFinite, hkChar, hAlg, ρ, hδ, hsimple, hρinj, hfix⟩

theorem w135c2_exists_outer_aut {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) {S : Type} [Group S] (ι : S ≃* ↥L)
    {t : MulAut W} (htY : t ∈ Y) (ht2 : orderOf t = 2) (htL : t ∉ L) :
    ∃ α : MulAut S, α * α = 1 ∧ (∀ c : S, α ≠ MulAut.conj c) ∧
      ∀ x : S, E3.mQuot ⊤ (fixV (Subgroup.zpowers ((ι ((α x)⁻¹ * x) : ↥L) : MulAut W))) ≤
        2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have hN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    w135c2_mem_normalizer_of_ctx hctx htY ht2
  let γ : MulAut ↥L := CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, hN⟩
  let α : MulAut S := ι.trans (γ.trans ι.symm)
  have hαapply : ∀ x : S, ι (α x) = γ (ι x) := by
    intro x
    simp [α]
  have hαcoe : ∀ x : S,
      ((ι (α x) : ↥L) : MulAut W) = t * ((ι x : ↥L) : MulAut W) * t⁻¹ := by
    intro x
    rw [hαapply x]
    exact CFSG.QuasithinUnique.Setup.X5.coe_conjOn L ⟨t, hN⟩ (ι x)
  have htt : t * t = 1 := by
    rw [← sq, ← ht2]
    exact pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hα2 : α * α = 1 := by
    ext x
    simp only [MulAut.mul_apply, MulAut.one_apply]
    apply ι.injective
    apply Subtype.ext
    rw [hαcoe (α x), hαcoe x, hti]
    calc t * (t * ((ι x : ↥L) : MulAut W) * t) * t
        = (t * t) * ((ι x : ↥L) : MulAut W) * (t * t) := by group
      _ = ((ι x : ↥L) : MulAut W) := by rw [htt, one_mul, mul_one]
  have hnotInner : ∀ c : S, α ≠ MulAut.conj c := by
    intro c hc
    have hcomm : ∀ l : ↥L,
        (((ι c : ↥L) : MulAut W)⁻¹ * t) * (l : MulAut W) =
          (l : MulAut W) * (((ι c : ↥L) : MulAut W)⁻¹ * t) := by
      intro l
      have h1 := hαcoe (ι.symm l)
      have h2 : α (ι.symm l) = MulAut.conj c (ι.symm l) := by rw [hc]
      rw [h2] at h1
      have h3 : ((ι (MulAut.conj c (ι.symm l)) : ↥L) : MulAut W) =
          ((ι c : ↥L) : MulAut W) * (l : MulAut W) *
            ((ι c : ↥L) : MulAut W)⁻¹ := by
        simp [MulAut.conj_apply]
      rw [h3] at h1
      simp only [MulEquiv.apply_symm_apply] at h1
      have h4 : t * (l : MulAut W) =
          ((ι c : ↥L) : MulAut W) * (l : MulAut W) *
            ((ι c : ↥L) : MulAut W)⁻¹ * t := by
        calc t * (l : MulAut W) = (t * (l : MulAut W) * t⁻¹) * t := by group
          _ = (((ι c : ↥L) : MulAut W) * (l : MulAut W) *
                ((ι c : ↥L) : MulAut W)⁻¹) * t := by rw [← h1]
          _ = ((ι c : ↥L) : MulAut W) * (l : MulAut W) *
                ((ι c : ↥L) : MulAut W)⁻¹ * t := rfl
      calc (((ι c : ↥L) : MulAut W)⁻¹ * t) * (l : MulAut W)
          = ((ι c : ↥L) : MulAut W)⁻¹ * (t * (l : MulAut W)) := by group
        _ = ((ι c : ↥L) : MulAut W)⁻¹ *
              (((ι c : ↥L) : MulAut W) * (l : MulAut W) *
                ((ι c : ↥L) : MulAut W)⁻¹ * t) := by rw [h4]
        _ = (l : MulAut W) * (((ι c : ↥L) : MulAut W)⁻¹ * t) := by group
    have huY : ((ι c : ↥L) : MulAut W)⁻¹ * t ∈ Y :=
      Y.mul_mem (Y.inv_mem (hctx.2.2.1 (ι c).2)) htY
    have huZ : ((ι c : ↥L) : MulAut W)⁻¹ * t ∈ Zc L := by
      refine w135c2_mem_Zc_of_comm hctx huY ?_
      intro l hl
      have h1 : ⁅((ι c : ↥L) : MulAut W)⁻¹ * t, l⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hcomm ⟨l, hl⟩
      rw [h1]
      exact (Zc L).one_mem
    have huL : ((ι c : ↥L) : MulAut W)⁻¹ * t ∈ L := w135c2_Zc_le L huZ
    apply htL
    have hmul : ((ι c : ↥L) : MulAut W) *
        (((ι c : ↥L) : MulAut W)⁻¹ * t) ∈ L := L.mul_mem (ι c).2 huL
    simpa [mul_assoc] using hmul
  refine ⟨α, hα2, hnotInner, fun x => ?_⟩
  set g : MulAut W := ((ι x : ↥L) : MulAut W) with hg
  have hfix : ((ι ((α x)⁻¹ * x) : ↥L) : MulAut W) = t * (g⁻¹ * t * g) := by
    have h1 : ι ((α x)⁻¹ * x) = (ι (α x))⁻¹ * ι x := by rw [map_mul, map_inv]
    have h2 := congrArg (fun z : ↥L => (z : MulAut W)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h2, hαcoe x, hti, hg]
    simp only [mul_inv_rev, hti]
    group
  rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx, hfix]
  have hR : 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) =
      2 * CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) := by
    rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx]
  rw [hR]
  have hmul := CFSG.Quasithin.H13.A5.M22Hat.rkIdx_fixV_mul_le hW t (g⁻¹ * t * g)
  have hconj : CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers (g⁻¹ * t * g))) =
      CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) := by
    rw [← CFSG.GroupTheory.mQuot_top_eq_rkIdx,
      show g⁻¹ * t * g = g⁻¹ * t * (g⁻¹)⁻¹ by rw [inv_inv],
      w135c2_mQuot_conj, CFSG.GroupTheory.mQuot_top_eq_rkIdx]
  calc CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers (t * (g⁻¹ * t * g))))
      ≤ CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) +
          CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers (g⁻¹ * t * g))) := hmul
    _ = CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) +
          CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) := by rw [hconj]
    _ = 2 * CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) := by rw [two_mul]

end CFSG.LocalAnalysis.WeakClosure81
