module

public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofCarrier
public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofEigen
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.TauCetiBridge.Twisted

namespace Item223Rank2Proof

theorem not_three_dvd_two_pow (f : ℕ) : ¬ 3 ∣ 2 ^ f := fun h => by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

section Fixed

variable {q : PrimePower} {hv : (LieTypeIndex.trialityD4 q).Valid}

theorem card_le_nine_of_fixedPoints (hp2 : q.p = 2)
    (E : Subgroup (D4Tripled.points (d4Closure q hv))) [Finite E]
    (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hfix : ∀ g ∈ E, (d4Index q hv).steinberg g = g) : Nat.card E ≤ 9 := by
  set L := d4Closure q hv with hL
  have hchar : d4Char q hv = 2 := by rw [d4Char_eq]; exact hp2
  have : CharP L 2 := hchar ▸ inferInstance
  have h3 : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (3 : L) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  set β : Fin 3 → ↥E →* Matrix.GeneralLinearGroup (Fin 8) L := fun k =>
    (blkHom k).comp ((Subgroup.inclusion (points_le_blockGL L)).comp E.subtype) with hβ
  have hβval : ∀ k (x : ↥E), ((β k x : Matrix.GeneralLinearGroup (Fin 8) L) :
      Matrix (Fin 8) (Fin 8) L) = blk k (((x : D4Tripled.points L) :
        Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) := fun _ _ => rfl
  have hcl : ∀ x : ↥E, CliffEq (((x : D4Tripled.points L) :
      Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) := fun x =>
    cliffEq_of_mem_points L _ (x : D4Tripled.points L).2
  refine card_le_nine_of_triality h3 (fun x y => hE.1.1.comm x y)
    (fun x => Subtype.ext (hE.2 x x.2)) β (fun x hx => ?_) (castM formMat)
    det_formMat_map_ne_zero muR nuR muR_smul_left muR_smul_right nuR_smul_right
    (fun x v s => ?_) (fun x v u => ?_) nuR_muR_add (d4Fr q hv) q.card
    (by rw [PrimePower.card_def, hp2]; exact not_three_dvd_two_pow _) (d4Fr_apply q hv)
    trialityBlkPerm
    (fun x j r c => ?_)
  ·
    have hM := d4_points_isBlockDiag L _ (x : D4Tripled.points L).2
    have h1 := eq_one_of_blk hM fun k => by
      rw [← hβval, hx k, Units.val_one]
    exact Subtype.ext (Subtype.ext (Units.ext h1))
  · rw [hβval, hβval, hβval]
    exact mulVec_muR (hcl x) v s
  · rw [hβval, hβval, hβval]
    exact mulVec_nuR (hcl x) v u
  · rw [hβval, hβval, d4Fr_apply]
    exact steinberg_fixed_blk _ (hfix x x.2) j r c

end Fixed

section Native


theorem exists_injective_fixedPoints {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ TwistTag.D4.order) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid) (_ : q.p = 2)
      (ρ : ↥(graphFixedRootGroup TwistTag.D4 K σ) →* D4Tripled.points (d4Closure q hv)),
      Function.Injective ρ ∧ ∀ x, (d4Index q hv).steinberg (ρ x) = ρ x := by
  set q : PrimePower := ⟨2, f, Nat.prime_two, hf⟩ with hqdef
  have hv : (LieTypeIndex.trialityD4 q).Valid := LieTypeIndex.valid_trialityD4 q
  refine ⟨q, hv, rfl, ?_⟩
  set L := d4Closure q hv with hL
  set p := d4Char q hv with hpdef
  have hp2 : p = 2 := d4Char_eq q hv
  have hp : Nat.Prime 2 := Nat.prime_two
  have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (hp2 ▸ hp) (k := f * 3) (by omega) (by rw [hK, hp2, pow_mul]; rfl)
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : Algebra.IsAlgebraic (ZMod p) K := Algebra.IsAlgebraic.of_finite (ZMod p) K
  let ι : K →ₐ[ZMod p] L := IsAlgClosed.lift
  let : Algebra K L := ι.toRingHom.toAlgebra
  have : IsScalarTower (ZMod p) K L :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ZMod p) K
  have : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  have hFr : ∀ c, d4Fr q hv c = c ^ (2 ^ f) := fun c => by
    rw [d4Fr_apply q hv c, PrimePower.card_def]
  have : CharP L 2 := hp2 ▸ inferInstance
  have h := CFSG.TauCetiBridge.Even.isTwistedIsogeny_steinberg_two (d4PushDown L) (q := q)
    (hv := hv) rfl
  have hperf := commutator_derived_eq L (d4Fr q hv) hp hf hK hσ hFr
  set ψ := h.derivedMap hperf with hψ
  have hψi : Function.Injective ψ := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    rw [h.coe_derivedMap, h.coe_derivedMap] at h1
    exact Subtype.ext (Subtype.ext (pushDown_injective L h1))
  have hψs := h.derivedMap_surjective hperf
  set φ₀ := rootGroupEquivDerived L (d4Fr q hv) hp hf hK hσ hFr with hφ₀
  set e := (MulEquiv.ofBijective ψ ⟨hψi, hψs⟩).symm with he
  refine ⟨(fixedSubgroup (d4Index q hv).steinberg).subtype.comp
    ((commutator ↥(fixedSubgroup (d4Index q hv).steinberg)).subtype.comp
      (e.toMonoidHom.comp φ₀.toMonoidHom)), ?_, fun x => ?_⟩
  · exact Subtype.val_injective.comp (Subtype.val_injective.comp
      (e.injective.comp φ₀.injective))
  · exact mem_fixedSubgroup.1 ((e (φ₀ x) : ↥(fixedSubgroup (d4Index q hv).steinberg)).2)

theorem card_le_nine_of_graphFixedRootGroup {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ TwistTag.D4.order) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (F : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  obtain ⟨q, hv, hq2, ρ, hρ, hρF⟩ := exists_injective_fixedPoints hf hK hσ
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have : Finite (F.map ρ) := Finite.of_surjective _ (ρ.subgroupMap_surjective F)
  have h := card_le_nine_of_fixedPoints hq2 (F.map ρ) (Sec4.isElemAbelian_map ρ hF) (by
    rintro _ ⟨x, -, rfl⟩
    exact hρF x)
  rwa [Subgroup.card_map_of_injective hρ] at h

end Native

end Item223Rank2Proof

open Item223Rank2Proof

theorem trialityD4EvenThreeRankTwo_holds :
    TrialityD4EvenThreeRankTwo := by
  intro X _ f hX
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hX
  exact Item223RankResProof.pRank_quotient_center_le_two_of_mulEquiv
    (e.trans (nativeEquiv hp hf hK hσ))
    (center_graphFixedRootGroup_eq_bot σ)
    (fun F hF => card_le_nine_of_graphFixedRootGroup hf hK hσ F hF)

end CFSG.RankThree.PartTwo.Sec21
