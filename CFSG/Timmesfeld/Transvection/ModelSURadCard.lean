module

public import CFSG.Timmesfeld.Transvection.ModelSUTheta
import CFSG.Timmesfeld.Transvection.ModelSUCentre

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed
open scoped commutatorElement

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem natCard_uRad {a d : Fin m → F} {T : Subgroup (SU σ m)} (Θ : SUThetaFacts σ a d T)
    (hTu : T ≤ uRad σ a) :
    Nat.card (uRad σ a) = Nat.card T * Nat.card (perpPair σ a d) := by
  let θ : ↥(uRad σ a) →* Multiplicative ↥(perpPair σ a d) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd ⟨radVec σ a d x, Θ.mem_perp x⟩) fun x y => by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (Θ.mul x.2 y.2)
  have hθ : Function.Surjective θ := fun w => by
    obtain ⟨x, hx, hxw⟩ := Θ.exists_eq (Multiplicative.toAdd w).2
    exact ⟨⟨x, hx⟩, Multiplicative.toAdd.injective (Subtype.ext hxw)⟩
  have hker : θ.ker = T.subgroupOf (uRad σ a) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← Θ.eq_zero_iff x.2]
    exact ⟨fun h => congrArg Subtype.val (congrArg Multiplicative.toAdd h),
      fun h => Multiplicative.toAdd.injective (Subtype.ext h)⟩
  rw [θ.ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTu).toEquiv,
    Nat.card_congr (Multiplicative.ofAdd : ↥(perpPair σ a d) ≃ Multiplicative ↥(perpPair σ a d)),
    mul_comm]

theorem radVec_commutatorElement_uTrans {a d : Fin m → F} {T : Subgroup (SU σ m)}
    (Θ : SUThetaFacts σ a d T) {e : Fin m → F} (he : e ∈ perpPair σ a d)
    (hee : uForm σ e e = 0) {t : SU σ m} (ht : suMat σ m t = uTrans σ e 1) {y : SU σ m}
    (hy : y ∈ uRad σ a) :
    radVec σ a d ⁅t, y⁆ = uForm σ e (radVec σ a d y) • e := by
  have hta : suMat σ m t *ᵥ a = (1 : F) • a := by rw [one_smul]; exact Θ.transv_a he ht
  have htl : t ∈ uLine σ a := ⟨1, one_ne_zero, hta⟩
  rw [commutatorElement_def, Θ.mul (conj_mem_uRad htl hy) (inv_mem hy), Θ.conj hta hy, Θ.inv hy,
    map_one, one_smul, Θ.levAct_transv he hee ht (Θ.mem_perp y), one_mul]
  abel

theorem eq_one_of_mem_uRad_of_mem_center [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {T : Subgroup (SU σ m)}
    (hT : IsUTransGroup σ a T) (Θ : SUThetaFacts σ a d T) (G : SUGeomFacts σ a d)
    {z : SU σ m} (hz : z ∈ uRad σ a) (hzc : z ∈ Subgroup.center (SU σ m)) : z = 1 :=
  eq_one_of_mem_isUTransGroup_of_mem_center hσ haa hdd had hT
    (mem_of_forall_commute_of_mem_uRad hσ htr haa hdd had Θ G hz
      fun u _ => (Subgroup.mem_center_iff.1 hzc u).symm) hzc

theorem uRad_le_centralizer {a : Fin m → F} {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) :
    uRad σ a ≤ Subgroup.centralizer (T : Set (SU σ m)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨c, -, htc⟩ := (hT.1 t).1 ht
  have h := suMat_conj_of_eq σ htc x
  rw [hx.1, ← htc] at h
  have h2 : x * t * x⁻¹ = t := suMat_injective σ h
  calc t * x = x * t * x⁻¹ * x := by rw [h2]
    _ = x * t := by group

end ModelRank

end CFSG.Timmesfeld.Transvection
