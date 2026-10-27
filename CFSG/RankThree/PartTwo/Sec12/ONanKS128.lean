module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLStatements
public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Reduce
public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Inner
public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Field
import CFSG.RankThree.PartTwo.Sec13.Item131Transport

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec12.KS128Move

theorem exists_u_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {x : slPi π 3 (p ^ f) K}
    (hxZ : x ∉ Subgroup.center (slPi π 3 (p ^ f) K)) (hx3 : x ^ 3 = 1)
    {ζ : MulAut (slPi π 3 (p ^ f) K)} (hζ3 : ζ ^ 3 = 1) (hζx : ζ x = x)
    (hζA : ζ ∉ Subgroup.zpowers (MulAut.conj x)) :
    ∃ u : slPi π 3 (p ^ f) K, u * x * u⁻¹ * x⁻¹ ∈ Subgroup.center (slPi π 3 (p ^ f) K) ∧
      u * x * u⁻¹ ≠ x ∧
      ζ u * u⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.center (slPi π 3 (p ^ f) K) ∧
      ζ u * u⁻¹ ∉ Subgroup.center (slPi π 3 (p ^ f) K) := by
  rcases exists_conj_or_field_of_pow_three_eq_one hK hq2 hζ3 with
    ⟨y, -, hζy⟩ | ⟨σ, hσ, H, hH, hζH⟩
  · exact exists_u_of_inner hK hq hxZ hx3 hζ3 hζx hζA hζy
  · obtain ⟨u, h1, h2, h3⟩ := exists_u_of_field hK hq hxZ hx3 hζx hσ hH hζH
    exact ⟨u, h1, h2, by rw [h3]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x),
      by rw [h3]; exact hxZ⟩

theorem ks128TypeCMove : KS128TypeCMove := by
  intro X _ _ hXq hX x hxZ hx3 Y hY hY9 hxY hfix
  obtain ⟨π, p, f, K, _, hK, hq, hq2, ⟨e₀⟩⟩ := Sec4.exists_slPi_model (L := (⊤ : Subgroup X))
    (Sec13.isSLThreePi_of_mulEquiv Subgroup.topEquiv.symm hX)
    (LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hXq)
  let e : X ≃* slPi π 3 (p ^ f) K := Subgroup.topEquiv.symm.trans e₀
  have hZ3 : Nat.card (Subgroup.center X) = 3 := by
    have h := card_center_slPi hK hq
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective] at h
    exact h
  obtain ⟨σ₀, hσ₀Y, hσ₀A⟩ := exists_not_mem_zpowers_conj hx3 hxZ hY9
  have hconj : MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
    refine MulEquiv.ext fun s => ?_
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hζ3 : MulAut.congr e σ₀ ^ 3 = 1 := by rw [← map_pow, hY.2 σ₀ hσ₀Y, map_one]
  have hζx : MulAut.congr e σ₀ (e x) = e x := by
    simp [MulAut.congr_apply, hfix σ₀ hσ₀Y]
  have hζA : MulAut.congr e σ₀ ∉ Subgroup.zpowers (MulAut.conj (e x)) := by
    intro h
    rw [← hconj] at h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    apply hσ₀A
    refine Subgroup.mem_zpowers_iff.2 ⟨k, (MulAut.congr e).injective ?_⟩
    rw [map_zpow, hk]
  have hxZ' : e x ∉ Subgroup.center (slPi π 3 (p ^ f) K) := fun h =>
    hxZ (by simpa using mem_center_of_mulEquiv e.symm h)
  have hx3' : (e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨u₀, h1, h2, h3, h4⟩ := exists_u_slPi hK hq hq2 hxZ' hx3' hζ3 hζx hζA
  have hσu : e (σ₀ (e.symm u₀) * (e.symm u₀)⁻¹) = MulAut.congr e σ₀ u₀ * u₀⁻¹ := by
    simp [MulAut.congr_apply]
  have h1' : e.symm u₀ * x * (e.symm u₀)⁻¹ * x⁻¹ ∈ Subgroup.center X := by
    simpa using mem_center_of_mulEquiv e.symm h1
  have h2' : e.symm u₀ * x * (e.symm u₀)⁻¹ ≠ x := by
    intro h
    apply h2
    simpa using congrArg e h
  have hsup : (Subgroup.zpowers x ⊔ Subgroup.center X).map (e : X →* slPi π 3 (p ^ f) K) =
      Subgroup.zpowers (e x) ⊔ Subgroup.center (slPi π 3 (p ^ f) K) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_center_eq]
    rfl
  have h3' : σ₀ (e.symm u₀) * (e.symm u₀)⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.center X := by
    have h3'' : e (σ₀ (e.symm u₀) * (e.symm u₀)⁻¹) ∈
        (Subgroup.zpowers x ⊔ Subgroup.center X).map (e : X →* slPi π 3 (p ^ f) K) := by
      rw [hsup, hσu]
      exact h3
    exact (Subgroup.mem_map_iff_mem e.injective).1 h3''
  have h4' : σ₀ (e.symm u₀) * (e.symm u₀)⁻¹ ∉ Subgroup.center X := fun h =>
    h4 (by rw [← hσu]; exact mem_center_of_mulEquiv e h)
  obtain ⟨hA, hB⟩ := move_of_one_generator hx3 hxZ hZ3 (fun σ hσ => hY.2 σ hσ) hY9 hxY hfix
    hσ₀Y hσ₀A h1' h3' h4'
  exact ⟨e.symm u₀, h1', h2', hA, hB⟩

end CFSG.RankThree.PartTwo.Sec12
