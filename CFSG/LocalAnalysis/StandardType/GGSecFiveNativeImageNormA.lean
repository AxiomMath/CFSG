module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermReflSigma
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameChange
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestPerm
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylOuterTransport

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

open scoped BigOperators

private theorem permAutHom_injective_aux {n p : ℕ} (hp : p.Prime) :
    Function.Injective (TypeBDatum.permAutHom n p) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have h1 : (TypeBDatum.permAutHom n p σ) (Pi.mulSingle i (ofAdd (1 : ZMod p))) =
      (TypeBDatum.permAutHom n p τ) (Pi.mulSingle i (ofAdd (1 : ZMod p))) := by
    rw [h]
  change permAut (p := p) σ (Pi.mulSingle i (ofAdd (1 : ZMod p))) =
      permAut (p := p) τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) at h1
  rw [permAut_mulSingle, permAut_mulSingle] at h1
  exact (mulSingle_ofAdd_eq_iff (p := p)
    (fun h0 => coord_zero_ne_one hp h0.symm) h1).1

private theorem aPermutationFull_eq_permAutHom_range {n p : ℕ} :
    aPermutationFull n p = (TypeBDatum.permAutHom n p).range := by
  rw [aPermutationFull, MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap (α := Fin n),
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨Equiv.swap a b, ⟨a, b, hab, rfl⟩, rfl⟩
  · rintro ⟨σ, ⟨a, b, hab, rfl⟩, rfl⟩
    exact ⟨a, b, hab, rfl⟩

private theorem exists_coord_eq_of_commute_swap {n p : ℕ} (hn : 2 ≤ n)
    {ψ : MulAut (Fin n → Multiplicative (ZMod p))}
    (hψ : ∀ a b : Fin n, a ≠ b →
      ψ * permAut (Equiv.swap a b) = permAut (Equiv.swap a b) * ψ) :
    ∃ α β : ZMod p, ∀ i k : Fin n,
      toAdd (ψ (Pi.mulSingle i (ofAdd (1 : ZMod p))) k) =
        α * (if k = i then 1 else 0) + β := by
  classical
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  let i0 : Fin n := ⟨0, hn0⟩
  let i1 : Fin n := ⟨1, hn1⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have h' := congrArg Fin.val h
    simp [i0, i1] at h'
  let other : Fin n → Fin n := fun a => if a = i0 then i1 else i0
  have hother : ∀ a, other a ≠ a := by
    intro a
    by_cases ha : a = i0
    · subst ha
      rw [show other i0 = i1 by simp [other]]
      exact Ne.symm hi01
    · rw [show other a = i0 by simp [other, ha]]
      exact Ne.symm ha
  let e : Fin n → Fin n → Multiplicative (ZMod p) := fun i => Pi.mulSingle i (ofAdd 1)
  let ψe : Fin n → Fin n → Multiplicative (ZMod p) := fun a => ψ (e a)
  let βfun : Fin n → ZMod p := fun a => toAdd (ψe a (other a))
  let αfun : Fin n → ZMod p := fun a => toAdd (ψe a a) - βfun a
  have ht_fix : ∀ a b c : Fin n, b ≠ c → a ≠ b → a ≠ c →
      permAut (Equiv.swap b c) (e a) = e a := by
    intro a b c _ hab hac
    rw [SpCoord.permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hab hac]
  have hfix_off : ∀ a b c : Fin n, b ≠ c → a ≠ b → a ≠ c →
      permAut (Equiv.swap b c) (ψe a) = ψe a := by
    intro a b c hbc hab hac
    have h1 : ψ (permAut (Equiv.swap b c) (e a)) =
        permAut (Equiv.swap b c) (ψ (e a)) := by
      have h2 := congrArg (fun g : MulAut (Fin n → Multiplicative (ZMod p)) => g (e a))
        (hψ b c hbc)
      simpa only [MulAut.mul_apply] using h2
    rw [← h1, ht_fix a b c hbc hab hac]
  have hconst_off : ∀ a k l : Fin n, k ≠ a → l ≠ a →
      toAdd (ψe a k) = toAdd (ψe a l) := by
    intro a k l hk hl
    by_cases hkl : k = l
    · rw [hkl]
    · have h1 := hfix_off a k l hkl (Ne.symm hk) (Ne.symm hl)
      have h2 := congrArg (fun f : Fin n → Multiplicative (ZMod p) => toAdd (f k)) h1
      rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
        Equiv.swap_apply_left] at h2
      exact h2.symm
  have hβ_off0 : ∀ a k : Fin n, k ≠ a → toAdd (ψe a k) = βfun a := by
    intro a k hk
    exact hconst_off a k (other a) hk (hother a)
  have hrel : ∀ a b : Fin n, a ≠ b →
      permAut (Equiv.swap a b) (ψe a) = ψe b := by
    intro a b hab
    have h1 : ψ (permAut (Equiv.swap a b) (e a)) =
        permAut (Equiv.swap a b) (ψ (e a)) := by
      have h2 := congrArg (fun g : MulAut (Fin n → Multiplicative (ZMod p)) => g (e a))
        (hψ a b hab)
      simpa only [MulAut.mul_apply] using h2
    rw [← h1]
    have h2 : permAut (Equiv.swap a b) (e a) = e b := by
      rw [SpCoord.permAut_mulSingle, Equiv.swap_apply_left]
    rw [h2]
  have hβ_const : ∀ a b : Fin n, a ≠ b → βfun a = βfun b := by
    intro a b hab
    rw [← hβ_off0 a b hab.symm, ← hβ_off0 b a hab]
    have h1 := hrel a b hab
    have h2 := congrArg (fun f : Fin n → Multiplicative (ZMod p) => toAdd (f a)) h1
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_left] at h2
    exact h2
  have hα_const : ∀ a b : Fin n, a ≠ b → αfun a = αfun b := by
    intro a b hab
    have h1 := hrel a b hab
    have h2 := congrArg (fun f : Fin n → Multiplicative (ZMod p) => toAdd (f b)) h1
    rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_right] at h2
    simp only [αfun]
    rw [hβ_const a b hab, h2]
  let β : ZMod p := βfun i0
  let α : ZMod p := αfun i0
  have hβfun : ∀ a, βfun a = β := by
    intro a
    by_cases ha : a = i0
    · rw [ha]
    · exact hβ_const a i0 ha
  have hαfun : ∀ a, αfun a = α := by
    intro a
    by_cases ha : a = i0
    · rw [ha]
    · exact hα_const a i0 ha
  have hβ_off : ∀ a k : Fin n, k ≠ a → toAdd (ψe a k) = β := by
    intro a k hk
    rw [hβ_off0 a k hk, hβfun a]
  have hα_diag : ∀ a, toAdd (ψe a a) = α + β := by
    intro a
    have h := hαfun a
    simp only [αfun] at h
    rw [hβfun a] at h
    exact sub_eq_iff_eq_add.mp h
  refine ⟨α, β, fun i k => ?_⟩
  by_cases hki : k = i
  · rw [hki, if_pos rfl, mul_one]
    exact hα_diag i
  · rw [if_neg hki, mul_zero, zero_add]
    exact hβ_off i k hki

private theorem add_form_of_commute_swap {n p : ℕ} [NeZero p]
    {ψ : MulAut (Fin n → Multiplicative (ZMod p))} (hn : 2 ≤ n)
    (hψ : ∀ a b : Fin n, a ≠ b →
      ψ * permAut (Equiv.swap a b) = permAut (Equiv.swap a b) * ψ) :
    ∃ α β : ZMod p, ∀ (f : Fin n → Multiplicative (ZMod p)) (k : Fin n),
      toAdd (ψ f k) = α * toAdd (f k) + β * ∑ i, toAdd (f i) := by
  classical
  obtain ⟨α, β, hcoord⟩ := exists_coord_eq_of_commute_swap hn hψ
  refine ⟨α, β, fun f k => ?_⟩
  have hdecomp : f = ∏ i, (Pi.mulSingle i (ofAdd (1 : ZMod p)) :
      Fin n → Multiplicative (ZMod p)) ^ (toAdd (f i)).val := by
    refine (Finset.univ_prod_mulSingle f).symm.trans ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← SpCoord.mulSingle_ofAdd_eq_pow i (toAdd (f i)), ofAdd_toAdd]
  calc toAdd (ψ f k)
      = toAdd (ψ (∏ i, (Pi.mulSingle i (ofAdd (1 : ZMod p)) :
          Fin n → Multiplicative (ZMod p)) ^ (toAdd (f i)).val) k) := by
        conv_lhs => rw [hdecomp]
    _ = ∑ i, ((toAdd (f i)).val : ZMod p) *
          toAdd (ψ (Pi.mulSingle i (ofAdd (1 : ZMod p))) k) := by
        rw [map_prod, Fintype.prod_apply, toAdd_prod]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_pow, Pi.pow_apply, toAdd_pow, nsmul_eq_mul]
    _ = ∑ i, ((toAdd (f i)).val : ZMod p) *
          (α * (if k = i then 1 else 0) + β) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoord i k]
    _ = α * ((toAdd (f k)).val : ZMod p) + β * ∑ i, ((toAdd (f i)).val : ZMod p) := by
        have hterm : ∀ i, ((toAdd (f i)).val : ZMod p) *
            (α * (if k = i then 1 else 0) + β) =
            α * (if k = i then ((toAdd (f i)).val : ZMod p) else 0) +
              β * ((toAdd (f i)).val : ZMod p) := by
          intro i
          by_cases hki : k = i
          · rw [if_pos hki, if_pos hki]
            ring
          · rw [if_neg hki, if_neg hki]
            ring
        rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, Fintype.sum_ite_eq]
    _ = α * toAdd (f k) + β * ∑ i, toAdd (f i) := by
        simp only [ZMod.natCast_zmod_val]

theorem exists_smul_perm_of_normalizes_aPermutationFull {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : ∀ w ∈ aPermutationFull n p, u * w * u⁻¹ ∈ aPermutationFull n p) :
    ∃ (α : ZMod p) (σ : Equiv.Perm (Fin n)),
      ∀ f : Fin n → Multiplicative (ZMod p), ∃ s : ZMod p, ∀ k : Fin n,
        toAdd (u f k) = α * toAdd (f (σ⁻¹ k)) + s := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hP : aPermutationFull n p = (TypeBDatum.permAutHom n p).range :=
    aPermutationFull_eq_permAutHom_range
  have hinj : Function.Injective (TypeBDatum.permAutHom n p) := permAutHom_injective_aux hp
  have hPeq : (aPermutationFull n p).map (MulAut.conj u).toMonoidHom =
      aPermutationFull n p := by
    have hle : (aPermutationFull n p).map (MulAut.conj u).toMonoidHom ≤
        aPermutationFull n p := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
      simpa [MulAut.conj_apply] using hu v hv
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj u).toMonoidHom)
      (MulAut.conj u).injective]
  have hnorm : u ∈ Subgroup.normalizer ((TypeBDatum.permAutHom n p).range : Set _) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hP]
    exact hPeq
  obtain ⟨F, hF⟩ :=
    exists_mulAut_conj_of_mem_normalizer_range (ρ := TypeBDatum.permAutHom n p) hinj hnorm
  have hF_swap : ∀ ⦃a b : Fin n⦄, a ≠ b → (F (Equiv.swap a b)).IsSwap := by
    intro a b hab
    have ht : permAut (Equiv.swap a b) ∈ aPermutationFull n p :=
      Subgroup.subset_closure ⟨a, b, hab, rfl⟩
    set v : MulAut (Fin n → Multiplicative (ZMod p)) :=
      u * permAut (Equiv.swap a b) * u⁻¹ with hv
    have hvP : v ∈ aPermutationFull n p := hu _ ht
    have hv2 : v ^ 2 = 1 := by
      rw [hv]
      have h := permAut_swap_sq (p := p) a b
      calc (u * permAut (Equiv.swap a b) * u⁻¹) ^ 2
          = u * permAut (Equiv.swap a b) ^ 2 * u⁻¹ := conj_pow
        _ = 1 := by rw [h]; simp
    have hfix : Nat.card {f : Fin n → Multiplicative (ZMod p) // v f = f} * p =
        Nat.card (Fin n → Multiplicative (ZMod p)) := by
      rw [hv, natCard_fix_conj_mulAut u (permAut (Equiv.swap a b))]
      exact card_fix_permAut_swap hp hp2 hab
    obtain ⟨c, d, hcd, hcd_eq⟩ :=
      eq_permAut_swap_of_mem_aPermutationFull hp hp2 hvP hv2 hfix
    refine ⟨c, d, hcd, ?_⟩
    apply hinj
    rw [hF (Equiv.swap a b)]
    change u * permAut (Equiv.swap a b) * u⁻¹ = permAut (Equiv.swap c d)
    rw [← hv, hcd_eq]
  have hF_swap' : ∀ σ : Equiv.Perm (Fin n), σ.IsSwap → (F σ).IsSwap := by
    rintro σ ⟨a, b, hab, rfl⟩
    exact hF_swap hab
  obtain ⟨π, hπ⟩ := exists_eq_conj_of_isSwap hn3 F F.injective hF_swap'
  have hconj_swap : ∀ a b : Fin n, a ≠ b →
      u * permAut (Equiv.swap a b) * u⁻¹ =
        permAut (Equiv.swap (π a) (π b)) := by
    intro a b hab
    have h1 := hF (Equiv.swap a b)
    change (TypeBDatum.permAutHom n p)
      ((F : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n)) (Equiv.swap a b)) =
      u * (TypeBDatum.permAutHom n p) (Equiv.swap a b) * u⁻¹ at h1
    rw [hπ (Equiv.swap a b)] at h1
    have h2 : (TypeBDatum.permAutHom n p) (π * Equiv.swap a b * π⁻¹) =
        (TypeBDatum.permAutHom n p) (Equiv.swap (π a) (π b)) := by
      rw [map_mul, map_mul, map_inv]
      exact TypeBDatum.permAut_mul_swap π a b
    rw [h2] at h1
    exact h1.symm
  let ψ : MulAut (Fin n → Multiplicative (ZMod p)) := permAut π⁻¹ * u
  have hψ_comm : ∀ a b : Fin n, a ≠ b →
      ψ * permAut (Equiv.swap a b) = permAut (Equiv.swap a b) * ψ := by
    intro a b hab
    have hconj : ψ * permAut (Equiv.swap a b) * ψ⁻¹ =
        permAut (Equiv.swap a b) := by
      have hcalc : ψ * permAut (Equiv.swap a b) * ψ⁻¹ =
          permAut π⁻¹ * (u * permAut (Equiv.swap a b) * u⁻¹) *
            (permAut π⁻¹)⁻¹ := by
        rw [show ψ = permAut π⁻¹ * u from rfl]
        group
      rw [hcalc, hconj_swap a b hab]
      simpa using TypeBDatum.permAut_mul_swap (p := p) π⁻¹ (π a) (π b)
    calc ψ * permAut (Equiv.swap a b)
        = (ψ * permAut (Equiv.swap a b) * ψ⁻¹) * ψ := by group
      _ = permAut (Equiv.swap a b) * ψ := by rw [hconj]
  obtain ⟨α, β, hform⟩ := add_form_of_commute_swap hn2 hψ_comm
  have hu_eq : u = permAut π * ψ := by
    have h1 : permAut π * ψ = u := by
      change (TypeBDatum.permAutHom n p) π *
        ((TypeBDatum.permAutHom n p) π⁻¹ * u) = u
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    exact h1.symm
  refine ⟨α, π, fun f => ⟨β * ∑ i, toAdd (f i), fun k => ?_⟩⟩
  rw [hu_eq, MulAut.mul_apply]
  change toAdd (permAut π (ψ f) k) = α * toAdd (f (π⁻¹ k)) + β * ∑ i, toAdd (f i)
  rw [SpCoord.permAut_apply, Function.comp_apply]
  exact hform f (π⁻¹ k)

end CFSG.StandardType

end
