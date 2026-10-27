module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockZ
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.StandardType.SpCoord
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix Multiplicative
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCSpFull

theorem sympMinusZ_vanish_of_fixes {K : Type} [Field K] {m : ℕ} (g : StatedSp m K)
    (P : Fin m → Prop)
    (hfix : ∀ i, P i → ∀ a : Fin 2, spEnd g (Pi.single (WitSpNs.coord a i) (1 : K)) =
      Pi.single (WitSpNs.coord a i) (1 : K))
    (v : Fin m ⊕ Fin m → K) (hv : ∀ i, P i → ∀ a : Fin 2, v (WitSpNs.coord a i) = 0) :
    ∀ i, P i → ∀ a : Fin 2, spEnd g v (WitSpNs.coord a i) = 0 := by
  intro i hi a
  have hpar : ∃ a' : Fin 2, par (WitSpNs.coord a i) = WitSpNs.coord a' i := by
    fin_cases a
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  obtain ⟨a', ha'⟩ := hpar
  have h1 : form (spEnd g v) (Pi.single (par (WitSpNs.coord a i)) (1 : K)) =
      form v (Pi.single (par (WitSpNs.coord a i)) (1 : K)) := by
    rw [ha']
    calc form (spEnd g v) (Pi.single (WitSpNs.coord a' i) (1 : K))
        = form (spEnd g v) (spEnd g (Pi.single (WitSpNs.coord a' i) (1 : K))) := by
          rw [hfix i hi a']
      _ = form v (Pi.single (WitSpNs.coord a' i) (1 : K)) := by
          rw [spEnd_apply, spEnd_apply]
          exact form_mulVec g v _
  rw [form_single_right, form_single_right, par_par, hv i hi a, zero_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_right (sgn_ne_zero _)

theorem sympMinusZ_fixes_of_supported {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f : Fin m → Multiplicative (ZMod p)) (Q : Fin m → Prop) (hQ : ∀ i, Q i → f i = 1)
    (u : Fin m ⊕ Fin m → K) (hu : ∀ i, ¬ Q i → ∀ a : Fin 2, u (WitSpNs.coord a i) = 0) :
    spEnd (spPlaneTorus m ζ f) u = u := by
  have hsum : u = ∑ c, u c • (Pi.single c (1 : K) : Fin m ⊕ Fin m → K) := by
    funext r
    simp [Finset.sum_apply, Pi.single_apply]
  calc spEnd (spPlaneTorus m ζ f) u
      = spEnd (spPlaneTorus m ζ f) (∑ c, u c • (Pi.single c (1 : K) : Fin m ⊕ Fin m → K)) := by
        rw [← hsum]
    _ = ∑ c, u c • spEnd (spPlaneTorus m ζ f) (Pi.single c (1 : K)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun c _ => by rw [map_smul]
    _ = ∑ c, u c • (Pi.single c (1 : K) : Fin m ⊕ Fin m → K) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hc0 : u c = 0
        · rw [hc0, zero_smul, zero_smul]
        · have hc : c = WitSpNs.coord (WitSpNs.side c) (WitSpNs.plane c) :=
            WitSpNs.eq_of_plane_side (by simp) (by simp)
          have hQc : Q (WitSpNs.plane c) := by
            by_contra hnq
            apply hc0
            have h := hu _ hnq (WitSpNs.side c)
            rwa [← hc] at h
          have hfix : spEnd (spPlaneTorus m ζ f) (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
            have h := sympMinusZ_basis_fixed ζ f (WitSpNs.plane c) (hQ _ hQc) (WitSpNs.side c)
            rwa [← hc] at h
          rw [hfix]
    _ = u := hsum.symm

theorem sympMinusZ_coeff_eq {K : Type} [Field K] {m : ℕ} (i : Fin m) (c₁ c₂ : Fin 2 → K)
    (h : ∑ b : Fin 2, c₁ b • (Pi.single (WitSpNs.coord b i) (1 : K) : Fin m ⊕ Fin m → K) =
      ∑ b : Fin 2, c₂ b • (Pi.single (WitSpNs.coord b i) (1 : K) : Fin m ⊕ Fin m → K))
    (b : Fin 2) : c₁ b = c₂ b := by
  have h2 := congrFun h (WitSpNs.coord b i)
  revert h2
  fin_cases b <;> intro h2 <;> simpa [Fin.sum_univ_two, Pi.single_apply] using h2

theorem sympMinusZ_sectionFrameAut_le {K : Type} [Field K] [CharP K 2] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K) (hζ : Function.Injective ζ)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J₀ : Subgroup (StatedSp m K)}
    (hsupp : ∀ j ∈ J₀, ∀ x : Fin m, f₀ x ≠ 1 → ∀ y : Fin m,
      blk (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0) :
    FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ ≤
      TypeBDatum.signedSupportedAut m p (Finset.univ.filter fun i : Fin m => f₀ i = 1) := by
  intro τ hτ
  obtain ⟨n, hnJ, hn⟩ := hτ
  have hτ' : τ ∈ TypeBDatum.signedAut m p :=
    sympMinus_sectionFrameAut_le_signedAut hp hp2 ζ hζ ⟨n, Subgroup.mem_top _, hn⟩
  obtain ⟨π, ε, hε, hπ⟩ := exists_signedPerm_of_normalizes (F := K) hp hp2 hζ n
    (fun f => ⟨τ f, hn f⟩)
  have hu : ∀ f i, toAdd (τ f (π i)) = ε i * toAdd (f i) := fun f i => hπ f (τ f) (hn f) i
  have hnfix : ∀ i : Fin m, f₀ i ≠ 1 → ∀ a : Fin 2,
      spEnd n (Pi.single (WitSpNs.coord a i) (1 : K)) = Pi.single (WitSpNs.coord a i) (1 : K) :=
    fun i hi a => sympMinusZ_spEnd_single_of_hsupp n f₀ (fun x hx y => hsupp n hnJ x hx y) hi a
  have hninv : ∀ i : Fin m, f₀ i ≠ 1 → ∀ a : Fin 2,
      spEnd n⁻¹ (Pi.single (WitSpNs.coord a i) (1 : K)) =
        Pi.single (WitSpNs.coord a i) (1 : K) := by
    intro i hi a
    have h1 : spEnd (n⁻¹ * n) (Pi.single (WitSpNs.coord a i) (1 : K)) =
        Pi.single (WitSpNs.coord a i) (1 : K) := by
      rw [inv_mul_cancel, spEnd_one, Module.End.one_apply]
    rw [spEnd_mul, Module.End.mul_apply, hnfix i hi a] at h1
    exact h1
  have hcoord : ∀ (f : Fin m → Multiplicative (ZMod p)) (i : Fin m), f₀ i ≠ 1 → τ f i = f i := by
    intro f i hi
    apply hζ
    apply Subtype.ext
    ext b a
    have h1 := congrArg (fun g => spEnd g (Pi.single (WitSpNs.coord a i) (1 : K))) (hn f)
    simp only [spEnd_mul, Module.End.mul_apply, hninv i hi a, sympMinusZ_spEnd_coord, map_sum,
      map_smul, hnfix i hi] at h1
    exact (sympMinusZ_coeff_eq i _ _ h1 b).symm
  refine TypeBDatum.mem_signedSupportedAut_of_fix hp hτ' _ fun i hi => ?_
  have hfi : f₀ i ≠ 1 := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
  have h := IsSignedPerm.apply_mulSingle hu i (1 : ZMod p)
  have hc := hcoord (Pi.mulSingle i (ofAdd 1)) i hfi
  rw [h] at hc
  have hc' := congrArg toAdd hc
  rw [toAdd_mulSingle, toAdd_mulSingle] at hc'
  by_cases hπi : π i = i
  · rw [if_pos hπi.symm, if_pos rfl] at hc'
    rw [h, hπi, hc']
  · rw [if_neg (fun e => hπi e.symm), if_pos rfl] at hc'
    exact absurd hc' (coord_zero_ne_one hp)

theorem sympMinusZ_commute_of_fix {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J₀ : Subgroup (StatedSp m K)}
    (hsupp : ∀ j ∈ J₀, ∀ x : Fin m, f₀ x ≠ 1 → ∀ y : Fin m,
      blk (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x = if y = x then 1 else 0)
    (f : Fin m → Multiplicative (ZMod p)) (hf : ∀ i, f₀ i = 1 → f i = 1)
    {j : StatedSp m K} (hj : j ∈ J₀) :
    spPlaneTorus m ζ f * j = j * spPlaneTorus m ζ f := by
  have hjfix : ∀ i : Fin m, f₀ i ≠ 1 → ∀ a : Fin 2,
      spEnd j (Pi.single (WitSpNs.coord a i) (1 : K)) = Pi.single (WitSpNs.coord a i) (1 : K) :=
    fun i hi a => sympMinusZ_spEnd_single_of_hsupp j f₀ (fun x hx y => hsupp j hj x hx y) hi a
  have hinj : Function.Injective
      (spEnd : StatedSp m K → Module.End K (Fin m ⊕ Fin m → K)) :=
    fun a b h => spLin_injective (Units.ext h)
  apply hinj
  rw [spEnd_mul, spEnd_mul]
  refine (Pi.basisFun K (Fin m ⊕ Fin m)).ext fun c => ?_
  rw [Pi.basisFun_apply, Module.End.mul_apply, Module.End.mul_apply]
  have hc : c = WitSpNs.coord (WitSpNs.side c) (WitSpNs.plane c) :=
    WitSpNs.eq_of_plane_side (by simp) (by simp)
  generalize WitSpNs.side c = a at hc
  generalize WitSpNs.plane c = i at hc
  subst hc
  by_cases hi : f₀ i = 1
  · rw [sympMinusZ_basis_fixed ζ f i (hf i hi) a]
    refine sympMinusZ_fixes_of_supported ζ f (fun i => f₀ i = 1) hf _ ?_
    refine sympMinusZ_vanish_of_fixes j (fun i => f₀ i ≠ 1) hjfix _ ?_
    intro i' hi' a'
    have hne : i' ≠ i := fun h => hi' (h ▸ hi)
    fin_cases a <;> fin_cases a' <;> simp [Pi.single_apply, hne]
  · rw [hjfix i hi a, sympMinusZ_spEnd_coord ζ f i a, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, hjfix i hi b]

end CFSG.StandardType.SympMinus

end
