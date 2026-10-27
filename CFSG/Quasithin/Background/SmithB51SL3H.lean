module

public import CFSG.Quasithin.Background.SmithB51SL3G
public import CFSG.Quasithin.Background.FFC13M

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank

theorem exists_hom_section {M S : Type*} [CommGroup M] [CommGroup S] (hM : ∀ m : M, m ^ 2 = 1)
    (hS : ∀ s : S, s ^ 2 = 1) (φ : M →* S) (hφ : Function.Surjective φ) :
    ∃ σ : S →* M, ∀ s, φ (σ s) = s := by
  let _ : Module (ZMod 2) (Additive M) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact (pow_two (Additive.toMul x)).symm.trans (hM _)
  let _ : Module (ZMod 2) (Additive S) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact (pow_two (Additive.toMul x)).symm.trans (hS _)
  let φL : Additive M →ₗ[ZMod 2] Additive S := (MonoidHom.toAdditive φ).toZModLinearMap 2
  have hsurj : LinearMap.range φL = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro s
    obtain ⟨m, hm⟩ := hφ (Additive.toMul s)
    exact ⟨Additive.ofMul m, by simp [φL, hm]⟩
  obtain ⟨g, hg⟩ := φL.exists_rightInverse_of_surjective hsurj
  refine ⟨MonoidHom.toAdditive.symm g.toAddMonoidHom, fun s => ?_⟩
  have := LinearMap.congr_fun hg (Additive.ofMul s)
  simpa [φL] using this

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

theorem rootP_le_axisSub : rootP K ≤ axisSub (coordHyp 1) := by
  rintro _ ⟨c, rfl⟩
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · rw [slAct_elT, mem_coordHyp.1 hv, mul_zero, Pi.single_zero, add_zero]
  · rw [slAct_elT, add_sub_cancel_left, mem_coordHyp]
    simp

theorem NatSec.exists_lift_axis {W I : Subgroup V} (c : NatSec L W I K) (hLW : L ≤ stabSub W)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) (hpre : c.pre A = axisSub (stdAxis K))
    (hlift : ∀ u ∈ W, (∀ a ∈ A, a u * u⁻¹ ∈ I) → ∃ u' ∈ W, u' ∈ fixV A ∧ u' * u⁻¹ ∈ I)
    {W' : Submodule K (Fin 3 → K)} (hW' : Module.finrank K W' = 2) (u : ↥W)
    (hu : Multiplicative.toAdd (c.f u) ∈ W') :
    ∃ u' : ↥W, (∀ γ ∈ axisSub W', ((c.π γ : ↥L) : MulAut V) u' = u') ∧ c.f u' = c.f u := by
  obtain ⟨g, hg⟩ := exists_slMap_eq (finrank_coordHyp (K := K) 2) hW'
  have hu₀W : ((c.π g⁻¹ : ↥L) : MulAut V) (u : V) ∈ W := ((hLW (c.π g⁻¹).2) u).2 u.2
  set u₀ : ↥W := ⟨_, hu₀W⟩ with hu₀
  have hfu₀ : c.f u₀ = natAct (StatedSL 3 K) g⁻¹ (c.f u) := c.hfe g⁻¹ u hu₀W
  have hu₀ax : Multiplicative.toAdd (c.f u₀) ∈ stdAxis K := by
    rw [hfu₀]
    show slAct g⁻¹ (Multiplicative.toAdd (c.f u)) ∈ stdAxis K
    rw [← mem_slMap, hg]
    exact hu
  have hA : ∀ a ∈ A, a (u₀ : V) * (u₀ : V)⁻¹ ∈ I := by
    intro a ha
    obtain ⟨γ, hγ⟩ := c.hπ.2 ⟨a, hAL ha⟩
    have hγA : γ ∈ axisSub (stdAxis K) := by
      rw [← hpre]
      show ((c.π γ : ↥L) : MulAut V) ∈ A
      rw [hγ]
      exact ha
    have hau : ((c.π γ : ↥L) : MulAut V) (u₀ : V) ∈ W := ((hLW (c.π γ).2) _).2 u₀.2
    have hmem : ((c.π γ : ↥L) : MulAut V) (u₀ : V) * (u₀ : V)⁻¹ ∈ W :=
      W.mul_mem hau (W.inv_mem u₀.2)
    have hf : c.f ⟨_, hmem⟩ = 1 := by
      have e1 : (⟨_, hmem⟩ : ↥W) = ⟨_, hau⟩ * u₀⁻¹ := rfl
      rw [e1, map_mul, map_inv, c.hfe γ u₀ hau, mul_inv_eq_one]
      apply Multiplicative.toAdd.injective
      exact hγA.1 _ hu₀ax
    have e : ((c.π γ : ↥L) : MulAut V) = a := congrArg Subtype.val hγ
    rw [← e]
    exact (c.hfk _).1 hf
  obtain ⟨u₀', hu₀'W, hu₀'A, hu₀'I⟩ := hlift _ u₀.2 hA
  have hu'W : ((c.π g : ↥L) : MulAut V) u₀' ∈ W := ((hLW (c.π g).2) _).2 hu₀'W
  refine ⟨⟨_, hu'W⟩, fun γ hγ => ?_, ?_⟩
  · rw [← hg, ← map_conj_axisSub] at hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    have hγ₀A : ((c.π γ₀ : ↥L) : MulAut V) ∈ A := by
      have : γ₀ ∈ c.pre A := by rw [hpre]; exact hγ₀
      exact this
    have hinv : ∀ x : V, ((c.π g⁻¹ : ↥L) : MulAut V) (((c.π g : ↥L) : MulAut V) x) = x := by
      intro x
      rw [← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one]
      rfl
    show ((c.π (g * γ₀ * g⁻¹) : ↥L) : MulAut V) (((c.π g : ↥L) : MulAut V) u₀') =
      ((c.π g : ↥L) : MulAut V) u₀'
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply, MulAut.mul_apply,
      hinv, hu₀'A _ hγ₀A]
  · have h1 : c.f ⟨u₀', hu₀'W⟩ = c.f u₀ := by
      have hmem : u₀' * (u₀ : V)⁻¹ ∈ W := W.mul_mem hu₀'W (W.inv_mem u₀.2)
      have h2 : c.f ⟨_, hmem⟩ = 1 := (c.hfk _).2 hu₀'I
      have e1 : (⟨_, hmem⟩ : ↥W) = ⟨u₀', hu₀'W⟩ * u₀⁻¹ := rfl
      rw [e1, map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2
    rw [c.hfe g ⟨u₀', hu₀'W⟩ hu'W, h1, hfu₀]
    apply Multiplicative.toAdd.injective
    exact slAct_slAct_inv g _

theorem sq_eq_one_mult [CharP K 2] (s : Multiplicative K) : s ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, two_nsmul, CharTwo.add_self_eq_zero, toAdd_one]

variable [Finite K] [CharP K 2]

theorem NatSec.exists_levi_lift (hV : ∀ v : V, v ^ 2 = 1) {W I : Subgroup V}
    (c : NatSec L W I K) (hLW : L ≤ stabSub W) {A : Subgroup (MulAut V)} (hAL : A ≤ L)
    (hpre : c.pre A = axisSub (stdAxis K))
    (hlift : ∀ u ∈ W, (∀ a ∈ A, a u * u⁻¹ ∈ I) → ∃ u' ∈ W, u' ∈ fixV A ∧ u' * u⁻¹ ∈ I)
    (hq : 2 ∣ Nat.card K) :
    ∃ σ : Multiplicative K →* ↥W, ∀ k : K,
      (∀ γ ∈ levi K, ((c.π γ : ↥L) : MulAut V) (σ (Multiplicative.ofAdd k)) =
        σ (Multiplicative.ofAdd k)) ∧
      Multiplicative.toAdd (c.f (σ (Multiplicative.ofAdd k))) = Pi.single 2 k := by
  classical
  set ρW : ↥L →* MulAut ↥W := (resHom W).comp (Subgroup.inclusion hLW) with hρW
  set actW : ↥(levi K) →* MulAut ↥W := (ρW.comp c.π).comp (levi K).subtype with hactW
  have hactW_apply : ∀ (g : ↥(levi K)) (w : ↥W),
      ((actW g w : ↥W) : V) = ((c.π (g : ↥(StatedSL 3 K)) : ↥L) : MulAut V) w := fun _ _ => rfl
  set ev : Multiplicative (Fin 3 → K) →* Multiplicative K :=
    AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 3 => K) 2) with hev
  have hev_apply : ∀ x, Multiplicative.toAdd (ev x) = Multiplicative.toAdd x 2 := fun _ => rfl
  set Φ : ↥W →* Multiplicative K := ev.comp c.f with hΦ
  have hfact : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥W),
      c.f (ρW (c.π γ) w) = natAct (StatedSL 3 K) γ (c.f w) := by
    intro γ w
    have hw : ((c.π γ : ↥L) : MulAut V) w ∈ W := ((hLW (c.π γ).2) w).2 w.2
    exact c.hfe γ w hw
  have hΦe : ∀ (g : ↥(levi K)) (w : ↥W), Φ (actW g w) = (1 : ↥(levi K) →* MulAut _) g (Φ w) := by
    intro g w
    show ev (c.f (ρW (c.π (g : ↥(StatedSL 3 K))) w)) = ev (c.f w)
    rw [hfact]
    apply Multiplicative.toAdd.injective
    rw [hev_apply, hev_apply]
    exact g.2.1 _
  set D : Subgroup ↥W :=
    { carrier := {w | ∀ γ ∈ rootP K, ρW (c.π γ) w = w}
      one_mem' := fun γ _ => map_one _
      mul_mem' := fun {x y} hx hy γ hγ => by rw [map_mul, hx γ hγ, hy γ hγ]
      inv_mem' := fun {x} hx γ hγ => by rw [map_inv, hx γ hγ] } with hD
  have hDs : Function.Surjective (Φ.comp D.subtype) := by
    intro k
    obtain ⟨u, hu⟩ := c.hfs (Multiplicative.ofAdd (Pi.single 2 (Multiplicative.toAdd k)))
    have hu1 : Multiplicative.toAdd (c.f u) ∈ coordHyp 1 := by
      rw [hu, toAdd_ofAdd, mem_coordHyp]
      simp
    obtain ⟨u', hu'fix, hu'f⟩ := c.exists_lift_axis hLW hAL hpre hlift (finrank_coordHyp 1) u hu1
    refine ⟨⟨u', fun γ hγ => Subtype.ext (hu'fix γ (rootP_le_axisSub hγ))⟩, ?_⟩
    show ev (c.f u') = k
    apply Multiplicative.toAdd.injective
    rw [hev_apply, hu'f, hu, toAdd_ofAdd, Pi.single_eq_same]
  obtain ⟨σ₀, hσ₀⟩ := exists_hom_section (B1.sq_eq_one_sub (B1.sq_eq_one_sub hV W) D)
    sq_eq_one_mult _ hDs
  set σ : Multiplicative K →* ↥W := D.subtype.comp σ₀ with hσ
  have hσs : ∀ s, Φ (σ s) = s := hσ₀
  have hσQ : ∀ g ∈ (rootP K).subgroupOf (levi K), ∀ s,
      σ ((1 : ↥(levi K) →* MulAut (Multiplicative K)) g s) = actW g (σ s) := by
    intro g hg s
    show σ s = ρW (c.π (g : ↥(StatedSL 3 K))) (σ s)
    exact ((σ₀ s).2 _ (Subgroup.mem_subgroupOf.1 hg)).symm
  obtain ⟨σ', hσ's, hσ'e⟩ := B69.avg_section actW 1 Φ hΦe sq_eq_one_mult
    ((rootP K).subgroupOf (levi K)) (odd_index_rootP hq) σ hσs hσQ
  refine ⟨σ', fun k => ?_⟩
  have hfix : ∀ γ ∈ levi K, ((c.π γ : ↥L) : MulAut V) (σ' (Multiplicative.ofAdd k)) =
      σ' (Multiplicative.ofAdd k) := by
    intro γ hγ
    have := hσ'e ⟨γ, hγ⟩ (Multiplicative.ofAdd k)
    exact (congrArg Subtype.val this).symm
  refine ⟨hfix, ?_⟩
  set x := Multiplicative.toAdd (c.f (σ' (Multiplicative.ofAdd k))) with hx
  have hxfix : ∀ γ ∈ levi K, slAct γ x = x := by
    intro γ hγ
    have h1 := hfact γ (σ' (Multiplicative.ofAdd k))
    have h2 : ρW (c.π γ) (σ' (Multiplicative.ofAdd k)) = σ' (Multiplicative.ofAdd k) :=
      Subtype.ext (hfix γ hγ)
    rw [h2] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  have hx2 : x 2 = k := by
    have h1 : Multiplicative.toAdd (Φ (σ' (Multiplicative.ofAdd k))) = k := by
      rw [hσ's, toAdd_ofAdd]
    exact h1
  rw [eq_single_of_levi_fix hxfix, hx2]

end B5

end CFSG.Quasithin
