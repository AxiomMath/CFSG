module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSpLift
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.LieType.Universal.Symplectic
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus

public section

namespace CFSG.StandardType

namespace StdSubSp

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank TableBSymp CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {n : ℕ}

section Diag

theorem mat_apply_eq_zero_of_commute_diag {x d : StatedSp n K} {α : Fin n ⊕ Fin n → K}
    (hd : mat n K d = diagonal α) (hx : x * d = d * x) {a b : Fin n ⊕ Fin n} (hab : α a ≠ α b) :
    mat n K x a b = 0 := by
  have e := congrFun (congrFun (congrArg (mat n K) hx) a) b
  rw [map_mul, map_mul, hd, mul_diagonal, diagonal_mul] at e
  have : mat n K x a b * (α b - α a) = 0 := by
    rw [mul_sub, e]
    ring
  exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hab))

theorem commute_of_diag_of_forall {x d d' : StatedSp n K} {α β : Fin n ⊕ Fin n → K}
    (hd : mat n K d = diagonal α) (hd' : mat n K d' = diagonal β)
    (hαβ : ∀ a b, α a = α b → β a = β b) (hx : x * d = d * x) : d' * x = x * d' := by
  refine mat_injective ?_
  ext a b
  rw [map_mul, map_mul, hd', mul_diagonal, diagonal_mul]
  by_cases hab : α a = α b
  · rw [hαβ a b hab]
    ring
  · rw [mat_apply_eq_zero_of_commute_diag hd hx hab]
    ring

end Diag

section Supp

variable {S : Set (Fin n ⊕ Fin n)}

theorem commute_of_mem_suppGroup {g d : StatedSp n K} {α : Fin n ⊕ Fin n → K}
    (hd : mat n K d = diagonal α) (hS : ∀ a ∈ S, α a = 1) (hg : g ∈ suppGroup S) :
    g * d = d * g := by
  refine mat_injective ?_
  ext a b
  rw [map_mul, map_mul, hd, mul_diagonal, diagonal_mul]
  by_cases h : a ∈ S ∧ b ∈ S
  · rw [hS a h.1, hS b h.2]
    ring
  · rw [mem_suppGroup.mp hg a b h]
    by_cases hab : a = b
    · subst hab
      ring
    · rw [one_apply_ne hab]
      ring

theorem conj_mem_suppGroup_of_commute {c g d : StatedSp n K} {α : Fin n ⊕ Fin n → K}
    (hd : mat n K d = diagonal α) (hS : ∀ a ∈ S, α a = 1) (hSc : ∀ a ∉ S, α a ≠ 1)
    (hc : c * d = d * c) (hg : g ∈ suppGroup S) : c * g * c⁻¹ ∈ suppGroup S := by
  have hc' : c⁻¹ * d = d * c⁻¹ := (Commute.inv_left (show Commute c d from hc)).eq
  have hg' := mem_suppGroup.mp hg
  have hrow : ∀ a ∉ S, ∀ v, (mat n K c * mat n K g) a v = mat n K c a v := by
    intro a ha v
    rw [show mat n K c a v =
        (mat n K c * (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) a v by rw [Matrix.mul_one],
      Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ S
    · rw [mat_apply_eq_zero_of_commute_diag hd hc (a := a) (b := u)
        (by rw [hS u hu]; exact hSc a ha), zero_mul, zero_mul]
    · rw [hg' u v (fun h => hu h.1)]
  have hcol : ∀ b ∉ S, ∀ u, (mat n K g * mat n K c⁻¹) u b = mat n K c⁻¹ u b := by
    intro b hb u
    rw [show mat n K c⁻¹ u b =
        ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * mat n K c⁻¹) u b by rw [Matrix.one_mul],
      Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ S
    · rw [mat_apply_eq_zero_of_commute_diag hd hc' (a := v) (b := b)
        (by rw [hS v hv]; exact (hSc b hb).symm), mul_zero, mul_zero]
    · rw [hg' u v (fun h => hv h.2)]
  rw [mem_suppGroup]
  intro a b hab
  rw [not_and_or] at hab
  rcases hab with ha | hb
  · have h1 : (mat n K c * mat n K g * mat n K c⁻¹) a b = (mat n K c * mat n K c⁻¹) a b := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun v _ => by rw [hrow a ha v]
    rw [map_mul, map_mul, h1, ← map_mul, mul_inv_cancel, map_one]
  · have h1 : (mat n K c * (mat n K g * mat n K c⁻¹)) a b = (mat n K c * mat n K c⁻¹) a b := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [hcol b hb u]
    rw [map_mul, map_mul, Matrix.mul_assoc, h1, ← map_mul, mul_inv_cancel, map_one]

theorem isQuasisimple_suppGroup_range {m : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) :
    CFSG.IsQuasisimple (suppGroup (K := K) (Set.range (Sum.map σ σ))) := by
  rw [← range_spEmbed hσ]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (spEmbed_injective hσ))
    (CFSG.LieType.Universal.Symplectic.isQuasisimple m K hm (Or.inl (Or.inr hK)))

theorem isSupp_diagonal {β : Fin n ⊕ Fin n → K} (hβ : ∀ a ∉ S, β a = 1) :
    IsSupp S (diagonal β) := by
  intro a b hab
  by_cases h : a = b
  · subst h
    rw [diagonal_apply_eq, one_apply_eq]
    exact hβ a fun ha => hab ⟨ha, ha⟩
  · rw [diagonal_apply_ne _ h, one_apply_ne h]

theorem isSupp_transvection {i j : Fin n ⊕ Fin n} (hi : i ∈ S) (hj : j ∈ S) (c : K) :
    IsSupp S (Matrix.transvection i j c) := by
  intro a b hab
  rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  have : ¬(i = a ∧ j = b) := fun h => hab ⟨h.1 ▸ hi, h.2 ▸ hj⟩
  rw [ite_eq_right this, add_zero]

theorem isSupp_permMatrix {π : Equiv.Perm (Fin n ⊕ Fin n)} (hπ : ∀ a ∉ S, π a = a) :
    IsSupp S (π.permMatrix K) := by
  intro a b hab
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  by_cases ha : a ∈ S
  · have hb : b ∉ S := fun hb => hab ⟨ha, hb⟩
    have hπa : π a ∈ S := by
      by_contra h
      have h1 := hπ _ h
      exact h (by rw [π.injective h1]; exact ha)
    rw [ite_eq_right (fun h => hb (by rw [h]; exact hπa)),
      one_apply_ne (fun h => hb (by rw [← h]; exact ha))]
  · rw [hπ a ha]
    by_cases hba : b = a
    · subst hba
      rw [ite_eq_left rfl, one_apply_eq]
    · rw [ite_eq_right hba, one_apply_ne (Ne.symm hba)]

end Supp

section Root

variable {p : ℕ} {ζ : Kˣ}

theorem mat_spTorusSt (hζ : ζ ^ p = 1) (g : Fin n → Multiplicative (ZMod p)) :
    mat n K (spTorusSt hζ g) = diagonal (diagSpEntry fun i => zmodPowHom hζ (g i)) := by
  rw [spTorusSt_eq_diagSp, mat_diagSp]

@[expose] noncomputable def spRootSt (k : Fin n) : Multiplicative K →* StatedSp n K :=
  spRootSp k

theorem mat_spRootSt (k : Fin n) (c : Multiplicative K) :
    mat n K (spRootSt k c) =
      Matrix.transvection (Sum.inl k) (Sum.inr k) (Multiplicative.toAdd c) :=
  spRootGL_coe k c

theorem spRootSt_injective (k : Fin n) : Function.Injective (spRootSt (K := K) k) := by
  intro c c' h
  have e := congrArg (fun x => mat n K x (Sum.inl k) (Sum.inr k)) h
  simp only [mat_spRootSt, Matrix.transvection, Matrix.add_apply, Matrix.single_apply_same,
    one_apply_ne (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k), zero_add] at e
  exact Multiplicative.toAdd.injective e

theorem spRootSt_sq [CharP K 2] (k : Fin n) (c : Multiplicative K) : spRootSt k c ^ 2 = 1 := by
  rw [← map_pow]
  have : c ^ 2 = 1 := by
    rw [← ofAdd_toAdd c, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
  rw [this, map_one]

theorem spTorusSt_conj_spRootSt (hζ : ζ ^ p = 1) (k : Fin n) (g : Fin n → Multiplicative (ZMod p))
    (c : Multiplicative K) :
    spTorusSt hζ g * spRootSt k c * (spTorusSt hζ g)⁻¹ =
      spRootSt k (Multiplicative.ofAdd (((zmodPowHom hζ (g k) : Kˣ) : K) *
        Multiplicative.toAdd c * ((zmodPowHom hζ (g k) : Kˣ) : K))) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact diagGL_pairedUnits_conj_spRootGL _ k c

@[expose] noncomputable def spSwapSt [CharP K 2] (k : Fin n) : StatedSp n K :=
  spSwapSp k

theorem mat_spSwapSt [CharP K 2] (k : Fin n) :
    mat n K (spSwapSt k) = (pairSwap k)⁻¹.permMatrix K :=
  TauCeti.permutationGL_coe _

theorem spSwapSt_conj_spTorusSt [CharP K 2] (hζ : ζ ^ p = 1) (k : Fin n)
    (g : Fin n → Multiplicative (ZMod p)) :
    spSwapSt k * spTorusSt hζ g * (spSwapSt k)⁻¹ =
      spTorusSt hζ (Function.update g k (g k)⁻¹) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  show TauCeti.permutationGL (pairSwap k) * spTorusGL hζ g *
      (TauCeti.permutationGL (pairSwap k))⁻¹ = spTorusGL hζ (Function.update g k (g k)⁻¹)
  rw [spTorusGL_apply, spTorusGL_apply, permutationGL_pairSwap_conj, pairedUnits_comp_pairSwap]
  congr 2
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

theorem zmodPowHom_ofAdd_one (hζ : ζ ^ p = 1) :
    zmodPowHom hζ (Multiplicative.ofAdd (1 : ZMod p)) = ζ := by
  have := zmodPowHom_natCast hζ 1
  rwa [Nat.cast_one, pow_one] at this

theorem units_mul_self_ne_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζo : orderOf ζ = p) : ((ζ : K) * ζ) ≠ 1 := by
  intro h
  have h2 : ζ ^ 2 = 1 := Units.ext (by rw [sq, Units.val_mul, h, Units.val_one])
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hζo] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

end Root

section CaseOne

theorem ggStdSubEltData_of_eq_one [CharP K 2] (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {f : Fin n → Multiplicative (ZMod p)} {k₀ : Fin n} (hk₀ : f k₀ = 1) :
    GGStdSubEltData p (spTorusSt (n := n) hζ).range (spTorusSt hζ f) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set S₁ : Finset (Fin n) := Finset.univ.filter fun i => f i = 1 with hS₁
  set σ : Fin S₁.card → Fin n := fun j => S₁.orderEmbOfFin rfl j with hσdef
  have hσ : Function.Injective σ := (S₁.orderEmbOfFin rfl).injective
  have hσr : ∀ i, i ∈ Set.range σ ↔ f i = 1 := by
    intro i
    have h1 : Set.range σ = (S₁ : Set (Fin n)) := Finset.range_orderEmbOfFin S₁ rfl
    rw [h1, Finset.mem_coe, hS₁, Finset.mem_filter]
    simp
  set S : Set (Fin n ⊕ Fin n) := Set.range (Sum.map σ σ) with hSdef
  have hmemS : ∀ x : Fin n ⊕ Fin n, x ∈ S ↔ f (Sum.elim id id x) = 1 := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      rcases y with j | j <;> exact (hσr _).mp ⟨j, rfl⟩
    · intro h
      rcases x with i | i
      · obtain ⟨j, hj⟩ := (hσr i).mpr h
        exact ⟨Sum.inl j, by simp [hj]⟩
      · obtain ⟨j, hj⟩ := (hσr i).mpr h
        exact ⟨Sum.inr j, by simp [hj]⟩
  set α := diagSpEntry fun i => zmodPowHom hζ (f i) with hα
  have hmatf : mat n K (spTorusSt hζ f) = diagonal α := mat_spTorusSt hζ f
  have hα1 : ∀ x : Fin n ⊕ Fin n, α x = 1 ↔ f (Sum.elim id id x) = 1 := by
    intro x
    rcases x with i | i
    · simp only [hα, diagSpEntry_inl, Sum.elim_inl, id]
      rw [Units.val_eq_one, zmodPowHom_eq_one_iff hζ hζo]
    · simp only [hα, diagSpEntry_inr, Sum.elim_inr, id]
      rw [Units.val_eq_one, inv_eq_one, zmodPowHom_eq_one_iff hζ hζo]
  have hαS : ∀ x ∈ S, α x = 1 := fun x hx => (hα1 x).mpr ((hmemS x).mp hx)
  have hαSc : ∀ x ∉ S, α x ≠ 1 := fun x hx h => hx ((hmemS x).mpr ((hα1 x).mp h))
  have hlS : (Sum.inl k₀ : Fin n ⊕ Fin n) ∈ S := (hmemS _).mpr hk₀
  have hrS : (Sum.inr k₀ : Fin n ⊕ Fin n) ∈ S := (hmemS _).mpr hk₀
  have hplane : ∀ x ∉ S, Sum.elim id id x ≠ k₀ := fun x hx h =>
    hx ((hmemS x).mpr (by rw [h]; exact hk₀))
  have hcard : 1 ≤ S₁.card := Finset.card_pos.mpr ⟨k₀, by simp [hS₁, hk₀]⟩
  set g₀ : Fin n → Multiplicative (ZMod p) := Pi.mulSingle k₀ (Multiplicative.ofAdd 1)
    with hg₀
  set tb := spTorusSt (K := K) hζ g₀ with htb
  have hT : ∀ s ∈ (spTorusSt (n := n) hζ).range, ∀ u ∈ (spRootSt (K := K) k₀).range,
      s * u * s⁻¹ ∈ (spRootSt (K := K) k₀).range := by
    rintro _ ⟨g, rfl⟩ _ ⟨c, rfl⟩
    exact ⟨_, (spTorusSt_conj_spRootSt hζ k₀ g c).symm⟩
  have htbD : tb ∈ suppGroup S := by
    rw [mem_suppGroup, htb, mat_spTorusSt]
    refine isSupp_diagonal fun x hx => ?_
    rcases x with i | i
    · have hi : i ≠ k₀ := hplane _ hx
      simp [hg₀, Pi.mulSingle_eq_of_ne hi]
    · have hi : i ≠ k₀ := hplane _ hx
      simp [hg₀, Pi.mulSingle_eq_of_ne hi]
  have hroot : ∀ c, spRootSt (K := K) k₀ c ∈ suppGroup S := by
    intro c
    rw [mem_suppGroup, mat_spRootSt]
    exact isSupp_transvection hlS hrS _
  have hswap : spSwapSt (K := K) k₀ ∈ suppGroup S := by
    rw [mem_suppGroup, mat_spSwapSt]
    refine isSupp_permMatrix fun x hx => ?_
    have h1 : x ≠ Sum.inl k₀ := fun h => hx (h ▸ hlS)
    have h2 : x ≠ Sum.inr k₀ := fun h => hx (h ▸ hrS)
    show (Equiv.swap (Sum.inl k₀) (Sum.inr k₀))⁻¹ x = x
    rw [Equiv.Perm.inv_def, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hζ1 : zmodPowHom hζ (g₀ k₀) = ζ := by
    rw [hg₀, Pi.mulSingle_eq_same, zmodPowHom_ofAdd_one]
  refine ⟨suppGroup S, fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_mem_suppGroup hmatf hαS hg), fun c hc d hd =>
    conj_mem_suppGroup_of_commute hmatf hαS hαSc (Subgroup.mem_centralizer_singleton_iff.mp hc) hd,
    isQuasisimple_suppGroup_range hσ hK hcard, (spRootSt (K := K) k₀).range, ?_, ?_, ?_, hT,
    tb, htbD, ?_, ?_, ?_, ⟨spRootSt k₀ (Multiplicative.ofAdd 1), hroot _, ?_⟩,
    spSwapSt k₀, hswap, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact hroot c
  · intro h
    have hmem : spRootSt (K := K) k₀ (Multiplicative.ofAdd 1) ∈ (spRootSt (K := K) k₀).range :=
      ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one (spRootSt (K := K) k₀)] at hmem
    have := spRootSt_injective k₀ hmem
    exact one_ne_zero (congrArg Multiplicative.toAdd this)
  · rintro ⟨_, c, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow]
    exact spRootSt_sq k₀ c
  · rw [htb, ← map_pow]
    have : g₀ ^ p = 1 := by
      rw [hg₀, ← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        ofAdd_zero, Pi.mulSingle_one]
    rw [this, map_one]
  · rintro _ ⟨g, rfl⟩
    rw [htb, ← map_mul, ← map_mul, mul_comm]
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact hT tb ⟨g₀, rfl⟩ u
    · intro hu
      have := hT tb⁻¹ ⟨g₀⁻¹, by rw [map_inv]⟩ _ hu
      simpa [mul_assoc] using this
  · intro hcomm
    have h1 : tb * spRootSt k₀ (Multiplicative.ofAdd 1) * tb⁻¹ =
        spRootSt k₀ (Multiplicative.ofAdd 1) := by
      rw [hcomm, mul_inv_cancel_right]
    rw [htb, spTorusSt_conj_spRootSt, hζ1] at h1
    have h2 := congrArg Multiplicative.toAdd (spRootSt_injective k₀ h1)
    simp only [toAdd_ofAdd, mul_one] at h2
    exact units_mul_self_ne_one hp hp2 hζo h2
  · rw [htb, spSwapSt_conj_spTorusSt, ← map_inv]
    congr 1
    funext j
    by_cases hj : j = k₀
    · subst hj
      simp [hg₀]
    · simp [hg₀, Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  · rintro _ ⟨g, rfl⟩
    rw [spSwapSt_conj_spTorusSt, ← map_inv, ← map_mul]
    have hg : g⁻¹ * Function.update g k₀ (g k₀)⁻¹ = Pi.mulSingle k₀ ((g k₀)⁻¹ * (g k₀)⁻¹) := by
      funext j
      by_cases hj : j = k₀
      · subst hj
        simp
      · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]
    rw [hg]
    refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd ((g k₀)⁻¹ * (g k₀)⁻¹)).val : ℤ),
      ?_⟩
    rw [zpow_natCast, htb, hg₀, spTorusSt_mulSingle_pow]

end CaseOne


end StdSubSp

end CFSG.StandardType

end
