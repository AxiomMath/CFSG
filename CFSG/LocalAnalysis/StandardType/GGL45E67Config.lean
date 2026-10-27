module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType

@[expose] def GGL45E67Config {R : Type} [Group R] (f : MulAut R) (r : ℕ) : Prop :=
  ∃ (a b : Fin r → R) (Q : Subgroup R),
    (∀ i, a i ^ 2 = 1) ∧ (∀ i, b i ^ 2 = 1) ∧ (∀ i, orderOf (a i * b i) = 3) ∧
    (∀ i, f (a i) = a i) ∧ (∀ i, f (b i) = b i) ∧
    (∀ i j, j < i → Commute (a i * b i) (a j) ∧ Commute (a i * b i) (b j)) ∧
    Nat.card (Subgroup.closure (Set.range fun i => a i * b i)) = 3 ^ r ∧
    IsPGroup 2 Q ∧ Q ≠ ⊥ ∧ (∀ g ∈ Q, f g ∈ Q) ∧
      ∀ i, a i * b i ∈ Subgroup.normalizer (Q : Set R)

theorem ggL45E67Config_of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {f : MulAut R} {f' : MulAut R'} (hf : ∀ x, f' (e x) = e (f x)) {r : ℕ}
    (h : GGL45E67Config f r) : GGL45E67Config f' r := by
  obtain ⟨a, b, Q, ha2, hb2, hab3, hfa, hfb, hcomm, hgen, hQ2, hQne, hQstab, hQnorm⟩ := h
  refine ⟨fun i => e (a i), fun i => e (b i), Q.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← map_pow, ha2, map_one]
  · intro i
    rw [← map_pow, hb2, map_one]
  · intro i
    rw [← map_mul, MulEquiv.orderOf_eq, hab3 i]
  · intro i
    rw [hf, hfa i]
  · intro i
    rw [hf, hfb i]
  · intro i j hij
    exact ⟨by
        simpa only [map_mul, MulEquiv.coe_toMonoidHom] using ((hcomm i j hij).1).map e.toMonoidHom,
      by
        simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
          ((hcomm i j hij).2).map e.toMonoidHom⟩
  · have hmap : (Subgroup.closure (Set.range fun i => a i * b i)).map e.toMonoidHom =
        Subgroup.closure (Set.range fun i => e (a i) * e (b i)) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simp only [map_mul, MulEquiv.coe_toMonoidHom]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨a i * b i, ⟨i, rfl⟩, by simp only [map_mul, MulEquiv.coe_toMonoidHom]⟩
    rw [← hmap, Subgroup.card_map_of_injective e.injective, hgen]
  · exact hQ2.map e.toMonoidHom
  · intro hbot
    apply hQne
    rw [eq_bot_iff]
    intro y hy
    have hmem : e y ∈ Q.map e.toMonoidHom := ⟨y, hy, rfl⟩
    rw [hbot] at hmem
    exact e.injective (by simpa using hmem)
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨f y, hQstab y hy, (hf y).symm⟩
  · intro i
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨y, hy, hhy⟩ := Subgroup.mem_map.mp hh
      have hhy' : e y = h := by simpa only [MulEquiv.coe_toMonoidHom] using hhy
      refine ⟨a i * b i * y * (a i * b i)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hQnorm i) y).1 hy, ?_⟩
      simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, hhy']
    · intro hh
      obtain ⟨y, hy, hhy⟩ := Subgroup.mem_map.mp hh
      have hhy' : e y = e (a i) * e (b i) * h * (e (a i) * e (b i))⁻¹ := by
        simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using hhy
      let w : R := e.symm h
      have hw : e w = h := e.apply_symm_apply h
      have h2 : e ((a i * b i) * w * (a i * b i)⁻¹) = e y := by
        rw [hhy']
        simp only [map_mul, map_inv, hw]
      have h3 : e ((a i * b i) * w * (a i * b i)⁻¹) ∈ Q.map e.toMonoidHom :=
        ⟨y, hy, by simpa only [MulEquiv.coe_toMonoidHom] using h2.symm⟩
      obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp h3
      have hze' : e z = e ((a i * b i) * w * (a i * b i)⁻¹) := by
        simpa only [MulEquiv.coe_toMonoidHom] using hze
      have hz' : z = (a i * b i) * w * (a i * b i)⁻¹ := e.injective hze'
      rw [hz'] at hz
      refine ⟨w, (Subgroup.mem_normalizer_iff.mp (hQnorm i) w).2 hz, ?_⟩
      simpa only [MulEquiv.coe_toMonoidHom] using hw

theorem ggL45E67Config_conj {R : Type} [Group R] {f : MulAut R} {r : ℕ} (u : MulAut R)
    (h : GGL45E67Config f r) : GGL45E67Config (u * f * u⁻¹) r :=
  ggL45E67Config_of_mulEquiv u (fun x => by simp [MulAut.mul_apply]) h

theorem card_closure_range_basis_eq_three_pow {R : Type} [Group R] {r : ℕ}
    (φ : Multiplicative (Fin r → ZMod 3) →* R) (hφ : Function.Injective φ) :
    Nat.card (Subgroup.closure (Set.range fun i => φ (Multiplicative.ofAdd (Pi.single i 1)))) =
      3 ^ r := by
  let gs : Fin r → (Fin r → ZMod 3) := fun i => Pi.single i 1
  let g : Fin r → Multiplicative (Fin r → ZMod 3) := fun i => Multiplicative.ofAdd (gs i)
  have htop : Subgroup.closure (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hv : Multiplicative.toAdd x =
        ∑ i : Fin r, (Multiplicative.toAdd x i).val • gs i := by
      have h1 : Multiplicative.toAdd x =
          ∑ i : Fin r, Pi.single i (Multiplicative.toAdd x i) := by
        ext j
        rw [Finset.sum_apply]
        exact (Fintype.sum_pi_single j (fun i => Multiplicative.toAdd x i)).symm
      conv_lhs => rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext j
      by_cases hij : j = i
      · subst hij
        simp only [gs, Pi.single_eq_same, Pi.smul_apply]
        rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      · simp [gs, Pi.single_eq_of_ne hij]
    have hx : x = ∏ i : Fin r,
        (g i) ^ (Multiplicative.toAdd x i).val := by
      calc x = Multiplicative.ofAdd (Multiplicative.toAdd x) := rfl
        _ = Multiplicative.ofAdd (∑ i : Fin r, (Multiplicative.toAdd x i).val • gs i) :=
              congrArg Multiplicative.ofAdd hv
        _ = ∏ i : Fin r,
              Multiplicative.ofAdd ((Multiplicative.toAdd x i).val • gs i) := by rw [ofAdd_sum]
        _ = ∏ i : Fin r,
              (Multiplicative.ofAdd (gs i)) ^ (Multiplicative.toAdd x i).val :=
              Finset.prod_congr rfl fun i _ => ofAdd_nsmul _ _
    rw [hx]
    refine Subgroup.prod_mem _ fun i _ => ?_
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (show g i ∈ Set.range g from ⟨i, rfl⟩))
      ((Multiplicative.toAdd x i).val)
  have hcl : Subgroup.closure (Set.range fun i =>
        φ (Multiplicative.ofAdd (Pi.single i 1))) = φ.range := by
    have hrange : Set.range (fun i => φ (g i)) = φ '' Set.range g := by
      simpa only [Function.comp_def] using Set.range_comp (g := φ) (f := g)
    change Subgroup.closure (Set.range fun i => φ (g i)) = φ.range
    rw [hrange, ← MonoidHom.map_closure φ (Set.range g), htop, Subgroup.map_top]
  rw [hcl, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

end CFSG.StandardType
