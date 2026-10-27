module

public import CFSG.Quasithin.Vol2.Ch6StatementsSec2
public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] {H U : Subgroup G} {A : Type} [AddCommGroup A]
  [Module (ZMod 2) A] {B : LinearMap.BilinForm (ZMod 2) A}
  {β : ↥U →* Multiplicative A} {ρ : ↥H →* (A ≃ₗ[ZMod 2] A)}

@[expose] def conjU_ch618 (x : ↥(Subgroup.normalizer (U : Set G))) : ↥U →* ↥U where
  toFun u := ⟨x * u * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp x.2 u).mp u.2⟩
  map_one' := by ext; simp
  map_mul' u u' := by ext; simp only [Subgroup.coe_mul]; group

theorem conjU_ch618_apply (x : ↥(Subgroup.normalizer (U : Set G))) (u : ↥U) :
    ((conjU_ch618 x u : ↥U) : G) = x * u * (x : G)⁻¹ := rfl

theorem ker_le_ch618 (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (x : ↥(Subgroup.normalizer (U : Set G))) : β.ker ≤ (β.comp (conjU_ch618 x)).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have huZ : (u : G) ∈ centerOf U := (hR.2.1 u).mp hu
  have hxu : x * (u : G) * (x : G)⁻¹ ∈ centerOf U :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centerOf U x.2) u).mp huZ
  exact (hR.2.1 _).mpr hxu

@[expose] noncomputable def realConjMul_ch618
    (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (x : ↥(Subgroup.normalizer (U : Set G))) : Multiplicative A →* Multiplicative A :=
  β.liftOfSurjective hR.1 ⟨β.comp (conjU_ch618 x), ker_le_ch618 hR x⟩

theorem realConjMul_ch618_apply (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (x : ↥(Subgroup.normalizer (U : Set G))) (u : ↥U) :
    realConjMul_ch618 hR x (β u) = β (conjU_ch618 x u) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u

theorem realConjMul_ch618_comp (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (x y : ↥(Subgroup.normalizer (U : Set G))) (a : Multiplicative A) :
    realConjMul_ch618 hR x (realConjMul_ch618 hR y a) = realConjMul_ch618 hR (x * y) a := by
  obtain ⟨u, rfl⟩ := hR.1 a
  rw [realConjMul_ch618_apply, realConjMul_ch618_apply, realConjMul_ch618_apply]
  congr 1
  ext
  simp only [conjU_ch618_apply, Subgroup.coe_mul]
  group

theorem realConjMul_ch618_one (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (a : Multiplicative A) : realConjMul_ch618 hR 1 a = a := by
  obtain ⟨u, rfl⟩ := hR.1 a
  rw [realConjMul_ch618_apply]
  congr 1
  ext
  simp [conjU_ch618_apply]

@[expose] noncomputable def realRho_ch618
    (hR : IsSymplecticRealization H U (centerOf U) A B β ρ) :
    ↥(Subgroup.normalizer (U : Set G)) →* (A ≃ₗ[ZMod 2] A) where
  toFun x :=
    { toFun := fun a => Multiplicative.toAdd (realConjMul_ch618 hR x (Multiplicative.ofAdd a))
      invFun := fun a => Multiplicative.toAdd (realConjMul_ch618 hR x⁻¹ (Multiplicative.ofAdd a))
      map_add' := fun a b => by
        rw [ofAdd_add, map_mul, toAdd_mul]
      map_smul' := fun c a => by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · simp only [zero_smul, ofAdd_zero, map_one, toAdd_one, RingHom.id_apply]
        · simp only [one_smul, RingHom.id_apply]
      left_inv := fun a => by
        simp only [ofAdd_toAdd, realConjMul_ch618_comp, inv_mul_cancel, realConjMul_ch618_one,
          toAdd_ofAdd]
      right_inv := fun a => by
        simp only [ofAdd_toAdd, realConjMul_ch618_comp, mul_inv_cancel, realConjMul_ch618_one,
          toAdd_ofAdd] }
  map_one' := LinearEquiv.ext fun a => by
    show Multiplicative.toAdd (realConjMul_ch618 hR 1 (Multiplicative.ofAdd a)) = a
    rw [realConjMul_ch618_one, toAdd_ofAdd]
  map_mul' x y := LinearEquiv.ext fun a => by
    show Multiplicative.toAdd (realConjMul_ch618 hR (x * y) (Multiplicative.ofAdd a)) =
      Multiplicative.toAdd (realConjMul_ch618 hR x (Multiplicative.ofAdd
        (Multiplicative.toAdd (realConjMul_ch618 hR y (Multiplicative.ofAdd a)))))
    rw [ofAdd_toAdd, realConjMul_ch618_comp]

theorem realRho_ch618_apply (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (x : ↥(Subgroup.normalizer (U : Set G))) (u : ↥U) :
    realRho_ch618 hR x (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β (conjU_ch618 x u)) := by
  show Multiplicative.toAdd (realConjMul_ch618 hR x (Multiplicative.ofAdd
    (Multiplicative.toAdd (β u)))) = _
  rw [ofAdd_toAdd, realConjMul_ch618_apply]

open scoped Classical in
@[expose] noncomputable def realHat_ch618 [Finite A]
    (hR : IsSymplecticRealization H U (centerOf U) A B β ρ) : HatModelU U where
  V := A
  π g := if hg : g ∈ U then Multiplicative.toAdd (β ⟨g, hg⟩) else 0
  B := B
  ρ := realRho_ch618 hR
  π_mul a ha b hb := by
    simp only [ha, hb, U.mul_mem ha hb, ↓reduceDIte]
    rw [← toAdd_mul, ← map_mul]
    rfl
  π_surj v := by
    obtain ⟨u, hu⟩ := hR.1 (Multiplicative.ofAdd v)
    exact ⟨u, u.2, by simp only [u.2, ↓reduceDIte, Subtype.coe_eta, hu, toAdd_ofAdd]⟩
  π_eq_iff a ha b hb := by
    simp only [ha, hb, ↓reduceDIte]
    rw [Multiplicative.toAdd.injective.eq_iff]
    have key := hR.2.1 (⟨a, ha⟩⁻¹ * ⟨b, hb⟩)
    rw [map_mul, map_inv, inv_mul_eq_one] at key
    simpa [eq_comm] using key
  B_spec a ha b hb := by
    simp only [ha, hb, ↓reduceDIte]
    exact not_iff_not.mp (hR.2.2.2 ⟨a, ha⟩ ⟨b, hb⟩)
  ρ_π x u hu := by
    have hxu : (x : G) * u * (x : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp x.2 u).mp hu
    simp only [hu, hxu, ↓reduceDIte]
    exact realRho_ch618_apply hR x ⟨u, hu⟩

theorem realRho_ch618_of_mem (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (hHN : H ≤ Subgroup.normalizer (U : Set G)) (x : ↥H) :
    realRho_ch618 hR ⟨(x : G), hHN x.2⟩ = ρ x := by
  refine LinearEquiv.ext fun a => ?_
  obtain ⟨u, hu⟩ := hR.1 (Multiplicative.ofAdd a)
  have ha : a = Multiplicative.toAdd (β u) := by rw [hu, toAdd_ofAdd]
  rw [ha, realRho_ch618_apply]
  exact hR.2.2.1 x u (conjU_ch618 (U := U) ⟨(x : G), hHN x.2⟩ u) rfl

theorem realHat_pi_ch618 [Finite A] (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    {g : G} (hg : g ∈ U) : (realHat_ch618 hR).π g = Multiplicative.toAdd (β ⟨g, hg⟩) := by
  exact dite_eq_left hg

theorem realHat_img_ch618 [Finite A] (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (hHN : H ≤ Subgroup.normalizer (U : Set G)) {K : Subgroup G} (hK : K ≤ H) :
    (realHat_ch618 hR).img K = (K.subgroupOf H).map ρ := by
  ext γ
  simp only [HatModelU.img, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hxK, rfl⟩
    exact ⟨⟨x, hK hxK⟩, hxK, (realRho_ch618_of_mem hR hHN ⟨x, hK hxK⟩).symm⟩
  · rintro ⟨x, hxK, rfl⟩
    exact ⟨⟨x, hHN x.2⟩, hxK, realRho_ch618_of_mem hR hHN x⟩

theorem realHat_img_self_ch618 [Finite A] (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    (hHN : H ≤ Subgroup.normalizer (U : Set G)) : (realHat_ch618 hR).img H = ρ.range := by
  rw [realHat_img_ch618 hR hHN le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]

theorem realHat_hat_ch618 [Finite A] (hR : IsSymplecticRealization H U (centerOf U) A B β ρ)
    {E : Subgroup G} (Wsp : Submodule (ZMod 2) A)
    (hW : ∀ a : A, a ∈ Wsp ↔ ∃ e : ↥U, (e : G) ∈ E ∧ Multiplicative.toAdd (β e) = a) :
    (realHat_ch618 hR).hat E = Wsp := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, ⟨hgE, hgU⟩, rfl⟩
    rw [realHat_pi_ch618 hR hgU]
    exact (hW _).mpr ⟨⟨g, hgU⟩, hgE, rfl⟩
  · intro a ha
    obtain ⟨e, heE, rfl⟩ := (hW a).mp ha
    apply Submodule.subset_span
    exact ⟨e, ⟨heE, e.2⟩, realHat_pi_ch618 hR e.2⟩

end CFSG.Quasithin.H13
