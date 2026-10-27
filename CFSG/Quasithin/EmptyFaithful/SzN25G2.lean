module

public import CFSG.Quasithin.EmptyFaithful.SzN24Top
public import CFSG.Quasithin.EmptyFaithful.SzN21G2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.SteinbergBS CFSG.Quasithin.SBd8
open scoped Pointwise

namespace SzN25

section Generic

theorem mem_normalizer_of_conj_le {G : Type} [Group G] [Finite G] {U : Subgroup G} {y : G}
    (h : ∀ u ∈ U, y * u * y⁻¹ ∈ U) : y ∈ Subgroup.normalizer (U : Set G) := by
  let f : ↥U → ↥U := fun u => ⟨y * u * y⁻¹, h u u.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => h g hg, fun hg => ?_⟩
  obtain ⟨w, hw⟩ := hsurj ⟨y * g * y⁻¹, hg⟩
  have := congrArg Subtype.val hw
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact w.2

end Generic

section Torus

variable {F : Type} [Field F]

theorem coe_torusG2 (p : Fˣ × Fˣ) :
    ((SzN21.torusG2 F p : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
      torusElt Tag.G2 F ⟨0, by decide⟩ p.1 * torusElt Tag.G2 F ⟨1, by decide⟩ p.2 := by
  change (List.ofFn fun i : Fin 2 => torusElt Tag.G2 F i (![p.1, p.2] i)).prod = _
  simp [List.ofFn_succ]
  rfl

theorem entrywise_torusG2 (σ : F ≃+* F) (p : Fˣ × Fˣ) :
    Units.map (entrywiseHom σ.toRingHom)
        ((SzN21.torusG2 F p : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
      ((SzN21.torusG2 F (Units.map σ.toRingHom.toMonoidHom p.1,
        Units.map σ.toRingHom.toMonoidHom p.2) : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) := by
  rw [coe_torusG2, coe_torusG2, map_mul, entrywise_torusElt, entrywise_torusElt]

theorem torusG2_mem_torusGroup (p : Fˣ × Fˣ) :
    ((SzN21.torusG2 F p : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) ∈ torusGroup Tag.G2 F :=
  (torusCoordHom Tag.G2 F (SzN21.pairHom Fˣ p)).2

end Torus

section G2

variable
  {F : Type} [Field F]

theorem g2_autRigid [Finite F] [CharP F 2] {e : ℕ} (hF : Nat.card F = 2 ^ e) (he : 2 ≤ e)
    {Ŝ : Subgroup ↥(adjointGroup Tag.G2 F)} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (α : ↥(adjointGroup Tag.G2 F) ≃* ↥(adjointGroup Tag.G2 F)) (h1 : ∀ g ∈ Ŝ, α g ∈ Ŝ)
    (h2 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set ↥(adjointGroup Tag.G2 F)), α b * b⁻¹ ∈ Ŝ) :
    ∃ x : ↥(adjointGroup Tag.G2 F), ∀ m, α m = x * m * x⁻¹ := by
  classical
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form he F
      hF).1 α
  let E : MulAut ↥(adjointGroup Tag.G2 F) := exactNormalAut Tag.G2 F 1 σ 0
  have hE : ∀ h : ↥(adjointGroup Tag.G2 F),
      ((E h : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 F) := by
    intro h
    change (exactNormalAut Tag.G2 F 1 σ 0 h : ModGL Tag.G2 F) = _
    rw [coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]
  have hαE : ∀ h, α h = g * E h * g⁻¹ := fun h => Subtype.ext (by
    have := hgσ h
    simp only at this
    rw [this, Subgroup.coe_mul, Subgroup.coe_mul, hE, Subgroup.coe_inv])
  let U : Subgroup ↥(adjointGroup Tag.G2 F) :=
    (posUnipotent Tag.G2 F).subgroupOf (adjointGroup Tag.G2 F)
  have hU : IsSylowTwoOf U ⊤ := g2Std_isSylowTwoOf
  obtain ⟨x, -, hx⟩ := B6.isSylowTwoOf_exists_conj hU hŜ
  have hmem : ∀ s, s ∈ Ŝ ↔ x⁻¹ * s * x ∈ U := by
    intro s
    rw [hx]
    constructor
    · rintro ⟨u, hu, rfl⟩
      show x⁻¹ * (x * u * x⁻¹) * x ∈ U
      rw [show x⁻¹ * (x * u * x⁻¹) * x = u by group]
      exact hu
    · intro hs
      refine ⟨x⁻¹ * s * x, hs, ?_⟩
      show x * (x⁻¹ * s * x) * x⁻¹ = s
      group
  have hEU : U.map E.toMonoidHom = U := (exactNormalAut_mem (K := F) (τ := Tag.G2) 1 σ 0).1
  have hEUsurj : ∀ u' ∈ U, ∃ u ∈ U, E u = u' := fun u' hu' => by
    rw [← hEU] at hu'
    obtain ⟨u, hu, h⟩ := hu'
    exact ⟨u, hu, h⟩
  set y : ↥(adjointGroup Tag.G2 F) := x⁻¹ * g * E x with hy
  have hy_conj : ∀ u' ∈ U, y * u' * y⁻¹ ∈ U := by
    intro u' hu'
    obtain ⟨u, hu, rfl⟩ := hEUsurj u' hu'
    have h3 : x * u * x⁻¹ ∈ Ŝ := (hmem _).mpr (by
      rw [show x⁻¹ * (x * u * x⁻¹) * x = u by group]
      exact hu)
    have h4 := (hmem _).mp (h1 _ h3)
    rw [hαE, map_mul, map_mul, map_inv] at h4
    have e : x⁻¹ * (g * (E x * E u * (E x)⁻¹) * g⁻¹) * x = y * E u * y⁻¹ := by
      rw [hy]
      group
    rw [e] at h4
    exact h4
  have hyB : y ∈ Subgroup.normalizer (U : Set ↥(adjointGroup Tag.G2 F)) :=
    mem_normalizer_of_conj_le hy_conj
  have hyB' : (y : ModGL Tag.G2 F) ∈ borelGroup Tag.G2 F := by
    rw [g2Std_normalizer_eq] at hyB
    exact Subgroup.mem_subgroupOf.mp hyB
  obtain ⟨hcomm, -, hHN, -, -, hUH, -, huniq, -, -, -, -⟩ := triangular_borel_structure.{0, 0} Tag.G2 F
  obtain ⟨v, hv, t, ht, hvt⟩ : ∃ v ∈ posUnipotent Tag.G2 F, ∃ t ∈ torusGroup Tag.G2 F,
      v * t = (y : ModGL Tag.G2 F) := by
    have : (y : ModGL Tag.G2 F) ∈ (posUnipotent Tag.G2 F : Set (ModGL Tag.G2 F)) *
        (torusGroup Tag.G2 F : Set (ModGL Tag.G2 F)) := by
      rw [← hUH]
      exact hyB'
    obtain ⟨v, hv, t, ht, h⟩ := Set.mem_mul.mp this
    exact ⟨v, hv, t, ht, h⟩
  have hσ1 : σ = 1 := by
    ext a
    by_cases ha : a = 0
    · simp [ha]
    let d : ↥(adjointGroup Tag.G2 F) := SzN21.torusG2 F (Units.mk0 a ha, 1)
    have hdN : d ∈ Subgroup.normalizer (U : Set ↥(adjointGroup Tag.G2 F)) :=
      SzN21.torusG2_mem_normalizer _
    have hdN' : x * d * x⁻¹ ∈ Subgroup.normalizer (Ŝ : Set ↥(adjointGroup Tag.G2 F)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      rw [hmem, hmem]
      have h1' := Subgroup.mem_normalizer_iff.mp hdN (x⁻¹ * s * x)
      have e : x⁻¹ * (x * d * x⁻¹ * s * (x * d * x⁻¹)⁻¹) * x = d * (x⁻¹ * s * x) * d⁻¹ := by
        group
      rw [e]
      exact h1'
    have h5 := (hmem _).mp (h2 _ hdN')
    rw [hαE, map_mul, map_mul, map_inv] at h5
    have h6 : y * E d * y⁻¹ * d⁻¹ ∈ U := by
      have e : x⁻¹ * (g * (E x * E d * (E x)⁻¹) * g⁻¹ * (x * d * x⁻¹)⁻¹) * x =
          y * E d * y⁻¹ * d⁻¹ := by
        rw [hy]
        group
      rw [← e]
      exact h5
    have hdT : (d : ModGL Tag.G2 F) ∈ torusGroup Tag.G2 F := torusG2_mem_torusGroup _
    have hEd : ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) ∈ torusGroup Tag.G2 F := by
      rw [hE]
      exact entrywise_mem_torusGroup hdT
    have h8 := Subgroup.mem_subgroupOf.mp h6
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h8
    rw [← hvt, mul_inv_rev] at h8
    have hct : t * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * t⁻¹ =
        ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) := by
      rw [hcomm t ht _ hEd, mul_inv_cancel_right]
    have h9 : v * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * v⁻¹ *
        ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹ ∈ posUnipotent Tag.G2 F := by
      have e : v * t * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * (t⁻¹ * v⁻¹) *
          ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹ =
          v * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * v⁻¹ *
            ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹ := by
        calc v * t * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * (t⁻¹ * v⁻¹) *
              ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹
            = v * (t * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * t⁻¹) * v⁻¹ *
                ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹ := by group
          _ = _ := by rw [hct]
      rw [← e]
      exact h8
    have hdN2 : ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * v *
        ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹ ∈ posUnipotent Tag.G2 F :=
      (Subgroup.mem_normalizer_iff.mp (hHN hdT) v).mp hv
    have hw : v⁻¹ * (v * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * v⁻¹ *
        ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹) *
        (((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * v *
          ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹) ∈ posUnipotent Tag.G2 F :=
      mul_mem (mul_mem (inv_mem hv) h9) hdN2
    have hEq : (1 : ModGL Tag.G2 F) * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
        (v⁻¹ * (v * ((E d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * v⁻¹ *
          ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹) *
          (((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) * v *
            ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F)⁻¹)) *
          ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) := by group
    obtain ⟨-, hEdd⟩ := huniq _ hEd _ hdT 1 (one_mem _) _ hw hEq
    have hEdM : E d = d := Subtype.ext hEdd
    have hmap : Units.map (entrywiseHom σ.toRingHom) ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
        ((d : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) := by
      rw [← hE, hEdM]
    have hmap' := hmap
    change Units.map (entrywiseHom σ.toRingHom)
        ((SzN21.torusG2 F (Units.mk0 a ha, 1) : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
      ((SzN21.torusG2 F (Units.mk0 a ha, 1) : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) at hmap'
    rw [entrywise_torusG2] at hmap'
    have hinj := SzN21.torusG2_injective (Subtype.ext hmap')
    have h10 := congrArg (fun q : Fˣ × Fˣ => ((q.1 : Fˣ) : F)) hinj
    simpa using h10
  have hE1 : E = 1 := by
    show exactNormalAut Tag.G2 F 1 σ 0 = 1
    rw [hσ1]
    exact exactNormalAut_one_one_zero
  refine ⟨g, fun m => ?_⟩
  rw [hαE, hE1]
  simp

theorem krig_of_g2 (hG2 : FactG2Cayley) {Ω : Type} [Group Ω] {K : Subgroup Ω} [Finite F] {e : ℕ}
    (hF : Nat.card F = 2 ^ e) (he : 2 ≤ e) (iso : ↥K ≃* ↥(CFSG.Open.quasithinG2 F)) :
    SzN22.KRig K := by
  have hcp : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have h4 : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one (K := F) h4
  have hZ : Subgroup.center ↥(CFSG.Open.quasithinG2 F) = ⊥ := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
    exact CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  have hG : IsG2 2 e ↥(CFSG.Open.quasithinG2 F) :=
    IsG2.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      (hG2 F e he hF)
  have hX : IsG2 2 e ↥K := IsG2.of_mulEquiv iso.symm hG
  obtain ⟨-, F', hFf, hFfin, hFcp, hF', ⟨ψ₀⟩⟩ := exists_mulEquiv_G2_model hX
  have : Finite (ModGL Tag.G2 F') := finite_modGL
  exact SzN24.krig_of_autRigid ψ₀ (fun Ŝ α hŜ h1 h2 _ _ => g2_autRigid hF' he hŜ α h1 h2)

theorem lieRigidG2_holds (hG2 : FactG2Cayley) : SzN24.LieRigidG2 := by
  intro Ω _ _ K e he ⟨F, _, _, hF, ⟨iso⟩⟩
  exact krig_of_g2 hG2 hF (by omega) iso

end G2


end SzN25

end CFSG.Quasithin
