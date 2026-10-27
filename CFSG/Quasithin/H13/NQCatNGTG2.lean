module

public import CFSG.Quasithin.H13.NQCatG2RadFacts
public import CFSG.Quasithin.H13.NQCatNGTSwap
public import CFSG.Quasithin.Background.SmithB42G2Id

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique.Vol2Native.L239.Lie
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

theorem card_centerOf_pCoreOf_map {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    Nat.card (centerOf (pCoreOf 2 (perfectCore (H.map f)))) =
      Nat.card (centerOf (pCoreOf 2 (perfectCore H))) := by
  rw [← map_perfectCore f H, G24X3.pCoreOf_map_of_inj f hf, ← G2Rad.map_centerOf hf,
    Subgroup.card_map_of_injective hf]

theorem no_swap_g2
    {G : Type} [Group G] [Finite G] {X : Subgroup G} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥X ≃* ↥(CFSG.Open.quasithinG2 F))
    {S M₀ M₁ : Subgroup G} (hS : IsSylowTwoOf S X)
    (hM₀ : S ≤ M₀ ∧ M₀ < X ∧ ∀ M' : Subgroup G, M₀ ≤ M' → M' < X → M' = M₀)
    (hM₁ : S ≤ M₁ ∧ M₁ < X ∧ ∀ M' : Subgroup G, M₁ ≤ M' → M' < X → M' = M₁)
    (hne : M₀ ≠ M₁) (φ : G ≃* G) (hφ : M₀.map φ.toMonoidHom = M₁) : False := by
  classical
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  let e₀ : ↥(CFSG.Open.quasithinG2 F) ≃* ↥(Explicit.cayleyGroup F) :=
    MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup
  have hG : IsG2 2 n ↥X :=
    IsG2.of_mulEquiv (e.trans e₀).symm (B42G2Id.chevalleyExceptionalModel_cayleyGroup hF hn)
  obtain ⟨-, K, _, _, _, hK, ⟨θ⟩⟩ := exists_mulEquiv_G2_model hG
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hIφ : Nat.card (centerOf (pCoreOf 2 (perfectCore M₁))) =
      Nat.card (centerOf (pCoreOf 2 (perfectCore M₀))) := by
    rw [← hφ]
    exact card_centerOf_pCoreOf_map φ.toMonoidHom φ.injective M₀
  set U₀ := (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) with hU₀def
  have hU₀ : IsSylowTwoOf U₀ ⊤ := isSylowTwoOf_subgroupOf_top
    (isSylowTwoOf_iff_isSylowOf.2 (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  have hR := G2_residualOvergroupsAt (K := K)
  have hSX : IsSylowTwoOf (S.subgroupOf X) ⊤ := Setup.Layer.isSylowTwoOf_subgroupOf_top' hS
  have hS' : IsSylowTwoOf ((S.subgroupOf X).map θ.toMonoidHom) ⊤ :=
    B113Lie.isSylowTwoOf_map_top θ hSX
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hU₀ hS'
  have hR' := hR.map (MulAut.conj c)
  have hcS : U₀.map (MulAut.conj c).toMonoidHom = (S.subgroupOf X).map θ.toMonoidHom := hc.symm
  rw [hcS] at hR'
  have hpre : ∀ M : Subgroup G, S ≤ M → M < X →
      (∀ M' : Subgroup G, M ≤ M' → M' < X → M' = M) →
      ∃ k : Fin 2, (M.subgroupOf X).map θ.toMonoidHom =
        ((parabolicSubgroup Tag.G2 K {g2Index k}).subgroupOf (adjointGroup Tag.G2 K)).map
          (MulAut.conj c).toMonoidHom := by
    intro M hSM hMX hmax
    have hcov := subgroupOf_covBy_top hMX hmax
    have hcov' : (M.subgroupOf X).map θ.toMonoidHom ⋖ ⊤ := by
      have := (apply_covBy_apply_iff (MulEquiv.mapSubgroup θ)).2 hcov
      have h2 : (⊤ : Subgroup X).map θ.toMonoidHom = ⊤ :=
        Subgroup.map_top_of_surjective θ.toMonoidHom fun y => ⟨θ.symm y, θ.apply_symm_apply y⟩
      change (M.subgroupOf X).map θ.toMonoidHom ⋖ (⊤ : Subgroup X).map θ.toMonoidHom at this
      rwa [h2] at this
    have hle : (S.subgroupOf X).map θ.toMonoidHom ≤ (M.subgroupOf X).map θ.toMonoidHom :=
      Subgroup.map_mono fun x hx => hSM hx
    exact (hR'.2.2.1 _ hle).1 hcov'
  have hval : ∀ (M : Subgroup G) (k : Fin 2), M ≤ X →
      (M.subgroupOf X).map θ.toMonoidHom =
        ((parabolicSubgroup Tag.G2 K {g2Index k}).subgroupOf (adjointGroup Tag.G2 K)).map
          (MulAut.conj c).toMonoidHom →
      Nat.card (centerOf (pCoreOf 2 (perfectCore M))) =
        Nat.card (centerOf (parabolicRadical Tag.G2 K {g2Index k})) := by
    intro M k hMX hMk
    let ι : ↥X →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp
      ((MulAut.conj c⁻¹).toMonoidHom.comp θ.toMonoidHom)
    have hι : Function.Injective ι :=
      (adjointGroup Tag.G2 K).subtype_injective.comp ((MulAut.conj c⁻¹).injective.comp
        θ.injective)
    have hMι : (M.subgroupOf X).map ι = parabolicSubgroup Tag.G2 K {g2Index k} := by
      have h1 : (M.subgroupOf X).map ι = (((M.subgroupOf X).map θ.toMonoidHom).map
          (MulAut.conj c⁻¹).toMonoidHom).map (adjointGroup Tag.G2 K).subtype := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      have h2 : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
          MonoidHom.id ↥(adjointGroup Tag.G2 K) := by
        ext x : 1
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
      have h3 : (((parabolicSubgroup Tag.G2 K {g2Index k}).subgroupOf
          (adjointGroup Tag.G2 K)).map (MulAut.conj c).toMonoidHom).map
            (MulAut.conj c⁻¹).toMonoidHom =
          (parabolicSubgroup Tag.G2 K {g2Index k}).subgroupOf (adjointGroup Tag.G2 K) := by
        rw [Subgroup.map_map, h2, Subgroup.map_id]
      rw [h1, hMk, h3, Subgroup.map_subgroupOf_eq_of_le (parabolicSubgroup_le_adjointGroup _ _ _)]
    have hMeq : M = (M.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hMX).symm
    rw [hMeq, card_centerOf_pCoreOf_map X.subtype X.subtype_injective,
      ← card_centerOf_pCoreOf_map ι hι, hMι,
      G2Rad.pCoreOf_perfectCore_parabolic hK hn (g2Index k)]
  obtain ⟨k₀, hk₀⟩ := hpre M₀ hM₀.1 hM₀.2.1 hM₀.2.2
  obtain ⟨k₁, hk₁⟩ := hpre M₁ hM₁.1 hM₁.2.1 hM₁.2.2
  have hk : k₀ ≠ k₁ := by
    intro hkk
    apply hne
    have h1 : M₀.subgroupOf X = M₁.subgroupOf X := by
      apply Subgroup.map_injective (f := θ.toMonoidHom) θ.injective
      rw [hk₀, hk₁, hkk]
    rw [← Subgroup.map_subgroupOf_eq_of_le hM₀.2.1.le, ← Subgroup.map_subgroupOf_eq_of_le
      hM₁.2.1.le, h1]
  have hv₀ := hval M₀ k₀ hM₀.2.1.le hk₀
  have hv₁ := hval M₁ k₁ hM₁.2.1.le hk₁
  have hsmall : Nat.card (centerOf (parabolicRadical Tag.G2 K {i1})) ≤ Nat.card K := by
    rw [G2Rad.centerOf_parabolicRadical_one]
    refine Nat.card_le_card_of_surjective (fun c => (⟨gX rC c, gX_c_mem_N1 c⟩ :
      ↥(N1 : Subgroup (ModGL Tag.G2 K)))) fun z => ?_
    obtain ⟨c, hc⟩ := G2Rad.exists_of_mem_N1 z.2
    exact ⟨c, Subtype.ext hc.symm⟩
  have hbig := G2Rad.card_le_card_centerOf_zero (K := K)
  have hlt : Nat.card K < Nat.card K * Nat.card K := lt_mul_self (by omega)
  have hidx : ∀ a b : Fin 2, a ≠ b → (g2Index a = i0 ∧ g2Index b = i1) ∨
      (g2Index a = i1 ∧ g2Index b = i0) := by
    intro a b hab
    have hne' : g2Index a ≠ g2Index b := fun h => hab (g2Index_injective h)
    rcases fin_two_cases (g2Index a) with ha | ha <;> rcases fin_two_cases (g2Index b) with hb | hb
    · exact absurd (ha.trans hb.symm) hne'
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact absurd (ha.trans hb.symm) hne'
  rcases hidx k₀ k₁ hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0] at hv₀
    rw [h1] at hv₁
    omega
  · rw [h0] at hv₀
    rw [h1] at hv₁
    omega

end CFSG.Quasithin.H13.NQCat.NGT
