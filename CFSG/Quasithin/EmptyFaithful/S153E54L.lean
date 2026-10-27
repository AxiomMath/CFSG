module

public import CFSG.Quasithin.EmptyFaithful.S153E54K

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
  CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

section Assembly

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem T_le_normalizer_S54 (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (S54 T Mc M V₁ : Set G) :=
  (T_le_normalizer_YU cx).trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem card_Sa_eq_Sb (cx : Ctx15350 T Mc M V₁ V₂ t) {M₁ M₂ Sa Sb : Subgroup G} {s₁ s₂ : ℕ}
    (o : G26Out54 T Mc M V₁ M₁ M₂ Sa Sb s₁ s₂) {t' : G} (ht' : t' ∈ T)
    (hsw1 : ∀ m ∈ M₁, t'⁻¹ * m * t' ∈ M₂) (hsw2 : ∀ m ∈ M₂, t' * m * t'⁻¹ ∈ M₁) :
    Nat.card ↥Sa = Nat.card ↥Sb := by
  have hSn := T_le_normalizer_S54 cx ht'
  have hSn' := T_le_normalizer_S54 cx (T.inv_mem ht')
  have hVn : t' ∈ Subgroup.normalizer (VZ T M : Set G) := T_le_N cx ht'
  have hVn' : t'⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) := T_le_N cx (T.inv_mem ht')
  have hab : ∀ x ∈ Sa, t' * x * t'⁻¹ ∈ Sb := by
    intro x hx
    have hxS := o.SaS hx
    have hs : t' * x * t'⁻¹ ∈ S54 T Mc M V₁ := (Subgroup.mem_normalizer_iff.1 hSn x).1 hxS
    refine (o.charb _ hs).2 fun m hm => ?_
    have hm'' : t'⁻¹ * m * t' ∈ M₂ := hsw1 m hm
    have h3 : ⁅t'⁻¹ * m * t', x⁆ ∈ VZ T M := (o.chara x hxS).1 hx _ hm''
    have e : ⁅m, t' * x * t'⁻¹⁆ = t' * ⁅t'⁻¹ * m * t', x⁆ * t'⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hVn _).1 h3
  have hba : ∀ x ∈ Sb, t'⁻¹ * x * t'⁻¹⁻¹ ∈ Sa := by
    intro x hx
    have hxS := o.SbS hx
    have hs : t'⁻¹ * x * t'⁻¹⁻¹ ∈ S54 T Mc M V₁ := (Subgroup.mem_normalizer_iff.1 hSn' x).1 hxS
    refine (o.chara _ hs).2 fun m hm => ?_
    have hm'' : t' * m * t'⁻¹ ∈ M₁ := hsw2 m hm
    have h3 : ⁅t' * m * t'⁻¹, x⁆ ∈ VZ T M := (o.charb x hxS).1 hx _ hm''
    have e : ⁅m, t'⁻¹ * x * t'⁻¹⁻¹⁆ = t'⁻¹ * ⁅t' * m * t'⁻¹, x⁆ * t'⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hVn' _).1 h3
  let f : ↥Sa → ↥Sb := fun x => ⟨t' * x * t'⁻¹, hab x x.2⟩
  let g' : ↥Sb → ↥Sa := fun x => ⟨t'⁻¹ * x * t'⁻¹⁻¹, hba x x.2⟩
  have hf : Function.Injective f := fun x y h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa [f] using this
  have hg : Function.Injective g' := fun x y h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa [g'] using this
  exact le_antisymm (Nat.card_le_card_of_injective f hf) (Nat.card_le_card_of_injective g' hg)

theorem s_eq_of_swap (cx : Ctx15350 T Mc M V₁ V₂ t) {M₁ M₂ Sa Sb : Subgroup G} {s₁ s₂ : ℕ}
    (o : G26Out54 T Mc M V₁ M₁ M₂ Sa Sb s₁ s₂) {t' : G} (ht' : t' ∈ T)
    (hsw1 : ∀ m ∈ M₁, t'⁻¹ * m * t' ∈ M₂) (hsw2 : ∀ m ∈ M₂, t' * m * t'⁻¹ ∈ M₁) :
    s₁ = s₂ := by
  have h1 := card_of_nat o.VSa o.nat₁
  have h2 := card_of_nat o.VSb o.nat₂
  have h3 := card_Sa_eq_Sb cx o ht' hsw1 hsw2
  rw [h1, h2] at h3
  have hpos : 0 < Nat.card ↥(VZ T M) := Nat.card_pos
  exact Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 4))
    (Nat.eq_of_mul_eq_mul_left hpos h3)

structure Four54 {G : Type} [Group G] (T Mc M V₁ : Subgroup G)
    (N₁ N₂ : Subgroup (MulAut ↥(VZ T M))) (g : G) (s₁ s₂ : ℕ) : Prop where
  sup : Pi153 T Mc M V₁ N₁ g ⊔ Pi153 T Mc M V₁ N₂ g = Pgp153 T M V₁ Mc g
  inf : Pi153 T Mc M V₁ N₁ g ⊓ Pi153 T Mc M V₁ N₂ g = VZ T M
  cent₁ : Pi153 T Mc M V₁ N₁ g =
    centralizerMod (VZ T M) (Pgp153 T M V₁ Mc g) (Ni153 T Mc M V₁ N₂)
  cent₂ : Pi153 T Mc M V₁ N₂ g =
    centralizerMod (VZ T M) (Pgp153 T M V₁ Mc g) (Ni153 T Mc M V₁ N₁)
  nat₁ : IsSumOfNatSL2ModulesN153 s₁ (Ni153 T Mc M V₁ N₁) (Pi153 T Mc M V₁ N₁ g)
    (Pgp153 T M V₁ Mc g) (VZ T M)
  nat₂ : IsSumOfNatSL2ModulesN153 s₂ (Ni153 T Mc M V₁ N₂) (Pi153 T Mc M V₁ N₂ g)
    (Pgp153 T M V₁ Mc g) (VZ T M)

omit [Finite G] in
theorem Four54.swap {g : G} {s₁ s₂ : ℕ} (h : Four54 T Mc M V₁ N₁ N₂ g s₁ s₂) :
    Four54 T Mc M V₁ N₂ N₁ g s₂ s₁ :=
  ⟨by rw [sup_comm]; exact h.sup, by rw [inf_comm]; exact h.inf, h.cent₂, h.cent₁, h.nat₂, h.nat₁⟩

omit [Finite G] in
theorem comm_inv_eq' (x u : G) : x * u * x⁻¹ * u⁻¹ = (⁅u, x⁆)⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem Sa_eq_centralizerMod (cx : Ctx15350 T Mc M V₁ V₂ t) {M₁ M₂ Sa Sb : Subgroup G}
    {s₁ s₂ : ℕ} (o : G26Out54 T Mc M V₁ M₁ M₂ Sa Sb s₁ s₂) :
    Sa = centralizerMod (VZ T M) (S54 T Mc M V₁) M₂ := by
  ext x
  constructor
  · intro hx
    have hxS := o.SaS hx
    refine ⟨hxS, YU_le_normalizer cx (pCoreOf_le 2 _ hxS), fun u hu => ?_⟩
    have h1 := (o.chara x hxS).1 hx u hu
    rw [comm_inv_eq']
    exact (VZ T M).inv_mem h1
  · rintro ⟨hxS, -, h⟩
    refine (o.chara x hxS).2 fun m hm => ?_
    have h2 := (VZ T M).inv_mem (h m hm)
    rw [comm_inv_eq', inv_inv] at h2
    exact h2

theorem Sb_eq_centralizerMod (cx : Ctx15350 T Mc M V₁ V₂ t) {M₁ M₂ Sa Sb : Subgroup G}
    {s₁ s₂ : ℕ} (o : G26Out54 T Mc M V₁ M₁ M₂ Sa Sb s₁ s₂) :
    Sb = centralizerMod (VZ T M) (S54 T Mc M V₁) M₁ := by
  ext x
  constructor
  · intro hx
    have hxS := o.SbS hx
    refine ⟨hxS, YU_le_normalizer cx (pCoreOf_le 2 _ hxS), fun u hu => ?_⟩
    have h1 := (o.charb x hxS).1 hx u hu
    rw [comm_inv_eq']
    exact (VZ T M).inv_mem h1
  · rintro ⟨hxS, -, h⟩
    refine (o.charb x hxS).2 fun m hm => ?_
    have h2 := (VZ T M).inv_mem (h m hm)
    rw [comm_inv_eq', inv_inv] at h2
    exact h2

theorem exists_order3_N₁ (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    ∃ r ∈ N₁, r ≠ 1 ∧ r ^ 3 = 1 := by
  obtain ⟨f⟩ := c.h53one.iso₁
  have h1 : (finRotate 3 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
  have h3 : (finRotate 3 : Equiv.Perm (Fin 3)) ^ 3 = 1 := by decide
  refine ⟨(f.symm (finRotate 3) : MulAut ↥(VZ T M)), (f.symm _).2, fun h => h1 ?_, ?_⟩
  · have : f.symm (finRotate 3) = 1 := Subtype.ext h
    simpa using congrArg f this
  · have : (f.symm (finRotate 3)) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact congrArg Subtype.val this

theorem exists_order3_N₂ (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    ∃ r ∈ N₂, r ≠ 1 ∧ r ^ 3 = 1 := by
  obtain ⟨f⟩ := c.h53one.iso₂
  have h1 : (finRotate 3 : Equiv.Perm (Fin 3)) ≠ 1 := by decide
  have h3 : (finRotate 3 : Equiv.Perm (Fin 3)) ^ 3 = 1 := by decide
  refine ⟨(f.symm (finRotate 3) : MulAut ↥(VZ T M)), (f.symm _).2, fun h => h1 ?_, ?_⟩
  · have : f.symm (finRotate 3) = 1 := Subtype.ext h
    simpa using congrArg f this
  · have : (f.symm (finRotate 3)) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact congrArg Subtype.val this

theorem four_case (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g)
    {N N' : Subgroup (MulAut ↥(VZ T M))} (hN : N ≤ N₁ ⊔ N₂) (hN' : N' ≤ N₁ ⊔ N₂)
    (hr : ∃ r ∈ N, r ≠ 1 ∧ r ^ 3 = 1) (hr' : ∃ r ∈ N', r ≠ 1 ∧ r ^ 3 = 1)
    {M₁ M₂ Sa Sb : Subgroup G} {s₁ s₂ : ℕ} (o : G26Out54 T Mc M V₁ M₁ M₂ Sa Sb s₁ s₂)
    (hM₁ : M₁ = Ni153 T Mc M V₁ N) (hM₂ : M₂ = Ni153 T Mc M V₁ N') :
    Four54 T Mc M V₁ N N' g s₁ s₂ := by
  have hP : Pgp153 T M V₁ Mc g = S54 T Mc M V₁ := by
    show pCoreOf 2 (Igp153 T M V₁ Mc g) = _
    rw [I_eq_54 h113 cx c hg hgZ]
  have hPa : Pi153 T Mc M V₁ N g = Sa :=
    Pi_eq h113 cx c hg hgZ hN hr hM₁ o.SaS o.VSa o.eqa (o.normalizes_a cx) o.nat₁
  have hPb : Pi153 T Mc M V₁ N' g = Sb :=
    Pi_eq h113 cx c hg hgZ hN' hr' hM₂ o.SbS o.VSb o.eqb (o.normalizes_b cx) o.nat₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPa, hPb, hP]
    exact o.supS
  · rw [hPa, hPb]
    exact o.infS
  · rw [hPa, hP, ← hM₂]
    exact Sa_eq_centralizerMod cx o
  · rw [hPb, hP, ← hM₁]
    exact Sb_eq_centralizerMod cx o
  · rw [← hM₁, hPa, hP]
    exact o.nat₁
  · rw [← hM₂, hPb, hP]
    exact o.nat₂

theorem four_exists (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    ∃ s : ℕ, Four54 T Mc M V₁ N₁ N₂ g s s := by
  obtain ⟨M₁, M₂, Sa, Sb, s₁, s₂, o⟩ := g26Out_exists h113 cx c hg hgZ
  obtain ⟨β₁, φ₁, hβ₁s, hβ₁k, -⟩ := o.nat₁
  obtain ⟨β₂, φ₂, hβ₂s, hβ₂k, -⟩ := o.nat₂
  have hid := ident_decomp h113 cx c o.SM₁ o.SM₂ o.M₁I o.M₂I o.sup o.comm β₁ hβ₁s hβ₁k β₂ hβ₂s
    hβ₂k
  obtain ⟨t', ht', hs1, hs2, hs3, hs4⟩ := exists_swap cx c
  have hr₁ := exists_order3_N₁ cx c
  have hr₂ := exists_order3_N₂ cx c
  rcases hid with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · have hsw1 : ∀ m ∈ M₁, t'⁻¹ * m * t' ∈ M₂ := fun m hm => by
      rw [e₂]
      exact hs1 m (e₁ ▸ hm)
    have hsw2 : ∀ m ∈ M₂, t' * m * t'⁻¹ ∈ M₁ := fun m hm => by
      rw [e₁]
      exact hs2 m (e₂ ▸ hm)
    have hs := s_eq_of_swap cx o ht' hsw1 hsw2
    refine ⟨s₁, ?_⟩
    have := four_case h113 cx c hg hgZ le_sup_left le_sup_right hr₁ hr₂ o e₁ e₂
    rwa [← hs] at this
  · have hsw1 : ∀ m ∈ M₁, t'⁻¹ * m * t' ∈ M₂ := fun m hm => by
      rw [e₂]
      exact hs3 m (e₁ ▸ hm)
    have hsw2 : ∀ m ∈ M₂, t' * m * t'⁻¹ ∈ M₁ := fun m hm => by
      rw [e₁]
      exact hs4 m (e₂ ▸ hm)
    have hs := s_eq_of_swap cx o ht' hsw1 hsw2
    refine ⟨s₁, ?_⟩
    have := (four_case h113 cx c hg hgZ le_sup_right le_sup_left hr₂ hr₁ o e₁ e₂).swap
    rwa [← hs] at this

end Assembly

end S153E54

end CFSG.Quasithin
