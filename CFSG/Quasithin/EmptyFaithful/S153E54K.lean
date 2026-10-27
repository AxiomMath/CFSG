module

public import CFSG.Quasithin.EmptyFaithful.S153E54J

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
  CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

section Swap

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem G26Out54.normalizes_a (cx : Ctx15350 T Mc M V₁ V₂ t)
    {M₁ M₂ Sa Sb : Subgroup G} {s₁ s₂ : ℕ} (o : G26Out54 T Mc M V₁ M₁ M₂ Sa Sb s₁ s₂) :
    ∀ y ∈ M₁, ∀ x ∈ Sa, y * x * y⁻¹ ∈ Sa := by
  intro y hy x hx
  have hyI : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := o.M₁I hy
  have hxS : x ∈ S54 T Mc M V₁ := o.SaS hx
  have hyxS : y * x * y⁻¹ ∈ S54 T Mc M V₁ :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hyI) x).1 hxS
  refine (o.chara _ hyxS).2 fun m hm => ?_
  have hVn := YU_le_normalizer cx hyI
  have hm' : y⁻¹ * m * y ∈ M₂ := by
    have h1 : ⁅y⁻¹, m⁆ ∈ ⁅M₁, M₂⁆ := Subgroup.commutator_mem_commutator (M₁.inv_mem hy) hm
    have h2 : y⁻¹ * m * y * m⁻¹ ∈ M₂ := by
      have := o.SM₂ (o.comm h1)
      simpa [commutatorElement_def] using this
    have e : y⁻¹ * m * y = (y⁻¹ * m * y * m⁻¹) * m := by group
    rw [e]
    exact M₂.mul_mem h2 hm
  have h3 : ⁅y⁻¹ * m * y, x⁆ ∈ VZ T M := (o.chara x hxS).1 hx _ hm'
  have e : ⁅m, y * x * y⁻¹⁆ = y * ⁅y⁻¹ * m * y, x⁆ * y⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 hVn _).1 h3

theorem G26Out54.normalizes_b (cx : Ctx15350 T Mc M V₁ V₂ t)
    {M₁ M₂ Sa Sb : Subgroup G} {s₁ s₂ : ℕ} (o : G26Out54 T Mc M V₁ M₁ M₂ Sa Sb s₁ s₂) :
    ∀ y ∈ M₂, ∀ x ∈ Sb, y * x * y⁻¹ ∈ Sb := by
  intro y hy x hx
  have hyI : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := o.M₂I hy
  have hxS : x ∈ S54 T Mc M V₁ := o.SbS hx
  have hyxS : y * x * y⁻¹ ∈ S54 T Mc M V₁ :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hyI) x).1 hxS
  refine (o.charb _ hyxS).2 fun m hm => ?_
  have hVn := YU_le_normalizer cx hyI
  have hm' : y⁻¹ * m * y ∈ M₁ := by
    have h1 : ⁅y⁻¹, m⁆ ∈ ⁅M₁, M₂⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (M₂.inv_mem hy) hm
    have h2 : y⁻¹ * m * y * m⁻¹ ∈ M₁ := by
      have := o.SM₁ (o.comm h1)
      simpa [commutatorElement_def] using this
    have e : y⁻¹ * m * y = (y⁻¹ * m * y * m⁻¹) * m := by group
    rw [e]
    exact M₁.mul_mem h2 hm
  have h3 : ⁅y⁻¹ * m * y, x⁆ ∈ VZ T M := (o.charb x hxS).1 hx _ hm'
  have e : ⁅m, y * x * y⁻¹⁆ = y * ⁅y⁻¹ * m * y, x⁆ * y⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 hVn _).1 h3

theorem card_N₁ (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    Nat.card ↥N₁ = 6 := by
  obtain ⟨e⟩ := c.h53one.iso₁
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem card_N₂ (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    Nat.card ↥N₂ = 6 := by
  obtain ⟨e⟩ := c.h53one.iso₂
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem card_Omega (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    Nat.card ↥(autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc)) = 36 := by
  have h := card_sup_of_comm c.h53one.inf c.h53one.comm
  rw [card_N₁ cx c, card_N₂ cx c] at h
  have e : autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) = N₁ ⊔ N₂ := autOn_YU_eq cx c
  rw [e]
  exact h

theorem exists_odd_T (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    ∃ (t' : G) (ht' : t' ∈ T), convI cx.c.hyp.elemAbelian
      ⟨t', T_le_N cx ht'⟩ ∉ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
  by_contra hcon
  push Not at hcon
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hT8 : Nat.card ↥(autI hV T) = 8 := hS.card_T cx.c.hyp.isSylowTwoOf_autI
  have hle : autI hV T ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    intro φ hφ
    obtain ⟨g, hgT, rfl⟩ := (mem_autI hV).1 hφ
    exact hcon g hgT
  have := Subgroup.card_dvd_of_le hle
  rw [hT8, card_Omega cx c] at this
  omega

theorem swap_of_odd (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) {t'' : G}
    (ht'' : t'' ∈ T)
    (hodd : convI cx.c.hyp.elemAbelian ⟨t'', T_le_N cx ht''⟩ ∉
      autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc)) :
    (∀ u ∈ Ni153 T Mc M V₁ N₁, t'' * u * t''⁻¹ ∈ Ni153 T Mc M V₁ N₂) ∧
      (∀ u ∈ Ni153 T Mc M V₁ N₂, t'' * u * t''⁻¹ ∈ Ni153 T Mc M V₁ N₁) := by
  have hV := cx.c.hyp.elemAbelian
  have hTN := T_le_N cx ht''
  set x := convI hV ⟨t'', hTN⟩ with hx
  have hxO : x ∈ orthogonalGroupOf (qW cx) := by
    rw [← (qW_spec cx).2.2.2]
    exact autI_mono hV (T_le_M cx) (convI_mem_autI hV ht'' hTN)
  have hxodd : ¬ Even (rk (commV (Subgroup.zpowers x))) := fun he =>
    hodd ((mem_autI_YU_iff cx c x).2 ⟨hxO, he⟩)
  obtain ⟨R₁, R₂, hRsup, hRinf, hRc, ⟨eR₁⟩, ⟨eR₂⟩, hswap⟩ := exists_split_swap
    (W := IntMod (VZ T M) hV) (q := qW cx) cx.c.hyp.card_VZ (qW_spec cx).1 (qW_spec cx).2.1
    (qW_spec cx).2.2.1
  obtain ⟨f₁⟩ := c.h53one.iso₁
  obtain ⟨f₂⟩ := c.h53one.iso₂
  let N₁' : Subgroup (MulAut (IntMod (VZ T M) hV)) := N₁
  let N₂' : Subgroup (MulAut (IntMod (VZ T M) hV)) := N₂
  have hsup : R₁ ⊔ R₂ = N₁' ⊔ N₂' := by
    ext g
    rw [hRsup g]
    have e : autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) = N₁' ⊔ N₂' := autOn_YU_eq cx c
    exact (mem_autI_YU_iff cx c g).symm.trans (Iff.of_eq (congrArg (fun K : Subgroup
      (MulAut (IntMod (VZ T M) hV)) => g ∈ K) e))
  have key := unique_decomp (Γ := MulAut (IntMod (VZ T M) hV)) (K₁ := R₁) (K₂ := R₂)
    (L₁ := N₁') (L₂ := N₂') hRinf hRc c.h53one.comm hsup eR₁ eR₂
    (f₁.trans S143.dihThreeEquivPerm.symm) (f₂.trans S143.dihThreeEquivPerm.symm)
  obtain ⟨hs1, hs2⟩ := hswap x hxO hxodd
  have hN : (∀ g ∈ N₁', x * g * x⁻¹ ∈ N₂') ∧ (∀ g ∈ N₂', x * g * x⁻¹ ∈ N₁') := by
    rcases key with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · exact (Subgroup.ext_iff.1 e₂ _).2 (hs1 g ((Subgroup.ext_iff.1 e₁ g).1 hg))
      · exact (Subgroup.ext_iff.1 e₁ _).2 (hs2 g ((Subgroup.ext_iff.1 e₂ g).1 hg))
    · refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · exact (Subgroup.ext_iff.1 e₂ _).2 (hs2 g ((Subgroup.ext_iff.1 e₁ g).1 hg))
      · exact (Subgroup.ext_iff.1 e₁ _).2 (hs1 g ((Subgroup.ext_iff.1 e₂ g).1 hg))
  have hconj : ∀ u : G, u ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc → ∀ hu : u ∈ Subgroup.normalizer
      (VZ T M : Set G), convI hV ⟨t'' * u * t''⁻¹, (Subgroup.normalizer (VZ T M : Set G)).mul_mem
        ((Subgroup.normalizer (VZ T M : Set G)).mul_mem hTN hu)
        ((Subgroup.normalizer (VZ T M : Set G)).inv_mem hTN)⟩ = x * convI hV ⟨u, hu⟩ * x⁻¹ :=
    fun u _ hu => by rw [hx, ← map_inv, ← map_mul, ← map_mul]; rfl
  have hI : ∀ u ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc,
      t'' * u * t''⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := fun u hu =>
    (Subgroup.mem_normalizer_iff.1 (T_le_normalizer_YU cx ht'') u).1 hu
  constructor
  · intro u hu
    obtain ⟨huI, huN, hum⟩ := mem_preAut153.1 hu
    refine mem_preAut153.2 ⟨hI u huI, ?_, ?_⟩
    · exact (Subgroup.normalizer (VZ T M : Set G)).mul_mem
        ((Subgroup.normalizer (VZ T M : Set G)).mul_mem hTN huN)
        ((Subgroup.normalizer (VZ T M : Set G)).inv_mem hTN)
    · have h1 : x * convI hV ⟨u, huN⟩ * x⁻¹ ∈ N₂' := hN.1 _ hum
      show convI hV _ ∈ N₂'
      rw [hconj u huI huN]
      exact h1
  · intro u hu
    obtain ⟨huI, huN, hum⟩ := mem_preAut153.1 hu
    refine mem_preAut153.2 ⟨hI u huI, ?_, ?_⟩
    · exact (Subgroup.normalizer (VZ T M : Set G)).mul_mem
        ((Subgroup.normalizer (VZ T M : Set G)).mul_mem hTN huN)
        ((Subgroup.normalizer (VZ T M : Set G)).inv_mem hTN)
    · have h1 : x * convI hV ⟨u, huN⟩ * x⁻¹ ∈ N₁' := hN.2 _ hum
      show convI hV _ ∈ N₁'
      rw [hconj u huI huN]
      exact h1

theorem exists_swap (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    ∃ t' ∈ T, (∀ u ∈ Ni153 T Mc M V₁ N₁, t'⁻¹ * u * t' ∈ Ni153 T Mc M V₁ N₂) ∧
      (∀ u ∈ Ni153 T Mc M V₁ N₂, t' * u * t'⁻¹ ∈ Ni153 T Mc M V₁ N₁) ∧
      (∀ u ∈ Ni153 T Mc M V₁ N₂, t'⁻¹ * u * t' ∈ Ni153 T Mc M V₁ N₁) ∧
      (∀ u ∈ Ni153 T Mc M V₁ N₁, t' * u * t'⁻¹ ∈ Ni153 T Mc M V₁ N₂) := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨t', ht', hodd⟩ := exists_odd_T cx c
  have hodd' : convI hV ⟨t'⁻¹, T_le_N cx (T.inv_mem ht')⟩ ∉
      autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    intro h
    apply hodd
    have e : convI hV ⟨t', T_le_N cx ht'⟩ = (convI hV ⟨t'⁻¹, T_le_N cx (T.inv_mem ht')⟩)⁻¹ := by
      rw [← map_inv]
      congr 1
      exact Subtype.ext (by simp)
    rw [e]
    exact Subgroup.inv_mem _ h
  obtain ⟨h1, h2⟩ := swap_of_odd cx c ht' hodd
  obtain ⟨h3, h4⟩ := swap_of_odd cx c (T.inv_mem ht') hodd'
  refine ⟨t', ht', fun u hu => ?_, h2, fun u hu => ?_, h1⟩
  · have := h3 u hu
    simpa using this
  · have := h4 u hu
    simpa using this

omit [Finite G] in
theorem card_of_nat {M' Si S S₂ : Subgroup G} {s : ℕ} (hle : S₂ ≤ Si)
    (h : IsSumOfNatSL2ModulesN153 s M' Si S S₂) : Nat.card ↥Si = Nat.card ↥S₂ * 4 ^ s := by
  obtain ⟨β, φ, -, -, hφs, hφk, -⟩ := h
  have hker : φ.ker = S₂.subgroupOf Si := by
    ext x
    rw [MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (↥Si ⧸ φ.ker) = Nat.card (Multiplicative (Fin s → Fin 2 → ZMod 2)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
  have h3 : Nat.card ↥φ.ker = Nat.card ↥S₂ := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h4 : Nat.card (Multiplicative (Fin s → Fin 2 → ZMod 2)) = 4 ^ s := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
    simp
  rw [h1, h2, h3, h4, mul_comm]

end Swap

end S153E54

end CFSG.Quasithin
