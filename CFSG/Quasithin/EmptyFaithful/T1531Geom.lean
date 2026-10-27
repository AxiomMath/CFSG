module

public import CFSG.Quasithin.EmptyFaithful.T1531Basic
public import CFSG.Quasithin.EmptyFaithful.S143Aux
public import CFSG.GroupTheory.KleinFourAutomorphism
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.EmptyFaithful.T1531Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417

section Transitive

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_conj_of_mem_V₁ (D : Decomp153 T M V₁ V₂ t) {x y : G}
    (hx : x ∈ V₁) (hy : y ∈ V₁) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ m ∈ M ⊓ Subgroup.centralizer (V₂ : Set G), m * x * m⁻¹ = y := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := D.model
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have hsq : ∀ u : ↥(commV L₁), u ^ 2 = 1 := fun u => Subtype.ext (IntMod.sq_eq_one u.1)
  have hexp : Monoid.exponent ↥(commV L₁) = 2 := by
    have hdvd : Monoid.exponent ↥(commV L₁) ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hsub : Subsingleton ↥(commV L₁) := Monoid.exp_eq_one_iff.mp h1
      have := Nat.card_of_subsingleton (1 : ↥(commV L₁))
      rw [hS.card_U₁] at this
      omega
    · exact h2
  have : IsKleinFour ↥(commV L₁) := ⟨hS.card_U₁, hexp⟩
  have ha1 : (⟨a, ha⟩ : ↥(commV L₁)) ≠ 1 := fun e => hx1 (by
    have := congrArg (fun u : ↥(commV L₁) => inclMod hV (u : IntMod (VZ T M) hV)) e
    simpa using this)
  have hb1 : (⟨b, hb⟩ : ↥(commV L₁)) ≠ 1 := fun e => hy1 (by
    have := congrArg (fun u : ↥(commV L₁) => inclMod hV (u : IntMod (VZ T M) hV)) e
    simpa using this)
  obtain ⟨ψ, hψ⟩ := CFSG.kleinFour_automorphism_transitive ↥(commV L₁) ⟨a, ha⟩ ⟨b, hb⟩ ha1 hb1
  obtain ⟨l, hl, hlψ⟩ := exists_apply_eq hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) ψ
  have hlX : l ∈ autI hV M := hS.L₁_le hl
  obtain ⟨g, hgM, hg⟩ := (mem_autI hV).1 hlX
  refine ⟨(g : G), ⟨hgM, ?_⟩, ?_⟩
  · refine (mem_centralizer_map_inclMod_iff hV g.2 (commV L₂)).2 fun u hu => ?_
    have : convI hV ⟨(g : G), g.2⟩ = l := hg
    rw [this]
    exact hS.L₁_fix₂ hl hu
  · have h1 := congrArg (fun u : ↥(commV L₁) => inclMod hV (u : IntMod (VZ T M) hV)) hψ
    simp only at h1
    have h2 : (convI hV g (a : IntMod (VZ T M) hV)).val = (g : G) * a.val * (g : G)⁻¹ :=
      convI_apply_val hV g a
    rw [hg, hlψ ⟨a, ha⟩] at h2
    rw [inclMod_apply, inclMod_apply] at h1 ⊢
    exact h2.symm.trans h1

theorem exists_conj_nonsingular (D : Decomp153 T M V₁ V₂ t) {x y : G}
    (hx : (x ∈ V₁ ∨ x ∈ V₂) ∧ x ≠ 1) (hy : (y ∈ V₁ ∨ y ∈ V₂) ∧ y ≠ 1) :
    ∃ m ∈ M, m * x * m⁻¹ = y := by
  have conj_ne : ∀ {w : G}, w ≠ 1 → t * w * t⁻¹ ≠ 1 := fun {w} hw e => hw (by
    have := congrArg (fun z => t⁻¹ * z * t) e
    simpa [mul_assoc] using this)
  rcases hx with ⟨hx | hx, hx1⟩ <;> rcases hy with ⟨hy | hy, hy1⟩
  · obtain ⟨m, hm, e⟩ := exists_conj_of_mem_V₁ D hx hy hx1 hy1
    exact ⟨m, hm.1, e⟩
  · have hx' : t * x * t⁻¹ ∈ V₂ := D.swap₁ x hx
    obtain ⟨m, hm, e⟩ := exists_conj_of_mem_V₁ D.swapPlanes hx' hy (conj_ne hx1) hy1
    exact ⟨m * t, M.mul_mem hm.1 D.t_mem, by rw [← e]; group⟩
  · have hx' : t * x * t⁻¹ ∈ V₁ := D.swap₂ x hx
    obtain ⟨m, hm, e⟩ := exists_conj_of_mem_V₁ D hx' hy (conj_ne hx1) hy1
    exact ⟨m * t, M.mul_mem hm.1 D.t_mem, by rw [← e]; group⟩
  · obtain ⟨m, hm, e⟩ := exists_conj_of_mem_V₁ D.swapPlanes hx hy hx1 hy1
    exact ⟨m, hm.1, e⟩

theorem exists_conj_singular (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {x y : G}
    (hx : x ∈ VZ T M ∧ x ∉ V₁ ∧ x ∉ V₂) (hy : y ∈ VZ T M ∧ y ∉ V₁ ∧ y ∉ V₂) :
    ∃ m ∈ M, m * x * m⁻¹ = y := by
  have hc : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.elemAbelian (D.le₁ ha) (D.le₂ hb)
  have hdec : ∀ {w : G}, w ∈ VZ T M → ∃ w₁ ∈ V₁, ∃ w₂ ∈ V₂, w₁ * w₂ = w := fun {w} hw => by
    have : w ∈ V₁ ⊔ V₂ := by rw [D.sup]; exact hw
    exact exists_mul_of_mem_sup_of_commute hc this
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hdec hx.1
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hdec hy.1
  have hx₁1 : x₁ ≠ 1 := fun e => hx.2.2 (by rw [e, one_mul]; exact hx₂)
  have hx₂1 : x₂ ≠ 1 := fun e => hx.2.1 (by rw [e, mul_one]; exact hx₁)
  have hy₁1 : y₁ ≠ 1 := fun e => hy.2.2 (by rw [e, one_mul]; exact hy₂)
  have hy₂1 : y₂ ≠ 1 := fun e => hy.2.1 (by rw [e, mul_one]; exact hy₁)
  obtain ⟨m₁, hm₁, e₁⟩ := exists_conj_of_mem_V₁ D hx₁ hy₁ hx₁1 hy₁1
  obtain ⟨m₂, hm₂, e₂⟩ := exists_conj_of_mem_V₁ D.swapPlanes hx₂ hy₂ hx₂1 hy₂1
  have c1 : m₂ * x₁ * m₂⁻¹ = x₁ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp hm₂.2 x₁ hx₁).symm
  have c2 : m₁ * y₂ * m₁⁻¹ = y₂ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp hm₁.2 y₂ hy₂).symm
  refine ⟨m₁ * m₂, M.mul_mem hm₁.1 hm₂.1, ?_⟩
  calc (m₁ * m₂) * (x₁ * x₂) * (m₁ * m₂)⁻¹
      = m₁ * ((m₂ * x₁ * m₂⁻¹) * (m₂ * x₂ * m₂⁻¹)) * m₁⁻¹ := by group
    _ = m₁ * (x₁ * y₂) * m₁⁻¹ := by rw [c1, e₂]
    _ = (m₁ * x₁ * m₁⁻¹) * (m₁ * y₂ * m₁⁻¹) := by group
    _ = y₁ * y₂ := by rw [e₁, c2]

end Transitive

section Singular

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem card_le_four_of_isTotSingular153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    {A : Subgroup G} (hA : IsTotSingular153 T M V₁ V₂ A) : Nat.card A ≤ 4 := by
  obtain ⟨hAV, h1, -⟩ := hA
  have hV₁N : V₁ ≤ Subgroup.normalizer (A : Set G) :=
    D.le₁.trans (HypF91.le_normalizer_of_isElemAbelian_le h.elemAbelian hAV)
  have hprod := S143.card_sup_mul_card_inf_of_le_normalizer hV₁N
  rw [h1, Subgroup.card_bot, D.card₁] at hprod
  have hcard : Nat.card ↥(A ⊔ V₁) ≤ Nat.card (VZ T M) := Subgroup.card_le_of_le (sup_le hAV D.le₁)
  rw [h.card_VZ] at hcard
  omega

theorem not_isTotSingular153_of_card (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    {A : Subgroup G} (hA : 8 ≤ Nat.card A) : ¬ IsTotSingular153 T M V₁ V₂ A := fun hts => by
  have := card_le_four_of_isTotSingular153 h D hts
  omega

omit [Finite G] in
theorem IsTotSingular153.mono {A B : Subgroup G} (hts : IsTotSingular153 T M V₁ V₂ B) (hAB : A ≤ B) :
    IsTotSingular153 T M V₁ V₂ A :=
  ⟨hAB.trans hts.1, eq_bot_iff.mpr (hts.2.1 ▸ inf_le_inf_right _ hAB),
    eq_bot_iff.mpr (hts.2.2 ▸ inf_le_inf_right _ hAB)⟩

end Singular

section Model

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_gen_inf_centralizer_Sgp153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    ∃ v ∈ V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G), v ≠ 1 ∧
      ∀ w ∈ V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G), w = 1 ∨ w = v := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := D.model
  have hsyl : IsSylowTwoOf (autI hV T) (autI hV M) := h.isSylowTwoOf_autI
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hsyl
  have hSbar := autI_nS hV hS h.T_le
  have hSN : Sgp153 T ((commV L₁).map (inclMod hV)) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    inf_le_left.trans (h.T_le.trans h.le_normalizer)
  have hfix : ∀ w : IntMod (VZ T M) hV,
      w ∈ fixV (autI hV (Sgp153 T ((commV L₁).map (inclMod hV)))) ↔
        (w = 1 ∨ w = a₁ ∨ w = a₂ ∨ w = a₁ * a₂) := fun w => by
    rw [← hF.sylow.fixS w, mem_fixV, hSbar]
  have hne2 : a₂ ∉ commV L₁ := fun ha => hF.sylow.a₂_ne (by
    have : a₂ ∈ commV L₁ ⊓ commV L₂ := ⟨ha, hF.sylow.a₂_mem⟩
    rwa [hS.inf, Subgroup.mem_bot] at this)
  have hne12 : a₁ * a₂ ∉ commV L₁ := fun ha => hne2 (by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hF.sylow.a₁_mem) ha
    simpa using this)
  refine ⟨a₁.val, ⟨⟨a₁, hF.sylow.a₁_mem, rfl⟩, ?_⟩, ?_, ?_⟩
  · exact (mem_fixV_autI hV hSN a₁).1 ((hfix a₁).2 (Or.inr (Or.inl rfl)))
  · intro e
    exact hF.sylow.a₁_ne (IntMod.val_injective e)
  · rintro w ⟨hw₁, hwC⟩
    obtain ⟨u, hu, rfl⟩ := hw₁
    have hu' : u ∈ fixV (autI hV (Sgp153 T ((commV L₁).map (inclMod hV)))) :=
      (mem_fixV_autI hV hSN u).2 hwC
    rcases (hfix u).1 hu' with h1 | h1 | h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]; rfl
    · exact absurd (h1 ▸ hu) hne2
    · exact absurd (h1 ▸ hu) hne12

theorem not_mem_V₁_V₂_of_fixed (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {z : G}
    (hzV : z ∈ VZ T M) (hzC : z ∈ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) :
    z ∉ V₁ ∧ z ∉ V₂ := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := D.model
  have hsyl : IsSylowTwoOf (autI hV T) (autI hV M) := h.isSylowTwoOf_autI
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hsyl
  have hzfix : IntMod.mk hV ⟨z, hzV⟩ ∈ fixV (autI hV T) :=
    (mem_fixV_autI hV (h.T_le.trans h.le_normalizer) _).2 hzC
  have hne2 : a₂ ∉ commV L₁ := fun ha => hF.sylow.a₂_ne (by
    have : a₂ ∈ commV L₁ ⊓ commV L₂ := ⟨ha, hF.sylow.a₂_mem⟩
    rwa [hS.inf, Subgroup.mem_bot] at this)
  have hne1 : a₁ ∉ commV L₂ := fun ha => hF.sylow.a₁_ne (by
    have : a₁ ∈ commV L₁ ⊓ commV L₂ := ⟨hF.sylow.a₁_mem, ha⟩
    rwa [hS.inf, Subgroup.mem_bot] at this)
  have hz' : IntMod.mk hV ⟨z, hzV⟩ = a₁ * a₂ := by
    rcases hF.fix _ (fun x hx => hzfix x hx) with h1 | h1
    · exfalso
      apply hz1
      exact congrArg IntMod.val h1
    · exact h1
  constructor
  · rintro ⟨u, hu, hu_eq⟩
    have : u = IntMod.mk hV ⟨z, hzV⟩ := IntMod.val_injective hu_eq
    rw [hz'] at this
    refine hne2 ?_
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hF.sylow.a₁_mem) (this ▸ hu)
    simpa using this
  · rintro ⟨u, hu, hu_eq⟩
    have : u = IntMod.mk hV ⟨z, hzV⟩ := IntMod.val_injective hu_eq
    rw [hz'] at this
    refine hne1 ?_
    have := Subgroup.mul_mem _ (this ▸ hu) (Subgroup.inv_mem _ hF.sylow.a₂_mem)
    simpa using this

theorem not_mem_V₁_V₂_of_mem_Z (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) : z ∉ V₁ ∧ z ∉ V₂ :=
  not_mem_V₁_V₂_of_fixed h D (h.Z_le_VZ hz)
    (Subgroup.mem_centralizer_iff.mpr fun _ hτ' =>
      (Subgroup.mem_centralizer_iff.mp (h.T_le_centralizer_Z hτ') z hz).symm) hz1

theorem conj_mem_V₁_or_V₂ (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {m x : G}
    (hm : m ∈ M) (hx : x ∈ V₁ ∨ x ∈ V₂) : m * x * m⁻¹ ∈ V₁ ∨ m * x * m⁻¹ ∈ V₂ := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := D.model
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer hm
  have hX : convI hV ⟨m, hmN⟩ ∈ autI hV M := convI_mem_autI hV hm hmN
  have key : ∀ u : IntMod (VZ T M) hV,
      m * inclMod hV u * m⁻¹ = inclMod hV (convI hV ⟨m, hmN⟩ u) := fun u => by
    rw [inclMod_apply, inclMod_apply]
    exact (convI_apply_val hV ⟨m, hmN⟩ u).symm
  rcases hx with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · rw [key u]
    rcases hS.perm _ hX with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl ⟨_, OfourStruct.commV_apply_mem _ L₁ L₁ h1 hu, rfl⟩
    · exact Or.inr ⟨_, OfourStruct.commV_apply_mem _ L₁ L₂ h1 hu, rfl⟩
  · rw [key u]
    rcases hS.perm _ hX with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨_, OfourStruct.commV_apply_mem _ L₂ L₂ h2 hu, rfl⟩
    · exact Or.inl ⟨_, OfourStruct.commV_apply_mem _ L₂ L₁ h2 hu, rfl⟩

theorem not_isTotSingular153_commutator (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {x : G}
    (hxM : x ∈ M) (hxZ : x ∈ Subgroup.centralizer (ZS153 T M V₁ : Set G))
    (hne : ⁅VZ T M, Subgroup.zpowers x⁆ ≠ ⊥) :
    ¬ IsTotSingular153 T M V₁ V₂ ⁅VZ T M, Subgroup.zpowers x⁆ := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := D.model
  have hMN := h.le_normalizer
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hxM
  have hsyl : IsSylowTwoOf (autI hV T) (autI hV M) := h.isSylowTwoOf_autI
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hsyl
  have hSbar := autI_nS hV hS h.T_le
  have hSN : Sgp153 T ((commV L₁).map (inclMod hV)) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    inf_le_left.trans (h.T_le.trans hMN)
  have ha₁fix : a₁ ∈ fixV (autI hV (Sgp153 T ((commV L₁).map (inclMod hV)))) := by
    rw [mem_fixV, hSbar]
    exact (hF.sylow.fixS a₁).2 (Or.inr (Or.inl rfl))
  have ha₁C : a₁.val ∈ Subgroup.centralizer
      (Sgp153 T ((commV L₁).map (inclMod hV)) : Set G) := (mem_fixV_autI hV hSN a₁).1 ha₁fix
  have ha₁Z : a₁.val ∈ ZS153 T M ((commV L₁).map (inclMod hV)) := ⟨a₁.val_mem, ha₁C⟩
  have hxa₁ : convI hV ⟨x, hxN⟩ a₁ = a₁ := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    have hc := Subgroup.mem_centralizer_iff.mp hxZ a₁.val ha₁Z
    calc x * a₁.val * x⁻¹ = (a₁.val * x) * x⁻¹ := by rw [hc]
      _ = a₁.val := by group
  have hxbX : convI hV ⟨x, hxN⟩ ∈ autI hV M := convI_mem_autI hV hxM hxN
  have hxbZ : convI hV ⟨x, hxN⟩ ∈ autI hV (Subgroup.zpowers x) :=
    convI_mem_autI hV (Subgroup.mem_zpowers x) hxN
  have hxbsup : convI hV ⟨x, hxN⟩ ∈ L₁ ⊔ L₂ := by
    refine (hS.mem_sup_iff hxbX).2 fun u hu => ?_
    rcases hS.perm _ hxbX with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact OfourStruct.commV_apply_mem _ L₁ L₁ h1 hu
    · exfalso
      have h2 : convI hV ⟨x, hxN⟩ a₁ ∈ commV L₂ := OfourStruct.commV_apply_mem _ L₁ L₂ h1 hF.sylow.a₁_mem
      rw [hxa₁] at h2
      have : a₁ ∈ commV L₁ ⊓ commV L₂ := ⟨hF.sylow.a₁_mem, h2⟩
      rw [hS.inf, Subgroup.mem_bot] at this
      exact hF.sylow.a₁_ne this
  obtain ⟨l₁, hl₁, l₂, hl₂, hxl⟩ := exists_mul_of_mem_sup_of_commute hS.comm hxbsup
  have hxb1 : convI hV ⟨x, hxN⟩ ≠ 1 := by
    intro e
    apply hne
    have hxC : x ∈ Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV ⟨x, hxN⟩).1 e
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv y hy
    have hyC : y ∈ Subgroup.centralizer (VZ T M : Set G) := Subgroup.zpowers_le.mpr hxC hy
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hyC v hv))
  have hcomm := commutator_eq_map_commV hV (Subgroup.zpowers_le.mpr hxN : Subgroup.zpowers x ≤
    Subgroup.normalizer (VZ T M : Set G))
  rintro ⟨-, h1, h2⟩
  by_cases hl₁1 : l₁ = 1
  · have hl₂1 : l₂ ≠ 1 := fun e => hxb1 (by rw [← hxl, hl₁1, e, mul_one])
    obtain ⟨u, hu, hu'⟩ : ∃ u ∈ commV L₂, l₂ u ≠ u := by
      by_contra hcon
      push Not at hcon
      exact hl₂1 (eq_one_of_forall_apply_eq hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hl₂
        hcon)
    have hxu : convI hV ⟨x, hxN⟩ u = l₂ u := by
      rw [← hxl, hl₁1, one_mul]
    have hmem : inclMod hV ((convI hV ⟨x, hxN⟩ u) * u⁻¹) ∈ ⁅VZ T M, Subgroup.zpowers x⁆ := by
      rw [hcomm]
      exact ⟨_, Subgroup.subset_closure ⟨_, hxbZ, u, rfl⟩, rfl⟩
    have hmem₂ : inclMod hV ((convI hV ⟨x, hxN⟩ u) * u⁻¹) ∈ (commV L₂).map (inclMod hV) :=
      ⟨_, Subgroup.mul_mem _ (hxu ▸ commV_stable L₂ hl₂ hu) (Subgroup.inv_mem _ hu), rfl⟩
    have hbot : inclMod hV ((convI hV ⟨x, hxN⟩ u) * u⁻¹) ∈
        ⁅VZ T M, Subgroup.zpowers x⁆ ⊓ (commV L₂).map (inclMod hV) := ⟨hmem, hmem₂⟩
    rw [h2, Subgroup.mem_bot] at hbot
    apply hu'
    rw [← hxu]
    have hw1 : (convI hV ⟨x, hxN⟩ u) * u⁻¹ = 1 := by
      apply IntMod.val_injective
      rw [inclMod_apply] at hbot
      exact hbot
    exact mul_inv_eq_one.mp hw1
  · obtain ⟨u, hu, hu'⟩ : ∃ u ∈ commV L₁, l₁ u ≠ u := by
      by_contra hcon
      push Not at hcon
      exact hl₁1 (eq_one_of_forall_apply_eq hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) hl₁
        hcon)
    have hxu : convI hV ⟨x, hxN⟩ u = l₁ u := by
      rw [← hxl, MulAut.mul_apply, hS.L₂_fix₁ hl₂ hu]
    have hmem : inclMod hV ((convI hV ⟨x, hxN⟩ u) * u⁻¹) ∈ ⁅VZ T M, Subgroup.zpowers x⁆ := by
      rw [hcomm]
      exact ⟨_, Subgroup.subset_closure ⟨_, hxbZ, u, rfl⟩, rfl⟩
    have hmem₁ : inclMod hV ((convI hV ⟨x, hxN⟩ u) * u⁻¹) ∈ (commV L₁).map (inclMod hV) :=
      ⟨_, Subgroup.mul_mem _ (hxu ▸ commV_stable L₁ hl₁ hu) (Subgroup.inv_mem _ hu), rfl⟩
    have hbot : inclMod hV ((convI hV ⟨x, hxN⟩ u) * u⁻¹) ∈
        ⁅VZ T M, Subgroup.zpowers x⁆ ⊓ (commV L₁).map (inclMod hV) := ⟨hmem, hmem₁⟩
    rw [h1, Subgroup.mem_bot] at hbot
    apply hu'
    rw [← hxu]
    have hw1 : (convI hV ⟨x, hxN⟩ u) * u⁻¹ = 1 := by
      apply IntMod.val_injective
      rw [inclMod_apply] at hbot
      exact hbot
    exact mul_inv_eq_one.mp hw1

end Model

section Fusion

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_conj_eq_of_card_le (h : Hyp153 G T Mc M) {P : Subgroup G} (hPM : P ≤ M)
    (hP : IsPGroup 2 P) (hcard : Nat.card T ≤ Nat.card P) :
    ∃ m ∈ M, P = conjSubgroup T m := by
  have hT' : IsSylowIn 2 T M := h.isSylowTwoOf
  obtain ⟨m, hm, hle⟩ := E3.exists_le_conj_of_isSylowIn hT' hPM hP
  refine ⟨m, hm, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [E3.card_conjSubgroup]
  exact hcard

theorem exists_ne_one_mem_Z (h : Hyp153 G T Mc M) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.qtfe.omegaOneCenter_ne_bot
  exact ⟨a.1, a.2, fun e => ha (Subtype.ext e)⟩

theorem exists_fixed_singular (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    ∃ z ∈ VZ T M, z ≠ 1 ∧ z ∉ V₁ ∧ z ∉ V₂ ∧ ∀ τ ∈ T, τ * z * τ⁻¹ = z := by
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_Z h
  have hs := not_mem_V₁_V₂_of_mem_Z h D hz hz1
  exact ⟨z, h.Z_le_VZ hz, hz1, hs.1, hs.2, fun τ hτ =>
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp (h.T_le_centralizer_Z hτ) z hz).symm⟩

theorem exists_nonsingular_centralizer_le (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (hC : Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M) :
    ∃ v ∈ V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G), v ≠ 1 ∧
      ∀ x : G, x * v * x⁻¹ = v → x ∈ M := by
  obtain ⟨v, hv, hv1, hvu⟩ := exists_gen_inf_centralizer_Sgp153 h D
  refine ⟨v, hv, hv1, fun x hx => hC (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)⟩
  have h1 : x * v = v * x := mul_inv_eq_iff_eq_mul.mp hx
  rcases hvu w hw with rfl | rfl
  · simp
  · exact h1.symm

theorem false_of_conj_fixed_nonsingular (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (hC : Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M)
    {z g : G} (hzT : ∀ τ ∈ T, τ * z * τ⁻¹ = z)
    (hy : g * z * g⁻¹ ∈ V₁ ∨ g * z * g⁻¹ ∈ V₂) (hy1 : g * z * g⁻¹ ≠ 1) : False := by
  obtain ⟨v₀, hv₀, hv₀1, hCv₀⟩ := exists_nonsingular_centralizer_le h D hC
  obtain ⟨m, hmM, hm⟩ := exists_conj_nonsingular D ⟨hy, hy1⟩ ⟨Or.inl hv₀.1, hv₀1⟩
  obtain ⟨a, ha⟩ : ∃ a : G, a = m * g := ⟨_, rfl⟩
  have haz : a * z * a⁻¹ = v₀ := by
    calc a * z * a⁻¹ = m * (g * z * g⁻¹) * m⁻¹ := by rw [ha]; group
      _ = v₀ := hm
  have hPC : ∀ x ∈ conjSubgroup T a⁻¹, x * v₀ * x⁻¹ = v₀ := fun x hx => by
    rw [E3.mem_conjSubgroup_inv_iff] at hx
    calc x * v₀ * x⁻¹ = a * ((a⁻¹ * x * a) * z * (a⁻¹ * x * a)⁻¹) * a⁻¹ := by
          conv_lhs => rw [← haz]
          group
      _ = v₀ := by rw [hzT _ hx, haz]
  have hPM : conjSubgroup T a⁻¹ ≤ M := fun x hx => hCv₀ x (hPC x hx)
  have hPp : IsPGroup 2 (conjSubgroup T a⁻¹) := E3.isPGroup_conjSubgroup h.isSylowTwoOf.2.1 a⁻¹
  obtain ⟨m', hm', hPeq⟩ :=
    exists_conj_eq_of_card_le h hPM hPp (by rw [E3.card_conjSubgroup])
  have hv₂T : ∀ τ ∈ T, τ * (m' * v₀ * m'⁻¹) * τ⁻¹ = m' * v₀ * m'⁻¹ := fun τ hτ => by
    have hx : m'⁻¹ * τ * m' ∈ conjSubgroup T m' := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hτ
    rw [← hPeq] at hx
    have h2 := hPC _ hx
    calc τ * (m' * v₀ * m'⁻¹) * τ⁻¹
        = m' * ((m'⁻¹ * τ * m') * v₀ * (m'⁻¹ * τ * m')⁻¹) * m'⁻¹ := by group
      _ = m' * v₀ * m'⁻¹ := by rw [h2]
  have hv₂1 : m' * v₀ * m'⁻¹ ≠ 1 := fun e => hv₀1 (by simpa using e)
  have hv₂n := conj_mem_V₁_or_V₂ h D hm' (Or.inl hv₀.1)
  have hv₂V : m' * v₀ * m'⁻¹ ∈ VZ T M := by
    rcases hv₂n with hh | hh
    · exact D.le₁ hh
    · exact D.le₂ hh
  have hv₂C : m' * v₀ * m'⁻¹ ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun τ hτ => mul_inv_eq_iff_eq_mul.mp (hv₂T τ hτ)
  have hs := not_mem_V₁_V₂_of_fixed h D hv₂V hv₂C hv₂1
  rcases hv₂n with hh | hh
  · exact hs.1 hh
  · exact hs.2 hh

theorem fusion_153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (hC : Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M) :
    ∀ x ∈ VZ T M, ∀ g : G, g * x * g⁻¹ ∈ VZ T M →
      ∃ m ∈ M, m * x * m⁻¹ = g * x * g⁻¹ := by
  intro x hx g hg
  by_cases hx1 : x = 1
  · exact ⟨1, M.one_mem, by simp [hx1]⟩
  have hy1 : g * x * g⁻¹ ≠ 1 := fun e => hx1 (by simpa using e)
  obtain ⟨z₀, hz₀V, hz₀1, hz₀1', hz₀2', hz₀T⟩ := exists_fixed_singular h D
  by_cases hxs : x ∈ V₁ ∨ x ∈ V₂
  · by_cases hys : g * x * g⁻¹ ∈ V₁ ∨ g * x * g⁻¹ ∈ V₂
    · exact exists_conj_nonsingular D ⟨hxs, hx1⟩ ⟨hys, hy1⟩
    · exfalso
      push Not at hys
      obtain ⟨m, -, e⟩ := exists_conj_singular h D ⟨hg, hys.1, hys.2⟩ ⟨hz₀V, hz₀1', hz₀2'⟩
      have hxe : (m * g)⁻¹ * z₀ * ((m * g)⁻¹)⁻¹ = x := by
        rw [← e]; group
      exact false_of_conj_fixed_nonsingular h D hC (z := z₀) (g := (m * g)⁻¹) hz₀T
        (by rw [hxe]; exact hxs) (by rw [hxe]; exact hx1)
  · push Not at hxs
    by_cases hys : g * x * g⁻¹ ∈ V₁ ∨ g * x * g⁻¹ ∈ V₂
    · exfalso
      obtain ⟨m, -, e⟩ := exists_conj_singular h D ⟨hx, hxs.1, hxs.2⟩ ⟨hz₀V, hz₀1', hz₀2'⟩
      have hye : g * m⁻¹ * z₀ * (g * m⁻¹)⁻¹ = g * x * g⁻¹ := by
        rw [← e]; group
      exact false_of_conj_fixed_nonsingular h D hC (z := z₀) (g := g * m⁻¹) hz₀T
        (by rw [hye]; exact hys) (by rw [hye]; exact hy1)
    · push Not at hys
      exact exists_conj_singular h D ⟨hx, hxs.1, hxs.2⟩ ⟨hg, hys.1, hys.2⟩

theorem totSingular_inter_153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (hC : Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M)
    {g : G} (hg : g ∉ M) :
    IsTotSingular153 T M V₁ V₂ (VZ T M ⊓ conjSubgroup (VZ T M) g) := by
  have key : ∀ w ∈ VZ T M ⊓ conjSubgroup (VZ T M) g, (w ∈ V₁ ∨ w ∈ V₂) → w = 1 := by
    intro w hw hws
    by_contra hw1
    obtain ⟨v₀, hv₀, hv₀1, hCv₀⟩ := exists_nonsingular_centralizer_le h D hC
    obtain ⟨m, hmM, hm⟩ := exists_conj_nonsingular D ⟨hws, hw1⟩ ⟨Or.inl hv₀.1, hv₀1⟩
    have hwg : g * w * g⁻¹ ∈ VZ T M := mem_conjSubgroup_iff.mp hw.2
    have hg' : g * m⁻¹ * v₀ * (g * m⁻¹)⁻¹ ∈ VZ T M := by
      have e : g * m⁻¹ * v₀ * (g * m⁻¹)⁻¹ = g * w * g⁻¹ := by rw [← hm]; group
      rw [e]
      exact hwg
    obtain ⟨m₂, hm₂, he⟩ := fusion_153 h D hC v₀ (D.le₁ hv₀.1) (g * m⁻¹) hg'
    have hx : m₂⁻¹ * (g * m⁻¹) * v₀ * (m₂⁻¹ * (g * m⁻¹))⁻¹ = v₀ := by
      calc m₂⁻¹ * (g * m⁻¹) * v₀ * (m₂⁻¹ * (g * m⁻¹))⁻¹
          = m₂⁻¹ * (g * m⁻¹ * v₀ * (g * m⁻¹)⁻¹) * m₂ := by group
        _ = m₂⁻¹ * (m₂ * v₀ * m₂⁻¹) * m₂ := by rw [he]
        _ = v₀ := by group
    have hxM := hCv₀ _ hx
    apply hg
    have e : g = m₂ * (m₂⁻¹ * (g * m⁻¹)) * m := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hm₂ hxM) hmM
  refine ⟨inf_le_left, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro w ⟨hw, hw₁⟩
    exact Subgroup.mem_bot.mpr (key w hw (Or.inl hw₁))
  · rw [eq_bot_iff]
    rintro w ⟨hw, hw₂⟩
    exact Subgroup.mem_bot.mpr (key w hw (Or.inr hw₂))

theorem totSingular_of_normalizer_153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (hC : Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M)
    {U : Subgroup G} (hUV : U ≤ VZ T M) (hN : ¬ Subgroup.normalizer (U : Set G) ≤ M) :
    IsTotSingular153 T M V₁ V₂ U := by
  obtain ⟨g, hgN, hgM⟩ : ∃ g : G, g ∈ Subgroup.normalizer (U : Set G) ∧ g ∉ M := by
    by_contra hcon
    push Not at hcon
    exact hN fun g hg => hcon g hg
  refine (totSingular_inter_153 h D hC hgM).mono fun u hu => ⟨hUV hu, ?_⟩
  exact mem_conjSubgroup_iff.mpr (hUV ((Subgroup.mem_normalizer_iff.mp hgN u).mp hu))

theorem one_lt_rParam_153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (hC : Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M) :
    1 < E3.rParam (VZ T M) := by
  have hHv : M = Subgroup.normalizer (VZ T M : Set G) := h.isHv_of_inM' h.inM
  have h2 : (2 : ℕ∞) ≤ E3.rParam (VZ T M) := by
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hUC⟩ := hU
    by_contra hlt
    push Not at hlt
    have hm : E3.mQuot (VZ T M) U ≤ 1 := by
      have : E3.mQuot (VZ T M) U < 2 := by exact_mod_cast hlt
      omega
    have hcard := E3.card_eq_two_pow_mul (B2F.isPGroup_of_isElemAbelian h.elemAbelian) hUV
    rw [h.card_VZ] at hcard
    have hU8 : 8 ≤ Nat.card U := by
      have h1 : 2 ^ E3.mQuot (VZ T M) U ≤ 2 := by
        calc 2 ^ E3.mQuot (VZ T M) U ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm
          _ = 2 := by norm_num
      have h3 : 0 < Nat.card U := Nat.card_pos
      nlinarith
    by_cases hN : Subgroup.normalizer (U : Set G) ≤ M
    · apply hUC
      rw [← hHv]
      exact (Subgroup.centralizer_le_normalizer (U : Set G)).trans hN
    · exact not_isTotSingular153_of_card h D hU8 (totSingular_of_normalizer_153 h D hC hUV hN)
  have h2' : (1 : ℕ∞) + 1 ≤ E3.rParam (VZ T M) := by
    rw [one_add_one_eq_two]
    exact h2
  exact (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mp h2'

theorem centralizer_nonsingular_153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (hC : Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M) :
    ∀ v : G, v ≠ 1 → (v ∈ V₁ ∨ v ∈ V₂) → Subgroup.centralizer ({v} : Set G) ≤ M := by
  intro v hv1 hvs x hx
  obtain ⟨v₀, hv₀, hv₀1, hCv₀⟩ := exists_nonsingular_centralizer_le h D hC
  obtain ⟨m, hmM, hm⟩ := exists_conj_nonsingular D ⟨hvs, hv1⟩ ⟨Or.inl hv₀.1, hv₀1⟩
  have hxv : x * v * x⁻¹ = v := by
    have := Subgroup.mem_centralizer_iff.mp hx v (Set.mem_singleton v)
    rw [← this]
    group
  have h2 : m * x * m⁻¹ * v₀ * (m * x * m⁻¹)⁻¹ = v₀ := by
    calc m * x * m⁻¹ * v₀ * (m * x * m⁻¹)⁻¹
        = m * x * m⁻¹ * (m * v * m⁻¹) * (m * x * m⁻¹)⁻¹ := by rw [hm]
      _ = m * (x * v * x⁻¹) * m⁻¹ := by group
      _ = v₀ := by rw [hxv, hm]
  have h3 := hCv₀ _ h2
  have e : x = m⁻¹ * (m * x * m⁻¹) * m := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hmM) h3) hmM

theorem normalizer_ZS_153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (hC : Subgroup.centralizer
      ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M) :
    Subgroup.normalizer (ZS153 T M V₁ : Set G) ≤ M := by
  intro g hg
  obtain ⟨v₀, hv₀, hv₀1, hCv₀⟩ := exists_nonsingular_centralizer_le h D hC
  have hv₀Z : v₀ ∈ ZS153 T M V₁ := ⟨D.le₁ hv₀.1, hv₀.2⟩
  have hwZ : g * v₀ * g⁻¹ ∈ ZS153 T M V₁ := (Subgroup.mem_normalizer_iff.mp hg v₀).mp hv₀Z
  have hwV : g * v₀ * g⁻¹ ∈ VZ T M := hwZ.1
  have hw1 : g * v₀ * g⁻¹ ≠ 1 := fun e => hv₀1 (by simpa using e)
  by_cases hws : g * v₀ * g⁻¹ ∈ V₁ ∨ g * v₀ * g⁻¹ ∈ V₂
  · obtain ⟨m, hmM, hm⟩ := exists_conj_nonsingular D ⟨hws, hw1⟩ ⟨Or.inl hv₀.1, hv₀1⟩
    have h2 : m * g * v₀ * (m * g)⁻¹ = v₀ := by
      calc m * g * v₀ * (m * g)⁻¹ = m * (g * v₀ * g⁻¹) * m⁻¹ := by group
        _ = v₀ := hm
    have h3 := hCv₀ _ h2
    have e : g = m⁻¹ * (m * g) := by group
    rw [e]
    exact M.mul_mem (M.inv_mem hmM) h3
  · exfalso
    push Not at hws
    obtain ⟨z₀, hz₀V, hz₀1, hz₀1', hz₀2', hz₀T⟩ := exists_fixed_singular h D
    obtain ⟨m, -, e⟩ := exists_conj_singular h D ⟨hwV, hws.1, hws.2⟩ ⟨hz₀V, hz₀1', hz₀2'⟩
    have hve : (m * g)⁻¹ * z₀ * ((m * g)⁻¹)⁻¹ = v₀ := by
      calc (m * g)⁻¹ * z₀ * ((m * g)⁻¹)⁻¹
          = (m * g)⁻¹ * (m * (g * v₀ * g⁻¹) * m⁻¹) * ((m * g)⁻¹)⁻¹ := by rw [e]
        _ = v₀ := by group
    exact false_of_conj_fixed_nonsingular h D hC (z := z₀) (g := (m * g)⁻¹) hz₀T
      (by rw [hve]; exact Or.inl hv₀.1) (by rw [hve]; exact hv₀1)

end Fusion

end CFSG.Quasithin
