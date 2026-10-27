module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentFull
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeOuter

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

section Split

variable {G : Type*} [Group G] {R D₁ D₂ : Subgroup G}

theorem exists_mulEquiv_prod_closure {c s : G} (hcR : c ∈ R) (hsR : s ∈ R) (hc2 : c * c = 1)
    (hs2 : s * s = 1) (hcz : ∀ r ∈ R, Commute r c) (hsz : ∀ r ∈ R, Commute r s)
    (hD₁ : ∀ x ∈ R, ∀ y ∈ R, x ∉ D₁ → y ∉ D₁ → x * y ∈ D₁)
    (hD₂ : ∀ x ∈ R, ∀ y ∈ R, x ∉ D₂ → y ∉ D₂ → x * y ∈ D₂)
    (hc₁ : c ∈ D₁) (hc₂ : c ∉ D₂) (hs₁ : s ∉ D₁) (hs₂ : s ∈ D₂)
    (hFK : ∀ x ∈ Subgroup.closure ({c, s} : Set G), x ∈ D₁ → x ∈ D₂ → x = 1) :
    ∃ e : (R ⊓ D₁ ⊓ D₂ : Subgroup G) × Subgroup.closure ({c, s} : Set G) ≃* R,
      ∀ x, (e x : G) = x.1 * x.2 := by
  have hcK : c ∈ Subgroup.closure ({c, s} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert c {s})
  have hsK : s ∈ Subgroup.closure ({c, s} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  have hKR : Subgroup.closure ({c, s} : Set G) ≤ R := (Subgroup.closure_le R).2 (by
    rintro x (rfl | rfl)
    · exact hcR
    · exact hsR)
  have hFR : R ⊓ D₁ ⊓ D₂ ≤ R := inf_le_left.trans inf_le_left
  have hcomm : ∀ (f : (R ⊓ D₁ ⊓ D₂ : Subgroup G)) (k : Subgroup.closure ({c, s} : Set G)),
      Commute ((R ⊓ D₁ ⊓ D₂).subtype f) ((Subgroup.closure ({c, s} : Set G)).subtype k) := by
    intro f k
    have hle : Subgroup.closure ({c, s} : Set G) ≤ Subgroup.centralizer {(f : G)} :=
      (Subgroup.closure_le _).2 (by
        rintro x (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hcz f (hFR f.2)).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hsz f (hFR f.2)).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle k.2)).symm
  have hμR : ∀ x, MonoidHom.noncommCoprod (R ⊓ D₁ ⊓ D₂).subtype
      (Subgroup.closure ({c, s} : Set G)).subtype hcomm x ∈ R :=
    fun x => R.mul_mem (hFR x.1.2) (hKR x.2.2)
  set μ := (MonoidHom.noncommCoprod (R ⊓ D₁ ⊓ D₂).subtype
    (Subgroup.closure ({c, s} : Set G)).subtype hcomm).codRestrict R hμR with hμ
  have hinj : Function.Injective μ := by
    intro x y hxy
    have h : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
    have h1 : (y.1 : G)⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
      calc (y.1 : G)⁻¹ * x.1 = (y.1 : G)⁻¹ * (x.1 * x.2) * (x.2 : G)⁻¹ := by group
        _ = (y.1 : G)⁻¹ * (y.1 * y.2) * (x.2 : G)⁻¹ := by rw [h]
        _ = y.2 * (x.2 : G)⁻¹ := by group
    have hF' : (y.1 : G)⁻¹ * x.1 ∈ R ⊓ D₁ ⊓ D₂ :=
      (R ⊓ D₁ ⊓ D₂).mul_mem ((R ⊓ D₁ ⊓ D₂).inv_mem y.1.2) x.1.2
    have hK' : (y.1 : G)⁻¹ * x.1 ∈ Subgroup.closure ({c, s} : Set G) := by
      rw [h1]
      exact Subgroup.mul_mem _ y.2.2 (Subgroup.inv_mem _ x.2.2)
    have h2 := hFK _ hK' hF'.1.2 hF'.2
    have h3 : (x.1 : G) = y.1 := (inv_mul_eq_one.1 h2).symm
    have h4 : (x.2 : G) = y.2 := by
      rw [h3] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have hsurj : Function.Surjective μ := by
    rintro ⟨r, hr⟩
    have key : ∃ k ∈ Subgroup.closure ({c, s} : Set G), r * k ∈ R ⊓ D₁ ⊓ D₂ ∧ r * k * k = r := by
      by_cases h1 : r ∈ D₁ <;> by_cases h2 : r ∈ D₂
      · exact ⟨1, Subgroup.one_mem _, by rw [mul_one]; exact ⟨⟨hr, h1⟩, h2⟩, by group⟩
      · refine ⟨c, hcK, ⟨⟨R.mul_mem hr hcR, D₁.mul_mem h1 hc₁⟩, hD₂ r hr c hcR h2 hc₂⟩, ?_⟩
        rw [mul_assoc, hc2, mul_one]
      · refine ⟨s, hsK, ⟨⟨R.mul_mem hr hsR, hD₁ r hr s hsR h1 hs₁⟩, D₂.mul_mem h2 hs₂⟩, ?_⟩
        rw [mul_assoc, hs2, mul_one]
      · have hrc₁ : r * c ∉ D₁ := fun h => h1 ((Subgroup.mul_mem_cancel_right D₁ hc₁).1 h)
        have hrc₂ : r * c ∈ D₂ := hD₂ r hr c hcR h2 hc₂
        have hrc : r * c ∈ R := R.mul_mem hr hcR
        refine ⟨c * s, Subgroup.mul_mem _ hcK hsK, ⟨⟨R.mul_mem hr (R.mul_mem hcR hsR), ?_⟩, ?_⟩, ?_⟩
        · rw [← mul_assoc]
          exact hD₁ _ hrc s hsR hrc₁ hs₁
        · rw [← mul_assoc]
          exact D₂.mul_mem hrc₂ hs₂
        · have hcs : c * s = s * c := hsz c hcR
          calc r * (c * s) * (c * s) = r * c * (s * c) * s := by group
            _ = r * c * (c * s) * s := by rw [hcs]
            _ = r * (c * c) * (s * s) := by group
            _ = r := by rw [hc2, hs2, mul_one, mul_one]
    obtain ⟨k, hkK, hrk, hrkk⟩ := key
    exact ⟨(⟨r * k, hrk⟩, ⟨k, hkK⟩), Subtype.ext hrkk⟩
  exact ⟨MulEquiv.ofBijective μ ⟨hinj, hsurj⟩, fun x => rfl⟩

theorem exists_mulEquiv_prod_zpowers {c : G} (hcR : c ∈ R) (hc2 : c * c = 1)
    (hcz : ∀ r ∈ R, Commute r c) (hD₂ : ∀ x ∈ R, ∀ y ∈ R, x ∉ D₂ → y ∉ D₂ → x * y ∈ D₂)
    (hc₁ : c ∈ D₁) (hc₂ : c ∉ D₂) :
    ∃ e : (R ⊓ D₁ ⊓ D₂ : Subgroup G) × Subgroup.zpowers c ≃* (R ⊓ D₁ : Subgroup G),
      ∀ x, (e x : G) = x.1 * x.2 := by
  have hc1 : c ≠ 1 := fun h => hc₂ (h ▸ D₂.one_mem)
  have hco : orderOf c = 2 := orderOf_eq_prime (by rw [sq]; exact hc2) hc1
  have hZ : Subgroup.zpowers c ≤ R ⊓ D₁ := (Subgroup.zpowers_le).2 ⟨hcR, hc₁⟩
  have hFR : R ⊓ D₁ ⊓ D₂ ≤ R ⊓ D₁ := inf_le_left
  have hcomm : ∀ (f : (R ⊓ D₁ ⊓ D₂ : Subgroup G)) (k : Subgroup.zpowers c),
      Commute ((R ⊓ D₁ ⊓ D₂).subtype f) ((Subgroup.zpowers c).subtype k) := by
    rintro f ⟨k, hk⟩
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two hco).1 hk with rfl | rfl
    · exact Commute.one_right _
    · exact hcz f f.2.1.1
  have hμR : ∀ x, MonoidHom.noncommCoprod (R ⊓ D₁ ⊓ D₂).subtype (Subgroup.zpowers c).subtype
      hcomm x ∈ R ⊓ D₁ := fun x => (R ⊓ D₁).mul_mem (hFR x.1.2) (hZ x.2.2)
  set μ := (MonoidHom.noncommCoprod (R ⊓ D₁ ⊓ D₂).subtype (Subgroup.zpowers c).subtype
    hcomm).codRestrict (R ⊓ D₁) hμR with hμ
  have hinj : Function.Injective μ := by
    intro x y hxy
    have h : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
    have h1 : (y.1 : G)⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
      calc (y.1 : G)⁻¹ * x.1 = (y.1 : G)⁻¹ * (x.1 * x.2) * (x.2 : G)⁻¹ := by group
        _ = (y.1 : G)⁻¹ * (y.1 * y.2) * (x.2 : G)⁻¹ := by rw [h]
        _ = y.2 * (x.2 : G)⁻¹ := by group
    have hF' : (y.1 : G)⁻¹ * x.1 ∈ R ⊓ D₁ ⊓ D₂ :=
      (R ⊓ D₁ ⊓ D₂).mul_mem ((R ⊓ D₁ ⊓ D₂).inv_mem y.1.2) x.1.2
    have hK' : (y.1 : G)⁻¹ * x.1 ∈ Subgroup.zpowers c := by
      rw [h1]
      exact Subgroup.mul_mem _ y.2.2 (Subgroup.inv_mem _ x.2.2)
    have h2 : (y.1 : G)⁻¹ * x.1 = 1 := by
      rcases (Short.mem_zpowers_iff_of_orderOf_eq_two hco).1 hK' with h | h
      · exact h
      · exact absurd (h ▸ hF'.2) hc₂
    have h3 : (x.1 : G) = y.1 := (inv_mul_eq_one.1 h2).symm
    have h4 : (x.2 : G) = y.2 := by
      rw [h3] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have hsurj : Function.Surjective μ := by
    rintro ⟨r, hr⟩
    by_cases h2 : r ∈ D₂
    · exact ⟨(⟨r, hr, h2⟩, 1), Subtype.ext (mul_one r)⟩
    · refine ⟨(⟨r * c, ⟨(R ⊓ D₁).mul_mem hr ⟨hcR, hc₁⟩, hD₂ r hr.1 c hcR h2 hc₂⟩⟩,
        ⟨c, Subgroup.mem_zpowers c⟩), Subtype.ext ?_⟩
      show r * c * c = r
      rw [mul_assoc, hc2, mul_one]
  exact ⟨MulEquiv.ofBijective μ ⟨hinj, hsurj⟩, fun x => rfl⟩

end Split

@[expose] def derivedStab
    (v : CVert) : Subgroup Shat :=
  (commutator (vStab v)).map (vStab v).subtype

theorem derivedStab_le
    (v : CVert) : derivedStab v ≤ vStab v := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem coe_mem_derivedStab_iff
    {v : CVert} (y : vStab v) :
    (y : Shat) ∈ derivedStab v ↔ y ∈ commutator (vStab v) :=
  Subgroup.mem_map_iff_mem (vStab v).subtype_injective

theorem coe_mem_derivedStab_iff_right
    {v : CVert} {ρ : vStab v →* GStar}
    (hρ : Function.Surjective ρ) (y : vStab v) :
    (y : Shat) ∈ derivedStab v ↔ (ρ y).right = 1 := by
  rw [coe_mem_derivedStab_iff, ← comap_Ginl_eq_commutator hρ, Subgroup.mem_comap]
  show ρ y ∈ (SemidirectProduct.inl : stdGroup →* GStar).range ↔ _
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    SemidirectProduct.rightHom_eq_right]

theorem mul_mem_derivedStab_iff
    {v : CVert} {x y : Shat} (hx : x ∈ vStab v) (hy : y ∈ vStab v) :
    x * y ∈ derivedStab v ↔ (x ∈ derivedStab v ↔ y ∈ derivedStab v) := by
  obtain ⟨g, hg⟩ := cvMul_transitive cv0 v
  have h := Subgroup.mul_mem_iff_of_index_two (index_commutator_vStab hg)
    (a := (⟨x, hx⟩ : vStab v)) (b := ⟨y, hy⟩)
  rw [← coe_mem_derivedStab_iff, ← coe_mem_derivedStab_iff, ← coe_mem_derivedStab_iff] at h
  exact h

theorem mul_mem_derivedStab
    {v : CVert} {x y : Shat} (hx : x ∈ vStab v) (hy : y ∈ vStab v)
    (hx' : x ∉ derivedStab v) (hy' : y ∉ derivedStab v) : x * y ∈ derivedStab v :=
  (mul_mem_derivedStab_iff hx hy).2 (iff_of_false hx' hy')

theorem betaStarElt_right_ne_one :
    betaStarElt.right ≠ 1 := fun h =>
  betaG_ne_one (congrArg Subtype.val h)

theorem clabelS_mem_derivedStab_self
    {v : CVert} {ρ : vStab v →* GStar}
    (hρ : Function.Surjective ρ)
    (hker : ∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) :
    clabelS v ∈ derivedStab v := by
  have h1 : ρ (cStab v) = 1 := (hker _).2 (Subgroup.mem_zpowers _)
  rw [← coe_cStab, coe_mem_derivedStab_iff_right hρ, h1]
  rfl

theorem not_mem_derivedStab_of_eq_beta
    {v : CVert} {ρ : vStab v →* GStar}
    (hρ : Function.Surjective ρ) {s : vStab v} (hρs : ρ s = betaStarElt) :
    (s : Shat) ∉ derivedStab v := by
  rw [coe_mem_derivedStab_iff_right hρ, hρs]
  exact betaStarElt_right_ne_one

@[expose] def pairF4
    (v u : CVert) : Subgroup Shat :=
  vStab v ⊓ vStab u ⊓ derivedStab v ⊓ derivedStab u

theorem pairF4_comm
    (v u : CVert) : pairF4 v u = pairF4 u v := by
  ext x
  simp only [pairF4, Subgroup.mem_inf]
  tauto

theorem pairF4_le_inf
    (v u : CVert) : pairF4 v u ≤ vStab v ⊓ vStab u :=
  inf_le_left.trans inf_le_left

theorem pairF4_le_vStab
    (v u : CVert) : pairF4 v u ≤ vStab v :=
  (pairF4_le_inf v u).trans inf_le_left

theorem pairF4_le_derivedStab
    (v u : CVert) : pairF4 v u ≤ derivedStab v :=
  inf_le_left.trans inf_le_right

section Rho

variable {v u : CVert} {ρ : vStab v →* GStar}

theorem rho_eq_inl_jHom (n : jStar.comap ρ) :
    ρ n = SemidirectProduct.inl
      ⟨((jHom ρ n : groupJ) : ModGL Tag.E6 K), groupJ_le_stdGroup (jHom ρ n).2⟩ :=
  (congrArg Subtype.val (jStarEquiv.symm_apply_apply (nToJStar ρ n))).symm

theorem map_comap_jStar
    (hρ : Function.Surjective ρ) {s : vStab v} (hs : (s : Shat) = clabelS u)
    (hρs : ρ s = betaStarElt)
    (hRN : (vStab u).subgroupOf (vStab v) = jStar.comap ρ ⊔ Subgroup.zpowers s) :
    (jStar.comap ρ).map (vStab v).subtype = vStab v ⊓ vStab u ⊓ derivedStab v := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    have hnR : n ∈ (vStab u).subgroupOf (vStab v) := hRN ▸ Subgroup.mem_sup_left hn
    exact ⟨⟨n.2, Subgroup.mem_subgroupOf.1 hnR⟩,
      (coe_mem_derivedStab_iff_right hρ n).2 ((mem_jStar_iff _).1 hn).1⟩
  · rintro x ⟨⟨hxv, hxu⟩, hxD⟩
    have hyC : (⟨x, hxv⟩ : vStab v) ∈ Subgroup.centralizer {s} :=
      subgroupOf_le_centralizer s hs (Subgroup.mem_subgroupOf.2 hxu)
    rcases mem_or_mul_mem hρs hyC with h | h
    · exact ⟨⟨x, hxv⟩, h, rfl⟩
    · exfalso
      have h1 : (ρ ⟨x, hxv⟩).right = 1 := (coe_mem_derivedStab_iff_right hρ _).1 hxD
      have h2 : (ρ (⟨x, hxv⟩ * s)).right = 1 := ((mem_jStar_iff _).1 h).1
      rw [map_mul, SemidirectProduct.mul_right, h1, one_mul, hρs] at h2
      exact betaStarElt_right_ne_one h2

@[expose] def pairF4ToN (hLN : (pairF4 v u).subgroupOf (vStab v) ≤ jStar.comap ρ) :
    pairF4 v u →* jStar.comap ρ where
  toFun f := ⟨⟨f, pairF4_le_vStab v u f.2⟩, hLN (Subgroup.mem_subgroupOf.2 f.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coe_pairF4ToN (hLN : (pairF4 v u).subgroupOf (vStab v) ≤ jStar.comap ρ)
    (f : pairF4 v u) : (((pairF4ToN hLN f : jStar.comap ρ) : vStab v) : Shat) = f := rfl

theorem pairF4_subgroupOf_le_comap
    (hmap : (jStar.comap ρ).map (vStab v).subtype = vStab v ⊓ vStab u ⊓ derivedStab v) :
    (pairF4 v u).subgroupOf (vStab v) ≤ jStar.comap ρ := by
  intro y hy
  have hy' : (y : Shat) ∈ (jStar.comap ρ).map (vStab v).subtype := by
    rw [hmap]
    exact (Subgroup.mem_subgroupOf.1 hy).1
  exact (Subgroup.mem_map_iff_mem (vStab v).subtype_injective).1 hy'

theorem exists_pairF4_equiv
    (hcu : clabelS v ∈ vStab u) (hc₂ : clabelS v ∉ derivedStab u)
    (hρ : Function.Surjective ρ) (hk : ρ.ker = Subgroup.zpowers (cStab v))
    (hmap : (jStar.comap ρ).map (vStab v).subtype = vStab v ⊓ vStab u ⊓ derivedStab v) :
    ∃ φ : pairF4 v u ≃* groupJ, ∀ (f : pairF4 v u) (y : vStab v), (y : Shat) = f →
      ρ y = SemidirectProduct.inl ⟨(φ f : ModGL Tag.E6 K), groupJ_le_stdGroup (φ f).2⟩ := by
  have hρc : ρ (cStab v) = 1 := by
    rw [← MonoidHom.mem_ker, hk]
    exact Subgroup.mem_zpowers _
  have hcD : clabelS v ∈ derivedStab v := by
    rw [← coe_cStab, coe_mem_derivedStab_iff_right hρ, hρc]
    rfl
  have hLN := pairF4_subgroupOf_le_comap hmap
  have hinj : Function.Injective ((jHom ρ).comp (pairF4ToN hLN)) := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have h0 : ((pairF4ToN hLN f : jStar.comap ρ) : vStab v) ∈ ρ.ker :=
      (jHom_eq_one_iff ρ (pairF4ToN hLN f)).1 ((MonoidHom.comp_apply _ _ f).symm.trans hf)
    have h1 : ((pairF4ToN hLN f : jStar.comap ρ) : vStab v) ∈ Subgroup.zpowers (cStab v) :=
      (SetLike.ext_iff.1 hk _).1 h0
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two (orderOf_cStab v)).1 h1 with h3 | h3
    · exact Subtype.ext (congrArg Subtype.val h3 :
        (((pairF4ToN hLN f : jStar.comap ρ) : vStab v) : Shat) = ((1 : vStab v) : Shat))
    · exfalso
      have h4 : (f : Shat) = clabelS v := congrArg Subtype.val h3
      exact hc₂ ((congrArg (fun x => x ∈ derivedStab u) h4).mp f.2.2)
  have hsurj : Function.Surjective ((jHom ρ).comp (pairF4ToN hLN)) := by
    intro j
    have hj := jHom_surjective ρ hρ j
    obtain ⟨n, hn⟩ := hj
    have hx : ((n : vStab v) : Shat) ∈ vStab v ⊓ vStab u ⊓ derivedStab v := by
      rw [← hmap]
      exact ⟨n, n.2, rfl⟩
    by_cases hD : ((n : vStab v) : Shat) ∈ derivedStab u
    · refine ⟨⟨_, hx, hD⟩, ?_⟩
      have e : pairF4ToN hLN ⟨_, hx, hD⟩ = n := Subtype.ext (Subtype.ext rfl)
      exact (MonoidHom.comp_apply _ _ _).trans ((congrArg (jHom ρ) e).trans hn)
    · have hcN : cStab v ∈ jStar.comap ρ := cStab_mem_comap hk
      have hm : ((n : vStab v) : Shat) * clabelS v ∈ pairF4 v u :=
        ⟨⟨⟨(vStab v).mul_mem hx.1.1 (clabelS_mem_vStab_self v), (vStab u).mul_mem hx.1.2 hcu⟩,
          (derivedStab v).mul_mem hx.2 hcD⟩, mul_mem_derivedStab hx.1.2 hcu hD hc₂⟩
      refine ⟨⟨_, hm⟩, ?_⟩
      have e : pairF4ToN hLN ⟨_, hm⟩ = n * ⟨cStab v, hcN⟩ := Subtype.ext (Subtype.ext rfl)
      have h1 : jHom ρ ⟨cStab v, hcN⟩ = 1 := (jHom_eq_one_iff ρ _).2 hρc
      calc ((jHom ρ).comp (pairF4ToN hLN)) ⟨_, hm⟩ = jHom ρ (pairF4ToN hLN ⟨_, hm⟩) :=
            MonoidHom.comp_apply _ _ _
        _ = jHom ρ (n * ⟨cStab v, hcN⟩) := congrArg (jHom ρ) e
        _ = jHom ρ n * jHom ρ ⟨cStab v, hcN⟩ := map_mul _ _ _
        _ = j * 1 := congrArg₂ (· * ·) hn h1
        _ = j := mul_one j
  refine ⟨MulEquiv.ofBijective _ ⟨hinj, hsurj⟩, fun f y hy => ?_⟩
  have e : y = ((pairF4ToN hLN f : jStar.comap ρ) : vStab v) := Subtype.ext hy
  have hφ : MulEquiv.ofBijective _ ⟨hinj, hsurj⟩ f = jHom ρ (pairF4ToN hLN f) :=
    (MulEquiv.ofBijective_apply _ _ f).trans (MonoidHom.comp_apply _ _ f)
  subst e
  exact (rho_eq_inl_jHom (pairF4ToN hLN f)).trans (congrArg (fun z : groupJ =>
    SemidirectProduct.inl (⟨(z : ModGL Tag.E6 K), groupJ_le_stdGroup z.2⟩ : stdGroup)) hφ.symm)

end Rho

theorem native_distance_three_pair_split_pinned_F4
    (hL : DistThreeLabelsInput)
    (hO : DistThreeOuterInput) (hP : DistThreePathInput) (hT : TypeThreeBoundInput)
    {v u : CVert} (hvu : cgraph.dist v u = 3) :
    pairF4 v u = ⁅vStab v ⊓ vStab u, vStab v ⊓ vStab u⁆ ∧
    (∃ e : pairF4 v u × Subgroup.closure ({clabelS v, clabelS u} : Set Shat) ≃*
        (vStab v ⊓ vStab u : Subgroup Shat), ∀ x, (e x : Shat) = x.1 * x.2) ∧
    (∃ s : vStab v, (s : Shat) = clabelS u ∧ ∃ (ρ : vStab v →* GStar)
        (iv : cgraph.neighborSet v ≃ rootClass), IsCompatLocal v ρ iv ∧ ρ s = betaStarElt) ∧
    ∃ Ψ : groupJ ≃* adjointGroup Tag.F4 (ZMod 2),
      (∀ (g : twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))) (x : groupJ),
        ((x : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) =
            baseChangeGL (algebraMap (ZMod 2) K) (g : ModGL TwistTag.E6.tag (ZMod 2)) →
          (Ψ x : ModGL Tag.F4 (ZMod 2)) = e6FixedToF4 (ZMod 2) g) ∧
      ∀ ρ : vStab v →* GStar, Function.Surjective ρ →
        (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
        ∀ s : vStab v, (s : Shat) = clabelS u → ρ s = betaStarElt →
          ∃ φ : pairF4 v u ≃* groupJ,
            (∀ (f : pairF4 v u) (y : vStab v), (y : Shat) = f →
              ρ y = SemidirectProduct.inl ⟨(φ f : ModGL Tag.E6 K), groupJ_le_stdGroup (φ f).2⟩) ∧
            (∃ e : pairF4 v u ≃* adjointGroup Tag.F4 (ZMod 2), ∀ f, e f = Ψ (φ f)) ∧
            (∃ e : pairF4 v u × Subgroup.zpowers (clabelS v) ≃* jStar.comap ρ,
              ∀ x, ((e x : vStab v) : Shat) = x.1 * x.2) ∧
            (pairF4 v u).subgroupOf (vStab v) ≤ jStar.comap ρ ∧
            Subgroup.zpowers (cStab v) ⊓ (pairF4 v u).subgroupOf (vStab v) = ⊥ ∧
            Subgroup.zpowers (cStab v) ⊔ (pairF4 v u).subgroupOf (vStab v) = jStar.comap ρ := by
  have huv : cgraph.dist u v = 3 := by rw [SimpleGraph.dist_comm]; exact hvu
  have hLvu := hL v u hvu
  obtain ⟨hsv, hcu, -, -⟩ := hLvu
  have hcR : clabelS v ∈ vStab v ⊓ vStab u := ⟨clabelS_mem_vStab_self v, hcu⟩
  have hsR : clabelS u ∈ vStab v ⊓ vStab u := ⟨hsv, clabelS_mem_vStab_self u⟩
  have hρ₀e := exists_compat_beta hO hP hT hvu ⟨clabelS u, hsv⟩ rfl
  obtain ⟨ρ₀, iv, hρ₀, hρ₀s⟩ := hρ₀e
  have hρ₁e := exists_compat_beta hO hP hT huv ⟨clabelS v, hcu⟩ rfl
  obtain ⟨ρ₁, iu, hρ₁, hρ₁c⟩ := hρ₁e
  have hc₁ : clabelS v ∈ derivedStab v := clabelS_mem_derivedStab_self hρ₀.1 hρ₀.2.1
  have hs₁ : clabelS u ∉ derivedStab v := not_mem_derivedStab_of_eq_beta hρ₀.1 hρ₀s
  have hc₂ : clabelS v ∉ derivedStab u := not_mem_derivedStab_of_eq_beta hρ₁.1 hρ₁c
  have hs₂ : clabelS u ∈ derivedStab u := clabelS_mem_derivedStab_self hρ₁.1 hρ₁.2.1
  have hk₀ := ker_eq_zpowers_cStab hρ₀.2.1
  have hFK : ∀ x ∈ Subgroup.closure ({clabelS v, clabelS u} : Set Shat),
      x ∈ derivedStab v → x ∈ derivedStab u → x = 1 := by
    intro x hx hxv hxu
    have hle : Subgroup.closure ({clabelS v, clabelS u} : Set Shat) ≤
        ((SemidirectProduct.inr : betaGroup →* GStar).range.comap ρ₀).map (vStab v).subtype := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · refine ⟨cStab v, ⟨1, ?_⟩, rfl⟩
        rw [map_one]
        exact ((MonoidHom.mem_ker).1 (hk₀ ▸ Subgroup.mem_zpowers (cStab v))).symm
      · exact ⟨⟨clabelS u, hsv⟩, ⟨_, hρ₀s.symm⟩, rfl⟩
    obtain ⟨y, ⟨b, hb⟩, rfl⟩ := hle hx
    have hr : (ρ₀ y).right = 1 := (coe_mem_derivedStab_iff_right hρ₀.1 y).1 hxv
    rw [← hb, SemidirectProduct.right_inr] at hr
    have hy1 : ρ₀ y = 1 := by rw [← hb, hr, map_one]
    have hy2 : y ∈ Subgroup.zpowers (cStab v) := hk₀ ▸ hy1
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two (orderOf_cStab v)).1 hy2 with h | h
    · rw [h]
      rfl
    · apply absurd _ hc₂
      rw [← coe_cStab, ← h]
      exact hxu
  have heR' := exists_mulEquiv_prod_closure (D₁ := derivedStab v) (D₂ := derivedStab u)
    hcR hsR (clabelS_mul_clabelS v) (clabelS_mul_clabelS u)
    (fun r hr => commute_clabelS_of_mem_vStab hr.1) (fun r hr => commute_clabelS_of_mem_vStab hr.2)
    (fun x hx y hy => mul_mem_derivedStab hx.1 hy.1)
    (fun x hx y hy => mul_mem_derivedStab hx.2 hy.2) hc₁ hc₂ hs₁ hs₂ hFK
  obtain ⟨eR, heR⟩ := heR'
  have hFull := native_distance_three_pair_is_full_local_centralizer hL hO hP hT hvu
  obtain ⟨s₀, hs₀, -, hN, -⟩ := hFull
  have key : ∀ ρ : vStab v →* GStar, Function.Surjective ρ →
      (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
      ∀ s : vStab v, (s : Shat) = clabelS u → ρ s = betaStarElt →
        (jStar.comap ρ).map (vStab v).subtype = vStab v ⊓ vStab u ⊓ derivedStab v ∧
        ∃ φ : pairF4 v u ≃* groupJ, ∀ (f : pairF4 v u) (y : vStab v), (y : Shat) = f →
          ρ y = SemidirectProduct.inl ⟨(φ f : ModGL Tag.E6 K), groupJ_le_stdGroup (φ f).2⟩ := by
    intro ρ hρ hker s hs hρs
    have hss : s = s₀ := Subtype.ext (hs.trans hs₀.symm)
    subst hss
    have hmap := map_comap_jStar hρ hs hρs (hN ρ hρ hker hρs).1
    exact ⟨hmap, exists_pairF4_equiv hcu hc₂ hρ (ker_eq_zpowers_cStab hker) hmap⟩
  have hΨe := CFSG.Monster.B.E6.FieldInvF4.exists_groupJ_mulEquiv_F4
  obtain ⟨Ψ, hΨ⟩ := hΨe
  have hkey₀ := key ρ₀ hρ₀.1 hρ₀.2.1 _ rfl hρ₀s
  obtain ⟨-, φ₀, -⟩ := hkey₀
  have hperf : Group.IsPerfect (pairF4 v u) := by
    have : Group.IsPerfect (adjointGroup Tag.F4 (ZMod 2)) :=
      (Group.isPerfect_def).2 (single_edge_perfect Tag.F4 (ZMod 2) (Or.inl rfl))
    exact Group.IsPerfect.ofSurjective
      (f := ((φ₀.trans Ψ).symm : adjointGroup Tag.F4 (ZMod 2) →* pairF4 v u))
      (φ₀.trans Ψ).symm.surjective
  have hFR : pairF4 v u = ⁅vStab v ⊓ vStab u, vStab v ⊓ vStab u⁆ := by
    apply le_antisymm
    · calc pairF4 v u = ⁅pairF4 v u, pairF4 v u⁆ := (Subgroup.commutator_eq_self).symm
        _ ≤ ⁅vStab v ⊓ vStab u, vStab v ⊓ vStab u⁆ :=
          Subgroup.commutator_mono (pairF4_le_inf v u) (pairF4_le_inf v u)
    · have hv : ⁅vStab v ⊓ vStab u, vStab v ⊓ vStab u⁆ ≤ derivedStab v := by
        rw [derivedStab, Subgroup.map_subtype_commutator]
        exact Subgroup.commutator_mono inf_le_left inf_le_left
      have hu : ⁅vStab v ⊓ vStab u, vStab v ⊓ vStab u⁆ ≤ derivedStab u := by
        rw [derivedStab, Subgroup.map_subtype_commutator]
        exact Subgroup.commutator_mono inf_le_right inf_le_right
      have hR : ⁅vStab v ⊓ vStab u, vStab v ⊓ vStab u⁆ ≤ vStab v ⊓ vStab u := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
      exact le_inf (le_inf hR hv) hu
  refine ⟨hFR, ⟨eR, heR⟩, ⟨⟨clabelS u, hsv⟩, rfl, ρ₀, iv, hρ₀, hρ₀s⟩, Ψ, hΨ,
    fun ρ hρ hker s hs hρs => ?_⟩
  have hkey := key ρ hρ hker s hs hρs
  obtain ⟨hmap, φ, hφ⟩ := hkey
  have hk := ker_eq_zpowers_cStab hker
  have hcN : cStab v ∈ jStar.comap ρ := cStab_mem_comap hk
  have heN' := exists_mulEquiv_prod_zpowers (R := vStab v ⊓ vStab u)
    (D₁ := derivedStab v) (D₂ := derivedStab u) hcR (clabelS_mul_clabelS v)
    (fun r hr => commute_clabelS_of_mem_vStab hr.1)
    (fun x hx y hy => mul_mem_derivedStab hx.2 hy.2) hc₁ hc₂
  obtain ⟨eN, heN⟩ := heN'
  let eNR : jStar.comap ρ ≃* (vStab v ⊓ vStab u ⊓ derivedStab v : Subgroup Shat) :=
    ((jStar.comap ρ).equivMapOfInjective (vStab v).subtype (vStab v).subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have heNR : ∀ n : jStar.comap ρ, ((eNR n : Shat)) = ((n : vStab v) : Shat) := fun n => rfl
  have hLN := pairF4_subgroupOf_le_comap hmap
  have hcL : cStab v ∉ (pairF4 v u).subgroupOf (vStab v) := fun h =>
    hc₂ (Subgroup.mem_subgroupOf.1 h).2
  refine ⟨φ, hφ, ⟨φ.trans Ψ, fun f => rfl⟩, ⟨eN.trans eNR.symm, fun x => ?_⟩, hLN, ?_, ?_⟩
  · calc ((((eN.trans eNR.symm) x : jStar.comap ρ) : vStab v) : Shat) =
          ((eNR (eNR.symm (eN x)) : Shat)) := (heNR _).symm
      _ = (eN x : Shat) := congrArg Subtype.val (eNR.apply_symm_apply (eN x))
      _ = x.1 * x.2 := heN x
  · rw [eq_bot_iff]
    intro x hx
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two (orderOf_cStab v)).1 hx.1 with h | h
    · exact Subgroup.mem_bot.2 h
    · exact absurd ((congrArg (fun z => z ∈ (pairF4 v u).subgroupOf (vStab v)) h).mp hx.2) hcL
  · refine le_antisymm (sup_le ((Subgroup.zpowers_le).2 hcN) hLN) (fun n hn => ?_)
    have hx : ((n : vStab v) : Shat) ∈ vStab v ⊓ vStab u ⊓ derivedStab v := by
      rw [← hmap]
      exact ⟨n, hn, rfl⟩
    by_cases hD : ((n : vStab v) : Shat) ∈ derivedStab u
    · exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 ⟨hx, hD⟩)
    · have hm : n * cStab v ∈ (pairF4 v u).subgroupOf (vStab v) := Subgroup.mem_subgroupOf.2
        ⟨⟨⟨(vStab v).mul_mem hx.1.1 (clabelS_mem_vStab_self v), (vStab u).mul_mem hx.1.2 hcu⟩,
          (derivedStab v).mul_mem hx.2 hc₁⟩, mul_mem_derivedStab hx.1.2 hcu hD hc₂⟩
      have e : n = n * cStab v * cStab v := (mul_mul_self_eq (orderOf_cStab v) n).symm
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hm)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

end CFSG.Monster.B.TwoA.Amalgam
