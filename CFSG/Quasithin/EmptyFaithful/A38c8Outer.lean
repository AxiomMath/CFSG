module

public import CFSG.Quasithin.EmptyFaithful.SBc5Three

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417

theorem eq_one_of_commute_alt8 (σ : Equiv.Perm (Fin 8))
    (h : ∀ τ ∈ alternatingGroup (Fin 8), σ * τ = τ * σ) : σ = 1 := by
  have key : ∀ x a b : Fin 8, x ≠ a → x ≠ b → a ≠ b → σ x = x ∨ σ x = a ∨ σ x = b := by
    intro x a b hxa hxb hab
    have hc : Equiv.swap x a * Equiv.swap a b ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxa,
        Equiv.Perm.sign_swap hab]
      decide
    have hcomm := congrArg (fun f => f x) (h _ hc)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hcomm
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have e1 : Equiv.swap a b (σ x) = σ x := Equiv.swap_apply_of_ne_of_ne h2 h3
    have e2 : Equiv.swap x a (σ x) = σ x := Equiv.swap_apply_of_ne_of_ne h1 h2
    have e3 : Equiv.swap a b x = x := Equiv.swap_apply_of_ne_of_ne hxa hxb
    rw [e3, e1, e2] at hcomm
    have : Equiv.swap x a x = x := by
      apply σ.injective
      exact hcomm
    simp at this
    exact hxa this.symm
  have hd : ∀ x : Fin 8, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 ∧ x ≠ x + 3 ∧ x ≠ x + 4 ∧
      x + 3 ≠ x + 4 := by decide
  have hv : ∀ x v : Fin 8, (v = x ∨ v = x + 1 ∨ v = x + 2) → (v = x ∨ v = x + 3 ∨ v = x + 4) →
      v = x := by decide
  apply Equiv.ext
  intro x
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd x
  exact hv x (σ x) (key x (x + 1) (x + 2) d1 d2 d3) (key x (x + 3) (x + 4) d4 d5 d6)

private theorem isSylowTwoOf_map_hom_range' {G K : Type*} [Group G] [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

theorem star_L_eq_alt8 {G : Type} [Group G] {T I L : Subgroup G}
    (hLI : L ≤ I) (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hq : CFSG.IsQuasisimple ↥(Star153 T I L)) (e : ↥(Star153 T I I) ≃* Equiv.Perm (Fin 8)) :
    ((Star153 T I L).subgroupOf (Star153 T I I)).map e.toMonoidHom = alternatingGroup (Fin 8) := by
  have hAB : Star153 T I L ≤ Star153 T I I := InternalSec.autOn_le_autOn_of_le hLI
  set N : Subgroup ↥(Star153 T I I) := (Star153 T I L).subgroupOf (Star153 T I I) with hN
  set K : Subgroup (Equiv.Perm (Fin 8)) := N.map e.toMonoidHom with hK
  let eAK : ↥(Star153 T I L) ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hAB).symm.trans (e.subgroupMap N)
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨e.symm g * n * (e.symm g)⁻¹, ?_, by simp⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := InternalSec.autOn_normal_of (U := UI153 T I) hIL _ (e.symm g).2 _ hn
    simpa using this
  have hqK : CFSG.IsQuasisimple ↥K := CFSG.LocalCores.isQuasisimple_of_mulEquiv eAK hq
  have hperf : commutator ↥K = ⊤ := hqK.1.commutator_eq_top
  have hbot : K ≠ ⊥ := by
    intro hb
    obtain ⟨-, -, a, b, hab⟩ := hqK
    have hs : Subsingleton ↥K := by rw [hb]; infer_instance
    have : Subsingleton (↥K ⧸ Subgroup.center ↥K) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [Subsingleton.elim x y]⟩
    exact hab (Subsingleton.elim _ _)
  exact SBc5.eq_alt8_of_perfect_normal hKn hperf hbot

theorem exists_outer_action {G : Type} [Group G] [Finite G]
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (c : Ctx15332 T Mc M V₁ V₂ Yp I L t)
    (hpre : Preamble32 T V₁ I L) :
    ∃ s ∈ Sgp153 T V₁, ¬ ∃ l ∈ L, ∀ x ∈ L, (s * x * s⁻¹)⁻¹ * (l * x * l⁻¹) ∈ pCoreOf 2 L := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  obtain ⟨hLcJ, -, -, -, hStarQ, -⟩ := c25.conc
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLcJ
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hS : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.sylow
  have hIN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ _
  obtain ⟨e⟩ := c.c31
  set ρ : ↥I →* ↥(Star153 T I I) := S153D.autOnHom hIN with hρ
  set φ : ↥I →* Equiv.Perm (Fin 8) := e.toMonoidHom.comp ρ with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (S153D.autOnHom_surjective hIN)
  have hφker : ∀ y : ↥I, φ y = 1 ↔ (y : G) ∈ Subgroup.centralizer (UI153 T I : Set G) := by
    intro y
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.map_eq_one_iff, hρ]
    exact S153D.autOnHom_eq_one_iff hIN y
  have hpc : ∀ y ∈ pCoreOf 2 L, y ∈ Subgroup.centralizer (UI153 T I : Set G) := fun y hy =>
    (hpre.1 ▸ hy : y ∈ L ⊓ Subgroup.centralizer (UI153 T I : Set G)).2
  have hKalt := star_L_eq_alt8 hLI hIL hStarQ e
  have hLmap : ∀ (x : G) (hx : x ∈ L), φ ⟨x, hLI hx⟩ ∈ alternatingGroup (Fin 8) := by
    intro x hx
    rw [← hKalt]
    refine Subgroup.mem_map.2 ⟨ρ ⟨x, hLI hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact mem_autOn_iff_exists.mpr ⟨x, hIN (hLI hx), hx, rfl⟩
  have hLsurj : ∀ k ∈ alternatingGroup (Fin 8), ∃ (x : G) (hx : x ∈ L), φ ⟨x, hLI hx⟩ = k := by
    intro k hk
    rw [← hKalt] at hk
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hk
    rw [Subgroup.mem_subgroupOf] at ha
    obtain ⟨x, hxN, hxL, hxa⟩ := mem_autOn_iff_exists.mp ha
    refine ⟨x, hxL, ?_⟩
    have : ρ ⟨x, hLI hxL⟩ = a := Subtype.ext (by rw [hρ, S153D.autOnHom_coe]; exact hxa)
    simp [hφ, this]
  by_contra hcon
  push Not at hcon
  have hSK : ∀ (s : G) (hs : s ∈ Sgp153 T V₁), φ ⟨s, hS.1 hs⟩ ∈ alternatingGroup (Fin 8) := by
    intro s hs
    obtain ⟨l, hl, hl'⟩ := hcon s hs
    set σ : Equiv.Perm (Fin 8) := (φ ⟨l, hLI hl⟩)⁻¹ * φ ⟨s, hS.1 hs⟩ with hσ
    have hcomm : ∀ τ ∈ alternatingGroup (Fin 8), σ * τ = τ * σ := by
      intro τ hτ
      obtain ⟨x, hx, rfl⟩ := hLsurj τ hτ
      have hxI : x ∈ I := hLI hx
      have hsl : s * x * s⁻¹ ∈ I := I.mul_mem (I.mul_mem (hS.1 hs) hxI) (I.inv_mem (hS.1 hs))
      have hlx : l * x * l⁻¹ ∈ I := I.mul_mem (I.mul_mem (hLI hl) hxI) (I.inv_mem (hLI hl))
      have h1 := hpc _ (hl' x hx)
      have h2 : φ ⟨(s * x * s⁻¹)⁻¹ * (l * x * l⁻¹), I.mul_mem (I.inv_mem hsl) hlx⟩ = 1 :=
        (hφker _).2 h1
      have h3 : φ ⟨s * x * s⁻¹, hsl⟩ = φ ⟨l * x * l⁻¹, hlx⟩ := by
        have : (⟨(s * x * s⁻¹)⁻¹ * (l * x * l⁻¹), I.mul_mem (I.inv_mem hsl) hlx⟩ : ↥I) =
            (⟨s * x * s⁻¹, hsl⟩ : ↥I)⁻¹ * ⟨l * x * l⁻¹, hlx⟩ := rfl
        rw [this, map_mul, map_inv, inv_mul_eq_one] at h2
        exact h2
      have e1 : (⟨s * x * s⁻¹, hsl⟩ : ↥I) = ⟨s, hS.1 hs⟩ * ⟨x, hxI⟩ * ⟨s, hS.1 hs⟩⁻¹ := rfl
      have e2 : (⟨l * x * l⁻¹, hlx⟩ : ↥I) = ⟨l, hLI hl⟩ * ⟨x, hxI⟩ * ⟨l, hLI hl⟩⁻¹ := rfl
      rw [e1, e2, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv] at h3
      rw [hσ]
      calc (φ ⟨l, hLI hl⟩)⁻¹ * φ ⟨s, hS.1 hs⟩ * φ ⟨x, hxI⟩
          = (φ ⟨l, hLI hl⟩)⁻¹ * (φ ⟨s, hS.1 hs⟩ * φ ⟨x, hxI⟩ * (φ ⟨s, hS.1 hs⟩)⁻¹) *
              φ ⟨s, hS.1 hs⟩ := by group
        _ = (φ ⟨l, hLI hl⟩)⁻¹ * (φ ⟨l, hLI hl⟩ * φ ⟨x, hxI⟩ * (φ ⟨l, hLI hl⟩)⁻¹) *
              φ ⟨s, hS.1 hs⟩ := by rw [h3]
        _ = φ ⟨x, hxI⟩ * ((φ ⟨l, hLI hl⟩)⁻¹ * φ ⟨s, hS.1 hs⟩) := by group
    have hσ1 := eq_one_of_commute_alt8 σ hcomm
    have : φ ⟨s, hS.1 hs⟩ = φ ⟨l, hLI hl⟩ := by
      rw [hσ, inv_mul_eq_one] at hσ1
      exact hσ1.symm
    rw [this]
    exact hLmap l hl
  have hSyl := isSylowTwoOf_map_hom_range' hS φ
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.2 hφs
  set P : Subgroup (Equiv.Perm (Fin 8)) := ((Sgp153 T V₁).subgroupOf I).map φ with hP
  have hPK : P ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hSK y.1 (Subgroup.mem_subgroupOf.1 hy)
  have hcard1 : Nat.card ↥(P.subgroupOf φ.range) * (P.subgroupOf φ.range).index =
      Nat.card ↥φ.range := Subgroup.card_mul_index _
  have hc2 : Nat.card ↥(P.subgroupOf φ.range) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSyl.1).toEquiv
  have hc3 : Nat.card ↥φ.range = 40320 := by
    rw [hrange, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hc4 : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hPK
  rw [hc4] at hm
  rw [hc2, hc3] at hcard1
  have hpos : 0 < Nat.card ↥P := Nat.card_pos
  have hidx : (P.subgroupOf φ.range).index = 2 * m := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hcard1]
    have h2m : Nat.card ↥P * (2 * m) = 2 * (Nat.card ↥P * m) := by ring
    omega
  exact hSyl.2.2 ⟨m, hidx⟩

end CFSG.Quasithin.A38c8
