module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteBAut

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le)

section Step7

variable {G : Type*} [Group G]

theorem exists_le_range_inf_centralizer_of_le_conj_of_forall {C' : Type*} [Group C']
    {φ' : C' →* G} (hφ' : Function.Injective φ') {J' : Subgroup C'} {X : Subgroup G} {q₀ : G}
    (hq₀ : q₀ ∈ φ'.range) (hX : X ≤ (J'.map φ').map (MulAut.conj q₀).toMonoidHom)
    {D : Type*} [Group D]
    (h7 : ∀ X'' : Subgroup C', X'' ≤ J' → Nat.card X'' = Nat.card X →
      ∃ P'' : Subgroup C', P'' ≤ centralizer (X'' : Set C') ∧ Nonempty (P'' ≃* D)) :
    ∃ P : Subgroup G, P ≤ φ'.range ⊓ centralizer (X : Set G) ∧ Nonempty (P ≃* D) := by
  set X'' : Subgroup C' := (X.map (MulAut.conj q₀⁻¹).toMonoidHom).comap φ' with hX''def
  have hmemX : ∀ x ∈ X, ∃ j ∈ J', φ' j = q₀⁻¹ * x * q₀ := by
    intro x hx
    obtain ⟨_, ⟨j, hj, rfl⟩, hjx⟩ := hX hx
    refine ⟨j, hj, ?_⟩
    rw [← hjx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hconjmem : ∀ x ∈ X, q₀⁻¹ * x * q₀ ∈ X.map (MulAut.conj q₀⁻¹).toMonoidHom := by
    intro x hx
    exact ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hmapX : X''.map φ' = X.map (MulAut.conj q₀⁻¹).toMonoidHom := by
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, -, hj⟩ := hmemX x hx
    refine ⟨j, ?_, ?_⟩
    · show φ' j ∈ X.map (MulAut.conj q₀⁻¹).toMonoidHom
      rw [hj]
      exact hconjmem x hx
    · rw [hj]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hX''J : X'' ≤ J' := by
    intro c hc
    have hc' : φ' c ∈ X.map (MulAut.conj q₀⁻¹).toMonoidHom := hc
    obtain ⟨x, hx, hxc⟩ := hc'
    obtain ⟨j, hj, hjx⟩ := hmemX x hx
    have : φ' j = φ' c := by
      rw [hjx, ← hxc]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hφ' this]
    exact hj
  have hcard : Nat.card X'' = Nat.card X := by
    rw [← card_map_of_injective hφ', hmapX, card_map_of_injective (MulAut.conj q₀⁻¹).injective]
  obtain ⟨P'', hP''c, ⟨eP⟩⟩ := h7 X'' hX''J hcard
  refine ⟨(P''.map φ').map (MulAut.conj q₀).toMonoidHom, le_inf ?_ ?_, ⟨?_⟩⟩
  · rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    obtain ⟨n', rfl⟩ := hq₀
    exact ⟨n' * c * n'⁻¹, by simp [MulAut.conj_apply]⟩
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨j, -, hjx⟩ := hmemX x hx
    have hjX'' : j ∈ X'' := by
      show φ' j ∈ X.map (MulAut.conj q₀⁻¹).toMonoidHom
      rw [hjx]
      exact hconjmem x hx
    have hcj := mem_centralizer_iff.1 (hP''c hc) j hjX''
    have hφc : φ' j * φ' c = φ' c * φ' j := by rw [← map_mul, ← map_mul, hcj]
    have hx' : x = q₀ * φ' j * q₀⁻¹ := by rw [hjx]; group
    rw [hx']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc q₀ * φ' j * q₀⁻¹ * (q₀ * φ' c * q₀⁻¹) = q₀ * (φ' j * φ' c) * q₀⁻¹ := by group
      _ = q₀ * (φ' c * φ' j) * q₀⁻¹ := by rw [hφc]
      _ = q₀ * φ' c * q₀⁻¹ * (q₀ * φ' j * q₀⁻¹) := by group
  · exact ((P''.map φ').equivMapOfInjective _ (MulAut.conj q₀).injective).symm.trans
      ((P''.equivMapOfInjective _ hφ').symm.trans eP)

end Step7

section RouteB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_le_centralizer_mulEquiv_of_inner_of_classes (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {κ : Type*} (rep : κ → C) {k : κ} {g : G}
    (hg : g⁻¹ * t * g = (e.symm (rep k) : G) ∨ g⁻¹ * t * g = t * (e.symm (rep k) : G))
    (hne : g⁻¹ * t * g ≠ t)
    (hinner : ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g,
      t * l * t⁻¹ = w' * l * w'⁻¹)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    (hF1 : ∀ x : C, orderOf x = 2 →
      Nonempty (perfectCore (centralizer ({x} : Set C)) ≃* (Q k ⊔ M k : Subgroup C)) →
      ∃ (k' : κ) (c : C), c * x * c⁻¹ = rep k')
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {D : Type*} [Group D]
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype)
    (hF7 : ∀ (k' : κ) (ι : M k ≃* M k') (X'' : Subgroup C),
      X'' ≤ ((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype →
      Nat.card X'' = Nat.card X →
      ∃ P'' : Subgroup C, P'' ≤ centralizer (X'' : Set C) ∧ Nonempty (P'' ≃* D)) :
    ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) ∧
      Nonempty (P ≃* D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC := EPilot.mem_centralizer_of_inf_centralizer_eq_zpowers hKt
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := EPilot.range_subtype_comp_mulEquiv_symm e
  have hg' : g⁻¹ * t * g = φ (rep k) ∨ g⁻¹ * t * g = t * φ (rep k) := hg
  obtain ⟨w', hw'L, hact⟩ := hinner
  have hw'2 : orderOf w' = 2 :=
    EPilot.orderOf_eq_two_of_inner ht hKt (e.symm (rep k)).2 hg hne hw'L hact
  obtain ⟨x', hx'⟩ := EPilot.exists_eq_conj_of_mem_conjugate e hw'L
  have hx'2 : orderOf x' = 2 := by rw [← EPilot.orderOf_conj_symm e g x', hx', hw'2]
  obtain ⟨φ'₀, hφ'₀, hφ'₀r, hφ'₀x⟩ :=
    EPilot.exists_coords_conjugate e g (x' := x') (c' := 1) (by rw [one_mul, inv_one, mul_one])
  rw [hx'] at hφ'₀x
  have hΛ₀ := EPilot.map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ'₀ hφ'₀r
    hg' (by rw [hφ'₀x]; exact hact)
  rw [hF3 k] at hΛ₀
  have hiso : Nonempty (perfectCore (centralizer ({x'} : Set C)) ≃* (Q k ⊔ M k : Subgroup C)) :=
    ⟨((perfectCore (centralizer ({x'} : Set C))).equivMapOfInjective φ'₀ hφ'₀).trans
      ((MulEquiv.subgroupCongr hΛ₀.symm).trans
        ((Q k ⊔ M k).equivMapOfInjective φ hφ).symm)⟩
  obtain ⟨k', c', hc'⟩ := hF1 x' hx'2 hiso
  obtain ⟨φ', hφ', hφ'r, hφ'rep⟩ := EPilot.exists_coords_conjugate e g hc'
  rw [hx'] at hφ'rep
  have hΛ := EPilot.map_perfectCore_centralizer_eq_of_inner hset hOut htC ht hφ hφr hφ' hφ'r
    hg' (by rw [hφ'rep]; exact hact)
  rw [hF3 k, hF3 k'] at hΛ
  have hXJ' : X ≤ J.map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  have hX2 : ¬ 2 ∣ Nat.card X := fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h)
  obtain ⟨hQeq, ι, -, q₀, hq₀, hXq⟩ := EPilot.exists_conj_le_map_of_two_decompositions hφ hφ'
    (hQ k) (hQ k') (hM k) (hM k') (hMN k) (hMN k') (hQM k) (hQM k') hΛ (hJ k) hXJ' hX2
  have hq₀' : q₀ ∈ φ'.range := by
    rw [hQeq] at hq₀
    obtain ⟨n, -, rfl⟩ := hq₀
    exact ⟨n, rfl⟩
  obtain ⟨P, hP, hPD⟩ :=
    exists_le_range_inf_centralizer_of_le_conj_of_forall hφ' hq₀' hXq (hF7 k' ι)
  refine ⟨P, le_inf (hP.trans inf_le_right) ?_, hPD⟩
  exact (hP.trans inf_le_left).trans (hφ'r ▸ EPilot.conjugate_le_centralizer_conj htC g)

theorem not_normal_map_oddCore_of_inner_of_classes (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {C : Type*} [Group C] (e : L ≃* C) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {κ : Type*} (rep : κ → C) {k : κ} {g : G}
    (hg : g⁻¹ * t * g = (e.symm (rep k) : G) ∨ g⁻¹ * t * g = t * (e.symm (rep k) : G))
    (hne : g⁻¹ * t * g ≠ t)
    (hinner : ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g,
      t * l * t⁻¹ = w' * l * w'⁻¹)
    (Q M : κ → Subgroup C)
    (hF3 : ∀ k, perfectCore (centralizer ({rep k} : Set C)) = Q k ⊔ M k)
    (hQ : ∀ k, IsPGroup 2 (Q k)) (hMN : ∀ k, M k ≤ normalizer (Q k : Set C))
    (hQM : ∀ k, Disjoint (Q k) (M k))
    (hM : ∀ k, ∀ N : Subgroup (M k), N.Normal → IsPGroup 2 N → N = ⊥)
    (hF1 : ∀ x : C, orderOf x = 2 →
      Nonempty (perfectCore (centralizer ({x} : Set C)) ≃* (Q k ⊔ M k : Subgroup C)) →
      ∃ (k' : κ) (c : C), c * x * c⁻¹ = rep k')
    {J : Subgroup C} (hJ : ∀ k, J ≤ M k) {DC : Subgroup C} (hrepD : rep k ∈ DC)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (J.map e.symm.toMonoidHom).map L.subtype)
    (hF7 : ∀ (k' : κ) (ι : M k ≃* M k') (X'' : Subgroup C),
      X'' ≤ ((J.subgroupOf (M k)).map ι.toMonoidHom).map (M k').subtype →
      Nat.card X'' = Nat.card X →
      ∃ P'' : Subgroup C, P'' ≤ centralizer (X'' : Set C) ∧ Nonempty (P'' ≃* DC))
    (htX : t ∈ centralizer (X : Set G))
    (hDX : (DC.map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G))
    (hDq : CFSG.Open.IsQuasisimple ((DC.map e.symm.toMonoidHom).map L.subtype))
    (hZD : center ((DC.map e.symm.toMonoidHom).map L.subtype) = ⊥)
    (hOutD : Group.IsSolvable (Outer ((DC.map e.symm.toMonoidHom).map L.subtype)))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((((DC.map e.symm.toMonoidHom).map L.subtype).subgroupOf
          (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((((DC.map e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_le_centralizer_mulEquiv_of_inner_of_classes hset hOut e ht hKt
    rep hg hne hinner Q M hF3 hQ hMN hQM hM hF1 hJ hXodd hXJ hF7
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  set DG := (DC.map e.symm.toMonoidHom).map L.subtype with hDG
  have hDGL : DG ≤ L := map_subtype_le _
  have hDt : DG ≤ centralizer ({t} : Set G) := hDGL.trans (le_centralizer_of_mem_centralizer htK.1)
  have hyD : (e.symm (rep k) : G) ∈ DG := ⟨e.symm (rep k), ⟨rep k, hrepD, rfl⟩, rfl⟩
  have hy1 : (e.symm (rep k) : G) ≠ 1 := by
    intro h
    rcases hg with h' | h'
    · rw [h] at h'
      have : t = 1 := by
        have e1 : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        rw [e1, h']
        group
      rw [this, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · rw [h, mul_one] at h'
      exact hne h'
  have eDG : DC ≃* DG :=
    (DC.equivMapOfInjective _ e.symm.injective).trans
      ((DC.map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht hDX hDq hZD hOutD hDt hsyl
    hyD hy1 hg hP ⟨eP.trans eDG⟩

end RouteB

end CFSG.SeitzReduction.TwistedE6Pilot
