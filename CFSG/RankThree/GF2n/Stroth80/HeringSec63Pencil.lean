module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig

public section

namespace CFSG.RankThree.GF2n.Stroth80

namespace HS6

open scoped Pointwise

section Defs

variable {N M : Type} [CommGroup N] [CommGroup M]

@[expose] def N0 (N M : Type) [CommGroup N] [CommGroup M] : Subgroup (N × M) :=
  Subgroup.prod ⊤ ⊥

@[expose] def Esub (N : Type) [CommGroup N] {M : Type} [CommGroup M] (S : Subgroup M) :
    Subgroup (N × M) :=
  Subgroup.prod ⊥ S

@[expose] def Nsub (N : Type) [CommGroup N] {M : Type} [CommGroup M] (S : Subgroup M) :
    Subgroup (N × M) :=
  Subgroup.prod ⊤ S

theorem mem_N0 {x : N × M} : x ∈ N0 N M ↔ x.2 = 1 := by
  simp [N0, Subgroup.mem_prod]

theorem mem_Esub {S : Subgroup M} {x : N × M} : x ∈ Esub N S ↔ x.1 = 1 ∧ x.2 ∈ S := by
  simp [Esub, Subgroup.mem_prod]

theorem mem_Nsub {S : Subgroup M} {x : N × M} : x ∈ Nsub N S ↔ x.2 ∈ S := by
  simp [Nsub, Subgroup.mem_prod]

end Defs

section Map

variable {A : Type} [CommGroup A]

@[expose] def mapA (γ : MulAut A) (S : Subgroup A) : Subgroup A :=
  S.map (γ : A →* A)

theorem mem_mapA {γ : MulAut A} {S : Subgroup A} {x : A} : x ∈ mapA γ S ↔ γ.symm x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

theorem mem_mapA_apply {γ : MulAut A} {S : Subgroup A} {x : A} : γ x ∈ mapA γ S ↔ x ∈ S := by
  rw [mem_mapA]
  simp

theorem mapA_mul (γ δ : MulAut A) (S : Subgroup A) : mapA (γ * δ) S = mapA γ (mapA δ S) := by
  ext x
  simp only [mem_mapA]
  rfl

theorem mapA_one (S : Subgroup A) : mapA (1 : MulAut A) S = S := by
  ext x
  simp [mem_mapA]
  rfl

theorem mapA_inv_mapA (γ : MulAut A) (S : Subgroup A) : mapA γ⁻¹ (mapA γ S) = S := by
  rw [← mapA_mul, inv_mul_cancel, mapA_one]

theorem mapA_mapA_inv (γ : MulAut A) (S : Subgroup A) : mapA γ (mapA γ⁻¹ S) = S := by
  rw [← mapA_mul, mul_inv_cancel, mapA_one]

theorem mapA_inf (γ : MulAut A) (S T : Subgroup A) : mapA γ (S ⊓ T) = mapA γ S ⊓ mapA γ T := by
  ext x
  simp only [mem_mapA, Subgroup.mem_inf]

theorem mapA_bot (γ : MulAut A) : mapA γ (⊥ : Subgroup A) = ⊥ := by
  ext x
  simp [mem_mapA]

theorem mapA_sup (γ : MulAut A) (S T : Subgroup A) : mapA γ (S ⊔ T) = mapA γ S ⊔ mapA γ T :=
  Subgroup.map_sup _ _ _

theorem mapA_le_iff (γ : MulAut A) {S T : Subgroup A} : mapA γ S ≤ mapA γ T ↔ S ≤ T := by
  constructor
  · intro h x hx
    have := h ((mem_mapA_apply (γ := γ)).mpr hx)
    exact mem_mapA_apply.mp this
  · intro h x hx
    rw [mem_mapA] at hx ⊢
    exact h hx

theorem mapA_inj (γ : MulAut A) {S T : Subgroup A} (h : mapA γ S = mapA γ T) : S = T :=
  le_antisymm ((mapA_le_iff γ).mp h.le) ((mapA_le_iff γ).mp h.ge)

theorem card_mapA (γ : MulAut A) (S : Subgroup A) : Nat.card (mapA γ S) = Nat.card S :=
  Subgroup.card_map_of_injective γ.injective

end Map

section Cards

variable {N M : Type} [CommGroup N] [CommGroup M]

theorem card_N0 : Nat.card (N0 N M) = Nat.card N := by
  unfold N0
  rw [Nat.card_congr (Subgroup.prodEquiv ⊤ ⊥).toEquiv, Nat.card_prod, Subgroup.card_top,
    Subgroup.card_bot, mul_one]

theorem card_Esub (S : Subgroup M) : Nat.card (Esub N S) = Nat.card S := by
  unfold Esub
  rw [Nat.card_congr (Subgroup.prodEquiv ⊥ S).toEquiv, Nat.card_prod, Subgroup.card_bot, one_mul]

theorem N0_sup_Esub (S : Subgroup M) : N0 N M ⊔ Esub N S = Nsub N S := by
  apply le_antisymm
  · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_N0] at hx
      rw [mem_Nsub, hx]
      exact S.one_mem
    · rw [mem_Esub] at hx
      rw [mem_Nsub]
      exact hx.2
  · intro x hx
    rw [mem_Nsub] at hx
    have h1 : ((x.1, 1) : N × M) ∈ N0 N M := by rw [mem_N0]
    have h2 : ((1, x.2) : N × M) ∈ Esub N S := by rw [mem_Esub]; exact ⟨rfl, hx⟩
    have := Subgroup.mul_mem_sup h1 h2
    simpa using this

theorem Esub_sup (S T : Subgroup M) : Esub N S ⊔ Esub N T = Esub N (S ⊔ T) := by
  apply le_antisymm
  · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_Esub] at hx ⊢
      exact ⟨hx.1, Subgroup.mem_sup_left hx.2⟩
    · rw [mem_Esub] at hx ⊢
      exact ⟨hx.1, Subgroup.mem_sup_right hx.2⟩
  · intro x hx
    rw [mem_Esub] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hx.2
    have h1 : ((1, a) : N × M) ∈ Esub N S := by rw [mem_Esub]; exact ⟨rfl, ha⟩
    have h2 : ((1, b) : N × M) ∈ Esub N T := by rw [mem_Esub]; exact ⟨rfl, hb⟩
    have := Subgroup.mul_mem_sup h1 h2
    have e : ((1, a) : N × M) * (1, b) = x := Prod.ext (by simp [hx.1]) (by simpa using hab)
    rwa [e] at this

theorem Esub_le_Esub {S T : Subgroup M} : Esub N S ≤ Esub N T ↔ S ≤ T := by
  constructor
  · intro h x hx
    have : ((1, x) : N × M) ∈ Esub N T := h (by rw [mem_Esub]; exact ⟨rfl, hx⟩)
    exact (mem_Esub.mp this).2
  · intro h x hx
    rw [mem_Esub] at hx ⊢
    exact ⟨hx.1, h hx.2⟩

theorem Esub_le_Nsub {S T : Subgroup M} : Esub N S ≤ Nsub N T ↔ S ≤ T := by
  constructor
  · intro h x hx
    have : ((1, x) : N × M) ∈ Nsub N T := h (by rw [mem_Esub]; exact ⟨rfl, hx⟩)
    exact mem_Nsub.mp this
  · intro h x hx
    rw [mem_Esub] at hx
    rw [mem_Nsub]
    exact h hx.2

theorem Nsub_inf (S T : Subgroup M) : Nsub N S ⊓ Nsub N T = Nsub N (S ⊓ T) := by
  ext x
  simp only [Subgroup.mem_inf, mem_Nsub]

theorem N0_le_Nsub (S : Subgroup M) : N0 N M ≤ Nsub N S := by
  intro x hx
  rw [mem_N0] at hx
  rw [mem_Nsub, hx]
  exact S.one_mem

end Cards

section Pencil

@[expose] def Orb {N M : Type} [CommGroup N] [CommGroup M] (Γ : Subgroup (MulAut (N × M))) :
    Set (Subgroup (N × M)) :=
  {S | ∃ γ ∈ Γ, S = mapA γ (N0 N M)}

structure PencilData (K : Type) [Field K] (N M : Type) [CommGroup N] [CommGroup M]
    (Lines : Finset (Subgroup M)) (Γ : Subgroup (MulAut (N × M))) : Prop where
  cardN : Nat.card N = Nat.card K
  N2 : ∀ n : N, n * n = 1
  M2 : ∀ x : M, x * x = 1
  cardM : Nat.card M = Nat.card K ^ 4
  cardLine : ∀ ℓ ∈ Lines, Nat.card ℓ = Nat.card K
  infLine : ∀ ℓ ∈ Lines, ∀ ℓ' ∈ Lines, ℓ ≠ ℓ' → ℓ ⊓ ℓ' = ⊥
  cardLines : Lines.card = Nat.card K ^ 2 + 1
  lineSum : ∀ ℓ₀ ∈ Lines, ∀ ℓ₁ ∈ Lines, ℓ₀ ≠ ℓ₁ → ∀ ℓ ∈ Lines, ℓ ≤ ℓ₀ ⊔ ℓ₁ → ℓ = ℓ₀ ∨ ℓ = ℓ₁
  span : ∀ ℓ₀ ∈ Lines, (⨆ ℓ ∈ Lines, ⨆ (_ : ℓ ≠ ℓ₀), ℓ) = ⊤
  TI : ∀ γ ∈ Γ, mapA γ (N0 N M) ≠ N0 N M → N0 N M ⊓ mapA γ (N0 N M) = ⊥
  lineOf : ∀ γ ∈ Γ, mapA γ (N0 N M) ≠ N0 N M → ∃ ℓ ∈ Lines, mapA γ (N0 N M) ≤ Nsub N ℓ
  trans : ∀ ℓ ∈ Lines, ∀ ℓ' ∈ Lines, ∃ γ ∈ Γ, (∀ n : N, γ (n, 1) = (n, 1)) ∧
    mapA γ (Esub N ℓ) = Esub N ℓ'
  torus : ∀ ℓ ∈ Lines, ∃ θ : ℓ ≃* Multiplicative K, ∀ c : K, c ≠ 0 → ∃ γ ∈ Γ,
    (∀ n : N, γ (n, 1) = (n, 1)) ∧ ∀ e : ℓ,
      γ (1, (e : M)) =
        (1, ((θ.symm (Multiplicative.ofAdd (c * Multiplicative.toAdd (θ e))) : ℓ) : M))
  nontriv : ∃ γ ∈ Γ, mapA γ (N0 N M) ≠ N0 N M

variable {K : Type} [Field K] {N M : Type} [CommGroup N] [CommGroup M] [Finite N] [Finite M]
  {Lines : Finset (Subgroup M)} {Γ : Subgroup (MulAut (N × M))}

theorem N0_mem_Orb : N0 N M ∈ Orb Γ := ⟨1, Γ.one_mem, (mapA_one _).symm⟩

theorem mapA_mem_Orb {S : Subgroup (N × M)} (hS : S ∈ Orb Γ) {γ : MulAut (N × M)} (hγ : γ ∈ Γ) :
    mapA γ S ∈ Orb Γ := by
  obtain ⟨δ, hδ, rfl⟩ := hS
  exact ⟨γ * δ, Γ.mul_mem hγ hδ, (mapA_mul γ δ _).symm⟩

section WithData

variable (D : PencilData K N M Lines Γ)
include D

theorem PencilData.Orb_card {S : Subgroup (N × M)} (hS : S ∈ Orb Γ) : Nat.card S = Nat.card K := by
  obtain ⟨γ, -, rfl⟩ := hS
  rw [card_mapA, card_N0, D.cardN]

theorem PencilData.Orb_inf {S T : Subgroup (N × M)} (hS : S ∈ Orb Γ) (hT : T ∈ Orb Γ)
    (hne : S ≠ T) : S ⊓ T = ⊥ := by
  obtain ⟨γ₁, h1, rfl⟩ := hS
  obtain ⟨γ₂, h2, rfl⟩ := hT
  have hγ : γ₁⁻¹ * γ₂ ∈ Γ := Γ.mul_mem (Γ.inv_mem h1) h2
  have e : mapA γ₂ (N0 N M) = mapA γ₁ (mapA (γ₁⁻¹ * γ₂) (N0 N M)) := by
    rw [← mapA_mul, mul_inv_cancel_left]
  have hne' : mapA (γ₁⁻¹ * γ₂) (N0 N M) ≠ N0 N M := by
    intro h
    apply hne
    rw [e, h]
  have := D.TI _ hγ hne'
  have h3 := congrArg (mapA γ₁) this
  rw [mapA_inf, mapA_bot, ← e] at h3
  exact h3

theorem PencilData.Orb_inf_N0 {S : Subgroup (N × M)} (hS : S ∈ Orb Γ) (hne : S ≠ N0 N M) :
    S ⊓ N0 N M = ⊥ :=
  D.Orb_inf hS N0_mem_Orb hne

theorem PencilData.Orb_line {S : Subgroup (N × M)} (hS : S ∈ Orb Γ) (hne : S ≠ N0 N M) :
    ∃ ℓ ∈ Lines, S ≤ Nsub N ℓ := by
  obtain ⟨γ, hγ, rfl⟩ := hS
  exact D.lineOf γ hγ hne

theorem PencilData.Orb_surj {S : Subgroup (N × M)} (hS : S ∈ Orb Γ) (hne : S ≠ N0 N M)
    {ℓ : Subgroup M} (hℓ : ℓ ∈ Lines) (hle : S ≤ Nsub N ℓ) (e : M) (he : e ∈ ℓ) :
    ∃ n : N, (n, e) ∈ S := by
  let f : S →* M := (MonoidHom.snd N M).comp S.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : (s : N × M) ∈ N0 N M := mem_N0.mpr hs
    have h2 : (s : N × M) ∈ S ⊓ N0 N M := ⟨s.2, h1⟩
    rw [D.Orb_inf_N0 hS hne] at h2
    exact Subtype.ext (Subgroup.mem_bot.mp h2)
  have hrange : f.range ≤ ℓ := by
    rintro _ ⟨s, rfl⟩
    exact mem_Nsub.mp (hle s.2)
  have hcard : Nat.card f.range = Nat.card S := by
    show Nat.card (Set.range f) = _
    exact (Nat.card_congr (Equiv.ofInjective f hinj)).symm
  have heq : f.range = ℓ := by
    apply Subgroup.eq_of_le_of_card_ge hrange
    rw [hcard, D.Orb_card hS, D.cardLine ℓ hℓ]
  have he' : e ∈ f.range := heq ▸ he
  obtain ⟨s, hs⟩ := he'
  exact ⟨(s : N × M).1, by
    have : (s : N × M) = ((s : N × M).1, e) := Prod.ext rfl hs
    rw [← this]
    exact s.2⟩

theorem PencilData.Orb_line_unique (hq : 2 ≤ Nat.card K) {S : Subgroup (N × M)} (hS : S ∈ Orb Γ)
    (hne : S ≠ N0 N M) {ℓ ℓ' : Subgroup M} (hℓ : ℓ ∈ Lines) (hℓ' : ℓ' ∈ Lines)
    (h1 : S ≤ Nsub N ℓ) (h2 : S ≤ Nsub N ℓ') : ℓ = ℓ' := by
  by_contra hne'
  have hinf := D.infLine ℓ hℓ ℓ' hℓ' hne'
  have h3 : S ≤ N0 N M := by
    have := le_inf h1 h2
    rw [Nsub_inf, hinf] at this
    exact this
  have h4 : S = ⊥ := by
    have := D.Orb_inf_N0 hS hne
    rwa [inf_eq_left.mpr h3] at this
  have h5 := D.Orb_card hS
  rw [h4, Subgroup.card_bot] at h5
  omega

end WithData

section Torus

variable {ℓ : Subgroup M}

@[expose] noncomputable def muMap (θ : ℓ ≃* Multiplicative K) (c : K) (e : ℓ) : ℓ :=
  θ.symm (Multiplicative.ofAdd (c * Multiplicative.toAdd (θ e)))

theorem theta_muMap (θ : ℓ ≃* Multiplicative K) (c : K) (e : ℓ) :
    Multiplicative.toAdd (θ (muMap θ c e)) = c * Multiplicative.toAdd (θ e) := by
  unfold muMap
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem muMap_mul_comp (θ : ℓ ≃* Multiplicative K) (c d : K) (e : ℓ) :
    muMap θ c (muMap θ d e) = muMap θ (c * d) e := by
  apply θ.injective
  apply Multiplicative.toAdd.injective
  rw [theta_muMap, theta_muMap, theta_muMap, mul_assoc]

theorem muMap_one (θ : ℓ ≃* Multiplicative K) (e : ℓ) : muMap θ 1 e = e := by
  apply θ.injective
  apply Multiplicative.toAdd.injective
  rw [theta_muMap, one_mul]

theorem apply_of_torus {θ : ℓ ≃* Multiplicative K} {c : K} {γ : MulAut (N × M)}
    (hN : ∀ n : N, γ (n, 1) = (n, 1))
    (hE : ∀ e : ℓ, γ (1, (e : M)) = (1, ((muMap θ c e : ℓ) : M))) (n : N) (e : ℓ) :
    γ (n, (e : M)) = (n, ((muMap θ c e : ℓ) : M)) := by
  have : ((n, (e : M)) : N × M) = (n, 1) * (1, (e : M)) := by simp
  rw [this, map_mul, hN, hE]
  simp

end Torus

section Free

variable (D : PencilData K N M Lines Γ) {ℓ : Subgroup M}
include D

theorem PencilData.free (hℓ : ℓ ∈ Lines) {θ : ℓ ≃* Multiplicative K} {S : Subgroup (N × M)}
    (hS : S ∈ Orb Γ) (hne : S ≠ N0 N M) (hle : S ≤ Nsub N ℓ) (hE : S ≠ Esub N ℓ) {ν : K}
    (hν : ν ≠ 1) {δ : MulAut (N × M)} (hδN : ∀ n : N, δ (n, 1) = (n, 1))
    (hδE : ∀ e : ℓ, δ (1, (e : M)) = (1, ((muMap θ ν e : ℓ) : M))) (hfix : mapA δ S = S) :
    False := by
  have hEle : Esub N ℓ ≤ S := by
    rintro ⟨n', m'⟩ hx
    obtain ⟨hn', hm'⟩ := mem_Esub.mp hx
    have hn'1 : n' = 1 := hn'
    subst hn'1
    set e'' : ℓ := ⟨m', hm'⟩ with he''
    set e : ℓ := θ.symm (Multiplicative.ofAdd ((ν - 1)⁻¹ * Multiplicative.toAdd (θ e''))) with he
    obtain ⟨n, hn⟩ := D.Orb_surj hS hne hℓ hle (e : M) e.2
    have h1 : δ (n, (e : M)) ∈ S := by
      have : δ (n, (e : M)) ∈ mapA δ S := mem_mapA_apply.mpr hn
      rwa [hfix] at this
    rw [apply_of_torus hδN hδE n e] at h1
    have h2 := S.mul_mem (S.inv_mem hn) h1
    have h3 : e⁻¹ * muMap θ ν e = e'' := by
      apply θ.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, theta_muMap, he, MulEquiv.apply_symm_apply,
        he'']
      have hν' : ν - 1 ≠ 0 := sub_ne_zero.mpr hν
      simp only [toAdd_ofAdd]
      field_simp
      ring
    have h4 : ((n, (e : M))⁻¹ * (n, ((muMap θ ν e : ℓ) : M)) : N × M) = (1, m') := by
      have : (((e⁻¹ * muMap θ ν e : ℓ)) : M) = m' := by rw [h3]
      simp only [Prod.inv_mk, Prod.mk_mul_mk, inv_mul_cancel]
      rw [← this]
      simp
    rwa [h4] at h2
  have hcard : Nat.card S ≤ Nat.card (Esub N ℓ) := by
    rw [card_Esub, D.Orb_card hS, D.cardLine ℓ hℓ]
  exact hE (Subgroup.eq_of_le_of_card_ge hEle hcard).symm

end Free

section Count

variable (D : PencilData K N M Lines Γ) {ℓ : Subgroup M}

@[expose] def Pset (Γ : Subgroup (MulAut (N × M))) (ℓ : Subgroup M) : Set (Subgroup (N × M)) :=
  {S | S ∈ Orb Γ ∧ S ≠ N0 N M ∧ S ≤ Nsub N ℓ}

@[expose] def Sset (Γ : Subgroup (MulAut (N × M))) (ℓ : Subgroup M) : Set (Subgroup (N × M)) :=
  {S | S ∈ Pset Γ ℓ ∧ S ≠ Esub N ℓ}

theorem mapA_N0_eq {γ : MulAut (N × M)} (hN : ∀ n : N, γ (n, 1) = (n, 1)) :
    mapA γ (N0 N M) = N0 N M := by
  apply le_antisymm
  · rintro x hx
    rw [mem_mapA] at hx
    obtain ⟨n, hn⟩ : ∃ n : N, γ.symm x = (n, 1) := ⟨(γ.symm x).1, Prod.ext rfl (mem_N0.mp hx)⟩
    have : x = γ (n, 1) := by rw [← hn]; simp
    rw [this, hN]
    exact mem_N0.mpr rfl
  · intro x hx
    have hx2 := mem_N0.mp hx
    have : x = (x.1, 1) := Prod.ext rfl hx2
    rw [mem_mapA]
    have h3 : γ (x.1, 1) = (x.1, 1) := hN x.1
    have h4 : γ.symm (x.1, 1) = (x.1, 1) := by
      rw [MulEquiv.symm_apply_eq]
      exact h3.symm
    rw [this, h4]
    exact mem_N0.mpr rfl

include D in
theorem PencilData.muMap_surj {θ : ℓ ≃* Multiplicative K} {c : K} (hc : c ≠ 0) (e' : ℓ) :
    ∃ e : ℓ, muMap θ c e = e' := by
  refine ⟨muMap θ c⁻¹ e', ?_⟩
  rw [muMap_mul_comp, mul_inv_cancel₀ hc, muMap_one]

include D in
theorem PencilData.torus_le {θ : ℓ ≃* Multiplicative K} {c : K} {γ : MulAut (N × M)}
    (hN : ∀ n : N, γ (n, 1) = (n, 1))
    (hE : ∀ e : ℓ, γ (1, (e : M)) = (1, ((muMap θ c e : ℓ) : M))) :
    mapA γ (Nsub N ℓ) ≤ Nsub N ℓ := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' := mem_Nsub.mp hy
  have := apply_of_torus hN hE y.1 ⟨y.2, hy'⟩
  show γ y ∈ _
  rw [show y = (y.1, ((⟨y.2, hy'⟩ : ℓ) : M)) from rfl, this]
  exact mem_Nsub.mpr (muMap θ c _).2

include D in
theorem PencilData.torus_Esub {θ : ℓ ≃* Multiplicative K} {c : K} (hc : c ≠ 0)
    {γ : MulAut (N × M)} (hE : ∀ e : ℓ, γ (1, (e : M)) = (1, ((muMap θ c e : ℓ) : M))) :
    mapA γ (Esub N ℓ) = Esub N ℓ := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hy1, hy2⟩ := mem_Esub.mp hy
    show γ y ∈ _
    have hy' : y = (1, ((⟨y.2, hy2⟩ : ℓ) : M)) := Prod.ext hy1 rfl
    rw [hy', hE]
    exact mem_Esub.mpr ⟨rfl, (muMap θ c _).2⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := mem_Esub.mp hx
    obtain ⟨e, he⟩ := D.muMap_surj (θ := θ) hc ⟨x.2, hx2⟩
    refine ⟨(1, (e : M)), mem_Esub.mpr ⟨rfl, e.2⟩, ?_⟩
    show γ (1, (e : M)) = x
    rw [hE, he]
    exact Prod.ext hx1.symm rfl

end Count

section Count2

variable [Finite K] (D : PencilData K N M Lines Γ) {ℓ : Subgroup M}
include D

theorem PencilData.torus_mem_Sset (hℓ : ℓ ∈ Lines) {θ : ℓ ≃* Multiplicative K} {c : K}
    (hc : c ≠ 0) {γ : MulAut (N × M)} (hγΓ : γ ∈ Γ) (hN : ∀ n : N, γ (n, 1) = (n, 1))
    (hE : ∀ e : ℓ, γ (1, (e : M)) = (1, ((muMap θ c e : ℓ) : M))) {S : Subgroup (N × M)}
    (hS : S ∈ Sset Γ ℓ) : mapA γ S ∈ Sset Γ ℓ := by
  obtain ⟨⟨hSO, hSne, hSle⟩, hSE⟩ := hS
  refine ⟨⟨mapA_mem_Orb hSO hγΓ, ?_, ?_⟩, ?_⟩
  · intro h
    apply hSne
    rw [← mapA_N0_eq hN] at h
    exact mapA_inj γ h
  · exact ((mapA_le_iff γ).mpr hSle).trans (D.torus_le hN hE)
  · intro h
    apply hSE
    rw [← D.torus_Esub hc hE] at h
    exact mapA_inj γ h

theorem PencilData.exists_ne_zero_one (hq : 4 ≤ Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  haveI := Fintype.ofFinite K
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
    intro c _
    by_cases hc : c = 0
    · simp [hc]
    · simp [h c hc]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

theorem PencilData.not_mem_of_Sset (hq : 4 ≤ Nat.card K) (hℓ : ℓ ∈ Lines)
    {S : Subgroup (N × M)} (hS : S ∈ Sset Γ ℓ) {e₀ : M} (he₀ : e₀ ∈ ℓ) (hne : e₀ ≠ 1) :
    (1, e₀) ∉ S := by
  intro h1
  obtain ⟨θ, hT⟩ := D.torus ℓ hℓ
  obtain ⟨c, hc0, hc1⟩ := D.exists_ne_zero_one hq
  obtain ⟨γ, hγΓ, hγN, hγE⟩ := hT c hc0
  have hγE' : ∀ e : ℓ, γ (1, (e : M)) = (1, ((muMap θ c e : ℓ) : M)) := hγE
  have hS' : mapA γ S ∈ Sset Γ ℓ := D.torus_mem_Sset hℓ hc0 hγΓ hγN hγE' hS
  have hne' : mapA γ S ≠ S := by
    intro h
    exact D.free hℓ hS.1.1 hS.1.2.1 hS.1.2.2 hS.2 hc1 hγN hγE' h
  have hinf := D.Orb_inf hS'.1.1 hS.1.1 hne'
  set e₀' : ℓ := ⟨e₀, he₀⟩ with he₀'
  have hc1' : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  set a₀ : K := Multiplicative.toAdd (θ e₀') with ha₀
  set e : ℓ := θ.symm (Multiplicative.ofAdd (a₀ * (c - 1)⁻¹)) with he
  obtain ⟨n, hn⟩ := D.Orb_surj hS.1.1 hS.1.2.1 hℓ hS.1.2.2 (e : M) e.2
  have h2 : (n, (e : M) * e₀) ∈ S := by
    have := S.mul_mem hn h1
    simpa using this
  have h3 : (n, ((muMap θ c e : ℓ) : M)) ∈ mapA γ S := by
    have := (mem_mapA_apply (γ := γ)).mpr hn
    rwa [apply_of_torus hγN hγE' n e] at this
  have h4 : muMap θ c e = e * e₀' := by
    apply θ.injective
    apply Multiplicative.toAdd.injective
    rw [theta_muMap, map_mul, toAdd_mul, he, MulEquiv.apply_symm_apply, ← ha₀]
    simp only [toAdd_ofAdd]
    field_simp
    ring
  have h5 : (n, (e : M) * e₀) ∈ mapA γ S ⊓ S := by
    refine ⟨?_, h2⟩
    have : (((muMap θ c e : ℓ)) : M) = (e : M) * e₀ := by rw [h4]; rfl
    rwa [this] at h3
  rw [hinf, Subgroup.mem_bot] at h5
  have h6 : (e : M) * e₀ = 1 := congrArg Prod.snd h5
  have h7 : e * e₀' = 1 := Subtype.ext h6
  have h8 : Multiplicative.toAdd (θ e) + a₀ = 0 := by
    have := congrArg (fun x => Multiplicative.toAdd (θ x)) h7
    simpa [map_mul, toAdd_mul] using this
  rw [he, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h8
  have h9 : a₀ = 0 := by
    have : a₀ * (c - 1)⁻¹ * c = 0 := by
      have : a₀ * (c - 1)⁻¹ + a₀ = a₀ * (c - 1)⁻¹ * c := by field_simp; ring
      rw [← this]
      exact h8
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd (inv_eq_zero.mp h') hc1'
    · exact absurd h hc0
  have h10 : θ e₀' = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact h9
  have h11 : e₀' = 1 := θ.injective (h10.trans (map_one θ).symm)
  exact hne (congrArg Subtype.val h11)

theorem PencilData.exists_ne_one_of_line (hq : 4 ≤ Nat.card K) (hℓ : ℓ ∈ Lines) :
    ∃ e₀ : M, e₀ ∈ ℓ ∧ e₀ ≠ 1 := by
  have hbot : ℓ ≠ ⊥ := by
    intro h
    have := D.cardLine ℓ hℓ
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

theorem PencilData.Sset_card (hq : 4 ≤ Nat.card K) (hℓ : ℓ ∈ Lines) :
    (Sset Γ ℓ).ncard = 0 ∨ (Sset Γ ℓ).ncard = Nat.card K - 1 := by
  classical
  have hfin : (Sset Γ ℓ).Finite := Set.toFinite _
  obtain ⟨e₀, he₀, he₀1⟩ := D.exists_ne_one_of_line hq hℓ
  by_cases hemp : Sset Γ ℓ = ∅
  · left
    rw [hemp, Set.ncard_empty]
  right
  obtain ⟨S₀, hS₀⟩ := Set.nonempty_iff_ne_empty.mpr hemp
  obtain ⟨θ, hT⟩ := D.torus ℓ hℓ
  have hup : (Sset Γ ℓ).ncard ≤ Nat.card K - 1 := by
    let ev : Subgroup (N × M) → N := fun S =>
      if h : ∃ n : N, (n, e₀) ∈ S then h.choose else 1
    have hev : ∀ S ∈ Sset Γ ℓ, (ev S, e₀) ∈ S := by
      intro S hS
      obtain ⟨n, hn⟩ := D.Orb_surj hS.1.1 hS.1.2.1 hℓ hS.1.2.2 e₀ he₀
      have h : ∃ n : N, (n, e₀) ∈ S := ⟨n, hn⟩
      show (if h : ∃ n : N, (n, e₀) ∈ S then h.choose else 1, e₀) ∈ S
      rw [dif_pos h]
      exact h.choose_spec
    have hmaps : Set.MapsTo ev (Sset Γ ℓ) {n : N | n ≠ 1} := by
      intro S hS h1
      have := hev S hS
      rw [h1] at this
      exact D.not_mem_of_Sset hq hℓ hS he₀ he₀1 this
    have hinj : Set.InjOn ev (Sset Γ ℓ) := by
      intro S₁ h₁ S₂ h₂ h12
      by_contra hne
      have hinf := D.Orb_inf h₁.1.1 h₂.1.1 hne
      have h3 : (ev S₁, e₀) ∈ S₁ ⊓ S₂ := ⟨hev S₁ h₁, by rw [h12]; exact hev S₂ h₂⟩
      rw [hinf, Subgroup.mem_bot] at h3
      exact he₀1 (congrArg Prod.snd h3)
    have hcardT : ({n : N | n ≠ 1} : Set N).ncard = Nat.card K - 1 := by
      have : ({n : N | n ≠ 1} : Set N) = Set.univ \ {1} := by
        ext n
        simp
      rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ, D.cardN]
    rw [← hcardT]
    exact Set.ncard_le_ncard_of_injOn ev hmaps hinj (Set.toFinite _)
  have hlow : Nat.card K - 1 ≤ (Sset Γ ℓ).ncard := by
    choose! γ hγΓ hγN hγE using hT
    have hγE' : ∀ c : K, c ≠ 0 → ∀ e : ℓ,
        γ c (1, (e : M)) = (1, ((muMap θ c e : ℓ) : M)) := fun c hc e => hγE c hc e
    let f : K → Subgroup (N × M) := fun c => mapA (γ c) S₀
    have hmaps : Set.MapsTo f {c : K | c ≠ 0} (Sset Γ ℓ) := by
      intro c hc
      exact D.torus_mem_Sset hℓ hc (hγΓ c hc) (hγN c hc) (hγE' c hc) hS₀
    have hinj : Set.InjOn f {c : K | c ≠ 0} := by
      intro c hc c' hc' hcc
      by_contra hne
      have hc0 : c ≠ 0 := hc
      have hc'0 : c' ≠ 0 := hc'
      have hν : c * c'⁻¹ ≠ 1 := by
        intro h
        apply hne
        field_simp at h
        exact h
      have hfix : mapA ((γ c')⁻¹ * γ c) S₀ = S₀ := by
        rw [mapA_mul]
        have : mapA (γ c) S₀ = mapA (γ c') S₀ := hcc
        rw [this, mapA_inv_mapA]
      refine D.free hℓ hS₀.1.1 hS₀.1.2.1 hS₀.1.2.2 hS₀.2 (θ := θ) hν (δ := (γ c')⁻¹ * γ c) ?_ ?_
        hfix
      · intro n
        have h1 : (γ c')⁻¹ (n, 1) = (n, 1) := by
          have : ((γ c')⁻¹ : MulAut (N × M)) = (γ c').symm := rfl
          rw [this, MulEquiv.symm_apply_eq]
          exact (hγN c' hc'0 n).symm
        show (γ c')⁻¹ (γ c (n, 1)) = (n, 1)
        rw [hγN c hc0 n, h1]
      · intro e
        show (γ c')⁻¹ (γ c (1, (e : M))) = _
        rw [hγE' c hc0 e]
        have : ((γ c')⁻¹ : MulAut (N × M)) = (γ c').symm := rfl
        have hcc' : c' * (c * c'⁻¹) = c := by field_simp
        rw [this, MulEquiv.symm_apply_eq, hγE' c' hc'0 (muMap θ (c * c'⁻¹) e), muMap_mul_comp,
          hcc']
    have hcardK : ({c : K | c ≠ 0} : Set K).ncard = Nat.card K - 1 := by
      have : ({c : K | c ≠ 0} : Set K) = Set.univ \ {0} := by
        ext c
        simp
      rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ 0), Set.ncard_univ]
    rw [← hcardK]
    exact Set.ncard_le_ncard_of_injOn f hmaps hinj hfin
  omega

end Count2

section Global

variable [Finite K] (D : PencilData K N M Lines Γ)
include D

theorem PencilData.Orb_mapA_iff {γ : MulAut (N × M)} (hγ : γ ∈ Γ) {S : Subgroup (N × M)} :
    mapA γ S ∈ Orb Γ ↔ S ∈ Orb Γ := by
  constructor
  · intro h
    have := mapA_mem_Orb h (Γ.inv_mem hγ)
    rwa [mapA_inv_mapA] at this
  · intro h
    exact mapA_mem_Orb h hγ

theorem PencilData.Esub_mem_iff {ℓ ℓ' : Subgroup M} (hℓ : ℓ ∈ Lines) (hℓ' : ℓ' ∈ Lines) :
    Esub N ℓ ∈ Orb Γ → Esub N ℓ' ∈ Orb Γ := by
  intro h
  obtain ⟨γ, hγΓ, -, hγE⟩ := D.trans ℓ hℓ ℓ' hℓ'
  rw [← hγE]
  exact mapA_mem_Orb h hγΓ

theorem PencilData.mapA_Nsub {ℓ ℓ' : Subgroup M} {γ : MulAut (N × M)}
    (hγN : ∀ n : N, γ (n, 1) = (n, 1)) (hγE : mapA γ (Esub N ℓ) = Esub N ℓ') :
    mapA γ (Nsub N ℓ) = Nsub N ℓ' := by
  rw [← N0_sup_Esub, ← N0_sup_Esub, mapA_sup, mapA_N0_eq hγN, hγE]

theorem PencilData.Pset_ncard_le {ℓ ℓ' : Subgroup M} (hℓ : ℓ ∈ Lines) (hℓ' : ℓ' ∈ Lines) :
    (Pset Γ ℓ).ncard ≤ (Pset Γ ℓ').ncard := by
  obtain ⟨γ, hγΓ, hγN, hγE⟩ := D.trans ℓ hℓ ℓ' hℓ'
  refine Set.ncard_le_ncard_of_injOn (mapA γ) ?_ ?_ (Set.toFinite _)
  · rintro S ⟨hSO, hSne, hSle⟩
    refine ⟨mapA_mem_Orb hSO hγΓ, ?_, ?_⟩
    · intro h
      apply hSne
      rw [← mapA_N0_eq hγN] at h
      exact mapA_inj γ h
    · rw [← D.mapA_Nsub hγN hγE]
      exact (mapA_le_iff γ).mpr hSle
  · intro S _ T _ h
    exact mapA_inj γ h

theorem PencilData.Pset_ncard_eq {ℓ ℓ' : Subgroup M} (hℓ : ℓ ∈ Lines) (hℓ' : ℓ' ∈ Lines) :
    (Pset Γ ℓ).ncard = (Pset Γ ℓ').ncard :=
  le_antisymm (D.Pset_ncard_le hℓ hℓ') (D.Pset_ncard_le hℓ' hℓ)

theorem PencilData.Esub_mem_Pset {ℓ : Subgroup M} (hq : 2 ≤ Nat.card K) (h : Esub N ℓ ∈ Orb Γ) :
    Esub N ℓ ∈ Pset Γ ℓ := by
  refine ⟨h, ?_, (Esub_le_Nsub).mpr le_rfl⟩
  intro h0
  have hN : 1 < Nat.card N := by rw [D.cardN]; omega
  haveI : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp hN
  obtain ⟨n, hn⟩ := exists_ne (1 : N)
  have hmem : ((n, 1) : N × M) ∈ Esub N ℓ := by
    rw [h0]
    exact mem_N0.mpr rfl
  exact hn (mem_Esub.mp hmem).1

open _root_.Classical in
theorem PencilData.Pset_ncard {ℓ : Subgroup M} (hq : 2 ≤ Nat.card K) :
    (Pset Γ ℓ).ncard = (Sset Γ ℓ).ncard + (if Esub N ℓ ∈ Orb Γ then 1 else 0) := by
  by_cases hE : Esub N ℓ ∈ Orb Γ
  · rw [if_pos hE]
    have : Pset Γ ℓ = insert (Esub N ℓ) (Sset Γ ℓ) := by
      ext S
      constructor
      · intro hS
        by_cases h : S = Esub N ℓ
        · left
          exact h
        · right
          exact ⟨hS, h⟩
      · rintro (rfl | ⟨hS, -⟩)
        · exact D.Esub_mem_Pset hq hE
        · exact hS
    rw [this, Set.ncard_insert_of_notMem (fun h => h.2 rfl) (Set.toFinite _)]
  · rw [if_neg hE]
    have : Pset Γ ℓ = Sset Γ ℓ := by
      ext S
      constructor
      · intro hS
        refine ⟨hS, ?_⟩
        rintro rfl
        exact hE hS.1
      · exact fun h => h.1
    rw [this]
    simp

theorem PencilData.exists_Pset_nonempty : ∃ ℓ ∈ Lines, (Pset Γ ℓ).Nonempty := by
  obtain ⟨γ, hγ, hne⟩ := D.nontriv
  obtain ⟨ℓ, hℓ, hle⟩ := D.lineOf γ hγ hne
  exact ⟨ℓ, hℓ, ⟨mapA γ (N0 N M), ⟨γ, hγ, rfl⟩, hne, hle⟩⟩

theorem PencilData.Pset_ncard_pos {ℓ : Subgroup M} (hℓ : ℓ ∈ Lines) : 1 ≤ (Pset Γ ℓ).ncard := by
  obtain ⟨ℓ₁, hℓ₁, hne⟩ := D.exists_Pset_nonempty
  rw [D.Pset_ncard_eq hℓ hℓ₁]
  exact Nat.succ_le_of_lt ((Set.ncard_pos (Set.toFinite _)).mpr hne)

theorem PencilData.Orb_ncard (hq : 2 ≤ Nat.card K) (c : ℕ)
    (hc : ∀ ℓ ∈ Lines, (Pset Γ ℓ).ncard = c) : (Orb Γ).ncard = 1 + Lines.card * c := by
  classical
  let F : Subgroup M → Finset (Subgroup (N × M)) := fun ℓ => (Set.toFinite (Pset Γ ℓ)).toFinset
  have hU : Orb Γ \ {N0 N M} = ↑(Lines.biUnion F) := by
    ext S
    simp only [Set.mem_diff, Set.mem_singleton_iff, Finset.coe_biUnion, Finset.mem_coe,
      Set.mem_iUnion, Set.Finite.mem_toFinset, F]
    constructor
    · rintro ⟨hS, hne⟩
      obtain ⟨ℓ, hℓ, hle⟩ := Orb_line D hS hne
      exact ⟨ℓ, hℓ, hS, hne, hle⟩
    · rintro ⟨ℓ, hℓ, hS, hne, -⟩
      exact ⟨hS, hne⟩
  have hdisj : ∀ x ∈ Lines, ∀ y ∈ Lines, x ≠ y → Disjoint (F x) (F y) := by
    intro x hx y hy hxy
    rw [Finset.disjoint_left]
    intro S hSx hSy
    simp only [F, Set.Finite.mem_toFinset] at hSx hSy
    exact hxy (D.Orb_line_unique hq hSx.1 hSx.2.1 hx hy hSx.2.2 hSy.2.2)
  have hcard : (Lines.biUnion F).card = Lines.card * c := by
    rw [Finset.card_biUnion hdisj]
    have : ∀ ℓ ∈ Lines, (F ℓ).card = c := fun ℓ hℓ => by
      simp only [F]
      rw [← Set.ncard_eq_toFinset_card (Pset Γ ℓ) (Set.toFinite _)]
      exact hc ℓ hℓ
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  have h1 := Set.ncard_diff_singleton_add_one (N0_mem_Orb (N := N) (M := M) (Γ := Γ))
    (Set.toFinite _)
  rw [hU, Set.ncard_coe_finset, hcard] at h1
  omega

@[expose] def Inside (Γ : Subgroup (MulAut (N × M))) (T : Subgroup (N × M)) :
    Set (Subgroup (N × M)) :=
  {S | S ∈ Orb Γ ∧ S ≤ T}

theorem PencilData.Inside_mapA {γ : MulAut (N × M)} (hγ : γ ∈ Γ) (T : Subgroup (N × M)) :
    Inside Γ (mapA γ T) = mapA γ '' Inside Γ T := by
  ext S
  constructor
  · rintro ⟨hS, hle⟩
    refine ⟨mapA γ⁻¹ S, ⟨(D.Orb_mapA_iff (Γ.inv_mem hγ)).mpr hS, ?_⟩, mapA_mapA_inv γ S⟩
    have := (mapA_le_iff γ⁻¹).mpr hle
    rwa [mapA_inv_mapA] at this
  · rintro ⟨S', ⟨hS', hle⟩, rfl⟩
    exact ⟨(D.Orb_mapA_iff hγ).mpr hS', (mapA_le_iff γ).mpr hle⟩

theorem PencilData.ncard_Inside_mapA {γ : MulAut (N × M)} (hγ : γ ∈ Γ) (T : Subgroup (N × M)) :
    (Inside Γ (mapA γ T)).ncard = (Inside Γ T).ncard := by
  rw [D.Inside_mapA hγ, Set.ncard_image_of_injective _ (fun S T h => mapA_inj γ h)]

theorem PencilData.Inside_Nsub {ℓ : Subgroup M} :
    Inside Γ (Nsub N ℓ) = insert (N0 N M) (Pset Γ ℓ) := by
  ext S
  constructor
  · rintro ⟨hS, hle⟩
    by_cases h : S = N0 N M
    · left
      exact h
    · right
      exact ⟨hS, h, hle⟩
  · rintro (rfl | ⟨hS, -, hle⟩)
    · exact ⟨N0_mem_Orb, N0_le_Nsub ℓ⟩
    · exact ⟨hS, hle⟩

theorem PencilData.ncard_Inside_Nsub {ℓ : Subgroup M} :
    (Inside Γ (Nsub N ℓ)).ncard = (Pset Γ ℓ).ncard + 1 := by
  rw [D.Inside_Nsub, Set.ncard_insert_of_notMem (fun h => h.2.1 rfl) (Set.toFinite _)]

theorem PencilData.N0_sup_eq_Nsub {ℓ : Subgroup M} (hℓ : ℓ ∈ Lines) {S : Subgroup (N × M)}
    (hS : S ∈ Pset Γ ℓ) : N0 N M ⊔ S = Nsub N ℓ := by
  obtain ⟨hSO, hSne, hSle⟩ := hS
  apply le_antisymm (sup_le (N0_le_Nsub ℓ) hSle)
  intro x hx
  have hx2 := mem_Nsub.mp hx
  obtain ⟨n', hn'⟩ := D.Orb_surj hSO hSne hℓ hSle x.2 hx2
  have h1 : ((x.1 * n'⁻¹, 1) : N × M) ∈ N0 N M := mem_N0.mpr rfl
  have := Subgroup.mul_mem_sup h1 hn'
  have e : ((x.1 * n'⁻¹, 1) : N × M) * (n', x.2) = x := Prod.ext (by simp) (by simp)
  rwa [e] at this

theorem PencilData.Inside_Esub_sup (hq : 2 ≤ Nat.card K) {ℓ₀ ℓ₁ : Subgroup M} (h₀ : ℓ₀ ∈ Lines)
    (h₁ : ℓ₁ ∈ Lines) (hne : ℓ₀ ≠ ℓ₁) (hE₀ : Esub N ℓ₀ ∈ Orb Γ) (hE₁ : Esub N ℓ₁ ∈ Orb Γ) :
    Inside Γ (Esub N (ℓ₀ ⊔ ℓ₁)) = {Esub N ℓ₀, Esub N ℓ₁} := by
  have hN : 1 < Nat.card N := by rw [D.cardN]; omega
  haveI : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp hN
  obtain ⟨n, hn⟩ := exists_ne (1 : N)
  ext T
  constructor
  · rintro ⟨hT, hle⟩
    have hTne : T ≠ N0 N M := by
      rintro rfl
      have : ((n, 1) : N × M) ∈ Esub N (ℓ₀ ⊔ ℓ₁) := hle (mem_N0.mpr rfl)
      exact hn (mem_Esub.mp this).1
    obtain ⟨ℓ, hℓ, hTℓ⟩ := D.Orb_line hT hTne
    have hTE : T ≤ Esub N ℓ := by
      intro x hx
      exact mem_Esub.mpr ⟨(mem_Esub.mp (hle hx)).1, mem_Nsub.mp (hTℓ hx)⟩
    have hTeq : T = Esub N ℓ :=
      Subgroup.eq_of_le_of_card_ge hTE (by rw [card_Esub, D.cardLine ℓ hℓ, D.Orb_card hT])
    have hℓle : ℓ ≤ ℓ₀ ⊔ ℓ₁ := by
      rw [← Esub_le_Esub (N := N)]
      rw [hTeq] at hle
      exact hle
    rcases D.lineSum ℓ₀ h₀ ℓ₁ h₁ hne ℓ hℓ hℓle with rfl | rfl
    · left
      exact hTeq
    · right
      exact hTeq
  · rintro (rfl | rfl)
    · exact ⟨hE₀, (Esub_le_Esub).mpr le_sup_left⟩
    · exact ⟨hE₁, (Esub_le_Esub).mpr le_sup_right⟩

theorem PencilData.E_case_false (hq : 4 ≤ Nat.card K) (hE : ∀ ℓ ∈ Lines, Esub N ℓ ∈ Orb Γ) :
    False := by
  have hq2 : 2 ≤ Nat.card K := by omega
  have hpow : 0 < Nat.card K ^ 2 := pow_pos (by omega) 2
  have hcard : 1 < Lines.card := by rw [D.cardLines]; omega
  obtain ⟨ℓ₀, h₀⟩ : Lines.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨ℓ₁, h₁, hne⟩ := Finset.exists_mem_ne hcard ℓ₀
  have hne' : ℓ₀ ≠ ℓ₁ := hne.symm
  have hEne : Esub N ℓ₀ ≠ Esub N ℓ₁ := by
    intro h
    exact hne' (le_antisymm ((Esub_le_Esub).mp h.le) ((Esub_le_Esub).mp h.ge))
  obtain ⟨k, hkΓ, hk⟩ := hE ℓ₀ h₀
  obtain ⟨T, hTdef⟩ : ∃ T, T = mapA k⁻¹ (Esub N ℓ₁) := ⟨_, rfl⟩
  have hmapT : mapA k T = Esub N ℓ₁ := by rw [hTdef, mapA_mapA_inv]
  have hT : T ∈ Orb Γ := by
    rw [hTdef]
    exact (D.Orb_mapA_iff (Γ.inv_mem hkΓ)).mpr (hE ℓ₁ h₁)
  have hTne : T ≠ N0 N M := by
    intro h
    rw [h] at hmapT
    exact hEne (hk.trans hmapT)
  obtain ⟨ℓ, hℓ, hTle⟩ := D.Orb_line hT hTne
  have hsup := D.N0_sup_eq_Nsub hℓ ⟨hT, hTne, hTle⟩
  have h1 := D.ncard_Inside_Nsub (ℓ := ℓ)
  have h2 := D.ncard_Inside_mapA hkΓ (N0 N M ⊔ T)
  have hmap : mapA k (N0 N M ⊔ T) = Esub N (ℓ₀ ⊔ ℓ₁) := by
    rw [mapA_sup, ← hk, hmapT, Esub_sup]
  rw [hmap, hsup, D.Inside_Esub_sup hq2 h₀ h₁ hne' (hE ℓ₀ h₀) (hE ℓ₁ h₁), Set.ncard_pair hEne,
    h1] at h2
  have hc : (Pset Γ ℓ).ncard = 1 := by omega
  have hPset : ∀ ℓ' ∈ Lines, Pset Γ ℓ' = {Esub N ℓ'} := by
    intro ℓ' hℓ'
    have hc' : (Pset Γ ℓ').ncard = 1 := by rw [D.Pset_ncard_eq hℓ' hℓ]; exact hc
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hc'
    have hmem := D.Esub_mem_Pset hq2 (hE ℓ' hℓ')
    rw [ha] at hmem ⊢
    rw [Set.mem_singleton_iff.mp hmem]
  have hα : ∀ S ∈ Orb Γ, S ≠ N0 N M → ∃ ℓ' ∈ Lines, S = Esub N ℓ' := by
    intro S hS hSne
    obtain ⟨ℓ', hℓ', hle⟩ := D.Orb_line hS hSne
    have : S ∈ Pset Γ ℓ' := ⟨hS, hSne, hle⟩
    rw [hPset ℓ' hℓ'] at this
    exact ⟨ℓ', hℓ', this⟩
  have hU₁ : ∀ S ∈ Orb Γ, S ≠ N0 N M → S ≤ Esub N ⊤ := by
    intro S hS hSne
    obtain ⟨ℓ', -, rfl⟩ := hα S hS hSne
    exact (Esub_le_Esub).mpr le_top
  have hkU : ∀ T' ∈ Orb Γ, T' ≠ Esub N ℓ₀ → T' ≤ mapA k (Esub N ⊤) := by
    intro T' hT' hne2
    have h3 : mapA k⁻¹ T' ∈ Orb Γ := (D.Orb_mapA_iff (Γ.inv_mem hkΓ)).mpr hT'
    have h4 : mapA k⁻¹ T' ≠ N0 N M := by
      intro h
      apply hne2
      rw [hk, ← h, mapA_mapA_inv]
    have h5 := (mapA_le_iff k).mpr (hU₁ _ h3 h4)
    rwa [mapA_mapA_inv] at h5
  have hEN0 : Esub N ℓ₀ ≠ N0 N M := (D.Esub_mem_Pset hq2 (hE ℓ₀ h₀)).2.1
  have hN0le : N0 N M ≤ mapA k (Esub N ⊤) := hkU _ N0_mem_Orb (Ne.symm hEN0)
  have hEle : ∀ ℓ' ∈ Lines, ℓ' ≠ ℓ₀ → Esub N ℓ' ≤ mapA k (Esub N ⊤) := by
    intro ℓ' hℓ' hne2
    refine hkU _ (hE ℓ' hℓ') fun h => hne2 ?_
    exact le_antisymm ((Esub_le_Esub).mp h.le) ((Esub_le_Esub).mp h.ge)
  have htop : mapA k (Esub N ⊤) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx2 : x.2 ∈ (⨆ ℓ' ∈ Lines, ⨆ (_ : ℓ' ≠ ℓ₀), ℓ') := by
      rw [D.span ℓ₀ h₀]
      exact Subgroup.mem_top _
    have hW' : (⨆ ℓ' ∈ Lines, ⨆ (_ : ℓ' ≠ ℓ₀), ℓ') ≤
        (mapA k (Esub N ⊤)).comap (MonoidHom.inr N M) := by
      refine iSup_le fun ℓ' => iSup_le fun hℓ' => iSup_le fun hne2 e he => ?_
      exact hEle ℓ' hℓ' hne2 (mem_Esub.mpr ⟨rfl, he⟩ : ((1, e) : N × M) ∈ Esub N ℓ')
    have h5 : ((1, x.2) : N × M) ∈ mapA k (Esub N ⊤) := hW' hx2
    have h6 : ((x.1, 1) : N × M) ∈ mapA k (Esub N ⊤) := hN0le (mem_N0.mpr rfl)
    have := (mapA k (Esub N ⊤)).mul_mem h6 h5
    simpa using this
  have hU1top : (Esub N (⊤ : Subgroup M) : Subgroup (N × M)) = ⊤ := by
    apply mapA_inj k
    rw [htop]
    ext x
    simp [mem_mapA]
  have hN : 1 < Nat.card N := by rw [D.cardN]; omega
  haveI : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp hN
  obtain ⟨n, hn⟩ := exists_ne (1 : N)
  have : ((n, 1) : N × M) ∈ Esub N ⊤ := by rw [hU1top]; exact Subgroup.mem_top _
  exact hn (mem_Esub.mp this).1

end Global

section AutBound

theorem orderOf_mulAut_ne_prime {A : Type} [CommGroup A] [Finite A] (hA : ∀ x : A, x * x = 1)
    {d : ℕ} (hd : Nat.card A = 2 ^ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : d < orderOf (2 : ZMod p)) (g : MulAut A) : orderOf g ≠ p := by
  have h2 : ∀ x : Additive A, (2 : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    simp [two_nsmul, hA (Additive.toMul x)]
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule h2
  haveI : Finite (Additive A) := inferInstanceAs (Finite A)
  haveI : FiniteDimensional (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive A) = d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_zmod] at this
    have h3 : Nat.card (Additive A) = 2 ^ d := hd
    rw [h3] at this
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  let Φ : MulAut A →* ((Additive A) ≃ₗ[ZMod 2] (Additive A)) :=
    { toFun := fun g => LinearEquiv.ofBijective
        (AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive g : Additive A ≃+ Additive A))
        ⟨(MulEquiv.toAdditive g).injective, (MulEquiv.toAdditive g).surjective⟩
      map_one' := by
        ext x
        rfl
      map_mul' := fun g h => by
        ext x
        rfl }
  have hΦ : Function.Injective Φ := by
    intro g h hgh
    ext x
    have := congrArg (fun L => L (Additive.ofMul x)) hgh
    exact Additive.ofMul.injective this
  intro hg
  have := orderOf_injective Φ hΦ g
  exact orderOf_ne_prime_of_finrank_lt hp hp2 (by rw [hfin]; exact hlt) (Φ g) (this ▸ hg)

end AutBound

section Final

variable {K : Type} [Field K] [Finite K] {N M : Type} [CommGroup N] [CommGroup M] [Finite N]
  [Finite M] {Lines : Finset (Subgroup M)} {Γ : Subgroup (MulAut (N × M))}
  (D : PencilData K N M Lines Γ)
include D

theorem PencilData.Orb_ncard_dvd : (Orb Γ).ncard ∣ Nat.card Γ := by
  letI : MulAction Γ (Subgroup (N × M)) :=
    { smul := fun γ S => mapA γ S
      one_smul := fun S => mapA_one S
      mul_smul := fun γ δ S => mapA_mul γ δ S }
  have hO : (MulAction.orbit Γ (N0 N M) : Set (Subgroup (N × M))) = Orb Γ := by
    ext S
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨⟨γ, hγ⟩, rfl⟩
  rw [← hO, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem PencilData.false_of_data {s : ℕ} (hs : 2 ≤ s) (hq : Nat.card K = 2 ^ s) : False := by
  have hq4 : 4 ≤ Nat.card K := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  by_cases hE : ∃ ℓ ∈ Lines, Esub N ℓ ∈ Orb Γ
  · obtain ⟨ℓ, hℓ, hEℓ⟩ := hE
    exact D.E_case_false hq4 (fun ℓ' hℓ' => D.Esub_mem_iff hℓ hℓ' hEℓ)
  push Not at hE
  have hc : ∀ ℓ ∈ Lines, (Pset Γ ℓ).ncard = Nat.card K - 1 := by
    intro ℓ hℓ
    have h1 := D.Pset_ncard (ℓ := ℓ) (by omega)
    rw [if_neg (hE ℓ hℓ), add_zero] at h1
    have h2 := D.Pset_ncard_pos hℓ
    rcases D.Sset_card hq4 hℓ with h | h <;> omega
  have hOrb := D.Orb_ncard (by omega) _ hc
  rw [D.cardLines] at hOrb
  obtain ⟨p, hp, hp2, hord⟩ := exists_prime_orderOf_two_eq (e := 6 * s) (by omega) (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ (Orb Γ).ncard := by
    rw [← ZMod.natCast_eq_zero_iff]
    set t : ZMod p := (2 : ZMod p) ^ s with ht
    have h6 : t ^ 6 = 1 := by
      rw [ht, ← pow_mul, mul_comm, ← hord]
      exact pow_orderOf_eq_one _
    have h3 : t ^ 3 ≠ 1 := by
      rw [ht, ← pow_mul]
      exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; omega)
    have h2 : t ^ 2 ≠ 1 := by
      rw [ht, ← pow_mul]
      exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; omega)
    have h3' : t ^ 3 + 1 = 0 := by
      have : (t ^ 3 - 1) * (t ^ 3 + 1) = 0 := by linear_combination h6
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) h3
      · exact h
    have h4 : t ^ 2 - t + 1 = 0 := by
      have : (t + 1) * (t ^ 2 - t + 1) = 0 := by linear_combination h3'
      rcases mul_eq_zero.mp this with h | h
      · exfalso
        have hsq : t ^ 2 - 1 = 0 := by linear_combination (t - 1) * h
        exact h2 (sub_eq_zero.mp hsq)
      · exact h
    have hqt : ((Nat.card K : ℕ) : ZMod p) = t := by rw [hq, ht]; push_cast; rfl
    rw [hOrb]
    have hq1 : 1 ≤ Nat.card K := by omega
    push_cast [Nat.cast_sub hq1]
    rw [hqt]
    linear_combination t * h4
  have hΓ := dvd_trans hpdvd D.Orb_ncard_dvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Γ) p hΓ
  have hA : ∀ x : N × M, x * x = 1 := fun x => Prod.ext (D.N2 x.1) (D.M2 x.2)
  have hd : Nat.card (N × M) = 2 ^ (5 * s) := by
    rw [Nat.card_prod, D.cardN, D.cardM, hq, ← pow_mul, ← pow_add]
    congr 1
    ring
  exact orderOf_mulAut_ne_prime hA hd hp hp2 (by rw [hord]; omega) (g : MulAut (N × M))
    (by rw [Subgroup.orderOf_coe]; exact hg)

end Final

end Pencil

end HS6

end CFSG.RankThree.GF2n.Stroth80
