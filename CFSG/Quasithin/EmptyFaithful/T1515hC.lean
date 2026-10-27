module

public import CFSG.Quasithin.EmptyFaithful.T1515hB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def a7Data {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    {β : ↥(blockU L) →* Multiplicative (AltHeart 7)}
    {γ : ↥(blockU L) →* Multiplicative ↥(evenWeight 7)} (hstr : A7Str L α β)
    (hγ : A7Gamma L α β γ) : CFSG.QuasithinUnique.L246A7.Alt7Data L where
  α := α
  hα := hstr.1
  hker := hstr.2.1
  β := γ
  hβ := hγ.surj
  hβker := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hγ.ker u
  hβeq := fun ℓ u v h i => by
    have := hγ.equi ℓ u v h
    rw [this]
    rfl

@[expose] def a7ConjG (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (blockU L : Set G))
    (x : ↥(blockU L)) : ↥(blockU L) :=
  ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp x.2⟩

omit [Finite G] in
theorem a7ConjG_mul (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (blockU L : Set G))
    (x y : ↥(blockU L)) : a7ConjG L hg (x * y) = a7ConjG L hg x * a7ConjG L hg y :=
  Subtype.ext (by simp only [a7ConjG, Subgroup.coe_mul]; group)

@[expose] noncomputable def a7Phi {L : Subgroup G}
    (γ : ↥(blockU L) →* Multiplicative ↥(evenWeight 7)) {g : G}
    (hg : g ∈ Subgroup.normalizer (blockU L : Set G)) (σ : Equiv.Perm (Fin 7)) :
    ↥(blockU L) →* Multiplicative ↥(evenWeight 7) where
  toFun x := Multiplicative.ofAdd (permWeight 7 σ⁻¹ (Multiplicative.toAdd (γ (a7ConjG L hg x))))
  map_one' := by
    have : a7ConjG L hg (1 : ↥(blockU L)) = 1 := Subtype.ext (by simp [a7ConjG])
    rw [this, map_one]
    exact congrArg Multiplicative.ofAdd (a7_permWeight_zero _)
  map_mul' x y := by
    rw [a7ConjG_mul, map_mul, toAdd_mul, a7_permWeight_add]
    rfl

theorem a7SigmaStep : A7SigmaStep := by
  intro G _ _ L α β hshort hstr P d hP hd
  obtain ⟨γ, hγ⟩ := a7_exists_gamma hstr
  obtain ⟨σ₀, h3sw, hcent⟩ := a7_exists_sigma0 hP hd
  refine ⟨σ₀, h3sw, ?_⟩
  intro g hgN hgY
  set D := a7Data hstr hγ with hD
  set σ : Equiv.Perm (Fin 7) := CFSG.QuasithinUnique.L246A7.rho D g with hσ
  have hconj : ∀ ℓ : ↥L, ((α ⟨g * ℓ * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN ℓ).mp ℓ.2⟩ :
      alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = σ * (α ℓ : Equiv.Perm (Fin 7)) * σ⁻¹ :=
    fun ℓ => CFSG.QuasithinUnique.L246A7.rho_conj D hgN ℓ.2
  have hind : A7InducesPerm L α g σ := by
    intro ℓ ℓ' h
    have : ℓ' = ⟨g * ℓ * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN ℓ).mp ℓ.2⟩ := Subtype.ext h
    rw [this]
    exact hconj ℓ
  have hC3 : ¬ 3 ∣ Nat.card α.ker := a7_hC3 hstr
  have hσcomm : ∀ a : Equiv.Perm (Fin 7), a ∈ alternatingGroup (Fin 7) → StabilizesPartition a P →
      a ^ 3 = 1 → σ * a = a * σ := by
    intro a ha hst ha3
    obtain ⟨t, hta, htmem⟩ := a7_exists_Y1_gen hstr.1 hC3 ha hst ha3
    have hcomm : (t : G) * g = g * t := Subgroup.mem_centralizer_iff.mp hgY t htmem
    have h1 := hconj t
    have e : (⟨g * t * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN t).mp t.2⟩ : ↥L) = t :=
      Subtype.ext (by
        show g * (t : G) * g⁻¹ = t
        rw [← hcomm]
        group)
    rw [e, hta] at h1
    calc σ * a = (σ * a * σ⁻¹) * σ := by group
      _ = a * σ := by rw [← h1]
  refine ⟨σ, hcent σ hσcomm, hind, ?_⟩
  have hgU : g ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU hgN
  have hgZ : g ∈ Subgroup.normalizer (blockZ L : Set G) := C1.mem_normalizer_blockZ hgN
  have hker : γ.ker ≤ (a7Phi γ hgU σ).ker := by
    intro x hx
    have hxZ : (x : G) ∈ blockZ L := (hγ.ker x).mp hx
    have hgxZ : g * (x : G) * g⁻¹ ∈ blockZ L := (Subgroup.mem_normalizer_iff.mp hgZ x).mp hxZ
    have h1 : γ (a7ConjG L hgU x) = 1 := (hγ.ker _).mpr hgxZ
    show Multiplicative.ofAdd (permWeight 7 σ⁻¹ (Multiplicative.toAdd (γ (a7ConjG L hgU x)))) = 1
    rw [h1]
    exact congrArg Multiplicative.ofAdd (a7_permWeight_zero _)
  have hact : ∀ (a : alternatingGroup (Fin 7)) (x : ↥(blockU L)), ∃ x' : ↥(blockU L),
      Multiplicative.toAdd (γ x') =
          permWeight 7 (a : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (γ x)) ∧
        Multiplicative.toAdd (a7Phi γ hgU σ x') =
          permWeight 7 (a : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (a7Phi γ hgU σ x)) := by
    intro a x
    obtain ⟨ℓ, rfl⟩ := hstr.1 a
    refine ⟨a7ConjU L ℓ x, hγ.equi ℓ x _ rfl, ?_⟩
    set ℓ' : ↥L := ⟨g * ℓ * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN ℓ).mp ℓ.2⟩ with hℓ'
    have e : a7ConjG L hgU (a7ConjU L ℓ x) = a7ConjU L ℓ' (a7ConjG L hgU x) :=
      Subtype.ext (by simp only [a7ConjG, a7ConjU, hℓ']; group)
    show permWeight 7 σ⁻¹ (Multiplicative.toAdd (γ (a7ConjG L hgU (a7ConjU L ℓ x)))) =
      permWeight 7 (α ℓ : Equiv.Perm (Fin 7))
        (permWeight 7 σ⁻¹ (Multiplicative.toAdd (γ (a7ConjG L hgU x))))
    rw [e, hγ.equi ℓ' (a7ConjG L hgU x) _ rfl, hconj ℓ, ← a7_permWeight_mul, ← a7_permWeight_mul]
    congr 1
    group
  have hne : ¬ ∀ x, a7Phi γ hgU σ x = 1 := by
    intro h1
    have hall : ∀ x : ↥(blockU L), γ (a7ConjG L hgU x) = 1 := by
      intro x
      have h2 : permWeight 7 σ⁻¹ (Multiplicative.toAdd (γ (a7ConjG L hgU x))) = 0 :=
        ofAdd_eq_one.mp (h1 x)
      have h3 : Multiplicative.toAdd (γ (a7ConjG L hgU x)) = 0 := by
        have := congrArg (permWeight 7 σ) h2
        rw [← a7_permWeight_mul, mul_inv_cancel, a7_permWeight_one, a7_permWeight_zero] at this
        exact this
      exact Multiplicative.toAdd.injective h3
    have hallU : ∀ u : ↥(blockU L), γ u = 1 := by
      intro u
      have hu' : g⁻¹ * (u : G) * g⁻¹⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem hgU) u).mp u.2
      have := hall ⟨g⁻¹ * (u : G) * g⁻¹⁻¹, hu'⟩
      have e : a7ConjG L hgU ⟨g⁻¹ * (u : G) * g⁻¹⁻¹, hu'⟩ = u :=
        Subtype.ext (by simp only [a7ConjG]; group)
      rwa [e] at this
    obtain ⟨u, hu⟩ := hγ.surj (Multiplicative.ofAdd (a7PairVec 0 1))
    have := hallU u
    rw [hu] at this
    exact a7PairVec_ne_zero (ofAdd_eq_one.mp this)
  have hΦγ : ∀ x, a7Phi γ hgU σ x = γ x := by
    rcases a7_schur_hom γ (a7Phi γ hgU σ) hγ.surj hker hact with h0 | h1
    · exact absurd h0 hne
    · exact h1
  intro x y hxy z hz
  have hy : y = a7ConjG L hgU x := Subtype.ext hxy
  have hzx : z = Multiplicative.toAdd (γ x) := by
    have h1 : (QuotientAddGroup.mk z : AltHeart 7) =
        QuotientAddGroup.mk (Multiplicative.toAdd (γ x)) := by rw [hz, hγ.mk_eq x]
    have := congrArg a7E h1
    rwa [a7E_mk, a7E_mk] at this
  have h1 : Multiplicative.toAdd (γ (a7ConjG L hgU x)) = permWeight 7 σ z := by
    have := hΦγ x
    have h2 : permWeight 7 σ⁻¹ (Multiplicative.toAdd (γ (a7ConjG L hgU x))) = z := by
      rw [hzx, ← this]
      rfl
    rw [← h2, ← a7_permWeight_mul, mul_inv_cancel, a7_permWeight_one]
  rw [← hγ.mk_eq y, hy, h1]

end CFSG.Quasithin
