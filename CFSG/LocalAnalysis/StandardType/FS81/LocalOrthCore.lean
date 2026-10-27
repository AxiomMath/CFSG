module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthMono
public import CFSG.LocalAnalysis.StandardType.FS81.OrthParity
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Multiplicative QuadraticMap Module CFSG.Open CFSG.Assembly
  CFSG.RankThree.Classical2 CFSG.StandardType.SpCoord CFSG.StandardType.NbrOrth

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def OmegaAutIsometric (Q : QuadraticForm (ZMod 2) V) : Prop :=
  ∀ α : MulAut ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
    ∃ h ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ x,
      ((α x : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
        V ≃ₗ[ZMod 2] V) = h * (x : V ≃ₗ[ZMod 2] V) * h⁻¹

variable {G : Type} [Group G]

private theorem closure_singleton_isElemAbelian {G : Type} [Group G] {K A : Subgroup G} {k : G}
    (hmax : IsMaxElemAb3 K A) (hkK : k ∈ K)
    (hkcomm : ∀ a ∈ A, a * k = k * a) (hk3 : k ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.closure ((A : Set G) ∪ {k})) := by
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a (ha | ha) b (hb | hb)
    · exact IsElemAbelian.comm hmax.2.1 ha hb
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact hkcomm a ha
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact (hkcomm b hb).symm
    · rw [Set.mem_singleton_iff] at ha hb
      subst ha
      subst hb
      rfl
  · rintro a (ha | ha)
    · exact hmax.2.1.2 a ha
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hk3

private theorem mem_of_closure_singleton_of_isMaxElemAb3 {G : Type} [Group G]
    {K A : Subgroup G} {k : G} (hmax : IsMaxElemAb3 K A) (hkK : k ∈ K)
    (hkcomm : ∀ a ∈ A, a * k = k * a) (hk3 : k ^ 3 = 1) : k ∈ A := by
  have hE'ab : IsElemAbelian 3 (Subgroup.closure ((A : Set G) ∪ {k})) :=
    closure_singleton_isElemAbelian hmax hkK hkcomm hk3
  have hE'K : Subgroup.closure ((A : Set G) ∪ {k}) ≤ K := by
    rw [Subgroup.closure_le]
    rintro a (ha | ha)
    · exact hmax.1 ha
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hkK
  have hle : A ≤ Subgroup.closure ((A : Set G) ∪ {k}) := fun a ha =>
    Subgroup.subset_closure (Or.inl ha)
  have hEq := hmax.2.2 _ hE'K hE'ab hle
  exact hEq ▸ Subgroup.subset_closure (Or.inr (Set.mem_singleton k))

private theorem card_orthImage {Q : QuadraticForm (ZMod 2) V} {K E : Subgroup G}
    (φ : ↥K ≃* ↥(orthDerived Q)) :
    Nat.card ↥(((E ⊓ K).subgroupOf K).map ((orthDerived Q).subtype.comp φ.toMonoidHom)) =
      Nat.card ↥(E ⊓ K) := by
  have h2 : Nat.card ↥((E ⊓ K).subgroupOf K) = Nat.card ↥(E ⊓ K) := by
    rw [← Subgroup.card_subtype K ((E ⊓ K).subgroupOf K),
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : E ⊓ K ≤ K)]
  exact (Subgroup.card_map_of_injective
    (f := (orthDerived Q).subtype.comp φ.toMonoidHom)
    ((Subgroup.subtype_injective (orthDerived Q)).comp φ.injective)).trans h2

private theorem card_coords (m : ℕ) :
    Nat.card (Fin m → Multiplicative (ZMod 3)) = 3 ^ m := by
  rw [Nat.card_fun, Nat.card_fin]
  congr 1
  rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod 3)), Nat.card_zmod]

private theorem exists_ne_one_of_card_eq_pow {G : Type} [Group G] {E : Subgroup G} {n : ℕ}
    (hcard : Nat.card ↥E = 3 ^ n) (hn : 1 ≤ n) : ∃ b ∈ E, b ≠ 1 := by
  have h3 : 3 ≤ Nat.card ↥E := by
    rw [hcard]
    exact le_self_pow (by norm_num : 1 ≤ 3) (by omega : n ≠ 0)
  have hne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3
    omega
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨b, b.2, fun h => hb1 (Subtype.ext h)⟩

private theorem inv_mem_inf_of_commute {Q : QuadraticForm (ZMod 2) V} {K E : Subgroup G}
    (φ : ↥K ≃* ↥(orthDerived Q)) (hmax : IsMaxElemAb3 K (E ⊓ K))
    {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : A = ((E ⊓ K).subgroupOf K).map ((orthDerived Q).subtype.comp φ.toMonoidHom))
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ orthDerived Q) (hg3 : g ^ 3 = 1)
    (hgc : ∀ c ∈ A, g * c = c * g) :
    ((φ.symm ⟨g, hg⟩ : ↥K) : G) ∈ E ⊓ K := by
  classical
  let k : ↥K := φ.symm ⟨g, hg⟩
  have hφk : φ k = ⟨g, hg⟩ := MulEquiv.apply_symm_apply φ ⟨g, hg⟩
  have hkcomm : ∀ a ∈ (E ⊓ K : Subgroup G), a * (k : G) = (k : G) * a := by
    intro a ha
    let x : ↥K := ⟨a, ha.2⟩
    have hxA : ((φ x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈ A := by
      rw [hA, Subgroup.mem_map]
      exact ⟨x, ⟨ha.1, x.2⟩, rfl⟩
    have h1 : (⟨g, hg⟩ : ↥(orthDerived Q)) * φ x = φ x * ⟨g, hg⟩ :=
      Subtype.ext (hgc ((φ x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) hxA)
    have h2 : k * x = x * k := by
      have := congrArg (fun z : ↥(orthDerived Q) => φ.symm z) h1
      simpa [k] using this
    have h4 := congrArg Subtype.val h2
    simpa [x] using h4.symm
  have hk3' : k ^ 3 = 1 := by
    apply φ.injective
    rw [map_pow, hφk, map_one]
    exact Subtype.ext (by simpa using hg3)
  have hk3 : (k : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hk3'
  exact mem_of_closure_singleton_of_isMaxElemAb3 hmax k.2 hkcomm hk3

private theorem mem_orthImage_of_commute {Q : QuadraticForm (ZMod 2) V} {K E : Subgroup G}
    (φ : ↥K ≃* ↥(orthDerived Q)) (hmax : IsMaxElemAb3 K (E ⊓ K))
    {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : A = ((E ⊓ K).subgroupOf K).map ((orthDerived Q).subtype.comp φ.toMonoidHom))
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ orthDerived Q) (hg3 : g ^ 3 = 1)
    (hgc : ∀ c ∈ A, g * c = c * g) : g ∈ A := by
  have hk : ((φ.symm ⟨g, hg⟩ : ↥K) : G) ∈ E ⊓ K :=
    inv_mem_inf_of_commute φ hmax hA hg hg3 hgc
  have hmem : ((φ (φ.symm ⟨g, hg⟩) : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈ A := by
    rw [hA, Subgroup.mem_map]
    exact ⟨φ.symm ⟨g, hg⟩, ⟨hk.1, (φ.symm ⟨g, hg⟩).2⟩, rfl⟩
  simpa using hmem

private theorem signed_perm_of_normalizer {Q : QuadraticForm (ZMod 2) V}
    (hind : OmegaAutIsometric Q) {n : ℕ} {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    {τ : (Fin n → Multiplicative (ZMod 3)) →* (V ≃ₗ[ZMod 2] V)}
    {τ' : (Fin n → Multiplicative (ZMod 3)) →* ↥(orthDerived Q)}
    (hτ' : ∀ f, ((τ' f : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) = τ f)
    (hτrange : τ.range = A)
    (hτ'range : ∀ x : ↥(orthDerived Q), x ∈ τ'.range ↔ (x : V ≃ₗ[ZMod 2] V) ∈ A)
    (hnorm : ∀ g : V ≃ₗ[ZMod 2] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
      ∃ (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    (α : MulAut ↥(orthDerived Q)) (hα : ∀ f, α (τ' f) ∈ τ'.range) :
    ∃ (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', α (τ' f) = τ' f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  classical
  obtain ⟨h, -, hhα⟩ := hind α
  have hAnorm : ∀ a ∈ A, h * a * h⁻¹ ∈ A := by
    intro a ha
    rw [← hτrange] at ha
    obtain ⟨f, rfl⟩ := ha
    have hmem : ((α (τ' f) : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈ A :=
      (hτ'range (α (τ' f))).mp (hα f)
    rw [← hτ' f, ← hhα (τ' f)]
    exact hmem
  obtain ⟨π, ε, hε, hrel⟩ := hnorm h hAnorm
  refine ⟨π, ε, hε, fun f f' hff i => hrel f f' ?_ i⟩
  have h1 := congrArg Subtype.val hff
  rw [hhα (τ' f), hτ' f, hτ' f'] at h1
  exact h1

private theorem exists_orthImage {Q : QuadraticForm (ZMod 2) V} {K E : Subgroup G}
    (φ : ↥K ≃* ↥(orthDerived Q)) (hmax : IsMaxElemAb3 K (E ⊓ K)) :
    ∃ A : Subgroup (V ≃ₗ[ZMod 2] V),
      A = ((E ⊓ K).subgroupOf K).map ((orthDerived Q).subtype.comp φ.toMonoidHom) ∧
      Nat.card A = Nat.card ↥(E ⊓ K) ∧ A ≤ orthDerived Q ∧ IsElemAbelian 3 A := by
  classical
  let f : ↥K →* (V ≃ₗ[ZMod 2] V) := (orthDerived Q).subtype.comp φ.toMonoidHom
  let A : Subgroup (V ≃ₗ[ZMod 2] V) := ((E ⊓ K).subgroupOf K).map f
  have hAdef : A = ((E ⊓ K).subgroupOf K).map
      ((orthDerived Q).subtype.comp φ.toMonoidHom) := rfl
  have hcardA : Nat.card A = Nat.card ↥(E ⊓ K) := by
    rw [hAdef]
    exact card_orthImage φ
  have hAΩ : A ≤ orthDerived Q := by
    intro a ha
    rw [hAdef] at ha
    obtain ⟨x, -, rfl⟩ := ha
    exact (φ x).2
  have hAab : IsElemAbelian 3 A := by
    rw [hAdef]
    exact (hmax.2.1.subgroupOf K).map f
  exact ⟨A, hAdef, hcardA, hAΩ, hAab⟩

private theorem exists_torus_orthImage [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {K E : Subgroup G} {n : ℕ}
    (φ : ↥K ≃* ↥(orthDerived Q))
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) V, finrank (ZMod 2) T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : A = ((E ⊓ K).subgroupOf K).map ((orthDerived Q).subtype.comp φ.toMonoidHom))
    (hAΩ : A ≤ orthDerived Q) (hAab : IsElemAbelian 3 A)
    (hmax : IsMaxElemAb3 K (E ⊓ K))
    (hcardA : Nat.card A = Nat.card ↥(E ⊓ K)) (hcard : Nat.card ↥(E ⊓ K) = 3 ^ n)
    (hne : ∃ b ∈ A, b ≠ 1) :
    ∃ τ : (Fin n → Multiplicative (ZMod 3)) →* (V ≃ₗ[ZMod 2] V),
      Function.Injective τ ∧ τ.range = A ∧
      (∀ σ : Equiv.Perm (Fin n), ∃ w ∈ orthDerived Q,
        ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin n, i ≠ j → ∃ w ∈ orthDerived Q,
        ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ g : V ≃ₗ[ZMod 2] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
        ∃ (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨r, τ, hτinj, hτrange, hperm, hdinv, hnorm, -⟩ :=
    CFSG.StandardType.OrthTorus.exists_torus (p := 3) (K := ZMod 2) (V := V) (Q := Q) (A := A)
      (by norm_num) (CFSG.StandardType.OrthTorus.three_dvd_card_sub_or_add (K := ZMod 2))
      hQ hT hAΩ hAab.2 (fun a ha b hb => IsElemAbelian.comm hAab ha hb)
      (fun g hg hg3 hgc => mem_orthImage_of_commute φ hmax hA hg hg3 hgc) hne
  have h1 : Nat.card (Fin r → Multiplicative (ZMod 3)) = Nat.card A := by
    rw [← hτrange]
    exact Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv
  have hr : r = n := by
    have h : 3 ^ r = 3 ^ n := by
      rw [← card_coords r, h1, hcardA, hcard]
    exact Nat.pow_right_injective (a := 3) (by norm_num) h
  subst r
  exact ⟨τ, hτinj, hτrange, hperm, hdinv, hnorm⟩

private theorem codRestrict_torus {Q : QuadraticForm (ZMod 2) V} {n : ℕ}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    {τ : (Fin n → Multiplicative (ZMod 3)) →* (V ≃ₗ[ZMod 2] V)}
    (hAΩ : A ≤ orthDerived Q) (hτinj : Function.Injective τ) (hτrange : τ.range = A) :
    ∃ τ' : (Fin n → Multiplicative (ZMod 3)) →* ↥(orthDerived Q),
      (∀ f, ((τ' f : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) = τ f) ∧
      Function.Injective τ' ∧
      (∀ x : ↥(orthDerived Q), x ∈ τ'.range ↔ (x : V ≃ₗ[ZMod 2] V) ∈ A) := by
  have hτmem : ∀ f, τ f ∈ orthDerived Q := fun f =>
    hAΩ (hτrange ▸ (show τ f ∈ τ.range from ⟨f, rfl⟩))
  let τ' : (Fin n → Multiplicative (ZMod 3)) →* ↥(orthDerived Q) :=
    τ.codRestrict (orthDerived Q) hτmem
  have hτ'coe : ∀ f, ((τ' f : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) = τ f := fun _ => rfl
  refine ⟨τ', hτ'coe, fun _ _ h => hτinj (Subtype.ext_iff.mp h), ?_⟩
  intro x
  constructor
  · rintro ⟨f, rfl⟩
    exact hτrange ▸ (show τ f ∈ τ.range from ⟨f, rfl⟩)
  · intro hx
    rw [← hτrange] at hx
    obtain ⟨f, hf⟩ := hx
    exact ⟨f, Subtype.ext hf⟩

private theorem mem_orthImage_iff {Q : QuadraticForm (ZMod 2) V} {K E : Subgroup G}
    (φ : ↥K ≃* ↥(orthDerived Q)) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : A = ((E ⊓ K).subgroupOf K).map ((orthDerived Q).subtype.comp φ.toMonoidHom)) :
    ∀ x : ↥K, ((φ x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈ A ↔ (x : G) ∈ E := by
  intro x
  rw [hA, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := φ.injective (Subtype.ext hxy)
    subst hyx
    exact hy.1
  · intro hx
    exact ⟨x, ⟨hx, x.2⟩, rfl⟩

private theorem perm_dinv_codRestrict {Q : QuadraticForm (ZMod 2) V} {n : ℕ}
    {τ : (Fin n → Multiplicative (ZMod 3)) →* (V ≃ₗ[ZMod 2] V)}
    {τ' : (Fin n → Multiplicative (ZMod 3)) →* ↥(orthDerived Q)}
    (hτ' : ∀ f, ((τ' f : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) = τ f)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∃ w ∈ orthDerived Q,
      ∀ f, w * τ f * w⁻¹ = τ (permAut σ f))
    (hdinv : ∀ i j : Fin n, i ≠ j → ∃ w ∈ orthDerived Q,
      ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) :
    (∀ σ : Equiv.Perm (Fin n), ∃ w : ↥(orthDerived Q),
      ∀ f, w * τ' f * w⁻¹ = τ' (permAut σ f)) ∧
    (∀ i j : Fin n, i ≠ j → ∃ w : ↥(orthDerived Q),
      ∀ f, w * τ' f * w⁻¹ = τ' (dinv i j f)) := by
  constructor
  · intro σ
    obtain ⟨w, hw, hws⟩ := hperm σ
    exact ⟨⟨w, hw⟩, fun f => Subtype.ext (by simpa [hτ'] using hws f)⟩
  · intro i j hij
    obtain ⟨w, hw, hws⟩ := hdinv i j hij
    exact ⟨⟨w, hw⟩, fun f => Subtype.ext (by simpa [hτ'] using hws f)⟩

theorem exists_basis_localOrth_of_model [Finite G] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) V, finrank (ZMod 2) T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hind : OmegaAutIsometric Q) {n : ℕ} (hn : 1 ≤ n) {b₀ : G} {K E : Subgroup G}
    (φ : ↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    (hKN : Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E) (hmax : IsMaxElemAb3 K (E ⊓ K))
    (hcard : Nat.card ↥(E ⊓ K) = 3 ^ n) :
    ∃ B : Basis3 G (n + 1), Adapted B b₀ K E ∧ (LocalOrthI B b₀ ∨ LocalOrthII B b₀) ∧
      evenFix0 n ⊆ B.realized K := by
  classical
  obtain ⟨A, hAdef, hcardA, hAΩ, hAab⟩ := exists_orthImage φ hmax
  have hne : ∃ b ∈ A, b ≠ 1 := by
    refine exists_ne_one_of_card_eq_pow (E := A) (n := n) ?_ hn
    rw [hcardA, hcard]
  obtain ⟨τ, hτinj, hτrange, hperm, hdinv, hnorm⟩ :=
    exists_torus_orthImage φ hQ hT hAdef hAΩ hAab hmax hcardA hcard hne
  obtain ⟨τ', hτ'coe, hτ'inj, hτ'range⟩ := codRestrict_torus hAΩ hτinj hτrange
  obtain ⟨hperm', hdinv'⟩ := perm_dinv_codRestrict hτ'coe hperm hdinv
  have hnorm' := signed_perm_of_normalizer hind hτ'coe hτrange hτ'range hnorm
  have hmemA := mem_orthImage_iff φ hAdef
  let B : Basis3 G (n + 1) := torusBasis φ hτ'inj hb₀ hKC hdisj
  have hEK : ∀ x : ↥K, (x : G) ∈ E ↔ φ x ∈ τ'.range := by
    intro x
    rw [hτ'range (φ x)]
    exact (hmemA x).symm
  have heven := torusBasis_heven φ hτ'inj hb₀ hKC hdisj hperm' hdinv'
  exact ⟨B, torusBasis_adapted φ hτ'inj hb₀ hKC hdisj hEK hsup,
    localOrth_of_monomial B (torusBasis_b_zero φ hτ'inj hb₀ hKC hdisj) hKC
      (torusBasis_hmono φ hτ'inj hb₀ hKC hdisj hKN hnorm') heven, heven⟩

private theorem exists_torus_frame_orthImage [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {K E : Subgroup G} {n : ℕ}
    (φ : ↥K ≃* ↥(orthDerived Q))
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) V, finrank (ZMod 2) T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : A = ((E ⊓ K).subgroupOf K).map ((orthDerived Q).subtype.comp φ.toMonoidHom))
    (hAΩ : A ≤ orthDerived Q) (hAab : IsElemAbelian 3 A)
    (hmax : IsMaxElemAb3 K (E ⊓ K))
    (hcardA : Nat.card A = Nat.card ↥(E ⊓ K)) (hcard : Nat.card ↥(E ⊓ K) = 3 ^ n)
    (hne : ∃ b ∈ A, b ≠ 1) :
    ∃ (F : SevOm.Frame Q 3 A n) (τ : (Fin n → Multiplicative (ZMod 3)) →* (V ≃ₗ[ZMod 2] V)),
      (∀ f, τ f = F.ι (OrthTorus.piMul n 3 f)) ∧ (∀ j, finrank (ZMod 2) (F.U j) = 2) ∧
      Function.Injective τ ∧ τ.range = A ∧
      (∀ σ : Equiv.Perm (Fin n), ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin n, i ≠ j → ∃ w ∈ orthDerived Q, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨r, τ, F, hτF, hU, -, hτinj, hτrange, hperm, hdinv, -, -⟩ :=
    CFSG.StandardType.OrthTorus.exists_torus_frame_full (p := 3) (K := ZMod 2) (V := V) (Q := Q)
      (A := A) (by norm_num) (CFSG.StandardType.OrthTorus.three_dvd_card_sub_or_add (K := ZMod 2))
      hQ hT hAΩ hAab.2 (fun a ha b hb => IsElemAbelian.comm hAab ha hb)
      (fun g hg hg3 hgc => mem_orthImage_of_commute φ hmax hA hg hg3 hgc) hne
  have h1 : Nat.card (Fin r → Multiplicative (ZMod 3)) = Nat.card A := by
    rw [← hτrange]
    exact Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv
  have hr : r = n := by
    have h : 3 ^ r = 3 ^ n := by
      rw [← card_coords r, h1, hcardA, hcard]
    exact Nat.pow_right_injective (a := 3) (by norm_num) h
  subst r
  exact ⟨F, τ, hτF, hU, hτinj, hτrange, hperm, hdinv⟩

theorem exists_basis_frame_of_model [Finite G] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) V, finrank (ZMod 2) T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {n : ℕ} (hn : 1 ≤ n) {b₀ : G} {K E : Subgroup G} (φ : ↥K ≃* ↥(orthDerived Q))
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E) (hmax : IsMaxElemAb3 K (E ⊓ K))
    (hcard : Nat.card ↥(E ⊓ K) = 3 ^ n) :
    ∃ (B : Basis3 G (n + 1)) (F : SevOm.Frame Q 3
        (((E ⊓ K).subgroupOf K).map ((orthDerived Q).subtype.comp φ.toMonoidHom)) n),
      Adapted B b₀ K E ∧ evenFix0 n ⊆ B.realized K ∧ (∀ j, finrank (ZMod 2) (F.U j) = 2) ∧
      ∀ (j : Fin n) (hj : B.b j.succ ∈ K),
        ((φ ⟨B.b j.succ, hj⟩ : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) =
          F.ι (ofAdd (Pi.single j 1)) := by
  classical
  obtain ⟨A, hAdef, hcardA, hAΩ, hAab⟩ := exists_orthImage φ hmax
  have hne : ∃ b ∈ A, b ≠ 1 := by
    refine exists_ne_one_of_card_eq_pow (E := A) (n := n) ?_ hn
    rw [hcardA, hcard]
  obtain ⟨F, τ, hτF, hU, hτinj, hτrange, hperm, hdinv⟩ :=
    exists_torus_frame_orthImage φ hQ hT hAdef hAΩ hAab hmax hcardA hcard hne
  obtain ⟨τ', hτ'coe, hτ'inj, hτ'range⟩ := codRestrict_torus hAΩ hτinj hτrange
  obtain ⟨hperm', hdinv'⟩ := perm_dinv_codRestrict hτ'coe hperm hdinv
  have hmemA := mem_orthImage_iff φ hAdef
  have hEK : ∀ x : ↥K, (x : G) ∈ E ↔ φ x ∈ τ'.range := by
    intro x
    rw [hτ'range (φ x)]
    exact (hmemA x).symm
  subst hAdef
  refine ⟨torusBasis φ hτ'inj hb₀ hKC hdisj, F, torusBasis_adapted φ hτ'inj hb₀ hKC hdisj hEK hsup,
    torusBasis_heven φ hτ'inj hb₀ hKC hdisj hperm' hdinv', hU, fun j hj => ?_⟩
  have hb : (⟨(torusBasis φ hτ'inj hb₀ hKC hdisj).b j.succ, hj⟩ : ↥K) =
      φ.symm (τ' (Pi.mulSingle j (ofAdd 1))) :=
    Subtype.ext (torusBasis_b_succ φ hτ'inj hb₀ hKC hdisj j)
  rw [hb, MulEquiv.apply_symm_apply, hτ'coe, hτF]
  rfl

private theorem isSign_ne_zero' {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (i : Fin k) :
    s i ≠ 0 := by
  rcases hs i with h | h <;> rw [h] <;> decide

private theorem spMat_inj_of_isSign {k : ℕ} {σ τ : Equiv.Perm (Fin k)} {s t : Fin k → ZMod 3}
    (hs : IsSign s) (_ht : IsSign t) (h : spMat σ s = spMat τ t) : σ = τ ∧ s = t := by
  have hval : ∀ j, σ j = τ j ∧ t j = s j := by
    intro j
    have hentry := congrFun (congrFun h (σ j)) j
    rw [spMat_apply, spMat_apply] at hentry
    by_cases hστ : σ j = τ j
    · simp [hστ] at hentry
      exact ⟨hστ, hentry.symm⟩
    · simp [hστ] at hentry
      exact absurd hentry (isSign_ne_zero' hs j)
  exact ⟨Equiv.ext fun j => (hval j).1, funext fun j => (hval j).2.symm⟩

private theorem prod_succ_ite_eq_neg {n : ℕ} (i : Fin n) :
    (∏ j : Fin n, (if j.succ = i.succ then (-1 : ZMod 3) else 1)) = -1 := by
  have h1 : (∏ j : Fin n, (if j = i then (-1 : ZMod 3) else 1)) = -1 :=
    Fintype.prod_ite_eq' i (fun _ => (-1 : ZMod 3))
  rw [← h1]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = i
  · subst hj
    simp
  · have hne : j.succ ≠ i.succ := fun hh => hj (Fin.succ_injective n hh)
    simp [hj, hne]

private theorem spMat_one_ite_neg_not_mem_evenFix0 {n : ℕ} (i : Fin n) :
    spMat (1 : Equiv.Perm (Fin (n + 1)))
      (fun j => if j = i.succ then (-1 : ZMod 3) else 1) ∉ evenFix0 n := by
  intro hmem
  rw [evenFix0, spSet] at hmem
  obtain ⟨σ, t, ht, hp, hEq⟩ := hmem
  obtain ⟨-, -, htp⟩ := hp
  have hexp : IsSign (fun j : Fin (n + 1) => if j = i.succ then (-1 : ZMod 3) else 1) := by
    intro j
    change (if j = i.succ then (-1 : ZMod 3) else 1) = 1 ∨
      (if j = i.succ then (-1 : ZMod 3) else 1) = -1
    by_cases h : j = i.succ
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]; exact Or.inl rfl
  have hst : (fun j : Fin (n + 1) => if j = i.succ then (-1 : ZMod 3) else 1) = t :=
    (spMat_inj_of_isSign hexp ht hEq).2
  have hprod : (∏ j : Fin n, t j.succ) = -1 := by
    rw [← hst]
    exact prod_succ_ite_eq_neg i
  rw [htp] at hprod
  exact absurd hprod (by decide)

private theorem not_mem_orthDerived_of_aut {Q : QuadraticForm (ZMod 2) V}
    {K C : Subgroup G} {c : G}
    (hKC : K ≤ C) (hKN : C ≤ Subgroup.normalizer (K : Set G))
    (hcC : c ∈ C) (hcnot : c ∉ K ⊔ (C ⊓ Subgroup.centralizer (K : Set G)))
    (φ : ↥K ≃* ↥(orthDerived Q))
    (α : MulAut ↥(orthDerived Q))
    (hα : α = φ.symm.trans ((ggConjAut K (hKN hcC)).trans φ))
    {h : V ≃ₗ[ZMod 2] V}
    (hhα : ∀ x : ↥(orthDerived Q),
      ((α x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) = h * (x : V ≃ₗ[ZMod 2] V) * h⁻¹) :
    h ∉ orthDerived Q := by
  intro hhΩ
  let k : ↥K := φ.symm ⟨h, hhΩ⟩
  have hkey : ∀ x : ↥K, (k : G) * (x : G) * (k : G)⁻¹ = c * (x : G) * c⁻¹ := by
    intro x
    have h1 : (⟨h, hhΩ⟩ : ↥(orthDerived Q)) * φ x * (⟨h, hhΩ⟩ : ↥(orthDerived Q))⁻¹
        = φ (ggConjAut K (hKN hcC) x) := by
      apply Subtype.ext
      have h3 : α (φ x) = φ (ggConjAut K (hKN hcC) x) := by
        rw [hα, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
      rw [← h3, hhα (φ x)]
      rfl
    have h2 : k * x * k⁻¹ = ggConjAut K (hKN hcC) x := by
      have := congrArg (fun z => φ.symm z) h1
      simpa [k] using this
    have h3 := congrArg (fun z : ↥K => (z : G)) h2
    simpa [ggConjAut_apply] using h3
  have hmemC : (k : G)⁻¹ * c ∈ C := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC k.2)) hcC
  have hmemCK : (k : G)⁻¹ * c ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hkey ⟨x, hx⟩
    calc x * ((k : G)⁻¹ * c)
        = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * c := by group
      _ = (k : G)⁻¹ * (c * x * c⁻¹) * c := by rw [h]
      _ = ((k : G)⁻¹ * c) * x := by group
  exact hcnot (by
    rw [show c = (k : G) * ((k : G)⁻¹ * c) by group]
    exact Subgroup.mul_mem_sup k.2 ⟨hmemC, hmemCK⟩)

private theorem inv_eq_pow_two_of_orderOf_eq_three {G : Type} [Group G] {x : G}
    (hx : orderOf x = 3) : x⁻¹ = x ^ 2 := by
  have h : x ^ 2 * x = 1 := by
    have h3 : x ^ 3 = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    rwa [show (3 : ℕ) = 2 + 1 from rfl, pow_succ] at h3
  exact mul_eq_one_iff_inv_eq'.mp h

theorem exists_basis_not_mem_evenFix0_of_not_le [Finite G] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) V, finrank (ZMod 2) T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (h6 : 6 ≤ finrank (ZMod 2) V) (hind : OmegaAutIsometric Q) {n : ℕ} (hn : 1 ≤ n)
    {b₀ : G} {K E : Subgroup G}
    (φ : ↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hdisj : Disjoint (Subgroup.zpowers b₀) K)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E) (hmax : IsMaxElemAb3 K (E ⊓ K))
    (hcard : Nat.card ↥(E ⊓ K) = 3 ^ n)
    (hout : ¬ Subgroup.centralizer ({b₀} : Set G) ≤
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))) :
    ∃ B : Basis3 G (n + 1), Adapted B b₀ K E ∧
      evenFix0 n ⊆ B.realized (Subgroup.centralizer ({b₀} : Set G)) ∧
      ∃ M ∈ B.realized (Subgroup.centralizer ({b₀} : Set G)), M ∉ evenFix0 n := by
  classical
  obtain ⟨A, hAdef, hcardA, hAΩ, hAab⟩ := exists_orthImage φ hmax
  have hne : ∃ b ∈ A, b ≠ 1 := by
    refine exists_ne_one_of_card_eq_pow (E := A) (n := n) ?_ hn
    rw [hcardA, hcard]
  obtain ⟨F, τ, hτF, hU, hτinj, hτrange, hperm, hdinv⟩ :=
    exists_torus_frame_orthImage φ hQ hT hAdef hAΩ hAab hmax hcardA hcard hne
  obtain ⟨τ', hτ'coe, hτ'inj, hτ'range⟩ := codRestrict_torus hAΩ hτinj hτrange
  obtain ⟨hperm', hdinv'⟩ := perm_dinv_codRestrict hτ'coe hperm hdinv
  have hEK : ∀ x : ↥K, (x : G) ∈ E ↔ φ x ∈ τ'.range := by
    intro x
    rw [hτ'range (φ x)]
    exact (mem_orthImage_iff φ hAdef x).symm
  let B : Basis3 G (n + 1) := torusBasis φ hτ'inj hb₀ hKC hdisj
  have hadapted : Adapted B b₀ K E :=
    torusBasis_adapted φ hτ'inj hb₀ hKC hdisj hEK hsup
  have heven : evenFix0 n ⊆ B.realized K :=
    torusBasis_heven φ hτ'inj hb₀ hKC hdisj hperm' hdinv'
  have hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
  obtain ⟨c, hcC, hcnot⟩ := Set.not_subset.mp hout
  let α : MulAut ↥(orthDerived Q) := φ.symm.trans ((ggConjAut K (hKN hcC)).trans φ)
  obtain ⟨h, hhO, hhα⟩ := hind α
  have hhΩ : h ∉ orthDerived Q :=
    not_mem_orthDerived_of_aut hKC hKN hcC hcnot φ α rfl hhα
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun a ha => OmMv.orthDerived_le_O Q (hAΩ ha)
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨ρ, hρO, hρΩ, hρτ⟩ := exists_reflection_conj_torus_sgnAut hQ hAO F hτF hU i
  have hhρΩ : h * ρ⁻¹ ∈ orthDerived Q :=
    mul_inv_mem_orthDerived_of_not_mem hQ h6 hhO hρO hhΩ hρΩ
  let k : ↥K := φ.symm ⟨h * ρ⁻¹, hhρΩ⟩
  let c' : G := (k : G)⁻¹ * c
  have hc'C : c' ∈ Subgroup.centralizer ({b₀} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC k.2)) hcC
  have hc'conj : ∀ x : ↥K, c' * (x : G) * c'⁻¹
      = (φ.symm ((⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q))⁻¹ * α (φ x) *
          (⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q))) : G) := by
    intro x
    have hmem : c' * (x : G) * c'⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hKN hc'C) (x : G)).mp x.2
    have hK1 : (⟨c' * (x : G) * c'⁻¹, hmem⟩ : ↥K)
        = k⁻¹ * ggConjAut K (hKN hcC) x * k := by
      apply Subtype.ext
      dsimp only [c', k]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [ggConjAut_apply]
      group
    have hb : φ (ggConjAut K (hKN hcC) x) = α (φ x) := by
      dsimp only [α]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hm : φ k = (⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q)) :=
      MulEquiv.apply_symm_apply φ _
    have hK2 : φ (⟨c' * (x : G) * c'⁻¹, hmem⟩ : ↥K)
        = (⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q))⁻¹ * α (φ x) *
          (⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q)) := by
      rw [hK1, map_mul, map_mul, map_inv, hb, hm]
    have hK : (⟨c' * (x : G) * c'⁻¹, hmem⟩ : ↥K)
        = φ.symm ((⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q))⁻¹ * α (φ x) *
          (⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q))) := by
      refine φ.injective ?_
      rw [MulEquiv.apply_symm_apply]
      exact hK2
    exact congrArg Subtype.val hK
  have hΩeq : ∀ m : Fin n, (⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q))⁻¹ *
      α (τ' (Pi.mulSingle m (ofAdd 1))) * (⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q))
      = τ' (sgnAut i (Pi.mulSingle m (ofAdd 1))) := by
    intro m
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hhα (τ' (Pi.mulSingle m (ofAdd 1))), hτ'coe, hτ'coe]
    rw [← hρτ (Pi.mulSingle m (ofAdd 1))]
    have hmval : ((⟨h * ρ⁻¹, hhρΩ⟩ : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) = h * ρ⁻¹ := rfl
    rw [hmval]
    group
  let s : Fin (n + 1) → ZMod 3 := fun j => if j = i.succ then -1 else 1
  have hs : IsSign s := by
    intro j
    dsimp only [s]
    change (if j = i.succ then (-1 : ZMod 3) else 1) = 1 ∨
      (if j = i.succ then (-1 : ZMod 3) else 1) = -1
    by_cases h : j = i.succ
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]; exact Or.inl rfl
  have hB0 : B.b 0 = b₀ := torusBasis_b_zero φ hτ'inj hb₀ hKC hdisj
  have hBsucc : ∀ m : Fin n, B.b m.succ = (φ.symm (τ' (Pi.mulSingle m (ofAdd 1))) : G) :=
    fun m => torusBasis_b_succ φ hτ'inj hb₀ hKC hdisj m
  have hActs : B.Acts c' (spMat (1 : Equiv.Perm (Fin (n + 1))) s) := by
    rw [Basis3.acts_spMat_iff B]
    intro j
    cases j using Fin.cases with
    | zero =>
      have hcomm : c' * b₀ = b₀ * c' := Subgroup.mem_centralizer_singleton_iff.mp hc'C
      have hs0 : s 0 = 1 := by
        dsimp only [s]
        rw [if_neg (Ne.symm (Fin.succ_ne_zero i))]
      rw [Equiv.Perm.one_apply, hB0, hs0, show ((1 : ZMod 3)).val = 1 from rfl, pow_one]
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    | succ m =>
      have hconj' := hc'conj (φ.symm (τ' (Pi.mulSingle m (ofAdd 1))))
      rw [Equiv.Perm.one_apply, hBsucc m, hconj', MulEquiv.apply_symm_apply, hΩeq m]
      by_cases hm : m = i
      · subst hm
        have hord : orderOf ((φ.symm (τ' (Pi.mulSingle i (ofAdd 1))) : ↥K) : G) = 3 := by
          rw [← hBsucc i]
          exact B.ord i.succ
        rw [sgnAut_mulSingle_self, map_inv, map_inv]
        have hsval : s i.succ = -1 := by
          dsimp only [s]
          rw [if_pos rfl]
        rw [hsval, show ((-1 : ZMod 3)).val = 2 from rfl]
        exact inv_eq_pow_two_of_orderOf_eq_three hord
      · have hne : m.succ ≠ i.succ := fun hh => hm (Fin.succ_injective n hh)
        have hsval : s m.succ = 1 := by
          dsimp only [s]
          rw [if_neg hne]
        rw [sgnAut_mulSingle_of_ne hm, hsval, show ((1 : ZMod 3)).val = 1 from rfl, pow_one]
  exact ⟨B, hadapted, (fun M hM => realized_mono B hKC (heven hM)),
    spMat (1 : Equiv.Perm (Fin (n + 1))) s, ⟨c', hc'C, hActs⟩,
    spMat_one_ite_neg_not_mem_evenFix0 i⟩

end CFSG.StandardType.FrameRoute.FS81
