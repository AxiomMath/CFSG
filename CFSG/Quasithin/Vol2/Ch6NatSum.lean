module

public import CFSG.Quasithin.Vol2.Ch6SL2Aut
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped IsMulCommutative MatrixGroups Matrix

variable {G : Type} [Group G]

namespace NatL2Data

variable {L W₁ W₂ : Subgroup G} {n : ℕ}

theorem exists_mulEquiv_ch6 (D₁ : NatL2Data L W₁ n) (D₂ : NatL2Data L W₂ n)
    (hker : ∀ ℓ ∈ L, ℓ ∈ Subgroup.centralizer (W₁ : Set G) ↔
      ℓ ∈ Subgroup.centralizer (W₂ : Set G)) :
    ∃ f : ↥W₁ ≃* ↥W₂, ∀ (ℓ : ↥L) (w : ↥W₁),
      f (conjAct W₁ ⟨ℓ, D₁.le_normalizer ℓ.2⟩ w) = conjAct W₂ ⟨ℓ, D₂.le_normalizer ℓ.2⟩ (f w) := by
  classical
  have hcard : Nat.card D₁.K = Nat.card D₂.K := D₁.card.trans D₂.card.symm
  have hn : n ≠ 0 := by
    rintro rfl
    have : Nat.card D₁.K = 1 := by simpa using D₁.card
    exact (Finite.one_lt_card (α := D₁.K)).ne' this
  have := Fintype.ofFinite D₁.K
  have hchar : CharP D₁.K 2 := by
    have h2 : ringChar D₁.K = 2 := by
      rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, D₁.card]
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn)
    exact ringChar.of_eq h2
  have hk : D₁.rho.ker = D₂.rho.ker := by
    ext ℓ
    rw [D₁.mem_ker_rho_iff, D₂.mem_ker_rho_iff]
    exact hker ℓ ℓ.2
  let θ : SL(2, D₁.K) ≃* SL(2, D₂.K) :=
    (QuotientGroup.quotientKerEquivOfSurjective D₁.rho D₁.rho_surjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective D₂.rho D₂.rho_surjective))
  have hθ : ∀ ℓ : ↥L, θ (D₁.rho ℓ) = D₂.rho ℓ := by
    intro ℓ
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective D₁.rho D₁.rho_surjective).symm
        (D₁.rho ℓ) = (ℓ : ↥L ⧸ D₁.rho.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [θ, MulEquiv.trans_apply, h1]
    rfl
  obtain ⟨f, hf⟩ := exists_addEquiv_of_sl2_mulEquiv_ch6 hcard θ
  refine ⟨D₁.E.trans ((AddEquiv.toMultiplicative f).trans D₂.E.symm), fun ℓ w => ?_⟩
  apply D₂.E.injective
  apply Multiplicative.toAdd.injective
  have h₁ : Multiplicative.toAdd (D₁.E (conjAct W₁ ⟨ℓ, D₁.le_normalizer ℓ.2⟩ w)) =
      ((D₁.rho ℓ : SL(2, D₁.K)) : Matrix (Fin 2) (Fin 2) D₁.K) *ᵥ
        Multiplicative.toAdd (D₁.E w) := by
    rw [← D₁.conj_apply, D₁.conj_eq_rho]
  have h₂ : ∀ w' : ↥W₂, Multiplicative.toAdd (D₂.E (conjAct W₂ ⟨ℓ, D₂.le_normalizer ℓ.2⟩ w')) =
      ((D₂.rho ℓ : SL(2, D₂.K)) : Matrix (Fin 2) (Fin 2) D₂.K) *ᵥ
        Multiplicative.toAdd (D₂.E w') := fun w' => by
    rw [← D₂.conj_apply, D₂.conj_eq_rho]
  rw [h₂]
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change f (Multiplicative.toAdd (D₁.E (conjAct W₁ ⟨ℓ, D₁.le_normalizer ℓ.2⟩ w))) =
    ((D₂.rho ℓ : SL(2, D₂.K)) : Matrix (Fin 2) (Fin 2) D₂.K) *ᵥ
      f (Multiplicative.toAdd (D₁.E w))
  rw [h₁, hf, hθ]

end NatL2Data

theorem le_normalizer_map_conj_ch6 {L X : Subgroup G} {t : G}
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    L ≤ Subgroup.normalizer ((X.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  intro ℓ hℓ
  refine ⟨t⁻¹ * ℓ * t, hLX ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htL) ℓ).mp hℓ
    simpa using this
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mem_normalizer_of_map_conj_eq_natSum {X : Subgroup G} {t : G}
    (h : X.map (MulAut.conj t).toMonoidHom = X) : t ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : t * y * t⁻¹ ∈ X.map (MulAut.conj t).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨y', hy', e⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    have : y' = y := by
      have := congrArg (fun z => t⁻¹ * z * t) e
      simpa [mul_assoc] using this
    rwa [← this]

theorem normalizer_le_of_isNatModCh5_ch6 [Finite G] {L M W U : Subgroup G} {n : ℕ}
    (hW : IsNatModCh5 L W n) (hML : M ≤ Subgroup.normalizer (L : Set G)) (hU : U ≠ ⊥)
    (hUW : U ≤ W) :
    M ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (W : Set G) := by
  rintro m ⟨hm, hmU⟩
  set W' := W.map (MulAut.conj m).toMonoidHom with hW'
  have hLW' := le_normalizer_map_conj_ch6 hW.1 (hML hm)
  have hN : L ≤ Subgroup.normalizer ((W ⊓ W' : Subgroup G) : Set G) := fun _ hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hW.1 hl, hLW' hl⟩
  have hUW' : U ≤ W' := by
    intro u hu
    refine ⟨m⁻¹ * u * m, hUW ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmU) u).mp hu
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rcases hW.irreducible (W ⊓ W') inf_le_left hN with h0 | h0
  · exfalso
    apply hU
    rw [eq_bot_iff, ← h0]
    exact le_inf hUW hUW'
  · have hle : W ≤ W' := (le_of_eq h0.symm).trans inf_le_right
    have hcard : Nat.card W' = Nat.card W :=
      Subgroup.card_map_of_injective (MulAut.conj m).injective
    exact mem_normalizer_of_map_conj_eq_natSum (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

section Invariant

variable [Finite G] {T L V W₁ W₂ : Subgroup G} {n : ℕ}

theorem exists_natural_invariant_ch6 (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hL₁ : L ≤ Subgroup.normalizer (W₁ : Set G)) (hL₂ : L ≤ Subgroup.normalizer (W₂ : Set G))
    (hdisj : W₁ ⊓ W₂ = ⊥) (hsup : W₁ ⊔ W₂ = V) (h₁ : IsNatModCh5 L W₁ n)
    (h₂ : IsNatModCh5 L W₂ n)
    (hker : ∀ ℓ ∈ L, ℓ ∈ Subgroup.centralizer (W₁ : Set G) ↔
      ℓ ∈ Subgroup.centralizer (W₂ : Set G)) :
    ∃ W : Subgroup G, W ≤ V ∧ T ≤ Subgroup.normalizer (W : Set G) ∧ IsNatModCh5 L W n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV ha hb
  have hW₁V : W₁ ≤ V := hsup ▸ le_sup_left
  have hW₂V : W₂ ≤ V := hsup ▸ le_sup_right
  have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
    hVc a (hW₁V ha) b (hW₂V hb)
  obtain ⟨f, hf⟩ := NatL2Data.exists_mulEquiv_ch6 h₂.data h₁.data
    (fun ℓ hℓ => (hker ℓ hℓ).symm)
  have hf' : ∀ ℓ ∈ L, ∀ (w : ↥W₂) (hw : ℓ * (w : G) * ℓ⁻¹ ∈ W₂),
      ((f ⟨ℓ * w * ℓ⁻¹, hw⟩ : ↥W₁) : G) = ℓ * (f w : G) * ℓ⁻¹ := by
    intro ℓ hℓ w hw
    have h := hf ⟨ℓ, hℓ⟩ w
    have e : (⟨ℓ * w * ℓ⁻¹, hw⟩ : ↥W₂) = conjAct W₂ ⟨ℓ, h₂.data.le_normalizer hℓ⟩ w :=
      Subtype.ext (conjAct_apply_coe ⟨ℓ, h₂.data.le_normalizer hℓ⟩ w).symm
    rw [e, h, conjAct_apply_coe]
  choose a ha b hb hab using fun v : ↥V => exists_mul_of_mem_sup hcomm (hsup.ge v.2)
  have huniq : ∀ (v : ↥V) {a' b' : G}, a' ∈ W₁ → b' ∈ W₂ → a' * b' = v →
      a v = a' ∧ b v = b' := fun v a' b' ha' hb' h' =>
    eq_of_mul_eq hdisj (ha v) ha' (hb v) hb' ((hab v).trans h'.symm)
  have hb_mul : ∀ v w : ↥V, b (v * w) = b v * b w := fun v w =>
    (huniq (v * w) (W₁.mul_mem (ha v) (ha w)) (W₂.mul_mem (hb v) (hb w)) (by
      show a v * a w * (b v * b w) = (v : G) * w
      rw [← hab v, ← hab w]
      calc a v * a w * (b v * b w) = a v * (a w * b v) * b w := by group
        _ = a v * (b v * a w) * b w := by rw [hcomm (a w) (ha w) (b v) (hb v)]
        _ = a v * b v * (a w * b w) := by group)).2
  let c : ↥V → G := fun v => (f ⟨b v, hb v⟩ : G)
  have hc : ∀ v, c v ∈ W₁ := fun v => (f ⟨b v, hb v⟩).2
  have hcsq : ∀ v, c v * c v = 1 := fun v => by
    have := hV.2 (c v) (hW₁V (hc v))
    rwa [pow_two] at this
  have hc_of_b : ∀ v, b v = 1 → c v = 1 := fun v hbv => by
    show (f ⟨b v, hb v⟩ : G) = 1
    have : (⟨b v, hb v⟩ : ↥W₂) = 1 := Subtype.ext hbv
    rw [this, map_one]
    rfl
  have hb_of_c : ∀ v, c v = 1 → b v = 1 := fun v hcv => by
    have h1 : f ⟨b v, hb v⟩ = 1 := Subtype.ext hcv
    have h2 : (⟨b v, hb v⟩ : ↥W₂) = 1 := f.injective (h1.trans (map_one f).symm)
    exact congrArg Subtype.val h2
  have hc_mul : ∀ v w, c (v * w) = c v * c w := by
    intro v w
    show (f ⟨b (v * w), hb (v * w)⟩ : G) = (f ⟨b v, hb v⟩ : G) * (f ⟨b w, hb w⟩ : G)
    have : (⟨b (v * w), hb (v * w)⟩ : ↥W₂) = ⟨b v, hb v⟩ * ⟨b w, hb w⟩ :=
      Subtype.ext (hb_mul v w)
    rw [this, map_mul]
    rfl
  let σ : ↥V →* ↥V :=
    { toFun := fun v => ⟨v * c v, V.mul_mem v.2 (hW₁V (hc v))⟩
      map_one' := Subtype.ext (by
        show (1 : G) * c 1 = 1
        rw [hc_of_b 1 (huniq 1 W₁.one_mem W₂.one_mem (by simp)).2, mul_one])
      map_mul' := fun v w => Subtype.ext (by
        show (v : G) * w * c (v * w) = v * c v * (w * c w)
        rw [hc_mul]
        have := hVc (c v) (hW₁V (hc v)) w w.2
        calc (v : G) * w * (c v * c w) = v * (w * c v) * c w := by group
          _ = v * (c v * w) * c w := by rw [← this]
          _ = v * c v * (w * c w) := by group) }
  have hσ : ∀ v : ↥V, ((σ v : ↥V) : G) = v * c v := fun _ => rfl
  have hb_σ : ∀ v, b (σ v) = b v := fun v =>
    (huniq (σ v) (W₁.mul_mem (ha v) (hc v)) (hb v) (by
      rw [hσ, ← hab v]
      have := hVc (c v) (hW₁V (hc v)) (b v) (hW₂V (hb v))
      calc a v * c v * b v = a v * (c v * b v) := by group
        _ = a v * (b v * c v) := by rw [this]
        _ = a v * b v * c v := by group)).2
  have hc_σ : ∀ v, c (σ v) = c v := fun v => by
    show (f ⟨b (σ v), hb (σ v)⟩ : G) = (f ⟨b v, hb v⟩ : G)
    have : (⟨b (σ v), hb (σ v)⟩ : ↥W₂) = ⟨b v, hb v⟩ := Subtype.ext (hb_σ v)
    rw [this]
  have hσσ : ∀ v, σ (σ v) = v := fun v => Subtype.ext (by
    rw [hσ, hc_σ, hσ, mul_assoc, hcsq, mul_one])
  have hσW₁ : ∀ v : ↥V, (v : G) ∈ W₁ → σ v = v := fun v hv => by
    have hbv : b v = 1 := (huniq v hv W₂.one_mem (mul_one _)).2
    apply Subtype.ext
    rw [hσ, hc_of_b v hbv, mul_one]
  have hconjV : ∀ ℓ ∈ L, ∀ v : ↥V, ℓ * (v : G) * ℓ⁻¹ ∈ V := fun ℓ hℓ v =>
    (Subgroup.mem_normalizer_iff.mp (hLV hℓ) v).mp v.2
  have hσL : ∀ (ℓ : G) (hℓ : ℓ ∈ L) (v : ↥V),
      ((σ ⟨ℓ * v * ℓ⁻¹, hconjV ℓ hℓ v⟩ : ↥V) : G) = ℓ * (σ v : G) * ℓ⁻¹ := by
    intro ℓ hℓ v
    have ha' : ℓ * a v * ℓ⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hL₁ hℓ) _).mp (ha v)
    have hb' : ℓ * b v * ℓ⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hL₂ hℓ) _).mp (hb v)
    have hdec := huniq ⟨ℓ * v * ℓ⁻¹, hconjV ℓ hℓ v⟩ ha' hb' (by
      show ℓ * a v * ℓ⁻¹ * (ℓ * b v * ℓ⁻¹) = ℓ * v * ℓ⁻¹
      rw [← hab v]
      group)
    have hc' : c ⟨ℓ * v * ℓ⁻¹, hconjV ℓ hℓ v⟩ = ℓ * c v * ℓ⁻¹ := by
      show (f ⟨b ⟨ℓ * v * ℓ⁻¹, hconjV ℓ hℓ v⟩, hb _⟩ : G) = ℓ * (f ⟨b v, hb v⟩ : G) * ℓ⁻¹
      have : (⟨b ⟨ℓ * v * ℓ⁻¹, hconjV ℓ hℓ v⟩, hb _⟩ : ↥W₂) = ⟨ℓ * b v * ℓ⁻¹, hb'⟩ :=
        Subtype.ext hdec.2
      rw [this]
      exact hf' ℓ hℓ ⟨b v, hb v⟩ hb'
    rw [hσ, hσ, hc']
    simp only
    group
  let sh : Subgroup G → Subgroup G := fun X => ((X.subgroupOf V).map σ).map V.subtype
  have hmem_sh : ∀ X g, g ∈ sh X ↔ ∃ v : ↥V, (v : G) ∈ X ∧ ((σ v : ↥V) : G) = g := by
    intro X g
    simp only [sh, Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨σ v, ⟨v, hv, rfl⟩, rfl⟩
  have hsh_le : ∀ X, sh X ≤ V := fun X g hg => by
    obtain ⟨v, -, rfl⟩ := (hmem_sh X g).mp hg
    exact (σ v).2
  have hsh_sh : ∀ X, X ≤ V → sh (sh X) = X := by
    intro X hXV
    ext g
    rw [hmem_sh]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, e⟩ := (hmem_sh X v).mp hv
      have : v = σ u := Subtype.ext e.symm
      rw [this, hσσ]
      exact hu
    · intro hg
      refine ⟨σ ⟨g, hXV hg⟩, (hmem_sh X _).mpr ⟨⟨g, hXV hg⟩, hg, rfl⟩, ?_⟩
      rw [hσσ]
  have hsh_V : sh V = V := by
    refine le_antisymm (hsh_le V) fun g hg => (hmem_sh V g).mpr ⟨σ ⟨g, hg⟩, (σ ⟨g, hg⟩).2, ?_⟩
    rw [hσσ]
  let P : Subgroup G → Prop := fun X =>
    X ≤ V ∧ L ≤ Subgroup.normalizer (X : Set G) ∧ X ≠ ⊥ ∧ X ≠ V
  have hshP : ∀ X, P X → P (sh X) := by
    rintro X ⟨hXV, hLX, hX1, hXV'⟩
    refine ⟨hsh_le X, ?_, ?_, ?_⟩
    · have key : ∀ ℓ ∈ L, ∀ g ∈ sh X, ℓ * g * ℓ⁻¹ ∈ sh X := by
        intro ℓ hℓ g hg
        obtain ⟨v, hv, rfl⟩ := (hmem_sh X g).mp hg
        refine (hmem_sh X _).mpr ⟨⟨ℓ * v * ℓ⁻¹, hconjV ℓ hℓ v⟩, ?_, hσL ℓ hℓ v⟩
        exact (Subgroup.mem_normalizer_iff.mp (hLX hℓ) v).mp hv
      intro ℓ hℓ
      rw [Subgroup.mem_normalizer_iff]
      intro g
      refine ⟨key ℓ hℓ g, fun hg => ?_⟩
      have := key ℓ⁻¹ (L.inv_mem hℓ) _ hg
      simpa [mul_assoc] using this
    · intro h0
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
      apply hx1
      have hmem : ((σ ⟨x, hXV x.2⟩ : ↥V) : G) ∈ sh X := (hmem_sh X _).mpr ⟨_, x.2, rfl⟩
      rw [h0, Subgroup.mem_bot] at hmem
      have h1 : σ ⟨x, hXV x.2⟩ = 1 := Subtype.ext hmem
      have h2 : (⟨x, hXV x.2⟩ : ↥V) = 1 := by
        rw [← hσσ ⟨x, hXV x.2⟩, h1, map_one]
      exact Subtype.ext (congrArg (fun y : ↥V => (y : G)) h2)
    · intro h0
      apply hXV'
      rw [← hsh_sh X hXV, h0, hsh_V]
  have hW₁ne : W₁ ≠ ⊥ := by
    intro h0
    have := h₁.card_eq
    rw [h0, Subgroup.card_bot] at this
    have h4 : 1 < 2 ^ n * 2 ^ n := by
      have : n ≠ 0 := by
        rintro rfl
        have : Nat.card h₁.data.K = 1 := by simpa using h₁.data.card
        exact (Finite.one_lt_card (α := h₁.data.K)).ne' this
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr this)
      nlinarith
    omega
  have hW₂ne : W₂ ≠ ⊥ := by
    intro h0
    have := h₂.card_eq
    rw [h0, Subgroup.card_bot] at this
    have h4 : 1 < 2 ^ n * 2 ^ n := by
      have : n ≠ 0 := by
        rintro rfl
        have : Nat.card h₂.data.K = 1 := by simpa using h₂.data.card
        exact (Finite.one_lt_card (α := h₂.data.K)).ne' this
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr this)
      nlinarith
    omega
  have hW₁P : P W₁ := by
    refine ⟨hW₁V, hL₁, hW₁ne, fun h0 => hW₂ne ?_⟩
    rw [← hdisj, h0]
    exact (inf_eq_right.mpr hW₂V).symm
  have hfix : ∀ X, P X → sh X = X → X = W₁ := by
    rintro X ⟨hXV, hLX, hX1, hXV'⟩ hsX
    have hN₁ : L ≤ Subgroup.normalizer ((X ⊓ W₁ : Subgroup G) : Set G) := fun _ hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hLX hl, hL₁ hl⟩
    rcases h₁.irreducible (X ⊓ W₁) inf_le_right hN₁ with h0 | h0
    · exfalso
      apply hX1
      rw [eq_bot_iff]
      intro x hx
      have hσx : ((σ ⟨x, hXV hx⟩ : ↥V) : G) ∈ X := by
        rw [← hsX]
        exact (hmem_sh X _).mpr ⟨⟨x, hXV hx⟩, hx, rfl⟩
      have hcx : c ⟨x, hXV hx⟩ ∈ X ⊓ W₁ := by
        refine ⟨?_, hc _⟩
        have := X.mul_mem (X.inv_mem hx) hσx
        rwa [hσ, inv_mul_cancel_left] at this
      rw [h0, Subgroup.mem_bot] at hcx
      have hbx := hb_of_c _ hcx
      have hxW₁ : x ∈ X ⊓ W₁ := by
        refine ⟨hx, ?_⟩
        have e : a ⟨x, hXV hx⟩ = x := by
          have := hab ⟨x, hXV hx⟩
          rwa [hbx, mul_one] at this
        rw [← e]
        exact ha _
      rw [h0] at hxW₁
      exact hxW₁
    · have hW₁X : W₁ ≤ X := (le_of_eq h0.symm).trans inf_le_left
      have hN₂ : L ≤ Subgroup.normalizer ((X ⊓ W₂ : Subgroup G) : Set G) := fun _ hl =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hLX hl, hL₂ hl⟩
      rcases h₂.irreducible (X ⊓ W₂) inf_le_right hN₂ with h2 | h2
      · exact eq_of_le_of_inf_eq_bot hcomm hW₁X (hXV.trans hsup.ge) h2
      · exfalso
        apply hXV'
        refine le_antisymm hXV ?_
        rw [← hsup]
        exact sup_le hW₁X ((le_of_eq h2.symm).trans inf_le_left)
  let N := {X : Subgroup G // P X}
  have : Fintype N := Fintype.ofFinite N
  let s : Function.End N := fun X => ⟨sh X.1, hshP X.1 X.2⟩
  have hs2 : s ^ 2 ^ 1 = 1 := by
    funext X
    apply Subtype.ext
    show sh (sh X.1) = X.1
    exact hsh_sh X.1 X.2.1
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hs2
  have hfix1 : Fintype.card (Function.fixedPoints s) = 1 := by
    rw [Fintype.card_eq_one_iff]
    have hW₁fix : s ⟨W₁, hW₁P⟩ = ⟨W₁, hW₁P⟩ := by
      apply Subtype.ext
      show sh W₁ = W₁
      ext g
      rw [hmem_sh]
      constructor
      · rintro ⟨v, hv, rfl⟩
        rw [hσW₁ v hv]
        exact hv
      · intro hg
        exact ⟨⟨g, hW₁V hg⟩, hg, by rw [hσW₁ _ hg]⟩
    refine ⟨⟨⟨W₁, hW₁P⟩, hW₁fix⟩, fun X => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hfix X.1.1 X.1.2 (congrArg Subtype.val X.2)
  rw [hfix1] at hmod
  have hodd : ¬ 2 ∣ Nat.card N := by
    rw [Nat.card_eq_fintype_card]
    intro h2
    have := Nat.ModEq.symm hmod
    unfold Nat.ModEq at this
    omega
  have hactP : ∀ (t : ↥T) (X : N), P (X.1.map (MulAut.conj (t : G)).toMonoidHom) := by
    rintro ⟨t, ht⟩ ⟨X, hXV, hLX, hX1, hXV'⟩
    refine ⟨?_, le_normalizer_map_conj_ch6 hLX (hTL ht), ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTV ht) x).mp (hXV hx)
    · exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj t).injective).not.mpr hX1
    · intro h0
      apply hXV'
      refine le_antisymm hXV fun y hy => ?_
      have hy' : t * y * t⁻¹ ∈ X.map (MulAut.conj t).toMonoidHom := by
        rw [h0]
        exact (Subgroup.mem_normalizer_iff.mp (hTV ht) y).mp hy
      obtain ⟨y', hy', e⟩ := hy'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
      have : y' = y := by
        have := congrArg (fun z => t⁻¹ * z * t) e
        simpa [mul_assoc] using this
      rwa [← this]
  let _ : MulAction ↥T N :=
    { smul := fun t X => ⟨X.1.map (MulAut.conj (t : G)).toMonoidHom, hactP t X⟩
      one_smul := fun X => Subtype.ext (by
        show X.1.map (MulAut.conj ((1 : ↥T) : G)).toMonoidHom = X.1
        ext g
        simp [Subgroup.mem_map])
      mul_smul := fun t₁ t₂ X => Subtype.ext (by
        show X.1.map (MulAut.conj ((t₁ * t₂ : ↥T) : G)).toMonoidHom =
          (X.1.map (MulAut.conj (t₂ : G)).toMonoidHom).map (MulAut.conj (t₁ : G)).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext g
        simp [MulAut.conj_apply, mul_assoc]) }
  obtain ⟨X, hX⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card N hodd
  have hTX : T ≤ Subgroup.normalizer (X.1 : Set G) := by
    intro t ht
    have := congrArg Subtype.val (hX ⟨t, ht⟩)
    exact mem_normalizer_of_map_conj_eq_natSum this
  refine ⟨X.1, X.2.1, hTX, ?_⟩
  exact (eq_or_isNatModCh5_of_le_sum ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, h₁, h₂⟩ hVc X.2.1
    X.2.2.1 X.2.2.2.1).resolve_left X.2.2.2.2

end Invariant

section Fixed

variable [Finite G] {L V W₁ W₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem commutator_mem_inf_centralizer_ch6 {W : Subgroup G} {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hxW : x ∈ Subgroup.centralizer (W : Set G)) {g : G} (hg : g ∈ L) :
    x * g * x⁻¹ * g⁻¹ ∈ L ⊓ Subgroup.centralizer (W : Set G) := by
  refine ⟨L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxL g).mp hg) (L.inv_mem hg), ?_⟩
  have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) :=
    F7.normalizer_le_normalizer_centralizer _ (hLW hg)
  have h1 : g * x⁻¹ * g⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hgC x⁻¹).mp (Subgroup.inv_mem _ hxW)
  have e : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hxW h1

theorem card_fixed_le_of_sum_ch6 (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hL₁ : L ≤ Subgroup.normalizer (W₁ : Set G)) (hL₂ : L ≤ Subgroup.normalizer (W₂ : Set G))
    (hdisj : W₁ ⊓ W₂ = ⊥) (hsup : W₁ ⊔ W₂ = V) (h₁ : IsNatModCh5 L W₁ n)
    (h₂ : IsNatModCh5 L W₂ n)
    (hker : ∀ ℓ ∈ L, ℓ ∈ Subgroup.centralizer (W₁ : Set G) ↔
      ℓ ∈ Subgroup.centralizer (W₂ : Set G))
    {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx₁ : x ∈ Subgroup.normalizer (W₁ : Set G)) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hxC : x ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 2 ^ n * 2 ^ n := by
  classical
  have hW₁V : W₁ ≤ V := hsup ▸ le_sup_left
  have hW₂V : W₂ ≤ V := hsup ▸ le_sup_right
  have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
    hVc a (hW₁V ha) b (hW₂V hb)
  obtain ⟨k, hk⟩ := hx2
  have hCV : x ∈ Subgroup.centralizer (W₁ : Set G) → x ∈ Subgroup.centralizer (W₂ : Set G) →
      x ∈ Subgroup.centralizer (V : Set G) := by
    intro c1 c2
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.ge hv)
    have e1 := Subgroup.mem_centralizer_iff.mp c1 a ha
    have e2 := Subgroup.mem_centralizer_iff.mp c2 b hb
    calc a * b * x = a * (b * x) := by group
      _ = a * (x * b) := by rw [e2]
      _ = (a * x) * b := by group
      _ = (x * a) * b := by rw [e1]
      _ = x * (a * b) := by group
  have hpow : ∀ W : Subgroup G, x ^ 2 ^ k ∈ Subgroup.centralizer (W : Set G) := fun W => by
    rw [hk]
    exact Subgroup.one_mem _
  by_cases hx₂ : x ∈ Subgroup.normalizer (W₂ : Set G)
  ·
    have hx₁C : x ∉ Subgroup.centralizer (W₁ : Set G) := by
      intro c1
      apply hxC
      refine hCV c1 (h₂.mem_centralizer_of_pow ⟨x, hx₂⟩ (fun g hg => ?_) k (hpow W₂))
      have hm := commutator_mem_inf_centralizer_ch6 hxL hL₁ c1 hg
      exact (hker _ hm.1).mp hm.2
    have hx₂C : x ∉ Subgroup.centralizer (W₂ : Set G) := by
      intro c2
      apply hxC
      refine hCV (h₁.mem_centralizer_of_pow ⟨x, hx₁⟩ (fun g hg => ?_) k (hpow W₁)) c2
      have hm := commutator_mem_inf_centralizer_ch6 hxL hL₂ c2 hg
      exact (hker _ hm.1).mpr hm.2
    have hle₁ := h₁.data.card_fixed_le_two_pow ⟨x, hx₁⟩ hxL hx₁C
    have hle₂ := h₂.data.card_fixed_le_two_pow ⟨x, hx₂⟩ hxL hx₂C
    choose a ha b hb hab using fun v : ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) =>
      exists_mul_of_mem_sup hcomm (hsup.ge v.2.1)
    have hfix : ∀ v : ↥(V ⊓ Subgroup.centralizer ({x} : Set G)),
        x * a v * x⁻¹ = a v ∧ x * b v * x⁻¹ = b v := by
      intro v
      refine conj_eq_of_conj_mul_eq hdisj hx₁ hx₂ (ha v) (hb v) ?_
      have hv := Subgroup.mem_centralizer_iff.mp v.2.2 x (Set.mem_singleton x)
      rw [hab v, hv, mul_inv_cancel_right]
    have hcent : ∀ {y : G}, x * y * x⁻¹ = y → y ∈ Subgroup.centralizer ({x} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [hy]
    let F : ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) →
        ↥(W₁ ⊓ Subgroup.centralizer ({x} : Set G)) ×
          ↥(W₂ ⊓ Subgroup.centralizer ({x} : Set G)) := fun v =>
      (⟨a v, ha v, hcent (hfix v).1⟩, ⟨b v, hb v, hcent (hfix v).2⟩)
    have hF : Function.Injective F := by
      intro v w hvw
      have h1 : a v = a w := congrArg (fun p => (p.1 : G)) hvw
      have h2 : b v = b w := congrArg (fun p => (p.2 : G)) hvw
      apply Subtype.ext
      rw [← hab v, ← hab w, h1, h2]
    calc Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) ≤
        Nat.card (↥(W₁ ⊓ Subgroup.centralizer ({x} : Set G)) ×
          ↥(W₂ ⊓ Subgroup.centralizer ({x} : Set G))) := Nat.card_le_card_of_injective F hF
      _ = Nat.card ↥(W₁ ⊓ Subgroup.centralizer ({x} : Set G)) *
          Nat.card ↥(W₂ ⊓ Subgroup.centralizer ({x} : Set G)) := Nat.card_prod _ _
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hle₁ hle₂
  ·
    set W₂' := W₂.map (MulAut.conj x).toMonoidHom with hW₂'
    have hN : L ≤ Subgroup.normalizer ((W₂ ⊓ W₂' : Subgroup G) : Set G) := fun _ hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hL₂ hl, le_normalizer_map_conj_ch6 hL₂ hxL hl⟩
    have h0 : W₂ ⊓ W₂' = ⊥ := by
      rcases h₂.irreducible (W₂ ⊓ W₂') inf_le_left hN with h0 | h0
      · exact h0
      · exfalso
        apply hx₂
        have hle : W₂ ≤ W₂' := (le_of_eq h0.symm).trans inf_le_right
        have hcard : Nat.card W₂' = Nat.card W₂ :=
          Subgroup.card_map_of_injective (MulAut.conj x).injective
        exact mem_normalizer_of_map_conj_eq_natSum (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
    have hdisj' : (V ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ W₂ = ⊥ := by
      rw [eq_bot_iff, ← h0]
      rintro y ⟨⟨-, hyx⟩, hy⟩
      refine ⟨hy, y, hy, ?_⟩
      have hv := Subgroup.mem_centralizer_iff.mp hyx x (Set.mem_singleton x)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hv, mul_inv_cancel_right]
    have hcomm' : ∀ y ∈ V ⊓ Subgroup.centralizer ({x} : Set G), ∀ z ∈ W₂, y * z = z * y :=
      fun y hy z hz => hVc y hy.1 z (hW₂V hz)
    have hc1 := card_sup_eq_mul hdisj' hcomm'
    have hc2 := card_sup_eq_mul hdisj hcomm
    rw [hsup] at hc2
    have hle : Nat.card ↥((V ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ W₂) ≤ Nat.card V :=
      Subgroup.card_le_of_le (sup_le inf_le_left hW₂V)
    have hpos : 0 < Nat.card W₂ := Nat.card_pos
    have h3 : Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) * Nat.card W₂ ≤
        Nat.card W₁ * Nat.card W₂ := by
      rw [← hc1, ← hc2]
      exact hle
    rw [← h₁.card_eq]
    exact Nat.le_of_mul_le_mul_right h3 hpos

end Fixed

end CFSG.Quasithin.H13
