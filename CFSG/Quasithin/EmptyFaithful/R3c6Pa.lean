module

public import CFSG.Quasithin.EmptyFaithful.R3c6Sign
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs

public section

namespace CFSG.Quasithin.R3c6

open CFSG.Open

section Abstract

variable {X : Type} [Group X]

structure BorelComp (X : Type) [Group X] (Q : Subgroup X) : Prop where
  strong : ∀ U : Subgroup X, U ≤ Q → U ≠ ⊥ →
    Subgroup.normalizer (U : Set X) ≤ Subgroup.normalizer (Q : Set X)
  cyclic : ∀ R : Subgroup X, R ≤ Subgroup.normalizer (Q : Set X) → IsPGroup 3 ↥R → IsCyclic ↥R
  elem : ∃ Z : Subgroup X, Z ≤ Q ∧ (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧ (∀ a ∈ Z, a ^ 2 = 1) ∧
    2 ^ 2 ≤ Nat.card Z

theorem sylow_and_cyclic_of_hom [Finite X] {Q₀ : Subgroup X} (hQ2 : IsPGroup 2 ↥Q₀)
    {F : Type} [Field F] (hF : ∀ (t : F) (k : ℕ), t ^ 2 ^ k = 1 → t = 1)
    (φ : ↥(Subgroup.normalizer (Q₀ : Set X)) →* F)
    (hφ : ∀ x : ↥(Subgroup.normalizer (Q₀ : Set X)), φ x = 1 → (x : X) ∈ Q₀) :
    (∃ S : Sylow 2 X, (S : Subgroup X) = Q₀) ∧
      ∀ R : Subgroup X, R ≤ Subgroup.normalizer (Q₀ : Set X) → IsPGroup 3 ↥R → IsCyclic ↥R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
    refine ⟨S, le_antisymm ?_ hS⟩
    by_contra hle
    set S' : Subgroup X := (S : Subgroup X) with hS'
    have : Group.IsNilpotent ↥S' := S.isPGroup'.isNilpotent
    set Q' : Subgroup ↥S' := Q₀.subgroupOf S' with hQ'
    have hlt : Q' < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => hle ?_
      intro x hx
      have : (⟨x, hx⟩ : ↥S') ∈ Q' := h ▸ Subgroup.mem_top _
      exact this
    obtain ⟨x, hxN, hxQ⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hlt)
    have hQ0 : Q₀ = Q'.map S'.subtype := (Subgroup.map_subgroupOf_eq_of_le hS).symm
    have hxN' : (x : X) ∈ Subgroup.normalizer (Q₀ : Set X) := by
      rw [hQ0]
      exact mem_normalizer_map_subtype.2 hxN
    obtain ⟨k, hk⟩ := S.isPGroup' x
    have hk' : ((⟨(x : X), hxN'⟩ : ↥(Subgroup.normalizer (Q₀ : Set X))) ^ 2 ^ k) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have h1 : φ ⟨(x : X), hxN'⟩ = 1 := hF _ k (by rw [← map_pow, hk', map_one])
    exact hxQ (hφ _ h1)
  · intro R hRN hR3
    set R' : Subgroup ↥(Subgroup.normalizer (Q₀ : Set X)) :=
      R.subgroupOf (Subgroup.normalizer (Q₀ : Set X)) with hR'
    have hR'3 : IsPGroup 3 ↥R' := hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
    have hinj : Function.Injective (φ.comp R'.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxQ : (((x : ↥(Subgroup.normalizer (Q₀ : Set X))) : X)) ∈ Q₀ := hφ _ hx
      have hxR : (((x : ↥(Subgroup.normalizer (Q₀ : Set X))) : X)) ∈ R := x.2
      have hdisj : Disjoint Q₀ R := IsPGroup.disjoint_of_ne 2 3 (by norm_num) Q₀ R hQ2 hR3
      have h1 : (((x : ↥(Subgroup.normalizer (Q₀ : Set X))) : X)) = 1 := by
        have := hdisj.le_bot ⟨hxQ, hxR⟩
        simpa using this
      exact Subtype.ext (Subtype.ext h1)
    have hc : IsCyclic ↥R' := isCyclic_of_injective_ringHom _ hinj
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hRN).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRN).symm.injective

end Abstract

section Transfer

variable {X : Type} [Group X]

theorem eq_bot_of_stronglyEmbedded [Finite X] {Q U : Subgroup X}
    (h : fusionStronglyEmbedded (Subgroup.normalizer (Q : Set X))) {g : X}
    (hg : g ∉ Subgroup.normalizer (Q : Set X)) (hU2 : IsPGroup 2 ↥U) (hUQ : U ≤ Q)
    (hUg : ∀ u ∈ U, g * u * g⁻¹ ∈ Q) : U = ⊥ := by
  by_contra hU
  obtain ⟨-, -, hodd⟩ := h
  have hgodd := hodd g hg
  set B := Subgroup.normalizer (Q : Set X) with hB
  have hQB : Q ≤ B := Subgroup.le_normalizer
  have hUle : U ≤ B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro u hu
    refine ⟨hQB (hUQ hu), Subgroup.mem_map.mpr ⟨g * u * g⁻¹, hQB (hUg u hu), ?_⟩⟩
    simp [mul_assoc]
  have hne : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU
  obtain ⟨n, hn, hcard⟩ := hU2.nontrivial_iff_card.mp hne
  have hdvd : 2 ∣ Nat.card ↥(B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup X) :=
    (dvd_pow_self 2 hn.ne').trans (hcard ▸ Subgroup.card_dvd_of_le hUle)
  exact (Nat.not_even_iff_odd.mpr hgodd) (even_iff_two_dvd.mpr hdvd)

theorem le_of_normal_odd_index [Finite X] (X₁ : Subgroup X) [X₁.Normal] (hodd : ¬ 2 ∣ X₁.index)
    (S : Sylow 2 X) : (S : Subgroup X) ≤ X₁ := by
  intro x hx
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hq : (QuotientGroup.mk x : X ⧸ X₁) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hk']
    rfl
  have hd1 : orderOf (QuotientGroup.mk x : X ⧸ X₁) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hq
  have hd2 : orderOf (QuotientGroup.mk x : X ⧸ X₁) ∣ X₁.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  obtain ⟨j, hj, hjd⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
  have hj0 : j = 0 := by
    by_contra hj0
    exact hodd ((dvd_pow_self 2 hj0).trans (hjd ▸ hd2))
  rw [hj0, pow_zero] at hjd
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 hjd)

theorem exists_sylow_subgroupOf [Finite X] (X₁ : Subgroup X) [X₁.Normal] (hodd : ¬ 2 ∣ X₁.index)
    (S : Sylow 2 X) :
    ∃ S₁ : Sylow 2 ↥X₁, (S₁ : Subgroup ↥X₁) = (S : Subgroup X).subgroupOf X₁ := by
  have hle := le_of_normal_odd_index X₁ hodd S
  have hp : IsPGroup 2 ((S : Subgroup X).subgroupOf X₁) :=
    S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hidx : ¬ 2 ∣ ((S : Subgroup X).subgroupOf X₁).index := by
    have h1 := Subgroup.relIndex_mul_index hle
    intro hd
    have hd' : 2 ∣ (S : Subgroup X).index := by
      rw [← h1]
      exact dvd_mul_of_dvd_left hd _
    exact S.not_dvd_index hd'
  exact ⟨hp.toSylow hidx, rfl⟩

theorem normalizer_le_of_normal_odd [Finite X] (X₁ : Subgroup X) [X₁.Normal] (hodd : ¬ 2 ∣ X₁.index)
    {q k : ℕ} (hB : fusionBenderBorel ↥X₁ q k) (Q : Sylow 2 X) {U : Subgroup X}
    (hUQ : U ≤ (Q : Subgroup X)) (hU : U ≠ ⊥) :
    Subgroup.normalizer (U : Set X) ≤ Subgroup.normalizer ((Q : Subgroup X) : Set X) := by
  intro g hg
  by_contra hgQ
  have hQle := le_of_normal_odd_index X₁ hodd Q
  have hQ2le := le_of_normal_odd_index X₁ hodd (g • Q)
  obtain ⟨S₁, hS₁⟩ := exists_sylow_subgroupOf X₁ hodd Q
  obtain ⟨S₂, hS₂⟩ := exists_sylow_subgroupOf X₁ hodd (g • Q)
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq ↥X₁ S₁ S₂
  have hne : S₂ ≠ S₁ := by
    intro h
    apply hgQ
    have h1 : ((g • Q : Sylow 2 X) : Subgroup X) = (Q : Subgroup X) := by
      have h2 : (S₂ : Subgroup ↥X₁) = (S₁ : Subgroup ↥X₁) := congrArg _ h
      rw [hS₁, hS₂] at h2
      exact le_antisymm
        (fun x hx => by
          have : (⟨x, hQ2le hx⟩ : ↥X₁) ∈ ((g • Q : Sylow 2 X) : Subgroup X).subgroupOf X₁ := hx
          rw [h2] at this
          exact this)
        (fun x hx => by
          have : (⟨x, hQle hx⟩ : ↥X₁) ∈ (Q : Subgroup X).subgroupOf X₁ := hx
          rw [← h2] at this
          exact this)
    have h3 : g • Q = Q := Sylow.ext h1
    have h4 := Sylow.smul_eq_iff_mem_normalizer.mp h3
    exact h4
  have hg₁N : g₁ ∉ Subgroup.normalizer (((S₁ : Subgroup ↥X₁)) : Set ↥X₁) := by
    intro h
    exact hne (hg₁.symm.trans (Sylow.smul_eq_iff_mem_normalizer.mpr h))
  have hUle : U ≤ X₁ := hUQ.trans hQle
  set U' : Subgroup ↥X₁ := U.subgroupOf X₁ with hU'
  have hU'S₁ : U' ≤ (S₁ : Subgroup ↥X₁) := by
    intro u hu
    rw [hS₁]
    exact hUQ hu
  have hU'ne : U' = ⊥ := by
    refine eq_bot_of_stronglyEmbedded (hB S₁).1 (g := g₁⁻¹) ?_ ?_ hU'S₁ ?_
    · intro h
      exact hg₁N (by simpa using h)
    · exact S₁.isPGroup'.to_le hU'S₁
    · intro u hu
      have huU : ((u : ↥X₁) : X) ∈ U := hu
      have hu2 : (u : ↥X₁) ∈ (S₂ : Subgroup ↥X₁) := by
        rw [hS₂]
        show ((u : ↥X₁) : X) ∈ ((g • Q : Sylow 2 X) : Subgroup X)
        have hgu : g⁻¹ * ((u : ↥X₁) : X) * g ∈ U := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) ((u : ↥X₁) : X)).mp huU
          simpa [mul_assoc] using this
        have hmem : g⁻¹ * ((u : ↥X₁) : X) * g ∈ (Q : Subgroup X) := hUQ hgu
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        refine Subgroup.mem_map.mpr ⟨g⁻¹ * ((u : ↥X₁) : X) * g, hmem, ?_⟩
        simp [mul_assoc]
      rw [← hg₁, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hu2
      obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.mp hu2
      have : g₁⁻¹ * (u : ↥X₁) * g₁⁻¹⁻¹ = s := by
        rw [← hsu]
        simp [mul_assoc]
      rw [this]
      exact hs
  apply hU
  rw [eq_bot_iff]
  intro u hu
  have : (⟨u, hUle hu⟩ : ↥X₁) ∈ U' := hu
  rw [hU'ne] at this
  simpa using this

theorem elem_of_normal_odd [Finite X] (X₁ : Subgroup X) [X₁.Normal] (hodd : ¬ 2 ∣ X₁.index)
    {q k : ℕ} (hq : 2 ^ 2 ≤ q) (hB : fusionBenderBorel ↥X₁ q k) (Q : Sylow 2 X) :
    ∃ Z : Subgroup X, Z ≤ (Q : Subgroup X) ∧ (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧
      (∀ a ∈ Z, a ^ 2 = 1) ∧ 2 ^ 2 ≤ Nat.card Z := by
  obtain ⟨S₁, hS₁⟩ := exists_sylow_subgroupOf X₁ hodd Q
  obtain ⟨-, -, hZ2, hZcard, -⟩ := hB S₁
  set C : Subgroup ↥X₁ := (Subgroup.center ↥(S₁ : Subgroup ↥X₁)).map (S₁ : Subgroup ↥X₁).subtype
    with hC
  refine ⟨C.map X₁.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, ⟨z, hz, rfl⟩, rfl⟩
    have h1 : (z : ↥X₁) ∈ (Q : Subgroup X).subgroupOf X₁ := by
      rw [← hS₁]
      exact z.2
    exact h1
  · rintro _ ⟨c, ⟨z, hz, rfl⟩, rfl⟩ _ ⟨c', ⟨z', hz', rfl⟩, rfl⟩
    show ((z : ↥X₁) : X) * ((z' : ↥X₁) : X) = ((z' : ↥X₁) : X) * ((z : ↥X₁) : X)
    have := Subgroup.mem_center_iff.mp hz' z
    exact congrArg (fun w : ↥S₁ => (((w : ↥X₁)) : X)) this
  · rintro _ ⟨c, ⟨z, hz, rfl⟩, rfl⟩
    show (((z : ↥X₁)) : X) ^ 2 = 1
    exact congrArg (fun w : ↥S₁ => (((w : ↥X₁)) : X)) (hZ2 z hz)
  · rw [Subgroup.card_map_of_injective X₁.subtype_injective,
      Subgroup.card_map_of_injective (S₁ : Subgroup ↥X₁).subtype_injective, hZcard]
    exact hq

theorem borelComp_of_normal_odd [Finite X] (X₁ : Subgroup X) [X₁.Normal] (hodd : ¬ 2 ∣ X₁.index)
    {q k : ℕ} (hq : 2 ^ 2 ≤ q) (hB : fusionBenderBorel ↥X₁ q k) (Q : Sylow 2 X)
    (hcyc : ∀ R : Subgroup X, R ≤ Subgroup.normalizer ((Q : Subgroup X) : Set X) →
      IsPGroup 3 ↥R → IsCyclic ↥R) :
    BorelComp X (Q : Subgroup X) :=
  ⟨fun _ hUQ hU => normalizer_le_of_normal_odd X₁ hodd hB Q hUQ hU, hcyc,
    elem_of_normal_odd X₁ hodd hq hB Q⟩

end Transfer

section Conj

variable {X : Type} [Group X]

theorem cyclic_of_sylow_conj [Finite X] {S₀ : Sylow 2 X}
    (h₀ : ∀ R : Subgroup X, R ≤ Subgroup.normalizer ((S₀ : Subgroup X) : Set X) →
      IsPGroup 3 ↥R → IsCyclic ↥R) (Q : Sylow 2 X) :
    ∀ R : Subgroup X, R ≤ Subgroup.normalizer ((Q : Subgroup X) : Set X) →
      IsPGroup 3 ↥R → IsCyclic ↥R := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ Q
  intro R hR hR3
  set R' : Subgroup X := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'
  have hR'N : R' ≤ Subgroup.normalizer ((S₀ : Subgroup X) : Set X) := by
    rintro _ ⟨r, hr, rfl⟩
    have hrQ : r • Q = Q := Sylow.smul_eq_iff_mem_normalizer.mpr (hR hr)
    have h1 : (g⁻¹ * r * g) • S₀ = S₀ := by
      rw [mul_smul, mul_smul, hg, hrQ, ← hg, inv_smul_smul]
    have h2 := Sylow.smul_eq_iff_mem_normalizer.mp h1
    simpa using h2
  have hequiv : R ≃* R' := Subgroup.equivMapOfInjective R (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective
  have hR'3 : IsPGroup 3 ↥R' := hR3.of_equiv hequiv
  have hc := h₀ R' hR'N hR'3
  exact isCyclic_of_injective hequiv.toMonoidHom hequiv.injective

theorem mem_normalizer_map_equiv {Y : Type} [Group Y] (e : X ≃* Y) (H : Subgroup X) (g : X) :
    e g ∈ Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup Y) : Set Y) ↔
      g ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have h1 := h (e x)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h1
    simpa using h1
  · intro h y
    have h1 := h (e.symm y)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simpa using h1

theorem BorelComp.of_mulEquiv {Y : Type} [Group Y] (e : X ≃* Y) {Q : Subgroup X}
    (h : BorelComp Y (Q.map e.toMonoidHom)) : BorelComp X Q := by
  refine ⟨?_, ?_, ?_⟩
  · intro U hUQ hU g hg
    have hU' : U.map e.toMonoidHom ≠ ⊥ := by
      intro h0
      apply hU
      rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h0
      exact h0
    have h1 := h.strong (U.map e.toMonoidHom) (Subgroup.map_mono hUQ) hU'
    have h2 : e g ∈ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup Y) : Set Y) :=
      (mem_normalizer_map_equiv e U g).2 hg
    exact (mem_normalizer_map_equiv e Q g).1 (h1 h2)
  · intro R hR hR3
    set R' : Subgroup Y := R.map e.toMonoidHom with hR'
    have hR'N : R' ≤ Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup Y) : Set Y) := by
      rintro _ ⟨r, hr, rfl⟩
      exact (mem_normalizer_map_equiv e Q r).2 (hR hr)
    have hequiv : R ≃* R' := Subgroup.equivMapOfInjective R e.toMonoidHom e.injective
    have hR'3 : IsPGroup 3 ↥R' := hR3.of_equiv hequiv
    have hc := h.cyclic R' hR'N hR'3
    exact isCyclic_of_injective hequiv.toMonoidHom hequiv.injective
  · obtain ⟨Z, hZQ, hZc, hZe, hZcard⟩ := h.elem
    refine ⟨Z.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have := hZQ hz
      rw [Subgroup.mem_map_equiv] at this
      simpa using this
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      show e.symm a * e.symm b = e.symm b * e.symm a
      rw [← map_mul, ← map_mul, hZc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      show (e.symm a) ^ 2 = 1
      rw [← map_pow, hZe a ha, map_one]
    · rw [Subgroup.card_map_of_injective e.symm.injective]
      exact hZcard

theorem exists_sylow_map_equiv {Y : Type} [Group Y] [Finite X] (e : X ≃* Y) (Q : Sylow 2 X) :
    ∃ S : Sylow 2 Y, (S : Subgroup Y) = (Q : Subgroup X).map e.toMonoidHom := by
  have hp : IsPGroup 2 ↥((Q : Subgroup X).map e.toMonoidHom) :=
    Q.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)
  have hidx : ¬ 2 ∣ ((Q : Subgroup X).map e.toMonoidHom).index := by
    have h := Subgroup.index_map_equiv (H := (Q : Subgroup X)) e
    rw [show ((Q : Subgroup X).map e.toMonoidHom).index = (Q : Subgroup X).index from h]
    exact Q.not_dvd_index
  exact ⟨hp.toSylow hidx, rfl⟩

theorem borelComp_forall_of_mulEquiv {Y : Type} [Group Y] [Finite X] (e : X ≃* Y)
    (h : ∀ S : Sylow 2 Y, BorelComp Y (S : Subgroup Y)) (Q : Sylow 2 X) :
    BorelComp X (Q : Subgroup X) := by
  obtain ⟨S, hS⟩ := exists_sylow_map_equiv e Q
  refine BorelComp.of_mulEquiv e ?_
  rw [← hS]
  exact h S

end Conj

end CFSG.Quasithin.R3c6
