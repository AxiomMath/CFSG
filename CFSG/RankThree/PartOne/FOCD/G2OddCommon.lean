module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.RankThree.PartOne.FOCD.RankInner

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.LieType.Chevalley

@[expose] def piFinTwoMulEquiv (G : Type*) [Group G] : (Fin 2 → G) ≃* G × G :=
  { piFinTwoEquiv (fun _ : Fin 2 => G) with map_mul' := fun _ _ => rfl }

theorem card_le_sq_of_prod {p : ℕ} (hp : p.Prime) {G₁ G₂ : Type} [Group G₁] [Group G₂]
    [IsCyclic G₁] [IsCyclic G₂] [Finite G₁] [Finite G₂] (H : Subgroup (G₁ × G₂))
    (hH : ∀ h ∈ H, h ^ p = 1) : Nat.card H ≤ p ^ 2 := by
  classical
  have hcyc : ∀ {G : Type} [Group G] [IsCyclic G] [Finite G],
      Nat.card {a : G // a ^ p = 1} ≤ p := by
    intro G _ _ _
    have := Fintype.ofFinite G
    have := IsCyclic.card_pow_eq_one_le (α := G) hp.pos
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact this
  let ι : H → {a : G₁ // a ^ p = 1} × {a : G₂ // a ^ p = 1} := fun h =>
    (⟨(h : G₁ × G₂).1, by
      have := congrArg Prod.fst (hH h h.2)
      simpa using this⟩,
     ⟨(h : G₁ × G₂).2, by
      have := congrArg Prod.snd (hH h h.2)
      simpa using this⟩)
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst hxy)
    · exact congrArg Subtype.val (congrArg Prod.snd hxy)
  calc Nat.card H ≤ Nat.card ({a : G₁ // a ^ p = 1} × {a : G₂ // a ^ p = 1}) :=
        Nat.card_le_card_of_injective ι hι
    _ = Nat.card {a : G₁ // a ^ p = 1} * Nat.card {a : G₂ // a ^ p = 1} := Nat.card_prod _ _
    _ ≤ p * p := Nat.mul_le_mul hcyc hcyc
    _ = p ^ 2 := (sq p).symm

variable {T : Type} [Group T]

theorem isPGroup_of_exponent {p : ℕ} (hp : p.Prime) (R : Subgroup T) (hR : ∀ r ∈ R, r ^ p = 1) :
    IsPGroup p R := by
  have : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hR g.1 g.2))
  rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
  · exact ⟨0, by rw [h2]; simp⟩
  · exact ⟨1, by rw [h2]; simp⟩

theorem pRankLeTwo_of_conj_cyclic2 {p : ℕ} (hp : p.Prime) {H : Subgroup T} {G₁ G₂ : Type}
    [Group G₁] [Group G₂] [IsCyclic G₁] [IsCyclic G₂] [Finite G₁] [Finite G₂]
    (e : ↥H ≃* G₁ × G₂)
    (hconj : ∀ P : Subgroup T, IsPGroup p P →
      ∃ g : T, P.map (MulAut.conj g).toMonoidHom ≤ H) : PRankLeTwo p T := by
  intro R hRp _
  obtain ⟨g, hg⟩ := hconj R (isPGroup_of_exponent hp R hRp)
  set R' : Subgroup T := R.map (MulAut.conj g).toMonoidHom with hR'
  have hc1 : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hc2 : Nat.card (R'.subgroupOf H) = Nat.card R' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv
  set H₀ : Subgroup (G₁ × G₂) := (R'.subgroupOf H).map e.toMonoidHom with hH₀
  have hc3 : Nat.card H₀ = Nat.card (R'.subgroupOf H) :=
    Subgroup.card_map_of_injective e.injective
  have hexp : ∀ h ∈ H₀, h ^ p = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow]
    have h1 : (r : T) ^ p = 1 := by
      have hr' : (r : T) ∈ R' := hr
      obtain ⟨s, hs, hsr⟩ := hr'
      rw [← hsr]
      change (g * s * g⁻¹) ^ p = 1
      rw [conj_pow, hRp s hs]
      simp
    have : r ^ p = 1 := Subtype.ext (by simpa using h1)
    rw [this, map_one]
  have := card_le_sq_of_prod hp H₀ hexp
  rw [hc3, hc2, hc1] at this
  exact this

theorem pRankLeTwo_of_mulEquiv {p : ℕ} {T' : Type} [Group T'] (φ : T ≃* T')
    (h : PRankLeTwo p T') : PRankLeTwo p T := by
  intro R hRp hRc
  have h1 := h (R.map φ.toMonoidHom)
    (by rintro _ ⟨r, hr, rfl⟩; rw [← map_pow, hRp r hr, map_one])
    (by
      rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_mul, hRc r hr s hs])
  rwa [Subgroup.card_map_of_injective φ.injective] at h1

theorem pRankLeTwo_of_cyclic {p : ℕ} (hp : p.Prime)
    (hcyc : ∀ P : Subgroup T, IsPGroup p P → IsCyclic P) : PRankLeTwo p T := by
  intro R hRp _
  have hRP := isPGroup_of_exponent hp R hRp
  have := hcyc R hRP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hRp g.1 g.2))
  have h2 : Nat.card R = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h3 : Nat.card R ≤ p := h2 ▸ Nat.le_of_dvd hp.pos h1
  calc Nat.card R ≤ p := h3
    _ ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p

theorem sq_eq_one_of_central_of_equiv_sl2 {K : Type} [Field K] {Q : Type} [Group Q]
    (e : SL2 K ≃* Q) {z : Q} (hz : ∀ q : Q, z * q = q * z) : z ^ 2 = 1 := by
  have hc : e.symm z ∈ Subgroup.center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := hz (e g)
    have h2 := congrArg e.symm this
    rw [map_mul, map_mul, e.symm_apply_apply] at h2
    exact h2.symm
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hsq : (e.symm z) ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hrz]
    simp only [Matrix.SpecialLinearGroup.coe_one]
    rw [← map_mul, ← pow_two, hr2, map_one]
  have := congrArg e hsq
  rwa [map_pow, e.apply_symm_apply, map_one] at this

theorem eq_one_of_sq_of_pow_odd {G : Type*} [Group G] {z : G} {p : ℕ} (hp : Odd p)
    (h2 : z ^ 2 = 1) (hpz : z ^ p = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hp
  have h3 : z ^ p = z := by
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← h3]
  exact hpz

theorem hZ_of_equiv_sl2 {K : Type} [Field K] {G : Type} [Group G] {Q : Subgroup G} {p : ℕ}
    (hp : Odd p) (e : SL2 K ≃* ↥Q) :
    ∀ z ∈ Q, (∀ q ∈ Q, z * q = q * z) → z ^ p = 1 → z = 1 := by
  intro z hzQ hzc hzp
  have h1 : (⟨z, hzQ⟩ : ↥Q) ^ 2 = 1 :=
    sq_eq_one_of_central_of_equiv_sl2 e fun q => Subtype.ext (hzc q.1 q.2)
  have h2 : z ^ 2 = 1 := by simpa using congrArg Subtype.val h1
  exact eq_one_of_sq_of_pow_odd hp h2 hzp

end CFSG.RankThree.PartOne.FOCD
