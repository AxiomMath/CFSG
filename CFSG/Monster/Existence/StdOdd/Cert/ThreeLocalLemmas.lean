module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open Subgroup CFSG.OrderReductions.FrattiniAutomorphisms

section Frattini

theorem frattini_quotient_card_eq_pow_of_rank_le {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q]
    [Finite Q] (hQ : IsPGroup p Q) {r : ℕ} (hrank : Group.rank Q ≤ r) :
    ∃ d : ℕ, d ≤ r ∧ Nat.card (Q ⧸ frattini Q) = p ^ d := by
  obtain ⟨-, hcomm, hpow, helem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ
  have hcard := CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := p) (Q ⧸ frattini Q)
  refine ⟨CFSG.generatorRank (Q ⧸ frattini Q), ?_, hcard⟩
  rw [CFSG.generatorRank_eq_group_rank]
  exact (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini Q))
    (QuotientGroup.mk'_surjective _)).trans hrank

theorem mulAut_eq_one_of_modEq {V : Type*} [Group V] [Finite V] {p q d : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hV : Nat.card V = p ^ d)
    (hord : ∀ k, k ≤ d → p ^ d ≡ p ^ k [MOD q] → k = d) (α : MulAut V) (hα : α ^ q = 1) :
    α = 1 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let σ : Equiv.Perm V := MulAut.toPerm V α
  have hσ : σ ^ q = 1 := by rw [← map_pow, hα, map_one]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := (⇑σ : Function.End V)) (p := q) (n := 1)
    (by
      rw [pow_one]
      have h2 := Equiv.Perm.coe_pow σ q
      rw [hσ, Equiv.Perm.coe_one] at h2
      exact h2.symm)
  let Fix : Subgroup V := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id V)
  have hFix : Fintype.card (Function.fixedPoints (⇑σ : Function.End V)) = Nat.card Fix := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.refl _)
  rw [← Nat.card_eq_fintype_card, hFix, hV] at hmod
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1
    (hV ▸ Subgroup.card_subgroup_dvd_card Fix)
  have hkd := hord k hk (by rw [← hkc]; exact hmod)
  have hfull : Nat.card Fix = Nat.card V := by rw [hkc, hV, hkd]
  have htop : Fix = ⊤ := (Subgroup.card_eq_iff_eq_top Fix).1 hfull
  ext x
  have hx : x ∈ Fix := htop ▸ Subgroup.mem_top x
  exact hx

theorem le_centralizer_of_frattini {G : Type*} [Group G] [Finite G] {p q r : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hpq : p ≠ q) {F : Subgroup G} (hF : IsPGroup p F) (hrank : Group.rank F ≤ r)
    (hord : ∀ d, d ≤ r → ∀ k, k ≤ d → p ^ d ≡ p ^ k [MOD q] → k = d) {g : G} (hg : orderOf g = q)
    (hgF : g ∈ normalizer (F : Set G)) : F ≤ centralizer ({g} : Set G) := by
  let a : ↥(normalizer (F : Set G)) := ⟨g, hgF⟩
  let α : MulAut F := F.normalizerMonoidHom a
  have hαq : α ^ q = 1 := by
    have h : a ^ q = 1 := Subtype.ext (by simpa [a] using hg ▸ pow_orderOf_eq_one g)
    rw [← map_pow, h, map_one]
  obtain ⟨d, hdr, hd⟩ := frattini_quotient_card_eq_pow_of_rank_le hF hrank
  have h1 : quotientAutomorphism (frattini F) α = 1 :=
    mulAut_eq_one_of_modEq hd (fun k hk h => hord d hdr k hk h) _
      (by rw [← map_pow, hαq, map_one])
  have hα1 : α = 1 := by
    by_contra hne
    have hdvd : orderOf α ∣ q := orderOf_dvd_of_pow_eq_one hαq
    have hordα : orderOf α = q := ((Nat.dvd_prime (Fact.out : q.Prime)).1 hdvd).resolve_left
      fun h => hne (orderOf_eq_one_iff.1 h)
    have hnd : ¬ q ∣ Nat.card F := by
      obtain ⟨n, hn⟩ := hF.exists_card_eq
      rw [hn]
      intro h
      exact hpq (((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).1
        ((Fact.out : q.Prime).dvd_of_dvd_pow h)).symm)
    exact hne (prime_order_frattini_kernel_trivial q α hordα hnd h1)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have h2 := congrArg (fun β : MulAut F => ((β ⟨x, hx⟩ : F) : G)) hα1
  simp only [α, a, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
  exact mul_inv_eq_iff_eq_mul.1 h2

end Frattini

section Conjugation

variable {G : Type*} [Group G]

theorem exists_conj_map_le_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {X : Subgroup G} (hX : IsPGroup p X) : ∃ c : G, X.map (MulAut.conj c).toMonoidHom ≤ P := by
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨c, ?_⟩
  calc X.map (MulAut.conj c).toMonoidHom ≤ (Q : Subgroup G).map (MulAut.conj c).toMonoidHom :=
        Subgroup.map_mono hQ
    _ = ((c • Q : Sylow p G) : Subgroup G) := by rw [Sylow.coe_subgroup_smul]; rfl
    _ = P := by rw [hc]

theorem mem_normalizer_map_conj (c : G) {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    c * g * c⁻¹ ∈ normalizer ((X.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  have h := Subgroup.map_equiv_normalizer_eq X (MulAut.conj c)
  have h2 : (MulAut.conj c).toMonoidHom g ∈ (normalizer X).map (MulAut.conj c).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hg
  rw [h] at h2
  simpa using h2

theorem orderOf_mul_mul_inv (c g : G) : orderOf (c * g * c⁻¹) = orderOf g := by
  have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective g
  simpa using this

theorem card_map_conjHom (c : G) (X : Subgroup G) :
    Nat.card (X.map (MulAut.conj c).toMonoidHom) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem exists_conj_elemAbelian_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (A : Subgroup G) (hp : ∀ a ∈ A, a ^ p = 1) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∃ (c : G) (B : Subgroup P), Nat.card B = Nat.card A ∧ (∀ b ∈ B, b ^ p = 1) ∧
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) ∧
      B.map (P : Subgroup G).subtype = A.map (MulAut.conj c).toMonoidHom := by
  have hA : IsPGroup p A := fun x => ⟨1, Subtype.ext (by simpa using hp x.1 x.2)⟩
  obtain ⟨c, hcA⟩ := exists_conj_map_le_sylow P hA
  refine ⟨c, (A.map (MulAut.conj c).toMonoidHom).subgroupOf P, ?_, ?_, ?_,
    Subgroup.map_subgroupOf_eq_of_le hcA⟩
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcA).toEquiv).trans (card_map_conjHom c A)
  · rintro b ⟨a, ha, hab⟩
    have hab : (MulAut.conj c).toMonoidHom a = (b : G) := hab
    apply Subtype.ext
    show (b : G) ^ p = 1
    rw [← hab, ← map_pow, hp a ha, map_one]
  · rintro b ⟨a, ha, hab⟩ b' ⟨a', ha', hab'⟩
    have hab : (MulAut.conj c).toMonoidHom a = (b : G) := hab
    have hab' : (MulAut.conj c).toMonoidHom a' = (b' : G) := hab'
    apply Subtype.ext
    show (b : G) * b' = b' * b
    rw [← hab, ← hab', ← map_mul, ← map_mul, hc a ha a' ha']

end Conjugation

section Perm

variable {N V : Type*} [Group N] [AddCommGroup V]

@[expose] def mulAutPerm (ι : N ≃* Multiplicative V) : MulAut N →* Equiv.Perm V :=
  (Equiv.permCongrHom (ι.toEquiv.trans Multiplicative.toAdd)).toMonoidHom.comp (MulAut.toPerm N)

theorem mulAutPerm_apply (ι : N ≃* Multiplicative V) (α : MulAut N) (x : V) :
    mulAutPerm ι α x = Multiplicative.toAdd (ι (α (ι.symm (Multiplicative.ofAdd x)))) := rfl

theorem mulAutPerm_zero (ι : N ≃* Multiplicative V) (α : MulAut N) : mulAutPerm ι α 0 = 0 := by
  rw [mulAutPerm_apply]
  simp only [ofAdd_zero, map_one, toAdd_one]

theorem symm_mulAutPerm (ι : N ≃* Multiplicative V) (α : MulAut N) (x : V) :
    ι.symm (Multiplicative.ofAdd (mulAutPerm ι α x)) = α (ι.symm (Multiplicative.ofAdd x)) := by
  rw [mulAutPerm_apply]
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem exists_perm_of_mem_normalizer {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (ι : N ≃* Multiplicative V) {g : G} (hg : g ∈ normalizer (N : Set G)) :
    ∃ σ : Equiv.Perm V, σ 0 = 0 ∧ (∀ n : ℕ, g ^ n = 1 → σ ^ n = 1) ∧
      (∀ x, ((ι.symm (Multiplicative.ofAdd (σ x)) : N) : G) =
        g * (ι.symm (Multiplicative.ofAdd x) : G) * g⁻¹) ∧
      Nat.card {x : V // σ x = x} ≤ Nat.card ↥(N ⊓ centralizer ({g} : Set G)) := by
  let β : MulAut N := N.normalizerMonoidHom ⟨g, hg⟩
  have hconj : ∀ y : N, ((β y : N) : G) = g * (y : G) * g⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ ⟨g, hg⟩ y
  have hσ : ∀ x, ((ι.symm (Multiplicative.ofAdd (mulAutPerm ι β x)) : N) : G) =
      g * (ι.symm (Multiplicative.ofAdd x) : G) * g⁻¹ := fun x => by
    rw [symm_mulAutPerm, hconj]
  refine ⟨mulAutPerm ι β, mulAutPerm_zero ι β, fun n hn => ?_, hσ, ?_⟩
  · have h : (⟨g, hg⟩ : ↥(normalizer (N : Set G))) ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [← map_pow, show β ^ n = 1 by rw [← map_pow, h, map_one], map_one]
  · refine Nat.card_le_card_of_injective
      (fun x => ⟨((ι.symm (Multiplicative.ofAdd x.1) : N) : G),
        Subgroup.mem_inf.2 ⟨(ι.symm (Multiplicative.ofAdd x.1)).2, ?_⟩⟩) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 := hσ x.1
      rw [x.2] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1.symm
    · intro x y hxy
      have h0 := congrArg Subtype.val hxy
      have h1 : ι.symm (Multiplicative.ofAdd x.1) = ι.symm (Multiplicative.ofAdd y.1) :=
        Subtype.ext h0
      exact Subtype.ext (Multiplicative.ofAdd.injective (ι.symm.injective h1))

end Perm

end CFSG.Monster.Existence.StdOdd.Cert
