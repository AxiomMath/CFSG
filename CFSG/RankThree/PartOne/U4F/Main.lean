module

public import CFSG.RankThree.PartOne.U4F.Transport
public import CFSG.RankThree.PartOne.U4F.Core

public section

namespace CFSG.RankThree.PartOne.U4F

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.BorelTits (unitaryInvolution)

variable {G : Type} [Group G] [Finite G]

theorem exists_gen_of_prime_card {R : Subgroup G} {r : ℕ} (hr : r.Prime) (hR : Nat.card ↥R = r) :
    ∃ a ∈ R, a ≠ 1 ∧ ∀ k ∈ R, ∃ n : ℕ, a ^ n = k := by
  have : Fact r.Prime := ⟨hr⟩
  have : Nontrivial ↥R := by
    rw [← Finite.one_lt_card_iff_nontrivial, hR]
    exact hr.one_lt
  obtain ⟨⟨a, ha⟩, hane⟩ := exists_ne (1 : ↥R)
  refine ⟨a, ha, fun h => hane (Subtype.ext h), fun k hk => ?_⟩
  have := mem_powers_of_prime_card hR (g := (⟨a, ha⟩ : ↥R)) hane (g' := ⟨k, hk⟩)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 this
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

omit [Finite G] in
theorem gamma_decomp {F P Q : Subgroup G} (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hint : (F ⊓ P) ⊓ (F ⊓ Q) = ⊥)
    (hdec : F = (F ⊓ Subgroup.centralizer (P : Set G)) ⊔ (F ⊓ P)) {a t : G}
    (hpow : ∀ k ∈ F ⊓ P, ∃ n : ℕ, a ^ n = k) (ht : t ∈ F ⊓ Q) (ht1 : t ≠ 1) :
    ∃ (c : G) (n : ℕ), c ∈ Subgroup.centralizer (P : Set G) ∧ c = t * (a ^ n)⁻¹ ∧ c ≠ 1 ∧
      a ^ n ∈ F ⊓ P := by
  have htmem : t ∈ (F ⊓ Subgroup.centralizer (P : Set G)) ⊔ (F ⊓ P) := by
    rw [← hdec]
    exact ht.1
  obtain ⟨c, hc, k, hk, hck⟩ := exists_mul_of_mem_sup
    (inf_le_left : F ⊓ Subgroup.centralizer (P : Set G) ≤ F) (inf_le_left : F ⊓ P ≤ F) hFab htmem
  obtain ⟨n, hn⟩ := hpow k hk
  refine ⟨c, n, hc.2, ?_, ?_, hn ▸ hk⟩
  · rw [hn, hck]
    group
  · intro hc1
    have htk : t = k := by rw [hck, hc1, one_mul]
    have : t ∈ (F ⊓ P) ⊓ (F ⊓ Q) := ⟨by rw [htk]; exact hk, ht⟩
    rw [hint, Subgroup.mem_bot] at this
    exact ht1 this

omit [Finite G] in
theorem map_centralizes {S : Type*} [Group S] {U P : Subgroup G} (ψ : ↥U ≃* S) {c : G}
    (hcU : c ∈ U) (hc : c ∈ Subgroup.centralizer (P : Set G)) :
    ∀ a ∈ (P.subgroupOf U).map ψ.toMonoidHom, a * ψ ⟨c, hcU⟩ = ψ ⟨c, hcU⟩ * a := by
  rintro _ ⟨y, hy, rfl⟩
  show ψ y * ψ ⟨c, hcU⟩ = ψ ⟨c, hcU⟩ * ψ y
  rw [← map_mul, ← map_mul]
  exact congrArg ψ (Subtype.ext
    (Subgroup.mem_centralizer_iff.1 hc (y : G) (Subgroup.mem_subgroupOf.1 hy)))

omit [Finite G] in
theorem gamma_field {S : Type*} [Group S] {U P Q F : Subgroup G} (ψ : ↥U ≃* S) (hPU : P ≤ U)
    (hQU : Q ≤ U) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hint : (F ⊓ P) ⊓ (F ⊓ Q) = ⊥)
    (hdec : F = (F ⊓ Subgroup.centralizer (P : Set G)) ⊔ (F ⊓ P)) {a t : G}
    (haP : a ∈ F ⊓ P) (htQ : t ∈ F ⊓ Q) (ht1 : t ≠ 1)
    (hpow : ∀ k ∈ F ⊓ P, ∃ n : ℕ, a ^ n = k) :
    ∃ γ ∈ Subgroup.closure {ψ ⟨a, hPU haP.2⟩, ψ ⟨t, hQU htQ.2⟩}, γ ≠ 1 ∧
      ∀ x ∈ (P.subgroupOf U).map ψ.toMonoidHom, x * γ = γ * x := by
  obtain ⟨c, n, hc, hceq, hc1, hk⟩ := gamma_decomp hFab hint hdec hpow htQ ht1
  have haU : a ∈ U := hPU haP.2
  have htU : t ∈ U := hQU htQ.2
  have hcU : c ∈ U := by
    rw [hceq]
    exact U.mul_mem htU (U.inv_mem (hPU hk.2))
  refine ⟨ψ ⟨c, hcU⟩, ?_, ?_, map_centralizes ψ hcU hc⟩
  · have h1 : (⟨c, hcU⟩ : ↥U) = ⟨t, htU⟩ * (⟨a ^ n, U.pow_mem haU n⟩ : ↥U)⁻¹ := Subtype.ext hceq
    rw [h1, map_mul, map_inv, show ψ ⟨a ^ n, U.pow_mem haU n⟩ = ψ ⟨a, haU⟩ ^ n from
      (map_pow ψ (⟨a, haU⟩ : ↥U) n)]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) n))
  · intro h
    exact hc1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))

theorem config_of_data {f r : ℕ} (hr : r.Prime) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {U Ks Kl F : Subgroup G}
    (ψ : ↥U ≃* ↥(SU (unitaryInvolution K 2 f) 4)) (hKsU : Ks ≤ U) (hKlU : Kl ≤ U)
    (hperfS : Group.IsPerfect ↥Ks)
    (hcardS : Nat.card ↥Ks = 2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1))
    (hperfL : Group.IsPerfect ↥Kl) (hcardL : Nat.card ↥Kl = 2 ^ f * ((2 ^ f) ^ 2 - 1))
    (hF : IsElementaryAbelian r F) (hcs : Nat.card ↥(F ⊓ Ks) = r) (hcl : Nat.card ↥(F ⊓ Kl) = r)
    (hint : (F ⊓ Ks) ⊓ (F ⊓ Kl) = ⊥)
    (hTs : F = (F ⊓ Subgroup.centralizer (Ks : Set G)) ⊔ (F ⊓ Ks))
    (hTl : F = (F ⊓ Subgroup.centralizer (Kl : Set G)) ⊔ (F ⊓ Kl))
    (hstd : ¬ F ⊓ Kl ≤ Subgroup.centralizer (Ks : Set G)) :
    ∃ ρ τ : ↥(SU (unitaryInvolution K 2 f) 4),
      Config (unitaryInvolution K 2 f) r ((Ks.subgroupOf U).map ψ.toMonoidHom)
        ((Kl.subgroupOf U).map ψ.toMonoidHom) ρ τ := by
  classical
  have : IsMulCommutative ↥F := hF.toIsMulCommutative
  have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hFpow : ∀ a ∈ F, a ^ r = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  obtain ⟨ρG, hρG, hρ1, hρpow⟩ := exists_gen_of_prime_card hr hcs
  obtain ⟨τG, hτG, hτ1, hτpow⟩ := exists_gen_of_prime_card hr hcl
  have hρU : ρG ∈ U := hKsU hρG.2
  have hτU : τG ∈ U := hKlU hτG.2
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ↥(SU (unitaryInvolution K 2 f) 4), ρ = ψ ⟨ρG, hρU⟩ := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : ↥(SU (unitaryInvolution K 2 f) 4), τ = ψ ⟨τG, hτU⟩ := ⟨_, rfl⟩
  have hρpowU : ∀ n : ℕ, ρ ^ n = ψ ⟨ρG ^ n, U.pow_mem hρU n⟩ := fun n => by
    rw [hρdef, ← map_pow]
    rfl
  have hτpowU : ∀ n : ℕ, τ ^ n = ψ ⟨τG ^ n, U.pow_mem hτU n⟩ := fun n => by
    rw [hτdef, ← map_pow]
    rfl
  have hFq : Nat.card (fixF (unitaryInvolution K 2 f)) = 2 ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  obtain ⟨γ₁, hγ₁, hγ₁1, hγ₁c⟩ := gamma_field ψ hKsU hKlU hFab hint hTs hρG hτG hτ1 hρpow
  obtain ⟨γ₂, hγ₂, hγ₂1, hγ₂c⟩ :=
    gamma_field ψ hKlU hKsU hFab (by rw [inf_comm]; exact hint) hTl hτG hρG hρ1 hτpow
  refine ⟨ρ, τ, ?_⟩
  refine
    { perfA := ?_, perfB := ?_, cardA := ?_, cardB := ?_, rho_mem := ?_, tau_mem := ?_,
      rho_pow := ?_, tau_pow := ?_, rho_ne := ?_, tau_ne := ?_, comm := ?_, inter := ?_,
      gamma₁ := ?_, gamma₂ := ?_, std := ?_ }
  · have : Group.IsPerfect ↥(Ks.subgroupOf U) := by
      have := hperfS
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hKsU).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKsU).symm.surjective
    exact Group.IsPerfect.map ψ.toMonoidHom
  · have : Group.IsPerfect ↥(Kl.subgroupOf U) := by
      have := hperfL
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hKlU).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKlU).symm.surjective
    exact Group.IsPerfect.map ψ.toMonoidHom
  · rw [Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKsU).toEquiv, hcardS,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK, pow_mul' 2 2 f]
  · rw [Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKlU).toEquiv, hcardL,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFq]
  · exact ⟨⟨ρG, hρU⟩, Subgroup.mem_subgroupOf.2 hρG.2, hρdef.symm⟩
  · exact ⟨⟨τG, hτU⟩, Subgroup.mem_subgroupOf.2 hτG.2, hτdef.symm⟩
  · rw [hρpowU r, show (⟨ρG ^ r, U.pow_mem hρU r⟩ : ↥U) = 1 from
      Subtype.ext (hFpow ρG hρG.1), map_one]
  · rw [hτpowU r, show (⟨τG ^ r, U.pow_mem hτU r⟩ : ↥U) = 1 from
      Subtype.ext (hFpow τG hτG.1), map_one]
  · intro h
    rw [hρdef] at h
    exact hρ1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))
  · intro h
    rw [hτdef] at h
    exact hτ1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))
  · rw [hρdef, hτdef, ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hFab ρG hρG.1 τG hτG.1))
  · intro i j h
    rw [hρpowU i, hτpowU j] at h
    have h'' : ρG ^ i = τG ^ j := congrArg Subtype.val (ψ.injective h)
    have hmem : ρG ^ i ∈ (F ⊓ Ks) ⊓ (F ⊓ Kl) :=
      ⟨(F ⊓ Ks).pow_mem hρG i, h'' ▸ (F ⊓ Kl).pow_mem hτG j⟩
    rw [hint, Subgroup.mem_bot] at hmem
    rw [hρpowU i, show (⟨ρG ^ i, U.pow_mem hρU i⟩ : ↥U) = 1 from Subtype.ext hmem, map_one]
  · rw [hρdef, hτdef]
    exact ⟨γ₁, hγ₁, hγ₁1, hγ₁c⟩
  · rw [hρdef, hτdef, Set.pair_comm]
    exact ⟨γ₂, hγ₂, hγ₂1, hγ₂c⟩
  ·
    have hτnc : τG ∉ Subgroup.centralizer (Ks : Set G) := by
      intro hτc
      apply hstd
      intro x hx
      obtain ⟨m, hm⟩ := hτpow x hx
      rw [← hm]
      exact Subgroup.pow_mem _ hτc m
    rw [Subgroup.mem_centralizer_iff] at hτnc
    push Not at hτnc
    obtain ⟨y, hy, hyne⟩ := hτnc
    refine ⟨ψ ⟨y, hKsU hy⟩, ⟨⟨y, hKsU hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩, fun h => hyne ?_⟩
    rw [hτdef] at h
    have h' : (⟨τG, hτU⟩ : ↥U) * ⟨y, hKsU hy⟩ = ⟨y, hKsU hy⟩ * ⟨τG, hτU⟩ :=
      ψ.injective (by rw [map_mul, map_mul]; exact h)
    exact (congrArg Subtype.val h').symm

end CFSG.RankThree.PartOne.U4F

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.U4F CFSG.Assembly.LowTwoRank

theorem U4F.kf1330Gen_holds :
    ∀ (G : Type) [Group G] [Finite G] (f r : ℕ) (U Ks Kl F : Subgroup G),
      2 ≤ f → r.Prime → r ∣ 2 ^ f - 1 →
      StatedClassicalModel U .PSU 4 2 f → Ks ≤ U → Kl ≤ U →
      StatedClassicalModel Ks .PSL 2 2 (2 * f) → StatedClassicalModel Kl .PSL 2 2 f →
      IsElementaryAbelian r F →
      Nat.card ↥(F ⊓ Ks) = r → Nat.card ↥(F ⊓ Kl) = r → (F ⊓ Ks) ⊓ (F ⊓ Kl) = ⊥ →
      F = (F ⊓ Subgroup.centralizer (Ks : Set G)) ⊔ (F ⊓ Ks) →
      F = (F ⊓ Subgroup.centralizer (Kl : Set G)) ⊔ (F ⊓ Kl) →
      ¬ (F ⊓ Kl ≤ Subgroup.centralizer (Ks : Set G)) →
      Ks ⊔ Kl = U := by
  intro G _ _ f r U Ks Kl F hf hr hrq hU hKsU hKlU hKs hKl hF hcs hcl hint hTs hTl hstd
  obtain ⟨K, _, _, _, hK, ⟨ψ⟩⟩ := exists_su_equiv (by omega : 1 ≤ f) hU
  obtain ⟨L₁, _, _, hL₁, ha₁, ⟨e₁⟩⟩ := exists_equiv_SL2_of_model hKs
  obtain ⟨L₂, _, _, hL₂, ha₂, ⟨e₂⟩⟩ := exists_equiv_SL2_of_model hKl
  obtain ⟨hperfS, hcardS⟩ := perfect_card_of_equiv_SL2 hL₁ ha₁ e₁
  obtain ⟨hperfL, hcardL⟩ := perfect_card_of_equiv_SL2 hL₂ ha₂ e₂
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  obtain ⟨ρ, τ, hc⟩ := config_of_data hr hK ψ hKsU hKlU hperfS hcardS hperfL hcardL hF hcs hcl
    hint hTs hTl hstd
  have htop := hc.sup_eq_top hf hK hr hr2 hrq
  have h1 : (Ks.subgroupOf U ⊔ Kl.subgroupOf U).map ψ.toMonoidHom =
      (⊤ : Subgroup ↥U).map ψ.toMonoidHom := by
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ ψ.surjective]
    exact htop
  have htop' : Ks.subgroupOf U ⊔ Kl.subgroupOf U = ⊤ := Subgroup.map_injective ψ.injective h1
  apply le_antisymm (sup_le hKsU hKlU)
  intro u hu
  have hmem : (⟨u, hu⟩ : ↥U) ∈ Ks.subgroupOf U ⊔ Kl.subgroupOf U := by
    rw [htop']
    trivial
  have h3 := Subgroup.mem_map_of_mem U.subtype hmem
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKsU,
    Subgroup.map_subgroupOf_eq_of_le hKlU] at h3

end CFSG.RankThree.PartOne
