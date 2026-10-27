module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

theorem sylow_eq_bot_of_le_center {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ⁅(⊤ : Subgroup G), ⊤⁆ = (⊤ : Subgroup G)) (P : Sylow p G)
    (hP : (P : Subgroup G) ≤ Subgroup.center G) :
    (P : Subgroup G) = ⊥ := by
  have hN : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Subgroup.centralizer (P : Set G) :=
    fun g _ x hx =>
      (Subgroup.mem_center_iff.mp (hP hx) g).symm
  have hker : (MonoidHom.transferSylow P hN).ker = ⊤ := by
    rw [eq_top_iff, ← hG, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply Subtype.ext
    have h := Subgroup.mem_center_iff.mp (hP (MonoidHom.transferSylow P hN a).2)
      ((MonoidHom.transferSylow P hN b : P) : G)
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inv, OneMemClass.coe_one, ← h]
    group
  have h := MonoidHom.ker_transferSylow_disjoint P hN (P : Subgroup G) P.isPGroup'
  rwa [hker, top_disjoint] at h

theorem perfect_modO2 {X : Type} [Group X] {B : Subgroup X} (hB : ⁅B, B⁆ = B) :
    ⁅(⊤ : Subgroup (ModO2 B)), ⊤⁆ = (⊤ : Subgroup (ModO2 B)) := by
  have h1 : ⁅(⊤ : Subgroup ↥B), ⊤⁆ = (⊤ : Subgroup ↥B) :=
    Subgroup.map_injective B.subtype_injective (by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hB])
  have hs := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥B)
  have h2 : (⊤ : Subgroup (ModO2 B)) = (⊤ : Subgroup ↥B).map (QuotientGroup.mk' _) :=
    (Subgroup.map_top_of_surjective _ hs).symm
  calc ⁅(⊤ : Subgroup (ModO2 B)), ⊤⁆ =
        (⁅(⊤ : Subgroup ↥B), ⊤⁆ : Subgroup ↥B).map (QuotientGroup.mk' _) := by
        rw [Subgroup.map_commutator, ← h2]
    _ = ⊤ := by rw [h1, ← h2]

theorem factorization_card_modO2 {X : Type} [Group X] [Finite X] (B : Subgroup X) {r : ℕ}
    (hr2 : r ≠ 2) :
    (Nat.card (ModO2 B)).factorization r = (Nat.card B).factorization r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
  have h := (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
  have hQ : Nat.card (ModO2 B) ≠ 0 := Nat.card_pos.ne'
  rw [h, hn, Nat.factorization_mul hQ (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Ne.symm hr2]

theorem card_sup_mul_card_inf {X : Type} [Group X] {B₁ B₂ : Subgroup X}
    (h : B₂ ≤ Subgroup.normalizer (B₁ : Set X)) :
    Nat.card ↥(B₂ ⊔ B₁) * Nat.card ↥(B₁ ⊓ B₂) = Nat.card B₁ * Nat.card B₂ := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B₂ B₁ h
  have h1 : B₁.relIndex B₂ = B₁.relIndex (B₂ ⊔ B₁) := Nat.card_congr e.toEquiv
  have h2 := Subgroup.relIndex_mul_card B₁ B₂
  have h3 := Subgroup.relIndex_mul_card B₁ (B₂ ⊔ B₁)
  rw [inf_of_le_left le_sup_right] at h3
  rw [← h2, ← h3, h1]
  ring

theorem false_of_sylowPart {X : Type} [Group X] [Finite X] {B₁ B₂ : Subgroup X} {r k : ℕ}
    [hr : Fact r.Prime] (hr2 : r ≠ 2) (hk : 1 ≤ k) (hB₁ : ⁅B₁, B₁⁆ = B₁)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁) (e : ModO2 B₁ ≃* ModO2 B₂)
    (hrB : r ^ k ∣ Nat.card B₁) (hX : ¬ r ^ (k + 1) ∣ Nat.card X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := (Nat.card B₁).factorization r with ha
  have hka : k ≤ a := (hr.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hrB
  have hB₂a : (Nat.card B₂).factorization r = a := by
    rw [← factorization_card_modO2 B₂ hr2, ← Nat.card_congr e.toEquiv,
      factorization_card_modO2 B₁ hr2]
  have hcB : ∀ y ∈ B₂, ∀ b ∈ B₁, y * b * y⁻¹ ∈ B₁ := fun y hy b hb => by
    have h1 : y * b * y⁻¹ * b⁻¹ ∈ B₁ := Subgroup.map_subtype_le _
      (hc (Subgroup.commutator_comm B₂ B₁ ▸ Subgroup.commutator_mem_commutator hy hb))
    simpa using B₁.mul_mem h1 hb
  have hN : B₂ ≤ Subgroup.normalizer (B₁ : Set X) := fun y hy =>
    Subgroup.mem_normalizer_iff.mpr fun b => ⟨fun hb => hcB y hy b hb, fun hb => by
      simpa [mul_assoc] using hcB y⁻¹ (B₂.inv_mem hy) _ hb⟩
  have hW : (Nat.card ↥(B₁ ⊓ B₂)).factorization r < a := by
    by_contra hge
    have hWa : (Nat.card ↥(B₁ ⊓ B₂)).factorization r = a := le_antisymm
      ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le inf_le_left) r) (not_lt.mp hge)
    set W' := (B₁ ⊓ B₂).subgroupOf B₁
    have hW' : Nat.card W' = Nat.card ↥(B₁ ⊓ B₂) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r W'))
    set φ : W' →* ModO2 B₁ := (QuotientGroup.mk' (CFSG.pCore 2 ↥B₁)).comp W'.subtype
    have hker : Disjoint (Q : Subgroup W') φ.ker := by
      refine IsPGroup.disjoint_of_ne r 2 hr2 _ _ Q.isPGroup' ?_
      have h2 := (CFSG.pCore_isPGroup (p := 2) (G := ↥B₁)).comap_of_injective W'.subtype
        W'.subtype_injective
      rwa [show φ.ker = (CFSG.pCore 2 ↥B₁).comap W'.subtype by
        ext w
        rw [MonoidHom.mem_ker]
        simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        rfl]
    have hinj : Function.Injective (φ.comp (Q : Subgroup W').subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro q hq
      have h1 : (q : W') ∈ (Q : Subgroup W') ⊓ φ.ker := ⟨q.2, hq⟩
      rw [hker.eq_bot, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    set Qb := (φ.comp (Q : Subgroup W').subtype).range
    have hQb : Nat.card Qb = r ^ a := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Sylow.card_eq_multiplicity, hW',
        hWa]
    have hcen : Qb ≤ Subgroup.center (ModO2 B₁) := by
      rintro _ ⟨q, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
      have hw : ((q : W') : ↥B₁) ∈ B₂.subgroupOf B₁ := ((q : W').2 : _).2
      have h1 : ⁅(x : X), (((q : W') : ↥B₁) : X)⁆ ∈ pCoreOf 2 B₁ :=
        hc (Subgroup.commutator_mem_commutator x.2 hw)
      rw [pCoreOf] at h1
      obtain ⟨c, hc1, hc2⟩ := h1
      have hcoe : ((⁅x, ((q : W') : ↥B₁)⁆ : ↥B₁) : X) = ⁅(x : X), (((q : W') : ↥B₁) : X)⁆ := by
        simp [commutatorElement_def]
      have h3 : ⁅x, ((q : W') : ↥B₁)⁆ ∈ CFSG.pCore 2 ↥B₁ := by
        rwa [show ⁅x, ((q : W') : ↥B₁)⁆ = c from Subtype.ext (hcoe.trans hc2.symm)]
      change QuotientGroup.mk' _ x * QuotientGroup.mk' _ ((q : W') : ↥B₁) =
        QuotientGroup.mk' _ ((q : W') : ↥B₁) * QuotientGroup.mk' _ x
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h3
    have hQbp : IsPGroup r Qb := IsPGroup.of_card hQb
    have hidx : ¬ r ∣ Qb.index := by
      intro hd
      have h2 : (Nat.card Qb * Qb.index).factorization r =
          (Nat.card (ModO2 B₁)).factorization r := by rw [Qb.card_mul_index]
      rw [Nat.factorization_mul Nat.card_pos.ne' (Subgroup.index_ne_zero_of_finite),
        Finsupp.add_apply, hQb, Nat.Prime.factorization_pow hr.out, Finsupp.single_eq_same,
        factorization_card_modO2 B₁ hr2] at h2
      have h3 := (hr.out.dvd_iff_one_le_factorization Subgroup.index_ne_zero_of_finite).mp hd
      omega
    have hbot := sylow_eq_bot_of_le_center (perfect_modO2 hB₁) (hQbp.toSylow hidx) hcen
    rw [IsPGroup.toSylow_coe] at hbot
    rw [hbot, Subgroup.card_bot] at hQb
    have := Nat.one_lt_pow (by omega : a ≠ 0) hr.out.one_lt
    omega
  have hprod : (Nat.card ↥(B₂ ⊔ B₁) * Nat.card ↥(B₁ ⊓ B₂)).factorization r =
      (Nat.card B₁ * Nat.card B₂).factorization r := by rw [card_sup_mul_card_inf hN]
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Finsupp.add_apply, hB₂a] at hprod
  have hJ : r ^ (k + 1) ∣ Nat.card ↥(B₂ ⊔ B₁) :=
    (hr.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr (by omega)
  exact hX (hJ.trans (Subgroup.card_subgroup_dvd_card _))

end CFSG.Quasithin.Vol2.Ch10.A312C
