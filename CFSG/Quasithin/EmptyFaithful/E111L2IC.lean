module

public import CFSG.Quasithin.EmptyFaithful.E111L2B
public import CFSG.Quasithin.EmptyFaithful.E111RMemB

public section

namespace CFSG.Quasithin.E2.E22N.E111L.KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R
open scoped commutatorElement

variable {G : Type} [Group G]

theorem perm3_mem_alternating_iff (σ : Equiv.Perm (Fin 3)) :
    σ ∈ alternatingGroup (Fin 3) ↔ σ ^ 3 = 1 := by
  rw [Equiv.Perm.mem_alternatingGroup]
  revert σ
  decide

theorem perm3_commutator_cycle (τ : Equiv.Perm (Fin 3)) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) :
    ⁅finRotate 3, τ⁆ ^ 3 = 1 ∧ ⁅finRotate 3, τ⁆ ≠ 1 := by
  revert τ
  decide +kernel

section Phi

variable {p : ℕ} [Fact p.Prime]

theorem exists_phi [Finite G]
    (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7) {D V : Subgroup G} (hD : IsPSL 2 p 1 ↥D)
    (hVD : V ≤ D) (hV : IsKleinFour ↥V) :
    ∃ Φ : ↥(Subgroup.normalizer (V : Set G) ⊓ D) →* Equiv.Perm (Fin 3),
      Function.Surjective Φ ∧ Φ.ker = V.subgroupOf (Subgroup.normalizer (V : Set G) ⊓ D) := by
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hD
  have hV' : IsKleinFour ↥(V.subgroupOf D) :=
    isKleinFour_of_equiv (Subgroup.subgroupOfEquivOfLe hVD) hV
  obtain ⟨Φ₀, hΦs, hΦk⟩ := CFSG.Quasithin.E22L2.e22ps4_exists_phi hV'
    (centralizer_kleinFour_of_equiv e (by omega) hV') (normalizer_surjective_of_equiv e hp7 hp8 hV')
  set ψ : ↥(Subgroup.normalizer (V : Set G) ⊓ D) ≃*
      ↥(Subgroup.normalizer ((V.subgroupOf D : Subgroup ↥D) : Set ↥D)) :=
    (Subgroup.subgroupOfEquivOfLe inf_le_right).symm.trans
      (MulEquiv.subgroupCongr (sub_normalizer_eq hVD).symm) with hψ
  refine ⟨Φ₀.comp ψ.toMonoidHom, hΦs.comp ψ.surjective, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hΦk]
  exact Iff.rfl

end Phi

theorem exists_evenPart [Finite G] {L V W T : Subgroup G} (hVL : V ≤ L) (hV : IsKleinFour ↥V)
    (hW : IsKleinFour ↥W) (hWL : W ≤ L) (hne : V ≠ W) (Φ : ↥L →* Equiv.Perm (Fin 3))
    (hΦs : Function.Surjective Φ) (hΦk : Φ.ker = V.subgroupOf L) (hL24 : Nat.card L = 24)
    (hT8 : Nat.card ↥(T ⊓ L) = 8) :
    ∃ P : Subgroup G, P ≤ L ∧ (∀ x, x ∈ P ↔ x ∈ L ∧ x ^ 3 ∈ V) ∧ V ≤ P ∧
      P ≤ V ⊔ ⁅P, W⁆ ∧ L ≤ P ⊔ (T ⊓ L) ∧
      ∃ y ∈ P, ∀ w ∈ L, w ∉ V → w * w = 1 → ∀ n : ℕ, ⁅y, w⁆ ^ 2 ^ n ≠ 1 := by
  set P' : Subgroup ↥L := (alternatingGroup (Fin 3)).comap Φ with hP'
  set P : Subgroup G := P'.map L.subtype with hP
  have hker : ∀ y : ↥L, Φ y = 1 ↔ (y : G) ∈ V := fun y => by
    rw [← MonoidHom.mem_ker, hΦk, Subgroup.mem_subgroupOf]
  have hmem : ∀ x, x ∈ P ↔ x ∈ L ∧ x ^ 3 ∈ V := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have h1 : Φ (y ^ 3) = 1 := by
        rw [map_pow]
        exact (perm3_mem_alternating_iff _).mp hy
      simpa using (hker _).mp h1
    · rintro ⟨hxL, hx3⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      show Φ ⟨x, hxL⟩ ∈ alternatingGroup (Fin 3)
      rw [perm3_mem_alternating_iff, ← map_pow]
      exact (hker _).mpr (by simpa using hx3)
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  refine ⟨P, hPL, hmem, fun v hv => (hmem v).mpr ⟨hVL hv, V.pow_mem hv 3⟩, ?_, ?_, ?_⟩
  ·
    obtain ⟨w, hw, hwA⟩ := CFSG.Quasithin.E22L2.e22ps4_exists_odd hW hV hne hWL Φ hΦk
    have h1 := CFSG.Quasithin.E22L2.e22ps4_comm_gen Φ (W.subgroupOf L) ⟨w, hw, hwA⟩
    have h1' := Subgroup.map_mono (f := L.subtype) h1
    rw [Subgroup.map_sup, Subgroup.map_commutator, hΦk, Subgroup.map_subgroupOf_eq_of_le hVL,
      Subgroup.map_subgroupOf_eq_of_le hWL] at h1'
    exact h1'
  ·
    have hidx : P'.index = 2 := by
      rw [hP', Subgroup.index_comap_of_surjective _ hΦs]
      exact alternatingGroup.index_eq_two
    have hP12 : Nat.card P = 12 := by
      have h := Subgroup.card_mul_index P'
      rw [hidx, hL24] at h
      rw [hP, Subgroup.card_map_of_injective L.subtype_injective]
      omega
    have hle : P ⊔ (T ⊓ L) ≤ L := sup_le hPL inf_le_right
    have hd1 : Nat.card P ∣ Nat.card ↥(P ⊔ (T ⊓ L)) := Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card ↥(P ⊔ (T ⊓ L)) ∣ Nat.card L := Subgroup.card_dvd_of_le hle
    have hd3 : Nat.card ↥(T ⊓ L) ∣ Nat.card ↥(P ⊔ (T ⊓ L)) := Subgroup.card_dvd_of_le le_sup_right
    rw [hP12] at hd1
    rw [hL24] at hd2
    rw [hT8] at hd3
    have h24 : Nat.card ↥(P ⊔ (T ⊓ L)) = 24 := by
      have hpos : 0 < Nat.card ↥(P ⊔ (T ⊓ L)) := Nat.card_pos
      have hle24 := Nat.le_of_dvd (by norm_num) hd2
      obtain ⟨a, ha⟩ := hd1
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h24, hL24])).symm.le
  ·
    obtain ⟨y, hy⟩ := hΦs (finRotate 3)
    refine ⟨y, ⟨y, ?_, rfl⟩, fun w hwL hwV hww n hn => ?_⟩
    · show Φ y ∈ alternatingGroup (Fin 3)
      rw [hy, perm3_mem_alternating_iff]
      decide
    set w' : ↥L := ⟨w, hwL⟩ with hw'
    have hτ1 : Φ w' ≠ 1 := fun h1 => hwV ((hker _).mp h1)
    have hτ2 : Φ w' * Φ w' = 1 := by
      rw [← map_mul, ← map_one Φ]
      congr 1
      exact Subtype.ext hww
    obtain ⟨h3, h1⟩ := perm3_commutator_cycle _ hτ2 hτ1
    have hc : Φ ⁅y, w'⁆ = ⁅finRotate 3, Φ w'⁆ := by
      rw [map_commutatorElement, hy]
    have h2 : ⁅finRotate 3, Φ w'⁆ ^ 2 ^ n = 1 := by
      rw [← hc, ← map_pow]
      have : ⁅y, w'⁆ ^ 2 ^ n = 1 := by
        apply Subtype.ext
        have hcomm : ((⁅y, w'⁆ : ↥L) : G) = ⁅(y : G), w⁆ := by
          simp [commutatorElement_def, hw']
        rw [Subgroup.coe_pow, hcomm]
        exact hn
      rw [this, map_one]
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right n (by norm_num)), Nat.dvd_one,
      orderOf_eq_one_iff] at hd
    exact h1 hd

section Diag

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C]
include h

theorem isPSL_diag {p : ℕ} (hSp : IsPSL 2 p 1 ↥S) : IsPSL 2 p 1 ↥(diagSub S C h.diagComm) :=
  CFSG.SectionRank.statedClassicalModel_of_mulEquiv h.diagEquiv.symm hSp

theorem inf_diag_eq [Finite G] : T ⊓ diagSub S C h.diagComm =
    ((T ⊓ S).subgroupOf S).map (diagHom S C h.diagComm) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := diagHom_injective h.diagComm h.center_trivial
  have hle : ((T ⊓ S).subgroupOf S).map (diagHom S C h.diagComm) ≤
      T ⊓ diagSub S C h.diagComm := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨diagHom_mem_of h.diagComm x fun c hc => ?_, ⟨x, rfl⟩⟩
    have hxT : (x : G) ∈ T := (Subgroup.mem_subgroupOf.mp hx).1
    exact T.mul_mem (T.mul_mem (h.AT (h.CA hc)) hxT) (T.inv_mem (h.AT (h.CA hc)))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective hinj, h.isSylowIn_diag.card_eq,
    ← Nat.card_congr h.diagEquiv.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ S ≤ S)).toEquiv,
    (isSylowIn_inf h.red h.comp).card_eq]

theorem diagHom_central [Finite G] {z : G} (hzS : z ∈ S) (hzc : ∀ x ∈ T ⊓ S, z * x = x * z) :
    ∀ x ∈ T ⊓ diagSub S C h.diagComm,
      diagHom S C h.diagComm ⟨z, hzS⟩ * x = x * diagHom S C h.diagComm ⟨z, hzS⟩ := by
  rw [inf_diag_eq h]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hzc _ (Subgroup.mem_subgroupOf.mp hy))

end Diag

end CFSG.Quasithin.E2.E22N.E111L.KMI
