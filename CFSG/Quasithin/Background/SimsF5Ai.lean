module

import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.Permutation.SymmetricCoxeter
public import CFSG.Quasithin.Background.SimsF5Lin
public import CFSG.Quasithin.Background.SimsF5Mono
public import CFSG.Quasithin.Background.SimsF5Quat
public import CFSG.Quasithin.Background.SimsF5Stab

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open
open scoped Pointwise commutatorElement

theorem ai_eJ_comm_iff : ∀ J : Finset (Fin 6),
    eJ J * fDot = fDot * eJ J ↔ ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J) := by
  decide +kernel

theorem Q2Dot_inf_centralizer_coe :
    ((Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) : Set GL6) =
      {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J) ∧
        g = eJ J} := by
  ext g
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
    Subgroup.mem_centralizer_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hq, hc⟩
    have hq' : g ∈ (Q2Dot : Set GL6) := hq
    rw [Q2Dot_coe] at hq'
    obtain ⟨J, hJ, hev, rfl⟩ := hq'
    exact ⟨J, hJ, hev, (ai_eJ_comm_iff J).1 hc, rfl⟩
  · rintro ⟨J, hJ, hev, h01, rfl⟩
    exact ⟨mono_eJ_mem_Q2Dot hJ hev, (ai_eJ_comm_iff J).2 h01⟩

theorem ai_comm_eJ_f : ∀ J : Finset (Fin 6), ⁅eJ J, fDot⁆ = 1 ∨ ⁅eJ J, fDot⁆ = tDot := by
  decide +kernel

theorem ai_tDot_eq_comm : tDot = ⁅eJ {0, 2}, fDot⁆ := by
  decide +kernel

theorem commutator_Q2Dot_fDot : ⁅Q2Dot, Subgroup.zpowers fDot⁆ = Subgroup.zpowers tDot := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro q hq g hg
    obtain ⟨J, rfl⟩ := mono_Q2Dot_elim hq
    rcases mono_mem_zpowers_involution mono_fDot_mul_self hg with rfl | rfl
    · rw [commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rcases ai_comm_eJ_f J with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le, ai_tDot_eq_comm]
    exact Subgroup.commutator_mem_commutator (mono_eJ_mem_Q2Dot (by decide) (by decide))
      (Subgroup.mem_zpowers _)

@[expose] def aiC5 : Subgroup (Equiv.Perm (Fin 5)) :=
  Subgroup.centralizer ({Equiv.swap (0 : Fin 5) 1} : Set (Equiv.Perm (Fin 5)))

theorem ai_card_C5 : Nat.card ↥aiC5 = 12 := by
  have : Nat.card ↥aiC5 =
      Nat.card {σ : Equiv.Perm (Fin 5) // σ * Equiv.swap 0 1 = Equiv.swap 0 1 * σ} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun σ => Subgroup.mem_centralizer_singleton_iff)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem ai_card_CQ2 :
    Nat.card ↥(Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = 8 := by
  have hf : ∀ J : {J : Finset (Fin 6) //
      J ⊆ Iset ∧ Even J.card ∧ ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J)},
      eJ J.1 ∈ Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := fun J =>
    ⟨mono_eJ_mem_Q2Dot J.2.1 J.2.2.1,
      Subgroup.mem_centralizer_singleton_iff.2 ((ai_eJ_comm_iff J.1).2 J.2.2.2)⟩
  let f : {J : Finset (Fin 6) // J ⊆ Iset ∧ Even J.card ∧
      ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J)} →
      ↥(Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) := fun J => ⟨eJ J.1, hf J⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro J K h
      exact Subtype.ext (mono_eJ_injective (congrArg Subtype.val h))
    · rintro ⟨g, hg⟩
      have hg' : g ∈ ((Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) :
          Set GL6) := hg
      rw [Q2Dot_inf_centralizer_coe] at hg'
      obtain ⟨J, hJ, hev, h01, rfl⟩ := hg'
      exact ⟨⟨J, hJ, hev, h01⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem ai_E2_decomp {g : GL6} (hg : g ∈ M2Dot) (hc : g * fDot = fDot * g) :
    ∃ σ ∈ aiC5, ∃ q ∈ Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6), g = s5Hom σ * q := by
  obtain ⟨σ, q, hq, rfl⟩ := mono_M2Dot_decomp hg
  have hfM : fDot ∈ M2Dot := fDot_mem_M12Dot.2
  have h1 : q * fDot * q⁻¹ = (s5Hom σ)⁻¹ * fDot * s5Hom σ := by
    calc q * fDot * q⁻¹ = (s5Hom σ)⁻¹ * (s5Hom σ * q * fDot) * q⁻¹ := by group
      _ = (s5Hom σ)⁻¹ * (fDot * (s5Hom σ * q)) * q⁻¹ := by rw [hc]
      _ = (s5Hom σ)⁻¹ * fDot * s5Hom σ := by group
  have h2 : q * fDot * q⁻¹ * fDot⁻¹ ∈ Q2Dot := by
    have h3 := Q2Dot.mul_mem hq (mono_conj_mem_Q2Dot hfM (Q2Dot.inv_mem hq))
    simpa [mul_assoc] using h3
  have h4 : q * fDot * q⁻¹ * fDot⁻¹ ∈ s5Hom.range := by
    rw [h1, fDot_eq_s5Hom]
    exact ⟨σ⁻¹ * Equiv.swap 0 1 * σ * (Equiv.swap 0 1)⁻¹, by simp only [map_mul, map_inv]⟩
  have h5 : q * fDot * q⁻¹ * fDot⁻¹ = 1 := by
    have : q * fDot * q⁻¹ * fDot⁻¹ ∈ s5Hom.range ⊓ Q2Dot := ⟨h4, h2⟩
    rw [s5Hom_range_inf] at this
    exact this
  have hqc : q * fDot = fDot * q := by
    calc q * fDot = (q * fDot * q⁻¹ * fDot⁻¹) * (fDot * q) := by group
      _ = fDot * q := by rw [h5, one_mul]
  have h6 : (s5Hom σ)⁻¹ * fDot * s5Hom σ = fDot := by
    rw [← h1]
    calc q * fDot * q⁻¹ = fDot * q * q⁻¹ := by rw [hqc]
      _ = fDot := by group
  refine ⟨σ, ?_, q, ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 hqc⟩, rfl⟩
  rw [fDot_eq_s5Hom] at h6
  have h7 : s5Hom (σ⁻¹ * Equiv.swap 0 1 * σ) = s5Hom (Equiv.swap 0 1) := by
    simpa [map_mul, map_inv] using h6
  have h8 := s5Hom_injective h7
  rw [aiC5, Subgroup.mem_centralizer_singleton_iff]
  calc σ * Equiv.swap 0 1 = σ * (σ⁻¹ * Equiv.swap 0 1 * σ) := by rw [h8]
    _ = Equiv.swap 0 1 * σ := by group

theorem ai_E2_eq : EDot M2Dot =
    (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ⊔ aiC5.map s5Hom := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgM, hgc⟩ := hg
    have hgc' : g * fDot = fDot * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
    obtain ⟨σ, hσ, q, hq, rfl⟩ := ai_E2_decomp hgM hgc'
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨σ, hσ, rfl⟩) (Subgroup.mem_sup_left hq)
  · apply sup_le
    · intro q hq
      exact ⟨Q2Dot_le_M2Dot hq.1, hq.2⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.1 hσ
      refine ⟨s5Hom_range_le ⟨σ, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [fDot_eq_s5Hom, ← map_mul, ← map_mul, h]

theorem ai_conj_CQ2 {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ aiC5) {s : GL6}
    (hs : s ∈ Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) :
    s5Hom σ * s * (s5Hom σ)⁻¹ ∈ Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  refine ⟨mono_conj_mem_Q2Dot (s5Hom_range_le ⟨σ, rfl⟩) hs.1,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hP : Commute (s5Hom σ) fDot := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 hσ
    show s5Hom σ * fDot = fDot * s5Hom σ
    rw [fDot_eq_s5Hom, ← map_mul, ← map_mul, h]
  have hsf : Commute s fDot := Subgroup.mem_centralizer_singleton_iff.1 hs.2
  exact ((hP.mul_left hsf).mul_left hP.inv_left)

theorem ai_card_E2 : Nat.card ↥(EDot M2Dot) = 96 := by
  have hinf : (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ⊓ aiC5.map s5Hom = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxQ, _⟩, ⟨σ, _, rfl⟩⟩
    have : s5Hom σ ∈ s5Hom.range ⊓ Q2Dot := ⟨⟨σ, rfl⟩, hxQ⟩
    rw [s5Hom_range_inf] at this
    exact this
  have hnorm : aiC5.map s5Hom ≤
      Subgroup.normalizer ((Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) :
        Set GL6) := by
    rintro _ ⟨σ, hσ, rfl⟩
    refine mono_mem_normalizer_of_conj (fun s hs => ai_conj_CQ2 hσ hs) (fun s hs => ?_)
    have := ai_conj_CQ2 (inv_mem hσ) hs
    rwa [map_inv, inv_inv] at this
  rw [ai_E2_eq, mono_card_sup_of_le_normalizer _ _ hinf hnorm, ai_card_CQ2,
    Subgroup.card_map_of_injective s5Hom_injective, ai_card_C5]

theorem ai_tDot_central {g : GL6} (hg : g ∈ M2Dot) (hc : g * fDot = fDot * g) :
    g * tDot = tDot * g := by
  have hf : g * fDot * g⁻¹ = fDot := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : g * tDot * g⁻¹ = ⁅g * eJ {0, 2} * g⁻¹, fDot⁆ := by
    have h := map_commutatorElement (MulAut.conj g) (eJ {0, 2}) fDot
    simp only [MulAut.conj_apply] at h
    rw [hf] at h
    rw [ai_tDot_eq_comm]
    exact h
  obtain ⟨J, hJ⟩ := mono_Q2Dot_elim (mono_conj_mem_Q2Dot hg
    (mono_eJ_mem_Q2Dot (J := {0, 2}) (by decide) (by decide)))
  rw [hJ] at h1
  rcases ai_comm_eJ_f J with h | h
  · exfalso
    rw [h] at h1
    have : tDot = 1 := by
      calc tDot = g⁻¹ * (g * tDot * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    exact tDot_ne_one this
  · rw [h] at h1
    calc g * tDot = (g * tDot * g⁻¹) * g := by group
      _ = tDot * g := by rw [h1]

theorem ai_perm4_normal_closure : ∀ σ : Equiv.Perm (Fin 4), σ ≠ 1 →
    ∃ ρ₁ ρ₂ : Equiv.Perm (Fin 4), ρ₁ * σ * ρ₁⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
      (ρ₁ * σ * ρ₁⁻¹) * (ρ₂ * σ * ρ₂⁻¹) = Equiv.swap 0 1 * Equiv.swap 2 3 := by
  decide +kernel

theorem ai_hom_perm4_injective {H : Type*} [Group H] (ψ : Equiv.Perm (Fin 4) →* H)
    (h : ψ (Equiv.swap 0 1 * Equiv.swap 2 3) ≠ 1) : Function.Injective ψ := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨ρ₁, ρ₂, hρ⟩ := ai_perm4_normal_closure σ hne
  have h1 : ∀ ρ, ψ (ρ * σ * ρ⁻¹) = 1 := fun ρ => by
    rw [map_mul, map_mul, hσ, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rcases hρ with hρ | hρ
  · exact h (hρ ▸ h1 ρ₁)
  · refine h ?_
    rw [← hρ, map_mul, h1, h1, mul_one]

@[expose] def aiGen (a b c : GL6) (i : ℕ) : GL6 :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else 1

theorem ai_isCoxeterA_gen {a b c : GL6} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b * a = b * a * b) (hbc : b * c * b = c * b * c) (hac : a * c = c * a) :
    CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 3 (aiGen a b c) where
  sq i hi := by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [aiGen, ha, hb, hc]
  braid i hi := by
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> simp [aiGen, hab, hbc]
  comm i j hij hj := by
    have : i = 0 ∧ j = 2 := by omega
    obtain ⟨rfl, rfl⟩ := this
    simp [aiGen, hac]

@[expose] def aiPsi {a b c : GL6}
    (h : CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 3 (aiGen a b c)) :
    Equiv.Perm (Fin 4) →* GL6 :=
  (CFSG.Permutation.SymmetricCoxeter.exists_hom_perm 3 (aiGen a b c) h).choose

theorem aiPsi_adjSwap {a b c : GL6}
    (h : CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 3 (aiGen a b c)) {i : ℕ} (hi : i < 3) :
    aiPsi h (CFSG.Permutation.SymmetricCoxeter.adjSwap 3 i) = aiGen a b c i :=
  (CFSG.Permutation.SymmetricCoxeter.exists_hom_perm 3 (aiGen a b c) h).choose_spec i hi

theorem aiPsi_mem {a b c : GL6}
    (h : CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 3 (aiGen a b c)) {E : Subgroup GL6}
    (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) (σ : Equiv.Perm (Fin 4)) : aiPsi h σ ∈ E := by
  have hle : (aiPsi h).range ≤ E := by
    rw [MonoidHom.range_eq_map, ← CFSG.Permutation.SymmetricCoxeter.closure_adjSwap 3,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    have hi' : i < 3 := hi
    rw [aiPsi_adjSwap h hi']
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simpa [aiGen] using ‹_›
  exact hle ⟨σ, rfl⟩

theorem aiPsi_injective {a b c : GL6}
    (h : CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 3 (aiGen a b c)) (hne : a * c ≠ 1) :
    Function.Injective (aiPsi h) := by
  apply ai_hom_perm4_injective
  have e0 : Equiv.swap (0 : Fin 4) 1 = CFSG.Permutation.SymmetricCoxeter.adjSwap 3 0 :=
    (CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt (n := 3) (i := 0) (by omega)).symm
  have e2 : Equiv.swap (2 : Fin 4) 3 = CFSG.Permutation.SymmetricCoxeter.adjSwap 3 2 :=
    (CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt (n := 3) (i := 2) (by omega)).symm
  rw [e0, e2, map_mul, aiPsi_adjSwap h (by omega), aiPsi_adjSwap h (by omega)]
  simpa [aiGen] using hne

theorem ai_mulEquiv_E4S4 {E : Subgroup GL6} (hcard : Nat.card ↥E ≤ 96) {a b : GL6}
    (haE : a ∈ E) (hbE : b ∈ E) (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hac : ∀ g ∈ E, g * a = a * g) (hbc : ∀ g ∈ E, g * b = b * g)
    (ψ : Equiv.Perm (Fin 4) →* GL6) (hψ : Function.Injective ψ) (hψE : ∀ σ, ψ σ ∈ E) :
    Nonempty (↥E ≃* Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4)) := by
  classical
  set Z : Subgroup GL6 := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hZ
  have hZE : Z ≤ E := sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hbE)
  have hZc : ∀ z ∈ Z, ∀ g ∈ E, g * z = z * g := by
    have hC : Z ≤ Subgroup.centralizer (E : Set GL6) := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_iff.2 fun g hg => hac g hg
      · exact Subgroup.mem_centralizer_iff.2 fun g hg => hbc g hg
    intro z hz g hg
    exact (Subgroup.mem_centralizer_iff.1 (hC hz)) g hg
  have hAB : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    rcases mono_mem_zpowers_involution ha2 hxa with rfl | rfl
    · exact Subgroup.one_mem _
    · rcases mono_mem_zpowers_involution hb2 hxb with h | h
      · exact absurd h ha1
      · exact absurd h hne
  have hcomm : ∀ h ∈ Subgroup.zpowers a, h * b = b * h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact Commute.zpow_left (show Commute a b from hab) k
  have hnorm : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set GL6) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hcomm)
  have hZcard : Nat.card ↥Z = 4 := by
    rw [hZ, mono_card_sup_of_le_normalizer _ _ hAB hnorm, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1,
      orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1]
  have hZsq : ∀ z ∈ Z, z * z = 1 := by
    intro z hz
    have hz' : z ∈ ((Subgroup.zpowers a : Set GL6) * (Subgroup.zpowers b : Set GL6)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm]
      exact hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz'
    rcases mono_mem_zpowers_involution ha2 hx with rfl | rfl <;>
      rcases mono_mem_zpowers_involution hb2 hy with rfl | rfl
    · simp
    · simpa using hb2
    · simpa using ha2
    · calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hab]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  haveI : Nontrivial ↥Z :=
    ⟨⟨⟨a, Subgroup.mem_sup_left (Subgroup.mem_zpowers a)⟩, 1,
      fun h => ha1 (congrArg Subtype.val h)⟩⟩
  have hZexp : Monoid.exponent ↥Z = 2 := by
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (hZsq g.1 g.2)) hg
  haveI : IsKleinFour ↥Z := ⟨hZcard, hZexp⟩
  obtain ⟨eZ⟩ : Nonempty (↥Z ≃* Multiplicative (ZMod 2 × ZMod 2)) :=
    IsKleinFour.nonempty_mulEquiv
  let ψE : Equiv.Perm (Fin 4) →* ↥E := ψ.codRestrict E hψE
  have hcm : ∀ (z : ↥Z) (σ : Equiv.Perm (Fin 4)),
      Commute (Subgroup.inclusion hZE z) (ψE σ) := by
    intro z σ
    apply Subtype.ext
    show (z : GL6) * ψ σ = ψ σ * z
    exact (hZc z z.2 (ψ σ) (hψE σ)).symm
  let Φ : ↥Z × Equiv.Perm (Fin 4) →* ↥E :=
    MonoidHom.noncommCoprod (Subgroup.inclusion hZE) ψE hcm
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨z, σ⟩ h
    have h1 : (z : GL6) * ψ σ = 1 := by
      have := congrArg Subtype.val h
      simpa [Φ, MonoidHom.noncommCoprod_apply, ψE] using this
    have h2 : ψ σ = (z : GL6)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hσ : σ = 1 := by
      apply CFSG.perm_eq_one_of_forall_commute (by simp)
      intro ρ
      apply hψ
      rw [map_mul, map_mul, h2]
      exact (hZc _ (Z.inv_mem z.2) (ψ ρ) (hψE ρ)).symm
    subst hσ
    rw [map_one] at h1
    have : z = 1 := Subtype.ext (by simpa using h1)
    rw [this]
    rfl
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hΦbij : Function.Bijective Φ := by
    refine hΦinj.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, hZcard, h24]
    omega
  exact ⟨(MulEquiv.ofBijective Φ hΦbij).symm.trans (MulEquiv.prodCongr eZ (MulEquiv.refl _))⟩

theorem ai_pCore_eq {E R : Subgroup GL6} (hE : Nat.card ↥E = 96) (hRE : R ≤ E)
    (hR : Nat.card ↥R = 16) (hnorm : ∀ g ∈ E, ∀ r ∈ R, g * r * g⁻¹ ∈ R) {u v : GL6}
    (hu : u ∈ E) (hv : v ∈ E) (hu2 : u * u = 1) (hv2 : v * v = 1) (huv3 : (u * v) ^ 3 = 1)
    (huv1 : u * v ≠ 1) : pCoreOf 2 E = R := by
  have hRp : IsPGroup 2 ↥R := IsPGroup.of_card (n := 4) (by rw [hR]; norm_num)
  have hEnorm : E ≤ Subgroup.normalizer (R : Set GL6) := fun g hg =>
    mono_mem_normalizer_of_conj (fun s hs => hnorm g hg s hs) (fun s hs => by
      have := hnorm g⁻¹ (E.inv_mem hg) s hs
      rwa [inv_inv] at this)
  have hRle : R ≤ pCoreOf 2 E :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRE hEnorm hRp
  refine le_antisymm ?_ hRle
  by_contra hnot
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 E) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 E
  have hPE : pCoreOf 2 E ≤ E := CFSG.LieType.BorelTits.pCoreOf_le 2 E
  have hPnorm : ∀ n ∈ E, ∀ r ∈ pCoreOf 2 E, n * r * n⁻¹ ∈ pCoreOf 2 E := fun n hn r hr =>
    mono_pCoreOf_conj E hn hr
  have hlt : R < pCoreOf 2 E := lt_of_le_of_ne hRle (fun h => hnot (h ▸ le_rfl))
  have hcard : 16 < Nat.card ↥(pCoreOf 2 E) := by
    rw [← hR]
    exact Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hdvd : Nat.card ↥(pCoreOf 2 E) ∣ 96 := hE ▸ Subgroup.card_dvd_of_le hPE
  have h32 : Nat.card ↥(pCoreOf 2 E) = 32 := by
    rw [hk] at hcard hdvd ⊢
    have hle : 2 ^ k ≤ 96 := Nat.le_of_dvd (by norm_num) hdvd
    have hk9 : k < 7 := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.1 h)
      omega
    interval_cases k <;> omega
  have hrel : (pCoreOf 2 E).relIndex E = 3 := by
    have := Subgroup.relIndex_mul_card (pCoreOf 2 E) E
    rw [inf_eq_left.2 hPE, h32, hE] at this
    omega
  have hodd : ¬ 2 ∣ (pCoreOf 2 E).relIndex E := by
    rw [hrel]
    omega
  have hu' : u ∈ pCoreOf 2 E := mono_mem_of_normal_odd_index hPE hPnorm hodd hu hu2
  have hv' : v ∈ pCoreOf 2 E := mono_mem_of_normal_odd_index hPE hPnorm hodd hv hv2
  have hy : u * v ∈ pCoreOf 2 E := Subgroup.mul_mem _ hu' hv'
  obtain ⟨n, hn⟩ := hP2 ⟨_, hy⟩
  have hyn : (u * v) ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h1 := orderOf_dvd_of_pow_eq_one hyn
  have h2 := orderOf_dvd_of_pow_eq_one huv3
  have h3 : Nat.Coprime (orderOf (u * v)) 3 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left n (by norm_num))
  exact huv1 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2))

theorem ai_isEn {CQ : Subgroup GL6} (hCQc : ∀ x ∈ CQ, ∀ y ∈ CQ, x * y = y * x)
    (hCQ2 : ∀ x ∈ CQ, x * x = 1) (hf : ∀ x ∈ CQ, x * fDot = fDot * x)
    (hcard : Nat.card ↥(Subgroup.zpowers fDot ⊔ CQ) = 16) :
    IsEn 4 ↥(Subgroup.zpowers fDot ⊔ CQ) := by
  have hnorm : Subgroup.zpowers fDot ≤ Subgroup.normalizer (CQ : Set GL6) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun x hx => hf x hx)
  have hel : ∀ x ∈ Subgroup.zpowers fDot ⊔ CQ, ∃ q ∈ CQ, x = q ∨ x = q * fDot := by
    intro x hx
    have hx2 : x ∈ ((CQ ⊔ Subgroup.zpowers fDot : Subgroup GL6) : Set GL6) := by
      rw [SetLike.mem_coe, sup_comm]
      exact hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hx2
    obtain ⟨q, hq, y, hy, rfl⟩ := hx2
    rcases mono_mem_zpowers_involution mono_fDot_mul_self hy with rfl | rfl
    · exact ⟨q, hq, Or.inl (mul_one q)⟩
    · exact ⟨q, hq, Or.inr rfl⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers fDot ⊔ CQ, ∀ y ∈ Subgroup.zpowers fDot ⊔ CQ,
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨q, hq, hxq⟩ := hel x hx
    obtain ⟨q', hq', hyq⟩ := hel y hy
    have c1 : Commute q q' := hCQc q hq q' hq'
    have c2 : Commute q fDot := hf q hq
    have c3 : Commute q' fDot := hf q' hq'
    rcases hxq with rfl | rfl <;> rcases hyq with rfl | rfl
    · exact c1.eq
    · exact (c1.mul_right c2).eq
    · exact (c1.mul_left c3.symm).eq
    · exact ((c1.mul_left c3.symm).mul_right (c2.mul_left (Commute.refl fDot))).eq
  refine ⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2), fun a => Subtype.ext ?_, hcard⟩
  obtain ⟨q, hq, h | h⟩ := hel a.1 a.2
  · show a.1 * a.1 = 1
    rw [h]
    exact hCQ2 q hq
  · show a.1 * a.1 = 1
    rw [h]
    calc q * fDot * (q * fDot) = q * (fDot * q) * fDot := by group
      _ = q * (q * fDot) * fDot := by rw [← hf q hq]
      _ = (q * q) * (fDot * fDot) := by group
      _ = 1 := by rw [hCQ2 q hq, mono_fDot_mul_self, one_mul]

theorem ai_R_normal {E Qi : Subgroup GL6} (hQ : ∀ g ∈ E, ∀ q ∈ Qi, g * q * g⁻¹ ∈ Qi)
    (hc : ∀ g ∈ E, g * fDot = fDot * g) :
    ∀ g ∈ E, ∀ r ∈ Subgroup.zpowers fDot ⊔ (Qi ⊓ Subgroup.centralizer ({fDot} : Set GL6)),
      g * r * g⁻¹ ∈ Subgroup.zpowers fDot ⊔ (Qi ⊓ Subgroup.centralizer ({fDot} : Set GL6)) := by
  intro g hg
  apply mono_conj_mem_sup
  · intro x hx
    apply Subgroup.mem_sup_left
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hgf : Commute g fDot := hc g hg
    have h : g * fDot ^ k * g⁻¹ = fDot ^ k := by
      rw [(hgf.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [h]
    exact hx
  · intro y hy
    apply Subgroup.mem_sup_right
    refine ⟨hQ g hg y hy.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hyf : Commute y fDot := Subgroup.mem_centralizer_singleton_iff.1 hy.2
    have hgf : Commute g fDot := hc g hg
    exact (hgf.mul_left hyf).mul_left hgf.inv_left

@[expose] def aiU1Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def aiU2Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def aiU3Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def aiU1 : GL6 := quatOfOrth aiU1Mat (by decide)
@[expose] def aiU2 : GL6 := quatOfOrth aiU2Mat (by decide)
@[expose] def aiU3 : GL6 := quatOfOrth aiU3Mat (by decide)

theorem aiU1_mem : aiU1 ∈ M2Dot :=
  ⟨quat_mem_MDot_of_refl [quatRV ![1, 2, 0, 0, 0, 0], quatRV ![0, 0, 1, 1, 0, 0]] aiU1
      (by decide) (by decide) (by decide),
    mono_mem_stabilizer_Lambda (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide)⟩

theorem aiU2_mem : aiU2 ∈ M2Dot :=
  ⟨quat_mem_MDot_of_refl [quatRV ![1, 2, 0, 0, 0, 0], quatRV ![0, 0, 0, 1, 1, 0]] aiU2
      (by decide) (by decide) (by decide),
    mono_mem_stabilizer_Lambda (Equiv.swap 0 1 * Equiv.swap 3 4) (by decide)⟩

theorem aiU3_mem : aiU3 ∈ M2Dot :=
  ⟨quat_mem_MDot_of_refl [quatRV ![1, 2, 0, 0, 0, 0], quatRV ![0, 0, 1, 2, 0, 0]] aiU3
      (by decide) (by decide) (by decide),
    mono_mem_stabilizer_Lambda (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide)⟩

theorem ai_mem_EDot {Mi : Subgroup GL6} {g : GL6} (h1 : g ∈ Mi) (h2 : g * fDot = fDot * g) :
    g ∈ EDot Mi :=
  ⟨h1, Subgroup.mem_centralizer_singleton_iff.2 h2⟩

theorem ai_comm_of_mem_EDot {Mi : Subgroup GL6} {g : GL6} (h : g ∈ EDot Mi) :
    g * fDot = fDot * g :=
  Subgroup.mem_centralizer_singleton_iff.1 h.2

theorem aiU1_mem_E2 : aiU1 ∈ EDot M2Dot := ai_mem_EDot aiU1_mem (by decide +kernel)
theorem aiU2_mem_E2 : aiU2 ∈ EDot M2Dot := ai_mem_EDot aiU2_mem (by decide +kernel)
theorem aiU3_mem_E2 : aiU3 ∈ EDot M2Dot := ai_mem_EDot aiU3_mem (by decide +kernel)

theorem ai_isCoxeterA_U :
    CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 3 (aiGen aiU1 aiU2 aiU3) :=
  ai_isCoxeterA_gen (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def aiPsi2 : Equiv.Perm (Fin 4) →* GL6 := aiPsi ai_isCoxeterA_U

theorem aiPsi2_injective : Function.Injective aiPsi2 :=
  aiPsi_injective ai_isCoxeterA_U (by decide +kernel)

theorem aiPsi2_mem (σ : Equiv.Perm (Fin 4)) : aiPsi2 σ ∈ EDot M2Dot :=
  aiPsi_mem ai_isCoxeterA_U aiU1_mem_E2 aiU2_mem_E2 aiU3_mem_E2 σ

theorem ai_tDot_mem_E2 : tDot ∈ EDot M2Dot :=
  ai_mem_EDot (Q2Dot_le_M2Dot (mono_eJ_mem_Q2Dot (J := {0, 1}) (by decide) (by decide)))
    (by decide +kernel)

theorem ai_fDot_mem_E2 : fDot ∈ EDot M2Dot := ai_mem_EDot fDot_mem_M12Dot.2 rfl

theorem ai_EDot_M2Dot_equiv :
    Nonempty (↥(EDot M2Dot) ≃* Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4)) :=
  ai_mulEquiv_E4S4 (by rw [ai_card_E2]) ai_tDot_mem_E2 ai_fDot_mem_E2 tDot_mul_self
    mono_fDot_mul_self (by decide +kernel) tDot_ne_one mono_fDot_ne_one (by decide +kernel)
    (fun g hg => ai_tDot_central hg.1 (ai_comm_of_mem_EDot hg))
    (fun g hg => ai_comm_of_mem_EDot hg) aiPsi2 aiPsi2_injective aiPsi2_mem

@[expose] def aiX (c : ZMod 3) (S : List V6) : Finset V6 :=
  Finset.univ.filter fun v => v 4 = 0 ∧ v 5 = 0 ∧ qV v = c ∧ ∀ w ∈ S, bil v w = 0

theorem ai_orbit_mem {h : GL6} (hh : h ∈ M1Dot) (S : List V6) (c : ZMod 3)
    (hfix : ∀ w ∈ S, h • w = w) {v : V6} (hv : v ∈ aiX c S) : h • v ∈ aiX c S := by
  simp only [aiX, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨h4, h5, hq, horth⟩ := hv
  have hOVq := MDot_le_OVq (Subgroup.mem_inf.1 hh).1
  have h45 := quat_M1Dot_mem hh ⟨h4, h5⟩
  refine ⟨h45.1, h45.2, ?_, ?_⟩
  · rw [quat_smul_def, qV_mulVec_of_mem_OVq hOVq]
    exact hq
  · intro w hw
    have hw' : (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w = w := hfix w hw
    rw [quat_smul_def]
    calc bil ((h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) w
        = bil ((h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v)
            ((h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w) := by rw [hw']
      _ = bil v w := bil_mulVec_of_mem_OVq hOVq v w
      _ = 0 := horth w hw

theorem ai_X_card1 : (aiX (-1) [x1 - x2]).card = 6 := by decide +kernel

theorem ai_X_card2 : (aiX 1 [x1 - x2, x1 + x2]).card = 4 := by decide +kernel

theorem ai_X_card3 : (aiX 1 [x1 - x2, x1 + x2, x3]).card = 2 := by decide +kernel

theorem ai_eigen_d : ∀ v : V6, v 4 = 0 → v 5 = 0 → fMat *ᵥ v = -v → qV v = -1 →
    v = x1 - x2 ∨ v = -(x1 - x2) := by
  decide +kernel

theorem ai_orbit_d {h : GL6} (hh : h ∈ EDot M1Dot) :
    h • (x1 - x2) = x1 - x2 ∨ h • (x1 - x2) = -(x1 - x2) := by
  obtain ⟨hM, hc⟩ := hh
  have hcomm : h * fDot = fDot * h := Subgroup.mem_centralizer_singleton_iff.1 hc
  have hOVq := MDot_le_OVq (Subgroup.mem_inf.1 hM).1
  have h45 := quat_M1Dot_mem hM (v := x1 - x2) (by decide)
  have hq : qV ((h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2)) = -1 := by
    rw [qV_mulVec_of_mem_OVq hOVq]
    exact qV_x1_sub_x2
  have hf : fMat *ᵥ ((h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2)) =
      -((h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2)) := by
    have e1 : (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) * fMat =
        fMat * (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
      congrArg Units.val hcomm
    have e2 : fMat *ᵥ (x1 - x2) = -(x1 - x2) := by decide
    rw [Matrix.mulVec_mulVec, ← e1, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_neg]
  rw [quat_smul_def]
  exact ai_eigen_d _ h45.1 h45.2 hf hq

abbrev aiG1 : Subgroup GL6 := EDot M1Dot ⊓ MulAction.stabilizer GL6 (x1 - x2)
abbrev aiG2 : Subgroup GL6 := aiG1 ⊓ MulAction.stabilizer GL6 (x1 + x2)
abbrev aiG3 : Subgroup GL6 := aiG2 ⊓ MulAction.stabilizer GL6 x3
abbrev aiG4 : Subgroup GL6 := aiG3 ⊓ MulAction.stabilizer GL6 x4

theorem ai_G4_eq_bot : aiG4 = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg3, h4⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hg2, h3⟩ := Subgroup.mem_inf.1 hg3
  obtain ⟨hg1, hw⟩ := Subgroup.mem_inf.1 hg2
  obtain ⟨hgE, hd⟩ := Subgroup.mem_inf.1 hg1
  have hd' : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 - x2) = x1 - x2 :=
    MulAction.mem_stabilizer_iff.1 hd
  have hw' : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (x1 + x2) = x1 + x2 :=
    MulAction.mem_stabilizer_iff.1 hw
  have hx3 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x3 = x3 := MulAction.mem_stabilizer_iff.1 h3
  have hx4 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x4 = x4 := MulAction.mem_stabilizer_iff.1 h4
  have e1 : x1 = (2 : ZMod 3) • ((x1 - x2) + (x1 + x2)) := by decide
  have e2 : x2 = (2 : ZMod 3) • ((x1 + x2) - (x1 - x2)) := by decide
  have f1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x1 = x1 := by
    conv_lhs => rw [e1]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, hd', hw', ← e1]
  have f2 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x2 = x2 := by
    conv_lhs => rw [e2]
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hd', hw', ← e2]
  exact Subgroup.mem_bot.2 (quat_eq_one_of_fix hgE.1 f1 f2 hx3 hx4)

set_option maxRecDepth 100000 in
theorem ai_card_E1_le : Nat.card ↥(EDot M1Dot) ≤ 96 := by
  have s0 := quat_card_step (EDot M1Dot) (x1 - x2) {x1 - x2, -(x1 - x2)} (fun h hh => by
    rcases ai_orbit_d hh with h1 | h1 <;> simp [h1])
  have s1 := quat_card_step aiG1 (x1 + x2) (aiX (-1) [x1 - x2]) fun h hh =>
    ai_orbit_mem hh.1.1 [x1 - x2] (-1) (by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      exact MulAction.mem_stabilizer_iff.1 hh.2) (by
      simp only [aiX, Finset.mem_filter, Finset.mem_univ, true_and]; decide)
  have s2 := quat_card_step aiG2 x3 (aiX 1 [x1 - x2, x1 + x2]) fun h hh =>
    ai_orbit_mem hh.1.1.1 [x1 - x2, x1 + x2] 1 (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact MulAction.mem_stabilizer_iff.1 hh.1.2
      · exact MulAction.mem_stabilizer_iff.1 hh.2) (by
      simp only [aiX, Finset.mem_filter, Finset.mem_univ, true_and]; decide)
  have s3 := quat_card_step aiG3 x4 (aiX 1 [x1 - x2, x1 + x2, x3]) fun h hh =>
    ai_orbit_mem hh.1.1.1.1 [x1 - x2, x1 + x2, x3] 1 (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact MulAction.mem_stabilizer_iff.1 hh.1.1.2
      · exact MulAction.mem_stabilizer_iff.1 hh.1.2
      · exact MulAction.mem_stabilizer_iff.1 hh.2) (by
      simp only [aiX, Finset.mem_filter, Finset.mem_univ, true_and]; decide)
  rw [Finset.card_pair (by decide)] at s0
  rw [ai_X_card1] at s1
  rw [ai_X_card2] at s2
  rw [ai_X_card3] at s3
  have s4 : Nat.card ↥aiG4 = 1 := by
    rw [ai_G4_eq_bot]
    exact Subgroup.card_bot
  calc Nat.card ↥(EDot M1Dot) ≤ 2 * Nat.card ↥aiG1 := s0
    _ ≤ 2 * (6 * Nat.card ↥aiG2) := Nat.mul_le_mul_left _ s1
    _ ≤ 2 * (6 * (4 * Nat.card ↥aiG3)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ s2)
    _ ≤ 2 * (6 * (4 * (2 * Nat.card ↥aiG4))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ s3))
    _ = 96 := by rw [s4]

@[expose] def aiT2Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 2, 2, 2, 0, 0; 2, 1, 2, 2, 0, 0; 2, 2, 1, 2, 0, 0; 2, 2, 2, 1, 0, 0; 0, 0, 0, 0, 2, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def aiT1 : GL6 := eJ {0, 1, 3, 4}

@[expose] def aiT2 : GL6 := quatOfOrth aiT2Mat (by decide)

@[expose] def aiT3 : GL6 := eJ {0, 1, 2, 4}

theorem aiT1_mem : aiT1 ∈ M1Dot :=
  quat_mem_M1Dot (eJ_mem_MDot _ (by decide) (by decide)) (by decide +kernel)

theorem aiT3_mem : aiT3 ∈ M1Dot :=
  quat_mem_M1Dot (eJ_mem_MDot _ (by decide) (by decide)) (by decide +kernel)

theorem aiT2_mem : aiT2 ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![1, 1, 1, 1, 0, 0], quatRV ![1, 0, 0, 0, 0, 0],
      quatRV ![0, 1, 0, 0, 0, 0], quatRV ![0, 0, 1, 0, 0, 0], quatRV ![0, 0, 0, 1, 0, 0],
      quatRV ![0, 0, 0, 0, 1, 0]] aiT2 (by decide) (by decide) (by decide))
    (by decide +kernel)

theorem aiT1_mem_E1 : aiT1 ∈ EDot M1Dot := ai_mem_EDot aiT1_mem (by decide +kernel)
theorem aiT2_mem_E1 : aiT2 ∈ EDot M1Dot := ai_mem_EDot aiT2_mem (by decide +kernel)
theorem aiT3_mem_E1 : aiT3 ∈ EDot M1Dot := ai_mem_EDot aiT3_mem (by decide +kernel)

theorem ai_isCoxeterA_T :
    CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 3 (aiGen aiT1 aiT2 aiT3) :=
  ai_isCoxeterA_gen (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def aiPsi1 : Equiv.Perm (Fin 4) →* GL6 := aiPsi ai_isCoxeterA_T

theorem aiPsi1_injective : Function.Injective aiPsi1 :=
  aiPsi_injective ai_isCoxeterA_T (by decide +kernel)

theorem aiPsi1_mem (σ : Equiv.Perm (Fin 4)) : aiPsi1 σ ∈ EDot M1Dot :=
  aiPsi_mem ai_isCoxeterA_T aiT1_mem_E1 aiT2_mem_E1 aiT3_mem_E1 σ

theorem ai_zDot_mem_E1 : zDot ∈ EDot M1Dot :=
  ai_mem_EDot (quat_mem_M1Dot zDot_mem_GDot.1 rfl) (by decide +kernel)

theorem ai_fDot_mem_E1 : fDot ∈ EDot M1Dot :=
  ai_mem_EDot (by
    have := fDot_mem_M12Dot
    exact this.1) rfl

theorem ai_EDot_M1Dot_equiv :
    Nonempty (↥(EDot M1Dot) ≃* Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4)) :=
  ai_mulEquiv_E4S4 ai_card_E1_le ai_zDot_mem_E1 ai_fDot_mem_E1 zDot_mul_self mono_fDot_mul_self
    (by decide +kernel) (by decide +kernel) mono_fDot_ne_one (by decide +kernel)
    (fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg.1.2)
    (fun g hg => ai_comm_of_mem_EDot hg) aiPsi1 aiPsi1_injective aiPsi1_mem

theorem ai_card_E1 : Nat.card ↥(EDot M1Dot) = 96 := by
  obtain ⟨e⟩ := ai_EDot_M1Dot_equiv
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [h24]
  have : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2 × ZMod 2) ≃ ZMod 2 × ZMod 2),
      Nat.card_prod]
    simp [Nat.card_zmod]
  rw [this]

@[expose] def aiP : Fin 8 → QuaternionGroup 2 × QuaternionGroup 2 :=
  ![(.a 0, .a 0), (.a 0, .a 2), (.a 1, .a 1), (.a 1, .a 3), (.xa 0, .xa 1), (.xa 0, .xa 3),
    (.xa 1, .xa 0), (.xa 1, .xa 2)]

@[expose] def aiE (k : Fin 8) : GL6 := q8Hom (aiP k)

theorem ai_E_comm_f : ∀ k : Fin 8, aiE k * fDot = fDot * aiE k := by decide +kernel

theorem ai_E_comm : ∀ j k : Fin 8, aiE j * aiE k = aiE k * aiE j := by decide +kernel

theorem ai_E_sq : ∀ k : Fin 8, aiE k * aiE k = 1 := by decide +kernel

theorem ai_E_inj : ∀ j k : Fin 8, aiE j = aiE k → j = k := by decide +kernel

theorem ai_q8Hom_ne_f : ∀ p : QuaternionGroup 2 × QuaternionGroup 2, q8Hom p ≠ fDot := by
  decide +kernel

theorem ai_q8Hom_comm_f : ∀ p : QuaternionGroup 2 × QuaternionGroup 2,
    q8Hom p * fDot = fDot * q8Hom p → ∃ k : Fin 8, q8Hom p = aiE k := by
  decide +kernel

theorem ai_mem_CQ1_iff {g : GL6} :
    g ∈ Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ↔ ∃ k : Fin 8, g = aiE k := by
  constructor
  · rintro ⟨hq, hc⟩
    rw [Q1Dot_eq] at hq
    obtain ⟨p, rfl⟩ := hq
    exact (ai_q8Hom_comm_f p (Subgroup.mem_centralizer_singleton_iff.1 hc)).imp fun k hk => hk
  · rintro ⟨k, rfl⟩
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (ai_E_comm_f k)⟩
    rw [Q1Dot_eq]
    exact ⟨aiP k, rfl⟩

theorem ai_card_CQ1 :
    Nat.card ↥(Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = 8 := by
  have hf : ∀ k : Fin 8, aiE k ∈ Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
    fun k => ai_mem_CQ1_iff.2 ⟨k, rfl⟩
  let f : Fin 8 → ↥(Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) := fun k => ⟨aiE k, hf k⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro j k h
      exact ai_E_inj j k (congrArg Subtype.val h)
    · rintro ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := ai_mem_CQ1_iff.1 hg
      exact ⟨k, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def aiA : Fin 8 → V6 :=
  ![0, 0, ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![2, 1, 2, 2, 0, 0], ![1, 1, 2, 1, 0, 0],
    ![2, 2, 2, 2, 0, 0], ![1, 2, 1, 2, 0, 0]]

@[expose] def aiB : Fin 8 → V6 :=
  ![0, 0, ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 0, 0], ![1, 1, 1, 2, 0, 0],
    ![2, 2, 1, 1, 0, 0], ![2, 1, 1, 2, 0, 0]]

theorem ai_commSp_eq_span {g : GL6} {a b : V6}
    (hcol : ∀ j : Fin 6, ∃ s t : ZMod 3,
      s • a + t • b = fun i => ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1) i j)
    (ha : ∃ c : V6, ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1) *ᵥ c = a)
    (hb : ∃ c : V6, ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1) *ᵥ c = b) :
    commSp g = spn {a, b} := by
  apply le_antisymm
  · unfold commSp spn
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s, t, h⟩ := hcol j
    rw [SetLike.mem_coe]
    have hc : ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1).col j =
        fun i => ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1) i j := rfl
    rw [hc, ← h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · unfold spn
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · obtain ⟨c, rfl⟩ := ha
      exact ⟨c, rfl⟩
    · obtain ⟨c, rfl⟩ := hb
      exact ⟨c, rfl⟩

theorem ai_range_vec2 (a b : V6) : Set.range ![a, b] = {a, b} := by
  ext w
  simp [Fin.exists_fin_two, eq_comm]
  tauto

theorem ai_plane_props {a b : V6} (h4a : a 4 = 0 ∧ a 5 = 0) (h4b : b 4 = 0 ∧ b 5 = 0)
    (hno : ∀ s t : ZMod 3, qV (s • a + t • b) = 0 → s = 0 ∧ t = 0) :
    spn {a, b} ≤ V4plus ∧ Module.finrank (ZMod 3) (spn {a, b}) = 2 ∧
      SignMinus (spn {a, b}) := by
  have hmem : ∀ w ∈ spn {a, b}, ∃ s t : ZMod 3, w = s • a + t • b := by
    intro w hw
    obtain ⟨s, t, h⟩ := Submodule.mem_span_pair.1 hw
    exact ⟨s, t, h.symm⟩
  have haniso : ∀ w ∈ spn {a, b}, qV w = 0 → w = 0 := by
    intro w hw hq
    obtain ⟨s, t, rfl⟩ := hmem w hw
    obtain ⟨rfl, rfl⟩ := hno s t hq
    simp
  have hli : LinearIndependent (ZMod 3) ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    apply hno
    rw [h]
    exact qV_zero
  have hfin : Module.finrank (ZMod 3) (spn {a, b}) = 2 := by
    have h := finrank_span_eq_card hli
    rw [ai_range_vec2] at h
    exact h
  refine ⟨?_, hfin, ?_, ?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro w (rfl | rfl)
    · exact (quat_mem_V4plus_iff _).2 h4a
    · exact (quat_mem_V4plus_iff _).2 h4b
  · intro w hw hb
    have h1 := hb w hw
    rw [bil_self] at h1
    have h2 : qV w = 0 := (by decide : ∀ x : ZMod 3, 2 * x = 0 → x = 0) _ h1
    exact haniso w hw h2
  · rw [hfin]
    decide
  · rintro ⟨U, hUW, hs, hdim⟩
    have hU : U = ⊥ := eq_bot_iff.2 fun u hu =>
      (Submodule.mem_bot _).2 (haniso u (hUW hu) (hs u hu))
    rw [hU, finrank_bot, hfin] at hdim
    omega

theorem ai_E_props (k : Fin 8) (hk : 2 ≤ k.val) :
    commSp (aiE k) ≤ V4plus ∧ Module.finrank (ZMod 3) (commSp (aiE k)) = 2 ∧
      SignMinus (commSp (aiE k)) := by
  have hcol : ∀ k : Fin 8, 2 ≤ k.val → ∀ j : Fin 6, ∃ s t : ZMod 3,
      s • aiA k + t • aiB k =
        fun i => (((aiE k : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1) i j := by
    decide +kernel
  have ha : ∀ k : Fin 8, 2 ≤ k.val → ∃ c : V6,
      (((aiE k : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1) *ᵥ c = aiA k := by
    decide +kernel
  have hb : ∀ k : Fin 8, 2 ≤ k.val → ∃ c : V6,
      (((aiE k : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1) *ᵥ c = aiB k := by
    decide +kernel
  have h4 : ∀ k : Fin 8, 2 ≤ k.val →
      (aiA k 4 = 0 ∧ aiA k 5 = 0) ∧ (aiB k 4 = 0 ∧ aiB k 5 = 0) := by
    decide +kernel
  have hno : ∀ k : Fin 8, 2 ≤ k.val → ∀ s t : ZMod 3,
      qV (s • aiA k + t • aiB k) = 0 → s = 0 ∧ t = 0 := by
    decide +kernel
  rw [ai_commSp_eq_span (hcol k hk) (ha k hk) (hb k hk)]
  exact ai_plane_props (h4 k hk).1 (h4 k hk).2 (hno k hk)

theorem Q1Dot_inf_centralizer_nonid :
    {u : GL6 | u ∈ Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ∧ u ≠ 1} =
      {zDot} ∪ {u : GL6 | u ∈ Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ∧ u ≠ 1 ∧
        u * u = 1 ∧ commSp u ≤ V4plus ∧ Module.finrank (ZMod 3) (commSp u) = 2 ∧
        SignMinus (commSp u)} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hu, hu1⟩
    obtain ⟨k, rfl⟩ := ai_mem_CQ1_iff.1 hu
    have hk : k = 0 ∨ k = 1 ∨ 2 ≤ k.val := by
      fin_cases k <;> simp
    rcases hk with rfl | rfl | hk
    · exact absurd (by decide +kernel : aiE 0 = 1) hu1
    · left
      decide +kernel
    · exact Or.inr ⟨hu, hu1, ai_E_sq k, ai_E_props k hk⟩
  · rintro (rfl | ⟨hu, hu1, -⟩)
    · exact ⟨ai_mem_CQ1_iff.2 ⟨1, by decide +kernel⟩, by decide⟩
    · exact ⟨hu, hu1⟩

theorem ai_fDot_not_mem_Q1Dot : fDot ∉ Q1Dot := by
  rw [Q1Dot_eq]
  rintro ⟨p, hp⟩
  exact ai_q8Hom_ne_f p hp

theorem ai_fDot_not_mem_Q2Dot : fDot ∉ Q2Dot := by
  intro h
  have : fDot ∈ s5Hom.range ⊓ Q2Dot := ⟨⟨Equiv.swap 0 1, fDot_eq_s5Hom.symm⟩, h⟩
  rw [s5Hom_range_inf] at this
  exact mono_fDot_ne_one this

theorem ai_R_card {Qi : Subgroup GL6}
    (hCQ : Nat.card ↥(Qi ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = 8) (hf : fDot ∉ Qi) :
    Subgroup.zpowers fDot ⊓ (Qi ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = ⊥ ∧
      Nat.card ↥(Subgroup.zpowers fDot ⊔ (Qi ⊓ Subgroup.centralizer ({fDot} : Set GL6))) = 16 := by
  have hinf : Subgroup.zpowers fDot ⊓ (Qi ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rcases mono_mem_zpowers_involution mono_fDot_mul_self hx1 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hx2.1 hf
  have hnorm : Subgroup.zpowers fDot ≤
      Subgroup.normalizer ((Qi ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) :
        Set GL6) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.1 hx.2
  refine ⟨hinf, ?_⟩
  have hord : orderOf fDot = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact mono_fDot_mul_self) mono_fDot_ne_one
  rw [sup_comm, mono_card_sup_of_le_normalizer _ _ (by rw [inf_comm]; exact hinf) hnorm, hCQ,
    Nat.card_zpowers, hord]

theorem ADot_M1Dot_eq : ADot M1Dot =
    Subgroup.zpowers fDot ⊔ (Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) := by
  have hcard := (ai_R_card ai_card_CQ1 ai_fDot_not_mem_Q1Dot).2
  have hRE : Subgroup.zpowers fDot ⊔ (Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ≤
      EDot M1Dot := by
    refine sup_le (Subgroup.zpowers_le.2 ai_fDot_mem_E1) fun x hx => ⟨?_, hx.2⟩
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 M1Dot hx.1
  exact ai_pCore_eq ai_card_E1 hRE hcard
    (ai_R_normal (fun g hg q hq => quat_Q1Dot_conj hg.1 hq) (fun g hg => ai_comm_of_mem_EDot hg))
    aiT1_mem_E1 aiT2_mem_E1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem ADot_M2Dot_eq : ADot M2Dot =
    Subgroup.zpowers fDot ⊔ (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) := by
  have hcard := (ai_R_card ai_card_CQ2 ai_fDot_not_mem_Q2Dot).2
  have hRE : Subgroup.zpowers fDot ⊔ (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ≤
      EDot M2Dot := by
    refine sup_le (Subgroup.zpowers_le.2 ai_fDot_mem_E2) fun x hx => ⟨Q2Dot_le_M2Dot hx.1, hx.2⟩
  exact ai_pCore_eq ai_card_E2 hRE hcard
    (ai_R_normal (fun g hg q hq => mono_conj_mem_Q2Dot hg.1 hq)
      (fun g hg => ai_comm_of_mem_EDot hg))
    aiU1_mem_E2 aiU2_mem_E2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem ADot_part1 :
    ADot M1Dot = Subgroup.zpowers fDot ⊔ (Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ∧
      Subgroup.zpowers fDot ⊓ (Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = ⊥ ∧
      ADot M2Dot = Subgroup.zpowers fDot ⊔ (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ∧
      Subgroup.zpowers fDot ⊓ (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = ⊥ :=
  ⟨ADot_M1Dot_eq, (ai_R_card ai_card_CQ1 ai_fDot_not_mem_Q1Dot).1, ADot_M2Dot_eq,
    (ai_R_card ai_card_CQ2 ai_fDot_not_mem_Q2Dot).1⟩

theorem ADot_M1Dot_isEn : IsEn 4 ↥(ADot M1Dot) := by
  rw [ADot_M1Dot_eq]
  refine ai_isEn ?_ ?_ (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx.2)
    (ai_R_card ai_card_CQ1 ai_fDot_not_mem_Q1Dot).2
  · intro x hx y hy
    obtain ⟨j, rfl⟩ := ai_mem_CQ1_iff.1 hx
    obtain ⟨k, rfl⟩ := ai_mem_CQ1_iff.1 hy
    exact ai_E_comm j k
  · intro x hx
    obtain ⟨k, rfl⟩ := ai_mem_CQ1_iff.1 hx
    exact ai_E_sq k

theorem ADot_M2Dot_isEn : IsEn 4 ↥(ADot M2Dot) := by
  rw [ADot_M2Dot_eq]
  refine ai_isEn ?_ ?_ (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx.2)
    (ai_R_card ai_card_CQ2 ai_fDot_not_mem_Q2Dot).2
  · intro x hx y hy
    obtain ⟨J, rfl⟩ := mono_Q2Dot_elim hx.1
    obtain ⟨K, rfl⟩ := mono_Q2Dot_elim hy.1
    exact mono_eJ_comm J K
  · intro x hx
    obtain ⟨J, rfl⟩ := mono_Q2Dot_elim hx.1
    exact mono_eJ_mul_self J

theorem EDot_structure (Mi : Subgroup GL6) (h : Mi = M1Dot ∨ Mi = M2Dot) :
    Nonempty (↥(EDot Mi) ≃* Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4)) ∧
      IsEn 4 ↥(ADot Mi) := by
  rcases h with rfl | rfl
  · exact ⟨ai_EDot_M1Dot_equiv, ADot_M1Dot_isEn⟩
  · exact ⟨ai_EDot_M2Dot_equiv, ADot_M2Dot_isEn⟩

theorem ai_mem_V3plus_iff (w : V6) : w ∈ V3plus ↔ w 2 = 0 ∧ w 3 = 0 ∧ w 4 = 0 := by
  constructor
  · intro hw
    unfold V3plus spn at hw
    induction hw using Submodule.span_induction with
    | mem x hx => rcases hx with rfl | rfl | rfl <;> decide
    | zero => decide
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_, ?_⟩
      · rw [Pi.add_apply, hx.1, hy.1]; exact add_zero _
      · rw [Pi.add_apply, hx.2.1, hy.2.1]; exact add_zero _
      · rw [Pi.add_apply, hx.2.2, hy.2.2]; exact add_zero _
    | smul c x _ hx =>
      refine ⟨?_, ?_, ?_⟩
      · rw [Pi.smul_apply, hx.1]; exact mul_zero _
      · rw [Pi.smul_apply, hx.2.1]; exact mul_zero _
      · rw [Pi.smul_apply, hx.2.2]; exact mul_zero _
  · rintro ⟨h2, h3, h4⟩
    have key : ∀ w : V6, w 2 = 0 → w 3 = 0 → w 4 = 0 →
        w = w 0 • x1 + w 1 • x2 + w 5 • x6 := by decide +kernel
    rw [key w h2 h3 h4]
    unfold V3plus spn
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem isNondegSub_V3plus : IsNondegSub V3plus := by
  intro w hw hb
  have hW := (ai_mem_V3plus_iff w).1 hw
  have h1 := hb x1 ((ai_mem_V3plus_iff _).2 (by decide))
  have h2 := hb x2 ((ai_mem_V3plus_iff _).2 (by decide))
  have h6 := hb x6 ((ai_mem_V3plus_iff _).2 (by decide))
  exact (by decide +kernel : ∀ w : V6, w 2 = 0 → w 3 = 0 → w 4 = 0 → bil w x1 = 0 →
    bil w x2 = 0 → bil w x6 = 0 → w = 0) w hW.1 hW.2.1 hW.2.2 h1 h2 h6

theorem ai_linearIndependent_of_dual {n : ℕ} (v : Fin n → V6) (p : Fin n → Fin 6)
    (h : ∀ i j, v j (p i) = if i = j then 1 else 0) : LinearIndependent (ZMod 3) v := by
  refine LinearIndependent.of_comp (LinearMap.pi fun i => LinearMap.proj (R := ZMod 3)
    (φ := fun _ : Fin 6 => ZMod 3) (p i)) ?_
  have : ((LinearMap.pi fun i => LinearMap.proj (R := ZMod 3)
      (φ := fun _ : Fin 6 => ZMod 3) (p i)) ∘ v : Fin n → (Fin n → ZMod 3)) =
      Pi.basisFun (ZMod 3) (Fin n) := by
    funext j i
    simp [h, Pi.basisFun_apply, Pi.single_apply]
  rw [this]
  exact (Pi.basisFun (ZMod 3) (Fin n)).linearIndependent

theorem finrank_V3plus : Module.finrank (ZMod 3) V3plus = 3 := by
  have hli : LinearIndependent (ZMod 3) ![x1, x2, x6] :=
    ai_linearIndependent_of_dual _ ![0, 1, 5] (by decide)
  have h := finrank_span_eq_card hli
  have hr : Set.range ![x1, x2, x6] = {x1, x2, x6} := by
    ext w
    simp [Fin.exists_fin_succ, eq_comm]
    tauto
  rw [hr] at h
  exact h

theorem det_gram_V3plus :
    Matrix.det (Matrix.of fun i j : Fin 3 => bil (![x1, x2, x6] i) (![x1, x2, x6] j)) = 1 := by
  decide +kernel

theorem ai_spn_neg (w : V6) : spn {-w} = spn {w} := by
  have := mono_spn_smul (c := (-1 : ZMod 3)) (by decide) w
  rwa [neg_one_smul] at this

theorem ai_V3_vectors : ∀ v : V6, v 2 = 0 → v 3 = 0 → v 4 = 0 → qV v = -1 →
    v = x1 + x2 ∨ v = -(x1 + x2) ∨ v = x1 - x2 ∨ v = -(x1 - x2) ∨ v = x6 ∨ v = -x6 := by
  decide +kernel

theorem DeltaDotH_eq : DeltaDotH =
    {S : PtX | S.1 = spn {x6} ∨ S.1 = spn {x1 - x2} ∨ S.1 = spn {x1 + x2}} := by
  ext S
  obtain ⟨S, v, hv, rfl⟩ := S
  show spn {v} ≤ V3plus ↔ spn {v} = spn {x6} ∨ spn {v} = spn {x1 - x2} ∨ spn {v} = spn {x1 + x2}
  constructor
  · intro h
    have hvV : v ∈ V3plus := h (Submodule.mem_span_singleton_self v)
    obtain ⟨h2, h3, h4⟩ := (ai_mem_V3plus_iff v).1 hvV
    rcases ai_V3_vectors v h2 h3 h4 hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inr (ai_spn_neg _))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl (ai_spn_neg _))
    · exact Or.inl rfl
    · exact Or.inl (ai_spn_neg _)
  · have hx6 : x6 ∈ V3plus := (ai_mem_V3plus_iff _).2 (by decide)
    have hd : x1 - x2 ∈ V3plus := (ai_mem_V3plus_iff _).2 (by decide)
    have hs : x1 + x2 ∈ V3plus := (ai_mem_V3plus_iff _).2 (by decide)
    rintro (h | h | h) <;> rw [h] <;> refine Submodule.span_le.2 ?_ <;>
      intro w hw <;> rw [Set.mem_singleton_iff] at hw <;> subst hw <;> assumption

@[expose] def aiFr : Fin 6 → V6 := ![x1 + x2, x1 - x2, x3, x4, x5, x6]

theorem aiFr_ne_zero : ∀ j : Fin 6, aiFr j ≠ 0 := by decide

theorem ai_scalar_ne_zero {h : GL6} {v : V6} {c : ZMod 3}
    (hc : (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = c • v) (hv : v ≠ 0) : c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hc
  exact hv (mono_mulVec_inj h (hc.trans (Matrix.mulVec_zero _).symm))

@[expose] def aiFrStab : Subgroup GL6 where
  carrier := {g | ∀ j : Fin 6, ∃ c : ZMod 3,
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j = c • aiFr j}
  mul_mem' := by
    intro g h hg hh j
    obtain ⟨c, hc⟩ := hg j
    obtain ⟨d, hd⟩ := hh j
    refine ⟨d * c, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_smul, hc, smul_smul]
  one_mem' := fun j => ⟨1, by simp⟩
  inv_mem' := by
    intro g hg j
    obtain ⟨c, hc⟩ := hg j
    have hc0 : c ≠ 0 := ai_scalar_ne_zero hc (aiFr_ne_zero j)
    refine ⟨c⁻¹, ?_⟩
    have h1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (c⁻¹ • aiFr j) = aiFr j := by
      rw [Matrix.mulVec_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    conv_lhs => rw [← h1]
    exact mono_inv_mulVec g _

theorem ai_mem_FrStab {g : GL6} :
    g ∈ aiFrStab ↔ ∀ j : Fin 6, ∃ c : ZMod 3,
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j = c • aiFr j := Iff.rfl

theorem ai_fDot_mem_FrStab : fDot ∈ aiFrStab := by
  rw [ai_mem_FrStab]
  decide +kernel

theorem ai_eJ_mem_FrStab : ∀ J : Finset (Fin 6), ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J) →
    eJ J ∈ aiFrStab := by
  have : ∀ J : Finset (Fin 6), ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J) → ∀ j : Fin 6, ∃ c : ZMod 3,
      ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j = c • aiFr j := by
    decide +kernel
  exact fun J hJ => ai_mem_FrStab.2 (this J hJ)

theorem ai_ADot_M2Dot_le_FrStab : ADot M2Dot ≤ aiFrStab := by
  rw [ADot_M2Dot_eq]
  refine sup_le (Subgroup.zpowers_le.2 ai_fDot_mem_FrStab) ?_
  intro x hx
  have hx' : x ∈ ((Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) :
      Set GL6) := hx
  rw [Q2Dot_inf_centralizer_coe] at hx'
  obtain ⟨J, hJ, hev, h01, rfl⟩ := hx'
  exact ai_eJ_mem_FrStab J h01

theorem ai_eJ_mem_A {J : Finset (Fin 6)} (hJ : J ⊆ Iset) (hev : Even J.card)
    (h01 : (0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J) : eJ J ∈ ADot M2Dot := by
  rw [ADot_M2Dot_eq]
  exact Subgroup.mem_sup_right ⟨mono_eJ_mem_Q2Dot hJ hev,
    Subgroup.mem_centralizer_singleton_iff.2 ((ai_eJ_comm_iff J).2 h01)⟩

theorem ai_fDot_mem_A : fDot ∈ ADot M2Dot := by
  rw [ADot_M2Dot_eq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem ai_eigen_frame : ∀ v : V6,
    (∃ c : ZMod 3, ((fDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = c • v) →
    (∃ c : ZMod 3, ((eJ {0, 1} : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = c • v) →
    (∃ c : ZMod 3, ((eJ {2, 3} : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = c • v) →
    (∃ c : ZMod 3, ((eJ {2, 4} : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = c • v) →
    qV v = -1 →
    v = x1 + x2 ∨ v = -(x1 + x2) ∨ v = x1 - x2 ∨ v = -(x1 - x2) ∨ v = x6 ∨ v = -x6 := by
  decide +kernel

theorem ai_normalizer_eigen
    {n : GL6} (hn : n ∈ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6)) {v : V6}
    (hv : ∀ a ∈ ADot M2Dot, ∃ c : ZMod 3, (a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = c • v) :
    ∀ a ∈ ADot M2Dot, ∃ c : ZMod 3,
      (a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((n : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) =
        c • ((n : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) := by
  intro a ha
  have hn' : n⁻¹ ∈ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6) :=
    Subgroup.inv_mem _ hn
  have ha' : n⁻¹ * a * (n⁻¹)⁻¹ ∈ ADot M2Dot := (Subgroup.mem_normalizer_iff.1 hn' a).1 ha
  obtain ⟨c, hc⟩ := hv _ ha'
  refine ⟨c, ?_⟩
  have e : n * (n⁻¹ * a * (n⁻¹)⁻¹) = a * n := by group
  have h1 : (a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((n : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) =
      ((n * (n⁻¹ * a * (n⁻¹)⁻¹) : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v := by
    rw [e, Units.val_mul, Matrix.mulVec_mulVec]
  rw [h1, Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]

theorem ai_N_maps {n : GL6} (hnM : n ∈ MDot)
    (hn : n ∈ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6)) :
    ∀ v ∈ V3plus, n • v ∈ V3plus := by
  have hy : ∀ j : Fin 6, (j = 0 ∨ j = 1 ∨ j = 5) →
      (n : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j ∈ V3plus := by
    intro j hj
    have heig' := ai_normalizer_eigen hn (fun a ha => ai_ADot_M2Dot_le_FrStab ha j)
    have hq : qV ((n : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j) = -1 := by
      rw [qV_mulVec_of_mem_OVq (MDot_le_OVq hnM)]
      rcases hj with rfl | rfl | rfl <;> decide
    have key := ai_eigen_frame _ (heig' fDot ai_fDot_mem_A)
      (heig' (eJ {0, 1}) (ai_eJ_mem_A (by decide) (by decide) (by decide)))
      (heig' (eJ {2, 3}) (ai_eJ_mem_A (by decide) (by decide) (by decide)))
      (heig' (eJ {2, 4}) (ai_eJ_mem_A (by decide) (by decide) (by decide))) hq
    rcases key with h | h | h | h | h | h <;> rw [h] <;> exact (ai_mem_V3plus_iff _).2 (by decide)
  intro v hv
  have hv' := (ai_mem_V3plus_iff v).1 hv
  have key : ∀ w : V6, w 2 = 0 → w 3 = 0 → w 4 = 0 →
      w = (2 * (w 0 + w 1)) • (x1 + x2) + (2 * (w 0 - w 1)) • (x1 - x2) + w 5 • x6 := by
    decide +kernel
  rw [quat_smul_def, key v hv'.1 hv'.2.1 hv'.2.2, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
  exact add_mem (add_mem (Submodule.smul_mem _ _ (hy 0 (by decide)))
    (Submodule.smul_mem _ _ (hy 1 (by decide)))) (Submodule.smul_mem _ _ (hy 5 (by decide)))

theorem ai_of_pm {v w : V6} (h : v = w ∨ v = -w) : ∃ s : ZMod 3, v = s • w := by
  rcases h with rfl | rfl
  · exact ⟨1, (one_smul _ _).symm⟩
  · exact ⟨-1, (neg_one_smul _ _).symm⟩

theorem ai_U_vectors : ∀ v : V6, v 0 = 0 → v 1 = 0 → v 5 = 0 → qV v = 1 →
    v = x3 ∨ v = -x3 ∨ v = x4 ∨ v = -x4 ∨ v = x5 ∨ v = -x5 := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem ai_orth_V3 : ∀ u : V6, u 2 = 0 → u 3 = 0 → u 4 = 0 → ∀ i : Fin 6,
    (i = 2 ∨ i = 3 ∨ i = 4) → bil (aiFr i) u = 0 := by
  decide +kernel

theorem ai_coords_of_orth : ∀ v : V6, bil v x1 = 0 → bil v x2 = 0 → bil v x6 = 0 →
    v 0 = 0 ∧ v 1 = 0 ∧ v 5 = 0 := by
  decide +kernel

theorem ai_pm_frame {v : V6} (hv : v ∈ V3plus) (hq : qV v = -1) :
    ∃ s : ZMod 3, ∃ k : Fin 6, v = s • aiFr k := by
  obtain ⟨h2, h3, h4⟩ := (ai_mem_V3plus_iff _).1 hv
  rcases ai_V3_vectors v h2 h3 h4 hq with h | h | h | h | h | h
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inl h : v = aiFr 0 ∨ v = -aiFr 0)
    exact ⟨s, 0, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inr h : v = aiFr 0 ∨ v = -aiFr 0)
    exact ⟨s, 0, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inl h : v = aiFr 1 ∨ v = -aiFr 1)
    exact ⟨s, 1, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inr h : v = aiFr 1 ∨ v = -aiFr 1)
    exact ⟨s, 1, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inl h : v = aiFr 5 ∨ v = -aiFr 5)
    exact ⟨s, 5, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inr h : v = aiFr 5 ∨ v = -aiFr 5)
    exact ⟨s, 5, hs⟩

theorem ai_pm_frame_pos {v : V6} (h0 : v 0 = 0) (h1 : v 1 = 0) (h5 : v 5 = 0) (hq : qV v = 1) :
    ∃ s : ZMod 3, ∃ k : Fin 6, v = s • aiFr k := by
  rcases ai_U_vectors v h0 h1 h5 hq with h | h | h | h | h | h
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inl h : v = aiFr 2 ∨ v = -aiFr 2)
    exact ⟨s, 2, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inr h : v = aiFr 2 ∨ v = -aiFr 2)
    exact ⟨s, 2, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inl h : v = aiFr 3 ∨ v = -aiFr 3)
    exact ⟨s, 3, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inr h : v = aiFr 3 ∨ v = -aiFr 3)
    exact ⟨s, 3, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inl h : v = aiFr 4 ∨ v = -aiFr 4)
    exact ⟨s, 4, hs⟩
  · obtain ⟨s, hs⟩ := ai_of_pm (Or.inr h : v = aiFr 4 ∨ v = -aiFr 4)
    exact ⟨s, 4, hs⟩

theorem ai_frame_perm {g : GL6} (hg : g ∈ OVq) (hstab : ∀ v : V6, v ∈ V3plus ↔ g • v ∈ V3plus)
    (j : Fin 6) : ∃ s : ZMod 3, ∃ k : Fin 6,
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j = s • aiFr k := by
  have hgv : ∀ v : V6, v ∈ V3plus → (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v ∈ V3plus :=
    fun v hv => (hstab v).1 hv
  have hgi : ∀ w : V6, w ∈ V3plus →
      ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w ∈ V3plus := by
    intro w hw
    refine (hstab _).2 ?_
    show (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w) ∈ V3plus
    rw [mono_mulVec_inv]
    exact hw
  by_cases hj : j = 0 ∨ j = 1 ∨ j = 5
  · have hmem : aiFr j ∈ V3plus := by
      rcases hj with rfl | rfl | rfl <;> exact (ai_mem_V3plus_iff _).2 (by decide)
    have hq : qV ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j) = -1 := by
      rw [qV_mulVec_of_mem_OVq hg]
      rcases hj with rfl | rfl | rfl <;> decide
    exact ai_pm_frame (hgv _ hmem) hq
  · have hjs : j = 2 ∨ j = 3 ∨ j = 4 := by
      revert hj
      fin_cases j <;> simp
    have horth : ∀ w ∈ V3plus,
        bil ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j) w = 0 := by
      intro w hw
      have hw'' := (ai_mem_V3plus_iff _).1 (hgi w hw)
      calc bil ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j) w
          = bil ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j)
              ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
                (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w)) := by
            rw [mono_mulVec_inv]
        _ = bil (aiFr j) (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w) :=
            bil_mulVec_of_mem_OVq hg _ _
        _ = 0 := ai_orth_V3 _ hw''.1 hw''.2.1 hw''.2.2 j hjs
    have hc := ai_coords_of_orth _ (horth x1 ((ai_mem_V3plus_iff _).2 (by decide)))
      (horth x2 ((ai_mem_V3plus_iff _).2 (by decide)))
      (horth x6 ((ai_mem_V3plus_iff _).2 (by decide)))
    have hq : qV ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j) = 1 := by
      rw [qV_mulVec_of_mem_OVq hg]
      rcases hjs with rfl | rfl | rfl <;> decide
    exact ai_pm_frame_pos hc.1 hc.2.1 hc.2.2 hq

theorem ai_ADot_M2Dot_le_MDot : ADot M2Dot ≤ MDot :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_left.trans inf_le_left)

theorem ai_case_eq {h : GL6} (hM : h ∈ MDot) (hst : h ∈ aiFrStab) {c : ZMod 3}
    (h0 : (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr 0 = c • aiFr 0)
    (h1 : (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr 1 = c • aiFr 1) :
    h ∈ Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  have e1 : x1 = (2 : ZMod 3) • (aiFr 0 + aiFr 1) := by decide
  have e2 : x2 = (2 : ZMod 3) • (aiFr 0 - aiFr 1) := by decide
  have hx1 : (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec 0 = c • xvec 0 := by
    show (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x1 = c • x1
    rw [e1, Matrix.mulVec_smul, Matrix.mulVec_add, h0, h1]
    module
  have hx2 : (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec 1 = c • xvec 1 := by
    show (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x2 = c • x2
    rw [e2, Matrix.mulVec_smul, Matrix.mulVec_sub, h0, h1]
    module
  have hdiag : ∀ i : Fin 6, ∃ c : ZMod 3,
      (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ xvec i = c • xvec i := by
    intro i
    fin_cases i
    · exact ⟨c, hx1⟩
    · exact ⟨c, hx2⟩
    · exact hst 2
    · exact hst 3
    · exact hst 4
    · exact hst 5
  obtain ⟨J, rfl⟩ := mono_eq_eJ_of_diag (MDot_le_OVq hM) hdiag
  have a0 : eJd J 0 = c := by
    have := congrFun ((mono_eJ_mulVec_xvec J 0).symm.trans hx1) 0
    simpa [mono_xvec_apply] using this
  have a1 : eJd J 1 = c := by
    have := congrFun ((mono_eJ_mulVec_xvec J 1).symm.trans hx2) 1
    simpa [mono_xvec_apply] using this
  have h01 : (0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J := by
    have := a0.trans a1.symm
    rw [mono_eJd_apply, mono_eJd_apply] at this
    by_cases h0J : (0 : Fin 6) ∈ J <;> by_cases h1J : (1 : Fin 6) ∈ J <;>
      simp only [h0J, h1J, if_true, if_false] at this ⊢ <;>
      first | exact absurd this (by decide) | simp
  exact ⟨(mono_mem_Q2Dot_iff _).2 ⟨hM, J, rfl⟩,
    Subgroup.mem_centralizer_singleton_iff.2 ((ai_eJ_comm_iff J).2 h01)⟩

theorem ai_frame_mem_A {h : GL6} (hM : h ∈ MDot) (hst : h ∈ aiFrStab) : h ∈ ADot M2Dot := by
  obtain ⟨c0, hc0⟩ := hst 0
  obtain ⟨c1, hc1⟩ := hst 1
  have hnz0 : c0 ≠ 0 := ai_scalar_ne_zero hc0 (aiFr_ne_zero 0)
  have hnz1 : c1 ≠ 0 := ai_scalar_ne_zero hc1 (aiFr_ne_zero 1)
  by_cases hcc : c0 = c1
  · subst hcc
    rw [ADot_M2Dot_eq]
    exact Subgroup.mem_sup_right (ai_case_eq hM hst hc0 hc1)
  · have hM' : fDot * h ∈ MDot := MDot.mul_mem fDot_mem_MDot hM
    have hst' : fDot * h ∈ aiFrStab := aiFrStab.mul_mem ai_fDot_mem_FrStab hst
    have hneg : -c1 = c0 := by
      have key : ∀ c0 c1 : ZMod 3, c0 ≠ 0 → c1 ≠ 0 → c0 ≠ c1 → -c1 = c0 := by decide
      exact key c0 c1 hnz0 hnz1 hcc
    have h0' : ((fDot * h : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr 0 = c0 • aiFr 0 := by
      have hf0 : ((fDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr 0 = aiFr 0 := by decide
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hc0, Matrix.mulVec_smul, hf0]
    have h1' : ((fDot * h : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr 1 = c0 • aiFr 1 := by
      have hf1 : ((fDot : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr 1 = -aiFr 1 := by decide
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hc1, Matrix.mulVec_smul, hf1, ← hneg]
      module
    have hmem := ai_case_eq hM' hst' h0' h1'
    have hA : fDot * (fDot * h) ∈ ADot M2Dot := by
      refine (ADot M2Dot).mul_mem ai_fDot_mem_A ?_
      rw [ADot_M2Dot_eq]
      exact Subgroup.mem_sup_right hmem
    rwa [← mul_assoc, mono_fDot_mul_self, one_mul] at hA

theorem ai_conj_mem {g : GL6} (hg : g ∈ MDot ⊓ MulAction.stabilizer GL6 V3plus) {a : GL6}
    (ha : a ∈ ADot M2Dot) : g * a * g⁻¹ ∈ ADot M2Dot := by
  obtain ⟨hgM, hgs⟩ := hg
  have hs' := (quat_mem_stabilizer_iff g⁻¹ V3plus).1
    ((MulAction.stabilizer GL6 V3plus).inv_mem hgs)
  have hgM' : g⁻¹ ∈ MDot := MDot.inv_mem hgM
  refine ai_frame_mem_A (MDot.mul_mem (MDot.mul_mem hgM (ai_ADot_M2Dot_le_MDot ha)) hgM') ?_
  intro j
  obtain ⟨s, k, hk⟩ := ai_frame_perm (MDot_le_OVq hgM') hs' j
  obtain ⟨c, hc⟩ := ai_ADot_M2Dot_le_FrStab ha k
  refine ⟨c, ?_⟩
  calc ((g * a * g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j
      = (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
          (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ aiFr j)) := by
        rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
          (s • aiFr k)) := by rw [hk]
    _ = (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (s • (c • aiFr k)) := by
        rw [Matrix.mulVec_smul, hc]
    _ = c • ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (s • aiFr k)) := by
        rw [smul_comm, Matrix.mulVec_smul]
    _ = c • aiFr j := by rw [← hk, mono_mulVec_inv]

theorem MDot_inf_stab_V3plus_eq : MDot ⊓ MulAction.stabilizer GL6 V3plus =
    MDot ⊓ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6) := by
  ext g
  constructor
  · intro hg
    refine ⟨hg.1, mono_mem_normalizer_of_conj (fun s hs => ai_conj_mem hg hs)
      (fun s hs => ?_)⟩
    have hg' : g⁻¹ ∈ MDot ⊓ MulAction.stabilizer GL6 V3plus := (MDot ⊓ _).inv_mem hg
    have := ai_conj_mem hg' hs
    rwa [inv_inv] at this
  · rintro ⟨hgM, hn⟩
    refine ⟨hgM, (quat_mem_stabilizer_iff g V3plus).2 fun v =>
      ⟨fun hv => ai_N_maps hgM hn v hv, fun hv => ?_⟩⟩
    have := ai_N_maps (MDot.inv_mem hgM) (Subgroup.inv_mem _ hn) _ hv
    rwa [inv_smul_smul] at this

theorem f57Model :
    (IsNondegSub V3plus ∧ Module.finrank (ZMod 3) V3plus = 3 ∧
      Matrix.det (Matrix.of fun i j : Fin 3 => bil (![x1, x2, x6] i) (![x1, x2, x6] j)) = 1 ∧
      DeltaDotH = {S : PtX | S.1 = spn {x6} ∨ S.1 = spn {x1 - x2} ∨ S.1 = spn {x1 + x2}} ∧
      MDot ⊓ MulAction.stabilizer GL6 V3plus =
        MDot ⊓ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6)) :=
  ⟨isNondegSub_V3plus, finrank_V3plus, det_gram_V3plus, DeltaDotH_eq, MDot_inf_stab_V3plus_eq⟩

theorem f53Model_of_inv
    (h4 : (∀ w : GL6, w ∈ MDot → w ≠ 1 → w * w = 1 →
        ((∃ g ∈ MDot, g * zDot * g⁻¹ = w) ↔
          (Module.finrank (ZMod 3) (commSp w) = 4 ∧ SignPlus (commSp w))) ∧
        ((∃ g ∈ MDot, g * fDot * g⁻¹ = w) ↔
          (Module.finrank (ZMod 3) (commSp w) = 2 ∧ SignMinus (commSp w))) ∧
        ((∃ g ∈ MDot, g * zDot * g⁻¹ = w) ∨ (∃ g ∈ MDot, g * fDot * g⁻¹ = w))) ∧
      ¬ ∃ g ∈ MDot, g * zDot * g⁻¹ = fDot) : F53Model :=
  ⟨fun Mi hMi => EDot_structure Mi hMi, ADot_part1, Q2Dot_inf_centralizer_coe,
    Q1Dot_inf_centralizer_nonid, h4, commutator_Q2Dot_fDot, tDot_ne_one⟩

end

end CFSG.Quasithin.SimsF5
