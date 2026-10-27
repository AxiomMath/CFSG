module

public import CFSG.RankThree.GF2n.Tim78S42
public import CFSG.RankThree.GF2n.Tim78S48PhaseGen
import CFSG.RankThree.GF2n.Tim78S48PairQuot
import CFSG.RankThree.PartOne.FTL.Frattini
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Cert43


theorem frattini_T_eq : frattini ↥T = B.subgroupOf T := by
  have h := H.frattini_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T
  ext x
  rw [Subgroup.mem_subgroupOf, ← h]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]

theorem acts_trivially_of_trivial_mod_B {m : G} (hm : m ∈ M) {d : ℕ} (hd : Odd d)
    (hmd : m ^ d = 1) (htriv : ∀ t ∈ T, ⁅m, t⁆ ∈ B) : ∀ t ∈ T, m * t * m⁻¹ = t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmT : m ∈ Subgroup.normalizer (T : Set G) := H.M_le_normalizer_T hm
  let τ : MulAut ↥T := T.normalizerMonoidHom ⟨m, hmT⟩
  have hτ : ∀ t : ↥T, ((τ t : ↥T) : G) = m * t * m⁻¹ := fun _ => rfl
  have hτd : τ ^ d = 1 := by
    have : (⟨m, hmT⟩ : ↥(Subgroup.normalizer (T : Set G))) ^ d = 1 :=
      Subtype.ext (by simpa using hmd)
    rw [← map_pow, this, map_one]
  have hP2 : IsPGroup 2 ↥T := H.isPGroup_Q.to_le H.T_le_Q
  have hcop : Nat.Coprime d 2 := Nat.coprime_two_right.mpr hd
  have hfrat := H.frattini_T_eq
  have htr : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥T) τ =
      1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
    show CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥T) τ
      (QuotientGroup.mk' (frattini ↥T) t) = QuotientGroup.mk' (frattini ↥T) t
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hfrat,
      Subgroup.mem_subgroupOf]
    have htM : (t : G) ∈ M := H.T_le_Q.trans H.Q_le_M t.2
    have h1 := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B (M.inv_mem htM))
      ⁅m, (t : G)⁆⁻¹).mp (B.inv_mem (htriv t t.2))
    have e : ((((τ t)⁻¹ * t : ↥T)) : G) = (t : G)⁻¹ * ⁅m, (t : G)⁆⁻¹ * ((t : G)⁻¹)⁻¹ := by
      simp [hτ, commutatorElement_def, mul_assoc]
    rw [e]
    exact h1
  have := CFSG.RankThree.PartOne.FTL.eq_one_of_trivial_mod_frattini hP2 hτd hcop htr
  intro t ht
  have := congrArg (fun f : MulAut ↥T => ((f ⟨t, ht⟩ : ↥T) : G)) this
  simpa [hτ] using this

theorem cartan_on_quotient :
    Nat.card B ≤ B.relIndex T ∧
    (Nat.card B = B.relIndex T →
      ∀ x ∈ T, ∀ y ∈ T, x ∉ B → y ∉ B → ∃ m ∈ M, y⁻¹ * (m * x * m⁻¹) ∈ B) := by
  classical
  obtain ⟨-, -, -, k, hkM, hko, hkreg⟩ := H.base_facts
  have hBM : B ≤ M := H.B_le_M
  haveI hnorm : (B.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBM).mpr H.M_le_normalizer_B
  set π := QuotientGroup.mk' (B.subgroupOf M) with hπ
  have hTM : T ≤ M := H.T_le_Q.trans H.Q_le_M
  set Ω : Subgroup (↥M ⧸ B.subgroupOf M) := (T.subgroupOf M).map π with hΩ
  set kk : ↥M ⧸ B.subgroupOf M := π ⟨k, hkM⟩ with hkk
  set Hc : Subgroup (↥M ⧸ B.subgroupOf M) := Subgroup.zpowers kk with hHc
  have hmem : ∀ y : ↥M, π y = 1 ↔ (y : G) ∈ B := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hΩcard : Nat.card Ω = B.relIndex T := by
    have h := relIndex_eq_card_map_mk (G := G) (X := M) (N := B) (S := T) hTM
    rw [inf_of_le_right H.B_le_T] at h
    exact h.symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp H.isPGroup_B
  have hq4 := H.q4
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hq1odd : Odd (Nat.card B - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' hn0).mpr even_two) odd_one |> fun h => by
      rw [hn]; exact h
  have hkpow : k ^ (Nat.card B - 1) = 1 := by rw [← hko]; exact pow_orderOf_eq_one k
  have hkB : ∀ i : ℕ, k ^ i ∈ B → k ^ i = 1 := by
    intro i hi
    have h2 : (k ^ i) ^ 2 = 1 := H.sq_eq_one _ hi
    have h3 : (k ^ i) ^ (Nat.card B - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hkpow, one_pow]
    have hcop : Nat.Coprime 2 (Nat.card B - 1) := Nat.coprime_two_left.mpr hq1odd
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rw [hcop.gcd_eq_one, Nat.dvd_one] at hd
    exact orderOf_eq_one_iff.mp hd
  have hkkpow : ∀ i : ℕ, kk ^ i = π ⟨k ^ i, pow_mem hkM i⟩ := fun i => by
    rw [hkk, ← map_pow]; rfl
  have hkk_eq_one : ∀ i : ℕ, kk ^ i = 1 ↔ k ^ i = 1 := fun i => by
    rw [hkkpow, hmem]
    exact ⟨hkB i, fun h => by show k ^ i ∈ B; rw [h]; exact B.one_mem⟩
  have hkkord : orderOf kk = Nat.card B - 1 := by
    rw [orderOf_eq_iff (by omega)]
    refine ⟨(hkk_eq_one _).mpr hkpow, fun m hm hm0 => ?_⟩
    rw [Ne, hkk_eq_one]
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hko] at this
    exact absurd (Nat.le_of_dvd hm0 this) (not_le.mpr hm)
  have hHccard : Nat.card Hc = Nat.card B - 1 := by rw [hHc, Nat.card_zpowers, hkkord]
  have hTMmem : ∀ t ∈ T, t ∈ M := fun t ht => hTM ht
  have hΩmem : ∀ t : G, ∀ ht : t ∈ T, π ⟨t, hTM ht⟩ ∈ Ω := fun t ht =>
    ⟨⟨t, hTM ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hΩe : Assembly.IsElemAbelian 2 Ω := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      show (a : ↥M ⧸ B.subgroupOf M) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 := H.commutator_mem (Q.inv_mem (H.T_le_Q (Subgroup.mem_subgroupOf.mp hb')))
        (Q.inv_mem (H.T_le_Q (Subgroup.mem_subgroupOf.mp ha')))
      have e : (((a' * b')⁻¹ * (b' * a') : ↥M) : G) =
          ⁅((b' : ↥M) : G)⁻¹, ((a' : ↥M) : G)⁻¹⁆ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact h1
    · obtain ⟨x', hx', rfl⟩ := hx
      rw [← map_pow, hmem]
      exact H.sq_mem (H.T_le_Q (Subgroup.mem_subgroupOf.mp hx'))
  have hrel : B.relIndex T ≠ 1 := by
    intro h1
    exact H.B_ne_T (le_antisymm H.B_le_T (Subgroup.relIndex_eq_one.mp h1))
  have hΩne : Ω ≠ ⊥ := by
    intro h
    apply hrel
    rw [← hΩcard, h, Subgroup.card_bot]
  have hHcnorm : Hc ≤ Subgroup.normalizer (Ω : Set (↥M ⧸ B.subgroupOf M)) := by
    rw [hHc, Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨a', ha', rfl⟩ := hx
    refine ⟨⟨k, hkM⟩ * a' * ⟨k, hkM⟩⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      have := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_T hkM) (a' : G)).mp
        (Subgroup.mem_subgroupOf.mp ha')
      simpa using this
    · rw [hkk, map_mul, map_mul, map_inv]
  have hHcc : ∀ a ∈ Hc, ∀ b ∈ Hc, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self kk i j).eq
  have hHcodd : Odd (Nat.card Hc) := by rw [hHccard]; exact hq1odd
  have hfaith : ∀ h ∈ Hc, (∀ x ∈ Ω, h * x * h⁻¹ = x) → h = 1 := by
    intro h hh hcomm
    have hh' : h ∈ Submonoid.powers kk := mem_powers_iff_mem_zpowers.mpr hh
    obtain ⟨j, rfl⟩ := hh'
    have hkjM : k ^ j ∈ M := pow_mem hkM j
    have hmd : (k ^ j) ^ (Nat.card B - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hkpow, one_pow]
    have htriv : ∀ t ∈ T, ⁅k ^ j, t⁆ ∈ B := by
      intro t ht
      have htM : t⁻¹ ∈ M := hTM (T.inv_mem ht)
      have h1 := hcomm (π ⟨t⁻¹, htM⟩) (hΩmem _ (T.inv_mem ht))
      simp only at h1
      rw [hkkpow j, ← map_inv, ← map_mul, ← map_mul] at h1
      have h2 : (QuotientGroup.mk (⟨k ^ j, hkjM⟩ * ⟨t⁻¹, htM⟩ * ⟨k ^ j, hkjM⟩⁻¹ : ↥M) :
          ↥M ⧸ B.subgroupOf M) = QuotientGroup.mk ⟨t⁻¹, htM⟩ := h1
      have h3 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h2)
      have e : ((((⟨k ^ j, hkjM⟩ * ⟨t⁻¹, htM⟩ * ⟨k ^ j, hkjM⟩⁻¹ : ↥M)⁻¹ * ⟨t⁻¹, htM⟩ : ↥M)) : G) =
          ⁅k ^ j, t⁆ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e] at h3
      exact h3
    have htrivact := H.acts_trivially_of_trivial_mod_B hkjM hq1odd hmd htriv
    have hkj1 : k ^ j = 1 := by
      by_contra hne
      have hi : j % (Nat.card B - 1) ≠ 0 := by
        intro h0
        apply hne
        rw [← pow_mod_orderOf, hko, h0, pow_zero]
      have hlt : j % (Nat.card B - 1) < Nat.card B - 1 := Nat.mod_lt _ (by omega)
      obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp H.B_ne_bot
      apply hb1
      have hcb : k ^ (j % (Nat.card B - 1)) * b = b * k ^ (j % (Nat.card B - 1)) := by
        have e : k ^ (j % (Nat.card B - 1)) = k ^ j := by
          rw [← hko]; exact pow_mod_orderOf k j
        rw [e]
        have := htrivact b (H.B_le_T hb)
        calc k ^ j * b = (k ^ j * b * (k ^ j)⁻¹) * k ^ j := by group
          _ = b * k ^ j := by rw [this]
      exact Subtype.ext (hkreg _ (Nat.pos_of_ne_zero hi) hlt b hb hcb)
    exact (hkk_eq_one j).mpr hkj1
  rcases tim78_2_5_sub hHcc hHcodd hΩe hΩne hHcnorm hfaith with hlt | ⟨heq, htr⟩
  · rw [hHccard, hΩcard] at hlt
    exact ⟨by omega, fun h => by omega⟩
  · rw [hHccard, hΩcard] at heq
    refine ⟨by omega, fun _ x hx y hy hxB hyB => ?_⟩
    have hxM : x ∈ M := hTM hx
    have hyM : y ∈ M := hTM hy
    obtain ⟨h, hh, h1⟩ := htr (π ⟨x, hxM⟩) (hΩmem x hx) (π ⟨y, hyM⟩) (hΩmem y hy)
      (fun h => hxB ((hmem _).mp h)) (fun h => hyB ((hmem _).mp h))
    have hh' : h ∈ Submonoid.powers kk := mem_powers_iff_mem_zpowers.mpr hh
    obtain ⟨j, rfl⟩ := hh'
    have hkjM : k ^ j ∈ M := pow_mem hkM j
    simp only at h1
    rw [hkkpow j, ← map_inv, ← map_mul, ← map_mul] at h1
    have h2 : (QuotientGroup.mk (⟨k ^ j, hkjM⟩ * ⟨x, hxM⟩ * ⟨k ^ j, hkjM⟩⁻¹ : ↥M) :
        ↥M ⧸ B.subgroupOf M) = QuotientGroup.mk ⟨y, hyM⟩ := h1
    have h3 := B.inv_mem (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h2))
    refine ⟨k ^ j, hkjM, ?_⟩
    simpa [mul_assoc] using h3

theorem eq_B_of_normal_comm {N : Subgroup G} (hBN : B ≤ N) (hNT : N ≤ T)
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : N = B := by
  by_contra hne
  exact H.not_comm_of_ne hBN (hNT.trans H.T_le_Q) hMN (Ne.symm hne) hN

theorem false_of_regular {x₀ : G} (hx₀T : x₀ ∈ T) (hx₀B : x₀ ∉ B) (hx₀2 : x₀ * x₀ = 1)
    (hreg : ∀ x ∈ T, ∀ y ∈ T, x ∉ B → y ∉ B → ∃ m ∈ M, y⁻¹ * (m * x * m⁻¹) ∈ B) : False := by
  have hsq : ∀ t ∈ T, t * t = 1 := by
    intro t ht
    by_cases htB : t ∈ B
    · rw [← sq]; exact H.sq_eq_one t htB
    · obtain ⟨m, hm, hb⟩ := hreg x₀ hx₀T t ht hx₀B htB
      have hmT : m ∈ Subgroup.normalizer (T : Set G) := H.M_le_normalizer_T hm
      have hu : m * x₀ * m⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hmT x₀).mp hx₀T
      have hu2 : (m * x₀ * m⁻¹) * (m * x₀ * m⁻¹) = 1 := by
        calc (m * x₀ * m⁻¹) * (m * x₀ * m⁻¹) = m * (x₀ * x₀) * m⁻¹ := by group
          _ = 1 := by rw [hx₀2]; group
      set b := t⁻¹ * (m * x₀ * m⁻¹) with hbdef
      have ht' : t = (m * x₀ * m⁻¹) * b⁻¹ := by rw [hbdef]; group
      have hbc : (m * x₀ * m⁻¹) * b⁻¹ = b⁻¹ * (m * x₀ * m⁻¹) := by
        have := H.T_comm_B hu (B.inv_mem hb)
        exact this
      have hb2 : b⁻¹ * b⁻¹ = 1 := by
        have := H.sq_eq_one b⁻¹ (B.inv_mem hb)
        rw [sq] at this; exact this
      calc t * t = ((m * x₀ * m⁻¹) * b⁻¹) * ((m * x₀ * m⁻¹) * b⁻¹) := by rw [← ht']
        _ = (m * x₀ * m⁻¹) * ((m * x₀ * m⁻¹) * b⁻¹) * b⁻¹ := by
          rw [mul_assoc, ← mul_assoc b⁻¹, ← hbc]; group
        _ = 1 := by rw [← mul_assoc, hu2, one_mul, hb2]
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    comm_of_mul_self_eq_one (hsq a ha) (hsq b hb) (hsq _ (T.mul_mem ha hb))
  have hTB : T ⊓ Subgroup.centralizer (T : Set G) = B :=
    H.inf_centralizer_eq_B H.B_le_T H.T_le_Q H.M_le_normalizer_T
  have : x₀ ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨hx₀T, Subgroup.mem_centralizer_iff.mpr fun h hh => (hcomm h hh x₀ hx₀T)⟩
  rw [hTB] at this
  exact hx₀B this

theorem false_of_index_two {T₀ : Subgroup G} (hBT₀ : B ≤ T₀) (hT₀T : T₀ ≤ T)
    (hT₀e : Assembly.IsElemAbelian 2 T₀) (hidx : T₀.relIndex T = 2) : False := by
  have hE1 := H.cartan_on_quotient
  have hq4 := H.q4
  have hT₀c : ∀ a ∈ T₀, ∀ b ∈ T₀, a * b = b * a := fun a ha b hb =>
    comm_of_isElemAbelian hT₀e ha hb
  by_cases hnorm : M ≤ Subgroup.normalizer (T₀ : Set G)
  · have hTB := H.eq_B_of_normal_comm hBT₀ hT₀T hnorm hT₀c
    rw [hTB] at hidx
    have := hE1.1
    rw [hidx] at this
    omega
  · obtain ⟨m, hmM, hm⟩ := SetLike.not_le_iff_exists.mp hnorm
    have hmT : m ∈ Subgroup.normalizer (T : Set G) := H.M_le_normalizer_T hmM
    set T₁ := conjSubgroup m T₀ with hT₁
    have hT₁ne : T₁ ≠ T₀ := fun h => hm (conjSubgroup_eq_self_iff.mp h)
    have hT₁T : T₁ ≤ T := by
      intro x hx
      rw [hT₁, mem_conjSubgroup] at hx
      have h1 := hT₀T hx
      have := (Subgroup.mem_normalizer_iff.mp hmT _).mp h1
      rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at this
    have hBT₁ : B ≤ T₁ := by
      intro b hb
      rw [hT₁, mem_conjSubgroup]
      refine hBT₀ ?_
      have := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B (M.inv_mem hmM)) b).mp hb
      simpa using this
    have hT₁e : Assembly.IsElemAbelian 2 T₁ := isElemAbelian_conjSubgroup hT₀e m
    have hT₁c : ∀ a ∈ T₁, ∀ b ∈ T₁, a * b = b * a := fun a ha b hb =>
      comm_of_isElemAbelian hT₁e ha hb
    have hcard₁ : Nat.card T₁ = Nat.card T₀ := card_conjSubgroup m T₀
    have hTcard₀ : T₀.relIndex T * Nat.card T₀ = Nat.card T := by
      have := Subgroup.relIndex_mul_card (H := T₀) (K := T)
      rwa [inf_of_le_left hT₀T] at this
    have hTcard₁ : T₁.relIndex T * Nat.card T₁ = Nat.card T := by
      have := Subgroup.relIndex_mul_card (H := T₁) (K := T)
      rwa [inf_of_le_left hT₁T] at this
    have hidx₁ : T₁.relIndex T = 2 := by
      rw [hcard₁] at hTcard₁
      have h := hTcard₁.trans hTcard₀.symm
      rw [hidx] at h
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
    have hsup : T₀ ⊔ T₁ = T := by
      set S := T₀ ⊔ T₁ with hS
      have hST : S ≤ T := sup_le hT₀T hT₁T
      have hd : S.relIndex T ∣ 2 := hidx ▸ Subgroup.relIndex_dvd_of_le_left T (le_sup_left : T₀ ≤ S)
      have hSTcard : S.relIndex T * Nat.card S = Nat.card T := by
        have := Subgroup.relIndex_mul_card (H := S) (K := T)
        rwa [inf_of_le_left hST] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · rw [h1, one_mul] at hSTcard
        exact Subgroup.eq_of_le_of_card_ge hST (by rw [hSTcard])
      · exfalso
        rw [h2, ← hidx] at hSTcard
        have hSc : Nat.card S = Nat.card T₀ :=
          Nat.eq_of_mul_eq_mul_left (by omega) (hSTcard.trans hTcard₀.symm)
        have hS0 : S = T₀ := (Subgroup.eq_of_le_of_card_ge (le_sup_left : T₀ ≤ S)
          (by rw [hSc])).symm
        have hT₁S : T₁ ≤ T₀ := hS0 ▸ (le_sup_right : T₁ ≤ S)
        exact hT₁ne (Subgroup.eq_of_le_of_card_ge hT₁S (by rw [hcard₁]))
    have hI : T₀ ⊓ T₁ = B := by
      refine le_antisymm (fun x hx => ?_) (le_inf hBT₀ hBT₁)
      have hcen : T ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [← hsup]
        refine sup_le (fun a ha => ?_) (fun a ha => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]; exact hT₀c a ha x hx.1
        · rw [Subgroup.mem_centralizer_singleton_iff]; exact hT₁c a ha x hx.2
      have hxT : x ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
        ⟨hT₀T hx.1, Subgroup.mem_centralizer_iff.mpr fun h hh =>
          Subgroup.mem_centralizer_singleton_iff.mp (hcen hh)⟩
      rwa [H.inf_centralizer_eq_B H.B_le_T H.T_le_Q H.M_le_normalizer_T] at hxT
    have hBidx : B.relIndex T ≤ 4 := by
      have := Subgroup.relIndex_inf_le (H := T₀) (K := T₁) (L := T)
      rw [hI, hidx, hidx₁] at this
      omega
    have hq : Nat.card B = B.relIndex T := by
      have := hE1.1
      omega
    have hBlt : B < T₀ := by
      refine lt_of_le_of_ne hBT₀ fun h => hnorm ?_
      rw [← h]
      exact H.M_le_normalizer_B
    obtain ⟨x₀, hx₀, hx₀B⟩ := SetLike.exists_of_lt hBlt
    exact H.false_of_regular (hT₀T hx₀) hx₀B
      (CFSG.Open.IsElemAbelian.mul_self_eq_one hT₀e hx₀) (hE1.2 hq)

end Cert43

end Hyp4

end CFSG.RankThree.GF2n.Tim78
