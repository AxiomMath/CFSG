module

public import CFSG.Quasithin.EmptyFaithful.A38c8Defs
public import CFSG.Quasithin.EmptyFaithful.A38c8L5Model
public import CFSG.Quasithin.Background.FLcLn
public import CFSG.Quasithin.Background.FLcSL
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem mem_pCore_iff_coe' {Y : Type*} [Group Y] {B : Subgroup Y} (x : ↥B) :
    x ∈ CFSG.pCore 2 ↥B ↔ (x : Y) ∈ pCoreOf 2 B := (CFSG.mem_openPCoreOf_iff x).symm

private theorem card_of_isPSL_four {X : Type} [Group X] (h : IsPSL 4 2 1 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

private theorem card_of_isPSL_five {X : Type} [Group X] (h : IsPSL 5 2 1 X) :
    Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h

section Transport

variable {Y : Type} [Group Y] {n : ℕ} {N T₀ B : Subgroup Y}

private noncomputable def modelEquiv (D : BorelIso n N T₀) (hBN : B ≤ N) :
    ↥B ≃* ↥(D.model B) :=
  (Subgroup.subgroupOfEquivOfLe hBN).symm.trans (D.e.subgroupMap (B.subgroupOf N))

private theorem model_perfect (D : BorelIso n N T₀) (hBN : B ≤ N) (hperf : ⁅B, B⁆ = B) :
    ⁅D.model B, D.model B⁆ = D.model B := by
  have h1 : ⁅B.subgroupOf N, B.subgroupOf N⁆ = B.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBN, hperf]
  show ⁅(B.subgroupOf N).map D.e.toMonoidHom, (B.subgroupOf N).map D.e.toMonoidHom⁆ =
    (B.subgroupOf N).map D.e.toMonoidHom
  rw [← Subgroup.map_commutator, h1]

private theorem card_quot_model (D : BorelIso n N T₀) (hBN : B ≤ N) :
    Nat.card (↥(D.model B) ⧸ CFSG.pCore 2 ↥(D.model B)) = Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) :=
  (Nat.card_congr (QuotientGroup.congr _ _ (modelEquiv D hBN)
    (CFSG.pCore_map_iso 2 (modelEquiv D hBN))).toEquiv).symm

private theorem mem_pCoreOf_of_model (D : BorelIso n N T₀) (hBN : B ≤ N) {w : ↥N}
    (hw : (w : Y) ∈ B) (hz : D.e w ∈ D.model B)
    (h : (⟨D.e w, hz⟩ : ↥(D.model B)) ∈ CFSG.pCore 2 ↥(D.model B)) : (w : Y) ∈ pCoreOf 2 B := by
  refine (mem_pCore_iff_coe' (⟨(w : Y), hw⟩ : ↥B)).1 ?_
  have hmap := CFSG.pCore_map_iso 2 (modelEquiv D hBN)
  have hmem : modelEquiv D hBN ⟨(w : Y), hw⟩ ∈
      (CFSG.pCore 2 ↥B).map (modelEquiv D hBN).toMonoidHom := by
    rw [hmap]
    exact h
  obtain ⟨b, hb, hbe⟩ := hmem
  have : b = ⟨(w : Y), hw⟩ := (modelEquiv D hBN).injective hbe
  rw [← this]
  exact hb

private theorem false_of_sup_eq [Finite Y] (hBN : B ≤ N) (hT₀2 : IsPGroup 2 T₀)
    (hT₀n : T₀ ≤ Subgroup.normalizer (B : Set Y)) (hsup : B ⊔ T₀ = N)
    (hord : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 20160) (hN : Nat.card ↥N = 9999360) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : B.relIndex (T₀ ⊔ B) = B.relIndex T₀ :=
    CFSG.Quasithin.A4.relIndex_sup_eq_of_le_normalizer' hT₀n
  rw [sup_comm, hsup] at h1
  obtain ⟨k, hk⟩ := hT₀2.index (B.subgroupOf T₀)
  have hk' : B.relIndex T₀ = 2 ^ k := hk
  have hcardN : Nat.card B * B.relIndex N = Nat.card N := by
    have h := Subgroup.card_mul_index (B.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv] at h
    exact h
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
  have hBcard : Nat.card ↥B = 20160 * 2 ^ j := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), hord, hj]
  have hmain : 20160 * (2 ^ j * 2 ^ k) = 20160 * 496 := by
    calc 20160 * (2 ^ j * 2 ^ k) = (20160 * 2 ^ j) * 2 ^ k := by ring
      _ = Nat.card B * B.relIndex N := by rw [hBcard, h1, hk']
      _ = 9999360 := by rw [hcardN, hN]
      _ = 20160 * 496 := by norm_num
  have h496 : 2 ^ j * 2 ^ k = 496 := Nat.eq_of_mul_eq_mul_left (by norm_num) hmain
  have h31 : (31 : ℕ) ∣ 2 ^ (j + k) := by
    rw [pow_add, h496]
    norm_num
  have h312 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 31) h31
  omega

end Transport

theorem inner_of_l5 {Y : Type} [Group Y] [Finite Y] {N T B : Subgroup Y} (hN : N.Normal)
    (hT : IsSylowTwoOf T ⊤) (hBN : B ≤ N) (hB : B ∈ lFamily T)
    (hTB : T ≤ Subgroup.normalizer (B : Set Y)) (h4 : IsPSL 4 2 1 (ModO2 B))
    (h5 : IsPSL 5 2 1 ↥N) : ∀ t ∈ T, InnerOnModO2 B t := by
  classical
  intro t ht
  have hNn : ∀ x : Y, x ∈ Subgroup.normalizer (N : Set Y) := fun x =>
    Subgroup.normalizer_eq_top_iff.2 hN ▸ Subgroup.mem_top x
  have hT₀ : IsSylowTwoOf (T ⊓ N) N :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hT le_top (fun x _ => hNn x)
  obtain ⟨e₀⟩ := nonempty_equiv_SLt_of_isPSL h5
  obtain ⟨D⟩ := exists_borelIso (by norm_num : 1 ≤ 5) hT₀ e₀
  have hT₀N : T ⊓ N ≤ N := inf_le_right
  have hT₀B : T ⊓ N ≤ Subgroup.normalizer (B : Set Y) := inf_le_left.trans hTB
  set P' : Subgroup Y := B ⊔ (T ⊓ N) with hP'
  have hBP' : B ≤ P' := le_sup_left
  have hT₀P' : T ⊓ N ≤ P' := le_sup_right
  have hP'N : P' ≤ N := sup_le hBN hT₀N
  set I : Set ℕ := D.cutsOf P' with hI
  have hmodP : D.model P' = QI 5 I := eq_QI_cuts ((D.Ut_le_model_iff hT₀N).2 hT₀P')
  have hIn : ∀ i ∈ I, 1 ≤ i ∧ i < 5 := fun i hi => D.isNode_of_mem_cutsOf hi
  have hB'Q : D.model B ≤ QI 5 I := hmodP ▸ (D.model_le_iff hBN).2 hBP'
  have hperfB : ⁅B, B⁆ = B := perfect_of_mem_cComp (X := B ⊔ T) hB
  have hperf' : ⁅D.model B, D.model B⁆ = D.model B := model_perfect D hBN hperfB
  have hord4 : Nat.card (ModO2 B) = 20160 := card_of_isPSL_four h4
  have hord : Nat.card (↥(D.model B) ⧸ CFSG.pCore 2 ↥(D.model B)) = 20160 := by
    rw [card_quot_model D hBN]
    exact hord4
  rcases l4_block_model hIn hB'Q hperf' hord with hI0 | ⟨hI14, hinner⟩
  ·
    exfalso
    have hPN : P' = N :=
      D.eq_of_cutsOf_eq hT₀N hT₀P' hP'N hT₀N le_rfl (by rw [← hI, hI0, D.cutsOf_L])
    exact false_of_sup_eq hBN (hT.2.1.to_le inf_le_left) hT₀B hPN hord4 (card_of_isPSL_five h5)
  ·
    have htN : t ∈ Subgroup.normalizer (N : Set Y) := hNn t
    have hconjT₀ : conjSub t (T ⊓ N) = T ⊓ N :=
      conjSub_eq_of_conj_mem (S := T) (P := T ⊓ N) (fun s hs p hp =>
        Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem hs (Subgroup.mem_inf.1 hp).1) (T.inv_mem hs),
          hN.conj_mem p (Subgroup.mem_inf.1 hp).2 s⟩) ht
    have hconjB : conjSub t B = B :=
      conjSub_eq_of_conj_mem (S := T) (fun s hs p hp =>
        (Subgroup.mem_normalizer_iff.1 (hTB hs) p).1 hp) ht
    have hφU : (Ut 5).map (D.autOf t htN).toMonoidHom = Ut 5 := by
      have h := D.model_conjSub t htN (T ⊓ N)
      rw [hconjT₀, D.model_B] at h
      exact h
    rcases aut_dichotomy (by norm_num : 3 ≤ 5) (D.autOf t htN) hφU with ⟨b, hbU, hb⟩ | hflip
    ·
      obtain ⟨β, hβT₀, hβb⟩ : ∃ β : ↥N, (β : Y) ∈ T ⊓ N ∧ D.e β = b := by
        have hbm : b ∈ D.model (T ⊓ N) := by
          rw [D.model_B]
          exact hbU
        obtain ⟨β, hβ, hβe⟩ := hbm
        exact ⟨β, hβ, hβe⟩
      have hact : ∀ x : ↥N, t * (x : Y) * t⁻¹ = (β : Y) * (x : Y) * (β : Y)⁻¹ := by
        intro x
        have h1 := hb (D.e x)
        rw [D.autOf_e] at h1
        have h2 : N.normalizerMonoidHom ⟨t, htN⟩ x = β * x * β⁻¹ := by
          apply D.e.injective
          rw [h1, ← hβb]
          simp
        have h3 := congrArg Subtype.val h2
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
        simpa using h3
      have hβT : (β : Y) ∈ T := hβT₀.1
      have hn : ∀ x ∈ D.model B, b * x * b⁻¹ ∈ D.model B := by
        intro x hx
        obtain ⟨x', rfl⟩ := D.e.surjective x
        have hx'B : (x' : Y) ∈ B := (D.mem_model x').1 hx
        have h1 : b * D.e x' * b⁻¹ = D.e (β * x' * β⁻¹) := by
          rw [← hβb]
          simp
        rw [h1, D.mem_model]
        exact (Subgroup.mem_normalizer_iff.1 (hTB hβT) (x' : Y)).1 hx'B
      obtain ⟨b', hb'B, hb'⟩ := hinner b (Ut_le_QI 5 I hbU) hn
      obtain ⟨x₁, rfl⟩ := D.e.surjective b'
      have hx₁B : (x₁ : Y) ∈ B := (D.mem_model x₁).1 hb'B
      refine ⟨(x₁ : Y), hx₁B, fun x hx => ?_⟩
      have hxN : x ∈ N := hBN hx
      have hxB' : D.e ⟨x, hxN⟩ ∈ D.model B := (D.mem_model ⟨x, hxN⟩).2 hx
      obtain ⟨hz, hzc⟩ := hb' _ hxB'
      set w : ↥N := (β * ⟨x, hxN⟩ * β⁻¹)⁻¹ * (x₁ * ⟨x, hxN⟩ * x₁⁻¹) with hw
      have hwe : (b * D.e ⟨x, hxN⟩ * b⁻¹)⁻¹ * (D.e x₁ * D.e ⟨x, hxN⟩ * (D.e x₁)⁻¹) = D.e w := by
        rw [← hβb]
        simp [hw]
      have hwY : (w : Y) = (t * x * t⁻¹)⁻¹ * ((x₁ : Y) * x * (x₁ : Y)⁻¹) := by
        rw [hact ⟨x, hxN⟩]
        rfl
      have hwB : (w : Y) ∈ B := by
        rw [hwY]
        have h1 : t * x * t⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hTB ht) x).1 hx
        exact B.mul_mem (B.inv_mem h1) (B.mul_mem (B.mul_mem hx₁B hx) (B.inv_mem hx₁B))
      have hz' : D.e w ∈ D.model B := (D.mem_model w).2 hwB
      have hkey : (⟨(b * D.e ⟨x, hxN⟩ * b⁻¹)⁻¹ * (D.e x₁ * D.e ⟨x, hxN⟩ * (D.e x₁)⁻¹), hz⟩ :
          ↥(D.model B)) = ⟨D.e w, hz'⟩ := Subtype.ext hwe
      rw [hkey] at hzc
      have := mem_pCoreOf_of_model D hBN hwB hz' hzc
      rw [hwY] at this
      exact this
    ·
      exfalso
      have hcut := D.cutsOf_conjSub hT₀N t htN hflip hT₀P'
      have hconjP : conjSub t P' = P' := by
        have h : conjSub t P' = conjSub t B ⊔ conjSub t (T ⊓ N) := Subgroup.map_sup _ _ _
        rw [h, hconjB, hconjT₀]
      rw [hconjP] at hcut
      have hcut' : I = flipNodes 5 I := hcut
      rcases hI14 with h1 | h1
      · have h4' : (4 : ℕ) ∈ flipNodes 5 I := ⟨1, by rw [h1]; rfl, rfl⟩
        rw [← hcut', h1] at h4'
        simp at h4'
      · have h1' : (1 : ℕ) ∈ flipNodes 5 I := ⟨4, by rw [h1]; rfl, rfl⟩
        rw [← hcut', h1] at h1'
        simp at h1'

end CFSG.Quasithin.A38c8
