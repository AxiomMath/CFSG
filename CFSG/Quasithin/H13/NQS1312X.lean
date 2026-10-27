module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent0
public import CFSG.Quasithin.H13.NQS1312J

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem card_centralizer_swap_alt5 : ∀ a b : Fin 5, a ≠ b →
    Fintype.card {g : alternatingGroup (Fin 5) //
      Equiv.swap a b * (g : Equiv.Perm (Fin 5)) = g * Equiv.swap a b} = 6 := by
  decide +kernel

theorem card_eq_of_two_pow_mul {a m N : ℕ} (h : 2 ^ a * m = N) (hm : ¬ 2 ∣ m) (hN : N = 60) :
    2 ^ a = 4 := by
  subst hN
  have ha : a ≤ 5 := by
    by_contra ha
    have : 2 ^ 6 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    nlinarith
  interval_cases a <;> omega

theorem card_eq_of_two_pow_mul_eight {a m N : ℕ} (h : 2 ^ a * m = N) (hm : ¬ 2 ∣ m)
    (hN : N = 20160) : 2 ^ a = 64 := by
  subst hN
  have ha : a ≤ 14 := by
    by_contra ha
    have : 2 ^ 15 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    nlinarith
  interval_cases a <;> omega

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem alpha_eq_one_of_mem_oTwoZIn_of_center {K : Subgroup G} {X : Type*} [Group X]
    (hZ : Subgroup.center X = ⊥) {α : ↥K →* X} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) {x : G} (hx : x ∈ oTwoZIn K) (hxK : x ∈ K) :
    α ⟨x, hxK⟩ = 1 := by
  obtain ⟨hxK', hc⟩ := SBc17.mem_oTwoZIn_iff.1 hx
  have hle : CFSG.pCore 2 ↥K ≤ α.ker := hker.ge
  set ᾱ := QuotientGroup.lift (CFSG.pCore 2 ↥K) α hle with hᾱ
  have hsurj : Function.Surjective ᾱ := by
    intro g
    obtain ⟨k, rfl⟩ := hα g
    exact ⟨QuotientGroup.mk k, QuotientGroup.lift_mk _ _ _⟩
  have h1 : ᾱ (QuotientGroup.mk ⟨x, hxK'⟩) ∈ Subgroup.center X :=
    Subgroup.map_center_le_center hsurj ⟨_, hc, rfl⟩
  rw [hZ, mem_bot, QuotientGroup.lift_mk] at h1
  exact h1

omit [Finite G] in
theorem alpha_eq_one_of_mem_oTwoZIn {K : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    {α : ↥K →* alternatingGroup (Fin n)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) {x : G} (hx : x ∈ oTwoZIn K) (hxK : x ∈ K) :
    α ⟨x, hxK⟩ = 1 :=
  alpha_eq_one_of_mem_oTwoZIn_of_center
    (alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn))
    hα hker hx hxK

omit [Finite G] in
theorem not_two_dvd_index_map {K P : Subgroup G} (hP : IsSylowTwoOf P K) {X : Type*} [Group X]
    {α : ↥K →* X} (hα : Function.Surjective α) : ¬ 2 ∣ ((P.subgroupOf K).map α).index :=
  fun h => hP.2.2 (h.trans (Subgroup.index_map_dvd _ hα))

theorem comm_mem_oTwoZIn {K Q Mh : Subgroup G} (hQK : Q ≤ normalizer (K : Set G))
    (hC1 : (K ⊔ Q) ⊓ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G) ≤
      pCoreOf 2 (K ⊔ Q) ⊔ oTwoZIn K)
    {t : G} (htQ : t ∈ Q) (htV : t ∈ normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G))
    (hautR : autOn Q (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) =
      zpowers (conjAct (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) ⟨t, htV⟩))
    (hMK : autOn (Mh ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) =
      autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) ⊓
        centralizer (autOn Q (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) : Set (MulAut _)))
    {y : G} (hy : y ∈ Mh ⊓ K) :
    t * y * t⁻¹ ∈ K ∧ t * y * t⁻¹ * y⁻¹ ∈ oTwoZIn K := by
  set VK := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hVK
  have hKV : K ≤ normalizer (VK : Set G) := SBc17.le_normalizer_V K Q
  have hyN : y ∈ normalizer (VK : Set G) := hKV hy.2
  have hyA : conjAct VK ⟨y, hyN⟩ ∈ autOn (Mh ⊓ K) VK :=
    SBc17.mem_autOn_iff.2 ⟨y, hyN, hy, rfl⟩
  rw [hMK] at hyA
  have htA : conjAct VK ⟨t, htV⟩ ∈ autOn Q VK := by
    rw [hautR]
    exact mem_zpowers _
  have hc := (mem_centralizer_iff.1 hyA.2) _ htA
  have htyK : t * y * t⁻¹ ∈ K := (mem_normalizer_iff.1 (hQK htQ) y).1 hy.2
  have hzK : t * y * t⁻¹ * y⁻¹ ∈ K := K.mul_mem htyK (K.inv_mem hy.2)
  have hzN : t * y * t⁻¹ * y⁻¹ ∈ normalizer (VK : Set G) := hKV hzK
  have hz1 : conjAct VK ⟨t * y * t⁻¹ * y⁻¹, hzN⟩ = 1 := by
    have e : (⟨t * y * t⁻¹ * y⁻¹, hzN⟩ : normalizer (VK : Set G)) =
        ⟨t, htV⟩ * ⟨y, hyN⟩ * ⟨t, htV⟩⁻¹ * ⟨y, hyN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  exact ⟨htyK, SBc17.inf_centralizer_le_oTwoZIn hC1 ⟨hzK, A4.conjAct_eq_one_iff.1 hz1⟩⟩

theorem false_of_c27Alt_five {K Q S Mh : Subgroup G} (hQK : Q ≤ normalizer (K : Set G))
    (hS : IsSylowTwoOf (S ⊓ K) K) (hSM : S ⊓ K ≤ Mh ⊓ K)
    (hC1 : (K ⊔ Q) ⊓ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G) ≤
      pCoreOf 2 (K ⊔ Q) ⊔ oTwoZIn K)
    {α : ↥K →* alternatingGroup (Fin 5)} (hαb : IsAltBlockTypeWith K 5 α)
    {t : G} (htQ : t ∈ Q) (htV : t ∈ normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G))
    (hautR : autOn Q (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) =
      zpowers (conjAct (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) ⟨t, htV⟩))
    {σ : Equiv.Perm (Fin 5)} (hσ : σ.IsSwap)
    (hσα : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin 5)) * σ⁻¹)
    (hMK : autOn (Mh ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) =
      autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) ⊓
        centralizer (autOn Q (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) : Set (MulAut _))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, hab, rfl⟩ := hσ
  set C : Subgroup (alternatingGroup (Fin 5)) :=
    (centralizer ({Equiv.swap a b} : Set (Equiv.Perm (Fin 5)))).comap
      (alternatingGroup (Fin 5)).subtype with hC
  have hle : ((S ⊓ K).subgroupOf K).map α ≤ C := by
    rintro _ ⟨⟨y, hyK⟩, hy, rfl⟩
    have hyS : y ∈ S ⊓ K := Subgroup.mem_subgroupOf.1 hy
    obtain ⟨htyK, hzZ⟩ := comm_mem_oTwoZIn hQK hC1 htQ htV hautR hMK (hSM hyS)
    have h1 := alpha_eq_one_of_mem_oTwoZIn (by norm_num) hαb.1 hαb.2.1 hzZ
      (K.mul_mem htyK (K.inv_mem hyK))
    have e2 : (⟨t * y * t⁻¹ * y⁻¹, K.mul_mem htyK (K.inv_mem hyK)⟩ : ↥K) =
        ⟨t * y * t⁻¹, htyK⟩ * (⟨y, hyK⟩ : ↥K)⁻¹ := rfl
    rw [e2, map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 := hσα y hyK htyK
    rw [h1] at h2
    rw [Subgroup.mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff]
    calc (α ⟨y, hyK⟩ : Equiv.Perm (Fin 5)) * Equiv.swap a b =
        Equiv.swap a b * (α ⟨y, hyK⟩ : Equiv.Perm (Fin 5)) * (Equiv.swap a b)⁻¹ *
          Equiv.swap a b := by rw [← h2]
      _ = Equiv.swap a b * (α ⟨y, hyK⟩ : Equiv.Perm (Fin 5)) := by group
  have hC6 : Nat.card C = 6 := by
    rw [← card_centralizer_swap_alt5 a b hab, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [hC, Subgroup.mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff]
    exact eq_comm
  have hP2 : IsPGroup 2 (((S ⊓ K).subgroupOf K).map α) :=
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map α
  obtain ⟨e, he⟩ := hP2.exists_card_eq
  have hidx := not_two_dvd_index_map hS hαb.1
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hmul := Subgroup.card_mul_index (((S ⊓ K).subgroupOf K).map α)
  rw [he, h60] at hmul
  have h4 := card_eq_of_two_pow_mul hmul hidx rfl
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [he, h4, hC6] at hdvd
  norm_num at hdvd

omit [Finite G] in
theorem card_le_two_of_unique {X : Type*} [Group X] {B : Subgroup X}
    (h : ∀ b ∈ B, ∀ b' ∈ B, b ≠ 1 → b' ≠ 1 → b = b') : Nat.card B ≤ 2 := by
  classical
  have hinj : Function.Injective (fun b : B => decide ((b : X) = 1)) := by
    intro b b' hbb
    simp only [decide_eq_decide] at hbb
    by_cases hb : (b : X) = 1
    · exact Subtype.ext (hb.trans (hbb.1 hb).symm)
    · exact Subtype.ext (h b b.2 b' b'.2 hb (fun h' => hb (hbb.2 h')))
  calc Nat.card B ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem false_of_c27Alt_eight {K Q S : Subgroup G} (hS : IsSylowTwoOf (S ⊓ K) K)
    (hidx : ∀ a ∈ S, ∀ b ∈ S, a ∉ Q → b ∉ Q → a⁻¹ * b ∈ Q)
    (hC1 : (K ⊔ Q) ⊓ centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G) ≤
      pCoreOf 2 (K ⊔ Q) ⊔ oTwoZIn K)
    {α : ↥K →* alternatingGroup (Fin 8)} (hαb : IsAltBlockTypeWith K 8 α)
    {t : G} (htV : t ∈ normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) : Set G))
    (hautR : autOn Q (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) =
      zpowers (conjAct (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) ⟨t, htV⟩))
    (hord : orderOf (conjAct (omegaOneCenterOf (pCoreOf 2 (K ⊔ Q))) ⟨t, htV⟩) = 2) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set VK := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hVK
  have hKV : K ≤ normalizer (VK : Set G) := SBc17.le_normalizer_V K Q
  have hαZ : ∀ (y : G) (hy : y ∈ K), y ∈ centralizer (VK : Set G) → α ⟨y, hy⟩ = 1 :=
    fun y hy hyC => alpha_eq_one_of_mem_oTwoZIn (by norm_num) hαb.1 hαb.2.1
      (SBc17.inf_centralizer_le_oTwoZIn hC1 ⟨hy, hyC⟩) hy
  set A := ((S ⊓ K).subgroupOf K).map α with hA
  set B := ((Q ⊓ K).subgroupOf K).map α with hB
  have hstar : ∀ (y : G) (hy : y ∈ Q ⊓ K), α ⟨y, hy.2⟩ ≠ 1 →
      conjAct VK ⟨y, hKV hy.2⟩ = conjAct VK ⟨t, htV⟩ := by
    intro y hy hα1
    have hyA : conjAct VK ⟨y, hKV hy.2⟩ ∈ autOn Q VK :=
      SBc17.mem_autOn_iff.2 ⟨y, hKV hy.2, hy.1, rfl⟩
    rw [hautR] at hyA
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hyA
    rw [← zpow_mod_orderOf, hord] at hm
    have h0 : 0 ≤ m % (2 : ℕ) := Int.emod_nonneg _ (by norm_num)
    have h2 : m % (2 : ℕ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
    have : m % (2 : ℕ) = 0 ∨ m % (2 : ℕ) = 1 := by omega
    rcases this with h | h
    · rw [h, zpow_zero] at hm
      exact absurd (hαZ y hy.2 (A4.conjAct_eq_one_iff.1 hm.symm)) hα1
    · rw [h, zpow_one] at hm
      exact hm.symm
  have hB2 : Nat.card B ≤ 2 := by
    refine card_le_two_of_unique ?_
    rintro _ ⟨⟨y, hyK⟩, hy, rfl⟩ _ ⟨⟨y', hy'K⟩, hy', rfl⟩ h1 h1'
    have hyQ : y ∈ Q ⊓ K := Subgroup.mem_subgroupOf.1 hy
    have hy'Q : y' ∈ Q ⊓ K := Subgroup.mem_subgroupOf.1 hy'
    have e1 := hstar y hyQ h1
    have e2 := hstar y' hy'Q h1'
    have hm : y⁻¹ * y' ∈ K := K.mul_mem (K.inv_mem hyK) hy'K
    have hc : conjAct VK ⟨y⁻¹ * y', hKV hm⟩ = 1 := by
      have e : (⟨y⁻¹ * y', hKV hm⟩ : normalizer (VK : Set G)) =
          (⟨y, hKV hyK⟩ : normalizer (VK : Set G))⁻¹ * ⟨y', hKV hy'K⟩ := rfl
      rw [e, map_mul, map_inv, e1, e2, inv_mul_cancel]
    have h3 := hαZ _ hm (A4.conjAct_eq_one_iff.1 hc)
    have e3 : (⟨y⁻¹ * y', hm⟩ : ↥K) = (⟨y, hyK⟩ : ↥K)⁻¹ * ⟨y', hy'K⟩ := rfl
    rw [e3, map_mul, map_inv, inv_mul_eq_one] at h3
    exact h3
  have hA4 : Nat.card A ≤ 4 := by
    by_cases hAB : A ≤ B
    · exact (Subgroup.card_le_of_le hAB).trans (by omega)
    · obtain ⟨a₀, ha₀A, ha₀B⟩ := Set.not_subset.1 hAB
      obtain ⟨⟨s₀, hs₀K⟩, hs₀, rfl⟩ := ha₀A
      have hs₀S : s₀ ∈ S ⊓ K := Subgroup.mem_subgroupOf.1 hs₀
      have hs₀Q : s₀ ∉ Q := fun h => ha₀B ⟨⟨s₀, hs₀K⟩, Subgroup.mem_subgroupOf.2 ⟨h, hs₀K⟩, rfl⟩
      have h1 := card_le_two_mul_card_inf (A := A) (B := B) ⟨⟨s₀, hs₀K⟩, hs₀, rfl⟩ ?_
      · exact h1.trans (by
          have := Subgroup.card_le_of_le (inf_le_right : A ⊓ B ≤ B)
          omega)
      · rintro _ ⟨⟨s, hsK⟩, hs, rfl⟩ hsB
        have hsS : s ∈ S ⊓ K := Subgroup.mem_subgroupOf.1 hs
        have hsQ : s ∉ Q := fun h => hsB ⟨⟨s, hsK⟩, Subgroup.mem_subgroupOf.2 ⟨h, hsK⟩, rfl⟩
        have hq := hidx s₀ hs₀S.1 s hsS.1 hs₀Q hsQ
        have hm : s₀⁻¹ * s ∈ K := K.mul_mem (K.inv_mem hs₀K) hsK
        refine ⟨⟨s₀⁻¹ * s, hm⟩, Subgroup.mem_subgroupOf.2 ⟨hq, hm⟩, ?_⟩
        have e : (⟨s₀⁻¹ * s, hm⟩ : ↥K) = (⟨s₀, hs₀K⟩ : ↥K)⁻¹ * ⟨s, hsK⟩ := rfl
        rw [e, map_mul, map_inv]
  have hP2 : IsPGroup 2 A :=
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map α
  obtain ⟨e, he⟩ := hP2.exists_card_eq
  have hidx2 := not_two_dvd_index_map hS hαb.1
  have h8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hmul := Subgroup.card_mul_index A
  rw [he, h8] at hmul
  have h64 := card_eq_of_two_pow_mul_eight hmul hidx2 rfl
  rw [he, h64] at hA4
  omega

end CFSG.Quasithin.H13.U3.NLine
