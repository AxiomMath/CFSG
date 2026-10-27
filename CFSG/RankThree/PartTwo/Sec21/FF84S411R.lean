module

public import CFSG.RankThree.PartTwo.Sec21.FF84S411Base
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Coord
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open scoped commutatorElement

@[expose] def HypTransvRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Post b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2, ∀ t : G,
      t ∈ Op 2 (Nor U) ⊓ Cen b → t ≠ 1 → Op 2 (Cen t) ≠ Op 2 (Nor U) →
        ∀ A : Subgroup G, A ≤ Op 2 (Cen b ⊓ Cen t) → IsElementaryAbelian 2 A → Nat.card A ≤ 8

@[expose] def HypOmNoAlt : Prop :=
  ∀ F : OmG → OmG → F6,
    (∀ g₁ ∈ Eτ, ∀ g₂ ∈ Eτ, polarMinus (F g₁ g₂) sig0 = 0 ∧ polarMinus (F g₁ g₂) tau0 = 0) →
    (∀ g₁ ∈ Eτ, ∀ g₁' ∈ Eτ, ∀ g₂ ∈ Eτ, F (g₁ * g₁') g₂ = F g₁ g₂ + F g₁' g₂) →
    (∀ g₁ ∈ Eτ, ∀ g₂ ∈ Eτ, ∀ g₂' ∈ Eτ, F g₁ (g₂ * g₂') = F g₁ g₂ + F g₁ g₂') →
    (∀ g ∈ Eτ, F g g = 0) →
    (∀ h ∈ P2, ∀ g₁ ∈ Eτ, ∀ g₂ ∈ Eτ, F (h * g₁ * h⁻¹) (h * g₂ * h⁻¹) = h • F g₁ g₂) →
    ∀ g₁ ∈ Eτ, ∀ g₂ ∈ Eτ, F g₁ g₂ = 0

structure Ctx411 {G : Type} [Group G] [Finite G] (S : Subgroup G) (e : ↥S ≃* Multiplicative F6)
    (ψ : ↥(Nor S) →* OmG) (s t : ↥S) (b : G) : Prop where
  H : OmSet S e ψ
  hes : Multiplicative.toAdd (e s) = sig0
  het : Multiplicative.toAdd (e t) = tau0
  hc : CFSG.Assembly.IsCharTwoType G
  hbs : b ∈ Cen (s : G)
  hbt : b ∈ Cen (t : G)
  hb3 : orderOf b = 3
  hU16 : Nat.card ↥(S ⊓ Cen b) = 16
  hrank : ∀ A : Subgroup G, A ≤ Op 2 (Cen b ⊓ Cen (t : G)) → IsElementaryAbelian 2 A →
    Nat.card A ≤ 8
  hSE : IsElementaryAbelian 2 S
  hPar : HypOmParabolic
  hPair : HypOmPair
  hNoAlt : HypOmNoAlt

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG} {s t : ↥S} {b : G}

theorem Ctx411.ht1 (C : Ctx411 S e ψ s t b) : (t : G) ≠ 1 := by
  intro h
  have : t = 1 := Subtype.ext h
  have h2 := C.het
  rw [this, map_one, toAdd_one] at h2
  exact tau0_ne_zero h2.symm

theorem Ctx411.hs1 (C : Ctx411 S e ψ s t b) : (s : G) ≠ 1 := by
  intro h
  have : s = 1 := Subtype.ext h
  have h2 := C.hes
  rw [this, map_one, toAdd_one] at h2
  exact sig0_ne_zero h2.symm

theorem two_subgroup_P2_trivial (hPair : HypOmPair) (X : Subgroup OmG) (hXP : X ≤ P2)
    (hnorm : ∀ h ∈ P2, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hX2 : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) = 1) : X = ⊥ := by
  obtain ⟨eA0⟩ := hPair qMinus_sig0 qMinus_tau0 qMinus_sig0_add_tau0 tau0_ne_zero
  have eA : ↥P2 ≃* alternatingGroup (Fin 5) := eA0
  let X' : Subgroup ↥P2 := X.subgroupOf P2
  haveI hX'n : X'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn⟩
  haveI : (X'.map eA.toMonoidHom).Normal := Subgroup.Normal.map hX'n _ eA.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X'.map eA.toMonoidHom) with h | h
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : (⟨x, hXP hx⟩ : ↥P2) ∈ X' := hx
    have h2 : eA ⟨x, hXP hx⟩ ∈ X'.map eA.toMonoidHom := ⟨_, h1, rfl⟩
    rw [h, Subgroup.mem_bot] at h2
    have h3 : (⟨x, hXP hx⟩ : ↥P2) = 1 := eA.injective (h2.trans (map_one eA).symm)
    exact congrArg Subtype.val h3
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP : IsPGroup 2 (alternatingGroup (Fin 5)) := by
      intro a
      have ha : a ∈ X'.map eA.toMonoidHom := by rw [h]; exact Subgroup.mem_top a
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨k, hk⟩ := hX2 x.1 hx
      refine ⟨k, ?_⟩
      have : x ^ (2 ^ k) = 1 := Subtype.ext hk
      show (eA x) ^ (2 ^ k) = 1
      rw [← map_pow, this, map_one]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Fintype.card_fin]
      decide
    rw [h60] at hn
    have h3 : 3 ∣ 2 ^ n := ⟨20, by omega⟩
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem psi_two_el (n : ↥(Nor S)) {K : Subgroup G} (hn : (n : G) ∈ Op 2 K) :
    ∃ k : ℕ, n ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := S3.Op_isPGroup 2 K ⟨(n : G), hn⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem mem_M_of_cen {s t : G} {x : G} (hxs : x ∈ Cen s) (hxt : x ∈ Cen t) :
    x ∈ CenS (Subgroup.closure ({s, t} : Set G)) := by
  rw [cenS_pair, Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hy with rfl | hy
  · exact (Subgroup.mem_centralizer_singleton_iff.1 hxs).symm
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxt).symm

theorem Ctx411.cenT_le_S (C : Ctx411 S e ψ s t b) {x : G} (hxT : x ∈ Op 2 (Cen (t : G)))
    (hxs : x ∈ Cen (s : G)) : x ∈ S := by
  have hxt : x ∈ Cen (t : G) := S3.Op_le 2 _ hxT
  have hM := mem_M_of_cen hxs hxt
  have hxN : x ∈ Nor S := M_le_nor C.H C.hes C.het hM
  let N : Subgroup G := Op 2 (Cen (t : G)) ⊓ Cen (s : G)
  let X : Subgroup OmG := (N.subgroupOf (Nor S)).map ψ
  have hXP : X ≤ P2 := by
    intro g hg
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
    have hnN : (n : G) ∈ N := hn
    have := mem_M_of_cen (Subgroup.mem_inf.1 hnN).2 (S3.Op_le 2 _ (Subgroup.mem_inf.1 hnN).1)
    exact (M_psi C.H C.hes C.het n).1 this
  have hXnorm : ∀ h ∈ P2, ∀ g ∈ X, h * g * h⁻¹ ∈ X := by
    intro h hh g hg
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨⟨m, hm⟩, hmφ⟩ := phiM_surj C.H C.hes C.het ⟨h, hh⟩
    have hmψ : ψ ⟨m, M_le_nor C.H C.hes C.het hm⟩ = h := by
      have := congrArg Subtype.val hmφ
      exact this
    have hmN := M_le_nor C.H C.hes C.het hm
    have hms : m ∈ Cen (s : G) := by
      rw [cenS_pair, Subgroup.mem_centralizer_iff] at hm
      exact Subgroup.mem_centralizer_singleton_iff.2 (hm _ (by simp)).symm
    have hmt : m ∈ Cen (t : G) := by
      rw [cenS_pair, Subgroup.mem_centralizer_iff] at hm
      exact Subgroup.mem_centralizer_singleton_iff.2 (hm _ (by simp)).symm
    have hnN : (n : G) ∈ N := hn
    refine Subgroup.mem_map.2 ⟨⟨m, hmN⟩ * n * ⟨m, hmN⟩⁻¹, ?_, ?_⟩
    · show (m * (n : G) * m⁻¹) ∈ N
      refine Subgroup.mem_inf.2 ⟨S3.Op_conj_mem 2 (Subgroup.le_normalizer hmt)
        (Subgroup.mem_inf.1 hnN).1, ?_⟩
      have hc1 : Commute m (s : G) := Subgroup.mem_centralizer_singleton_iff.1 hms
      have hc2 : Commute (n : G) (s : G) :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hnN).2
      exact Subgroup.mem_centralizer_singleton_iff.2 ((hc1.mul_left hc2).mul_left hc1.inv_left)
    · rw [map_mul, map_mul, map_inv, hmψ]
  have hX2 : ∀ g ∈ X, ∃ k : ℕ, g ^ (2 ^ k) = 1 := by
    intro g hg
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨k, hk⟩ := psi_two_el n (Subgroup.mem_inf.1 (show (n : G) ∈ N from hn)).1
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hX := two_subgroup_P2_trivial C.hPair X hXP hXnorm hX2
  have hmem : ψ ⟨x, hxN⟩ ∈ X := Subgroup.mem_map.2 ⟨⟨x, hxN⟩, Subgroup.mem_inf.2 ⟨hxT, hxs⟩, rfl⟩
  rw [hX, Subgroup.mem_bot] at hmem
  exact (C.H.psi_eq_one_iff _).1 hmem

theorem Ctx411.not_R_le_Cen (C : Ctx411 S e ψ s t b) :
    ¬ ∀ x ∈ S ⊓ Op 2 (Cen (t : G)), x ∈ Cen b := by
  intro hall
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsord : orderOf (s : G) = 2 := by
    have h : (s : G) ^ 2 = 1 := by
      have := congrArg Subtype.val (sq_S e s)
      rw [pow_two]
      exact this
    exact orderOf_eq_prime h C.hs1
  have hPp : IsPGroup 2 (Subgroup.zpowers (s : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hsord]
    norm_num
  have hst : (s : G) ∈ Cen (t : G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (S_comm' e s.2 t.2)
  have hTB : ∀ x : G, x ∈ Cen (t : G) → x ∈ Nor (Op 2 (Cen (t : G))) := fun x hx =>
    le_nor_op2 (Cen (t : G)) hx
  have hPQ : ⁅Subgroup.zpowers (s : G), Subgroup.zpowers b⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₁
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
    have hc : Commute (s : G) b := (Subgroup.mem_centralizer_singleton_iff.1 C.hbs).symm
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hc.zpow_zpow i j).eq
  have hcomm := B_PQ (p := 2) (Subgroup.zpowers (s : G)) (Subgroup.zpowers b)
    (Op 2 (Cen (t : G))) hPp (S3.Op_isPGroup 2 _)
    (by rw [Nat.card_zpowers, C.hb3]; norm_num)
    (by rw [Subgroup.zpowers_le]; exact hTB _ hst)
    (by rw [Subgroup.zpowers_le]; exact hTB _ C.hbt) hPQ
    (by
      intro x hx
      obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.1 hx
      have hxs : x ∈ Cen (s : G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hxC (s : G) (Subgroup.mem_zpowers _)).symm
      have hxS : x ∈ S := C.cenT_le_S hxT hxs
      have hxb : x ∈ Cen b := hall x (Subgroup.mem_inf.2 ⟨hxS, hxT⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hc : Commute x b := Subgroup.mem_centralizer_singleton_iff.1 hxb
      exact ((hc.zpow_right k).symm).eq)
  have hbC : b ∈ CenS (Op 2 (Cen (t : G))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 : ⁅r, b⁆ ∈ ⁅Op 2 (Cen (t : G)), Subgroup.zpowers b⁆ :=
      Subgroup.commutator_mem_commutator hr (Subgroup.mem_zpowers b)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hbT : b ∈ Op 2 (Cen (t : G)) :=
    B_charTwo_cen C.hc (orderOf_t e C.ht1) (Subgroup.mem_inf.2 ⟨C.hbt, hbC⟩)
  obtain ⟨k, hk⟩ := S3.Op_isPGroup 2 _ ⟨b, hbT⟩
  have hk' : b ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hdvd : orderOf b ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [C.hb3] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem Ctx411.not_S_le_T (C : Ctx411 S e ψ s t b) : ¬ S ≤ Op 2 (Cen (t : G)) := by
  intro hST
  have hSt : S ≤ Cen (t : G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (S_comm' e hx t.2)
  let A' : Subgroup G := Op 2 (Cen (t : G)) ⊓ Cen b
  have hA'le : A' ≤ Op 2 (Cen b ⊓ Cen (t : G)) := by
    refine S3.le_Op_of_normal 2 (Cen b ⊓ Cen (t : G)) A' ?_ ?_ ?_
    · exact fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
        S3.Op_le 2 _ (Subgroup.mem_inf.1 hx).1⟩
    · exact (S3.Op_isPGroup 2 _).to_le (inf_le_left)
    · intro h hh m hm
      obtain ⟨hmT, hmb⟩ := Subgroup.mem_inf.1 hm
      obtain ⟨hhb, hht⟩ := Subgroup.mem_inf.1 hh
      refine Subgroup.mem_inf.2 ⟨S3.Op_conj_mem 2 (Subgroup.le_normalizer hht) hmT, ?_⟩
      have hc1 : Commute h b := Subgroup.mem_centralizer_singleton_iff.1 hhb
      have hc2 : Commute m b := Subgroup.mem_centralizer_singleton_iff.1 hmb
      exact Subgroup.mem_centralizer_singleton_iff.2 ((hc1.mul_left hc2).mul_left hc1.inv_left)
  have hAle : S ⊓ Cen b ≤ Op 2 (Cen b ⊓ Cen (t : G)) := fun x hx =>
    hA'le (Subgroup.mem_inf.2 ⟨hST (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩)
  have := C.hrank _ hAle (isEA_of_le C.hSE inf_le_left)
  rw [C.hU16] at this
  omega

theorem Ctx411.R_perp (C : Ctx411 S e ψ s t b) :
    ∀ x : ↥S, (x : G) ∈ Op 2 (Cen (t : G)) ↔
      polarMinus (Multiplicative.toAdd (e x)) tau0 = 0 :=
  claim1_core C.H C.het C.ht1 C.hbt C.not_R_le_Cen C.not_S_le_T

theorem Ctx411.CR (C : Ctx411 S e ψ s t b) : CenS (S ⊓ Op 2 (Cen (t : G))) = S :=
  claim2_core C.H C.het C.hPar C.R_perp

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
