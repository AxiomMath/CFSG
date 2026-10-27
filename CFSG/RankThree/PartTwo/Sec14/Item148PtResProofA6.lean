module

public import CFSG.RankThree.PartTwo.Sec14.Item148PointProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Concl143Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Item148PtRes

variable {G : Type} [Group G] [Finite G]

theorem false_of_tripleCover_A6 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B : Subgroup G} (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) {X : Subgroup G}
    (hCX : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hX : X ∈ thetaComponentsAt 3 b)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)))
    (hQX : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X) : False := by
  have hD := h.toSec13Data
  have hbA : b ∈ A := hB.1 hb
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set N := pPrimeCoreOf 3 Cb with hN
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAC : A ≤ Cb := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx b hbA)
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 Cb
  have hXCb : X ≤ Cb := le_centralizer_of_mem_thetaComponentsAt hX
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := hXCb.trans hCbN
  have hθXN : θX ≤ N := by
    rw [hθX, Sec6.theta_eq_inf_of_mem_thetaComponentsAt hX]
    exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf _)
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hX
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  have hNX : N ⊓ X ≤ θX := inf_le_theta_of_quasisimple hXN hN3 hq hZ
  have h3X : 3 ∣ Nat.card X := by
    have h1 : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ∣
        Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := Subgroup.card_subgroup_dvd_card _
    rw [hZ] at h1
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨u, huB, hub⟩ := exists_mem_not_mem_zpowers hD.card_eq hD.isElemAbelian.2 hB hbA
  have huA : u ∈ A := hB.1 huB
  have hu3 : u ^ 3 = 1 := hD.isElemAbelian.2 u huA
  have hu1 : u ≠ 1 := fun h1 => hub (h1 ▸ one_mem _)
  have hne : Subgroup.zpowers b ≠ Subgroup.zpowers u := fun he =>
    hub (he ▸ Subgroup.mem_zpowers u)
  have huCb : u ∈ Cb := hAC huA
  have hCB : Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Item148HJ.centralizer_inf_le_of_mem_hyperplane hD.isElemAbelian hD.card_eq hB hb huB hb1 hu1
      hne
  have hQYC : Q ≤ Y ⊓ Cb := le_inf (hQY.trans inf_le_left)
    (hQY.trans (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))))
  have hcontra : Q ≤ N → False := fun hQN =>
    hQb ((le_inf hQN hQYC).trans (inf_le_pPrimeCoreOf148 (inf_le_right.trans hCbN) hN3))
  by_cases htriv : ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ θX
  ·
    have hM : ∀ m ∈ N ⊔ X, ⁅m, u⁆ ∈ N := fun m hm =>
      commutator_mem_of_mem_sup hXN (hCbN huCb) (fun x hx => by
        have h1 : ⁅x, u⁆ = (u * x * u⁻¹ * x⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact hθXN (inv_mem (htriv x hx))) hm
    set J := (N ⊔ X) ⊓ Subgroup.centralizer ({u} : Set G) with hJ
    have hNJ : N ⊔ J = N ⊔ X := by
      apply le_antisymm (sup_le le_sup_left inf_le_left)
      intro m hm
      have hMK : N ⊔ X ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hXN
      obtain ⟨c', hc'M, hc'u, hc'm⟩ := Item148HJ.exists_commute_of_commutator_mem hu3 le_sup_left
        hMK (hCbN huCb) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3) hm (hM m hm)
      have hc'J : c' ∈ J :=
        Subgroup.mem_inf.mpr ⟨hc'M, Subgroup.mem_centralizer_singleton_iff.mpr hc'u⟩
      have hm' : m = c' * (c'⁻¹ * m) := by group
      rw [hm', sup_comm]
      exact mul_mem (Subgroup.mem_sup_left hc'J) (Subgroup.mem_sup_right hc'm)
    have hJCb : J ≤ Cb := inf_le_left.trans (sup_le (pPrimeCoreOf_le 3 Cb) hXCb)
    have hR : Y ⊓ Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
      intro g hg
      obtain ⟨hgYC, hgu⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨hgY, hgb⟩ := Subgroup.mem_inf.mp hgYC
      exact le_normalizer_pPrimeCoreOf 3 _
        (Subgroup.mem_inf.mpr ⟨hgY, hCB (Subgroup.mem_inf.mpr ⟨hgb, hgu⟩)⟩)
    have hQR : Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) :=
      (le_sSup ⟨hQ, hQY⟩ : Q ≤ deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G))).trans
        (hYB B hB)
    have hCbNJ : Cb ≤ Subgroup.normalizer ((N ⊔ J : Subgroup G) : Set G) := by
      rw [hNJ]
      exact hCX
    have hQNJ : Q ≤ N ⊔ J := by
      rw [hNJ]
      exact hQX
    exact hQb (Item148HJ.le_pPrimeCoreOf_of_coprime hu3 (pPrimeCoreOf_le 3 Cb) hN3 hCbN hCbNJ
      (hY.2 huA) huCb hJCb inf_le_right hR (coprime_card_pPrimeCoreOf 3 _) hQR hQYC hQNJ)
  ·
    push Not at htriv
    obtain ⟨x₀, hx₀, hx₀u⟩ := htriv
    apply hcontra
    have huX : u ∈ Subgroup.normalizer (X : Set G) :=
      mem_normalizer_of_le_sup hX h3X huCb (hCX huCb)
    set σ : MulAut (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
      Sec4.thetaQuotMulAut ↥X (X.normalizerMonoidHom ⟨u, huX⟩) with hσ
    have hσmk : ∀ (x : G) (hx : x ∈ X),
        σ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨x, hx⟩) =
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
            ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.mp huX x).mp hx⟩ := fun x hx => by
      rw [hσ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
      rfl
    have hmk : ∀ (x y : G) (hx : x ∈ X) (hy : y ∈ X),
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨x, hx⟩ : ↥X) =
            QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ↔ x * y⁻¹ ∈ θX := by
      intro x y hx hy
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
      constructor
      · intro h1
        exact ⟨_, h1, by simp [div_eq_mul_inv]⟩
      · rintro ⟨z, hz, hzeq⟩
        have : z = (⟨x, hx⟩ : ↥X) / ⟨y, hy⟩ := Subtype.ext (by
          simp only [Subgroup.coe_subtype] at hzeq
          rw [hzeq, Subgroup.coe_div, div_eq_mul_inv])
        rwa [← this]
    have hσ3 : σ ^ 3 = 1 := by
      have h1 : (⟨u, huX⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hu3)
      rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
    have hσ1 : σ ≠ 1 := by
      intro h1
      apply hx₀u
      have h2 := hσmk x₀ hx₀
      rw [h1, MulAut.one_apply] at h2
      exact (hmk _ _ _ hx₀).mp h2.symm
    have : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X) := hq.1
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
    intro q hq'
    obtain ⟨n, hn, y, hy, rfl⟩ := exists_mul_of_mem_sup hXN (hQX hq')
    have hqu : u * (n * y) * u⁻¹ = n * y := by
      have h1 := Subgroup.mem_centralizer_iff.mp ((hQY hq').2) u huB
      calc u * (n * y) * u⁻¹ = n * y * u * u⁻¹ := by rw [h1]
        _ = n * y := by group
    have hyN : u * y * u⁻¹ * y⁻¹ ∈ N := by
      have h1 : u * y * u⁻¹ * y⁻¹ = (u * n * u⁻¹)⁻¹ * n := by
        have h2 : u * y * u⁻¹ = (u * n * u⁻¹)⁻¹ * (n * y) := by
          rw [← hqu]
          group
        rw [h2]
        group
      rw [h1]
      exact mul_mem (inv_mem ((Subgroup.mem_normalizer_iff.mp (hCbN huCb) n).mp hn)) hn
    have hyX : u * y * u⁻¹ * y⁻¹ ∈ X :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp huX y).mp hy) (inv_mem hy)
    have hfix : σ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ := by
      rw [hσmk y hy]
      exact (hmk _ _ _ hy).mpr (hNX (Subgroup.mem_inf.mpr ⟨hyN, hyX⟩))
    set k := orderOf (n * y) with hk
    have hk3 : Nat.Coprime k 3 := by
      have h1 : k ∣ Nat.card Q := by
        rw [hk, ← Subgroup.orderOf_mk (n * y) hq']
        exact orderOf_dvd_natCard _
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        fun h3 => hQ3 (h3.trans h1))
    obtain ⟨n', hn', hpow⟩ := exists_pow_eq_mul hXN hn hy k
    have hyk : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨y, hy⟩ : ↥X) ^ k = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have h1 : y ^ k = n'⁻¹ := by
        have h2 : n' * y ^ k = 1 := by rw [← hpow, hk, pow_orderOf_eq_one]
        exact eq_inv_of_mul_eq_one_right h2
      have h2 : y ^ k ∈ θX := hNX (Subgroup.mem_inf.mpr ⟨h1 ▸ inv_mem hn', pow_mem hy k⟩)
      obtain ⟨z, hz, hzeq⟩ := h2
      have : z = (⟨y, hy⟩ : ↥X) ^ k := Subtype.ext (by
        simp only [Subgroup.coe_subtype] at hzeq
        rw [hzeq, Subgroup.coe_pow])
      rwa [← this]
    have hy1 := eq_one_of_fixed_tripleCover hZ e hσ3 hσ1 hfix hyk hk3
    have hyθ : y ∈ θX := by
      have h1 := (QuotientGroup.eq_one_iff _).mp hy1
      exact ⟨_, h1, rfl⟩
    exact mul_mem hn (hθXN hyθ)

end Item148PtRes

theorem step148PointHJdA6_holds : Step148PointHJdA6 := by
  intro G _ _ A c L h Y hY _ hYB B hB Q hQ hQY b hb hb1 _ hQb _ _ _ _ _ _ _ _ _ _ _ X _ hCX hX hT
    hQX
  exact (Item148PtRes.false_of_tripleCover_A6 h hY hYB hB hQ hQY hb hb1 hQb hCX hX hT hQX).elim

end CFSG.RankThree.PartTwo.Sec14
