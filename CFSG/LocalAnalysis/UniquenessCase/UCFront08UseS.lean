module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08Use
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace F08

@[expose] def R869NS (D : Data G) : Prop :=
  ∀ L : Subgroup G, L ≤ D.M → D.M ≤ normalizer (L : Set G) → IsProdOfCalC D.M L →
    (∃ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L) →
    ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ A : Subgroup G, A ≤ D.M → Nat.card A = r →
      (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L → normalizer (A : Set G) ≤ D.M

theorem R869NS_of_R869N (D : Data G) (h : R869N D) : R869NS D := by
  intro L hLM hML hprod ⟨p, hp, h2⟩
  refine h L hLM hML hprod fun hthin => ?_
  have h1 := hthin p (D.sig_prime p hp).1 (D.sig_prime p hp).2
  omega

end F08

theorem uc22p2214_faith_of_normalizer_le (D : Data G) (Ch : Choice2011 G) (hV : S22_V D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKV : ¬ K ≤ centralizer (c.V : Set G))
    (hN : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ A : Subgroup G, A ≤ D.M → Nat.card A = r →
      (conjClosure D.M K ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 (conjClosure D.M K) =
        conjClosure D.M K → normalizer (A : Set G) ≤ D.M)
    (hfix : ∀ K' ∈ conjSetOf D.M K, c.B0 ≤ normalizer (K' : Set G)) {a : G} (ha : a ∈ c.B0)
    (ha1 : a ≠ 1) :
    ∃ K' ∈ conjSetOf D.M K, ∃ k ∈ K', a * k * a⁻¹ * k⁻¹ ∉ centralizer (c.V : Set G) := by
  by_contra hall
  have hall' : ∀ K' ∈ conjSetOf D.M K, ∀ k ∈ K',
      a * k * a⁻¹ * k⁻¹ ∈ centralizer (c.V : Set G) := by
    intro K' hK' k hk
    by_contra hk'
    exact hall ⟨K', hK', k, hk, hk'⟩
  have hMM : D.M ≤ normalizer (D.M : Set G) := Subgroup.le_normalizer
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd le_rfl hMM hK
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hO2 : CFSG.pCore 2 (MBar D.M c.V) = ⊥ := (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 hred
  have haM : a ∈ D.M := c.hBM ha
  have haX : CentralizesBar a (conjClosure D.M K) := by
    refine uc22p2214_centralizesBar_conjClosure (hMX haM) fun K' hK' k hk => ?_
    have hK'C := uc22p2214_calC_of_mem_conjSetOf hK hK'
    have hK'V := uc22p2214_not_le_centralizer_of_mem_conjSetOf c.hVM hKV hK'
    have hcb := uc22p2214_centralizesBar_of_comm c.hVM hO2 hK'C hK'V (hfix K' hK' ha)
      (hall' K' hK')
    have h1 : a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 D.M :=
      uc22p22r_pCoreOf_le_of_isSubnormal hK'C.1 (hcb.2 k hk)
    have hkX : k ∈ conjClosure D.M K :=
      le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf D.M K) => A) K' hK' le_rfl hk
    have h2 : a * k * a⁻¹ * k⁻¹ ∈ conjClosure D.M K :=
      (conjClosure D.M K).mul_mem ((mem_normalizer_iff.1 (hMX haM) k).1 hkX)
        ((conjClosure D.M K).inv_mem hkX)
    exact uc22p2214_pCoreOf_inf_le hXM ⟨h1, h2⟩
  have hodd : Odd (orderOf a) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 ha
  have hne1 : orderOf a ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  have hr : (orderOf a).minFac.Prime := Nat.minFac_prime hne1
  have hrd : (orderOf a).minFac ∣ orderOf a := Nat.minFac_dvd _
  have hr2 : (orderOf a).minFac ≠ 2 := by
    intro h2
    rw [h2] at hrd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  have hord : orderOf (a ^ (orderOf a / (orderOf a).minFac)) = (orderOf a).minFac :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne' hrd
  set a' : G := a ^ (orderOf a / (orderOf a).minFac)
  set r : ℕ := (orderOf a).minFac
  have hAcard : Nat.card (zpowers a') = r := by rw [Nat.card_zpowers, hord]
  have hAB : zpowers a' ≤ c.B0 := zpowers_le.2 (c.B0.pow_mem ha _)
  have hAc : ∀ g ∈ zpowers a', CentralizesBar g (conjClosure D.M K) := fun g hg =>
    uc22p21d_centralizesBar_of_mem_zpowers (uc22p21d_centralizesBar_pow haX _) hg
  have hXQ : (conjClosure D.M K ⊓ centralizer ((zpowers a' : Subgroup G) : Set G)) ⊔
      pCoreOf 2 (conjClosure D.M K) = conjClosure D.M K :=
    uc22p21d_sup_pCore_eq hr hr2 hAcard hAc
  exact s21_2 D Ch h1930 { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers a') hAB
    (hN r hr hr2 (zpowers a') (hAB.trans c.hBM) hAcard hXQ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
