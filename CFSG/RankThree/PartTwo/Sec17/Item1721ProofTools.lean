module

public import CFSG.RankThree.PartTwo.Sec17.Item1727Tools
public import CFSG.RankThree.PartTwo.Late.Cores17
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec14.Item145Bot
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped Pointwise

namespace TailProof

variable {G : Type} [Group G] [Finite G]

theorem false_of_inf_centralizer_ne_bot {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    {V : Subgroup G} (hVe : CFSG.Assembly.IsElemAbelian p V) (hV : Nat.card V = p ^ 2) {e t : G}
    (he3 : e ^ 3 = 1) (heV : e ∈ Subgroup.normalizer (V : Set G))
    (heC : e ∉ Subgroup.centralizer (V : Set G))
    (hfix : V ⊓ Subgroup.centralizer ({e} : Set G) ≠ ⊥)
    (htV : t ∈ Subgroup.normalizer (V : Set G)) (hte : t * e * t⁻¹ = e⁻¹) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.zpowers e with hE
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime he3 (fun h1 => heC (h1 ▸ Subgroup.one_mem _)))
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr heV
  have hV3 : ¬ 3 ∣ Nat.card V := by
    rw [hV]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    exact hp3 this.symm
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hCE : Subgroup.centralizer (E : Set G) = Subgroup.centralizer ({e} : Set G) := by
    rw [hE, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  set W := ⁅V, E⁆ with hW
  have hWV : W ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hEV
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three E V hE3 hV3 hEV
  rw [hCE] at hfac
  have hcop : Nat.Coprime (Nat.card E) (Nat.card V) := by
    rw [hE, Nat.card_zpowers, orderOf_eq_prime he3 (fun h1 => heC (h1 ▸ Subgroup.one_mem _)), hV]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes Nat.prime_three hp.out).mpr
      (Ne.symm hp3))
  have hfit := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot hVc hEV hcop
  rw [Subgroup.commutator_comm, hCE] at hfit
  have hdisj : W ⊓ (V ⊓ Subgroup.centralizer ({e} : Set G)) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_left _ inf_le_right) hfit.le)
  have hnormW : V ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [hVc x hx.1 y (hWV hy), mul_inv_cancel_right]
    exact hy
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W
    (V ⊓ Subgroup.centralizer ({e} : Set G)) hnormW (disjoint_iff.mpr hdisj)
  rw [← hfac, hV] at hcard
  have hCdvd : Nat.card (V ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) ∣ p ^ 2 :=
    hV ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow hp.out).mp hCdvd
  have hm1 : m = 1 := by
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h0 | h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hmc, h0, pow_zero])) hfix
    · exact h1
    · exfalso
      apply heC
      have heq : V ⊓ Subgroup.centralizer ({e} : Set G) = V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hmc, h2, hV])
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : v ∈ V ⊓ Subgroup.centralizer ({e} : Set G) := by rw [heq]; exact hv
      exact Subgroup.mem_centralizer_singleton_iff.mp hv'.2
  rw [hm1, pow_one] at hmc
  have hWp : Nat.card W = p := by
    rw [hmc] at hcard
    have hp0 : 0 < p := hp.out.pos
    have : Nat.card W * p = p * p := by rw [← hcard, sq]
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  have hWe : CFSG.Assembly.IsElemAbelian p W := ⟨⟨⟨fun a b => Subtype.ext
    (hVc a (hWV a.2) b (hWV b.2))⟩⟩, fun x hx => hVe.2 x (hWV hx)⟩
  have hW1 : W ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hWp
    exact hp.out.one_lt.ne hWp
  have heW : e ∈ Subgroup.normalizer (W : Set G) := by
    have h := Subgroup.normalizer_commutator_ge_left E V
    rw [Subgroup.commutator_comm] at h
    exact h (Subgroup.mem_zpowers e)
  have hWfix : W ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
    refine le_bot_iff.mp (le_trans ?_ hdisj.le)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hWV) inf_le_right)
  have htW : t ∈ Subgroup.normalizer (W : Set G) := by
    refine mem_normalizer_of_map_conj_eq' ?_
    rw [hW, Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer htV, hE,
      MonoidHom.map_zpowers]
    change ⁅V, Subgroup.zpowers (t * e * t⁻¹)⁆ = _
    rw [hte, Subgroup.zpowers_inv]
  exact card_ne_of_inverts hWe hW1 he3 heW hWfix htW hte hWp

theorem le_centralizer_of_inverts_one {p : ℕ} [hp : Fact p.Prime] {V F : Subgroup G}
    (hVe : CFSG.Assembly.IsElemAbelian p V) (hV : Nat.card V = p) (hF3 : ∀ f ∈ F, f ^ 3 = 1)
    (hFV : F ≤ Subgroup.normalizer (V : Set G)) {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) (htF : ∀ f ∈ F, t * f * t⁻¹ = f⁻¹) :
    F ≤ Subgroup.centralizer (V : Set G) := by
  intro f hf
  by_contra hfC
  have hfix : V ⊓ Subgroup.centralizer ({f} : Set G) = ⊥ := by
    have hdvd : Nat.card (V ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ∣ p :=
      hV ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | hpc
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply hfC
      have heq : V ⊓ Subgroup.centralizer ({f} : Set G) = V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hpc, hV])
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : v ∈ V ⊓ Subgroup.centralizer ({f} : Set G) := by rw [heq]; exact hv
      exact Subgroup.mem_centralizer_singleton_iff.mp hv'.2
  have hV1 : V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hV
    exact hp.out.one_lt.ne hV
  exact card_ne_of_inverts hVe hV1 (hF3 f hf) (hFV hf) hfix htV (htF f hf) hV

theorem le_centralizer_of_inverts_two {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    {V F : Subgroup G} (hVe : CFSG.Assembly.IsElemAbelian p V) (hV : Nat.card V = p ^ 2)
    (hF3 : ∀ f ∈ F, f ^ 3 = 1) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hF9 : Nat.card F = 9)
    (hFV : F ≤ Subgroup.normalizer (V : Set G)) {c s t : G} (hc3 : c ^ 3 = 1)
    (hcF : ∀ f ∈ F, c * f = f * c) (hcV : c ∈ Subgroup.normalizer (V : Set G))
    (hcC : c ∉ Subgroup.centralizer (V : Set G))
    (hsV : s ∈ Subgroup.normalizer (V : Set G)) (hsc : s * c * s⁻¹ = c⁻¹)
    (hsF : ∀ f ∈ F, s * f * s⁻¹ ∈ F)
    (htV : t ∈ Subgroup.normalizer (V : Set G)) (htc : t * c * t⁻¹ = c)
    (htF : ∀ f ∈ F, t * f * t⁻¹ = f⁻¹) :
    F ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hFC
  obtain ⟨e, he, heC⟩ := Set.not_subset.mp hFC
  have hfpf : ∀ f ∈ F, f ∉ Subgroup.centralizer (V : Set G) →
      V ⊓ Subgroup.centralizer ({f} : Set G) = ⊥ := fun f hf hfC => by
    by_contra hne
    exact false_of_inf_centralizer_ne_bot hp3 hVe hV (hF3 f hf) (hFV hf) hfC hne htV (htF f hf)
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hV3 : Nat.Coprime 3 (Nat.card V) := by
    rw [hV]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes Nat.prime_three hp.out).mpr
      (Ne.symm hp3))
  set D₀ := F ⊓ Subgroup.centralizer (V : Set G) with hD₀
  have hD₀1 : D₀ ≠ ⊥ := by
    intro hbot
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
      Nat.prime_three F V ⟨⟨⟨fun a b => Subtype.ext (hFab a a.2 b b.2)⟩⟩, hF3⟩
      (by rw [hF9]; norm_num) hFV hV3
    have hle : V ≤ ⊥ := by
      rw [← hgen]
      refine iSup_le fun D => iSup_le fun hD => ?_
      obtain ⟨hDF, hD3⟩ := hD
      obtain ⟨f, hfD, hf1⟩ := (Subgroup.bot_or_exists_ne_one D).resolve_left (by
        intro h
        rw [h, Subgroup.card_bot] at hD3
        norm_num at hD3)
      have hfC : f ∉ Subgroup.centralizer (V : Set G) := fun hfC => hf1 (by
        have : f ∈ D₀ := ⟨hDF hfD, hfC⟩
        rw [hbot] at this
        exact this)
      calc V ⊓ Subgroup.centralizer (D : Set G) ≤ V ⊓ Subgroup.centralizer ({f} : Set G) :=
            inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hfD))
        _ = ⊥ := hfpf f (hDF hfD) hfC
    rw [le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hV
    have := hp.out.one_lt
    nlinarith
  have hD₀F : D₀ ≤ F := inf_le_left
  have hD₀card : Nat.card D₀ = 3 := by
    have hdvd : Nat.card D₀ ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hF9]
      exact Subgroup.card_dvd_of_le hD₀F
    obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h0 | h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hmc, h0, pow_zero])) hD₀1
    · rw [hmc, h1, pow_one]
    · exfalso
      have heq : D₀ = F := Subgroup.eq_of_le_of_card_ge hD₀F (by rw [hmc, h2, hF9]; norm_num)
      exact heC ((heq ▸ he : e ∈ D₀).2)
  have heD₀ : e ∉ D₀ := fun h => heC h.2
  have hdisj : Disjoint (Subgroup.zpowers e) D₀ := by
    rw [disjoint_iff]
    have hdvd : Nat.card (Subgroup.zpowers e ⊓ D₀ : Subgroup G) ∣ 3 := by
      rw [← hD₀card]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers e ⊓ D₀ = D₀ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hD₀card])
      have he1 : e ≠ 1 := fun h1 => heC (h1 ▸ Subgroup.one_mem _)
      have heo : orderOf e = 3 := orderOf_eq_prime (hF3 e he) he1
      have hle : D₀ ≤ Subgroup.zpowers e := by
        rw [← heq]
        exact inf_le_left
      have heq' : D₀ = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hD₀card, Nat.card_zpowers, heo])
      exact heD₀ (heq' ▸ Subgroup.mem_zpowers e)
  have hD₀N : D₀ ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro d hd
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [hFab d (hD₀F hd) y (Subgroup.zpowers_le.mpr he hy), mul_inv_cancel_right]
    exact hy
  have hFeq : F = Subgroup.zpowers e ⊔ D₀ := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr he) hD₀F) ?_).symm
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hD₀N hdisj,
      hD₀card, Nat.card_zpowers,
      orderOf_eq_prime (hF3 e he) (fun h1 => heC (h1 ▸ Subgroup.one_mem _)), hF9]
  have hse : ∃ k : ℤ, ∃ y ∈ Subgroup.centralizer (V : Set G), s * e * s⁻¹ = e ^ k * y := by
    have hmem : s * e * s⁻¹ ∈ Subgroup.zpowers e ⊔ D₀ := hFeq ▸ hsF e he
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hD₀N] at hmem
    obtain ⟨x, hx, y, hy, hxy⟩ := hmem
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨k, y, hy.2, hxy.symm⟩
  have hcCe : ∀ x ∈ F, x * c = c * x := fun x hx => (hcF x hx).symm
  by_cases hc1 : V ⊓ Subgroup.centralizer ({c} : Set G) = ⊥
  · exact heC (mem_centralizer_of_inverts hp3 hVe hV hc3 (hF3 e he) (hcF e he) hcV (hFV he) hsV
      htV hc1 hsc htc hse ⟨1, Subgroup.one_mem _, by rw [mul_one]; exact htF e he⟩)
  ·
    set ℓ := V ⊓ Subgroup.centralizer ({c} : Set G) with hℓ
    have hdvd : Nat.card ℓ ∣ p ^ 2 := hV ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have hm1 : m = 1 := by
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h0 | h1 | h2
      · exact absurd (Subgroup.card_eq_one.mp (by rw [hmc, h0, pow_zero])) hc1
      · exact h1
      · exfalso
        apply hcC
        have heq : ℓ = V := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hmc, h2, hV])
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hv' : v ∈ ℓ := by rw [heq]; exact hv
        exact Subgroup.mem_centralizer_singleton_iff.mp hv'.2
    rw [hm1, pow_one] at hmc
    have hℓe : CFSG.Assembly.IsElemAbelian p ℓ := ⟨⟨⟨fun a b => Subtype.ext
      (hVc a a.2.1 b b.2.1)⟩⟩, fun x hx => hVe.2 x hx.1⟩
    have heℓ : e ∈ Subgroup.normalizer (ℓ : Set G) :=
      mem_normalizer_inf_centralizer (hFV he) (hcCe e he)
    have hℓfix : ℓ ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans (hfpf e he heC).le)
    have htℓ : t ∈ Subgroup.normalizer (ℓ : Set G) :=
      mem_normalizer_inf_centralizer_of_eq htV (by rw [htc])
    exact card_ne_of_inverts hℓe hc1 (hF3 e he) heℓ hℓfix htℓ (htF e he) hmc

end TailProof

end CFSG.RankThree.PartTwo.Sec17
