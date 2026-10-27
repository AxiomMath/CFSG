module

public import CFSG.Quasithin.Vol2.KGFactInspExcCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.Quasithin.EmptyFaithful.R3c18B

public section

namespace CFSG.Quasithin.H13.KGInsp4316.Exc

open CFSG.Quasithin (perfectCore)
open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {X : Type} [Group X] [Finite X] {S R K : Subgroup X} {n : ℕ} {x : X}

theorem two_le_pRank_g2
    (h : Cfg4316 S R K n x) (hRS : R ≤ S) {f : ℕ}
    (hm : ChevalleyExceptionalModel ↥S .G2 2 f) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1) : 2 ≤ CFSG.Open.pRank p S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, L, _, _, _, hL, ⟨e⟩⟩ := CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model hm
  have : Finite (ModGL Tag.G2 L) := finite_modGL
  have hBT : CFSG.LieType.BorelTits.Holds ↥(adjointGroup Tag.G2 L) 2 :=
    (CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hm).of_mulEquiv e
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 L).subgroupOf (adjointGroup Tag.G2 L)) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2
        (CFSG.QuasithinUnique.Setup.X6.unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := L) 2).1)
  obtain ⟨j, D, hD, hdvd⟩ := exists_le_perfectCore h hRS e hBT hU₀
    CFSG.QuasithinUnique.Setup.X6.G2_residualOvergroupsAt
  obtain ⟨g, hg, hker⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_levi_hom_adjoint
    (τ := Tag.G2) (K := L) hL hf (CFSG.QuasithinUnique.Setup.X6.g2Index j)
  have hodd : Odd (4 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
      ((Nat.even_pow' (by have := h.two_le; omega)).mpr (by decide)) odd_one
  have h1 := odd_dvd_card_of_le hD g hker hodd hdvd
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hL, ← pow_mul, mul_comm f 2,
    pow_mul] at h1
  norm_num at h1
  have hnf : n ∣ f := dvd_of_four_pow_sub_one_dvd (by have := h.two_le; omega) h1
  have hpf : p ∣ 2 ^ f - 1 := hpn.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)
  have hpSL : p ∣ Nat.card (SL2 L) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hL]
    exact Dvd.dvd.mul_left (hpf.trans (by simpa using Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2)) _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpSL
  obtain ⟨E, hE, hEel, -⟩ := CFSG.Quasithin.R3c18.exists_sq_g2 (RingEquiv.refl L) hp ha
    (by ext i j; simp)
  have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup Tag.G2 L)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hEel hE
  exact CFSG.QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv e hp.one_lt h2

end CFSG.Quasithin.H13.KGInsp4316.Exc
