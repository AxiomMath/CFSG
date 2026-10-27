module

public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality

public section

namespace CFSG.Quasithin.C58NS.MPB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_seven {X L : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat ↥X)
    (hL : IsBlock2 X L) (α : ↥L →* alternatingGroup (Fin 7)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro t ht
  by_contra hnot
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₂ : Subgroup G := L.map (MulAut.conj t).toMonoidHom with hL₂def
  have hXt : X.map (MulAut.conj t).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.1 ht
  have hL₂ : IsBlock2 X L₂ := by
    have := Setup.Campbell.isBlock2_map_conj hL t
    rwa [hXt] at this
  have hne : L ≠ L₂ := fun h => hnot (Subgroup.mem_normalizer_iff_map_conj_eq.2 h.symm)
  have hcomm : ⁅L, L₂⁆ = ⊥ := distinctBlocksCommuteStatement X L L₂ hX hL hL₂ hne
  have hLc : L ≤ Subgroup.centralizer (L₂ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hr : 2 ≤ CFSG.Open.pRank 3 L :=
    C1GN.le_pRank_three_of_alt_quotient α hα hker C1GN.two_le_pRank_alt7
  obtain ⟨E, hEL, hE, hEcard⟩ := exists_pRank (p := 3) (by norm_num) L
  have h3 : 3 ∣ Nat.card L₂ := by
    rw [hL₂def, Subgroup.card_map_of_injective (MulAut.conj t).injective]
    refine (dvd_pow_self 3 (by omega : CFSG.Open.pRank 3 L ≠ 0)).trans ?_
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hEL
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L₂) 3 h3
  have hy' : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hcommE : ∀ e ∈ E, Commute e (y : G) := fun e he =>
    (Subgroup.mem_centralizer_iff.1 (hLc (hEL he)) (y : G) y.2).symm
  have hyE : (y : G) ∉ E := by
    intro hyE
    have hyc : ∀ h ∈ L₂, h * (y : G) = (y : G) * h := fun h hh =>
      Subgroup.mem_centralizer_iff.1 (hLc (hEL hyE)) h hh
    have hyO : (y : G) ∈ pCoreOf 2 L₂ := by
      refine hL₂.1.2.1 ⟨y.2, ?_⟩
      show (y : G) ∈ Subgroup.centralizer (pCoreOf 2 L₂ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hyc h (CFSG.LieType.BorelTits.pCoreOf_le 2 L₂ hh)
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₂) ⟨(y : G), hyO⟩
    have hdvd : orderOf (y : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    rw [hy'] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  obtain ⟨hE', hcard'⟩ := exists_elemAbelian_sup_zpowers hE hy' hcommE hyE
  have hle : E ⊔ Subgroup.zpowers (y : G) ≤ X :=
    sup_le (hEL.trans hL.2.1) ((Subgroup.zpowers_le.2 y.2).trans hL₂.2.1)
  rw [hEcard] at hcard'
  have hrank : CFSG.Open.pRank 3 L + 1 ≤ CFSG.Open.pRank 3 X :=
    le_pRank Nat.prime_three hle hE' (by rw [hcard', pow_succ])
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
    pRank_top_subtype (p := 3) X
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2 :=
    isStronglyQuasithin_iff.mp hSQ.1 3 Nat.prime_three (by norm_num)
  omega

end CFSG.Quasithin.C58NS.MPB
