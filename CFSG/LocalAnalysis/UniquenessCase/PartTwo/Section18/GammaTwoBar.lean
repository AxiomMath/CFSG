module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sq_mem_centralizer_of_centralizesMod {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hsmall : mSub V₀ ≤ 1) {x : G} (hxM : x ∈ D.M)
    (hx : CentralizesMod V₀ V x) :
    x ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
  have hcard : Nat.card V₀ ≤ 2 := (mSub_le_one_iff h.pairFacts.elemAbelian₀).1 hsmall
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hzV₀ : x * v * x⁻¹ * v⁻¹ ∈ V₀ := hx v hv
  have hz2 : (x * v * x⁻¹ * v⁻¹) ^ 2 = 1 := h.pairFacts.elemAbelian₀.2 _ hzV₀
  have hzfix : x * (x * v * x⁻¹ * v⁻¹) * x⁻¹ = x * v * x⁻¹ * v⁻¹ := by
    by_cases hz1 : x * v * x⁻¹ * v⁻¹ = 1
    · rw [hz1]; simp
    · have hwV₀ : x * (x * v * x⁻¹ * v⁻¹) * x⁻¹ ∈ V₀ :=
        (Subgroup.mem_normalizer_iff.1 (h.pairFacts.le_normalizer₀ hxM) _).1 hzV₀
      have hw1 : x * (x * v * x⁻¹ * v⁻¹) * x⁻¹ ≠ 1 := by
        intro h1
        apply hz1
        have := congrArg (fun y => x⁻¹ * y * x) h1
        simpa [mul_assoc] using this
      have h2le : 2 ≤ Nat.card V₀ := by
        have hord : orderOf (x * v * x⁻¹ * v⁻¹) = 2 := orderOf_eq_prime hz2 hz1
        have hzp : Nat.card (Subgroup.zpowers (x * v * x⁻¹ * v⁻¹)) = 2 := by
          rw [Nat.card_zpowers, hord]
        calc 2 = Nat.card (Subgroup.zpowers (x * v * x⁻¹ * v⁻¹)) := hzp.symm
          _ ≤ Nat.card V₀ :=
              Nat.card_mono (Set.toFinite _) (Subgroup.zpowers_le.2 hzV₀)
      have hcard2 : Nat.card V₀ = 2 := le_antisymm hcard h2le
      obtain ⟨b, -, huniv⟩ := (Nat.card_eq_two_iff' (1 : ↥V₀)).1 hcard2
      have hz : (⟨x * v * x⁻¹ * v⁻¹, hzV₀⟩ : ↥V₀) = b := huniv _ (by simpa using hz1)
      have hw : (⟨x * (x * v * x⁻¹ * v⁻¹) * x⁻¹, hwV₀⟩ : ↥V₀) = b := huniv _ (by simpa using hw1)
      exact congrArg Subtype.val (hw.trans hz.symm)
  have hx2v : x ^ 2 * v * (x ^ 2)⁻¹ = v := by
    have hz2' : (x * v * x⁻¹ * v⁻¹) * (x * v * x⁻¹ * v⁻¹) = 1 := by
      simpa [pow_two] using hz2
    calc x ^ 2 * v * (x ^ 2)⁻¹
        = x * (x * v * x⁻¹) * x⁻¹ := by rw [pow_two]; group
      _ = x * ((x * v * x⁻¹ * v⁻¹) * v) * x⁻¹ := by group
      _ = (x * (x * v * x⁻¹ * v⁻¹) * x⁻¹) * (x * v * x⁻¹) := by group
      _ = (x * v * x⁻¹ * v⁻¹) * (x * v * x⁻¹) := by rw [hzfix]
      _ = (x * v * x⁻¹ * v⁻¹) * ((x * v * x⁻¹ * v⁻¹) * v) := by group
      _ = v := by rw [← mul_assoc, hz2', one_mul]
  calc v * x ^ 2 = (x ^ 2 * v * (x ^ 2)⁻¹) * x ^ 2 := by rw [hx2v]
    _ = x ^ 2 * v := by group

theorem isCyclic_of_isPGroup_le_cTilde {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hsmall : mSub V₀ ≤ 1) (h129 : R129_1 D) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {P : Subgroup G} (hP : IsPGroup p P) (hPC : P ≤ F11.CTilde D.M V₀ V) : IsCyclic P := by
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hpodd : Odd p := (D.sig_prime p hp).1.eq_two_or_odd'.resolve_left hp2
  have hPV : P ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have hxM : x ∈ D.M := CFSG.LocalAnalysis.WeakClosure81.cTilde_le_M D.M V₀ V (hPC hx)
    have hxC : CentralizesMod V₀ V x :=
      CFSG.LocalAnalysis.WeakClosure81.centralizesMod_of_mem_cTilde h.pairFacts.elemAbelian
        h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ (hPC hx)
    have hx2 : x ^ 2 ∈ Subgroup.centralizer (V : Set G) :=
      sq_mem_centralizer_of_centralizesMod h hsmall hxM hxC
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.1 hP ⟨x, hx⟩
    have hn' : orderOf x = p ^ n := by simpa using hn
    have hxodd : Odd (orderOf x) := by
      rw [hn']
      exact hpodd.pow
    obtain ⟨k, hk⟩ := hxodd
    have hxeq : x = (x ^ 2) ^ (k + 1) := by
      have hpow : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
      calc x = x ^ (2 * k + 2) := by
              rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ, hpow, one_mul]
        _ = (x ^ 2) ^ (k + 1) := by rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
    rw [hxeq]
    exact Subgroup.pow_mem _ hx2 (k + 1)
  exact s15_13A_isCyclic_of_le_centralizer D h129 h61 h hp
    (fun x hx => CFSG.LocalAnalysis.WeakClosure81.cTilde_le_M D.M V₀ V (hPC hx)) hPV hP

theorem normalizer_inf_cTilde_le_normalizer_wClos {D : Data G} {V₀ V : Subgroup G}
    (hW : E3.wClos V 0 D.T ≤ F11.CTilde D.M V₀ V) :
    Subgroup.normalizer ((D.T ⊓ F11.CTilde D.M V₀ V : Subgroup G) : Set G) ≤
      Subgroup.normalizer (E3.wClos V 0 D.T : Set G) := by
  have hgoal : E3.wClos V 0 (D.T ⊓ F11.CTilde D.M V₀ V) = E3.wClos V 0 D.T := by
    refine le_antisymm (E3.wClos_mono inf_le_left) ?_
    refine E3.wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm⟩ := (E3.mem_gammaSet_iff).1 hA
    exact E3.le_wClos (E3.mem_gammaSet_iff.2
      ⟨le_inf hAT ((E3.le_wClos ⟨hAT, g, hAg, hm⟩).trans hW), g, hAg, hm⟩)
  rw [← hgoal]
  exact E3.normalizer_le_normalizer_wClos (D.T ⊓ F11.CTilde D.M V₀ V)

theorem normalizer_wClos_le_of_le_cTilde (D : Data G) (h129 : R129_1 D) (h61 : UC6.R6_1 D)
    (hne : D.sig.Nonempty) (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hsmall : mSub V₀ ≤ 1)
    (hW : E3.wClos V 0 D.T ≤ F11.CTilde D.M V₀ V) :
    Subgroup.normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := F11.CTilde D.M V₀ V with hCdef
  have hCM : C ≤ D.M := CFSG.LocalAnalysis.WeakClosure81.cTilde_le_M D.M V₀ V
  have hMN : D.M ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).mp
      (CFSG.LocalAnalysis.WeakClosure81.cTilde_subgroupOf_normal h.pairFacts.elemAbelian
        h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀)
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ C) C :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hCM hMN
  obtain ⟨p, hp⟩ := hne
  have hp2 : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp2⟩
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp2 D.M
  have hcard3 : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp2.pos (hrk p hp)
  set Q : Subgroup G := C ⊔ E with hQdef
  have hCQ : C ≤ Q := le_sup_left
  have hEQ : E ≤ Q := le_sup_right
  have hQM : Q ≤ D.M := sup_le hCM hEM
  have hQN : Q ≤ Subgroup.normalizer (C : Set G) :=
    sup_le Subgroup.le_normalizer (hEM.trans hMN)
  have hEC : Nat.card ↥(E ⊓ C) ≤ p := by
    have hcyc : IsCyclic ↥(E ⊓ C) :=
      isCyclic_of_isPGroup_le_cTilde h hsmall h129 h61 hp
        (hEel.mono inf_le_left).isPGroup (le_trans inf_le_right (le_of_eq hCdef))
    have h1 : Monoid.exponent ↥(E ⊓ C) = Nat.card ↥(E ⊓ C) := IsCyclic.exponent_eq_card
    have h2 : Monoid.exponent ↥(E ⊓ C) ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hEel.2 (x : G) x.2.1)
    rw [← h1]
    exact Nat.le_of_dvd hp2.pos h2
  have hidx : ∃ k : ℕ, C.relIndex Q = p ^ k := by
    rw [hQdef, s15_13A_relIndex_sup (hEM.trans hMN)]
    have hdvd : (E ⊓ C).relIndex E ∣ p ^ CFSG.Open.pRank p D.M := by
      rw [← hEcard]
      exact Subgroup.relIndex_dvd_card (H := E ⊓ C) (K := E)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp2).1 hdvd
    exact ⟨k, hk⟩
  have hQsup : Q ≤ C ⊔ (Q ⊓ Subgroup.normalizer ((D.T ⊓ C : Subgroup G) : Set G)) :=
    s15_13A_le_sup_inf_normalizer hCQ hQN hS
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf p
    (Q ⊓ Subgroup.normalizer ((D.T ⊓ C : Subgroup G) : Set G))
  have hQR : Q ≤ C ⊔ R :=
    s15_13A_le_sup_of_isSylowOf hp2 hCQ hQN inf_le_left hQsup hidx hR
  have hRM : R ≤ D.M := (hR.le.trans inf_le_left).trans hQM
  have hRN : R ≤ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    (hR.le.trans inf_le_right).trans
      (normalizer_inf_cTilde_le_normalizer_wClos (by rw [← hCdef]; exact hW))
  have hRc : ¬ IsCyclic ↥R :=
    s15_13A_not_cyclic_of_card hp2 hCQ hQN hEQ hEel hEC hcard3
      (hR.le.trans inf_le_left) hQR
  have hXne : E3.wClos V 0 D.T ≠ ⊥ := by
    intro hbot
    have hVX : V ≤ E3.wClos V 0 D.T := s15_13A_le_wClos h
    exact h.pairFacts.ne_bot (le_bot_iff.1 (hVX.trans_eq hbot))
  have hX2 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le 0 D.T)
  exact normalizer_le_of_noncyclic D h61 hp hRM hR.isPGroup hRc hXne hX2 hRN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
