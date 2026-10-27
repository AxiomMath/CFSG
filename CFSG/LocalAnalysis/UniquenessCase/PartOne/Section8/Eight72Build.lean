module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Sz
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Orbit
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Pair
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Coprime
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99InnerFour
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 calC)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (SuzukiModel)

variable {G : Type} [Group G] [Finite G]

private theorem eight72_rhoL_eq_one_of_centralizesBar {K : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (K : Set G)) (hx : UC22.CentralizesBar x K) :
    UC6S846.rhoL K ⟨x, hxN⟩ = 1 := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H l =>
    rw [MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff K ⟨x, hxN⟩ l).2 (hx.2 l l.2)

private theorem eight72_exists_fixed_of_centralizesBar {K B : Subgroup G}
    (hBN : B ≤ normalizer (K : Set G)) (hcent : ∀ b ∈ B, UC22.CentralizesBar b K)
    (h5 : 5 ∣ Nat.card (Bar2 K)) :
    ∃ V : Subgroup (Bar2 K), Nat.card V = 5 ∧
      ∀ b (hb : b ∈ B), ∀ v ∈ V, UC6S846.rhoL K ⟨b, hBN hb⟩ v = v := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := Bar2 K) 5 (n := 1)
    (by simpa using h5)
  refine ⟨V, by simpa using hV, ?_⟩
  intro b hb v _hv
  rw [eight72_rhoL_eq_one_of_centralizesBar (hBN hb) (hcent b hb)]
  rfl

private theorem eight72_inner_centralizes {D : Data G} {p : ℕ}
    (hpp : p.Prime) (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p D.M)
    {L K : Subgroup G} (hLN : D.M ≤ normalizer (L : Set G)) (hKL : K ≤ L)
    (hK : K ∈ calC D.M) {f : ℕ} (hKS : SuzukiModel (Bar2 K) 2 f)
    (hKZ : center (Bar2 K) = ⊥) (hpL : CFSG.Open.pRank p L ≤ 1)
    (hpbar : p ∣ Nat.card (Bar2 K)) {A₀ : Subgroup G} (hA₀M : A₀ ≤ D.M)
    (hA₀el : IsElemAbelian p A₀) (hA₀card : Nat.card A₀ = p ^ 3) :
    ∃ (B : Subgroup G) (hBN : B ≤ normalizer (K : Set G)) (V : Subgroup (Bar2 K)),
      B ≤ A₀ ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧ Nat.card V = 5 ∧
        ∀ b (hb : b ∈ B), ∀ v ∈ V, UC6S846.rhoL K ⟨b, hBN hb⟩ v = v := by
  classical
  have : Fact p.Prime := ⟨hpp⟩
  have hMN : D.M ≤ normalizer (K : Set G) := by
    intro g hg
    by_contra hgN
    have hgM : D.M.map (MulAut.conj g).toMonoidHom = D.M :=
      UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hg)
    have hKg : K.map (MulAut.conj g).toMonoidHom ∈ calC D.M :=
      UC6S846.calC_map D.M (MulAut.conj g) hgM hK
    have hKgne : K ≠ K.map (MulAut.conj g).toMonoidHom := fun h =>
      hgN (UC6S846.mem_normalizer_iff_map_conj.2 h.symm)
    have hKgL : K.map (MulAut.conj g).toMonoidHom ≤ L := by
      have hLg : L.map (MulAut.conj g).toMonoidHom = L :=
        UC6S846.mem_normalizer_iff_map_conj.1 (hLN hg)
      rw [← hLg]
      exact Subgroup.map_mono hKL
    have hdvdK : p ∣ Nat.card K :=
      hpbar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))
    have hdvdKg : p ∣ Nat.card (K.map (MulAut.conj g).toMonoidHom) := by
      have hbar : Nat.card (Bar2 (K.map (MulAut.conj g).toMonoidHom)) =
          Nat.card (Bar2 K) := by
        let e : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) :=
          Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective
        exact (Nat.card_congr (UC6S846.bar2Equiv e).toEquiv).symm
      have hbar' : p ∣ Nat.card (Bar2 (K.map (MulAut.conj g).toMonoidHom)) := by
        rw [hbar]
        exact hpbar
      exact hbar'.trans
        (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(K.map (MulAut.conj g).toMonoidHom)))
    have h2le := eight72_two_le_pRank_sup hK hKg hKgne hKZ hpp hp2 hdvdK hdvdKg
    have hmono := CFSG.SectionRank.pRank_mono hpp.one_lt
      (show K ⊔ K.map (MulAut.conj g).toMonoidHom ≤ L from sup_le hKL hKgL)
    omega
  have hOp : UC22.F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hpp hsp
  have hcomm : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 K),
      a * b = b * a :=
    r899_outer_comm_Sz (eight72_isSz_of_suzukiModel hKS)
  obtain ⟨C, hCA₀, hCcent, hCcard⟩ :=
    r899_exists_centralizesBar_of_inner hpp hp2 hKZ
      (fun Q hQ => eight72_card_le_of_isElemAbelian hKS hpp hp2 Q hQ)
      hA₀el (fun b hb => hMN (hA₀M hb))
      (fun b hb => r899_inner_of_le_normalizer hMN hpp hOp hcomm (hA₀M hb) (hA₀el.2 b hb))
  have hCel : IsElemAbelian p C := hA₀el.mono hCA₀
  have hpc : p ^ 2 ≤ Nat.card C := by
    have h := hCcard
    rw [hA₀card, show p ^ 3 = p * p ^ 2 by ring] at h
    exact Nat.le_of_mul_le_mul_left h hpp.pos
  obtain ⟨B, hBC, hBel, hBcard⟩ := UC6S846.exists_card_p_sq hpp hCel hpc
  have hBA₀ : B ≤ A₀ := hBC.trans hCA₀
  have hBN : B ≤ normalizer (K : Set G) := hBA₀.trans (fun b hb => hMN (hA₀M hb))
  obtain ⟨V, hVcard, hVfix⟩ :=
    eight72_exists_fixed_of_centralizesBar hBN (fun b hb => hCcent b (hBC hb))
      (eight72_five_dvd_of_suzukiModel hKS)
  exact ⟨B, hBN, V, hBA₀, hBel, hBcard, hVcard, hVfix⟩

theorem eight72_exists_B {D : Data G} (hSg : UC6S846.SigmaStd D)
    {p : ℕ} (hpσ : p ∈ D.sig) (hsp : IsStronglyPEmbedded p D.M) (hp5 : p ≠ 5)
    {L K₁ K₂ : Subgroup G} (hLN : D.M ≤ normalizer (L : Set G)) (h3L : ¬ 3 ∣ Nat.card L)
    (h₁ : K₁ ∈ calC D.M) (h₂ : K₂ ∈ calC D.M) (hne : K₁ ≠ K₂) (hK₁L : K₁ ≤ L) (hK₂L : K₂ ≤ L)
    (hZ₁ : center (Bar2 K₁) = ⊥) (hZ₂ : center (Bar2 K₂) = ⊥) {f₁ f₂ : ℕ}
    (hS₁ : SuzukiModel (Bar2 K₁) 2 f₁) (hS₂ : SuzukiModel (Bar2 K₂) 2 f₂)
    (hpL : CFSG.Open.pRank p L ≤ 1) (h5 : CFSG.Open.pRank 5 D.M ≤ 3) :
    ∃ B : Subgroup G, B ≤ D.M ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧
      ∃ (hBN₁ : B ≤ normalizer (K₁ : Set G)) (hBN₂ : B ≤ normalizer (K₂ : Set G)),
        (∃ V₁ : Subgroup (Bar2 K₁), Nat.card V₁ = 5 ∧
          ∀ b (hb : b ∈ B), ∀ v ∈ V₁, UC6S846.rhoL K₁ ⟨b, hBN₁ hb⟩ v = v) ∧
        (∃ V₂ : Subgroup (Bar2 K₂), Nat.card V₂ = 5 ∧
          ∀ b (hb : b ∈ B), ∀ v ∈ V₂, UC6S846.rhoL K₂ ⟨b, hBN₂ hb⟩ v = v) := by
  classical
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨A₀, hA₀M, hA₀el, hA₀card⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hSg.three_le p hpσ)
  have hK₁M : K₁ ≤ D.M := UC22.uc22p22a_le_of_isSubnormal h₁.1
  have hK₂M : K₂ ≤ D.M := UC22.uc22p22a_le_of_isSubnormal h₂.1
  have h3K₁ : ¬ 3 ∣ Nat.card (Bar2 K₁) := by
    intro h
    refine h3L (h.trans ?_)
    exact (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₁)).trans
      (Subgroup.card_dvd_of_le hK₁L)
  have h3K₂ : ¬ 3 ∣ Nat.card (Bar2 K₂) := by
    intro h
    refine h3L (h.trans ?_)
    exact (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₂)).trans
      (Subgroup.card_dvd_of_le hK₂L)
  have h5bar₁ : 5 ∣ Nat.card (Bar2 K₁) := eight72_five_dvd_of_suzukiModel hS₁
  have h5bar₂ : 5 ∣ Nat.card (Bar2 K₂) := eight72_five_dvd_of_suzukiModel hS₂
  have h5K₁ : 5 ∣ Nat.card K₁ :=
    h5bar₁.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₁))
  have h5K₂ : 5 ∣ Nat.card K₂ :=
    h5bar₂.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₂))
  obtain ⟨X₁, hX₁K₁, hX₁card⟩ : ∃ X : Subgroup G, X ≤ K₁ ∧ Nat.card X = 5 := by
    obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K₁) 5 (n := 1)
      (by simpa using h5K₁)
    refine ⟨V.map K₁.subtype, Subgroup.map_subtype_le V, ?_⟩
    rw [Subgroup.card_map_of_injective K₁.subtype_injective]
    simpa using hV
  obtain ⟨X₂, hX₂K₂, hX₂card⟩ : ∃ X : Subgroup G, X ≤ K₂ ∧ Nat.card X = 5 := by
    obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K₂) 5 (n := 1)
      (by simpa using h5K₂)
    refine ⟨V.map K₂.subtype, Subgroup.map_subtype_le V, ?_⟩
    rw [Subgroup.card_map_of_injective K₂.subtype_injective]
    simpa using hV
  have hZ₁' : ¬ 5 ∣ Nat.card (center (Bar2 K₁)) := by
    rw [hZ₁, Subgroup.card_bot]
    exact Nat.prime_five.not_dvd_one
  have hZ₂' : ¬ 5 ∣ Nat.card (center (Bar2 K₂)) := by
    rw [hZ₂, Subgroup.card_bot]
    exact Nat.prime_five.not_dvd_one
  by_cases hp3 : p = 3
  ·
    subst p
    have hA₀exp3 : ∀ a ∈ A₀, a ^ 3 = 1 := hA₀el.2
    have hinf9 : 9 ≤ Nat.card ↥(A₀ ⊓ normalizer (K₁ : Set G)) := by
      have h := eight72_card_le_three_mul h₁ hA₀M hA₀exp3 (r := 5) Nat.prime_five
        (by norm_num) hX₁K₁ hX₁card hZ₁' h5
      rw [hA₀card] at h
      have h27 : 3 * 9 ≤ 3 * Nat.card ↥(A₀ ⊓ normalizer (K₁ : Set G)) := by
        simpa using h
      exact Nat.le_of_mul_le_mul_left h27 (by norm_num)
    have hAelinf : IsElemAbelian 3 (A₀ ⊓ normalizer (K₁ : Set G)) :=
      hA₀el.mono inf_le_left
    obtain ⟨B, hBinf, hBel, hBcard⟩ :=
      UC6S846.exists_card_p_sq (p := 3) Nat.prime_three hAelinf (by simpa using hinf9)
    have hBM : B ≤ D.M := (hBinf.trans inf_le_left).trans hA₀M
    have hBN₁ : B ≤ normalizer (K₁ : Set G) := hBinf.trans inf_le_right
    have hBN₂ : B ≤ normalizer (K₂ : Set G) := by
      intro b hb
      have hbodd : Odd (orderOf b) :=
        Odd.of_dvd_nat (by norm_num) (orderOf_dvd_of_pow_eq_one (hBel.2 b hb))
      exact eight72_mem_normalizer_of_odd h₁ h₂ hne (hA₀M (hBinf hb).1) hbodd (hBN₁ hb)
        Nat.prime_five (by norm_num) hX₁K₁ hX₂K₂ hX₁card hX₂card hZ₁' hZ₂' h5
    obtain ⟨V₁, hV₁card, hV₁fix⟩ :=
      eight72_exists_fixed_of_coprime hBN₁ Nat.prime_three hBel.isPGroup h3K₁
        Nat.prime_five (by norm_num) h5bar₁
        (fun S => eight72_sylow_isCyclic_of_suzukiModel hS₁ (r := 5) (by norm_num) S)
    obtain ⟨V₂, hV₂card, hV₂fix⟩ :=
      eight72_exists_fixed_of_coprime hBN₂ Nat.prime_three hBel.isPGroup h3K₂
        Nat.prime_five (by norm_num) h5bar₂
        (fun S => eight72_sylow_isCyclic_of_suzukiModel hS₂ (r := 5) (by norm_num) S)
    exact ⟨B, hBM, hBel, hBcard, hBN₁, hBN₂,
      ⟨V₁, hV₁card, hV₁fix⟩, ⟨V₂, hV₂card, hV₂fix⟩⟩
  ·
    have hpodd : Odd p := hpp.odd_of_ne_two hp2
    have hp6 : Nat.Coprime p 6 := by
      have h2 : Nat.Coprime p 2 := hpodd.coprime_two_right
      have h3 : Nat.Coprime p 3 := by
        rw [hpp.coprime_iff_not_dvd]
        intro hd
        rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
        · exact hpp.ne_one h
        · exact hp3 h
      have hm := h2.mul_right h3
      simpa using hm
    have hp4 : Nat.Coprime p 4 := by
      have hm := hpodd.coprime_two_right.pow_right 2
      simpa using hm
    have hA₀N₁ : A₀ ≤ normalizer (K₁ : Set G) := by
      intro a ha
      have hdvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hA₀el.2 a ha)
      have hcop : Nat.Coprime (orderOf a) 6 := by
        rcases (Nat.dvd_prime hpp).1 hdvd with h | h
        · rw [h]; decide
        · rw [h]; exact hp6
      exact eight72_mem_normalizer_of_coprime_six h₁ (hA₀M ha) hcop Nat.prime_five
        (by norm_num) hX₁K₁ hX₁card hZ₁' h5
    have hA₀N₂ : A₀ ≤ normalizer (K₂ : Set G) := by
      intro a ha
      have hdvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hA₀el.2 a ha)
      have hcop : Nat.Coprime (orderOf a) 6 := by
        rcases (Nat.dvd_prime hpp).1 hdvd with h | h
        · rw [h]; decide
        · rw [h]; exact hp6
      exact eight72_mem_normalizer_of_coprime_six h₂ (hA₀M ha) hcop Nat.prime_five
        (by norm_num) hX₂K₂ hX₂card hZ₂' h5
    have hnotboth : ¬ (p ∣ Nat.card (Bar2 K₁) ∧ p ∣ Nat.card (Bar2 K₂)) := by
      rintro ⟨hd₁, hd₂⟩
      have hdK₁ : p ∣ Nat.card K₁ :=
        hd₁.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₁))
      have hdK₂ : p ∣ Nat.card K₂ :=
        hd₂.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₂))
      have h2le := eight72_two_le_pRank_sup h₁ h₂ hne hZ₁ hpp hp2 hdK₁ hdK₂
      have hmono := CFSG.SectionRank.pRank_mono hpp.one_lt
        (show K₁ ⊔ K₂ ≤ L from sup_le hK₁L hK₂L)
      omega
    by_cases hd₁ : p ∣ Nat.card (Bar2 K₁)
    ·
      obtain ⟨B, hBN₁, V₁, hBA₀, hBel, hBcard, hV₁card, hV₁fix⟩ :=
        eight72_inner_centralizes hpp hp2 hsp hLN hK₁L h₁ hS₁ hZ₁ hpL hd₁ hA₀M hA₀el
          hA₀card
      have hBN₂ : B ≤ normalizer (K₂ : Set G) := hBA₀.trans hA₀N₂
      obtain ⟨V₂, hV₂card, hV₂fix⟩ :=
        eight72_exists_fixed_of_coprime hBN₂ hpp hBel.isPGroup
          (fun h => hnotboth ⟨hd₁, h⟩) Nat.prime_five (by simpa using hp4) h5bar₂
          (fun S => eight72_sylow_isCyclic_of_suzukiModel hS₂ (r := 5) (by norm_num) S)
      exact ⟨B, hBA₀.trans hA₀M, hBel, hBcard, hBN₁, hBN₂,
        ⟨V₁, hV₁card, hV₁fix⟩, ⟨V₂, hV₂card, hV₂fix⟩⟩
    · by_cases hd₂ : p ∣ Nat.card (Bar2 K₂)
      ·
        obtain ⟨B, hBN₂, V₂, hBA₀, hBel, hBcard, hV₂card, hV₂fix⟩ :=
          eight72_inner_centralizes hpp hp2 hsp hLN hK₂L h₂ hS₂ hZ₂ hpL hd₂ hA₀M hA₀el
            hA₀card
        have hBN₁ : B ≤ normalizer (K₁ : Set G) := hBA₀.trans hA₀N₁
        obtain ⟨V₁, hV₁card, hV₁fix⟩ :=
          eight72_exists_fixed_of_coprime hBN₁ hpp hBel.isPGroup
            (fun h => hnotboth ⟨h, hd₂⟩) Nat.prime_five (by simpa using hp4) h5bar₁
            (fun S => eight72_sylow_isCyclic_of_suzukiModel hS₁ (r := 5) (by norm_num) S)
        exact ⟨B, hBA₀.trans hA₀M, hBel, hBcard, hBN₁, hBN₂,
          ⟨V₁, hV₁card, hV₁fix⟩, ⟨V₂, hV₂card, hV₂fix⟩⟩
      ·
        have hp23 : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hpp.pos (by norm_num)
        obtain ⟨B, hBA₀, hBel, hBcard⟩ :=
          UC6S846.exists_card_p_sq hpp hA₀el (by rw [hA₀card]; exact hp23)
        have hBN₁ : B ≤ normalizer (K₁ : Set G) := hBA₀.trans hA₀N₁
        have hBN₂ : B ≤ normalizer (K₂ : Set G) := hBA₀.trans hA₀N₂
        obtain ⟨V₁, hV₁card, hV₁fix⟩ :=
          eight72_exists_fixed_of_coprime hBN₁ hpp hBel.isPGroup hd₁ Nat.prime_five
            (by simpa using hp4) h5bar₁
            (fun S => eight72_sylow_isCyclic_of_suzukiModel hS₁ (r := 5) (by norm_num) S)
        obtain ⟨V₂, hV₂card, hV₂fix⟩ :=
          eight72_exists_fixed_of_coprime hBN₂ hpp hBel.isPGroup hd₂ Nat.prime_five
            (by simpa using hp4) h5bar₂
            (fun S => eight72_sylow_isCyclic_of_suzukiModel hS₂ (r := 5) (by norm_num) S)
        exact ⟨B, hBA₀.trans hA₀M, hBel, hBcard, hBN₁, hBN₂,
          ⟨V₁, hV₁card, hV₁fix⟩, ⟨V₂, hV₂card, hV₂fix⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
