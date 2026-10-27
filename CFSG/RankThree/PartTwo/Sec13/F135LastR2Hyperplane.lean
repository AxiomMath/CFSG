module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

theorem r2b_card_eq_p {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {A Z : Subgroup G} (hAcard : Nat.card A = p ^ 2) (hZA : Z ≤ A) (hZ : Z ≠ ⊥)
    (hle : Nat.card Z ≤ p) : Nat.card Z = p := by
  have hdvd : Nat.card Z ∣ p ^ 2 := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le hZA
  obtain ⟨k, hk, hkZ⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
  have hp2 : 2 ≤ p := hp.out.two_le
  interval_cases k
  · have h1 : Nat.card Z = 1 := by rw [hkZ, pow_zero]
    exact absurd (Subgroup.eq_bot_of_card_eq Z h1) hZ
  · rw [hkZ, pow_one]
  · exfalso
    rw [hkZ] at hle
    nlinarith

theorem r2b_card_map {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    {A : Subgroup G} (hAcard : Nat.card A = p ^ 2) (B : Subgroup A) (hB : B.index = p) :
    Nat.card (B.map A.subtype) = p := by
  have h3 : Nat.card B * B.index = Nat.card A := B.card_mul_index
  rw [hB, hAcard, sq] at h3
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact Nat.eq_of_mul_eq_mul_right hp.out.pos h3

theorem r2b_le_centralizer_of_hyperplanes {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {A R W : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRp : ¬ p ∣ Nat.card R)
    (h : ∀ Y : Subgroup G, Y ≤ A → Nat.card Y = p →
      W ≤ Subgroup.centralizer ((R ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G)) :
    W ≤ Subgroup.centralizer (R : Set G) := by
  classical
  haveI : Nontrivial A := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    have hp2 : 2 ≤ p := hp.out.two_le
    rw [hAcard]
    nlinarith
  haveI : IsElementaryAbelian p A :=
    { is_comm := hA.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hA.2 x x.2) }
  letI : Subgroup.Normalizes A R := ⟨hAR⟩
  have hgen : ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B R = ⊤ :=
    CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := R) hRp
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B R) ≤
      (Subgroup.centralizer (W : Set G)).comap R.subtype := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro w hw
    have hxY : (x : G) ∈ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨b, hb, rfl⟩
      have hb' := congrArg Subtype.val (hx ⟨b, hb⟩)
      change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at hb'
      calc (b : G) * (x : G) = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
        _ = (x : G) * (b : G) := by rw [hb']
    have hxR : (x : G) ∈ (R ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) :
        Subgroup G) := ⟨x.2, hxY⟩
    have hc := Subgroup.mem_centralizer_iff.mp
      (h (B.map A.subtype) (Subgroup.map_subtype_le B) (r2b_card_map hAcard B hB) hw) (x : G) hxR
    exact hc.symm
  rw [hgen] at hle
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.mem_comap.mp (hle (Subgroup.mem_top (⟨r, hr⟩ : R)))) w hw).symm

theorem exists_hyperplane_not_in_frattini {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A Φ R : Subgroup G) (hA : CFSG.Open.IsElemAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (hAΦ : Nat.card (A ⊓ Φ : Subgroup G) ≤ p) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRp : ¬ p ∣ Nat.card R)
    (hfaith : ∀ Z : Subgroup G, Z ≤ A → Z ≠ ⊥ → ¬ Z ≤ Subgroup.centralizer (R : Set G)) :
    ∃ Y : Subgroup G, Y ≤ A ∧ Nat.card Y = p ∧ ¬ Y ≤ Φ ∧
      ¬ A ≤ Subgroup.centralizer ((R ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  classical
  by_contra hcon
  have hcon' : ∀ Y : Subgroup G, Y ≤ A → Nat.card Y = p → ¬ Y ≤ Φ →
      A ≤ Subgroup.centralizer ((R ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
    intro Y hYA hYc hYΦ
    by_contra hne
    exact hcon ⟨Y, hYA, hYc, hYΦ, hne⟩
  rcases eq_or_ne (A ⊓ Φ : Subgroup G) ⊥ with hZ | hZ
  ·
    have hA_gen : A ≤ Subgroup.centralizer (R : Set G) := by
      refine r2b_le_centralizer_of_hyperplanes hA hAcard hAR hRp ?_
      intro Y hYA hYc
      refine hcon' Y hYA hYc ?_
      intro hYΦ
      have hYbot : Y ≤ A ⊓ Φ := le_inf hYA hYΦ
      rw [hZ] at hYbot
      have hY1 : Y = ⊥ := le_bot_iff.mp hYbot
      rw [hY1, Subgroup.card_bot] at hYc
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      omega
    have hAne : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hAcard
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      nlinarith
    exact hfaith A le_rfl hAne hA_gen
  ·
    have hZp : Nat.card (A ⊓ Φ : Subgroup G) = p :=
      r2b_card_eq_p hAcard (inf_le_left : (A ⊓ Φ : Subgroup G) ≤ A) hZ hAΦ
    have hZ_gen : A ⊓ Φ ≤ Subgroup.centralizer (R : Set G) := by
      refine r2b_le_centralizer_of_hyperplanes hA hAcard hAR hRp ?_
      intro Y hYA hYc
      by_cases hYΦ : Y ≤ Φ
      · have hYeq : Y = A ⊓ Φ :=
          Subgroup.eq_of_le_of_card_ge (le_inf hYA hYΦ) (hZp.trans hYc.symm).le
        rw [hYeq]
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : x ∈ Subgroup.centralizer ((A ⊓ Φ : Subgroup G) : Set G) :=
          (Subgroup.mem_inf.mp (SetLike.mem_coe.mp hx)).2
        exact ((Subgroup.mem_centralizer_iff.mp hx') z hz).symm
      · exact le_trans (inf_le_left : (A ⊓ Φ : Subgroup G) ≤ A) (hcon' Y hYA hYc hYΦ)
    exact hfaith (A ⊓ Φ) (inf_le_left : (A ⊓ Φ : Subgroup G) ≤ A) hZ hZ_gen

end CFSG.RankThree.PartTwo.Sec13.F135Last
