module

public import CFSG.Quasithin.Background.SmithD39TwoBender
public import CFSG.Quasithin.Background.SmithD39TwoSz

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

theorem mp_le_of_d3Std {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) : Mp ≤ M := by
  rw [hD.hyp.Mp_eq]
  exact conjClosure_le fun s hs l hl =>
    M.mul_mem (M.mul_mem (hD.hyp.sylow.1 hs) (le_of_mem_cComp hD.hyp.comp hl))
      (M.inv_mem (hD.hyp.sylow.1 hs))

theorem mp_perfect_of_d3Std {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) : ⁅Mp, Mp⁆ = Mp := by
  have hL : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hD.hyp.quasi.1
    exact Subgroup.commutator_eq_self
  rw [hD.hyp.Mp_eq]
  exact perfect_conjClosure hL

theorem commV_mp_eq_top {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) : commV Mp = ⊤ := by
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hMn : ∀ m ∈ M, ∀ l ∈ Mp, m * l * m⁻¹ ∈ Mp := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  exact Z391.commV_eq_top hMn hVcomm hD.hyp.gen

theorem pCoreOf_two_cent_eq_bot {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) :
    pCoreOf 2 (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := pCoreOf_le_pCoreOf_of_le_normalizer 2 inf_le_left
    (le_normalizer_inf_centralizer hD.hyp.Mp_normal)
  rw [hD.hyp.pCoreOf_eq_bot] at h
  exact le_bot_iff.1 h

theorem not_three_dvd_card_of_pow {X : Subgroup (MulAut W)}
    (h3 : ∀ x ∈ X, x ^ 3 = 1 → x = 1) : ¬ 3 ∣ Nat.card ↥X := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hy3 : (y : MulAut W) ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one y
    rw [hy] at h1
    exact congrArg Subtype.val h1
  have hy1 : y = 1 := Subtype.ext (h3 _ y.2 hy3)
  rw [hy1, orderOf_one] at hy
  norm_num at hy

theorem inf_cent_eq_bot (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) {A : Subgroup (MulAut W)} {r : ℚ}
    (hr : qhatOf M = (r : WithTop ℚ)) (hr2 : r ≤ 2) (hA : A ∈ QhatStar M)
    (hOp : ∀ p : ℕ, p.Prime → 5 ≤ p → ⁅pCoreOf p M, A⁆ = ⊥)
    (h3 : ∀ x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)), x ^ 3 = 1 → x = 1) :
    A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ := by
  classical
  set C := M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) with hCdef
  set B := A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) with hBdef
  by_contra hB
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAM : A ≤ M := hA2.1
  have hBC : B ≤ C := inf_le_inf_right _ hAM
  have hB2 : IsPGroup 2 ↥B := hA2.isElemAbelian2.isPGroup.to_le inf_le_left
  have hNM := hD.hyp.Mp_normal
  have hMq := hD.hyp.qsqtk
  rcases exists_moved_piece (pCoreOf_two_cent_eq_bot hD) hBC hB2 hB hNM with
    ⟨p, hp, hp2, hpB⟩ | ⟨K, hK, hKq, hKC, hKB⟩
  · have : Fact p.Prime := ⟨hp⟩
    by_cases hp3 : p = 3
    ·
      subst hp3
      apply not_three_dvd_card_of_pow (X := pCoreOf 3 C)
        (fun x hx hx3 => h3 x (pCoreOf_le 3 C hx) hx3)
      rcases (pCoreOf_isPGroup 3 C).card_eq_or_dvd with h | h
      · exfalso
        apply hpB
        rw [Subgroup.eq_bot_of_card_eq _ h]
        exact bot_le
      · exact h
    ·
      have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · exact absurd (h ▸ hp) (by norm_num)
        · exact h
      apply hpB
      have h1 := hOp p hp hp5
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hgM := pCoreOf_le_pCoreOf_of_le_normalizer p (inf_le_left : C ≤ M)
        (le_normalizer_inf_centralizer hNM) hg
      exact (Subgroup.mem_centralizer_iff.1 (h1 hgM)) b hb.1
  ·
    have h3K : ¬ 3 ∣ Nat.card ↥K :=
      not_three_dvd_card_of_pow fun x hx hx3 => h3 x (hKC hx) hx3
    have hSz := suzukiModel_of_le_of_not_dvd hA23 hSzF hMq (hKC.trans inf_le_left) hKq h3K
    apply hKB
    exact (inf_le_left : B ≤ A).trans (sz_comp_le_centralizer h38 hD.hyp.exp hMq hNM
      (mp_le_of_d3Std hD) (mp_perfect_of_d3Std hD) (commV_mp_eq_top hD) hr hr2 hA hK hKq
      (hKC.trans inf_le_right) hSz)

end CFSG.Quasithin.SmithD321
