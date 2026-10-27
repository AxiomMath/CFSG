module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217Three
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08Use
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ue
import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s217c_false_of_chev (D : Data G) (Ch : Choice2011 G) (h212 : S21_12 D Ch)
    (h869 : F08.R869N D) (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal)
    (hChev : ∀ K ∈ conjSetOf D.M L, ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsChev (BarInf K) p) : False := by
  classical
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  obtain ⟨r, hr, hr2, hr3, hrd⟩ := CFSG.exists_prime_ne_two_ne_three_dvd_two_pow_sub_one hn3
  have hmem : r ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hr, hrd⟩
  obtain ⟨b, hbB, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet hmem
  have hb3 : b ∈ CFSG.Quasithin.opResidual 3 c.B0 :=
    CFSG.Quasithin.mem_opResidual_of_coprime hbB (by
      rw [hbo]
      exact (Nat.coprime_primes hr Nat.prime_three).2 hr3)
  have hbM : b ∈ D.M := c.hBM hbB
  have hcb : ∀ K ∈ conjSetOf D.M L, CentralizesBar b K := by
    intro K hK
    obtain ⟨p, hp, hp2, hKp⟩ := hChev K hK
    have h12 := (h212 hH c₀ K (uc22p2214_calC_of_mem_conjSetOf hL hK) p hp hp2 hKp).2
    exact uc22p21d_centralizesBar_iff.2 fun k hk =>
      h12 (Subgroup.commutator_mem_commutator hb3 hk)
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have hbX : CentralizesBar b (conjClosure D.M L) := by
    refine uc22p2214_centralizesBar_conjClosure (hMX hbM) fun K hK k hk => ?_
    have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
    have h1 : b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 D.M :=
      uc22p22r_pCoreOf_le_of_isSubnormal hKC.1 ((hcb K hK).2 k hk)
    have hkX : k ∈ conjClosure D.M L := uc22s217u3a_le_conjClosure hK hk
    have h2 : b * k * b⁻¹ * k⁻¹ ∈ conjClosure D.M L :=
      (conjClosure D.M L).mul_mem ((mem_normalizer_iff.1 (hMX hbM) k).1 hkX)
        ((conjClosure D.M L).inv_mem hkX)
    exact uc22p2214_pCoreOf_inf_le hXM ⟨h1, h2⟩
  have hbc : Nat.card (zpowers b) = r := by rw [Nat.card_zpowers, hbo]
  have hXQ := uc22p21d_sup_pCore_eq hr hr2 hbc fun g hg =>
    uc22p21d_centralizesBar_of_mem_zpowers hbX hg
  have hLM : L ≤ D.M := hL.1.le
  have hnN' : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 h)
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnN'
  have hKm : L.map (MulAut.conj m).toMonoidHom ∈ conjSetOf D.M L := ⟨m, hmM, rfl⟩
  have hne : L.map (MulAut.conj m).toMonoidHom ≠ L := fun he =>
    hmN (UC6S846.mem_normalizer_iff_map_conj.2 he)
  have hLX : L ≤ conjClosure D.M L :=
    uc22s217u3a_le_conjClosure ⟨1, D.M.one_mem, by ext x; simp⟩
  have hKX : L.map (MulAut.conj m).toMonoidHom ≤ conjClosure D.M L :=
    uc22s217u3a_le_conjClosure hKm
  have hthin : ¬ F08.Thin8 (conjClosure D.M L) :=
    uc22p22u_not_thin_of_conj (uc22p22u_calC_of_le hL hLX hXM)
      (uc22p22u_calC_of_le (uc22p2214_calC_of_mem_conjSetOf hL hKm) hKX hXM) hne
      ⟨m⁻¹, by simp [uniqueFourConj]⟩ hLX hKX le_rfl
  have hAB : zpowers b ≤ c.B0 := Subgroup.zpowers_le.2 hbB
  exact s21_2 D Ch hH c₀ (zpowers b) hAB
    (h869 _ hXM hMX hprod hthin r hr hr2 (zpowers b) (hAB.trans c.hBM) hbc hXQ)

theorem uc22s217c_not_isL2_two (D : Data G) (Ch : Choice2011 G) (h212 : S21_12 D Ch)
    (h869 : F08.R869N D) (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) :
    ¬ IsL2 (Bar2 L) 2 := fun hL2 =>
  uc22s217c_false_of_chev D Ch h212 h869 hH c hn3 hL hnN fun K hK => by
    have hK2 : IsL2 (Bar2 K) 2 := by
      obtain ⟨g, -, rfl⟩ := hK
      obtain ⟨e⟩ := uc22p20d_bar2_conj g L
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2
    exact P2251h.exists_isChev (uc22p2214_calC_of_mem_conjSetOf hL hK)
      (Or.inl (P22fin.isL2Ev_of_isL2 hK2).1)

theorem uc22s217c_not_isL2Odd (D : Data G) (Ch : Choice2011 G) (h212 : S21_12 D Ch)
    (h869 : F08.R869N D) (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) : ¬ IsL2Odd (Bar2 L) q := fun hLq =>
  uc22s217c_false_of_chev D Ch h212 h869 hH c hn3 hL hnN fun K hK => by
    have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
    have hKq : IsL2Odd (Bar2 K) q := by
      obtain ⟨g, -, rfl⟩ := hK
      obtain ⟨e⟩ := uc22p20d_bar2_conj g L
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hLq
    haveI : IsSimpleGroup (Bar2 K) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hKq
    obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hKC.2.2 (uc22p21k_center_eq_bot hKC.2.2)
    exact ⟨q, hq, by omega, .PSL, 2, 1, hKq.admissible,
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm hKq⟩

@[expose] def S21_17RT2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ (L.subgroupOf D.M).Normal →
    (∀ n : ℕ, IsPowTwo n → IsL2 (Bar2 L) n → (conjSetOf D.M L).ncard ≤ 2) ∧
    (IsJ1 (Bar2 L) → (conjSetOf D.M L).ncard = 2 ∧ c.n = 3 ∧ conjClosure D.M L = Opp 7 D.M ∧
      ∀ A : Subgroup G, A ≤ L → Nat.card A = 7 → A ∈ uniqueSet D.M)

theorem s21_17RT_of_s21_17RT2 {D : Data G} {Ch : Choice2011 G} (h212 : S21_12 D Ch)
    (h869 : F08.R869N D) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h : S21_17RT2 D Ch) :
    S21_17RT D Ch := fun hH c L hL hnN =>
  ⟨(h hH c L hL hnN).1,
    fun _ => uc22s217c_not_isL2_two D Ch h212 h869 hH c (hn3 hH c) hL hnN,
    fun _ hq hq5 => uc22s217c_not_isL2Odd D Ch h212 h869 hH c (hn3 hH c) hL hnN hq hq5,
    (h hH c L hL hnN).2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
