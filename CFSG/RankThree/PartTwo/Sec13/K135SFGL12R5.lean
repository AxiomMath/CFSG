module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR5
public import CFSG.RankThree.PartTwo.Sec13.K135SFFinal
public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12Defs
public import CFSG.RankThree.PartTwo.Sec13.F135LastR2
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Cube
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Data
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5H2a
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5H2b

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

theorem false_of_kf135_gl12 (hKF : K135SF.KF135GL12) {M' : Type} [Group M'] [Finite M']
    (J : Subgroup M') (hJq : CFSG.IsQuasisimple J) (hK : CFSG.IsKGroup (J ⧸ Subgroup.center J))
    (hGL : K135SF.GL12Data (J ⧸ Subgroup.center J)) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (Ē : Subgroup M') (hĒexp : ∀ e ∈ Ē, e ^ p = 1) (hĒN : Ē ≤ Subgroup.normalizer (J : Set M'))
    (hidx : p ^ 3 ≤ (Subgroup.centralizer (J : Set M') ⊓ Ē).relIndex Ē)
    (hH2a : ∀ F : Subgroup (MulAut (J ⧸ Subgroup.center J)),
      F ≤ (MulAut.conj : (J ⧸ Subgroup.center J) →* MulAut (J ⧸ Subgroup.center J)).range →
      CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
      ∀ T : Subgroup (J ⧸ Subgroup.center J), T ≠ ⊥ → IsPGroup 2 T →
        ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T) : False := by
  have hperf : Group.IsPerfect J := hJq.1
  have hSsimple : IsSimpleGroup (J ⧸ Subgroup.center J) := hJq.2.1
  have hSnonab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := hJq.2.2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0, hP0⟩ : ∃ P0 : Subgroup (MulAut (J ⧸ Subgroup.center J)),
      P0 = (Ē.subgroupOf (Subgroup.normalizer (J : Set M'))).map (actS J) := ⟨_, rfl⟩
  have hPexp : ∀ y ∈ P0, y ^ p = 1 := by
    rw [hP0]
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    have hnE : (n : M') ^ p = 1 := hĒexp _ (Subgroup.mem_subgroupOf.mp hn)
    have hn1 : n ^ p = 1 := Subtype.ext (by simpa using hnE)
    rw [← map_pow, hn1, map_one]
  have hPp : IsPGroup p P0 := r5e_isPGroup_of_exp _ hPexp
  have hP3 : p ^ 3 ≤ Nat.card P0 := by
    rw [hP0, r5e_card hperf hĒN]
    exact hidx
  exact hKF (J ⧸ Subgroup.center J) hK hSsimple hSnonab hGL p hp hp7 P0 hPp hP3 hPexp hH2a

theorem r5_holds_gl12 (hLP : Sec4.Item4_1LargePrime)
    (hTC : Sec4.Item4_1ThreeCover) (h42 : Sec4.Item4_2) (hMP : KFactMultPrime) (hKF : KF135)
    (hMPG : K135SF.KFactMultPrimeGL12) (hKFG : K135SF.KF135GL12) : R5 := by
  intro G _ _ A c L p C c5
  haveI : c5.R.Normal := c5.R_normal
  have hcrit := c5.crit
  have hp : p.Prime := hcrit.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := c5.p_ge_seven
  have hp2 : p ≠ 2 := by omega
  have hzL := c5.z_mem
  have hY : Nat.card c5.Y = p := c5.Y_card
  have hYM : c5.Y ≤ cM c5.Y := r5g_Y_le_cM hp hY
  obtain ⟨hY', hYc⟩ := r5g_Y_sub hp hY
  have hYD : c5.Y ≤ dPrime L p C c5.z := c5.Y_le.trans inf_le_left
  have hDp : IsPGroup p (dPrime L p C c5.z) := isPGroup_dPrime hcrit hzL
  have hDexp : ∀ x ∈ dPrime L p C c5.z, x ^ p = 1 := dPrime_exp hcrit hzL
  obtain ⟨hEp, hEexp, hYE, hYΦ⟩ := r5g_E_facts hDp hDexp hYD hY c5.Y_not_frattini
  have hTF : TheoremFourHyp G := c5.data.toTheoremFourHyp
  have hYne : c5.Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hY
    exact hp.one_lt.ne hY
  have hMne : cM c5.Y ≠ ⊤ := r5g_cM_ne_top hTF.isSimpleGroup hTF.nonabelian hYne
  have hSM : SectionFourHyp (cM c5.Y) := hTF.sectionFourHyp hMne
  have hJq : CFSG.IsQuasisimple c5.J := c5.J_comp.1
  have hcases : Sec4.Census.List42 (↥c5.J ⧸ Subgroup.center ↥c5.J) ∨
      (CFSG.IsKGroup (↥c5.J ⧸ Subgroup.center ↥c5.J) ∧
        K135SF.GL12Data (↥c5.J ⧸ Subgroup.center ↥c5.J)) :=
    K135SF.list42_or_gl12_of_relPPrimeCore hLP hTC h42 (cM c5.Y) hSM hp hp2 c5.R c5.R_eq c5.R_odd
      c5.R_coprime c5.J c5.J_comp
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥c5.J) := by
    rcases hcases with hList | ⟨hK, hGL⟩
    · exact hMP _ hJq hList p hp hp7
    · exact hMPG _ hJq hK hGL p hp hp7
  have hR : ¬ p ∣ Nat.card c5.R := (Nat.Prime.coprime_iff_not_dvd hp).mp c5.R_coprime
  have hlr : CFSG.Assembly.RankThreeEven.localRank p G < 3 := hTF.localRank_lt p hp (by omega)
  have hno := hno_of_localRank hp hlr (cM c5.Y)
  have hEN : (eOf (dPrime L p C c5.z) c5.Y).map (QuotientGroup.mk' c5.R) ≤
      Subgroup.normalizer (c5.J : Set (cM c5.Y ⧸ c5.R)) := by
    rintro _ ⟨e, he, rfl⟩
    exact c5.J_normE e he
  have hH2a := h2a_of_lifting hp hp2 c5.R hR (c5.Y.subgroupOf (cM c5.Y)) hY' hYc c5.J hJq.1 hZ hno
  have hH2b := h2b_of_lifting hp hp2 c5.R hR (c5.Y.subgroupOf (cM c5.Y))
    (eOf (dPrime L p C c5.z) c5.Y) hY' hYc hEp hEexp hYE hYΦ c5.J hJq.1 hZ hEN c5.E_ker hno
  have hu : c5.u ∈ cM c5.Y := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (c5.Y_le hy).2
  obtain ⟨hU2, hUf⟩ := r5g_U_facts c5.U_eq
  have hU2' : IsPGroup 2 ((c5.U.subgroupOf (cM c5.Y)).map (QuotientGroup.mk' c5.R)) :=
    (hU2.comap_subtype (K := cM c5.Y)).map _
  rcases hcases with hList | ⟨hK, hGL⟩
  · refine identified_of_kf135 hKF c5.J hJq hList hp hp7
      ((eOf (dPrime L p C c5.z) c5.Y).map (QuotientGroup.mk' c5.R))
      (((dPrime L p C c5.z ⊓ cM c5.Y ⊓ Subgroup.centralizer ({c5.u} : Set G)).subgroupOf
        (cM c5.Y)).map (QuotientGroup.mk' c5.R))
      ((c5.U.subgroupOf (cM c5.Y)).map (QuotientGroup.mk' c5.R))
      ((⟨c5.u, hu⟩ : cM c5.Y) : cM c5.Y ⧸ c5.R)
      (hEp.map _) ?_ hEN c5.E_index (c5.J_normu hu) ?_ c5.J_normU hU2' c5.U_nontrivial
      (c5.u_nontrivial hu) ?_ ?_ ?_ c5.U_comm_Eu hH2a hH2b
    ·
      rintro _ ⟨e, he, rfl⟩
      rw [← map_pow, hEexp e he, map_one]
    ·
      have h : (⟨c5.u, hu⟩ : cM c5.Y) * ⟨c5.u, hu⟩ = 1 := Subtype.ext c5.u_sq
      rw [← QuotientGroup.mk_mul, h]
      rfl
    ·
      rintro _ ⟨e, he, rfl⟩
      have he' : (e : G) ∈ dPrime L p C c5.z ⊓ cM c5.Y ⊓ Subgroup.centralizer ({c5.u} : Set G) :=
        Subgroup.mem_subgroupOf.mp he
      exact ⟨e, Subgroup.mem_subgroupOf.mpr he'.1, rfl⟩
    ·
      rintro _ ⟨e, he, rfl⟩
      have he' : (e : G) ∈ dPrime L p C c5.z ⊓ cM c5.Y ⊓ Subgroup.centralizer ({c5.u} : Set G) :=
        Subgroup.mem_subgroupOf.mp he
      have hc : e * (⟨c5.u, hu⟩ : cM c5.Y) = ⟨c5.u, hu⟩ * e :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp he'.2)
      rw [Subgroup.mem_centralizer_singleton_iff]
      show ((e : cM c5.Y) : cM c5.Y ⧸ c5.R) * ((⟨c5.u, hu⟩ : cM c5.Y) : cM c5.Y ⧸ c5.R) =
        ((⟨c5.u, hu⟩ : cM c5.Y) : cM c5.Y ⧸ c5.R) * ((e : cM c5.Y) : cM c5.Y ⧸ c5.R)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
    ·
      rintro _ ⟨e, he, rfl⟩
      exact r5g_map_normalizer c5.R _ (r5g_subgroupOf_normalizer (cM c5.Y) _ (hUf (e : G) he))
  · refine (false_of_kf135_gl12 hKFG c5.J hJq hK hGL hp hp7
      ((eOf (dPrime L p C c5.z) c5.Y).map (QuotientGroup.mk' c5.R)) ?_ hEN c5.E_index hH2a).elim
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hEexp e he, map_one]
end CFSG.RankThree.PartTwo.Sec13.F135Last
