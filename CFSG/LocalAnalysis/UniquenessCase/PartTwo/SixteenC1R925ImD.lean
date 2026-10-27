module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Fit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Gl2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r925_im_N0 (hKSch : UCK.KSch) {Γ : Type} [Group Γ]
    [Finite Γ] {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M)
    (hA5 : IsAlt ↥(K.map (toModO3p Γ)) 5) :
    ∃ N : Subgroup Γ, N ≤ K ⊓ CFSG.pPrimeCore 3 Γ ∧ N.Normal ∧ Odd (Nat.card N) ∧
      ∀ w ∈ K ⊓ CFSG.pPrimeCore 3 Γ, ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ N := by
  classical
  let J : Subgroup Γ := CFSG.pPrimeCore 3 Γ
  let W : Subgroup Γ := K ⊓ J
  obtain ⟨ψ, hψ⟩ := r925_pcore_reps h.rank_gt_three
  haveI hKn : K.Normal := h.normal_k
  haveI hJn : J.Normal := CFSG.pPrimeCore_normal
  haveI hWn : W.Normal := Subgroup.normal_inf_normal K J
  let N : Subgroup Γ := W ⊓ ⨅ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (ψ p).ker
  haveI hiInf : (⨅ p : {p : ℕ // p.Prime ∧ 5 ≤ p}, (ψ p).ker).Normal :=
    Subgroup.normal_iInf_normal fun p => MonoidHom.normal_ker (ψ p)
  haveI hNn : N.Normal := Subgroup.normal_inf_normal W _
  have hW3 : ∀ w ∈ ((toModO3p Γ).subgroupMap K).ker, ¬ 3 ∣ orderOf w := by
    intro w hw
    have hwπ : (toModO3p Γ) (w : Γ) = 1 := by
      have hw' : w ∈ (toModO3p Γ).ker.subgroupOf K := by
        rwa [Subgroup.ker_subgroupMap] at hw
      exact Subgroup.mem_subgroupOf.mp hw'
    have hwJ : (w : Γ) ∈ J := by
      change (w : Γ) ∈ CFSG.pPrimeCore 3 Γ
      rw [← QuotientGroup.ker_mk' (N := CFSG.pPrimeCore 3 Γ)]
      exact MonoidHom.mem_ker.mpr hwπ
    rw [← Subgroup.orderOf_coe w]
    exact r925_pPrimeCore_orderOf (w : Γ) hwJ
  have hq : IsAlt (↥K ⧸ ((toModO3p Γ).subgroupMap K).ker) 5 := by
    obtain ⟨f⟩ := hA5
    exact ⟨(r925QuotEquiv (toModO3p Γ) K).trans f⟩
  refine ⟨N, ?_, hNn, ?_, ?_⟩
  · intro x hx
    have hxW : x ∈ W := (Subgroup.mem_inf.mp hx).1
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hxW).1, (Subgroup.mem_inf.mp hxW).2⟩
  · by_contra hodd
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hnord⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 hodd
    have hnord' : orderOf (n : Γ) = 2 := (Subgroup.orderOf_coe n).trans hnord
    have hnN : (n : Γ) ∈ N := n.2
    have hnW : (n : Γ) ∈ W := (Subgroup.mem_inf.mp hnN).1
    have hnK : (n : Γ) ∈ K := (Subgroup.mem_inf.mp hnW).1
    have hnJ : (n : Γ) ∈ J := (Subgroup.mem_inf.mp hnW).2
    have hcent_pCore : ∀ p : {p : ℕ // p.Prime ∧ 5 ≤ p},
        ∀ x ∈ CFSG.pCore p.1 Γ, (n : Γ) * x = x * (n : Γ) := by
      intro p x hx
      have h1 : ψ p (n : Γ) = 1 := by
        have hmem : (n : Γ) ∈ (ψ p).ker :=
          Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hnN).2 p
        exact MonoidHom.mem_ker.mp hmem
      have hp2 : ¬ p.1 ∣ orderOf (n : Γ) := by
        rw [hnord']
        intro hpdiv
        have h2 : p.1 = 2 :=
          ((Nat.dvd_prime Nat.prime_two).mp hpdiv).resolve_left p.2.1.ne_one
        omega
      exact (hψ p).1 (n : Γ) h1 hp2 x hx
    have hcentGe5 : ∀ x ∈ r925PCoreGe5 Γ, (n : Γ) * x = x * (n : Γ) := by
      have hA := r925_centralizes_pCoreGe5 (Subgroup.zpowers (n : Γ))
        (fun p hp h5 a ha x hx => by
          rw [Subgroup.mem_zpowers_iff] at ha
          obtain ⟨m, rfl⟩ := ha
          exact Commute.zpow_left (hcent_pCore ⟨p, hp, h5⟩ x hx) m)
      exact fun x hx => hA (n : Γ) (Subgroup.mem_zpowers _) x hx
    have hcentLayer : (n : Γ) ∈ centralizer (r925LayerIn J : Set Γ) := by
      have hKlayer := r925_layer_centralized hKSch h.kgroup
        (fun q hq h5 => h.rank_gt_three q hq (by omega)) h.perfect_k h.threeGen_k
      exact hKlayer hnK
    have hfit_le : r925FittingIn J ≤ r925PCoreGe5 Γ := r925_fitting_le_pCoreGe5 h.o2_eq_bot
    have hcentFit : (n : Γ) ∈ centralizer (r925FittingIn J : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => (hcentGe5 z (hfit_le hz)).symm
    have hcentFstar : (n : Γ) ∈ centralizer (Fstar J : Set Γ) := by
      rw [r925_fstar_eq_sup J, Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      rcases hz with hzF | hzL
      · exact Subgroup.mem_centralizer_iff.mp hcentFit z hzF
      · exact Subgroup.mem_centralizer_iff.mp hcentLayer z hzL
    have hmem : (n : Γ) ∈ centralizer (Fstar J : Set Γ) ⊓ J :=
      Subgroup.mem_inf.mpr ⟨hcentFstar, hnJ⟩
    have hfit : (n : Γ) ∈ r925FittingIn J := r925_centralizer_fstar_le_fitting J hmem
    have hge5 : (n : Γ) ∈ r925PCoreGe5 Γ := hfit_le hfit
    have hcop := r925_pCoreGe5_orderOf (n : Γ) hge5
    rw [hnord'] at hcop
    norm_num at hcop
  · intro w hw k hk
    have hwK : w ∈ K := (Subgroup.mem_inf.mp hw).1
    have hwJ : w ∈ J := (Subgroup.mem_inf.mp hw).2
    have hwW : w ∈ W := Subgroup.mem_inf.mpr ⟨hwK, hwJ⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hconj : k * w⁻¹ * k⁻¹ ∈ W :=
        Subgroup.mem_inf.mpr ⟨hKn.conj_mem w⁻¹ (K.inv_mem hwK) k,
          hJn.conj_mem w⁻¹ (J.inv_mem hwJ) k⟩
      simpa only [mul_assoc] using W.mul_mem hwW hconj
    · refine Subgroup.mem_iInf.mpr ?_
      intro p
      haveI : Fact p.1.Prime := ⟨p.2.1⟩
      have hgl2 := r925_gl2_of_a5 h.perfect_k ((toModO3p Γ).subgroupMap K).ker hW3 hq p.1 p.2.2
        ((ψ p).comp K.subtype)
      have hwker : w ∈ (toModO3p Γ).ker := by
        rw [QuotientGroup.ker_mk']
        exact hwJ
      have hmem : (⟨w, hwK⟩ : ↥K) ∈ ((toModO3p Γ).subgroupMap K).ker := by
        rw [Subgroup.ker_subgroupMap]
        exact Subgroup.mem_subgroupOf.mpr hwker
      rw [MonoidHom.mem_ker]
      rcases hgl2 with h1 | ⟨-, hcomm⟩
      · have h1w : ψ p w = 1 := by
          have := congrArg (fun f => f ⟨w, hwK⟩) h1
          simpa using this
        have h1k : ψ p k = 1 := by
          have := congrArg (fun f => f ⟨k, hk⟩) h1
          simpa using this
        simp [h1w, h1k]
      · have hcw : ψ p w * ψ p k = ψ p k * ψ p w := by
          have := hcomm (⟨w, hwK⟩ : ↥K) hmem (⟨k, hk⟩ : ↥K)
          simpa using this
        simp only [map_mul, map_inv]
        rw [hcw]
        group

theorem r925_im_eqTimesOdd (hKSch : UCK.KSch) {Γ : Type} [Group Γ]
    [Finite Γ] {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M)
    (hA5 : IsAlt ↥(K.map (toModO3p Γ)) 5) (hYK : Y.map (toModO3p Γ) = K.map (toModO3p Γ)) :
    EqTimesOdd Y K := by
  obtain ⟨N, hNle, hNn, hNodd, hcomm⟩ := r925_im_N0 hKSch h hA5
  have hK : K = Y ⊔ (K ⊓ CFSG.pPrimeCore 3 Γ) := by
    have := r925_eq_sup_inf_ker (toModO3p Γ) h.y_le_k hYK
    rwa [QuotientGroup.ker_mk'] at this
  have hNK : N ≤ K := hNle.trans inf_le_left
  exact ⟨N, hNK, hNn.subgroupOf K, hNodd,
    r925_eq_sup_of_commutator h.perfect_k h.y_le_k hK hNK (hNn.subgroupOf K)
      hcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
