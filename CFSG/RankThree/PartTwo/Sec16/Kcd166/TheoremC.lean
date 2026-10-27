module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.CaseA
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.CaseB
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.MonomialSix
public import CFSG.RankThree.PartTwo.Sec4.Item420
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG CFSG.RankThree.PartTwo

private lemma exists_minimal_noncentral_normal {Γ : Type*} [Group Γ] [Finite Γ]
    {K P : Subgroup Γ} (hPn : P.Normal) (hPK : P ≤ K)
    (hPZ : ¬ P ≤ Subgroup.center Γ) :
    ∃ Q : Subgroup Γ, Q.Normal ∧ Q ≤ K ∧ Q ≤ P ∧ ¬ Q ≤ Subgroup.center Γ ∧
      ∀ R : Subgroup Γ, R.Normal → R < Q → R ≤ Subgroup.center Γ := by
  classical
  obtain ⟨Q, hQ, hQmin⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup.exists_minimal_subgroup
      (fun Q : Subgroup Γ => Q.Normal ∧ Q ≤ P ∧ ¬ Q ≤ Subgroup.center Γ)
      ⟨P, hPn, le_rfl, hPZ⟩
  obtain ⟨hQn, hQP, hQZ⟩ := hQ
  refine ⟨Q, hQn, hQP.trans hPK, hQP, hQZ, ?_⟩
  intro R hRn hRQ
  by_contra hRZ
  have hRQle : R ≤ Q := hRQ.le
  have hReq : R = Q := hQmin R ⟨hRn, hRQle.trans hQP, hRZ⟩ hRQle
  exact hRQ.ne hReq

theorem ker_le_center_of_finrank_le_nine {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] {p : ℕ}
    [CharP 𝕜 p] (hp : p.Prime) (hp5 : 5 ≤ p)
    {Γ : Type*} [Group Γ] [Finite Γ] (hperf : Group.IsPerfect Γ)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank 𝕜 V ≤ 9)
    {T : Type} [Group T] (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hker3 : Nat.Coprime (Nat.card π.ker) 3) (hkerS : Group.IsSolvable π.ker)
    (hr3 : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3) :
    π.ker ≤ Subgroup.center Γ := by
  classical
  haveI : π.ker.Normal := MonoidHom.normal_ker π
  by_contra hker
  obtain ⟨r, hr, P, hPn, hPD, hPr, hPZ⟩ :=
    Sec4.exists_noncentral_normal_pSubgroup (G := Γ) π.ker hkerS hker
  obtain ⟨Q, hQn, hQD, hQP, hQZ, hQmin⟩ :=
    exists_minimal_noncentral_normal (K := π.ker) hPn hPD hPZ
  have hQr : IsPGroup r Q := hPr.to_le hQP
  have h2 : (2 : 𝕜) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : 𝕜) = 0 := by exact_mod_cast h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff 𝕜 p 2).1 h0'
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  by_cases hQc : IsMulCommutative Q
  · obtain ⟨W, σ, hW1, hWind, hWtop, hσW, hσ⟩ :=
      exists_six_lines hp hperf ρ hirr hfaith hdim π hπ hT hkerS hr hQn hQr hQc hQZ
    exact false_of_monomial_six h2 ρ hfaith W hW1 hWind hWtop σ hσW hσ hr3
  · exact false_of_nonabelian_minimal hp hp5 hperf ρ hirr hfaith hdim π hπ hT hker3 hkerS
      hr3 hr hQn hQD hQr hQc hQmin

end CFSG.RankThree.PartTwo.Sec16.Kcd166
