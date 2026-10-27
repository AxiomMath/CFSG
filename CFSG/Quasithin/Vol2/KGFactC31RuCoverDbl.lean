module

public import CFSG.Quasithin.Vol2.KGFactC31RuCoverLift
public import Certificates.Certificate15024
public import Certificates.Certificate15026
public import Certificates.Certificate7257
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Faithful

public section

namespace CFSG.Quasithin.KGC31.RuCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits CFSG.Sporadic.Recognition.RuMultiplier
  CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.TwoRu CFSG.Sporadic.J4.QT
  CFSG.Sporadic.SmallF2

theorem eta_congr {G : Type*} [Group G] {u u' : ℕ → G} (c : ℕ) :
    ∀ m, (∀ j < m, u j = u' j) → eta u m c = eta u' m c
  | 0, _ => by simp [eta]
  | m + 1, h => by
    rw [eta_succ, eta_succ, eta_congr c m fun j hj => h j (by omega), h m (by omega)]

theorem exists_lifts
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {q : L →* ruP}
    (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2)
    (hker : q.ker = Subgroup.zpowers t) (hcen : Subgroup.zpowers t ≤ Subgroup.center L) :
    ∃ e n : ℕ → L, Elem e 3 ∧
      (∀ j < 2, ∀ i < 3, n j * e i * (n j)⁻¹ = eta e 3 ((tabC.getD j []).getD i 0)) ∧
      (∀ c < 8, eta e 3 c ≠ t) ∧
      (∀ k < 7, ∃ c, ((q (eta e 3 c) : ruP) : Equiv.Perm (Fin 4060)) = ruEElt k) ∧
      ((q (n 0) : ruP) : Equiv.Perm (Fin 4060)) = ruNs0 ∧
      ((q (n 1) : ruP) : Equiv.Perm (Fin 4060)) = ruNs1 := by
  have hTab : RuTabFact := Certificates.certificate15024
  have hRho : ruRhoCheck = true := Certificates.certificate15025
  have hL0 := Certificates.certificate15026
  have hc : coverChk () = true := Certificates.certificate7257
  have : IsSimpleGroup ruP := isSimpleGroup_ruP
  obtain ⟨qJ, hqJx⟩ : ∃ qJ : L →* J ruVec, ∀ x, qJ x = ruJEquivP.symm (q x) :=
    ⟨MonoidHom.comp (MulEquiv.toMonoidHom ruJEquivP.symm) q, fun _ => rfl⟩
  have hqJs : Function.Surjective qJ := fun y => by
    obtain ⟨x, hx⟩ := hq (ruJEquivP y)
    exact ⟨x, by rw [hqJx, hx, MulEquiv.symm_apply_apply]⟩
  have hkerJ : qJ.ker = Subgroup.zpowers t := by
    rw [← hker]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hqJx, MulEquiv.map_eq_one_iff]
  have hkerc : qJ.ker ≤ Subgroup.center L := hkerJ ▸ hcen
  obtain ⟨hfin, hle⟩ := card_ruCover_le hTab hL0
  have hcardL : Nat.card L = 291852288000 := by
    rw [qJ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hqJs).toEquiv,
      CFSG.Sporadic.Bridge.Ru.card_J, hkerJ, Nat.card_zpowers, ht]
  obtain ⟨φ, hφ, hcomp⟩ := CFSG.Sporadic.Recognition.CoverTransfer.exists_bijective_of_card_le
    isPresentation_ruGen ruCommW_mem_commutator (lift_ruCommW hTab) qJ hqJs hkerc (hcardL ▸ hle)
  let eqv : RuCover ≃* L := MulEquiv.ofBijective φ hφ
  let ρ : RuCover →* Equiv.Perm (Fin 16240) := ruRho' hRho
  let ψ : L →* Equiv.Perm (Fin 16240) := ρ.comp eqv.symm.toMonoidHom
  have hψe : ∀ x, ψ (φ x) = ρ x := fun x => by
    show ρ (eqv.symm (eqv x)) = ρ x
    rw [MulEquiv.symm_apply_apply]
  have hqφ : ∀ x, ((q (φ x) : ruP) : Equiv.Perm (Fin 4060)) = ruJtoP (ruπ hTab x) := by
    intro x
    have h1 : qJ (φ x) = ruπ hTab x := by rw [← MonoidHom.comp_apply, hcomp]
    have h2 : q (φ x) = ruJEquivP (qJ (φ x)) := by
      rw [hqJx, MulEquiv.apply_symm_apply]
    rw [h2, h1]
    rfl
  have hzP : ruWE ruZWord = ruP0E ^ 2 := by
    rw [pow_two, ruZWord, ruWE_append]
    rfl
  have hzP1 : ruWE ruZWord ≠ 1 := by rw [hzP]; exact ruP0E_sq_ne_one hRho
  have hzPker : ruπ hTab (ruWE ruZWord) = 1 := by rw [hzP, map_pow, ruπ_ruP0E, a_sq]
  have hφz : φ (ruWE ruZWord) = t := by
    have hmem : φ (ruWE ruZWord) ∈ qJ.ker := by
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp]
      exact hzPker
    rw [hkerJ] at hmem
    rcases eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
    · exact absurd (hφ.1 (h1.trans (map_one φ).symm)) hzP1
    · exact h1
  obtain ⟨-, -, -, -, -, h6, h7, h8, h9, h10⟩ := chk16240_parts hc
  have hE := rep_eA hc hRho
  have hN := rep_nA hc hRho
  have hP : ∀ c, Rep 16240 (prodA 16240 (eArr ()) c)
      (eta (fun i => ρ (pElt (eW.getD i []))) 3 c) := rep_prodA hE
  have hz := rep_zA hc hRho
  have hne : ∀ c < 8, eta (fun i => ρ (pElt (eW.getD i []))) 3 c ≠ ρ (ruWE ruZWord) :=
    fun c hc8 h => by
      have h1 := (eqA_iff (hP c) hz).2 h
      rw [h9 c hc8] at h1
      exact Bool.false_ne_true h1
  have hρz : ρ (ruWE ruZWord) ≠ 1 := fun h1 => hne 0 (by norm_num) (by rw [eta_zero, h1])
  have hψt : ψ t = ρ (ruWE ruZWord) := by rw [← hφz, hψe]
  have hψinj : Function.Injective ψ :=
    injective_of_ker_zpowers hq ht hker ψ (by rw [hψt]; exact hρz)
  have hψeta : ∀ c, ψ (eta (fun i => φ (pElt (eW.getD i []))) 3 c) =
      eta (fun i => ρ (pElt (eW.getD i []))) 3 c := fun c => by
    rw [map_eta]
    simp only [hψe]
  refine ⟨fun i => φ (pElt (eW.getD i [])), fun j => φ (pElt (nW.getD j [])), ⟨?_, ?_⟩, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro i hi
    apply hψinj
    rw [map_mul, map_one, hψe]
    exact eq_of_eqA (rep_compA (hE i hi) (hE i hi)) rep_idA (h7 i hi)
  · intro i hi j hj
    apply hψinj
    rw [map_mul, map_mul, hψe, hψe]
    exact eq_of_eqA (rep_compA (hE i hi) (hE j hj)) (rep_compA (hE j hj) (hE i hi))
      (h8 i hi j hj)
  · intro j hj i hi
    apply hψinj
    rw [map_mul, map_mul, map_inv, hψe, hψe, hψeta]
    have hinv := rep_inv_of_isInvA (hN j hj)
      (isInvA_of_allPermsOK h6 (by have : (nArr ()).size = 2 := rfl; omega))
    exact eq_of_eqA (rep_compA (rep_compA (hN j hj) (hE i hi)) hinv) (hP _) (h10 j hj i hi)
  · intro c hc8 h
    apply hne c hc8
    rw [← hψeta, h, hψt]
  · intro k hk
    refine ⟨eCode.getD k 0, ?_⟩
    rw [ruEElt_eq_eta hc k hk, map_eta, ← Subgroup.coe_subtype, map_eta]
    refine eta_congr _ 3 fun j hj => ?_
    simp only [Subgroup.coe_subtype]
    rw [hqφ]
    exact ruJtoP_eW hc hTab j hj
  · rw [hqφ]
    exact ruJtoP_nW0 hc hTab
  · rw [hqφ]
    exact ruJtoP_nW1 hc hTab

end CFSG.Quasithin.KGC31.RuCover

end
