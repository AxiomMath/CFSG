module

public import CFSG.Permutation.FiveTransitive.PrimeCycleFixedActionNotDvd
public import CFSG.Permutation.FiveTransitive.TwoPrimeCycleCentralizer
public import CFSG.Permutation.FiveTransitive.CentralizingSingletonFixed
public import CFSG.Permutation.FiveTransitive.NormalizerGoursatNotDvd

public section

namespace CFSG

namespace FiveTransitive.ThreePrimeFourCycleObstruction

open MulAction FixedNormalizerAction

private theorem cycle_type
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    (hp : p.Prime) (g : Equiv.Perm X) (hg : orderOf g = p)
    (hn : Fintype.card X = 3 * p + 4)
    (hf : Nat.card (Function.fixedPoints g) = p + 4) : g.cycleType = {p,p} := by
  have hs : g.support.card = 2 * p := by
    rw [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints, g.sum_cycleType, hn] at hf
    have hle := Finset.card_le_univ g.support
    rw [hn] at hle
    omega
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rwa [hg])
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, hg, hs] at hsum
  have hk2 : k + 1 = 2 := (Nat.mul_right_cancel hp.pos hsum)
  rw [hk, hg, hk2]
  simp

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    (hp : p.Prime) (hp17 : 17 ≤ p)
    (P : Subgroup (Equiv.Perm X)) (hn : Fintype.card X = 3 * p + 4)
    (h5 : IsMultiplyPretransitive P X 5)
    (u : P) (hu : orderOf u = p)
    (hf : Nat.card (Function.fixedPoints u.val) = p + 4)
    [Fintype (Fixed (X := X) (Subgroup.zpowers u))]
    (hAlt : alternatingGroup (Fixed (X := X) (Subgroup.zpowers u)) ≤
      Image (X := X) (Subgroup.zpowers u)) : alternatingGroup X ≤ P := by
  classical
  let Q := Subgroup.zpowers u
  let F := Fixed (X := X) Q
  let r : Q := ⟨u, Subgroup.mem_zpowers u⟩
  have hfixed : (F : Set X) = Function.fixedPoints u.val := by
    change Fixed (X := X) Q = _
    rw [fixed_eq]
    exact CentralizingSingletonFixed.fixed_zpowers u
  have hF : Fintype.card F = p + 4 := by
    rw [← Nat.card_eq_fintype_card, hfixed]
    exact hf
  have hQcard : Nat.card Q = p := (Nat.card_zpowers u).trans hu
  have hAut : Nat.card (MulAut Q) = p - 1 := by
    rw [IsCyclic.card_mulAut Q, hQcard, Nat.totient_prime hp]
  have htype := cycle_type hp u.val ((Subgroup.orderOf_coe u).trans hu) hn hf
  let g := u.val
  let gs : Equiv.Perm g.support := g.subtypePerm (fun _ => g.apply_mem_support)
  have hgs : Equiv.Perm.ofSubtype gs = g := Equiv.Perm.ofSubtype_subtypePerm
    (fun _ => g.apply_mem_support) (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgst : gs.cycleType = {p,p} := by
    rw [← Equiv.Perm.cycleType_ofSubtype, hgs]
    exact htype
  have hgsn : Fintype.card g.support = 2 * p := by
    rw [Fintype.card_coe, ← g.sum_cycleType, htype]
    simp [Nat.two_mul]
  have hcent : Nat.card (Subgroup.centralizer ({gs} : Set (Equiv.Perm g.support))) =
      2 * p ^ 2 := TwoPrimeCycleCentralizer.double_cycle_centralizer_card p hgsn hgst
  apply NormalizerGoursatNotDvd.alternatingGroup_le_of_fixed_action_of_two_not_dvd
    X P (by omega) (by
      intro a b ha hb
      obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
      exact ⟨g,fun i => DFunLike.congr_fun hg i⟩) Q r hfixed (by rw [hF]; omega) hAlt
  · change ¬ Nat.card (alternatingGroup F) ∣ Nat.card Q.normalizerMonoidHom.range
    intro hd
    apply PrimeCycleFixedActionNotDvd.alternating_card_not_dvd_pred_of_lt_fixed_card
      F (by rw [hF]; omega) hp (by rw [hF]; omega)
    exact hd.trans (hAut ▸ Subgroup.card_subgroup_dvd_card Q.normalizerMonoidHom.range)
  · change ¬ Nat.card (alternatingGroup F) ∣
      Nat.card (Subgroup.centralizer ({gs} : Set (Equiv.Perm g.support)))
    rw [hcent]
    have hFnt : 1 < Nat.card F := by rw [Nat.card_eq_fintype_card,hF]; omega
    let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp hFnt
    have hthree : 3 ∣ Nat.card (alternatingGroup F) := by
      have h6 : 6 ∣ (Fintype.card F).factorial := Nat.dvd_factorial (by norm_num) (by rw [hF]; omega)
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
      obtain ⟨k,hk⟩ := h6
      refine ⟨k, ?_⟩
      rw [hk]
      omega
    intro hd
    have hp3 : ¬ 3 ∣ p := by intro h; have := (Nat.dvd_prime hp).mp h; omega
    rcases Nat.prime_three.dvd_mul.mp (hthree.trans hd) with h | h
    · norm_num at h
    · exact hp3 (Nat.prime_three.dvd_of_dvd_pow h)

end FiveTransitive.ThreePrimeFourCycleObstruction

end CFSG
