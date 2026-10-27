module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.CGT.Timmesfeld75.OddCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

private theorem borel86_rs_odd_card_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem borel86_rs_isPerfect {Y : Type} [Group Y] {m n : ℕ} (hm : 3 < m) (hn : 1 < n)
    (hY : IsSpGp Y m n ∨ IsPSUGp Y m n) : Group.IsPerfect Y := by
  rcases hY with hSp | hU
  · obtain ⟨k, rfl, F, _, _, hF, ⟨e⟩⟩ := hSp
    haveI : Fintype F := Fintype.ofFinite F
    have h2n : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcard : 4 ≤ Fintype.card F := by
      rw [← Nat.card_eq_fintype_card, hF]
      exact le_trans (by norm_num : 4 ≤ 2 ^ 2) h2n
    obtain ⟨s, -, hs⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4) (by simpa using hcard)
    haveI : Group.IsPerfect ↥(StatedSp k F) :=
      CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp k F (Or.inl ⟨s, hs⟩)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · obtain ⟨⟨hp, -, hm3, hnq⟩, K, _, _, hK, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hU
    haveI : Fact (Nat.Prime 2) := ⟨hp⟩
    haveI : Group.IsPerfect ↥(StatedSU m (2 ^ n) K) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hm3 hnq
    haveI : Group.IsPerfect (StatedProj (StatedSU m (2 ^ n) K)) := inferInstance
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem borel86_rs_odd_card_of_isSymGp {X : Type} [Group X] [Finite X]
    (hO2 : CFSG.pCore 2 X = ⊥) (hX : Group.IsPerfect (X ⧸ Subgroup.center X)) {n' : ℕ}
    (h : IsSymGp (X ⧸ fusionOddCore X) n') : Odd (Nat.card X) := by
  have hO2' : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
    le_bot_iff.1 (hO2 ▸ CFSG.LieType.BorelTits.le_pCore 2 hN hp)
  have hoddZ : Odd (Nat.card (Subgroup.center X)) :=
    CFSG.CGT.Timmesfeld75.odd_card_center hO2'
  have hZle : Subgroup.center X ≤ fusionOddCore X := le_sSup ⟨inferInstance, hoddZ⟩
  have hle : Subgroup.center X ≤ (fusionOddCore X).comap (MonoidHom.id X) :=
    fun x hx => hZle hx
  have hmap : Function.Surjective
      (QuotientGroup.map (Subgroup.center X) (fusionOddCore X) (MonoidHom.id X) hle) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore X) y
    exact ⟨QuotientGroup.mk' (Subgroup.center X) x, by
      rw [QuotientGroup.map_mk']
      rfl⟩
  haveI : Group.IsPerfect (X ⧸ Subgroup.center X) := hX
  haveI : Group.IsPerfect (X ⧸ fusionOddCore X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.map (Subgroup.center X) (fusionOddCore X)
      (MonoidHom.id X) hle) hmap
  obtain ⟨e⟩ := h
  have hn'1 : n' ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ n' := by
      have := not_le.1 hcon
      omega
    haveI : Nontrivial (Fin n') := Fin.nontrivial_iff_two_le.2 h2
    haveI : Group.IsPerfect (Equiv.Perm (Fin n')) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    haveI : Group.IsPerfect ℤˣ :=
      Group.IsPerfect.ofSurjective (f := Equiv.Perm.sign) (Equiv.Perm.sign_surjective (Fin n'))
    haveI : Nontrivial ℤˣ := ⟨⟨-1, 1, by decide⟩⟩
    exact (Group.IsPerfect.not_isMulCommutative ℤˣ) inferInstance
  haveI : Subsingleton (Fin n') := Fintype.card_le_one_iff_subsingleton.1 (by simpa using hn'1)
  haveI : Subsingleton (Equiv.Perm (Fin n')) :=
    ⟨fun f g => Equiv.ext fun x => Subsingleton.elim _ _⟩
  haveI : Subsingleton (X ⧸ fusionOddCore X) := e.toEquiv.subsingleton
  have htop : fusionOddCore X = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)
  rw [show Nat.card X = Nat.card (fusionOddCore X) by rw [htop, Subgroup.card_top]]
  exact borel86_rs_odd_card_fusionOddCore X

end CFSG.LocalAnalysis.WeakClosure81

end
