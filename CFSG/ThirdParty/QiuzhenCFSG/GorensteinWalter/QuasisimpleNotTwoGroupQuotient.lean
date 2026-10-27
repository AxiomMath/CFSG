module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddPInvertedCentralized
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A quasisimple group cannot have a two-group odd-core quotient

The odd core is solvable by Feit--Thompson and a finite `2`-group is
solvable, so the whole group would be solvable, contradicting the
nontrivial-perfect defining property of a quasisimple group.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem quasisimple_not_quotient_isTwoGroup
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q)
    (hQ2 : IsPGroup 2 (Q ⧸ pPrimeCore 2 Q)) :
    False := by
  let O : Subgroup Q := pPrimeCore 2 Q
  have hOcop : Nat.Coprime 2 (Nat.card ↥O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := Q)
  have hOodd : Odd (Nat.card ↥O) := Nat.coprime_two_left.mp hOcop
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (Q ⧸ O) :=
    IsPGroup.isNilpotent (by simpa [O] using hQ2)
  have hQsolvQ : Group.IsSolvable (Q ⧸ O) := inferInstance
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let : Group.IsSolvable O := hOsolv
  let : Group.IsSolvable (Q ⧸ O) := hQsolvQ
  have hQsolv : Group.IsSolvable Q :=
    isSolvable_of_normal_subgroup_and_quotient O
  let : Nontrivial Q := hQ.1
  let : Group.IsPerfect Q := (Group.isPerfect_def).2 hQ.2.1
  exact Group.IsPerfect.not_isSolvable Q hQsolv

/-- A quasisimple group is not solvable. -/
public theorem quasisimple_not_solvable
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  let : Nontrivial Q := hQ.1
  let : Group.IsPerfect Q := (Group.isPerfect_def).2 hQ.2.1
  exact Group.IsPerfect.not_isSolvable Q

/-- A quasisimple group has even order. -/
public theorem quasisimple_even_card
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) :
    2 ∣ Nat.card Q := by
  classical
  let : Nontrivial Q := hQ.1
  let : Group.IsPerfect Q := (Group.isPerfect_def).2 hQ.2.1
  by_contra hnot
  have hodd : Odd (Nat.card Q) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hnot (even_iff_two_dvd.mp heven)
  have hsolv : Group.IsSolvable Q := odd_order_theorem Q hodd
  exact Group.IsPerfect.not_isSolvable Q hsolv

public theorem pPrimeCore_le_center_of_isQuasisimple
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) :
    pPrimeCore 2 Q ≤ Subgroup.center Q := by
  classical
  let O : Subgroup Q := pPrimeCore 2 Q
  let Z : Subgroup Q := Subgroup.center Q
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let : Z.Normal := by
    dsimp [Z]
    infer_instance
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let Obar : Subgroup (Q ⧸ Z) := O.map π
  have hObarNormal : Obar.Normal :=
    (inferInstance : O.Normal).map π (QuotientGroup.mk'_surjective Z)
  have hsimple : IsSimpleGroup (Q ⧸ Z) := hQ.2.2
  rcases (haveI := hObarNormal; hsimple.eq_bot_or_eq_top_of_normal Obar) with hbot | htop
  · intro x hx
    have hxmap : π x ∈ Obar := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hxmap
    have hxZ : x ∈ Z :=
      (QuotientGroup.eq_one_iff (N := Z) x).mp (Subgroup.mem_bot.mp hxmap)
    exact hxZ
  · exfalso
    have hcom : Z ⊔ O = ⊤ := by
      calc
        Z ⊔ O = Subgroup.comap π Obar :=
          (QuotientGroup.comap_map_mk' Z O).symm
        _ = Subgroup.comap π (⊤ : Subgroup (Q ⧸ Z)) := by rw [htop]
        _ = ⊤ := by simp
    have hOZ : O ⊔ Z = ⊤ := by simpa [sup_comm] using hcom
    have hleO : _root_.commutator Q ≤ O :=
      (inferInstance : O.Normal).commutator_le_of_self_sup_commutative_eq_top
        hOZ (by infer_instance)
    have hOeq : O = ⊤ := by
      rw [hQ.2.1] at hleO
      exact eq_top_iff.mpr hleO
    have hOcard : Nat.card O = Nat.card Q := by
      rw [hOeq]
      simp
    have hOodd : Odd (Nat.card O) := by
      simpa [O] using pPrimeCore_coprime_card (p := 2) (G := Q)
    have hoddQ : Odd (Nat.card Q) := by
      rwa [hOcard] at hOodd
    exact hoddQ.not_two_dvd_nat (quasisimple_even_card hQ)

public theorem oddPSubgroup_le_center_of_le_pPrimeCore_of_isQuasisimple
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (P : Subgroup Q)
    (hPleCore : P ≤ pPrimeCore 2 Q) :
    P ≤ Subgroup.center Q :=
  hPleCore.trans (pPrimeCore_le_center_of_isQuasisimple hQ)

public theorem no_inverted_oddP_of_le_pPrimeCore_of_isQuasisimple
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (X : Subgroup Q)
    (hXleCore : X ≤ pPrimeCore 2 Q)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hXp : IsPGroup p X)
    (hXne : X ≠ ⊥) {t : Q} (ht : IsInvolution t)
    (hXinv : BenderGlauberman.IsInvertedBy t X) :
    False := by
  have hXcenter : X ≤ Subgroup.center Q :=
    oddPSubgroup_le_center_of_le_pPrimeCore_of_isQuasisimple hQ X hXleCore
  have hXcent : X ≤ Subgroup.centralizer ({t} : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxcent := hXcenter hx
    exact (Subgroup.mem_center_iff.mp hxcent t).symm
  exact no_nontrivial_oddP_inverted_centralized t X hXinv hXcent hXp hpodd hXne

end CFSG.GorensteinWalter
