module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_e

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_1_f
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.1(f). -/
public theorem CFSG.lemma_12_1_f
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    subgroupCentralizerIn E₃ E = ⊥ := by
  classical
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE12, hE1, hE2, ⟨hE3E, hHallE3⟩⟩
  have hCent_le_E : subgroupCentralizerIn E₃ E ≤ E := by
    intro x hx
    exact hE3E hx.1
  let C : Subgroup E := (subgroupCentralizerIn E₃ E).subgroupOf E
  have hCcard : Nat.card C = Nat.card (subgroupCentralizerIn E₃ E) :=
    natCard_subgroupOf_eq _ _ hCent_le_E
  have hC_le_E3sub : C ≤ E₃.subgroupOf E := by
    intro x hx
    exact hx.1
  have hC_center : C ≤ Subgroup.center E := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxCent : (x : G) ∈ Subgroup.centralizer (E : Set G) := hx.2
    exact Subgroup.mem_centralizer_iff.mp hxCent (y : G) y.property
  apply Subgroup.card_eq_one.mp
  apply section12_card_eq_one_of_no_prime_dvd
  intro p hpdiv
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hpC : p.val ∣ Nat.card C := by
    rwa [hCcard]
  have hpE3 : p.val ∣ Nat.card E₃ := by
    have hCcard_sub : Nat.card C ∣ Nat.card (E₃.subgroupOf E) :=
      Subgroup.card_dvd_of_le hC_le_E3sub
    have hE3sub_card : Nat.card (E₃.subgroupOf E) = Nat.card E₃ :=
      natCard_subgroupOf_eq _ _ hE3E
    exact hpC.trans (by simpa [hE3sub_card] using hCcard_sub)
  have hpτ3 : p ∈ section12Tau3Primes M :=
    hHallE3.p_in_pi_of_p_dvd_card p
      (by simpa [natCard_subgroupOf_eq _ _ hE3E] using hpE3)
  let Q : Sylow p.val C := Classical.choice (Sylow.nonempty (p := p.val) (G := C))
  have hQ_ne_bot : (Q : Subgroup C) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := C) Q (by simpa using hpC)
  let Qmap : Subgroup E := (Q : Subgroup C).map C.subtype
  have hQmap_ne_bot : Qmap ≠ ⊥ := by
    intro hQmap_bot
    have hQ_bot : (Q : Subgroup C) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (Q : Subgroup C)) (f := C.subtype)
        C.subtype_injective).1 (by simpa [Qmap] using hQmap_bot)
    exact hQ_ne_bot hQ_bot
  have hQmap_p : IsPGroup p.val Qmap :=
    IsPGroup.map Q.isPGroup' C.subtype
  obtain ⟨P, hQmap_le_P⟩ := IsPGroup.exists_le_sylow (G := E) (p := p.val) hQmap_p
  have hnilE : Group.IsNilpotent (ambientDerivedSubgroup E) :=
    lemma_12_1_a (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) hM hEdata
  have hP_le_der : (P : Subgroup E) ≤ derivedSubgroup E :=
    section12_tau3_sylow_le_derived (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hEdata hnilE hpτ3 P
  have hpG : p.val ∣ Nat.card G :=
    hpE3.trans (Subgroup.card_subgroup_dvd_card E₃)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  have hprank : primeRank p.val E ≤ 1 := section12_tau3_primeRank_E_le_one hcomp hpτ3
  have hPcyc : IsCyclic (P : Subgroup E) :=
    section12_sylow_cyclic_of_primeRank_le_one hpodd hprank P
  have hPcenter_bot : (P : Subgroup E) ⊓ Subgroup.center E = ⊥ :=
    section12_sylow_inf_center_eq_bot_of_le_commutator P hPcyc (by
      change (P : Subgroup E) ≤ derivedSeries E 1 at hP_le_der
      rw [derivedSeries_one] at hP_le_der
      exact hP_le_der)
  have hQmap_le_center : Qmap ≤ Subgroup.center E := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact hC_center y.property
  have hQmap_le_bot : Qmap ≤ ⊥ := by
    intro x hx
    have hxinf : x ∈ (P : Subgroup E) ⊓ Subgroup.center E :=
      ⟨hQmap_le_P hx, hQmap_le_center hx⟩
    simpa [hPcenter_bot] using hxinf
  exact hQmap_ne_bot (le_bot_iff.mp hQmap_le_bot)

end Section12
