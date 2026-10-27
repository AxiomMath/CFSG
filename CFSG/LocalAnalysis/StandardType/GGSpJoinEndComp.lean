module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem spEnd_eq_map_conj_of_component {p : ℕ} (hp : p.Prime) {x y : G} {L K : Subgroup G} (T : G)
    (hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hK : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K)
    (hzw : Subgroup.zpowers (T * x * T⁻¹) = Subgroup.zpowers y) (hpL : p ∣ Nat.card L)
    (hZ : Subgroup.center K = ⊥) {e : G} (he1 : e ≠ 1) (heK : e ∈ K)
    (heL : e ∈ L.map (MulAut.conj T).toMonoidHom) :
    K = L.map (MulAut.conj T).toMonoidHom := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hLcomp : IsComponentOf (L.map (MulAut.conj T).toMonoidHom)
      (Subgroup.centralizer ({y} : Set G)) := by
    have h := isComponentOf_map_mulEquiv' (MulAut.conj T) hL
    rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton,
      centralizer_singleton_eq_of_zpowers_eq hzw] at h
    exact h
  have hcard : Nat.card (L.map (MulAut.conj T).toMonoidHom) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj T).injective
  have hLnotle : ¬ L.map (MulAut.conj T).toMonoidHom ≤
      CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({y} : Set G)) := by
    apply not_le_lBalancePrimeCore_of_dvd
    rw [hcard]
    exact hpL
  obtain ⟨-, hKp⟩ :=
    (largeEvenPComponent_iff_lBalance p (Subgroup.centralizer ({y} : Set G)) K).1 hK
  rcases lBalanceIsPComponent_eq_or_commute hLcomp hLnotle hKp with hEq | hComm
  · exact hEq
  ·
    exfalso
    have hcent : K ≤ Subgroup.centralizer
        ((L.map (MulAut.conj T).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hComm
    have hcenter : (⟨e, heK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hcomm : (g : G) * e = e * (g : G) := by
        have hg := hcent g.2
        rw [Subgroup.mem_centralizer_iff] at hg
        exact (hg e heL).symm
      simpa using hcomm
    have hmem : (⟨e, heK⟩ : ↥K) ∈ (⊥ : Subgroup ↥K) := by
      rw [← hZ]
      exact hcenter
    have heq1 : (⟨e, heK⟩ : ↥K) = 1 := Subgroup.mem_bot.mp hmem
    exact he1 (by simpa using congrArg Subtype.val heq1)

end CFSG.StandardType
