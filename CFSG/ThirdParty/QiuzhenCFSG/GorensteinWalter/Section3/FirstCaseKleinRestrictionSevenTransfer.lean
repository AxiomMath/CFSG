module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinHallCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionFive
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinReflectionExists
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem card_ne_one_of_ne_bot_local
    {G : Type u} [Group G] [Finite G]
    (X : Subgroup G) (hXne : X ≠ ⊥) : Nat.card X ≠ 1 := by
  intro hcard
  exact hXne (Subgroup.eq_bot_of_card_eq X hcard)

private theorem involution_of_order_two_local
    {G : Type u} [Group G] (x : G) (hx : orderOf x = 2) :
    IsInvolution x := by
  refine ⟨?_, ?_⟩
  · intro hx1
    rw [hx1, orderOf_one] at hx
    omega
  · rw [← hx]
    exact pow_orderOf_eq_one x

private theorem conjugate_subgroup_card_local
    {G : Type u} [Group G] [Finite G]
    (X : Subgroup G) (g : G) :
    Nat.card (conjugateSubgroup X g) = Nat.card X := by
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv.symm

public theorem firstCase_klein_restrictionSeven_transfer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hyJ : y ∈ firstCaseJ c n)
    (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    :
    ∃ g : G, ∃ L : Subgroup G,
      IsHallIn L c.FU ∧ L ≠ ⊥ ∧
        conjugateSubgroup X g ≤ L ∧
        g ∉ c.Hhat ∧
        Subgroup.normalizer (conjugateSubgroup X g : Set G) ≤ c.Hhat ∧
        c.FU ≤ Subgroup.centralizer
          (conjugateSubgroup X g : Set G) := by
  classical
  have hyJ' : IsInvolution y ∧ y ∉ c.Hhat ∧
      firstCaseCosetInvolutions c y = n := by
    simpa [firstCaseJ] using hyJ
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr, hrV⟩ :=
    firstCase_klein_exists_reflection_not_mem_twoCore hmin c hfirst hklein
  obtain ⟨L, hLr, hLHall, hLne, hLall⟩ :=
    firstCase_klein_commutator_centralizes_fitting hmin c hfirst hklein
      r hr hrV
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  have h2dvd : 2 ∣ Nat.card C := even_iff_two_dvd.mp hC_even
  obtain ⟨aC, haCorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) 2 h2dvd
  let a : G := (aC : G)
  have haorder : orderOf a = 2 := by
    simpa [a] using (Subgroup.orderOf_coe aC).trans haCorder
  have haI : IsInvolution a := involution_of_order_two_local a haorder
  have haCent : a ∈ C := aC.2
  obtain ⟨g, hga⟩ :=
    fact_2_preamble_involutions_conjugate hmin a c.t haI c.t_involution
  let Xg : Subgroup G := conjugateSubgroup X g
  have hXgcard : Nat.card Xg = Nat.card X :=
    conjugate_subgroup_card_local X g
  have hXgne : Xg ≠ ⊥ := by
    intro hbot
    apply hXne
    exact (Subgroup.map_eq_bot_iff_of_injective X
      (MulAut.conj g).injective).mp (by simpa [Xg, conjugateSubgroup] using hbot)
  have hXgodd : Nat.Coprime 2 (Nat.card Xg) := by
    rw [hXgcard]
    exact hXodd
  have hXgH : Xg ≤ c.H := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, hzx⟩
    rw [c.H_eq_centralizer]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hax : a * x = x * a :=
      (Subgroup.mem_centralizer_iff.mp haCent) x hx |>.symm
    have htz : c.t * z = z * c.t := by
      rw [← hzx, ← hga]
      change (g * a * g⁻¹) * (g * x * g⁻¹) =
        (g * x * g⁻¹) * (g * a * g⁻¹)
      calc
        (g * a * g⁻¹) * (g * x * g⁻¹) =
            g * (a * x) * g⁻¹ := by group
        _ = g * (x * a) * g⁻¹ := by rw [hax]
        _ = (g * x * g⁻¹) * (g * a * g⁻¹) := by group
    exact htz.symm
  have hXgU : Xg ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hXgH hXgodd
  let yg : G := g * y * g⁻¹
  have hyI : IsInvolution yg := by
    refine ⟨?_, ?_⟩
    · intro hy1
      apply hyJ'.1.1
      have : y = g⁻¹ * yg * g := by simp [yg]; group
      rw [this, hy1]
      simp
    · have hy2 : y * y = 1 := by simpa [pow_two] using hyJ'.1.2
      calc
        yg ^ 2 = g * (y * y) * g⁻¹ := by simp [pow_two, yg]
        _ = 1 := by rw [hy2]; simp
  have hyInv : ∀ z : G, z ∈ Xg →
      yg * z * yg⁻¹ = z⁻¹ := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, hzx⟩
    have hxInv : y * x * y⁻¹ = x⁻¹ := (hXinv x hx).2
    rw [← hzx]
    simp only [yg, MulAut.conj_apply]
    calc
      (g * y * g⁻¹) * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ =
          g * (y * x * y⁻¹) * g⁻¹ := by group
      _ = g * x⁻¹ * g⁻¹ := by rw [hxInv]
      _ = (g * x * g⁻¹)⁻¹ := by group
  have hyH : yg ∈ c.Hhat := by
    by_contra hyHnot
    have hcard := firstCase_klein_restrictionFive hmin c hfirst hklein yg hyI hyHnot
    let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
    have hBcard : Nat.card {z : G // z ∈ invertedElements B yg} = 1 := by
      simpa [B] using hcard
    have hXgcardle : Nat.card Xg ≤ Nat.card
        {z : G // z ∈ invertedElements B yg} := by
      let f : Xg → {z : G // z ∈ invertedElements B yg} := fun z =>
        ⟨z, ⟨(show (z : G) ∈ B from Subgroup.mem_sup_right (hXgU z.2)),
          hyInv z.1 z.2⟩⟩
      have hf : Function.Injective f := by
        intro z w hzw
        apply Subtype.ext
        exact congrArg (fun q : {z : G // z ∈ invertedElements B yg} => (q : G)) hzw
      exact Nat.card_le_card_of_injective f hf
    have hXgcardge : 2 ≤ Nat.card Xg := by
      have hne1 : Nat.card Xg ≠ 1 := card_ne_one_of_ne_bot_local Xg hXgne
      have hpos : 0 < Nat.card Xg := Nat.card_pos
      omega
    rw [hBcard] at hXgcardle
    omega
  have hyV : yg ∉ twoCoreOf c.Hhat := by
    intro hyV
    have hcent : Xg ≤ Subgroup.centralizer ({yg} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hVcent : twoCoreOf c.Hhat ≤
          Subgroup.centralizer (c.U : Set G) := by
        simpa [(theorem_2_6 hmin c).1] using
          twoCoreOf_centralizes_oddCoreOf c.Hhat
      have hzcomm : z * yg = yg * z :=
        (Subgroup.mem_centralizer_iff.mp (hVcent hyV) z (hXgU hz))
      exact hzcomm
    have hXgodd' : Odd (Nat.card Xg) := Nat.coprime_two_left.mp hXgodd
    have hbot := oddOrder_subgroup_eq_bot_of_inverted_and_centralized
      Xg yg hXgodd' hcent hyInv
    exact hXgne hbot
  have hLall' := hLall yg hyH hyI hyV
  have hXgL : Xg ≤ L := by
    intro z hz
    change (z : G) ∈ (L : Set G)
    rw [hLall'.1]
    exact ⟨hXgU hz, hyInv z hz⟩
  have hgnot : g ∉ c.Hhat := by
    intro hgH
    have hUnormHhat : IsNormalIn c.U c.Hhat := by
      rw [(theorem_2_6 hmin c).1]
      refine ⟨?_, ?_⟩
      · exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
      · intro h hh x hx
        rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
        refine Subgroup.mem_map.mpr ⟨
          (⟨h, hh⟩ : c.Hhat) * z * (⟨h, hh⟩ : c.Hhat)⁻¹, ?_, by simp⟩
        exact (pPrimeCore_normal (p := 2) (G := ↥c.Hhat)).conj_mem
          z hz (⟨h, hh⟩ : c.Hhat)
    have hXU : X ≤ c.U := by
      intro x hx
      have hxg : g * x * g⁻¹ ∈ c.U := by
        exact hXgU (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      have hxback := hUnormHhat.2 g⁻¹ (c.Hhat.inv_mem hgH) (g * x * g⁻¹) hxg
      simpa [mul_assoc] using hxback
    have hcard := firstCase_klein_restrictionFive hmin c hfirst hklein y
      hyJ'.1 hyJ'.2.1
    let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
    have hBcard : Nat.card {z : G // z ∈ invertedElements B y} = 1 := by
      simpa [B] using hcard
    let f : X → {z : G // z ∈ invertedElements B y} := fun z =>
      ⟨z, ⟨Subgroup.mem_sup_right (hXU z.2), (hXinv z.1 z.2).2⟩⟩
    have hf : Function.Injective f := by
      intro z w hzw
      apply Subtype.ext
      exact congrArg (fun q : {z : G // z ∈ invertedElements B y} => (q : G)) hzw
    have hle : Nat.card X ≤ Nat.card {z : G // z ∈ invertedElements B y} :=
      Nat.card_le_card_of_injective f hf
    have hge : 2 ≤ Nat.card X := by
      have hne1 := card_ne_one_of_ne_bot_local X hXne
      have hpos : 0 < Nat.card X := Nat.card_pos
      omega
    rw [hBcard] at hle
    omega
  have hNXg : Subgroup.normalizer (Xg : Set G) ≤ c.Hhat := by
    exact hfirst.2 Xg hXgne (hXgL.trans hLHall.1)
  have hFUcent : c.FU ≤ Subgroup.centralizer (Xg : Set G) := by
    have hFU_L : c.FU ≤ Subgroup.centralizer (L : Set G) :=
      firstCase_klein_FU_centralizes_hall c hr hLr hLHall
    exact hFU_L.trans (Subgroup.centralizer_le (by
      intro z hz
      exact hXgL hz))
  exact ⟨g, L, hLHall, hLne, by simpa [Xg] using hXgL, hgnot, hNXg, hFUcent⟩

end CFSG.GorensteinWalter
