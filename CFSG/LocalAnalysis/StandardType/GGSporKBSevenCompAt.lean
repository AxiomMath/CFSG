module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndComp

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

private theorem commutator_self_eq_of_perfect {G : Type*} [Group G] {H : Subgroup G}
    (h : _root_.commutator ↥H = ⊤) : ⁅H, H⁆ = H := by
  have hmap := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥H)) (H₂ := ⊤) H.subtype
  rw [Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hc : (_root_.commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def]
    exact hmap
  rw [h, Subgroup.map_top, Subgroup.range_subtype] at hc
  exact hc.symm

@[expose] def BSevenCompAt {K : Type} [Group K] (x : K) : Prop :=
  ∃ J : Subgroup K, IsComponentOf J (Subgroup.centralizer {x}) ∧
    (∀ J' : Subgroup K, IsComponentOf J' (Subgroup.centralizer {x}) → J' = J) ∧
    Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set K)) = 2 ∧
    LargeEvenPPrimeCore 7 ↥(Subgroup.centralizer ({x} : Set K)) =
      (J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf (Subgroup.centralizer {x})

theorem bSevenCompAt_of_quasisimple {K : Type} [Group K] [Finite K] {x : K} (hx : orderOf x = 7)
    {J : Subgroup K} (hJle : J ≤ Subgroup.centralizer {x}) (hJq : IsQuasisimple ↥J)
    (hJz : Nat.card ↥(Subgroup.center ↥J) = 2) (hJcard : Nat.card ↥J = 40320)
    (hcard : Nat.card ↥(Subgroup.centralizer ({x} : Set K)) ∣ 564480)
    (hcore : Nat.card ↥(LargeEvenPPrimeCore 7 ↥(Subgroup.centralizer ({x} : Set K))) ≤ 2) :
    BSevenCompAt x := by
  classical
  let C : Subgroup K := Subgroup.centralizer ({x} : Set K)
  let X : Subgroup K := Subgroup.zpowers x
  let D0 : Subgroup K := X ⊔ J
  have hXdef : X = Subgroup.zpowers x := rfl
  have hD0def : D0 = X ⊔ J := rfl
  have hXleC : X ≤ C := by
    rw [hXdef]
    exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hXJ : X ≤ Subgroup.centralizer (J : Set K) := by
    rw [hXdef]
    refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 ?_)
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJle hj)
  have hD0leC : D0 ≤ C := by
    rw [hD0def]
    exact sup_le hXleC hJle
  have hxnotJ : x ∉ J := by
    intro hxJ
    have hxcenter : (⟨x, hxJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJle j.2)
    have hord : orderOf (⟨x, hxJ⟩ : ↥J) = 7 := by
      rw [Subgroup.orderOf_mk, hx]
    have hdvd : orderOf (⟨x, hxJ⟩ : ↥J) ∣ Nat.card ↥(Subgroup.center ↥J) :=
      Subgroup.orderOf_dvd_natCard _ hxcenter
    rw [hord, hJz] at hdvd
    norm_num at hdvd
  have hXcard : Nat.card ↥X = 7 := by
    rw [hXdef, Nat.card_zpowers, hx]
  have hinf : X ⊓ J = ⊥ := by
    haveI : Fact (Nat.card ↥X).Prime := ⟨by rw [hXcard]; norm_num⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((X ⊓ J).subgroupOf X) with h | h
    · have hbot : (X ⊓ J) ⊓ X = ⊥ := (Subgroup.subgroupOf_eq_bot.1 h).eq_bot
      rwa [inf_eq_left.2 inf_le_left] at hbot
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact absurd (h (Subgroup.mem_zpowers x)).2 hxnotJ
  have hJnormalD0 : (J.subgroupOf D0).Normal := by
    rw [hD0def, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    exact sup_le (hXJ.trans (Subgroup.centralizer_le_normalizer (J : Set K)))
      (Subgroup.le_normalizer (H := J))
  have hxD0 : x ∈ D0 := by
    rw [hD0def]
    exact Subgroup.mem_sup_left (show x ∈ X from Subgroup.mem_zpowers x)
  have hX'cyc : IsCyclic ↥(X.subgroupOf D0) := by
    have hgen : X.subgroupOf D0 =
        Subgroup.zpowers (⟨x, hxD0⟩ : ↥D0) := by
      ext y
      rw [Subgroup.mem_subgroupOf, hXdef, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, Subtype.ext ?_⟩
        rw [Subgroup.coe_zpow]
        simpa using hk
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have h := congrArg (fun z : ↥D0 => (z : K)) hk
        rw [Subgroup.coe_zpow] at h
        simpa using h
    rw [hgen]
    exact Subgroup.isCyclic_zpowers _
  have hcomp : Subgroup.IsComplement' (X.subgroupOf D0) (J.subgroupOf D0) := by
    haveI : (J.subgroupOf D0).Normal := hJnormalD0
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · refine disjoint_iff.2 ?_
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      have hyX : (y : K) ∈ X := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hy).1
      have hyJ : (y : K) ∈ J := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hy).2
      have hmem : (y : K) ∈ X ⊓ J := Subgroup.mem_inf.2 ⟨hyX, hyJ⟩
      rw [hinf] at hmem
      exact Subtype.ext (Subgroup.mem_bot.1 hmem)
    · have hle : X.subgroupOf D0 ≤ Subgroup.normalizer (J.subgroupOf D0 : Set ↥D0) := by
        rw [Subgroup.normalizer_eq_top]
        exact le_top
      have hsup : X.subgroupOf D0 ⊔ J.subgroupOf D0 = ⊤ := by
        refine le_antisymm le_top fun y _ => ?_
        have hle0 : X ≤ Subgroup.normalizer (J : Set K) :=
          hXJ.trans (Subgroup.centralizer_le_normalizer (J : Set K))
        have hy : (y : K) ∈ X ⊔ J := y.2
        have hy' : (y : K) ∈ (↑(X ⊔ J) : Set K) := hy
        rw [Subgroup.coe_mul_of_left_le_normalizer_right X J hle0, Set.mem_mul] at hy'
        obtain ⟨a, haX, b, hbJ, hab⟩ := hy'
        have haD : a ∈ D0 := by rw [hD0def]; exact Subgroup.mem_sup_left haX
        have hbD : b ∈ D0 := by rw [hD0def]; exact Subgroup.mem_sup_right hbJ
        have hmul : (⟨a, haD⟩ : ↥D0) * ⟨b, hbD⟩ = y := by
          apply Subtype.ext
          simpa using hab
        rw [← hmul]
        exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.2 haX)
          (Subgroup.mem_subgroupOf.2 hbJ)
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (X.subgroupOf D0) (J.subgroupOf D0) hle]
      rw [hsup]
      simp
  have hcardX' : Nat.card ↥(X.subgroupOf D0) = Nat.card ↥X := by
    rw [← Subgroup.card_subtype D0 (X.subgroupOf D0), Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 le_sup_left]
  have hcardJ' : Nat.card ↥(J.subgroupOf D0) = Nat.card ↥J := by
    rw [← Subgroup.card_subtype D0 (J.subgroupOf D0), Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 le_sup_right]
  have hcardD0 : Nat.card ↥D0 = 282240 := by
    calc Nat.card ↥D0 = Nat.card ↥(X.subgroupOf D0) * Nat.card ↥(J.subgroupOf D0) :=
          hcomp.card_mul_card.symm
      _ = Nat.card ↥X * Nat.card ↥J := by rw [hcardX', hcardJ']
      _ = 7 * 40320 := by rw [hXcard, hJcard]
      _ = 282240 := by norm_num
  have hD0'card : Nat.card ↥(D0.subgroupOf C) = 282240 := by
    rw [← Subgroup.card_subtype C (D0.subgroupOf C), Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hD0leC, hcardD0]
  have hmul_index : 282240 * (D0.subgroupOf C).index = Nat.card ↥C := by
    rw [← hD0'card]
    exact Subgroup.card_mul_index (H := D0.subgroupOf C)
  have hindex_dvd : (D0.subgroupOf C).index ∣ 2 := by
    have hdiv : 282240 * (D0.subgroupOf C).index ∣ 282240 * 2 := by
      rw [hmul_index]
      have : (282240 : ℕ) * 2 = 564480 := by norm_num
      rw [this]
      exact hcard
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdiv
  have hindex_cases : (D0.subgroupOf C).index = 1 ∨ (D0.subgroupOf C).index = 2 :=
    Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hindex_dvd
  have hD0'normal : (D0.subgroupOf C).Normal := by
    rcases hindex_cases with h | h
    · rw [Subgroup.index_eq_one.1 h]; exact Subgroup.normal_top
    · exact Subgroup.normal_of_index_eq_two h
  have hquotC : IsMulCommutative (↥C ⧸ (D0.subgroupOf C)) := by
    haveI : (D0.subgroupOf C).Normal := hD0'normal
    have hdvdcard : Nat.card (↥C ⧸ (D0.subgroupOf C)) ∣ 2 := by
      rw [← Subgroup.index_eq_card]
      exact hindex_dvd
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    haveI : IsCyclic (↥C ⧸ (D0.subgroupOf C)) := isCyclic_of_card_dvd_prime hdvdcard
    exact IsCyclic.isMulCommutative
  have hcommC : _root_.commutator ↥C ≤ D0.subgroupOf C :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D0.subgroupOf C)).1 hquotC
  have hquotD0 : IsMulCommutative (↥D0 ⧸ (J.subgroupOf D0)) := by
    haveI : (J.subgroupOf D0).Normal := hJnormalD0
    haveI : IsCyclic ↥(X.subgroupOf D0) := hX'cyc
    haveI : IsCyclic (↥D0 ⧸ (J.subgroupOf D0)) :=
      (hcomp.QuotientMulEquiv).isCyclic.2 hX'cyc
    exact IsCyclic.isMulCommutative
  have hcommD0 : _root_.commutator ↥D0 ≤ J.subgroupOf D0 :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := J.subgroupOf D0)).1 hquotD0
  have hcommD0' : ⁅D0, D0⁆ ≤ J := by
    have hmap : (_root_.commutator ↥D0).map D0.subtype = ⁅D0, D0⁆ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    calc ⁅D0, D0⁆ = (_root_.commutator ↥D0).map D0.subtype := hmap.symm
      _ ≤ (J.subgroupOf D0).map D0.subtype := Subgroup.map_mono hcommD0
      _ = J ⊓ D0 := Subgroup.subgroupOf_map_subtype J D0
      _ = J := inf_eq_left.2 le_sup_right
  have hJqA : Assembly.IsQuasisimple ↥J := ⟨hJq.1.commutator_eq_top, hJq.2.1⟩
  have hJcomm : ⁅J, J⁆ = J := commutator_self_eq_of_perfect hJq.1.commutator_eq_top
  have hJle_comm : J ≤ ⁅D0, D0⁆ := by
    rw [← hJcomm]
    exact Subgroup.commutator_mono le_sup_right le_sup_right
  have hJeq : J = ⁅D0, D0⁆ := le_antisymm hJle_comm hcommD0'
  have hD0conj : ∀ g ∈ C, D0.map (MulAut.conj g) = D0 := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hD0leC).1 hD0'normal hg)
  have hJnormalC : (J.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJle]
    intro h k hh hk
    have hmap : J.map (MulAut.conj k) = J := by
      rw [hJeq, Subgroup.map_commutator, hD0conj k hk, ← hJeq]
    have hmem : MulAut.conj k h ∈ J.map (MulAut.conj k) := ⟨h, hh, rfl⟩
    rw [hmap] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hsub : IsSubnormal J C := IsSubnormal.step hJle hJnormalC (IsSubnormal.refl C)
  have hIsComp : IsComponentOf J C := ⟨hJle, hsub, hJqA⟩
  have hXcyc : IsCyclic X := by
    rw [hXdef]
    exact Subgroup.isCyclic_zpowers x
  have huniq : ∀ J' : Subgroup K, IsComponentOf J' C → J' = J := by
    intro J' hJ'
    have hJ'comm : ⁅J', J'⁆ = J' := commutator_self_eq_of_perfect hJ'.2.2.1
    have hJ'leD0 : J' ≤ D0 := by
      have hcommC' : ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ D0.subgroupOf C := by
        rw [← commutator_def]
        exact hcommC
      have hP'eq : J'.subgroupOf C = ⁅J'.subgroupOf C, J'.subgroupOf C⁆ := by
        apply Subgroup.map_injective (f := C.subtype)
        intro a b hab
        exact Subtype.ext hab
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJ'.1]
        have hmap : (⁅J'.subgroupOf C, J'.subgroupOf C⁆).map C.subtype = ⁅J', J'⁆ := by
          rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJ'.1]
        rw [hmap, hJ'comm]
      have hle : J'.subgroupOf C ≤ D0.subgroupOf C := by
        rw [hP'eq]
        exact (Subgroup.commutator_mono le_top le_top).trans hcommC'
      calc J' = (J'.subgroupOf C).map C.subtype := by
              rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJ'.1]
        _ ≤ (D0.subgroupOf C).map C.subtype := Subgroup.map_mono hle
        _ = D0 ⊓ C := Subgroup.subgroupOf_map_subtype D0 C
        _ = D0 := inf_eq_left.2 hD0leC
    have hcompJ' : IsComponentOf J' D0 :=
      IsComponentOf.of_le_of_le hJ' hJ'leD0 hD0leC
    exact TwE6D3.eq_of_isComponentOf_sup hXcyc hXJ hJqA hcompJ'
  have hZcard : Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set K)) = 2 := by
    have hZ : (Subgroup.center ↥J).map J.subtype =
        J ⊓ Subgroup.centralizer (J : Set K) := by
      rw [inf_comm]
      rw [← Subgroup.subgroupOf_map_subtype (Subgroup.centralizer (J : Set K)) J]
      congr 1
      ext a
      rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      constructor
      · intro h b hb
        have h' := congrArg Subtype.val (h ⟨b, hb⟩)
        simpa using h'
      · intro h b
        exact Subtype.ext (h (b : K) b.2)
    rw [← hZ, Subgroup.card_subtype J (Subgroup.center ↥J), hJz]
  have hZleC : J ⊓ Subgroup.centralizer (J : Set K) ≤ C := inf_le_left.trans hJle
  have hZnormal : ((J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZleC]
    intro z g hz hg
    have hzJ : z ∈ J := hz.1
    have hzc : z ∈ Subgroup.centralizer (J : Set K) := hz.2
    refine ⟨(Subgroup.normal_subgroupOf_iff hJle).1 hJnormalC z g hzJ hg, ?_⟩
    change g * z * g⁻¹ ∈ Subgroup.centralizer (J : Set K)
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hgjg : g⁻¹ * j * g ∈ J := by
      simpa using (Subgroup.normal_subgroupOf_iff hJle).1 hJnormalC j g⁻¹ hj (C.inv_mem hg)
    have hcomm : (g⁻¹ * j * g) * z = z * (g⁻¹ * j * g) :=
      (Subgroup.mem_centralizer_iff.1 hzc) _ hgjg
    calc j * (g * z * g⁻¹) = g * ((g⁻¹ * j * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * j * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * z * g⁻¹) * j := by group
  have hZ'card : Nat.card ↥((J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf C) = 2 := by
    rw [← Subgroup.card_subtype C ((J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf C),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hZleC, hZcard]
  have hZ'le_core : (J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf C ≤
      LargeEvenPPrimeCore 7 ↥C := by
    rw [LargeEvenPPrimeCore, CFSG.pPrimeCore]
    refine le_sSup ⟨hZnormal, ?_⟩
    rw [hZ'card]
    norm_num
  have hcoreEq : LargeEvenPPrimeCore 7 ↥C =
      (J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf C := by
    refine le_antisymm ?_ hZ'le_core
    have h := Subgroup.eq_of_le_of_card_ge hZ'le_core (by rw [hZ'card]; exact hcore)
    exact h.symm.le
  exact ⟨J, hIsComp, huniq, hZcard, hcoreEq⟩

end CFSG.StandardType.SporadicShape
