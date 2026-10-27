module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rc
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem card_center_of_isSylowOf_of_bar2 {K R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R K)
    (hZS : ∀ S : Sylow 3 (Bar2 K), Nat.card (center (S : Subgroup (Bar2 K))) = 3) :
    Nat.card (center ↥R) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, rfl⟩ := hR
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).domRestrict (T : Subgroup ↥K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk',
      subgroupOf_eq_bot]
    exact IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ CFSG.pCore_isPGroup T.isPGroup'
  have h := hZS (T.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)))
  rw [Sylow.coe_mapSurjective] at h
  let e₁ : ↥(T : Subgroup ↥K) ≃*
      ↥((T : Subgroup ↥K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) :=
    (MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _))
  let e₂ : ↥((T : Subgroup ↥K).map K.subtype) ≃* ↥(T : Subgroup ↥K) :=
    ((T : Subgroup ↥K).equivMapOfInjective K.subtype K.subtype_injective).symm
  exact (Nat.card_congr (centerCongr (e₂.trans e₁)).toEquiv).trans h

theorem card_center_sylow_eq_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite Y] {p n : ℕ}
    [Fact p.Prime] (e : X ≃* Y) (h : ∀ S : Sylow p X, Nat.card (center (S : Subgroup X)) = n)
    (S : Sylow p Y) : Nat.card (center (S : Subgroup Y)) = n := by
  have h₁ := h (S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  exact (Nat.card_congr (centerCongr
    ((S : Subgroup Y).equivMapOfInjective e.symm.toMonoidHom e.symm.injective)).toEquiv).trans h₁

theorem le_upperCentralSeries_two_map_of_card_nine {P W : Subgroup G} (hP : IsPGroup 3 P)
    (hWP : W ≤ P) (hPW : P ≤ normalizer (W : Set G)) (hWc : Nat.card W = 9) :
    W ≤ (Subgroup.upperCentralSeries ↥P 2).map P.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (W.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hWP).mpr hPW
  have hc : Nat.card ↥(W.subgroupOf P) = 3 ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWP).toEquiv, hWc]
    norm_num
  have h := uc22p22r_le_upperCentralSeries_two hP hc
  intro w hw
  exact ⟨⟨w, hWP hw⟩, h (mem_subgroupOf.mpr hw), rfl⟩

theorem exists_planes_of_commute {P R R' : Subgroup G} (hP : IsPGroup 3 P)
    (hRP : R ≤ P) (hR'P : R' ≤ P) (hPR : P ≤ normalizer (R : Set G))
    (hPR' : P ≤ normalizer (R' : Set G)) (hcomm : ∀ r ∈ R, ∀ r' ∈ R', r * r' = r' * r)
    (hZR : Nat.card (center ↥R) = 3) (hZR' : Nat.card (center ↥R') = 3)
    (hRc : ¬ IsCyclic R) (hR'c : ¬ IsCyclic R') (hrank : CFSG.Open.pRank 3 P ≤ 3) :
    ∃ W B Z₀ : Subgroup G, W ≤ R ∧ IsElemAbelian 3 W ∧ Nat.card W = 9 ∧ W ≤ B ∧ B ≤ P ∧
      IsElemAbelian 3 B ∧ Nat.card B = 27 ∧ P ≤ normalizer (B : Set G) ∧
      B ≤ (Subgroup.upperCentralSeries ↥P 2).map P.subtype ∧ Z₀ ≤ W ∧ Nat.card Z₀ = 3 ∧
      ∀ b ∈ B, b ∈ (center ↥P).map P.subtype → b ∈ Z₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨W, hWR, hPW, hWc, hW3, hWcomm⟩ := CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le
    Nat.prime_three (by norm_num) hP hRP hPR hRc
  obtain ⟨W', hW'R', hPW', hW'c, hW'3, hW'comm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le Nat.prime_three (by norm_num) hP hR'P
      hPR' hR'c
  have hWel : IsElemAbelian 3 W :=
    ⟨IsMulCommutative.of_comm fun u v => Subtype.ext (hWcomm _ u.2 _ v.2), hW3⟩
  have hW'el : IsElemAbelian 3 W' :=
    ⟨IsMulCommutative.of_comm fun u v => Subtype.ext (hW'comm _ u.2 _ v.2), hW'3⟩
  have hc : ∀ a ∈ W, ∀ b ∈ W', a * b = b * a := fun a ha b hb =>
    hcomm a (hWR ha) b (hW'R' hb)
  have hBel : IsElemAbelian 3 (W ⊔ W') := hWel.sup_of_commute hW'el hc
  have hBP : W ⊔ W' ≤ P := sup_le (hWR.trans hRP) (hW'R'.trans hR'P)
  have hcard := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hc
  rw [hWc, hW'c] at hcard
  set Zc : Subgroup G := (center ↥R).map R.subtype with hZcdef
  set Zc' : Subgroup G := (center ↥R').map R'.subtype with hZc'def
  have hZcc : Nat.card Zc = 3 := by rw [hZcdef, card_map_of_injective R.subtype_injective, hZR]
  have hZcc' : Nat.card Zc' = 3 := by
    rw [hZc'def, card_map_of_injective R'.subtype_injective, hZR']
  have hRR'Z : R ⊓ R' ≤ Zc := fun y hy =>
    ⟨⟨y, hy.1⟩, mem_center_iff.mpr fun s => Subtype.ext (hcomm s s.2 y hy.2), rfl⟩
  have hRR'Z' : R ⊓ R' ≤ Zc' := fun y hy =>
    ⟨⟨y, hy.2⟩, mem_center_iff.mpr fun s => Subtype.ext (hcomm y hy.1 s s.2).symm, rfl⟩
  have hI : W ⊓ W' ≤ R ⊓ R' := inf_le_inf hWR hW'R'
  have hI3 : Nat.card ↥(W ⊓ W') = 3 := by
    have hdvd : Nat.card ↥(W ⊓ W') ∣ 3 := hZcc ▸ card_dvd_of_le (hI.trans hRR'Z)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exfalso
      rw [h, mul_one] at hcard
      have h4 : 4 ≤ CFSG.Open.pRank 3 P :=
        CFSG.SectionRank.le_pRank (by norm_num) hBP hBel (k := 4) (by rw [hcard]; norm_num)
      omega
    · exact h
  have hIZ : W ⊓ W' = Zc := eq_of_le_of_card_ge (hI.trans hRR'Z) (by rw [hI3, hZcc])
  have hIZ' : W ⊓ W' = Zc' := eq_of_le_of_card_ge (hI.trans hRR'Z') (by rw [hI3, hZcc'])
  have hBc : Nat.card ↥(W ⊔ W') = 27 := by
    rw [hI3] at hcard
    omega
  refine ⟨W, W ⊔ W', W ⊓ W', hWR, hWel, hWc.trans (by norm_num), le_sup_left, hBP, hBel, hBc,
    (le_inf hPW hPW').trans (inf_normalizer_le_normalizer_sup W W'),
    sup_le (le_upperCentralSeries_two_map_of_card_nine hP (hWR.trans hRP) hPW
      (hWc.trans (by norm_num)))
      (le_upperCentralSeries_two_map_of_card_nine hP (hW'R'.trans hR'P) hPW'
        (hW'c.trans (by norm_num))), inf_le_left, hI3, ?_⟩
  intro b hb hbZ
  obtain ⟨c, hcZ, rfl⟩ := mem_map.mp hbZ
  have hcP : ∀ x ∈ P, x * (c : G) = (c : G) * x := fun x hx =>
    congrArg Subtype.val (mem_center_iff.mp hcZ ⟨x, hx⟩)
  have hset := coe_mul_of_left_le_normalizer_right W W'
    (CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.le_normalizer_of_commute fun a ha b hb => (hc b hb a ha).symm)
  have hb' : (c : G) ∈ ((W ⊔ W' : Subgroup G) : Set G) := hb
  rw [hset] at hb'
  obtain ⟨w, hw, w', hw', hww''⟩ := hb'
  have hww' : w * w' = (c : G) := hww''
  have hwZ : w ∈ W ⊓ W' := by
    rw [hIZ]
    refine ⟨⟨w, hWR hw⟩, mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
    have h1 := hcP s (hRP s.2)
    rw [← hww'] at h1
    have h2 : (s : G) * w' = w' * s := hcomm s s.2 w' (hW'R' hw')
    have h3 : (s : G) * w * w' = w * s * w' := by
      calc (s : G) * w * w' = s * (w * w') := mul_assoc _ _ _
        _ = w * w' * s := h1
        _ = w * (w' * s) := mul_assoc _ _ _
        _ = w * (s * w') := by rw [h2]
        _ = w * s * w' := (mul_assoc _ _ _).symm
    exact mul_right_cancel h3
  have hw'Z : w' ∈ W ⊓ W' := by
    rw [hIZ']
    refine ⟨⟨w', hW'R' hw'⟩, mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
    have h1 := hcP s (hR'P s.2)
    rw [← hww'] at h1
    have h2 : w * (s : G) = s * w := hcomm w (hWR hw) s s.2
    have h3 : w * ((s : G) * w') = w * (w' * s) := by
      calc w * ((s : G) * w') = w * s * w' := (mul_assoc _ _ _).symm
        _ = s * w * w' := by rw [h2]
        _ = s * (w * w') := mul_assoc _ _ _
        _ = w * w' * s := h1
        _ = w * (w' * s) := mul_assoc _ _ _
    exact mul_left_cancel h3
  change (c : G) ∈ W ⊓ W'
  rw [← hww']
  exact ⟨W.mul_mem hw hw'Z.1, W'.mul_mem hwZ.2 hw'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
