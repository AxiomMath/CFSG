module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM24
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowJ2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeKFact

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_alternatingGroup_six' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem card_alternatingGroup_seven' : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem isSimpleGroup_alternatingGroup_fin {n : ℕ} (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)

section M24

open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.AGLEmbeddingD2.Wilson.Census219
open CFSG.Sporadic.SmallOddCore (tp)


theorem good427_m24y :
    Good427 (Subgroup.centralizer ({m24y} : Set Blueprint.NativeSporadic.M24)) := by
  obtain ⟨-, ⟨e'⟩, hQ⟩ := m24_layer
  exact good427_of_isExtOf (isExtOf_congr e'.symm hQ.isExtOf)
    (isSimpleGroup_alternatingGroup_fin (by norm_num)) inferInstance
    (not_dvd_sixty_of_nine_dvd (by rw [card_alternatingGroup_six']; norm_num))

theorem good427_m24 (s : Blueprint.NativeSporadic.M24) (hs : orderOf s = 3) :
    Good427 (Subgroup.centralizer ({s} : Set Blueprint.NativeSporadic.M24)) := by
  have hord : orderOf (s : Equiv.Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hs
  obtain ⟨r, hr, g, hg, hgr⟩ := m24_cover s.2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  set gP : Blueprint.NativeSporadic.M24 := ⟨g, hg⟩ with hgP
  set φ : Blueprint.NativeSporadic.M24 ≃* Blueprint.NativeSporadic.M24 := MulAut.conj gP⁻¹ with hφ
  have hφs : ((φ s : Blueprint.NativeSporadic.M24) : Equiv.Perm (Fin 24)) = tp 24 r.rep := by
    have : ((φ s : Blueprint.NativeSporadic.M24) : Equiv.Perm (Fin 24)) =
        g⁻¹ * (s : Equiv.Perm (Fin 24)) * g := by
      simp [hφ, hgP, MulAut.conj_apply]
    rw [this, hgr]
    group
  refine Good427.of_mulEquiv_centralizer φ ?_
  rcases hr with rfl | rfl
  · have hφy : φ s = m24y := Subtype.ext hφs
    rw [hφy]
    exact good427_m24y
  · exact good427_of_not_five_dvd (by rw [card_centralizer_m24B hφs]; norm_num)

theorem noCfgS427_m24 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .M24) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  have hcard : Nat.card S = 244823040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M24
  refine ⟨noCfgS427_of_model (G' := ↥Blueprint.NativeSporadic.M24) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (CFSG.Quasithin.A318P.not_dvd_outer_M24 e Nat.prime_three (by norm_num)) good427_m24,
    noONS427_of_card (by rw [hcard]; norm_num)⟩

end M24

section He

open CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
open CFSG.Sporadic.HeldB


theorem good427_heY : Good427 (Subgroup.centralizer ({heY} : Set heP)) := by
  obtain ⟨-, ⟨e'⟩, hQ⟩ := he_layer
  exact good427_of_isExtOf (isExtOf_congr e'.symm hQ.isExtOf)
    (isSimpleGroup_alternatingGroup_fin (by norm_num)) inferInstance
    (not_dvd_sixty_of_nine_dvd (by rw [card_alternatingGroup_seven']; norm_num))

theorem good427_heP (y : heP) (hy : orderOf y = 3) :
    Good427 (Subgroup.centralizer ({y} : Set heP)) := by
  have hord : orderOf ((y : heP) : Equiv.Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hy
  rcases three_conj_cases y.2 hord with ⟨c, hc, hcy⟩ | ⟨c, hc, hcy⟩
  · let φ : heP ≃* heP := MulAut.conj (⟨c, hc⟩ : heP)⁻¹
    have hφ : φ y = heY := by
      apply Subtype.ext
      show c⁻¹ * ((y : heP) : Equiv.Perm (Fin 8330)) * c = bOf heThreeWordsA
      rw [hcy]
      group
    refine Good427.of_mulEquiv_centralizer φ ?_
    rw [hφ]
    exact good427_heY
  · let φ : heP ≃* heP := MulAut.conj (⟨c, hc⟩ : heP)⁻¹
    have hφ : ((φ y : heP) : Equiv.Perm (Fin 8330)) = bOf heThreeWordsB := by
      show c⁻¹ * ((y : heP) : Equiv.Perm (Fin 8330)) * c = bOf heThreeWordsB
      rw [hcy]
      group
    refine Good427.of_mulEquiv_centralizer φ (good427_of_not_five_dvd ?_)
    rw [card_centralizer_heP, hφ, card_cent_B]
    norm_num

theorem noCfgS427_he :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Spor .He) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .He ≃* Spor .He := b
  let e' : S ≃* heP := (e.trans b'.symm).trans heEquivP
  have hcard : Nat.card S = 4030387200 := (Nat.card_congr e'.toEquiv).trans card_heP
  refine ⟨noCfgS427_of_model (G' := ↥heP) e' (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e spor_he.1) good427_heP,
    noONS427_of_card (by rw [hcard]; norm_num)⟩

end He

section J2


theorem centralizer_zpowers_eq {G : Type*} [Group G] (y : G) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h y (Subgroup.mem_zpowers y)).symm
  · intro h z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_right (show Commute x y from h) k)).eq.symm

theorem noCfgS427_j2 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Spor .J2) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J2 ≃* Spor .J2 := b
  have hcard : Nat.card S = 604800 :=
    (Nat.card_congr (e.trans b'.symm).toEquiv).trans CFSG.Sporadic.J2.card_J2
  refine ⟨noCfgS427_of_inner (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e spor_j2.1) fun y hy => ?_,
    noONS427_of_card (by rw [hcard]; norm_num)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hyp : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hP⟩ := hyp.exists_le_sylow
  have hyP : y ∈ (P : Subgroup S) := hP (Subgroup.mem_zpowers y)
  set Z : Subgroup S := (P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S)
    with hZdef
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hext, -⟩, h4, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 S ⟨e.trans b'.symm⟩ P Z hZdef _ rfl
  have hZcard : Nat.card Z = 3 := card_inf_centralizer_of_isHeisThree hHeis
  by_cases hyZ : y ∈ Z
  ·
    have hZeq : Subgroup.zpowers y = Z := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyZ)
      exact le_of_eq (by rw [Nat.card_zpowers, hy, hZcard])
    rw [← centralizer_zpowers_eq, hZeq]
    exact good427_of_isExtOf hext (isSimpleGroup_alternatingGroup_fin (by norm_num)) inferInstance
      (not_dvd_sixty_of_nine_dvd (by rw [card_alternatingGroup_six']; norm_num))
  ·
    have hcomm : ∀ a ∈ Z, ∀ c ∈ Subgroup.zpowers y, a * c = c * a := by
      intro a ha c hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hay : a * y = y * a := (Subgroup.mem_centralizer_iff.mp ha.2 y hyP).symm
      exact ((Commute.zpow_right (show Commute a y from hay) k)).eq
    have hinf : Z ⊓ Subgroup.zpowers y = ⊥ := by
      have hd : Nat.card (Z ⊓ Subgroup.zpowers y : Subgroup S) ∣ 3 := by
        rw [← hy, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have heq : Z ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hy])
        exact hyZ ((heq ▸ inf_le_left : Subgroup.zpowers y ≤ Z) (Subgroup.mem_zpowers y))
    have hAcard : Nat.card (Z ⊔ Subgroup.zpowers y : Subgroup S) = 9 := by
      have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z (Subgroup.zpowers y)
        hcomm).1
      rw [hinf, Subgroup.card_bot, mul_one, hZcard, Nat.card_zpowers, hy] at h
      exact h
    have hAP : Z ⊔ Subgroup.zpowers y ≤ (P : Subgroup S) :=
      sup_le inf_le_left (Subgroup.zpowers_le.mpr hyP)
    obtain ⟨-, ⟨eN⟩, -⟩ := h4 (Z ⊔ Subgroup.zpowers y) ⟨hAP, hAcard⟩ y
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) hyZ
    have hNcard : Nat.card (Subgroup.normalizer
        ((Subgroup.zpowers y : Subgroup S) : Set S)) = 72 := by
      rw [Nat.card_congr eN.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card (α := alternatingGroup (Fin 4))]
      rfl
    have hle : Subgroup.centralizer ({y} : Set S) ≤
        Subgroup.normalizer ((Subgroup.zpowers y : Subgroup S) : Set S) := by
      rw [← centralizer_zpowers_eq]
      exact Subgroup.centralizer_le_normalizer _
    exact good427_of_card_dvd (M := 72)
      (hNcard ▸ Subgroup.card_dvd_of_le hle) (by norm_num)

end J2

section Rows



section M24Row


theorem rowOf427_m24
    : RowOf427 (Spor .M24) :=
  rowOf427_spor (s := .M24) CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv noCfgS427_m24

end M24Row

section HeRow


theorem rowOf427_he
    : RowOf427 (Spor .He) := rowOf427_of_noCfgS noCfgS427_he

end HeRow

section J2Row


theorem rowOf427_j2
    : RowOf427 (Spor .J2) := rowOf427_of_noCfgS noCfgS427_j2

end J2Row

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
