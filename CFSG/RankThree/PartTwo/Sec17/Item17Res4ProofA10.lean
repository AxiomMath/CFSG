module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofTenL
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofPerm
import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofSeven
public import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.RankThree.PartTwo.Sec17.Proof171Gen

theorem axisElt_eq_axisGen : ∀ e : Fin 6, ∃ i : Fin 3, i.val = e.val / 2 ∧
    (axisElt e = axisGen i ∨ axisElt e = (axisGen i)⁻¹) := by
  decide +kernel

theorem axisGen_two : axisGen 2 = dThree := rfl

theorem kOneF_kTwoF_comm_dThree : ∀ m : Fin 4,
    kOneF m * dThree = dThree * kOneF m ∧ kTwoF m * dThree = dThree * kTwoF m := by
  decide +kernel

theorem kThreeF_comm_dThree : ∀ m : Fin 4, kThreeF m * dThree = dThree * kThreeF m → m = 0 := by
  decide +kernel

theorem kOneF_trans : ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 →
    ∃ i : Fin 3, dOne ^ (i : ℕ) * kOneF m * (dOne ^ (i : ℕ))⁻¹ = kOneF n := by
  decide +kernel

theorem kTwoF_trans : ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 →
    ∃ i : Fin 3, dTwo ^ (i : ℕ) * kTwoF m * (dTwo ^ (i : ℕ))⁻¹ = kTwoF n := by
  decide +kernel

theorem kThreeF_trans : ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 →
    ∃ i : Fin 3, dThree ^ (i : ℕ) * kThreeF m * (dThree ^ (i : ℕ))⁻¹ = kThreeF n := by
  decide +kernel

theorem pow_mem_eTwentySeven (i : ℕ) :
    dOne ^ i ∈ eTwentySeven ∧ dTwo ^ i ∈ eTwentySeven ∧ dThree ^ i ∈ eTwentySeven :=
  ⟨pow_mem dOne_mem i, pow_mem dTwo_mem i, pow_mem dThree_mem i⟩

theorem kF_irreducible {R K : Subgroup (Perm (Fin 10))} (hK : K = kOne ∨ K = kTwo ∨ K = kThree)
    (hRK : R ≤ K) (hE : eTwentySeven ≤ Subgroup.normalizer (R : Set (Perm (Fin 10))))
    (hR : R ≠ ⊥) : R = K := by
  obtain ⟨⟨r, hrR⟩, hr1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
  have hr1 : r ≠ 1 := fun h1 => hr1' (Subtype.ext h1)
  have hconj : ∀ x ∈ eTwentySeven, ∀ y ∈ R, x * y * x⁻¹ ∈ R := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hE hx) y).mp hy
  refine le_antisymm hRK ?_
  rcases hK with rfl | rfl | rfl
  · obtain ⟨m, hm⟩ := hRK hrR
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hr1 (by rw [hm]; rfl)
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst hn
      exact R.one_mem
    obtain ⟨i, hi⟩ := kOneF_trans m n hm0 hn
    rw [← hi, ← hm]
    exact hconj _ (pow_mem_eTwentySeven i).1 _ hrR
  · obtain ⟨m, hm⟩ := hRK hrR
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hr1 (by rw [hm]; rfl)
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst hn
      exact R.one_mem
    obtain ⟨i, hi⟩ := kTwoF_trans m n hm0 hn
    rw [← hi, ← hm]
    exact hconj _ (pow_mem_eTwentySeven i).2.1 _ hrR
  · obtain ⟨m, hm⟩ := hRK hrR
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hr1 (by rw [hm]; rfl)
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst hn
      exact R.one_mem
    obtain ⟨i, hi⟩ := kThreeF_trans m n hm0 hn
    rw [← hi, ← hm]
    exact hconj _ (pow_mem_eTwentySeven i).2.2 _ hrR


variable {G : Type} [Group G] [Finite G]

structure A10Pic (A : Subgroup G) (c : G) (L Y₀ : Subgroup G)
    (φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) (g : Perm (Fin 10)) : Prop where
  le_y0 : A ≤ Y₀
  L_le : L ≤ Y₀
  c_mem : c ∈ Y₀
  inj : ∀ a : ↥Y₀, (a : G) ∈ A → projTen Y₀ φ a = 1 → a = 1
  mem : ∀ a : ↥Y₀, (a : G) ∈ A → g * projTen Y₀ φ a * g⁻¹ ∈ eTwentySeven
  surj : ∀ x ∈ eTwentySeven, ∃ a : ↥Y₀, (a : G) ∈ A ∧ g * projTen Y₀ φ a * g⁻¹ = x
  lift : ∀ h ∈ normAlt, ∃ y : ↥Y₀, (y : G) ∈ Subgroup.normalizer (A : Set G) ∧
    (∀ a : ↥Y₀, (a : G) ∈ A →
      g * projTen Y₀ φ (y * a * y⁻¹) * g⁻¹ = h * (g * projTen Y₀ φ a * g⁻¹) * h⁻¹) ∧
    ∃ a₀ : ↥Y₀, (a₀ : G) ∈ A ∧ g * projTen Y₀ φ y * g⁻¹ = h * (g * projTen Y₀ φ a₀ * g⁻¹)
  c_axis : g * projTen Y₀ φ ⟨c, c_mem⟩ * g⁻¹ = dThree ∨
    g * projTen Y₀ φ ⟨c, c_mem⟩ * g⁻¹ = dThree⁻¹
  L_cent : ∀ l : ↥Y₀, (l : G) ∈ L →
    g * projTen Y₀ φ l * g⁻¹ * dThree = dThree * (g * projTen Y₀ φ l * g⁻¹)
  L_seven : ∀ l : ↥Y₀, (l : G) ∈ L →
    g * projTen Y₀ φ l * g⁻¹ ∈ (alternatingGroup (Fin 7)).map embedSeven
  L_cover : ∀ R : Subgroup (Perm (Fin 10)),
    R ≤ Subgroup.centralizer ({dThree} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10) →
    ¬ 3 ∣ Nat.card R → ∀ z ∈ R, ∃ l : ↥Y₀, (l : G) ∈ L ∧ g * projTen Y₀ φ l * g⁻¹ = z

theorem exists_a10Pic {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10))
    (φL : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    (hΩ3 : (omegaA A).ncard = 3) : ∃ g : Perm (Fin 10), A10Pic A c L Y₀ φ g := by
  classical
  have hAY : A ≤ Y₀ := h.le_y0_of_alternating_ten ⟨φ⟩
  have hD := h.toSec13Data
  have hcA : c ∈ A := h.c_mem
  have hcY : c ∈ Y₀ := hAY hcA
  obtain ⟨hinj, g, hmem, hsurj, hlift⟩ :=
    Res162b.exists_conj_lift hD.isElemAbelian hD.card_eq hAY φ
  obtain ⟨e, he⟩ := Res162b.exists_axisElt_of_mem_omegaA hAY φ hΩ3 hinj hmem hlift
    h.zpowers_mem_omegaA
  obtain ⟨i, -, hei⟩ := axisElt_eq_axisGen e
  obtain ⟨k, hk, hki⟩ := exists_conj_axisGen i 2
  rw [axisGen_two] at hki
  have hkN : k ∈ normTen := (Subgroup.mem_inf.mp hk).1
  set π := projTen Y₀ φ with hπ
  set g' := k * g with hg'
  have hconj : ∀ z : Perm (Fin 10), g' * z * g'⁻¹ = k * (g * z * g⁻¹) * k⁻¹ := fun z => by
    rw [hg']
    group
  have hc' : g' * π ⟨c, hcY⟩ * g'⁻¹ = dThree ∨ g' * π ⟨c, hcY⟩ * g'⁻¹ = dThree⁻¹ := by
    rw [hconj]
    have he' : g * π ⟨c, hcY⟩ * g⁻¹ = axisElt e := he
    rw [he']
    rcases hei with h1 | h1
    · left
      rw [h1, hki]
    · right
      rw [h1, ← hki]
      group
  have hLcent : ∀ l : ↥Y₀, (l : G) ∈ L →
      g' * π l * g'⁻¹ * dThree = dThree * (g' * π l * g'⁻¹) := by
    intro l hl
    have hlc : (l : G) * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp
      (h.le_centralizer_c hl)
    have hlc' : l * ⟨c, hcY⟩ = ⟨c, hcY⟩ * l := Subtype.ext hlc
    have hπc : π l * π ⟨c, hcY⟩ = π ⟨c, hcY⟩ * π l := by
      rw [← map_mul, ← map_mul, hlc']
    have hcomm : Commute (g' * π l * g'⁻¹) (g' * π ⟨c, hcY⟩ * g'⁻¹) := by
      change (g' * π l * g'⁻¹) * (g' * π ⟨c, hcY⟩ * g'⁻¹) =
        (g' * π ⟨c, hcY⟩ * g'⁻¹) * (g' * π l * g'⁻¹)
      calc (g' * π l * g'⁻¹) * (g' * π ⟨c, hcY⟩ * g'⁻¹) = g' * (π l * π ⟨c, hcY⟩) * g'⁻¹ := by
            group
        _ = g' * (π ⟨c, hcY⟩ * π l) * g'⁻¹ := by rw [hπc]
        _ = (g' * π ⟨c, hcY⟩ * g'⁻¹) * (g' * π l * g'⁻¹) := by group
    have hcomm' : Commute (g' * π l * g'⁻¹) dThree := by
      rcases hc' with h1 | h1
      · rwa [h1] at hcomm
      · rw [h1] at hcomm
        simpa using hcomm.inv_right
    exact hcomm'.eq
  obtain ⟨h2520, hperf, -, -⟩ := Res162b.img_facts_of_ten h.le_y0 hcY h.c_pow_three hD.ne_one
    h.le_centralizer_c (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) φL φ
  set H := (imgTen Y₀ φ L).map (MulAut.conj g').toMonoidHom with hH
  have hHc : H ≤ Subgroup.centralizer ({dThree} : Set (Perm (Fin 10))) ⊓
      alternatingGroup (Fin 10) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨l, hl, rfl⟩ := (mem_imgTen Y₀ φ).mp hw
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hLcent l hl), ?_⟩
    exact (alternatingGroup.normal (α := Fin 10)).conj_mem _
      (projTen_mem_alternatingGroup Y₀ φ l) g'
  have hHp : ⁅H, H⁆ = H := commutator_map_conj_self hperf g'
  have hH7 : 2520 ≤ Nat.card H := by
    rwa [hH, Subgroup.card_map_of_injective (MulAut.conj g').injective]
  have hmemH : ∀ l : ↥Y₀, (l : G) ∈ L → g' * π l * g'⁻¹ ∈ H := fun l hl =>
    ⟨π l, (mem_imgTen Y₀ φ).mpr ⟨l, hl, rfl⟩, rfl⟩
  refine ⟨g', ⟨hAY, h.le_y0, hcY, hinj, fun a ha => ?_, fun x hx => ?_, fun h' hh' => ?_, hc',
    hLcent, fun l hl => Res162b.le_eSeven_of_perfect hHc hHp (hmemH l hl), ?_⟩⟩
  ·
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp hkN _).mp (hmem a ha)
  ·
    have hx' : k⁻¹ * x * k ∈ eTwentySeven := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hkN) x).mp hx
      rwa [inv_inv] at this
    obtain ⟨a, ha, hax⟩ := hsurj _ hx'
    refine ⟨a, ha, ?_⟩
    rw [hconj, hax]
    group
  ·
    have hh'' : k⁻¹ * h' * k ∈ normAlt := mul_mem (mul_mem (inv_mem hk) hh') hk
    obtain ⟨y, hyN, hy, a₀, ha₀, hya₀⟩ := hlift _ hh''
    refine ⟨y, hyN, fun a ha => ?_, a₀, ha₀, ?_⟩
    · have e1 := hconj (π (y * a * y⁻¹))
      have e2 := hconj (π a)
      rw [e1, hy a ha, e2]
      group
    · have e1 := hconj (π y)
      have e2 := hconj (π a₀)
      rw [e1, hya₀, e2]
      group
  ·
    intro R hR hR3 z hz
    obtain ⟨w, hw, hwz⟩ := le_of_le_centralizer_dThree hHc hHp hH7 hR hR3 hz
    obtain ⟨l, hl, rfl⟩ := (mem_imgTen Y₀ φ).mp hw
    exact ⟨l, hl, hwz⟩

end CFSG.RankThree.PartTwo.Sec17.Proof17Res4
