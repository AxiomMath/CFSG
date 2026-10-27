module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2Step0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AStep

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_inv_mul_inv_mul_eq_one_iff {u v : G} (hu : u * u = 1) :
    v⁻¹ * u⁻¹ * v * u = 1 ↔ v * u = u * v := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  rw [hui]
  constructor
  · intro h
    have h1 : u * v * u = v := by
      calc u * v * u = v * (v⁻¹ * u * v * u) := by group
        _ = v * 1 := by rw [h]
        _ = v := by group
    have h2 : u * v = v * u := by
      calc u * v = (u * v * u) * u⁻¹ := by group
        _ = v * u⁻¹ := by rw [h1]
        _ = v * u := by rw [hui]
    exact h2.symm
  · intro h
    have h1 : u * v * u = v := by
      calc u * v * u = (v * u) * u := by rw [← h]
        _ = v * (u * u) := by group
        _ = v * 1 := by rw [hu]
        _ = v := by group
    calc v⁻¹ * u * v * u = v⁻¹ * (u * v * u) := by group
      _ = v⁻¹ * v := by rw [h1]
      _ = 1 := by group

theorem c23ne_transvection_mul {V Y : Subgroup G} (hV : IsElemAbelian 2 V) (hY : mSub Y = 1)
    {s t : G} (hs : s ∈ normalizer (V : Set G)) (ht : t ∈ normalizer (V : Set G))
    (hs2 : s ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hst : V ⊓ centralizer ({s} : Set G) = V ⊓ centralizer ({t} : Set G))
    (hsY : commElt V s = Y) (htY : commElt V t = Y) :
    V ≤ centralizer ({s * t} : Set G) := by
  have hs1 : s * s = 1 := by simpa [pow_two] using hs2
  have ht1 : t * t = 1 := by simpa [pow_two] using ht2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs1
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht1
  have hYV : Y ≤ V := by
    rw [← hsY]
    refine (Subgroup.closure_le V).2 ?_
    rintro x ⟨w, hw, rfl⟩
    have h1 : s⁻¹ * w * s ∈ V := (Subgroup.mem_normalizer_iff''.1 hs w).1 hw
    have h2 : w⁻¹ * (s⁻¹ * w * s) ∈ V := V.mul_mem (V.inv_mem hw) h1
    simpa only [mul_assoc, SetLike.mem_coe] using h2
  have hYpg : IsPGroup 2 ↥Y := hV.isPGroup.to_le hYV
  have hcardY : Nat.card Y = 2 := by
    rw [card_eq_two_pow_mSub hYpg, hY]
    norm_num
  have huniq : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨y, _, hyu⟩ := (Nat.card_eq_two_iff' (1 : Y)).1 hcardY
    have ha' : (⟨a, ha⟩ : Y) ≠ 1 := fun h => ha1 (by simpa using congrArg Subtype.val h)
    have hb' : (⟨b, hb⟩ : Y) ≠ 1 := fun h => hb1 (by simpa using congrArg Subtype.val h)
    exact Subtype.ext_iff.1 ((hyu ⟨a, ha⟩ ha').trans (hyu ⟨b, hb⟩ hb').symm)
  have hYcent : Y ≤ centralizer ({s} : Set G) := by
    rw [← hsY]
    refine (Subgroup.closure_le (centralizer ({s} : Set G))).2 ?_
    rintro x ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hy : w⁻¹ * s⁻¹ * w * s ∈ Y := by
      rw [← hsY]
      exact Subgroup.subset_closure ⟨w, hw, rfl⟩
    have hgw : w⁻¹ * s⁻¹ * w * s ∈ V := hYV hy
    have hg2 : (w⁻¹ * s⁻¹ * w * s) * (w⁻¹ * s⁻¹ * w * s) = 1 :=
      hV.mul_self_eq_one hgw
    have hginv : (w⁻¹ * s⁻¹ * w * s)⁻¹ = w⁻¹ * s⁻¹ * w * s :=
      inv_eq_of_mul_eq_one_right hg2
    have hconj : s * (w⁻¹ * s⁻¹ * w * s) * s⁻¹ = w⁻¹ * s⁻¹ * w * s := by
      calc s * (w⁻¹ * s⁻¹ * w * s) * s⁻¹
          = s * w⁻¹ * s⁻¹ * w * (s * s⁻¹) := by group
        _ = s * w⁻¹ * s⁻¹ * w := by rw [mul_inv_cancel, mul_one]
        _ = (w⁻¹ * s⁻¹ * w * s)⁻¹ := by
              simp only [mul_inv_rev, inv_inv]
              rw [hsi]
              group
        _ = w⁻¹ * s⁻¹ * w * s := hginv
    calc (w⁻¹ * s⁻¹ * w * s) * s
        = (s * (w⁻¹ * s⁻¹ * w * s) * s⁻¹) * s := by rw [hconj]
      _ = s * (w⁻¹ * s⁻¹ * w * s) := by group
  have hfixY : ∀ y ∈ Y, s * y * s⁻¹ = y := by
    intro y hy
    have hyc : y * s = s * y :=
      Subgroup.mem_centralizer_singleton_iff.1 (hYcent hy)
    calc s * y * s⁻¹ = (y * s) * s⁻¹ := by rw [← hyc]
      _ = y := by group
  intro v hv
  have hys1 : v⁻¹ * s⁻¹ * v * s = 1 ↔ v ∈ centralizer ({s} : Set G) := by
    rw [c23ne_inv_mul_inv_mul_eq_one_iff hs1, Subgroup.mem_centralizer_singleton_iff]
  have hyt1 : v⁻¹ * t⁻¹ * v * t = 1 ↔ v ∈ centralizer ({t} : Set G) := by
    rw [c23ne_inv_mul_inv_mul_eq_one_iff ht1, Subgroup.mem_centralizer_singleton_iff]
  have hcent : v ∈ centralizer ({s} : Set G) ↔ v ∈ centralizer ({t} : Set G) := by
    have hmem := SetLike.ext_iff.1 hst v
    simpa [hv] using hmem
  have hy_s : v⁻¹ * s⁻¹ * v * s ∈ Y := by
    rw [← hsY]
    exact Subgroup.subset_closure ⟨v, hv, rfl⟩
  have hy_t : v⁻¹ * t⁻¹ * v * t ∈ Y := by
    rw [← htY]
    exact Subgroup.subset_closure ⟨v, hv, rfl⟩
  have hysyt : v⁻¹ * s⁻¹ * v * s = v⁻¹ * t⁻¹ * v * t := by
    by_cases hys : v⁻¹ * s⁻¹ * v * s = 1
    · have hyt : v⁻¹ * t⁻¹ * v * t = 1 :=
        hyt1.2 (hcent.1 (hys1.1 hys))
      rw [hys, hyt]
    · have hyt : v⁻¹ * t⁻¹ * v * t ≠ 1 := by
        intro h
        exact hys (hys1.2 (hcent.2 (hyt1.1 h)))
      exact huniq _ hy_s _ hy_t hys hyt
  have hσs : s * v * s⁻¹ = v * (v⁻¹ * s⁻¹ * v * s) := by
    rw [hsi]
    group
  have hσt : t * v * t⁻¹ = v * (v⁻¹ * t⁻¹ * v * t) := by
    rw [hti]
    group
  have hmain : (s * t) * v * (s * t)⁻¹ = v := by
    calc (s * t) * v * (s * t)⁻¹
        = s * (t * v * t⁻¹) * s⁻¹ := by rw [mul_inv_rev]; group
      _ = s * (v * (v⁻¹ * t⁻¹ * v * t)) * s⁻¹ := by rw [hσt]
      _ = (s * v * s⁻¹) * (s * (v⁻¹ * t⁻¹ * v * t) * s⁻¹) := by group
      _ = (v * (v⁻¹ * s⁻¹ * v * s)) * (v⁻¹ * t⁻¹ * v * t) := by
            rw [hσs, hfixY _ hy_t]
      _ = v := by
            have hT2 : (v⁻¹ * t⁻¹ * v * t) * (v⁻¹ * t⁻¹ * v * t) = 1 :=
              hV.mul_self_eq_one (hYV hy_t)
            calc (v * (v⁻¹ * s⁻¹ * v * s)) * (v⁻¹ * t⁻¹ * v * t)
                = v * ((v⁻¹ * t⁻¹ * v * t) * (v⁻¹ * t⁻¹ * v * t)) := by
                    rw [hysyt]
                    group
              _ = v * 1 := by rw [hT2]
              _ = v := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc v * (s * t) = ((s * t) * v * (s * t)⁻¹) * (s * t) := by rw [hmain]
    _ = (s * t) * v := by group

variable {M V₀ V N₁ N₂ Y : Subgroup G} {g : G}

theorem c23ne_step1 (h : C23NeO2 M V₀ V N₁ N₂ Y g) (h0 : conjSubgroup V₀ g ≤ M)
    (hc : ∀ w ∈ conjSubgroup V₀ g, w ≠ 1 →
      V ⊓ centralizer ({w} : Set G) = V ⊓ conjSubgroup M g) :
    E3.mQuot V (conjSubgroup M g) = 2 ∧ (N₁ ≤ conjSubgroup M g ∨ N₂ ≤ conjSubgroup M g) := by
  have hV := h.pair.elem
  have hUV : V ⊓ conjSubgroup M g ≤ V := inf_le_left
  have hmeq : E3.mQuot V (V ⊓ conjSubgroup M g) = E3.mQuot V (conjSubgroup M g) :=
    c23a_o2_mQuot_inf_left V _
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup N₁ g := by
    rw [← h.pair'.inf]; exact inf_le_left
  have hnotU : ¬ V ≤ V ⊓ conjSubgroup M g := fun hle => h.notLe' (hle.trans inf_le_right)
  have hrank : ∀ w ∈ conjSubgroup V₀ g, w ≠ 1 →
      mSub (commElt V w) = E3.mQuot V (conjSubgroup M g) ∧
        ¬ V ≤ centralizer ({w} : Set G) ∧ w ∈ M ∧ w ^ 2 = 1 := by
    intro w hw hw1
    have hwM := h0 hw
    have hw2 : w ^ 2 = 1 := h.pair'.elem.2 w (h.pair'.le₁ (hV₀g hw))
    have hsplit := c23a_mSub_commElt_add hV (h.pair.norm hwM)
    rw [hc w hw hw1] at hsplit
    have hquot := c23a_o2_mQuot_eq_rk_sub hUV
    refine ⟨?_, ?_, hwM, hw2⟩
    · rw [← hmeq]
      simp only [mSub] at hsplit hquot ⊢
      omega
    · intro hle
      apply hnotU
      have h1 : V ⊓ centralizer ({w} : Set G) = V := inf_eq_left.2 hle
      rw [← hc w hw hw1, h1]
  have hm2 : E3.mQuot V (conjSubgroup M g) ≤ 2 := h.mU
  have hm0 : E3.mQuot V (conjSubgroup M g) ≠ 0 := by
    intro h0'
    rw [← hmeq] at h0'
    exact hnotU ((E3.mQuot_eq_zero_iff hV.isPGroup hUV).1 h0').symm.le
  have hcard : 3 ≤ Nat.card ↥(conjSubgroup V₀ g) := by rw [c23ne_card_conj_V₀ h]; norm_num
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := c23ne_exists_two_ne_one hcard
  have hm1 : E3.mQuot V (conjSubgroup M g) ≠ 1 := by
    intro h1
    have hY : ∀ w ∈ conjSubgroup V₀ g, w ≠ 1 → commElt V w = Y := by
      intro w hw hw1
      obtain ⟨hr, hnot, hwM, hw2⟩ := hrank w hw hw1
      rcases h.pair.oneSided w hwM hw2 hnot (by rw [hr]; omega) with ⟨-, hY⟩ | ⟨h2, -⟩
      · exact hY
      · omega
    obtain ⟨-, -, haM, ha2⟩ := hrank a ha ha1
    obtain ⟨-, -, hbM, hb2⟩ := hrank b hb hb1
    have hab1 : a * b ≠ 1 := by
      intro h'
      apply hab
      have h3 : a = b⁻¹ := eq_inv_of_mul_eq_one_left h'
      have h4 : b⁻¹ = b := by
        have : b * b = 1 := by simpa [pow_two] using hb2
        exact (inv_eq_of_mul_eq_one_right this)
      rw [h3, h4]
    have hcent : V ≤ centralizer ({a * b} : Set G) :=
      c23ne_transvection_mul hV h.pair.rank_Y (h.pair.norm haM) (h.pair.norm hbM) ha2 hb2
        ((hc a ha ha1).trans (hc b hb hb1).symm) (hY a ha ha1) (hY b hb hb1)
    have hab_mem : a * b ∈ conjSubgroup V₀ g := (conjSubgroup V₀ g).mul_mem ha hb
    apply hnotU
    have h3 : V ⊓ centralizer ({a * b} : Set G) = V := inf_eq_left.2 hcent
    rw [← hc (a * b) hab_mem hab1, h3]
  have hm_eq : E3.mQuot V (conjSubgroup M g) = 2 := by omega
  refine ⟨hm_eq, ?_⟩
  obtain ⟨hr, hnot, hwM, hw2⟩ := hrank a ha ha1
  rcases h.pair.oneSided a hwM hw2 hnot (by rw [hr, hm_eq]) with ⟨h1', -⟩ | ⟨-, -, hside⟩
  · rw [hr, hm_eq] at h1'
    omega
  · rcases hside with ⟨hcent, -⟩ | ⟨hcent, -⟩
    · right
      have hle : N₂ ≤ V ⊓ centralizer ({a} : Set G) := fun y hy =>
        Subgroup.mem_inf.2 ⟨h.pair.le₂ hy,
          Subgroup.mem_centralizer_singleton_iff.2 (hcent y hy).symm⟩
      rw [hc a ha ha1] at hle
      exact hle.trans inf_le_right
    · left
      have hle : N₁ ≤ V ⊓ centralizer ({a} : Set G) := fun y hy =>
        Subgroup.mem_inf.2 ⟨h.pair.le₁ hy,
          Subgroup.mem_centralizer_singleton_iff.2 (hcent y hy).symm⟩
      rw [hc a ha ha1] at hle
      exact hle.trans inf_le_right

theorem c23ne_step1' (h : C23NeO2 M V₀ V N₁ N₂ Y g) (h0 : V₀ ≤ conjSubgroup M g)
    (hc : ∀ w ∈ V₀, w ≠ 1 →
      conjSubgroup V g ⊓ centralizer ({w} : Set G) = conjSubgroup V g ⊓ M) :
    E3.mQuot (conjSubgroup V g) M = 2 ∧ (conjSubgroup N₁ g ≤ M ∨ conjSubgroup N₂ g ≤ M) := by
  have h1 := c23ne_step1 h.swap (by simpa only [conjSubgroup_conjSubgroup_inv] using h0)
    (by simpa only [conjSubgroup_conjSubgroup_inv] using hc)
  simpa only [conjSubgroup_conjSubgroup_inv] using h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
