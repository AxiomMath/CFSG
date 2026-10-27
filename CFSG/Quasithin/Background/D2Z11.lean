module

public import CFSG.Quasithin.Background.D2Z9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def Pfam (X : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {Y | Y ≤ pCoreOf 3 X ∧ Nat.card Y = 3 ∧ rk (commV Y) = 2}

section Canon

variable {X : Subgroup (MulAut V)} {s : ℕ} {Pi : Fin s → Subgroup (MulAut V)}

theorem PDecomp.eq_one_of_trivial_on_V (hV : ∀ v : V, v ^ 2 = 1) (d : PDecomp X Pi)
    {g : MulAut V} (hg : g ∈ pCoreOf 3 X) (hgV : ∀ i, ∀ v ∈ commV (Pi i), g v = v) : g = 1 := by
  have hdir := isDirectSum_commV_fixV hV X
  have hU : commV (pCoreOf 3 X) ≤ fixV (Subgroup.zpowers g) := by
    rw [← d.vsup]
    refine iSup_le fun i v hv => ?_
    exact mem_fixV_zpowers_iff.mpr (hgV i v hv)
  have hW : fixV (pCoreOf 3 X) ≤ fixV (Subgroup.zpowers g) :=
    fixV_anti (Subgroup.zpowers_le.mpr hg)
  apply eq_one_of_fixV_eq_top
  rw [eq_top_iff, ← hdir.1]
  exact sup_le hU hW

theorem PDecomp.range_eq (hV : ∀ v : V, v ^ 2 = 1) (d : PDecomp X Pi)
    (hcomm : ∀ x ∈ pCoreOf 3 X, ∀ y ∈ pCoreOf 3 X, x * y = y * x) :
    Set.range Pi = Pfam X := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  ext Y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨d.le_P i, d.card_eq i, d.rk_eq i⟩
  · rintro ⟨hYP, hYcard, hYrk⟩
    obtain ⟨y, hyY, hy1, hyz, hyo⟩ := exists_generator_of_prime_card (p := 3) hYcard
    have hyP : y ∈ pCoreOf 3 X := hYP hyY
    have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    have hK : ∀ i, (⨆ (j) (_ : j ≠ i), Pi j) ≤ pCoreOf 3 X := fun i =>
      iSup₂_le fun j _ => d.le_P j
    have hKtriv : ∀ i, ∀ q ∈ (⨆ (j) (_ : j ≠ i), Pi j), ∀ v ∈ commV (Pi i), q v = v := by
      intro i q hq v hv
      have hle : (⨆ (j) (_ : j ≠ i), Pi j) ≤ centSub (commV (Pi i)) :=
        iSup₂_le fun j hj g hg w hw => d.triv i j (Ne.symm hj) hw g hg
      exact hle hq v hv
    have hfac : ∀ i, ∃ p ∈ Pi i, ∃ q ∈ (⨆ (j) (_ : j ≠ i), Pi j), y = p * q := by
      intro i
      have hsplit : pCoreOf 3 X = Pi i ⊔ ⨆ (j) (_ : j ≠ i), Pi j := by
        rw [← d.sup_eq]
        exact iSup_split_single Pi i
      have hc : ∀ a ∈ Pi i, ∀ b ∈ (⨆ (j) (_ : j ≠ i), Pi j), a * b = b * a := fun a ha b hb =>
        hcomm a (d.le_P i ha) b (hK i hb)
      obtain ⟨p, hp, q, hq, e⟩ := mem_sup_of_forall_commute hc (hsplit ▸ hyP)
      exact ⟨p, hp, q, hq, e⟩
    choose p hp q hq hy using hfac
    have hA : ∀ i, p i ≠ 1 → commV (Pi i) ≤ commV (Subgroup.zpowers y) := by
      intro i hpi
      have hyV : ∀ w ∈ commV (Pi i), y w = p i w := by
        intro w hw
        rw [hy i]
        show p i (q i w) = p i w
        rw [hKtriv i (q i) (hq i) w hw]
      have hpz : Subgroup.zpowers (p i) = Pi i := zpowers_eq_of_prime_card (d.card_eq i) (hp i) hpi
      have hinvp : ∀ w ∈ commV (Pi i), p i w ∈ commV (Pi i) := fun w hw =>
        commV_smul_mem (fun x hx => (Pi i).mul_mem ((Pi i).mul_mem (hp i) hx)
          ((Pi i).inv_mem (hp i))) hw
      have hinvy : ∀ w ∈ commV (Pi i), y w ∈ commV (Pi i) := fun w hw => by
        rw [hyV w hw]; exact hinvp w hw
      have hys : y ∈ stabSub (commV (Pi i)) := mem_stabSub_of_cube hy3 hinvy
      have hinvz : ∀ x ∈ Subgroup.zpowers y, ∀ w ∈ commV (Pi i), x w ∈ commV (Pi i) :=
        fun x hx w hw => ((mem_stabSub.mp (Subgroup.zpowers_le.mpr hys hx)) w).mpr hw
      have hfixbot : commV (Pi i) ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
        rw [eq_bot_iff]
        rintro w ⟨hw, hwf⟩
        have h1 : y w = w := mem_fixV_zpowers_iff.mp hwf
        rw [hyV w hw] at h1
        have h2 : w ∈ fixV (Pi i) := by
          rw [← hpz]; exact mem_fixV_zpowers_iff.mpr h1
        have : w ∈ commV (Pi i) ⊓ fixV (Pi i) := ⟨hw, h2⟩
        rwa [(commV_card_three hV (d.card_eq i)).2.1, Subgroup.mem_bot] at this
      have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
        rw [Nat.card_zpowers, hyo]; exact ⟨1, rfl⟩
      obtain ⟨hsup, -⟩ := coprime_decomp hodd hV hinvz
      rw [hfixbot, sup_bot_eq] at hsup
      refine hsup.symm.le.trans ?_
      rw [commV_eq_commSub (Subgroup.zpowers y)]
      exact commSub_mono le_top le_rfl
    have hB : ∀ i j, p i ≠ 1 → p j ≠ 1 → i = j := by
      intro i j hi hj
      by_contra hij
      have hdisj := d.vindep.pairwiseDisjoint hij
      have hsup : commV (Pi i) ⊔ commV (Pi j) ≤ commV (Subgroup.zpowers y) :=
        sup_le (hA i hi) (hA j hj)
      have h1 := rk_sup_add_rk_inf (commV (Pi i)) (commV (Pi j))
      rw [disjoint_iff.mp hdisj, rk_bot, d.rk_eq i, d.rk_eq j] at h1
      have h2 := rk_mono hsup
      rw [hyz, hYrk] at h2
      omega
    have hC : ∃ i, p i ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hy1
      refine d.eq_one_of_trivial_on_V hV hyP fun i v hv => ?_
      rw [hy i, hcon i, one_mul]
      exact hKtriv i (q i) (hq i) v hv
    obtain ⟨i₀, hi₀⟩ := hC
    have hq1 : q i₀ = 1 := by
      refine d.eq_one_of_trivial_on_V hV ((hK i₀) (hq i₀)) fun l v hv => ?_
      by_cases hl : l = i₀
      · subst hl
        exact hKtriv l (q l) (hq l) v hv
      · have hpl : p l = 1 := by
          by_contra hne
          exact hl (hB l i₀ hne hi₀)
        have hyv : y v = v := by
          rw [hy l, hpl, one_mul]
          exact hKtriv l (q l) (hq l) v hv
        have hpv : p i₀ v = v := (d.triv l i₀ hl) hv (p i₀) (hp i₀)
        have : y v = p i₀ (q i₀ v) := by rw [hy i₀]; rfl
        rw [hyv] at this
        have h3 : p i₀ (q i₀ v) = p i₀ v := by rw [← this, hpv]
        exact (p i₀).injective h3
    have hyp : y = p i₀ := by rw [hy i₀, hq1, mul_one]
    have hle : Y ≤ Pi i₀ := by
      rw [← hyz]
      exact Subgroup.zpowers_le.mpr (hyp ▸ hp i₀)
    exact ⟨i₀, (Subgroup.eq_of_le_of_card_ge hle (by rw [d.card_eq i₀, hYcard])).symm⟩

end Canon

end CFSG.Quasithin
