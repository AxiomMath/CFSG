module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Open.LocalVocabulary
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private theorem s1614_st_mem_stabSub_fixV {V : Type*} [CommGroup V] {B : Subgroup (MulAut V)}
    {g : MulAut V} (h : ∀ b ∈ B, b * g = g * b) : g ∈ stabSub (fixV B) := by
  intro u
  have key : ∀ b ∈ B, b (g u) = g (b u) := fun b hb => by
    have := congrArg (fun φ : MulAut V => φ u) (h b hb)
    simpa using this
  constructor
  · intro hu b hb
    have h1 : b (g u) = g u := hu b hb
    rw [key b hb] at h1
    exact g.injective h1
  · intro hu b hb
    rw [key b hb, hu b hb]

theorem s1614_blocks_stab {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    {A : Subgroup (MulAut W)} (hA : IsElemAbelian 3 A) (hA27 : Nat.card ↥A = 27)
    {h : MulAut W} (hh : h ∈ A) (hrk : rk ↥(fixV (Subgroup.zpowers h)) = 2) :
    ∃ B : Subgroup (MulAut W), B ≤ A ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
      ∀ y ∈ fixV (Subgroup.zpowers h), y ∈ fixV B := by
  classical
  have hV2 : ∀ v : W, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hW v
  let Y : Subgroup W := fixV (Subgroup.zpowers h)
  have hYcard : Nat.card ↥Y = 2 ^ 2 := by
    simpa [Y, hrk] using card_eq_two_pow hV2 Y
  have hAstab : A ≤ stabSub Y := by
    intro a ha
    refine s1614_st_mem_stabSub_fixV (B := Subgroup.zpowers h) ?_
    intro b hb
    have hcomm : h * a = a * h :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨h, hh⟩ ⟨a, ha⟩)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute h a from hcomm).zpow_left k).eq
  have hcard := card_autSub_mul (A := A) (U := Y) hAstab
  rw [hA27] at hcard
  have hAutY : Nat.card (MulAut ↥Y) = 6 := by
    have hY2 : ∀ e : ↥Y, e * e = 1 := fun e => Subtype.ext (by simpa using hW (e : W))
    rw [CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two hY2 2 hYcard]
    norm_num [Fin.prod_univ_succ]
  have hdvd6 : Nat.card (autSub A Y) ∣ 6 := by
    rw [← hAutY]
    exact Subgroup.card_subgroup_dvd_card (autSub A Y)
  have hdvd27 : Nat.card (autSub A Y) ∣ 27 := ⟨Nat.card ↥(A ⊓ centSub Y), hcard.symm⟩
  have hle3 : Nat.card (autSub A Y) ≤ 3 := by
    refine Nat.le_of_dvd (by norm_num) ?_
    have h := Nat.dvd_gcd hdvd6 hdvd27
    norm_num at h
    exact h
  have hBcard : 9 ≤ Nat.card ↥(A ⊓ centSub Y) := by
    have h3 := Nat.mul_le_mul_right (Nat.card ↥(A ⊓ centSub Y)) hle3
    rw [hcard] at h3
    omega
  refine ⟨A ⊓ centSub Y, inf_le_left, ?_, ?_, ?_⟩
  · intro x
    exact ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa using hA.2 x.1 x.2.1)⟩
  · intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hA.2 g.1 g.2.1)
    have horder : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    have hcardg : Nat.card ↥(A ⊓ centSub Y) = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) horder
    omega
  · intro y hy
    rw [mem_fixV]
    intro b hb
    exact (mem_centSub.mp hb.2) y hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
