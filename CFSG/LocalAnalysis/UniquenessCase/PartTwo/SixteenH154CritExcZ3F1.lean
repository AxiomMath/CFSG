module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3R7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3R5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16h_isPGroup_two_of_coprime_three {W : Type} [CommGroup W] [Finite W]
    (hcard : Nat.card W = 64) {l : MulAut W} (hl : orderOf l = 3)
    (hfpf : ∀ w : W, l w = w → w = 1) {D J : Subgroup (MulAut W)} (hD : IsElemAbelian 3 D)
    (hD27 : 27 ≤ Nat.card ↥D) (hDl : D ≤ centralizer ({l} : Set (MulAut W)))
    (hJl : J ≤ centralizer ({l} : Set (MulAut W))) (hDJ : D ≤ normalizer (J : Set (MulAut W)))
    (hJ3 : ¬ 3 ∣ Nat.card ↥J) : IsPGroup 2 J := by
  classical
  have hprime : ∀ ⦃r : ℕ⦄, r.Prime → r ∣ Nat.card ↥J → r = 2 := by
    intro r hr hrdvd
    by_contra hr2
    have hr3 : r ≠ 3 := fun h => hJ3 (h ▸ hrdvd)
    have hr5 : 5 ≤ r := by
      have h2 : 2 ≤ r := hr.two_le
      have h4 : r ≠ 4 := by
        rintro rfl
        exact (by norm_num : ¬ Nat.Prime 4) hr
      omega
    let α : ↥D →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hDJ)
    have hα : ∀ (d : ↥D) (x : ↥J),
        J.subtype ((α d) x) = (d : MulAut W) * (x : MulAut W) * (d : MulAut W)⁻¹ := fun d x =>
      Subgroup.normalizerMonoidHom_apply_apply_coe J (Subgroup.inclusion hDJ d) x
    have hDpg : IsPGroup 3 ↥D := fun x => ⟨1, by
      show x ^ (3 ^ 1) = 1
      rw [pow_one]
      exact Subtype.ext (hD.2 x.1 x.2)⟩
    obtain ⟨P, hP⟩ := CFSG.SolvableSignalizer.exists_sylow_isInvariant 3 (by norm_num)
      hDpg α r hr hJ3
    letI : Fact r.Prime := ⟨hr⟩
    have hPne : (P : Subgroup ↥J) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hrdvd
    set R : Subgroup (MulAut W) := (P : Subgroup ↥J).map J.subtype with hRdef
    have hRle : R ≤ J := by
      rw [hRdef]
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hRl : R ≤ centralizer ({l} : Set (MulAut W)) := hRle.trans hJl
    have hRne : R ≠ ⊥ := by
      rw [hRdef]
      intro h
      exact hPne ((Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup ↥J))
        J.subtype_injective).mp h)
    have hRr : IsPGroup r R := by
      rw [hRdef]
      exact P.isPGroup'.map J.subtype
    have hDR : D ≤ normalizer (R : Set (MulAut W)) := by
      intro d hd
      refine (Subgroup.mem_normalizer_iff (H := R) (g := d)).mpr ?_
      intro h
      constructor
      · rintro ⟨y, hyP, rfl⟩
        have hmem : α ⟨d, hd⟩ y ∈ (P : Subgroup ↥J) := by
          rw [← hP ⟨d, hd⟩]
          exact (Subgroup.mem_map_iff_mem (α ⟨d, hd⟩).injective).mpr hyP
        exact ⟨α ⟨d, hd⟩ y, hmem, by simpa using (hα ⟨d, hd⟩ y)⟩
      · intro hmem
        obtain ⟨y, hyP, hyh⟩ := hmem
        have hmem' : (α ((⟨d, hd⟩)⁻¹)) y ∈ (P : Subgroup ↥J) := by
          rw [← hP ((⟨d, hd⟩)⁻¹)]
          exact (Subgroup.mem_map_iff_mem (α ((⟨d, hd⟩)⁻¹)).injective).mpr hyP
        refine ⟨(α ((⟨d, hd⟩)⁻¹)) y, hmem', ?_⟩
        have hyh' : (y : MulAut W) = d * h * d⁻¹ := hyh
        rw [hα ((⟨d, hd⟩)⁻¹) y, hyh']
        simp only [zpow_neg_one, Subgroup.coe_inv, inv_inv]
        group
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' r hrdvd
    have hρl : (x : MulAut W) * l = l * (x : MulAut W) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hJl x.2)
    have hρord : orderOf (x : MulAut W) = r := by
      rw [Subgroup.orderOf_coe, hxord]
    rcases s16h_fix_card_of_prime_Z3 hcard hl hfpf hρl hr hr5 hρord with
      ⟨hr7eq, _⟩ | ⟨hr5eq, _⟩
    · subst hr7eq
      exact s16h_false_of_seven_torus hcard hl hfpf hRl hRr hRne hDl hD hD27 hDR
    · subst hr5eq
      exact s16h_false_of_five_torus hcard hl hfpf hRl hRr hRne hD hD27 hDR
  have hpos : Nat.card ↥J ≠ 0 := Nat.card_pos.ne'
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos ?_)
  intro d hd hdvd
  exact hprime (r := d) hd hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
