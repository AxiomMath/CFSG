module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
public import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem le_inner_of_card_outer_three {X : Type*} [Group X] [Finite X]
    (hO : Nat.card (Outer X) = 3) {Y : Subgroup (MulAut X)} (hY : ¬ 3 ∣ Nat.card Y) :
    Y ≤ (MulAut.conj : X →* MulAut X).range := by
  set q : MulAut X →* Outer X := QuotientGroup.mk' (inner X) with hq
  intro φ hφ
  have h1 : orderOf (q φ) ∣ Nat.card Y :=
    (orderOf_map_dvd q φ).trans (Subgroup.orderOf_dvd_natCard Y hφ)
  have h2 : orderOf (q φ) ∣ 3 := hO ▸ orderOf_dvd_natCard (q φ)
  have h3 : orderOf (q φ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
    · exact h
    · exact absurd (h ▸ h1) hY
  have h4 : q φ = 1 := orderOf_eq_one_iff.mp h3
  exact (QuotientGroup.eq_one_iff φ).mp h4

variable {X : Type*} [Group X]

theorem conj_aut_apply (φ : MulAut X) (x : X) :
    MulAut.conj (φ x) = φ * MulAut.conj x * φ⁻¹ := by
  ext y
  simp [MulAut.conj_apply]

theorem apply_eq_of_commute (hinj : Function.Injective (MulAut.conj : X →* MulAut X))
    {φ : MulAut X} {x : X} (h : φ * MulAut.conj x = MulAut.conj x * φ) : φ x = x := by
  apply hinj
  rw [conj_aut_apply, h]
  group

theorem eq_bot_of_hyperplanes [Finite X] (hZ : Subgroup.center X = ⊥)
    (hO : Nat.card (Outer X) = 3)
    {N : Subgroup (MulAut X)} (hN : CFSG.Assembly.IsElemAbelian 3 N) (hN27 : Nat.card N = 27)
    {E : Subgroup X} (hEN : E.map (MulAut.conj : X →* MulAut X) ≤ N)
    (hcent : ∀ E' : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E' → Nat.card E' = 9 →
      ∀ x : X, (∀ e ∈ E', x * e = e * x) → x ^ 9 = 1)
    (hfix : ∀ α : MulAut X, α ^ 3 = 1 → α ∉ (MulAut.conj : X →* MulAut X).range →
      (∀ e ∈ E, α e = e) → ∀ W : Subgroup X, ¬ 3 ∣ Nat.card W → (∀ w ∈ W, α w = w) →
        E ≤ Subgroup.normalizer (W : Set X) → W = ⊥)
    {Y : Subgroup (MulAut X)} (hY3 : ¬ 3 ∣ Nat.card Y)
    (hYN : N ≤ Subgroup.normalizer (Y : Set (MulAut X))) : Y = ⊥ := by
  have : Finite (MulAut X) := MulEquiv.finite_left
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hZ
  have hYin := le_inner_of_card_outer_three hO hY3
  set W := Y.comap (MulAut.conj : X →* MulAut X) with hW
  have hWY : W.map (MulAut.conj : X →* MulAut X) = Y := Subgroup.map_comap_eq_self hYin
  have hWcard : Nat.card W = Nat.card Y := by
    conv_rhs => rw [← hWY]
    rw [Subgroup.card_map_of_injective hinj]
  have hW3 : ¬ 3 ∣ Nat.card W := by rw [hWcard]; exact hY3
  rw [← le_bot_iff]
  refine CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_sub_le (p := 3) (k := 2)
    Nat.prime_three hN (by rw [hN27]; norm_num) hYN
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3) ?_
  intro H hHN hH9 φ hφ
  obtain ⟨hφY, hφC⟩ := hφ
  rw [Subgroup.mem_bot]
  obtain ⟨w, hwW, rfl⟩ : ∃ w ∈ W, MulAut.conj w = φ := by
    have : φ ∈ W.map (MulAut.conj : X →* MulAut X) := hWY ▸ hφY
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp this
    exact ⟨w, hw, rfl⟩
  suffices hw1 : w = 1 by rw [hw1, map_one]
  by_cases hHinn : ∀ ψ ∈ H, ψ ∈ (MulAut.conj : X →* MulAut X).range
  ·
    set EH := H.comap (MulAut.conj : X →* MulAut X) with hEH
    have hEHmap : EH.map (MulAut.conj : X →* MulAut X) = H :=
      Subgroup.map_comap_eq_self fun ψ hψ => hHinn ψ hψ
    have hEHcard : Nat.card EH = 9 := by
      rw [← Subgroup.card_map_of_injective hinj, hEHmap, hH9]
      norm_num
    have hEHe : CFSG.Assembly.IsElemAbelian 3 EH :=
      Item434Kit.isElemAbelian_of_map_injective hinj
        (by rw [hEHmap]; exact CFSG.RankThree.PartTwo.Sec5.isElemAbelian_of_le hN hHN)
    have hwc : ∀ e ∈ EH, w * e = e * w := by
      intro e he
      have h1 : MulAut.conj e ∈ H := by
        have : MulAut.conj e ∈ EH.map (MulAut.conj : X →* MulAut X) :=
          Subgroup.mem_map_of_mem _ he
        rwa [hEHmap] at this
      have h2 := Subgroup.mem_centralizer_iff.mp hφC (MulAut.conj e) h1
      apply hinj
      rw [map_mul, map_mul]
      exact h2.symm
    have h9 := hcent EH hEHe hEHcard w hwc
    have hdvd1 : orderOf w ∣ 3 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one h9
    have hdvd2 : orderOf w ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hwW
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd1
    rcases i with _ | i
    · exact orderOf_eq_one_iff.mp (by simpa using hi)
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero i)).trans (hi ▸ hdvd2)) hW3
  ·
    push Not at hHinn
    obtain ⟨v, hvH, hvout⟩ := hHinn
    have hvN : v ∈ N := hHN hvH
    have hv3 : v ^ 3 = 1 := hN.2 v hvN
    have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hN.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hvE : ∀ e ∈ E, v e = e := by
      intro e he
      refine apply_eq_of_commute hinj ?_
      exact hNcomm v hvN _ (hEN (Subgroup.mem_map_of_mem _ he))
    let Wv : Subgroup X :=
      { carrier := {x | x ∈ W ∧ v x = x}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          exact ⟨W.mul_mem ha hb, by rw [map_mul, ha', hb']⟩
        one_mem' := ⟨W.one_mem, map_one v⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          exact ⟨W.inv_mem ha, by rw [map_inv, ha']⟩ }
    have hmemWv : ∀ x, x ∈ Wv ↔ x ∈ W ∧ v x = x := fun x => Iff.rfl
    have hWvN : E ≤ Subgroup.normalizer (Wv : Set X) := by
      have key : ∀ e ∈ E, ∀ x ∈ Wv, e * x * e⁻¹ ∈ Wv := by
        intro e he x hx
        rw [hmemWv] at hx ⊢
        obtain ⟨hxW, hvx⟩ := hx
        refine ⟨?_, ?_⟩
        · have hcn := hYN (hEN (Subgroup.mem_map_of_mem _ he))
          have hcx : MulAut.conj x ∈ Y := hxW
          have := (Subgroup.mem_normalizer_iff.mp hcn (MulAut.conj x)).mp hcx
          have e1 : MulAut.conj e * MulAut.conj x * (MulAut.conj e)⁻¹ =
              MulAut.conj (e * x * e⁻¹) := by
            rw [map_mul, map_mul, map_inv]
          rw [e1] at this
          exact this
        · rw [map_mul, map_mul, map_inv, hvx, hvE e he]
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => key e he x hx, fun hx => ?_⟩
      have h2 := key e⁻¹ (E.inv_mem he) _ hx
      have e2 : e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x := by group
      rwa [e2] at h2
    have hWv3 : ¬ 3 ∣ Nat.card Wv := fun h =>
      hW3 (h.trans (Subgroup.card_dvd_of_le (fun x hx => ((hmemWv x).mp hx).1)))
    have hbot := hfix v hv3 hvout hvE Wv hWv3 (fun w' hw' => ((hmemWv w').mp hw').2) hWvN
    have hwv : w ∈ Wv := by
      rw [hmemWv]
      refine ⟨hwW, ?_⟩
      exact apply_eq_of_commute hinj (Subgroup.mem_centralizer_iff.mp hφC v hvH)
    rw [hbot] at hwv
    exact Subgroup.mem_bot.mp hwv

end CFSG.RankThree.PartTwo.Sec4.Item434G28
