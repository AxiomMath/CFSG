module

public import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_notMem_zpowers_of_card_nine {E : Subgroup G} (hE9 : Nat.card E = 9) (t : G)
    (ht3 : t ^ 3 = 1) : ∃ f ∈ E, f ∉ Subgroup.zpowers t := by
  by_contra hc
  push Not at hc
  have h1 := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers t from hc)
  rw [hE9, Nat.card_zpowers] at h1
  have h2 : orderOf t ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ht3)
  omega

theorem eq_bot_of_forbidden {R W E : Subgroup G} (hRcard : Nat.card R ∣ 12096)
    (hWR : W ≤ R) (hER : E ≤ R)
    (hF3 : ∀ e ∈ R, ∀ y ∈ R, e ^ 3 = 1 → e ≠ 1 → y ^ 7 = 1 → y ≠ 1 → e * y ≠ y * e)
    (hF2 : ∀ e ∈ R, ∀ t ∈ R, ∀ t' ∈ R, e ^ 3 = 1 → e ≠ 1 → t ^ 2 = 1 → t ≠ 1 → t' ^ 2 = 1 →
      t' ≠ 1 → t ≠ t' → t * e = e * t → t' * e = e * t' → t * t' = t' * t → False)
    (hF1 : ∀ e ∈ R, ∀ u ∈ R, ∀ t ∈ R, e ^ 3 = 1 → e ≠ 1 → u ^ 3 = 1 → u ≠ 1 → u ≠ e →
      u ≠ e * e → t ^ 2 = 1 → t ≠ 1 → t * e = e * t → t * u = u * t → u * e = e * u → False)
    (hW : ¬ 3 ∣ Nat.card W) (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEW : E ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ := by
  by_contra hWne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨e, heE, he1, hDne⟩ :
      ∃ e ∈ E, e ≠ 1 ∧ W ⊓ Subgroup.centralizer ({e} : Set G) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hWne
    refine le_bot_iff.mp (CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_sub_le
      (p := 3) (k := 1) Nat.prime_three hE (by rw [hE9]; norm_num) hEW
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW) (fun H hHE hH => ?_))
    obtain ⟨e, heH, he1, rfl⟩ := CFSG.RankThree.PartTwo.Sec5.exists_eq_zpowers_of_card_eq_prime
      Nat.prime_three (by rw [hH]; norm_num)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact le_bot_iff.mpr (hcon e (hHE heH) he1)
  set D := W ⊓ Subgroup.centralizer ({e} : Set G) with hD
  have he3 : e ^ 3 = 1 := hE.2 e heE
  have heR : e ∈ R := hER heE
  have hDW : D ≤ W := inf_le_left
  have hDC : ∀ d ∈ D, e * d = d * e := fun d hd =>
    (Subgroup.mem_centralizer_iff.mp hd.2) e rfl
  have hDN : ∀ u ∈ E, ∀ d ∈ D, u * d * u⁻¹ ∈ D := by
    intro u hu d hd
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hEW hu) d).mp hd.1, ?_⟩
    show u * d * u⁻¹ ∈ Subgroup.centralizer ({e} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have hc : Commute e u := hEcomm e heE u hu
    have hc' : Commute e u⁻¹ := hc.inv_right
    calc e * (u * d * u⁻¹) = (e * u) * d * u⁻¹ := by simp only [mul_assoc]
      _ = (u * e) * d * u⁻¹ := by rw [hc.eq]
      _ = u * (e * d) * u⁻¹ := by simp only [mul_assoc]
      _ = u * (d * e) * u⁻¹ := by rw [hDC d hd]
      _ = u * d * (e * u⁻¹) := by simp only [mul_assoc]
      _ = u * d * (u⁻¹ * e) := by rw [hc'.eq]
      _ = u * d * u⁻¹ * e := by simp only [mul_assoc]
  have hDcard : Nat.card D ∣ 12096 := (Subgroup.card_dvd_of_le (hDW.trans hWR)).trans hRcard
  have hD3 : ¬ 3 ∣ Nat.card D := fun h => hW (h.trans (Subgroup.card_dvd_of_le hDW))
  by_cases h7 : 7 ∣ Nat.card D
  ·
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 h7
    have hy7 : (y : G) ^ 7 = 1 := by
      have := pow_orderOf_eq_one y
      rw [hy] at this
      exact congrArg Subtype.val this
    have hy1 : (y : G) ≠ 1 := by
      intro h1
      have : y = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hy
      omega
    exact hF3 e heR y (hWR (hDW y.2)) he3 he1 hy7 hy1 (hDC y y.2) 
  ·
    obtain ⟨n, hn⟩ : ∃ n, Nat.card D = 2 ^ n := by
      have hc3 : Nat.Coprime (Nat.card D) 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3).symm
      have hc7 : Nat.Coprime (Nat.card D) 7 :=
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7).symm
      have hdvd : Nat.card D ∣ 2 ^ 6 * (3 ^ 3 * 7) := by
        have : (12096 : ℕ) = 2 ^ 6 * (3 ^ 3 * 7) := by norm_num
        rwa [← this]
      have hcop : Nat.Coprime (Nat.card D) (3 ^ 3 * 7) := (hc3.pow_right 3).mul_right hc7
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hcop.dvd_of_dvd_mul_right hdvd)
      exact ⟨i, hi⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hD2 : IsPGroup 2 D := IsPGroup.of_card hn
    have hDnt : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
    have hZnt : Nontrivial (Subgroup.center D) := hD2.center_nontrivial
    have hZ2 : IsPGroup 2 (Subgroup.center D) := hD2.to_subgroup _
    have hZdvd : 2 ∣ Nat.card (Subgroup.center D) := by
      rcases hZ2.card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card.ne')
      · exact h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hZdvd
    obtain ⟨t, htD, ht2, ht1, htc⟩ :
        ∃ t : G, t ∈ D ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧ ∀ d ∈ D, t * d = d * t := by
      refine ⟨(((x : Subgroup.center D) : D) : G), ((x : Subgroup.center D) : D).2, ?_, ?_, ?_⟩
      · have := pow_orderOf_eq_one x
        rw [hx] at this
        exact congrArg (fun z : Subgroup.center D => (((z : Subgroup.center D) : D) : G)) this
      · intro h1
        have : x = 1 := Subtype.ext (Subtype.ext h1)
        rw [this, orderOf_one] at hx
        omega
      · intro d hd
        have := Subgroup.mem_center_iff.mp x.2 ⟨d, hd⟩
        exact (congrArg Subtype.val this).symm
    obtain ⟨u, huE, huz⟩ := exists_mem_notMem_zpowers_of_card_nine hE9 e he3
    have hu3 : u ^ 3 = 1 := hE.2 u huE
    have hu1 : u ≠ 1 := fun h => huz (h ▸ Subgroup.one_mem _)
    have hue : u ≠ e := fun h => huz (h ▸ Subgroup.mem_zpowers e)
    have hue2 : u ≠ e * e := fun h =>
      huz (h ▸ Subgroup.mul_mem _ (Subgroup.mem_zpowers e) (Subgroup.mem_zpowers e))
    have hcomm_ue : u * e = e * u := hEcomm u huE e heE
    have ht'D : u * t * u⁻¹ ∈ D := hDN u huE t htD
    have ht'2 : (u * t * u⁻¹) ^ 2 = 1 := by
      rw [conj_pow, ht2]
      group
    have ht'1 : u * t * u⁻¹ ≠ 1 := by
      intro h
      apply ht1
      calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
        _ = 1 := by rw [h]; group
    have htcc : ∀ d ∈ D, (u * t * u⁻¹) * d = d * (u * t * u⁻¹) := by
      intro d hd
      have hd' : u⁻¹ * d * u ∈ D := by
        have := hDN u⁻¹ (E.inv_mem huE) d hd
        simpa using this
      have h2 := htc (u⁻¹ * d * u) hd'
      calc u * t * u⁻¹ * d = u * (t * (u⁻¹ * d * u)) * u⁻¹ := by group
        _ = u * ((u⁻¹ * d * u) * t) * u⁻¹ := by rw [h2]
        _ = d * (u * t * u⁻¹) := by group
    by_cases htt : u * t * u⁻¹ = t
    ·
      have htu : t * u = u * t := by
        calc t * u = (u * t * u⁻¹) * u := by rw [htt]
          _ = u * t := by group
      exact hF1 e heR u (hER huE) t (hWR (hDW htD)) he3 he1 hu3 hu1 hue hue2 ht2 ht1
        (hDC t htD).symm htu hcomm_ue
    · exact hF2 e heR t (hWR (hDW htD)) (u * t * u⁻¹) (hWR (hDW ht'D)) he3 he1 ht2 ht1 ht'2 ht'1
        (Ne.symm htt) (hDC t htD).symm (hDC _ ht'D).symm (htc _ ht'D)

end CFSG.RankThree.PartTwo.Sec4.Item434G28
