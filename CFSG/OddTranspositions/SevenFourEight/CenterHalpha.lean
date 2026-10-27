module

public import CFSG.OddTranspositions.SixNineUnconditional

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem center_Halpha_le_of_sevenSix (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hα : hC.alpha = {hC.d}) {p : ℕ} (hpp : p.Prime)
    (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (hμ : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).ncard = p)
    (hR : ∀ w ∈ D, ¬ Commute w hC.d → ∀ r ∈ commSet D hC.d ∩ commSet D w,
      ∀ r' ∈ commSet D hC.d ∩ commSet D w, r ≠ r' → ¬ Commute r r')
    (hZ2 : ∀ z ∈ Subgroup.center ↥(Halpha D hC.alpha), (z : G) * z = 1) :
    ∀ z ∈ Subgroup.center ↥(Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d := by
  classical
  intro z hz
  have hD := hC.setup.oddT
  have hN := hC.setup.normal
  have hu : hC.d ∈ D := hC.hd
  have hu2 : hC.d * hC.d = 1 := hD.mul_self_eq_one hu
  have hui : hC.d⁻¹ = hC.d := hD.inv_eq hu
  set t : G := (z : G) with htdef
  have ht2 : t * t = 1 := hZ2 z hz
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hHu : ∀ h ∈ Halpha D hC.alpha, Commute h hC.d := by
    intro h hh
    refine Subgroup.closure_induction (p := fun y _ => Commute y hC.d) ?_ ?_ ?_ ?_ hh
    · intro y hy
      exact (hC.DalphaStar_subset_commute hy).2
    · exact Commute.one_left _
    · intro y w _ _ hy hw
      exact hy.mul_left hw
    · intro y _ hy
      exact hy.inv_left
  have htu : Commute t hC.d := hHu t z.2
  have htH : ∀ h ∈ Halpha D hC.alpha, Commute t h := by
    intro h hh
    have e := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨h, hh⟩)
    exact e.symm
  have hDuH : ∀ x ∈ commSet D hC.d, x ∈ Halpha D hC.alpha := by
    rintro x ⟨hxD, hxu, hxne⟩
    refine Subgroup.subset_closure ?_
    rcases (Set.ext_iff.mp hC.eq_alpha_union x).mp hxD with (h | h) | h
    · rw [hα] at h
      exact (hxne h).elim
    · exact h
    · exact ((mem_Gamma_iff.mp (show x ∈ Gamma hC from h)).2.1 hxu).elim
  have hAmem : ∀ w ∈ D, ¬ Commute w hC.d → w ∈ AalphaStar D hC.alpha := by
    intro w hw hwu
    rw [hC.AalphaStar_eq_diff_alpha, hα]
    refine ⟨⟨hw, hwu⟩, fun h => hwu ?_⟩
    rw [Set.mem_singleton_iff.mp h]
  have hZG : ∀ g : G, (∀ x ∈ D, Commute g x) → g = 1 := by
    intro g hg
    have hle : Subgroup.closure D ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hg x hx).symm.eq
    have hcent : g ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (by rw [hC.setup.gen]; trivial))
    have hZ : Subgroup.center G = ⊥ :=
      hrad _ inferInstance (Group.isSolvable_of_comm fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm)
    rw [hZ, Subgroup.mem_bot] at hcent
    exact hcent
  have htC : ∀ x ∈ D, Commute x hC.d → Commute t x := by
    intro x hx hxu
    by_cases hxe : x = hC.d
    · rw [hxe]
      exact htu
    · exact htH x (hDuH x ⟨hx, hxu, hxe⟩)
  have hKt : ∀ k ∈ Subgroup.closure ((D : Set G) ∩ Subgroup.centralizer ({hC.d} : Set G)),
      Commute k t := by
    intro k hk
    refine Subgroup.closure_induction (p := fun y _ => Commute y t) ?_ ?_ ?_ ?_ hk
    · rintro y ⟨hyD, hyc⟩
      exact (htC y hyD (Subgroup.mem_centralizer_singleton_iff.mp hyc)).symm
    · exact Commute.one_left _
    · intro y w _ _ hy hw
      exact hy.mul_left hw
    · intro y _ hy
      exact hy.inv_left
  have hμ' : ∀ r ∈ D, ∀ r' ∈ D, ¬ Commute r r' → (commSet D r ∩ commSet D r').ncard = p := by
    intro r hr r' hr' hrr'
    obtain ⟨d₀, hd₀⟩ := hC.setup.isClass
    have h1 : IsConj d₀ hC.d := (Set.ext_iff.mp hd₀ hC.d).mp hu
    have h2 : IsConj d₀ r := (Set.ext_iff.mp hd₀ r).mp hr
    obtain ⟨g, hg⟩ := isConj_iff.mp (h1.symm.trans h2)
    have hr''D : g⁻¹ * r' * g ∈ D := by simpa using hN g⁻¹ r' hr'
    have hr''u : ¬ Commute (g⁻¹ * r' * g) hC.d := by
      intro hc
      apply hrr'
      have := (Commute.conj_iff g).mpr hc.symm
      rwa [hg, show g * (g⁻¹ * r' * g) * g⁻¹ = r' by group] at this
    have hr'eq : r' = g * (g⁻¹ * r' * g) * g⁻¹ := by group
    rw [← hg, hr'eq, commSet_conj hN, commSet_conj hN, ← Set.image_inter
      (fun a b h => by simpa using h), ncard_cimg]
    exact hμ _ hr''D hr''u
  have hkey : ∀ w ∈ D, ¬ Commute w hC.d → Commute t w ∨ Commute (t * hC.d) w := by
    intro w hw hwu
    have hw2 : w * w = 1 := hD.mul_self_eq_one hw
    set ρ := hC.d * w with hρdef
    have hρ : orderOf ρ = p := hp _ hu _ hw (fun h => hwu h.symm)
    have hpodd : Odd p := hρ ▸ hD.odd_of_not_commute hu hw (fun h => hwu h.symm)
    have hp2 : 2 ≤ p := hpp.two_le
    obtain ⟨r, r', hr, hr', hrr'⟩ :=
      (Set.one_lt_ncard_iff (Set.toFinite _)).mp (by rw [hμ w hw hwu]; omega)
    have hnc := hR w hw hwu r hr r' hr' hrr'
    obtain ⟨⟨hrD, hru, hrne⟩, ⟨-, hrw, -⟩⟩ := hr
    obtain ⟨⟨hr'D, hr'u, hr'ne⟩, ⟨-, hr'w, -⟩⟩ := hr'
    have hinvρ : hC.d * ρ * hC.d⁻¹ = ρ⁻¹ := by
      rw [hρdef, mul_inv_rev, hui, hD.inv_eq hw, ← mul_assoc, hu2, one_mul]
    have hrefD : ∀ i : ℕ, ρ ^ i * hC.d ∈ D := by
      intro i
      obtain ⟨j, hj⟩ := OddTransp.exists_zpow_conj_eq hu2 hw2 (hρ ▸ hpodd) (i : ℤ)
      rw [zpow_natCast] at hj
      rw [← hj]
      exact hN _ _ hu
    have hρr : ∀ x : G, Commute x hC.d → Commute x w → ∀ i : ℕ, Commute x (ρ ^ i * hC.d) :=
      fun x hxu hxw i => ((hxu.mul_right hxw).pow_right i).mul_right hxu
    have hrefne : ∀ i < p, ∀ x : G, Commute x hC.d → x ≠ hC.d → ρ ^ i * hC.d ≠ x := by
      intro i hi x hxu hxne he
      apply hxne
      rw [← he] at hxu
      have h1 : ρ ^ i = (ρ ^ i)⁻¹ := by
        have := hxu.eq
        have h2 : hC.d * ρ ^ i * hC.d⁻¹ = (ρ ^ i)⁻¹ := by rw [← conj_pow, hinvρ, inv_pow]
        rw [← h2, hui]
        calc ρ ^ i = ρ ^ i * hC.d * hC.d := by rw [mul_assoc, hu2, mul_one]
          _ = hC.d * (ρ ^ i * hC.d) := by rw [this]
          _ = hC.d * ρ ^ i * hC.d := by rw [mul_assoc]
      have h3 : ρ ^ (2 * i) = 1 := by
        rw [two_mul, pow_add]
        nth_rewrite 2 [h1]
        exact mul_inv_cancel _
      have h4 : p ∣ 2 * i := hρ ▸ orderOf_dvd_of_pow_eq_one h3
      rcases (Nat.Prime.dvd_mul hpp).mp h4 with h5 | h5
      · have := Nat.le_of_dvd (by norm_num) h5
        obtain ⟨s, hs⟩ := hpodd
        omega
      · have hi0 : i = 0 := by
          rcases Nat.eq_zero_or_pos i with h | h
          · exact h
          · exact absurd (Nat.le_of_dvd h h5) (by omega)
        rw [← he, hi0, pow_zero, one_mul]
    set L := commSet D r ∩ commSet D r' with hLdef
    set Ref : Set G := (fun i : ℕ => ρ ^ i * hC.d) '' (↑(Finset.range p) : Set ℕ) with hRefdef
    have hRefL : Ref ⊆ L := by
      rintro x ⟨i, hi, rfl⟩
      have hi' : i < p := Finset.mem_range.mp hi
      exact ⟨⟨hrefD i, (hρr r hru hrw i).symm, hrefne i hi' r hru hrne⟩,
        ⟨hrefD i, (hρr r' hr'u hr'w i).symm, hrefne i hi' r' hr'u hr'ne⟩⟩
    have hRefcard : Ref.ncard = p := by
      rw [hRefdef, Set.InjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]
      intro i hi j hj hij
      have hij' : ρ ^ i = ρ ^ j := mul_right_cancel hij
      have hmod := (pow_eq_pow_iff_modEq).mp hij'
      rw [hρ] at hmod
      exact Nat.ModEq.eq_of_lt_of_lt hmod (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
    have hRefeq : Ref = L :=
      Set.eq_of_subset_of_ncard_le hRefL (by rw [hRefcard, hμ' r hrD r' hr'D hnc]) (Set.toFinite _)
    have htr : Commute t r := htC r hrD hru
    have htr' : Commute t r' := htC r' hr'D hr'u
    have htwL : t * w * t⁻¹ ∈ L := by
      have hmem : ∀ s ∈ D, Commute t s → Commute w s → w ≠ s →
          t * w * t⁻¹ ∈ commSet D s := by
        intro s hs hts hws hwne
        refine ⟨hN t w hw, ?_, ?_⟩
        · have := (Commute.conj_iff t).mpr hws
          rwa [show t * s * t⁻¹ = s by rw [hts.eq, mul_inv_cancel_right]] at this
        · intro he
          apply hwne
          calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
            _ = t⁻¹ * s * t := by rw [he]
            _ = s := by rw [mul_assoc, ← hts.eq, inv_mul_cancel_left]
      refine ⟨hmem r hrD htr hrw.symm ?_, hmem r' hr'D htr' hr'w.symm ?_⟩
      · intro he
        rw [he] at hwu
        exact hwu hru
      · intro he
        rw [he] at hwu
        exact hwu hr'u
    rw [← hRefeq] at htwL
    obtain ⟨a, ha, hta⟩ := htwL
    have ha' : a < p := Finset.mem_range.mp ha
    have hta' : t * w * t⁻¹ = ρ ^ a * hC.d := hta.symm
    have htρ : t * ρ * t⁻¹ = (ρ ^ a)⁻¹ := by
      calc t * ρ * t⁻¹ = (t * hC.d * t⁻¹) * (t * w * t⁻¹) := by rw [hρdef]; group
        _ = hC.d * (ρ ^ a * hC.d) := by rw [hta', htu.eq, mul_inv_cancel_right]
        _ = hC.d * ρ ^ a * hC.d⁻¹ := by rw [hui, mul_assoc]
        _ = (ρ ^ a)⁻¹ := by rw [← conj_pow, hinvρ, inv_pow]
    have hsq : ρ ^ (a * a) = ρ ^ 1 := by
      have h1 : t * (ρ ^ a)⁻¹ * t⁻¹ = (ρ ^ (a * a))⁻¹⁻¹ := by
        rw [← conj_inv, ← conj_pow, htρ, inv_pow, ← pow_mul]
      have h2 : t * (t * ρ * t⁻¹) * t⁻¹ = ρ := by
        rw [show t * (t * ρ * t⁻¹) * t⁻¹ = (t * t) * ρ * (t * t)⁻¹ by group, ht2]
        group
      rw [htρ, h1, inv_inv] at h2
      rw [h2, pow_one]
    have hmod := (pow_eq_pow_iff_modEq).mp hsq
    rw [hρ] at hmod
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h] at hmod
        have := Nat.ModEq.eq_of_lt_of_lt hmod (by omega) (by omega)
        omega
      · exact h
    have hdvd : p ∣ (a - 1) * (a + 1) := by
      have h := (Nat.modEq_iff_dvd' (by nlinarith)).mp hmod.symm
      have e : a * a - 1 = (a - 1) * (a + 1) := by
        obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
      rwa [e] at h
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h | h
    ·
      have ha1' : a = 1 := by
        have : a - 1 < p := by omega
        rcases Nat.eq_zero_or_pos (a - 1) with h0 | h0
        · omega
        · exact absurd (Nat.le_of_dvd h0 h) (by omega)
      right
      rw [ha1', pow_one] at htρ
      have hc1 : Commute (t * hC.d) ρ := by
        show t * hC.d * ρ = ρ * (t * hC.d)
        have : t * hC.d * ρ * (t * hC.d)⁻¹ = ρ := by
          calc t * hC.d * ρ * (t * hC.d)⁻¹ = t * (hC.d * ρ * hC.d⁻¹) * t⁻¹ := by group
            _ = ρ := by rw [hinvρ, ← conj_inv, htρ, inv_inv]
        calc t * hC.d * ρ = t * hC.d * ρ * (t * hC.d)⁻¹ * (t * hC.d) := by group
          _ = ρ * (t * hC.d) := by rw [this]
      have hc2 : Commute (t * hC.d) hC.d := htu.mul_left (Commute.refl _)
      have hwe : w = hC.d * ρ := by rw [hρdef, ← mul_assoc, hu2, one_mul]
      rw [hwe]
      exact hc2.mul_right hc1
    ·
      have hap : a + 1 = p := by
        have := Nat.le_of_dvd (by omega) h
        omega
      left
      have hρa : (ρ ^ a)⁻¹ = ρ := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ, hap, ← hρ, pow_orderOf_eq_one]
      rw [hρa] at htρ
      have hc1 : Commute t ρ := by
        show t * ρ = ρ * t
        calc t * ρ = t * ρ * t⁻¹ * t := by group
          _ = ρ * t := by rw [htρ]
      have hwe : w = hC.d * ρ := by rw [hρdef, ← mul_assoc, hu2, one_mul]
      rw [hwe]
      exact htu.mul_right hc1
  by_cases hS : ∃ w₀ ∈ D, ¬ Commute w₀ hC.d ∧ Commute t w₀
  · left
    obtain ⟨w₀, hw₀D, hw₀u, htw₀⟩ := hS
    apply hZG
    intro x hx
    by_cases hxu : Commute x hC.d
    · exact htC x hx hxu
    · obtain ⟨k, hk, hkx⟩ := cenGen_transitive_AalphaStar_unconditional hC hsecond w₀
        (hAmem w₀ hw₀D hw₀u) x (hAmem x hx hxu)
      rw [← hkx]
      have hkt := hKt k hk
      have := (Commute.conj_iff k).mpr htw₀
      rwa [show k * t * k⁻¹ = t by rw [hkt.eq, mul_inv_cancel_right]] at this
  · right
    push Not at hS
    have htu1 : t * hC.d = 1 := by
      apply hZG
      intro x hx
      by_cases hxu : Commute x hC.d
      · exact (htC x hx hxu).mul_left hxu.symm
      · exact (hkey x hx hxu).resolve_left (hS x hx hxu)
    calc t = t * hC.d * hC.d⁻¹ := by group
      _ = hC.d := by rw [htu1, one_mul, hui]

end CFSG.OddTranspositions

end
