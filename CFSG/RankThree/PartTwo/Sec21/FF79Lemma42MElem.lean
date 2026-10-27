module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem m42_closure_pair_zpow {e f : G} (hc : Commute e f) {x : G}
    (hx : x ∈ Subgroup.closure ({e, f} : Set G)) : ∃ i j : ℤ, x = e ^ i * f ^ j := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    refine ⟨i + k, j + l, ?_⟩
    have h := (hc.zpow_zpow k j).symm.eq
    calc e ^ i * f ^ j * (e ^ k * f ^ l) = e ^ i * (f ^ j * e ^ k) * f ^ l := by group
      _ = e ^ i * (e ^ k * f ^ j) * f ^ l := by rw [← h]
      _ = e ^ (i + k) * f ^ (j + l) := by rw [zpow_add, zpow_add]; group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, zpow_neg, zpow_neg]
    exact ((hc.zpow_zpow i j).inv_inv).eq.symm

variable [Finite G]

theorem m42_card_pair_le {e f : G} (he : orderOf e = 3) (hf : orderOf f = 3) (hc : Commute e f) :
    Nat.card (Subgroup.closure ({e, f} : Set G)) ≤ 9 := by
  let g : Fin 3 × Fin 3 → G := fun p => e ^ (p.1 : ℕ) * f ^ (p.2 : ℕ)
  have hred : ∀ (x : G) (n : ℕ), orderOf x = n → 0 < n → ∀ i : ℤ,
      ∃ k : Fin n, x ^ i = x ^ (k : ℕ) := by
    intro x n hx hn i
    have h := zpow_mod_orderOf x i
    rw [hx] at h
    refine ⟨⟨(i % n).toNat, ?_⟩, ?_⟩
    · have := Int.emod_lt_of_pos i (show (0 : ℤ) < n by exact_mod_cast hn)
      omega
    · rw [← h, ← zpow_natCast]
      congr 1
      exact (Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))).symm
  have hsub : ((Subgroup.closure ({e, f} : Set G) : Subgroup G) : Set G) ⊆ Set.range g := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := m42_closure_pair_zpow hc hx
    obtain ⟨a, ha⟩ := hred e 3 he (by norm_num) i
    obtain ⟨b, hb⟩ := hred f 3 hf (by norm_num) j
    exact ⟨(a, b), by simp [g, ha, hb]⟩
  have h1 : ((Subgroup.closure ({e, f} : Set G) : Subgroup G) : Set G).ncard ≤
      (Set.range g).ncard := Set.ncard_le_ncard hsub (Set.finite_range g)
  have h2 : (Set.range g).ncard ≤ 9 := by
    have := Set.ncard_image_le (f := g) (Set.finite_univ (α := Fin 3 × Fin 3))
    rw [← Set.image_univ]
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using this
  rw [← Nat.card_coe_set_eq] at h1
  simpa using h1.trans h2

theorem m42_card_pair {e f : G} (he : orderOf e = 3) (hf : orderOf f = 3) (hc : Commute e f)
    (hint : Subgroup.zpowers e ⊓ Subgroup.zpowers f = ⊥) :
    Nat.card (Subgroup.closure ({e, f} : Set G)) = 9 := by
  let g : Fin 3 × Fin 3 → G := fun p => e ^ (p.1 : ℕ) * f ^ (p.2 : ℕ)
  have hup := m42_card_pair_le he hf hc
  have hlow : 9 ≤ Nat.card (Subgroup.closure ({e, f} : Set G)) := by
    let ι : Fin 3 × Fin 3 → ↥(Subgroup.closure ({e, f} : Set G)) := fun p =>
      ⟨g p, Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)⟩
    have hinj : Function.Injective ι := by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      have h0 : e ^ (a : ℕ) * f ^ (b : ℕ) = e ^ (c : ℕ) * f ^ (d : ℕ) :=
        congrArg Subtype.val h
      have h1 : e ^ ((a : ℤ) - c) = f ^ ((d : ℤ) - b) := by
        have hc1 : f ^ (b : ℤ) * f ^ (-(d : ℤ)) = e ^ (-(a : ℤ)) * e ^ (c : ℤ) := by
          have : e ^ (a : ℤ) * f ^ (b : ℤ) = e ^ (c : ℤ) * f ^ (d : ℤ) := by
            simpa [zpow_natCast] using h0
          calc f ^ (b : ℤ) * f ^ (-(d : ℤ))
              = e ^ (-(a : ℤ)) * (e ^ (a : ℤ) * f ^ (b : ℤ)) * f ^ (-(d : ℤ)) := by group
            _ = e ^ (-(a : ℤ)) * (e ^ (c : ℤ) * f ^ (d : ℤ)) * f ^ (-(d : ℤ)) := by rw [this]
            _ = e ^ (-(a : ℤ)) * e ^ (c : ℤ) := by group
        have h2 : e ^ ((a : ℤ) - c) = (e ^ (-(a : ℤ)) * e ^ (c : ℤ))⁻¹ := by group
        rw [h2, ← hc1]
        group
      have hm1 : e ^ ((a : ℤ) - c) ∈ Subgroup.zpowers e ⊓ Subgroup.zpowers f :=
        ⟨⟨_, rfl⟩, ⟨_, h1.symm⟩⟩
      rw [hint, Subgroup.mem_bot] at hm1
      have hm2 : f ^ ((d : ℤ) - b) = 1 := by rw [← h1]; exact hm1
      have h3 := (orderOf_dvd_iff_zpow_eq_one.mpr hm1)
      have h4 := (orderOf_dvd_iff_zpow_eq_one.mpr hm2)
      rw [he] at h3
      rw [hf] at h4
      have h3' : (3 : ℤ) ∣ (a : ℤ) - c := by exact_mod_cast h3
      have h4' : (3 : ℤ) ∣ (d : ℤ) - b := by exact_mod_cast h4
      have ha := a.2
      have hb := b.2
      have hc2 := c.2
      have hd := d.2
      have e1 : (a : ℕ) = c := by omega
      have e2 : (b : ℕ) = d := by omega
      exact Prod.ext (Fin.ext e1) (Fin.ext e2)
    have := Nat.card_le_card_of_injective ι hinj
    simpa using this
  omega

theorem m42_cen_eq_of_mem_zpowers {x y : G} (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hxy : x ∈ Subgroup.zpowers y) : Cen x = Cen y := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_le]; exact hxy
  have hfin : Finite (Subgroup.zpowers y) := by
    have : 0 < orderOf y := by omega
    exact (Nat.card_pos_iff.mp (by rwa [Nat.card_zpowers])).2
  have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy])
  have hyx : y ∈ Subgroup.zpowers x := by rw [heq]; exact Subgroup.mem_zpowers y
  have key : ∀ {a b : G}, a ∈ Subgroup.zpowers b → Cen b ≤ Cen a := by
    intro a b hab z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hab
    exact m42_mem_cen (((show Commute b z from m42_cen_comm hz).zpow_left i).eq)
  exact le_antisymm (key hyx) (key hxy)

theorem m42_map_HCen {H : Subgroup G} {g : G} (hg : g ∈ H) (e : G) :
    (H ⊓ Cen e).map (MulAut.conj g).toMonoidHom = H ⊓ Cen (g * e * g⁻¹) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨m, ⟨hmH, hme⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hg hmH) (H.inv_mem hg), ?_⟩
    have hc : Commute e m := m42_cen_comm hme
    refine m42_mem_cen ?_
    have : Commute (g * e * g⁻¹) (g * m * g⁻¹) := by
      have := hc.map (MulAut.conj g)
      simpa using this
    exact this.eq
  · rintro ⟨hyH, hye⟩
    refine ⟨g⁻¹ * y * g, ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hyH) hg, ?_⟩, by simp [mul_assoc]⟩
    have hc : Commute (g * e * g⁻¹) y := m42_cen_comm hye
    refine m42_mem_cen ?_
    have := hc.map (MulAut.conj g⁻¹)
    simpa [mul_assoc] using this.eq

variable [Finite G]

end CFSG.RankThree.PartTwo.Sec21.FF79
