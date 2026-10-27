module

public import CFSG.Quasithin.EmptyFaithful.SBc15F5Def
public import CFSG.Quasithin.EmptyFaithful.SBc15F5Dec

public section

namespace CFSG.Quasithin

open Equiv

namespace SBc15

namespace AltFive

theorem conj_klein {x : Fin 5} {g h : Perm (Fin 5)} (hg : Perm.sign g = 1) (hgx : g x = x)
    (hh : Perm.sign h = 1 ∧ h x = x ∧ h * h = 1) :
    Perm.sign (g * h * g⁻¹) = 1 ∧ (g * h * g⁻¹) x = x ∧
      (g * h * g⁻¹) * (g * h * g⁻¹) = 1 := by
  obtain ⟨hs, hx, hsq⟩ := hh
  have hginv : g⁻¹ x = x := by rw [Perm.inv_eq_iff_eq]; exact hgx.symm
  refine ⟨by simp [hg, hs], by simp [Perm.mul_apply, hginv, hx, hgx], ?_⟩
  calc (g * h * g⁻¹) * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
    _ = 1 := by rw [hsq]; group

theorem fixes_of_normalizes {x : Fin 5} {g : Perm (Fin 5)}
    (h : ∀ h : Perm (Fin 5), Perm.sign h = 1 → h x = x → h * h = 1 → (g * h * g⁻¹) x = x) :
    g x = x := by
  by_contra hne
  have hy : g⁻¹ x ≠ x := fun heq => hne (by rw [Perm.inv_eq_iff_eq] at heq; exact heq.symm)
  obtain ⟨v, hvs, hvx, hvsq, hvy⟩ := dec_unique_fixed x (g⁻¹ x) hy
  have h1 := h v hvs hvx hvsq
  rw [Perm.mul_apply, Perm.mul_apply] at h1
  exact hvy (Perm.eq_inv_iff_eq.mpr h1)

theorem natCard_eq_card_filter (H : Subgroup (Perm (Fin 5))) [DecidablePred (· ∈ H)] :
    Nat.card H = (Finset.univ.filter (· ∈ H)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem exists_fixed_point {V : Subgroup (Perm (Fin 5))} (hV : Nat.card V = 4) :
    ∃ x : Fin 5, ∀ g ∈ V, g x = x := by
  have h2 : IsPGroup 2 V := IsPGroup.of_card_dvd_pow (n := 2) (by rw [hV]; norm_num)
  have h := h2.card_modEq_card_fixedPoints (Fin 5)
  by_contra hcon
  push Not at hcon
  have hempty : MulAction.fixedPoints V (Fin 5) = ∅ := by
    ext y
    simp only [MulAction.mem_fixedPoints, Set.mem_empty_iff_false, iff_false]
    intro hy
    obtain ⟨g, hg, hgy⟩ := hcon y
    exact hgy (hy ⟨g, hg⟩)
  rw [hempty] at h
  simp at h
  exact absurd h (by decide)

theorem mem_klein_iff {V : Subgroup (Perm (Fin 5))} (hVA : V ≤ alternatingGroup (Fin 5))
    (hV : Nat.card V = 4) {x : Fin 5} (hx : ∀ g ∈ V, g x = x) (g : Perm (Fin 5)) :
    g ∈ V ↔ (Perm.sign g = 1 ∧ g x = x ∧ g * g = 1) := by
  classical
  have hfwd : ∀ g ∈ V, Perm.sign g = 1 ∧ g x = x ∧ g * g = 1 := by
    intro g hg
    have hs := Equiv.Perm.mem_alternatingGroup.mp (hVA hg)
    refine ⟨hs, hx g hg, dec_sq g hs ?_⟩
    have h4 : orderOf g ∣ 4 := by
      have := Subgroup.orderOf_dvd_natCard V hg
      rwa [hV] at this
    exact orderOf_dvd_iff_pow_eq_one.mp h4
  refine ⟨hfwd g, fun hg => ?_⟩
  set S : Finset (Perm (Fin 5)) :=
    Finset.univ.filter (fun g => Perm.sign g = 1 ∧ g x = x ∧ g * g = 1) with hS
  set Vf : Finset (Perm (Fin 5)) := Finset.univ.filter (· ∈ V) with hVf
  have hVc : Vf.card = 4 := (natCard_eq_card_filter V).symm.trans hV
  have hsub : Vf ⊆ S := by
    intro y hy
    simp only [hVf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfwd y hy
  have heq : Vf = S := Finset.eq_of_subset_of_card_le hsub (by rw [dec_card_klein x, hVc])
  have hgS : g ∈ S := by simp [hS, hg]
  rw [← heq] at hgS
  simpa [hVf] using hgS

def stabAlt (x : Fin 5) : Subgroup (Perm (Fin 5)) :=
  alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) x

theorem mem_stab_iff (x : Fin 5) (g : Perm (Fin 5)) :
    g ∈ stabAlt x ↔ Perm.sign g = 1 ∧ g x = x := by
  simp [stabAlt, Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup, MulAction.mem_stabilizer_iff]

theorem card_stabilizer (x : Fin 5) : Nat.card (stabAlt x) = 12 := by
  classical
  rw [natCard_eq_card_filter]
  have : (Finset.univ.filter (· ∈ stabAlt x)) =
      Finset.univ.filter (fun g : Perm (Fin 5) => Perm.sign g = 1 ∧ g x = x) :=
    Finset.filter_congr (fun g _ => mem_stab_iff x g)
  rw [this]
  exact dec_card_stab x

theorem eq_stabilizer {x : Fin 5} {V Y : Subgroup (Perm (Fin 5))}
    (hVx : ∀ g, g ∈ V ↔ (Perm.sign g = 1 ∧ g x = x ∧ g * g = 1))
    (hYA : Y ≤ alternatingGroup (Fin 5)) (hVY : ∀ v ∈ V, ∀ y ∈ Y, v * y * v⁻¹ ∈ Y)
    (hO : oTwoUpper Y = Y) (h3 : 3 ∣ Nat.card Y) (h12 : Nat.card Y ∣ 12) :
    Y = stabAlt x := by
  have hBmem : ∀ g, g ∈ stabAlt x ↔ Perm.sign g = 1 ∧ g x = x := mem_stab_iff x
  have hodd : ∀ y ∈ Y, Odd (orderOf y) → y ^ 3 = 1 := by
    intro y hy hyo
    have h1 : orderOf y ∣ 12 := (Subgroup.orderOf_dvd_natCard Y hy).trans h12
    have hcop : Nat.Coprime (orderOf y) 4 := by
      simpa using Nat.Coprime.pow_right 2 hyo.coprime_two_right
    have h2 : orderOf y ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using h1)
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  have hfix : ∀ y ∈ Y, y ^ 3 = 1 → y x = x := by
    intro y hy hy3
    by_contra hne
    obtain ⟨v, hvs, hvx, hvsq, h5, h51⟩ :=
      dec_five x y (Equiv.Perm.mem_alternatingGroup.mp (hYA hy)) hy3 hne
    have hvV : v ∈ V := (hVx v).mpr ⟨hvs, hvx, hvsq⟩
    have hz : y * (v * y * v⁻¹) ∈ Y := Y.mul_mem hy (hVY v hvV y hy)
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hord : orderOf (y * (v * y * v⁻¹)) = 5 := orderOf_eq_prime h5 h51
    have h5Y : 5 ∣ Nat.card Y := by
      have := Subgroup.orderOf_dvd_natCard Y hz
      rwa [hord] at this
    have := h5Y.trans h12
    omega
  have hYB : Y ≤ stabAlt x := by
    have h : oTwoUpper Y ≤ stabAlt x := by
      refine (Subgroup.closure_le (stabAlt x)).mpr ?_
      rintro y ⟨hy, hyo⟩
      exact (hBmem y).mpr
        ⟨Equiv.Perm.mem_alternatingGroup.mp (hYA hy), hfix y hy (hodd y hy hyo)⟩
    rwa [hO] at h
  refine le_antisymm hYB fun g hg => ?_
  obtain ⟨hgs, hgx⟩ := (hBmem g).mp hg
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have htY : (t' : Perm (Fin 5)) ∈ Y := t'.2
  have hto : orderOf (t' : Perm (Fin 5)) = 3 := by rw [Subgroup.orderOf_coe]; exact ht'
  have ht3 : (t' : Perm (Fin 5)) ^ 3 = 1 := by rw [← hto]; exact pow_orderOf_eq_one _
  have ht1 : (t' : Perm (Fin 5)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hto
    omega
  have hts := Equiv.Perm.mem_alternatingGroup.mp (hYA htY)
  have htx : (t' : Perm (Fin 5)) x = x := ((hBmem _).mp (hYB htY)).2
  have hVY' : ∀ w ∈ V, w ∈ Y := by
    intro w hw
    obtain ⟨hws, hwx, hwsq⟩ := (hVx w).mp hw
    obtain ⟨v, hvs, hvx, hvsq, hv⟩ := dec_comm x _ hts htx ht3 ht1 w hws hwx hwsq
    have hvV : v ∈ V := (hVx v).mpr ⟨hvs, hvx, hvsq⟩
    rw [← hv]
    exact Y.mul_mem (hVY v hvV _ htY) (Y.inv_mem htY)
  obtain ⟨v, hvs, hvx, hvsq, hv⟩ := dec_gen x _ hts htx ht3 ht1 g hgs hgx
  have hvY : v ∈ Y := hVY' v ((hVx v).mpr ⟨hvs, hvx, hvsq⟩)
  rcases hv with h | h | h <;> rw [h]
  · exact hvY
  · exact Y.mul_mem hvY htY
  · exact Y.mul_mem hvY (Y.pow_mem htY 2)

theorem comm_surj {x : Fin 5} {V : Subgroup (Perm (Fin 5))}
    (hVx : ∀ g, g ∈ V ↔ (Perm.sign g = 1 ∧ g x = x ∧ g * g = 1)) {a : Perm (Fin 5)}
    (ha : a ∈ stabAlt x) (hao : orderOf a = 3) : ∀ w ∈ V, ∃ v ∈ V, v * a * v⁻¹ * a⁻¹ = w := by
  obtain ⟨has, hax⟩ := (mem_stab_iff x a).mp ha
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hao
    omega
  intro w hw
  obtain ⟨hws, hwx, hwsq⟩ := (hVx w).mp hw
  obtain ⟨v, hvs, hvx, hvsq, hv⟩ := dec_comm x a has hax ha3 ha1 w hws hwx hwsq
  exact ⟨v, (hVx v).mpr ⟨hvs, hvx, hvsq⟩, hv⟩

theorem a5Facts : A5Facts (Perm (Fin 5)) (alternatingGroup (Fin 5)) where
  card_A := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  exists_normalizer := fun V hVA hV => by
    obtain ⟨x, hx⟩ := exists_fixed_point hV
    have hVx := mem_klein_iff hVA hV hx
    refine ⟨stabAlt x, card_stabilizer x, ?_, ?_, ?_, ?_⟩
    · intro g hg v hv
      obtain ⟨hgs, hgx⟩ := (mem_stab_iff x g).mp hg
      exact (hVx _).mpr (conj_klein hgs hgx ((hVx v).mp hv))
    · intro g hgA hn
      have hgs := Equiv.Perm.mem_alternatingGroup.mp hgA
      refine (mem_stab_iff x g).mpr ⟨hgs, fixes_of_normalizes ?_⟩
      intro h hs hfix hsq
      exact ((hVx _).mp (hn h ((hVx h).mpr ⟨hs, hfix, hsq⟩))).2.1
    · intro Y hYA hVY hO h3 h12
      exact eq_stabilizer hVx hYA hVY hO h3 h12
    · intro a ha hao
      exact comm_surj hVx ha hao

end AltFive

end SBc15

end CFSG.Quasithin
