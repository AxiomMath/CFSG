module

public import CFSG.Quasithin.Vol2.Ch10SecC3E

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13 (fsuV Row711L3Wreath Concl701FF tensorPairModel)
open scoped Matrix IsMulCommutative

theorem card_mul_card_fixV_lt {A : Subgroup (MulAut WMod)} (hAN : A ≤ norm)
    (hA : IsElemAbelian2 A) (hne : A ≠ ⊥) : Nat.card A * Nat.card ↥(fixV A) < 2 ^ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hI : A ≤ img
  · exact card_mul_card_fixV_lt_of_le_img hAN hA hne hI
  obtain ⟨s, hsA, hsi⟩ := Set.not_subset.mp hI
  have hs1 : s ≠ 1 := fun h => hsi (h ▸ img.one_mem)
  have hs2 : s * s = 1 := by rw [← sq]; exact hA.2 s hsA
  obtain ⟨a, rfl⟩ := eq_rho_mul_tau (hAN hsA) hsi hs2
  have hB' : ∀ g : ↥SL32 × ↥SL32, rho g ∈ A → g.1 * a = a * g.2 := fun g hg =>
    eq_conj_of_commute (hA.1 _ hg _ hsA)
  set B := A ⊓ img with hBdef
  have hAB : Nat.card A ≤ 2 * Nat.card B := by
    classical
    let f : ↥A → Bool × ↥B := fun x =>
      if hx : (x : MulAut WMod) ∈ img then (false, ⟨x, x.2, hx⟩)
      else (true, ⟨x * (rho (a, a⁻¹) * tau), A.mul_mem x.2 hsA,
        mul_mem_img (hAN x.2) (hAN hsA) hx hsi⟩)
    have hf : Function.Injective f := by
      intro x y hxy
      simp only [f] at hxy
      split_ifs at hxy with hx hy hy
      · exact Subtype.ext (congrArg (Subtype.val : ↥B → MulAut WMod) (Prod.mk.inj hxy).2)
      · exact absurd (Prod.mk.inj hxy).1 (by decide)
      · exact absurd (Prod.mk.inj hxy).1 (by decide)
      · exact Subtype.ext (mul_right_cancel (congrArg Subtype.val (Prod.mk.inj hxy).2))
    calc Nat.card A ≤ Nat.card (Bool × ↥B) := Nat.card_le_card_of_injective f hf
      _ = 2 * Nat.card B := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  have hB4 : Nat.card B ≤ 4 := by
    set B' := B.comap rho with hB'def
    have hBB' : Nat.card B = Nat.card B' := by
      have hm := Subgroup.map_comap_eq_self (f := rho) (show B ≤ rho.range from inf_le_right)
      calc Nat.card B = Nat.card ((B.comap rho).map rho) := by rw [hm]
        _ = Nat.card B' := Subgroup.card_map_of_injective rho_injective
    have hc : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := fun x hx y hy =>
      rho_injective (by rw [map_mul, map_mul]; exact hA.1 _ hx.1 _ hy.1)
    have h2 : ∀ x ∈ B', x * x = 1 := fun x hx =>
      rho_injective (by rw [map_mul, map_one, ← sq]; exact hA.2 _ hx.1)
    set P := B'.map (MonoidHom.snd ↥SL32 ↥SL32) with hPdef
    have hP : Nat.card P ≤ 4 := card_le_four_of_elem
      (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact congrArg Prod.snd (hc x hx y hy))
      (by rintro _ ⟨x, hx, rfl⟩; exact congrArg Prod.snd (h2 x hx))
    rw [hBB']
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : ↥B' => (⟨x.1.2, x.1, x.2, rfl⟩ : ↥P)) ?_) hP
    intro x y hxy
    have hsnd : x.1.2 = y.1.2 := congrArg Subtype.val hxy
    have hfst : x.1.1 = y.1.1 := by
      have hx := hB' x.1 x.2.1
      have hy := hB' y.1 y.2.1
      rw [hsnd, ← hy] at hx
      exact mul_right_cancel hx
    exact Subtype.ext (Prod.ext hfst hsnd)
  by_cases hB : B = ⊥
  · have hA2 : Nat.card A ≤ 2 := by
      rw [hB, Subgroup.card_bot] at hAB
      omega
    calc Nat.card A * Nat.card ↥(fixV A) ≤ 2 * 64 :=
          Nat.mul_le_mul hA2 (card_fixV_le_of_mem hAN hA hsA hs1)
      _ < 2 ^ 9 := by norm_num
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB
  obtain ⟨g, hg⟩ := x.2.2
  have hgA : rho g ∈ A := hg ▸ x.2.1
  have hcad := hB' g hgA
  have hc1 : g.1 ≠ 1 := by
    intro h
    rw [h, one_mul] at hcad
    have hd : g.2 = 1 := (mul_eq_left.mp hcad.symm)
    apply hx1
    apply Subtype.ext
    rw [← hg, show g = 1 from Prod.ext h hd, map_one]
    rfl
  obtain ⟨X, hXs, hXb⟩ := exists_fix_not_fix hcad hc1
  set s := rho (a, a⁻¹) * tau with hsdef
  have hle : fixV A ≤ fixV (Subgroup.zpowers s) := fun v hv y hy =>
    hv y ((Subgroup.zpowers_le.mpr hsA) hy)
  have hXin : X ∈ fixV (Subgroup.zpowers s) := mem_fixV_zpowers.mpr hXs
  have hXnot : X ∉ fixV A := fun hX => hXb (hX _ hgA)
  have h64 : Nat.card ↥(fixV (Subgroup.zpowers s)) ≤ 64 :=
    card_fixV_le (hAN hsA) (orderOf_eq_prime (hA.2 s hsA) hs1)
  have h32 : Nat.card ↥(fixV A) ≤ 32 := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
    have hpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      exact hXnot ((Subgroup.eq_of_le_of_card_ge hle hm.le) ▸ hXin)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact absurd hm (Nat.card_pos (α := ↥(fixV (Subgroup.zpowers s)))).ne'
    have : Nat.card ↥(fixV A) * 2 ≤ Nat.card ↥(fixV A) * m := Nat.mul_le_mul_left _ (by omega)
    omega
  have hA8 : Nat.card A ≤ 8 := by omega
  calc Nat.card A * Nat.card ↥(fixV A) ≤ 8 * 32 := Nat.mul_le_mul hA8 h32
    _ < 2 ^ 9 := by norm_num

theorem fixV_bot {V : Type*} [CommGroup V] : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
  refine eq_top_iff.mpr fun v _ x hx => ?_
  rw [Subgroup.mem_bot.mp hx]
  rfl

theorem not_isFFStarOffender_of_tensorPair {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H) (A : Subgroup (MulAut V)) :
    ¬ IsFFStarOffender (Subgroup.normalizer (H : Set (MulAut V))) A := by
  rintro ⟨hAN, hAne, hAel, hmax⟩
  obtain ⟨e, he⟩ := exists_model hreal
  have hV := hmax ⊥ bot_le
  rw [Subgroup.card_bot, one_mul, fixV_bot, Subgroup.card_top] at hV
  have hN : A.map (congrHom e) ≤ L3Wr.norm := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut WMod)) :
          Set (MulAut WMod)) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    have h4 := (Subgroup.map_mono (f := congrHom e) hAN).trans (le_of_eq h3)
    have h5 := congrArg (fun K : Subgroup (MulAut WMod) => Subgroup.normalizer
      (K : Set (MulAut WMod))) he
    exact h4.trans (le_of_eq h5)
  have hne : A.map (congrHom e) ≠ ⊥ := fun h =>
    hAne ((Subgroup.map_eq_bot_iff_of_injective A (congrHom_injective e)).mp h)
  have hlt := card_mul_card_fixV_lt hN ((isElemAbelian2_map_congrHom e).mpr hAel) hne
  have h1 : Nat.card ↥(A.map (congrHom e)) = Nat.card ↥A := card_map_congrHom e A
  have h2 : Nat.card ↥(fixV (A.map (congrHom e))) = Nat.card ↥(fixV A) :=
    (congrArg (fun K : Subgroup WMod => Nat.card ↥K) (fixV_map_congrHom e A)).trans
      (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective)
  have key : Nat.card ↥A * Nat.card ↥(fixV A) < 2 ^ 9 := by
    rw [← h1, ← h2]
    exact hlt
  have hcardV : Nat.card V = 2 ^ 9 := by rw [Nat.card_congr e.toEquiv, card_WMod]
  omega

theorem not_concl701FF_of_l3Wreath {G : Type} [Group G] {T L I : Subgroup G}
    [IsMulCommutative ↥(fsuV T I)] (h : Row711L3Wreath T L I) : ¬ Concl701FF T L I :=
  fun ⟨A, hA⟩ => not_isFFStarOffender_of_tensorPair h.2 A hA

end CFSG.Quasithin.Vol2.Ch10.C3
