module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Alg

variable {X : Type} [Group X] [Finite X]

private def endg_h1_conjEquiv {Y : Subgroup X} (hY : Y.Normal) (g : X) : ↥Y ≃* ↥Y where
  toFun u := ⟨g * (u : X) * g⁻¹, hY.conj_mem _ u.2 g⟩
  invFun u := ⟨g⁻¹ * (u : X) * g, hY.conj_mem' _ u.2 g⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

private theorem endg_h1_map_normal {Y : Subgroup X} (hY : Y.Normal) (S : Subgroup ↥Y)
    (hS : ∀ g : X, ∀ u ∈ S, endg_h1_conjEquiv hY g u ∈ S) : (S.map Y.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hn
  exact Subgroup.mem_map.mpr ⟨endg_h1_conjEquiv hY g u, hS g u hu, rfl⟩

private theorem endg_h1_eq_bot_of_map {Y : Subgroup X} (S : Subgroup ↥Y)
    (h : S.map Y.subtype = ⊥) : S = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  have h1 : Y.subtype u ∈ S.map Y.subtype := Subgroup.mem_map_of_mem _ hu
  rw [h, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

private theorem endg_h1_le_pCore {Y : Subgroup X} (hY : Y.Normal) (hp : IsPGroup 2 Y) :
    Y ≤ pCore 2 X :=
  le_sSup ⟨hY, hp⟩

theorem endg_pCore_eq_bot_of_normal (ho : pCore 2 X = ⊥) {Y : Subgroup X} (hY : Y.Normal) :
    pCore 2 ↥Y = ⊥ := by
  have hstab : ∀ g : X, ∀ u ∈ pCore 2 ↥Y, endg_h1_conjEquiv hY g u ∈ pCore 2 ↥Y := by
    intro g u hu
    have h : (pCore 2 ↥Y).map (endg_h1_conjEquiv hY g).toMonoidHom = pCore 2 ↥Y :=
      CFSG.pCore_map_iso 2 (endg_h1_conjEquiv hY g)
    have h2 : endg_h1_conjEquiv hY g u ∈
        (pCore 2 ↥Y).map (endg_h1_conjEquiv hY g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hu
    rwa [h] at h2
  have hnorm := endg_h1_map_normal hY (pCore 2 ↥Y) hstab
  have hp : IsPGroup 2 ((pCore 2 ↥Y).map Y.subtype) :=
    IsPGroup.map CFSG.pCore_isPGroup Y.subtype
  have hle : (pCore 2 ↥Y).map Y.subtype ≤ pCore 2 X := endg_h1_le_pCore hnorm hp
  rw [ho, le_bot_iff] at hle
  exact endg_h1_eq_bot_of_map _ hle

theorem endg_eq_bot_of_normal_abelian {H : Subgroup X} (ho : pCore 2 X = ⊥)
    (h5 : ∀ Y : Subgroup X, Y.Normal → Y ≤ H → Odd (Nat.card Y) → Y = ⊥)
    {Y : Subgroup X} (hY : Y.Normal) (hYH : Y ≤ H)
    (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) : Y = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := ↥Y)).ne'
  let f : ↥Y →* ↥Y :=
    { toFun := fun y => y ^ (2 ^ a)
      map_one' := one_pow _
      map_mul' := fun x y => by
        have hc : Commute x y := by
          show x * y = y * x
          exact Subtype.ext (hab x x.2 y y.2)
        exact hc.mul_pow _ }
  let O : Subgroup X := f.range.map Y.subtype
  have hOle : O ≤ Y := by
    intro w hw
    obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hw
    exact u.2
  have hOH : O ≤ H := hOle.trans hYH
  have hOn : O.Normal := by
    apply endg_h1_map_normal hY
    intro g u hu
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hu
    refine MonoidHom.mem_range.mpr ⟨endg_h1_conjEquiv hY g v, ?_⟩
    exact (map_pow (endg_h1_conjEquiv hY g) v (2 ^ a)).symm
  have hOm : ∀ w : X, w ∈ O → w ^ m = 1 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hu
    show ((v ^ (2 ^ a) : ↥Y) : X) ^ m = 1
    rw [← Subgroup.coe_pow, ← pow_mul, ← hcard,
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard v), Subgroup.coe_one]
  have hOodd : Odd (Nat.card O) := by
    rcases Nat.even_or_odd (Nat.card O) with he | ho'
    · exfalso
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥O) 2 (even_iff_two_dvd.mp he)
      have h1 : orderOf (x : X) = 2 := (Subgroup.orderOf_coe x).trans hx
      have h3 : orderOf (x : X) ∣ m := orderOf_dvd_of_pow_eq_one (hOm x x.2)
      rw [h1] at h3
      have h4 := Nat.odd_iff.mp hm
      omega
    · exact ho'
  have hObot : O = ⊥ := h5 O hOn hOH hOodd
  have hYp : IsPGroup 2 ↥Y := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    refine ⟨a, ?_⟩
    have hmem : Y.subtype (g ^ (2 ^ a)) ∈ O :=
      Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [hObot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hle : Y ≤ pCore 2 X := endg_h1_le_pCore hY hYp
  rw [ho, le_bot_iff] at hle
  exact hle

theorem endg_center_eq_bot_of_normal {H : Subgroup X} (ho : pCore 2 X = ⊥)
    (h5 : ∀ Y : Subgroup X, Y.Normal → Y ≤ H → Odd (Nat.card Y) → Y = ⊥)
    {Y : Subgroup X} (hY : Y.Normal) (hYH : Y ≤ H) : Subgroup.center ↥Y = ⊥ := by
  have hstab : ∀ g : X, ∀ u ∈ Subgroup.center ↥Y,
      endg_h1_conjEquiv hY g u ∈ Subgroup.center ↥Y := by
    intro g u hu
    rw [Subgroup.mem_center_iff] at hu ⊢
    intro y
    have hy := hu ⟨g⁻¹ * (y : X) * g, hY.conj_mem' _ y.2 g⟩
    have hy' : (g⁻¹ * (y : X) * g) * (u : X) = (u : X) * (g⁻¹ * (y : X) * g) :=
      congrArg Subtype.val hy
    apply Subtype.ext
    calc (y : X) * (g * (u : X) * g⁻¹) = g * ((g⁻¹ * (y : X) * g) * (u : X)) * g⁻¹ := by
          group
      _ = g * ((u : X) * (g⁻¹ * (y : X) * g)) * g⁻¹ := by rw [hy']
      _ = g * (u : X) * g⁻¹ * (y : X) := by group
  have hZ : ((Subgroup.center ↥Y).map Y.subtype).Normal := endg_h1_map_normal hY _ hstab
  have hZH : (Subgroup.center ↥Y).map Y.subtype ≤ H := by
    intro w hw
    obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hw
    exact hYH u.2
  have hZab : ∀ a ∈ (Subgroup.center ↥Y).map Y.subtype,
      ∀ b ∈ (Subgroup.center ↥Y).map Y.subtype, a * b = b * a := by
    intro a ha b hb
    obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hb
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hv u)
  have hZbot := endg_eq_bot_of_normal_abelian ho h5 hZ hZH hZab
  exact endg_h1_eq_bot_of_map _ hZbot

theorem endg_goldschmidtOddCore_eq_bot {H : Subgroup X}
    (h5 : ∀ Y : Subgroup X, Y.Normal → Y ≤ H → Odd (Nat.card Y) → Y = ⊥)
    {Y : Subgroup X} (hY : Y.Normal) (hYH : Y ≤ H) : goldschmidtOddCore ↥Y = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : goldschmidtOddCore ↥Y = CFSG.pPrimeCore 2 ↥Y := by
    simp only [goldschmidtOddCore, CFSG.pPrimeCore, Nat.coprime_two_left]
  rw [hcore]
  have hstab : ∀ g : X, ∀ u ∈ CFSG.pPrimeCore 2 ↥Y,
      endg_h1_conjEquiv hY g u ∈ CFSG.pPrimeCore 2 ↥Y := by
    intro g u hu
    have h : (CFSG.pPrimeCore 2 ↥Y).map (endg_h1_conjEquiv hY g).toMonoidHom =
        CFSG.pPrimeCore 2 ↥Y :=
      CFSG.pPrimeCore_map_iso 2 (endg_h1_conjEquiv hY g)
    have h2 : endg_h1_conjEquiv hY g u ∈
        (CFSG.pPrimeCore 2 ↥Y).map (endg_h1_conjEquiv hY g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hu
    rwa [h] at h2
  have hnorm := endg_h1_map_normal hY (CFSG.pPrimeCore 2 ↥Y) hstab
  have hodd : Odd (Nat.card ((CFSG.pPrimeCore 2 ↥Y).map Y.subtype)) := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hle : (CFSG.pPrimeCore 2 ↥Y).map Y.subtype ≤ H := by
    intro w hw
    obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hw
    exact hYH u.2
  exact endg_h1_eq_bot_of_map _ (h5 _ hnorm hle hodd)

theorem endg_exists_sylow_central {A : Subgroup X} (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥)
    (T : Sylow 2 X) (hT : (T : Subgroup X) ≤ Subgroup.normalizer (A : Set X)) :
    ∃ z ∈ A, z ≠ 1 ∧ z ∈ (T : Subgroup X) ∧ ∀ x ∈ (T : Subgroup X), x * z = z * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥(T : Subgroup X) := T.isPGroup'
  have hTA : ∀ t : ↥(T : Subgroup X), ∀ a : ↥A, (t : X) * (a : X) * (t : X)⁻¹ ∈ A :=
    fun t a => (Subgroup.mem_normalizer_iff.mp (hT t.2) (a : X)).mp a.2
  letI : MulAction ↥(T : Subgroup X) ↥A :=
    { smul := fun t a => ⟨(t : X) * (a : X) * (t : X)⁻¹, hTA t a⟩
      one_smul := fun a => Subtype.ext (show (1 : X) * (a : X) * (1 : X)⁻¹ = (a : X) by simp)
      mul_smul := fun s t a => Subtype.ext (show
        ((s : X) * (t : X)) * (a : X) * ((s : X) * (t : X))⁻¹ =
          (s : X) * ((t : X) * (a : X) * (t : X)⁻¹) * (s : X)⁻¹ by group) }
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hA1
    exact Subgroup.eq_bot_of_card_eq (H := A) (by rw [hk]; simp)
  have h2A : 2 ∣ Nat.card A := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hmod := hT2.card_modEq_card_fixedPoints ↥A
  have hF : 2 ∣ Nat.card (MulAction.fixedPoints ↥(T : Subgroup X) ↥A) :=
    (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr h2A))
  obtain ⟨z, hzfix, hz1⟩ : ∃ z : ↥A, (∀ t : ↥(T : Subgroup X), t • z = z) ∧ z ≠ 1 := by
    by_contra! hcon
    have hsub : Subsingleton (MulAction.fixedPoints ↥(T : Subgroup X) ↥A) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : (a : ↥A) = 1 := hcon _ (MulAction.mem_fixedPoints.mp a.2)
      have hb : (b : ↥A) = 1 := hcon _ (MulAction.mem_fixedPoints.mp b.2)
      exact ha.trans hb.symm
    have hle : Nat.card (MulAction.fixedPoints ↥(T : Subgroup X) ↥A) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    haveI : Nonempty (MulAction.fixedPoints ↥(T : Subgroup X) ↥A) :=
      ⟨⟨1, MulAction.mem_fixedPoints.mpr fun t =>
        Subtype.ext (show (t : X) * (1 : X) * (t : X)⁻¹ = 1 by simp)⟩⟩
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥(T : Subgroup X) ↥A) := Nat.card_pos
    have := Nat.le_of_dvd hpos hF
    omega
  have hQ : IsPGroup 2 (((T : Subgroup X) ⊔ A : Subgroup X)) :=
    IsPGroup.to_sup_of_normal_right' hT2 hA hT
  have hsup : (T : Subgroup X) ⊔ A = (T : Subgroup X) := T.is_maximal' hQ le_sup_left
  have hAT : A ≤ (T : Subgroup X) := by
    intro a ha
    have h' : a ∈ (T : Subgroup X) ⊔ A := Subgroup.mem_sup_right ha
    rwa [hsup] at h'
  refine ⟨(z : X), z.2, fun h => hz1 (Subtype.ext h), hAT z.2, fun x hx => ?_⟩
  have h : (x : X) * (z : X) * (x : X)⁻¹ = (z : X) := congrArg Subtype.val (hzfix ⟨x, hx⟩)
  calc (x : X) * (z : X) = ((x : X) * (z : X) * (x : X)⁻¹) * (x : X) := by group
    _ = (z : X) * (x : X) := by rw [h]

theorem endg_perfect_hom_trivial {K : Subgroup X} (hK : ⁅K, K⁆ = K) {G' : Type} [Group G']
    [Group.IsSolvable G'] (φ : ↥K →* G') (k : ↥K) : φ k = 1 := by
  have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    refine Subgroup.map_injective K.subtype_injective ?_
    rw [Subgroup.map_commutator, htop]
    exact hK
  have hD : ∀ n : ℕ, derivedSeries ↥K n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero _
    | succ n ih => rw [derivedSeries_succ, ih, hperf]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G')
  have hmem : k ∈ derivedSeries ↥K n := by
    rw [hD n]
    exact Subgroup.mem_top k
  have hk : φ k ∈ derivedSeries G' n :=
    map_derivedSeries_le_derivedSeries φ n (Subgroup.mem_map_of_mem φ hmem)
  rw [hn] at hk
  exact Subgroup.mem_bot.mp hk

private theorem endg_h1_stab {Y : Type} [Group Y] [Finite Y] (f : ℕ → Subgroup Y)
    (hf : Antitone f) : ∃ i, f i = f (i + 1) := by
  haveI : Finite (Subgroup Y) :=
    Finite.of_injective (fun H : Subgroup Y => (H : Set Y)) SetLike.coe_injective
  obtain ⟨x, y, hxy, hfxy⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, le_antisymm ((le_of_eq hfxy).trans (hf (Nat.succ_le_of_lt h))) (hf (Nat.le_succ x))⟩
  · exact ⟨y, le_antisymm ((le_of_eq hfxy.symm).trans (hf (Nat.succ_le_of_lt h)))
      (hf (Nat.le_succ y))⟩

theorem endg_exists_perfCore (R : Subgroup X) :
    ∃ K : Subgroup X, K ≤ R ∧ ⁅K, K⁆ = K ∧
      (∀ g : X, g ∈ Subgroup.normalizer (R : Set X) → g ∈ Subgroup.normalizer (K : Set X)) ∧
      ∀ (S : Type) [Group S] (π : ↥R →* S), Function.Surjective π →
        ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ →
        ∀ N : Subgroup X, (∀ r : ↥R, π r = 1 ↔ (r : X) ∈ N) → R ≤ K ⊔ N := by
  obtain ⟨i, hi⟩ := endg_h1_stab (derivedSeries ↥R) (derivedSeries_antitone (G := ↥R))
  have hconj : ∀ (n : ℕ) (x : X), x ∈ Subgroup.normalizer (R : Set X) →
      ∀ u ∈ (derivedSeries ↥R n).map R.subtype,
        x * u * x⁻¹ ∈ (derivedSeries ↥R n).map R.subtype := by
    intro n x hx u hu
    let c : ↥R →* ↥R :=
      { toFun := fun r => ⟨x * (r : X) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx (r : X)).mp r.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun r s => Subtype.ext (by simp [mul_assoc]) }
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    have hcv : c v ∈ (derivedSeries ↥R n).map c := Subgroup.mem_map_of_mem c hv
    exact Subgroup.mem_map.mpr ⟨c v, map_derivedSeries_le_derivedSeries c n hcv, rfl⟩
  refine ⟨(derivedSeries ↥R i).map R.subtype, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp hw
    exact u.2
  · rw [← Subgroup.map_commutator, ← derivedSeries_succ, ← hi]
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj i g hg h
    · intro hh
      have h' := hconj i g⁻¹ ((Subgroup.normalizer (R : Set X)).inv_mem hg) _ hh
      simpa [mul_assoc] using h'
  · intro S _ π hπ hperfS N hN
    have hpi : ∀ n : ℕ, (derivedSeries ↥R n).map π = ⊤ := by
      intro n
      induction n with
      | zero =>
        rw [derivedSeries_zero]
        exact Subgroup.map_top_of_surjective π hπ
      | succ n ih => rw [derivedSeries_succ, Subgroup.map_commutator, ih, hperfS]
    intro x hx
    have hmem : π ⟨x, hx⟩ ∈ (derivedSeries ↥R i).map π := by
      rw [hpi i]
      exact Subgroup.mem_top _
    obtain ⟨v, hv, hvπ⟩ := Subgroup.mem_map.mp hmem
    have hw : π (v⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, hvπ, inv_mul_cancel]
    have hN' : (v : X)⁻¹ * x ∈ N := (hN _).mp hw
    have hvK : (v : X) ∈ (derivedSeries ↥R i).map R.subtype :=
      Subgroup.mem_map_of_mem R.subtype hv
    have h' := Subgroup.mul_mem_sup hvK hN'
    rwa [mul_inv_cancel_left] at h'

end Alg

end CFSG.RankThree.GF2n.Stroth80
