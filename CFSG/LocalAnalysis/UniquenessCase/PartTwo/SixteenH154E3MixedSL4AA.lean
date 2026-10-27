module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_z0_le_Z (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x ≤
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hxinvM : x⁻¹ ∈ D.M := D.M.inv_mem hxM
  have hxninv : x⁻¹ ∉ nBar D.M ⊥ V hV L := fun hh =>
    hxn ((nBar D.M ⊥ V hV L).inv_mem_iff.mp hh)
  have hE : conjSubgroup L x⁻¹ ≤ stabTil ⊥ V := by
    refine (E3.conjSubgroup_mono_left x⁻¹ (h.hyp151.le.trans hMs)).trans ?_
    rw [show conjSubgroup (stabTil ⊥ V) x⁻¹ = stabTil ⊥ V from
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hMs hxinvM))]
  have hcomm : commSub (wTil ⊥ V hV L) (barSub ⊥ V hV (conjSubgroup L x⁻¹)) = ⊥ :=
    (h.hyp151.commute x⁻¹ hxinvM hxninv).2
  have hWle : wSub ⊥ V hV L ≤ preTil ⊥ V hV (fixV (barSub ⊥ V hV (conjSubgroup L x⁻¹))) :=
    s16c34_wSub_le_preTil_fixV hV hcomm
  have hLcentW : conjSubgroup L x⁻¹ ≤ Subgroup.centralizer (wSub ⊥ V hV L : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwV : w ∈ V := preTil_le ⊥ V hV _ (hWle hw)
    have h1 :=
      (s15_Glue_mem_preTil_fixV_iff ⊥ V (conjSubgroup L x⁻¹) hV hE hwV).1 (hWle hw) e he
    rw [Subgroup.mem_bot] at h1
    have h2 : e * w * e⁻¹ = w := mul_inv_eq_one.1 h1
    have h3 : e * w = w * e := by
      calc e * w = (e * w * e⁻¹) * e := by group
        _ = w * e := by rw [h2]
    exact h3.symm
  have hLcentWx : L ≤ Subgroup.centralizer
      (conjSubgroup (wSub ⊥ V hV L) x : Set G) := by
    have hmono := E3.conjSubgroup_mono_left x hLcentW
    rw [E3.conjSubgroup_inv_conj L x, E3.conjSubgroup_centralizer (wSub ⊥ V hV L) x] at hmono
    exact hmono
  have hWxcentL : conjSubgroup (wSub ⊥ V hV L) x ≤ Subgroup.centralizer (L : Set G) :=
    (Subgroup.le_centralizer_iff (H := L)
      (K := conjSubgroup (wSub ⊥ V hV L) x)).1 hLcentWx
  exact le_inf inf_le_left (inf_le_right.trans hWxcentL)

private theorem s16h_sl4_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    have hx : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h
    rw [mem_modNull] at hx
    exact IntMod.val_injective (by simpa using hx)
  · rintro rfl
    exact map_one _

private theorem s16h_sl4_card_preTil_bot {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil ⊥ V hV)) :
    Nat.card ↥(preTil ⊥ V hV S) = Nat.card ↥S := by
  unfold preTil
  rw [Subgroup.card_map_of_injective (f := valHom V hV)
    (K := S.comap (mkTil ⊥ V hV)) (fun x y h => IntMod.val_injective h)]
  rw [← Subgroup.card_map_of_injective (f := mkTil ⊥ V hV)
    (K := S.comap (mkTil ⊥ V hV)) (s16h_sl4_mkTil_bot_injective hV),
    Subgroup.map_comap_eq_self_of_surjective (mkTil_surjective ⊥ V hV) S]

theorem s16h_sl4_card_Z (D : Data G) (hJP : K_JonesParshallH1) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    Nat.card ↥(wSub ⊥ V h.hyp151.isElemAbelian L ⊓
      Subgroup.centralizer (L : Set G)) = 4 := by
  let Sbar : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian) :=
    commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)
  have hZeq : wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) =
      preTil ⊥ V h.hyp151.isElemAbelian Sbar :=
    s16h_wSub_inf_centralizer_eq_preTil D h
  have hcard_pre : Nat.card ↥(preTil ⊥ V h.hyp151.isElemAbelian Sbar) =
      Nat.card ↥Sbar := s16h_sl4_card_preTil_bot h.hyp151.isElemAbelian Sbar
  have hsq : ∀ y : Vtil ⊥ V h.hyp151.isElemAbelian, y ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one ⊥ V h.hyp151.isElemAbelian
  have hcardS : Nat.card ↥Sbar = 2 ^ rk ↥Sbar := CFSG.Quasithin.card_eq_two_pow hsq Sbar
  have hrk : rk ↥Sbar ≤ 2 :=
    (hJP (Vtil ⊥ V h.hyp151.isElemAbelian) hsq (lBar ⊥ V h.hyp151.isElemAbelian L)).2
      (by simpa [Sbar] using hrow)
  have hrk2 : rk ↥Sbar = 2 := by
    by_contra hne
    have hle1 : rk ↥Sbar ≤ 1 := by omega
    rw [hcardS] at hZ4
    have h1 : 2 ^ rk ↥Sbar ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle1
    norm_num at h1
    omega
  rw [hZeq, hcard_pre, hcardS, hrk2]
  norm_num

private theorem s16h_sl4_eq_of_ne_one_of_card_le_two {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H ≤ 2) {a b : H} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hcase : Nat.card H = 1 ∨ Nat.card H = 2 := by omega
  rcases hcase with h1 | h2
  · haveI : Subsingleton H :=
      (Finite.card_le_one_iff_subsingleton (α := H)).mp (le_of_eq h1)
    exact absurd (Subsingleton.elim a 1) ha
  · obtain ⟨y, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
    exact (huniq a ha).trans (huniq b hb).symm

theorem s16h_sl4_bot_or_eq_of_card_four {Z₀ Z : Subgroup G} {d : G}
    (hZ₀Z : Z₀ ≤ Z) (hZcard : Nat.card ↥Z = 4)
    (hinv : ∀ z ∈ Z₀, d * z * d⁻¹ ∈ Z₀)
    (hfpf : ∀ z ∈ Z, d * z * d⁻¹ = z → z = 1) :
    Z₀ = ⊥ ∨ Z₀ = Z := by
  have hdvd : Nat.card ↥Z₀ ∣ 4 := by
    have h1 : Nat.card ↥(Z₀.subgroupOf Z) ∣ Nat.card ↥Z :=
      Subgroup.card_subgroup_dvd_card (Z₀.subgroupOf Z)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₀Z).toEquiv, hZcard] at h1
  have hdvd' : Nat.card ↥Z₀ ∣ 2 ^ 2 := by
    simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using hdvd
  obtain ⟨k, hk, hpow⟩ := (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).1 hdvd'
  have hk012 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk012 with rfl | rfl | rfl
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz1 : (⟨z, hz⟩ : ↥Z₀) = ⟨1, Z₀.one_mem⟩ := by
      haveI : Subsingleton ↥Z₀ :=
        (Finite.card_le_one_iff_subsingleton (α := ↥Z₀)).mp (by
          rw [hpow]
          norm_num)
      exact Subsingleton.elim _ _
    exact congrArg Subtype.val hz1
  · exfalso
    have hcardZ₀ : Nat.card ↥Z₀ = 2 := by
      simpa using hpow
    have hne : Z₀ ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcardZ₀
      omega
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hz : (z : G) ∈ Z₀ := z.2
    have hdz : d * (z : G) * d⁻¹ ∈ Z₀ := hinv (z : G) hz
    have hdz1 : d * (z : G) * d⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      refine Subtype.ext ?_
      calc (z : G) = d⁻¹ * (d * (z : G) * d⁻¹) * d := by group
        _ = d⁻¹ * 1 * d := by rw [h1]
        _ = 1 := by group
    have heq : z = ⟨d * (z : G) * d⁻¹, hdz⟩ :=
      s16h_sl4_eq_of_ne_one_of_card_le_two
        (H := ↥Z₀) (by omega) hz1 (fun h => hdz1 (congrArg Subtype.val h))
    have hzfix : d * (z : G) * d⁻¹ = (z : G) := (congrArg Subtype.val heq).symm
    exact hz1 (Subtype.ext (hfpf (z : G) (hZ₀Z hz) hzfix))
  · right
    exact Subgroup.eq_of_le_of_card_ge hZ₀Z (by rw [hZcard, hpow]; norm_num)

theorem s16h_sl4_scalar_free
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    ∃ d : G, d ∈ D.M ∧ orderOf d = 3 ∧
      (∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L,
        d * w * d⁻¹ ∈ wSub ⊥ V h.hyp151.isElemAbelian L) ∧
      (∀ w ∈ conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x,
        d * w * d⁻¹ ∈ conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x) ∧
      (∀ z ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G),
        d * z * d⁻¹ = z → z = 1) := by
  obtain ⟨d, hdM, hd3, hWn, hWxn, hZn, hnt⟩ :=
    s16h_sl4_scalar_element D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad hrow
      hZ4 hxM hxn
  exact ⟨d, hdM, hd3, hWn, hWxn,
    s16h_sl4_fpf_of_card_four (s16h_sl4_card_Z D hJP h hrow hZ4) hd3 hZn hnt⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
