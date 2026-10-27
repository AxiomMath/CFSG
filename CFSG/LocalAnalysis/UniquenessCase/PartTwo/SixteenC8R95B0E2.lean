module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0D
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrobPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem r95_frattini_lift {E Qm : Type} [Group E] [Finite E] [Group Qm] (π : E →* Qm)
    (hπ : Function.Surjective π) (p : ℕ) [Fact p.Prime]
    {V : Subgroup Qm} (hV : IsPGroup p V) :
    ∃ R : Subgroup E, IsPGroup p R ∧ R.map π = V ∧
      ∀ x ∈ Subgroup.normalizer (V : Set Qm), ∃ n ∈ Subgroup.normalizer (R : Set E), ∃ v ∈ V, π n =
      x * v := by
  classical
  let N : Subgroup E := (Subgroup.normalizer (V : Set Qm)).comap π
  let P : Subgroup E := V.comap π
  have hPN : P ≤ N := Subgroup.comap_mono Subgroup.le_normalizer
  have hle : N ≤ Subgroup.normalizer (P : Set E) := Subgroup.le_normalizer_comap π
  let P' : Subgroup ↥N := P.subgroupOf N
  have hP'normal : P'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr hle
  haveI : P'.Normal := hP'normal
  let R' : Sylow p ↥P' := default
  have hR'p : IsPGroup p (R' : Subgroup ↥P') := R'.isPGroup'
  let H' : Subgroup ↥N := (R' : Subgroup ↥P').map P'.subtype
  let R : Subgroup E := H'.map N.subtype
  let π' : ↥P' →* ↥V :=
    { toFun := fun z => ⟨π ((z : ↥N) : E),
        Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp (z : ↥P').2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [map_mul]) }
  have hπ' : Function.Surjective π' := by
    intro v
    obtain ⟨e, he⟩ := hπ (v : Qm)
    have heP : e ∈ P := Subgroup.mem_comap.mpr (by rw [he]; exact v.2)
    have heN : e ∈ N :=
      Subgroup.mem_comap.mpr (by rw [he]; exact Subgroup.le_normalizer v.2)
    exact ⟨⟨⟨e, heN⟩, Subgroup.mem_subgroupOf.mpr heP⟩, Subtype.ext he⟩
  have hfr : Subgroup.normalizer (H' : Set ↥N) ⊔ P' = ⊤ := Sylow.normalizer_sup_eq_top R'
  have hcomp : (π.comp N.subtype).comp P'.subtype = V.subtype.comp π' := by
    ext z
    rfl
  have hRmapπ : R.map π = ((R' : Subgroup ↥P').map π').map V.subtype := by
    change (((R' : Subgroup ↥P').map P'.subtype).map N.subtype).map π
      = ((R' : Subgroup ↥P').map π').map V.subtype
    calc (((R' : Subgroup ↥P').map P'.subtype).map N.subtype).map π
        = ((R' : Subgroup ↥P').map P'.subtype).map (π.comp N.subtype) :=
          Subgroup.map_map ((R' : Subgroup ↥P').map P'.subtype) π N.subtype
      _ = (R' : Subgroup ↥P').map ((π.comp N.subtype).comp P'.subtype) :=
          Subgroup.map_map (R' : Subgroup ↥P') (π.comp N.subtype) P'.subtype
      _ = (R' : Subgroup ↥P').map (V.subtype.comp π') := by rw [hcomp]
      _ = ((R' : Subgroup ↥P').map π').map V.subtype :=
          (Subgroup.map_map (R' : Subgroup ↥P') V.subtype π').symm
  let S' : Sylow p ↥V := Sylow.mapSurjective (f := π') hπ' R'
  have hS'coe : (S' : Subgroup ↥V) = (R' : Subgroup ↥P').map π' :=
    Sylow.coe_mapSurjective (f := π') hπ' R'
  have hS'top : (S' : Subgroup ↥V) = ⊤ :=
    (S'.is_maximal' (hV.to_subgroup (⊤ : Subgroup ↥V)) le_top).symm
  have hmapπ' : (R' : Subgroup ↥P').map π' = ⊤ := by rw [← hS'coe, hS'top]
  have htopmap : (⊤ : Subgroup ↥V).map V.subtype = V := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hRmap : R.map π = V := by rw [hRmapπ, hmapπ', htopmap]
  have hRp : IsPGroup p R := (hR'p.map P'.subtype).map N.subtype
  refine ⟨R, hRp, hRmap, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hπ x
  have hyN : y ∈ N := Subgroup.mem_comap.mpr (by rw [hy]; exact hx)
  have hytop : (⟨y, hyN⟩ : ↥N) ∈ (⊤ : Subgroup ↥N) := Subgroup.mem_top _
  rw [← hfr] at hytop
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := Subgroup.normalizer (H' : Set ↥N))
      (t := P')).mp hytop
  refine ⟨N.subtype a, ?_, (π (N.subtype b))⁻¹, ?_, ?_⟩
  · exact Subgroup.le_normalizer_map N.subtype (Subgroup.mem_map_of_mem N.subtype ha)
  · have hbP : (b : E) ∈ P := Subgroup.mem_subgroupOf.mp hb
    exact V.inv_mem (Subgroup.mem_comap.mp hbP)
  · have hπab : π (N.subtype a) * π (N.subtype b) = x := by
      rw [← map_mul, ← map_mul N.subtype, hab]
      exact hy
    exact (eq_mul_inv_iff_mul_eq).mpr hπab

theorem r95_exists_seven_normalizer {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q}
    (hE : HasL32Quot E) :
    ∃ D R : Subgroup Q, D ≤ E ∧ R ≤ E ∧ Nat.card D = 3 ∧ IsPGroup 7 R ∧ R ≠ ⊥ ∧ D ≤
    Subgroup.normalizer (R : Set Q) := by
  classical
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  haveI : Finite Qm := Finite.of_surjective π hπ
  have hm7 : LieModel Qm .PSL 2 7 1 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism Qm hm
  have hX : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsLThreeTwo Qm :=
    CFSG.AGLEmbeddingD2.McLaughlin.Lie.isLThreeTwo_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel hm7 (by decide))
  have hcard : Nat.card Qm = 168 := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_card_eq hX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Qm) 3 (by rw [hcard]; norm_num)
  obtain ⟨b, hb7, hb1, hcb⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.exists_frobenius_pair hX hc
  have hbord : orderOf b = 7 := orderOf_eq_prime hb7 hb1
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  set c' : Qm := if c * b = b ^ 2 * c then c else c⁻¹ with hc'def
  have hc'ord : orderOf c' = 3 := by
    by_cases h : c * b = b ^ 2 * c
    · rw [hc'def, if_pos h]; exact hc
    · rw [hc'def, if_neg h, orderOf_inv, hc]
  have hc'b : c' * b = b ^ 2 * c' := by
    by_cases h : c * b = b ^ 2 * c
    · rw [hc'def, if_pos h]; exact h
    · rw [hc'def, if_neg h]
      rcases hcb with h1 | h2
      · exact absurd h1 h
      · exact h2
  set V : Subgroup Qm := Subgroup.zpowers b with hVdef
  have hVcard : Nat.card ↥V = 7 := by rw [hVdef, Nat.card_zpowers, hbord]
  have hVp : IsPGroup 7 V := by
    rw [hVdef]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbord]; norm_num)
  have hVbot : V ≠ ⊥ := by
    intro h
    have hb : b ∈ (⊥ : Subgroup Qm) := h ▸ Subgroup.mem_zpowers b
    exact hb1 (Subgroup.mem_bot.mp hb)
  have hc'N : c' ∈ Subgroup.normalizer (V : Set Qm) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hVdef, MonoidHom.map_zpowers]
    have hconj : MulAut.conj c' b = b ^ 2 := by rw [MulAut.conj_apply, hc'b]; group
    have hb2 : Subgroup.zpowers (b ^ 2) = Subgroup.zpowers b := by
      have hbmem : b ∈ Subgroup.zpowers (b ^ 2) := by
        have h4 : (b ^ 2) ^ 4 = b := by
          calc (b ^ 2) ^ 4 = b ^ (2 * 4) := by rw [pow_mul]
            _ = b ^ 8 := by norm_num
            _ = b ^ 7 * b := by rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ]
            _ = 1 * b := by rw [hb7]
            _ = b := by rw [one_mul]
        have h := Subgroup.pow_mem (Subgroup.zpowers (b ^ 2)) (Subgroup.mem_zpowers (b ^ 2)) 4
        rwa [h4] at h
      exact le_antisymm
        (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) 2))
        (Subgroup.zpowers_le.mpr hbmem)
    change Subgroup.zpowers (MulAut.conj c' b) = Subgroup.zpowers b
    rw [hconj, hb2]
  obtain ⟨R₀, hR₀p, hR₀π, hfr⟩ := r95_frattini_lift π hπ 7 hVp
  obtain ⟨n, hn, v, hv, hπn⟩ := hfr c' hc'N
  have h3V : (π n) ^ 3 ∈ V := by
    set w : Qm := c' * v * c'⁻¹ with hwdef
    have hwV : w ∈ V := (Subgroup.mem_normalizer_iff.mp hc'N v).mp hv
    have hw1V : c' * w * c'⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hc'N w).mp hwV
    have hw2V : c' ^ 2 * w * (c' ^ 2)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hc'N 2) w).mp hwV
    have hcc : c' ^ 3 = 1 := by rw [← hc'ord]; exact pow_orderOf_eq_one c'
    have hcv : c' * v = w * c' := by rw [hwdef]; group
    have hident : (w * c') ^ 3
        = w * (c' * w * c'⁻¹) * (c' ^ 2 * w * (c' ^ 2)⁻¹) * c' ^ 3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
      group
    rw [hπn, hcv, hident, hcc, mul_one]
    exact V.mul_mem (V.mul_mem hwV hw1V) hw2V
  have hx7 : ∀ x ∈ V, x ^ 7 = 1 := by
    intro x hx
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [← hVcard]; exact Subgroup.orderOf_dvd_natCard V hx)
  have h21 : (π n) ^ 21 = 1 := by
    rw [show (21 : ℕ) = 3 * 7 from by norm_num, pow_mul]
    exact hx7 _ h3V
  have h3dvdπ : 3 ∣ orderOf (π n) := by
    by_contra h3
    have hcop : Nat.Coprime 3 (orderOf (π n)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hdvd21 : orderOf (π n) ∣ 21 := orderOf_dvd_iff_pow_eq_one.mpr h21
    have hdvd7 : orderOf (π n) ∣ 7 := (hcop.symm.dvd_mul_left).mp (by simpa using hdvd21)
    have h7 : (π n) ^ 7 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd7
    have hmul : π n * ((π n) ^ 3) ^ 2 = 1 := by
      rw [← pow_mul, show (3 * 2 : ℕ) = 6 from by norm_num, ← pow_succ']
      exact h7
    have hxmem : π n ∈ V := by
      rw [eq_inv_of_mul_eq_one_left hmul]
      exact V.inv_mem (Subgroup.pow_mem _ h3V 2)
    have hc'V : c' ∈ V := by
      have hcv' : c' = π n * v⁻¹ := by rw [hπn]; group
      rw [hcv']
      exact V.mul_mem hxmem (V.inv_mem hv)
    have hdvd : orderOf c' ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr (hx7 c' hc'V)
    rw [hc'ord] at hdvd
    exact absurd hdvd (by norm_num)
  have h3dvd : 3 ∣ orderOf n := h3dvdπ.trans (orderOf_map_dvd π n)
  have hord0 : orderOf n ≠ 0 := by
    intro h0
    have h : Nat.card ↥E = 0 := Nat.eq_zero_of_zero_dvd (h0 ▸ orderOf_dvd_natCard n)
    exact Nat.card_pos.ne' h
  let y : ↥E := n ^ (orderOf n / 3)
  have hyord : orderOf y = 3 := orderOf_pow_orderOf_div (x := n) (n := 3) hord0 h3dvd
  have hyN : y ∈ Subgroup.normalizer (R₀ : Set ↥E) := Subgroup.pow_mem _ hn _
  refine ⟨(Subgroup.zpowers y).map E.subtype, R₀.map E.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective, Nat.card_zpowers, hyord]
  · exact hR₀p.map E.subtype
  · intro hbot
    have hR₀bot : R₀ = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective R₀ E.subtype_injective).mp hbot
    have h : R₀.map π = ⊥ := by rw [hR₀bot, Subgroup.map_bot]
    rw [hR₀π] at h
    exact hVbot h
  · calc (Subgroup.zpowers y).map E.subtype
        ≤ (Subgroup.normalizer (R₀ : Set ↥E)).map E.subtype :=
          Subgroup.map_mono (Subgroup.zpowers_le.mpr hyN)
      _ ≤ Subgroup.normalizer ((R₀ : Subgroup ↥E).map E.subtype : Set Q) :=
          Subgroup.le_normalizer_map E.subtype

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
