module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1End175

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129SP

open CFSG CFSG.RankThree.LocalRank

theorem exists_oddCore {Y : Type} [Group Y] [Finite Y] (U : Subgroup Y) [U.Normal]
    (hUs : Group.IsSolvable U) (β : MulAut Y) (hβU : ∀ u, u ∈ U ↔ β u ∈ U)
    (R : Subgroup Y) (hRU : R ≤ U) (hRn : ∀ u ∈ U, ∀ r ∈ R, u * r * u⁻¹ ∈ R)
    (hRodd : Odd (Nat.card R)) :
    ∃ O : Subgroup U, O.Normal ∧ Odd (Nat.card O) ∧ R.subgroupOf U ≤ O ∧
      (O.map U.subtype).Normal ∧ (O.map U.subtype).map β.toMonoidHom = O.map U.subtype := by
  classical
  obtain ⟨hOs, hOchar, hO2, hOmax, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥U) Nat.prime_two
  set O : Subgroup U := aschbacherSolvableCore 2 U with hO
  haveI : O.Characteristic := hOchar
  have hR'O : R.subgroupOf U ≤ O := by
    refine hOmax _ ⟨fun r hr u => ?_⟩ ?_ ?_
    · rw [Subgroup.mem_subgroupOf] at hr ⊢
      simpa using hRn u u.2 r hr
    · haveI := hUs
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv]
      exact hRodd.not_two_dvd_nat
  refine ⟨O, inferInstance, ?_, hR'O, ?_, ?_⟩
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hO2)
  · refine ⟨fun n hn y => ?_⟩
    obtain ⟨o, ho, rfl⟩ := hn
    have hmem : (MulAut.conjNormal y : MulAut U) o ∈ O := by
      have h := hOchar.fixed (MulAut.conjNormal y : MulAut U)
      have : o ∈ O.comap (MulAut.conjNormal y : MulAut U).toMonoidHom := by
        rw [h]; exact ho
      exact this
    exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
  · have hmap : U.map β.toMonoidHom = U := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact (hβU u).1 hu
      · intro hy
        refine ⟨β.symm y, ?_, by simp⟩
        exact (hβU (β.symm y)).2 (by simpa using hy)
    let βU : MulAut U :=
      (Subgroup.equivMapOfInjective U β.toMonoidHom β.injective).trans
        (MulEquiv.subgroupCongr hmap)
    have hO' : O.map βU.toMonoidHom = O := Subgroup.characteristic_iff_map_eq.mp hOchar βU
    ext y
    constructor
    · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
      have : βU o ∈ O := by
        rw [← hO']
        exact ⟨o, ho, rfl⟩
      exact ⟨βU o, this, rfl⟩
    · rintro ⟨o, ho, rfl⟩
      rw [← hO'] at ho
      obtain ⟨o', ho', rfl⟩ := ho
      exact ⟨o', ⟨o', ho', rfl⟩, rfl⟩

theorem centralizes_mod_oddCore {Y : Type} [Group Y] [Finite Y] (hYp : Group.IsPerfect Y)
    (U : Subgroup Y) [U.Normal] (hUs : Group.IsSolvable U) {W : Type} [Group W]
    (hWs : IsSimpleGroup W) (π : Y →* W) (hπ : Function.Surjective π) (hker : π.ker = U)
    (β : MulAut Y) (hβ : ∃ y : Y, y⁻¹ * β y ∉ U) (OY : Subgroup Y) [hOn : OY.Normal]
    (hOYU : OY ≤ U) (hβOY : OY.map β.toMonoidHom = OY) (hfix : ∀ u ∈ U, u⁻¹ * β u ∈ OY) :
    ∀ y : Y, ∀ u ∈ U, y * u * y⁻¹ * u⁻¹ ∈ OY := by
  classical
  haveI := hUs
  set q : Y →* Y ⧸ OY := QuotientGroup.mk' OY with hq
  let β' : MulAut (Y ⧸ OY) := QuotientGroup.congr OY OY β hβOY
  have hβ'q : ∀ y : Y, β' (q y) = q (β y) := fun y => rfl
  have hfix' : ∀ u ∈ U, β' (q u) = q u := by
    intro u hu
    rw [hβ'q]
    symm
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hfix u hu
  let k : Subgroup Y :=
    (Subgroup.centralizer ((U.map q : Subgroup (Y ⧸ OY)) : Set (Y ⧸ OY))).comap q
  have hkmem : ∀ y : Y, y ∈ k ↔ ∀ u ∈ U, q y * q u = q u * q y := by
    intro y
    simp only [k, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
      Subgroup.mem_map]
    constructor
    · intro h u hu
      exact (h (q u) ⟨u, hu, rfl⟩).symm
    · rintro h _ ⟨u, hu, rfl⟩
      exact (h u hu).symm
  have hkn : k.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hkmem] at hn ⊢
    intro u hu
    have h1 := hn (g⁻¹ * u * g) (by
      have := Subgroup.Normal.conj_mem inferInstance u hu g⁻¹
      simpa using this)
    simp only [map_mul, map_inv] at h1 ⊢
    obtain ⟨c, hc⟩ : ∃ c, c = (q g)⁻¹ * q u * q g := ⟨_, rfl⟩
    have hqu : q u = q g * c * (q g)⁻¹ := by rw [hc]; group
    have h1' : q n * c = c * q n := by rw [hc]; exact h1
    rw [hqu]
    calc q g * q n * (q g)⁻¹ * (q g * c * (q g)⁻¹) = q g * (q n * c) * (q g)⁻¹ := by group
      _ = q g * (c * q n) * (q g)⁻¹ := by rw [h1']
      _ = q g * c * (q g)⁻¹ * (q g * q n * (q g)⁻¹) := by group
  have hdk : ∀ y : Y, y⁻¹ * β y ∈ k := by
    intro y
    rw [hkmem]
    intro u hu
    have hu' : y * u * y⁻¹ ∈ U := Subgroup.Normal.conj_mem inferInstance u hu y
    have hbu : q (β u) = q u := by rw [← hβ'q]; exact hfix' u hu
    have h1 : q (β (y * u * y⁻¹)) = q (y * u * y⁻¹) := by rw [← hβ'q]; exact hfix' _ hu'
    simp only [map_mul, map_inv, hbu] at h1 ⊢
    calc (q y)⁻¹ * q (β y) * q u
        = (q y)⁻¹ * (q (β y) * q u * (q (β y))⁻¹) * q (β y) := by group
      _ = (q y)⁻¹ * (q y * q u * (q y)⁻¹) * q (β y) := by rw [h1]
      _ = q u * ((q y)⁻¹ * q (β y)) := by group
  set J : Subgroup Y := Subgroup.normalClosure (Set.range fun y : Y => y⁻¹ * β y) with hJ
  have hJk : J ≤ k := Subgroup.normalClosure_le_normal (by rintro _ ⟨y, rfl⟩; exact hdk y)
  have hYJU : ∀ y : Y, ∃ j ∈ J, ∃ u ∈ U, y = j * u := by
    have hπJ : J.map π = ⊤ := by
      have hn : (J.map π).Normal := Subgroup.Normal.map inferInstance π hπ
      rcases hn.eq_bot_or_eq_top with h | h
      · exfalso
        obtain ⟨y, hy⟩ := hβ
        apply hy
        rw [← hker, MonoidHom.mem_ker]
        have : π (y⁻¹ * β y) ∈ J.map π :=
          Subgroup.mem_map_of_mem π (Subgroup.subset_normalClosure ⟨y, rfl⟩)
        rw [h, Subgroup.mem_bot] at this
        exact this
      · exact h
    intro y
    have : π y ∈ J.map π := by rw [hπJ]; trivial
    obtain ⟨j, hj, hjy⟩ := this
    refine ⟨j, hj, j⁻¹ * y, ?_, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hjy, inv_mul_cancel]
  have hktop : k = ⊤ := by
    haveI := hkn
    have hsolv : Group.IsSolvable (Y ⧸ k) := by
      refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' k).comp U.subtype) ?_
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective k z
      obtain ⟨j, hj, u, hu, rfl⟩ := hYJU y
      refine ⟨⟨u, hu⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      show (u⁻¹ * (j * u)) ∈ k
      have h2 : u⁻¹ * (j * u) = u⁻¹ * j * u⁻¹⁻¹ := by group
      rw [h2]
      exact hkn.conj_mem j (hJk hj) u⁻¹
    haveI : Group.IsPerfect (Y ⧸ k) := inferInstance
    by_contra hne
    haveI : Nontrivial (Y ⧸ k) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (Y ⧸ k) hsolv
  intro y u hu
  have h := (hkmem y).1 (by rw [hktop]; trivial) u hu
  rw [← QuotientGroup.eq_one_iff]
  simp only [hq, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h ⊢
  rw [h]
  group

theorem odd_card_of_perfect_cover {Y : Type} [Group Y] [Finite Y] (hYp : Group.IsPerfect Y)
    (U : Subgroup Y) [U.Normal] (hUs : Group.IsSolvable U) {W : Type} [Group W]
    (hWs : IsSimpleGroup W) (hND : CFSG.Monster.Schur.NoPerfectDoubleCover W)
    (π : Y →* W) (hπ : Function.Surjective π) (hker : π.ker = U)
    (β : MulAut Y) (hβU : ∀ u, u ∈ U ↔ β u ∈ U) (hβ : ∃ y : Y, y⁻¹ * β y ∉ U)
    (R : Subgroup Y) (hRU : R ≤ U) (hRn : ∀ u ∈ U, ∀ r ∈ R, u * r * u⁻¹ ∈ R)
    (hRodd : Odd (Nat.card R)) (hR : ∀ u ∈ U, u⁻¹ * β u ∈ R) :
    Odd (Nat.card U) := by
  classical
  haveI : Finite W := Finite.of_surjective π hπ
  obtain ⟨O, hOn, hOodd, hRO, hOYn, hβOY⟩ := exists_oddCore U hUs β hβU R hRU hRn hRodd
  haveI : O.Normal := hOn
  set OY : Subgroup Y := O.map U.subtype with hOY
  haveI : OY.Normal := hOYn
  have hOYU : OY ≤ U := by rintro _ ⟨o, -, rfl⟩; exact o.2
  have hROY : ∀ r ∈ R, r ∈ OY := fun r hr =>
    ⟨⟨r, hRU hr⟩, hRO ((Subgroup.mem_subgroupOf).2 hr), rfl⟩
  have hfix : ∀ u ∈ U, u⁻¹ * β u ∈ OY := fun u hu => hROY _ (hR u hu)
  have hcent := centralizes_mod_oddCore hYp U hUs hWs π hπ hker β hβ OY hOYU hβOY hfix
  by_contra hodd
  have h2 : 2 ∣ Nat.card U := by
    rcases Nat.even_or_odd (Nat.card U) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  have hab : ∀ a b : U ⧸ O, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have h := hcent (b : Y)⁻¹ (a : Y)⁻¹ (U.inv_mem a.2)
        obtain ⟨o, ho, hoe⟩ := h
        have hoe' : (o : Y) = (b : Y)⁻¹ * (a : Y)⁻¹ * (b : Y)⁻¹⁻¹ * (a : Y)⁻¹⁻¹ := hoe
        have : o = (a * b)⁻¹ * (b * a) := by
          apply Subtype.ext
          rw [hoe']
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
          group
        rw [← this]
        exact ho
  have hindex : Nat.card O * O.index = Nat.card U := Subgroup.card_mul_index O
  have h2idx : 2 ∣ Nat.card (U ⧸ O) := by
    have h2' : 2 ∣ Nat.card O * O.index := by rw [hindex]; exact h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2' with h | h
    · exact absurd h hOodd.not_two_dvd_nat
    · exact h
  obtain ⟨M, hM⟩ := CFSG.ComponentClassification.RankTwoSporadic.Co1.exists_index_two hab h2idx
  set H₀ : Subgroup U := M.comap (QuotientGroup.mk' O) with hH₀
  have hH₀idx : H₀.index = 2 := by
    rw [hH₀, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective O), hM]
  have hOH₀ : O ≤ H₀ := by
    intro o ho
    show (o : U ⧸ O) ∈ M
    rw [(QuotientGroup.eq_one_iff o).2 ho]
    exact M.one_mem
  set H : Subgroup Y := H₀.map U.subtype with hH
  have hHU : H ≤ U := by rintro _ ⟨o, -, rfl⟩; exact o.2
  have hOYH : OY ≤ H := Subgroup.map_mono hOH₀
  have hHn : H.Normal := by
    refine ⟨fun h hh y => ?_⟩
    have hhU : h ∈ U := hHU hh
    have h1 : y * h * y⁻¹ * h⁻¹ ∈ H := hOYH (hcent y h hhU)
    have : y * h * y⁻¹ = (y * h * y⁻¹ * h⁻¹) * h := by group
    rw [this]
    exact H.mul_mem h1 hh
  let πE : Y ⧸ H →* W := QuotientGroup.lift H π (by rw [hker]; exact hHU)
  have hsurj : Function.Surjective πE := by
    intro w
    obtain ⟨y, rfl⟩ := hπ w
    exact ⟨(y : Y ⧸ H), rfl⟩
  haveI : Group.IsPerfect (Y ⧸ H) := by haveI := hYp; infer_instance
  have hcardker : Nat.card πE.ker = 2 := by
    have e1 : Nat.card (Y ⧸ H) = Nat.card W * Nat.card πE.ker := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup πE.ker
      rw [this, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πE hsurj).toEquiv]
    have e2 : Nat.card Y = Nat.card (Y ⧸ H) * Nat.card H :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup H
    have e3 : Nat.card Y = Nat.card W * Nat.card U := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup U
      rw [this, ← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
    have e4 : Nat.card U = Nat.card H₀ * 2 := by
      rw [← hH₀idx]
      exact (Subgroup.card_mul_index H₀).symm
    have e5 : Nat.card H = Nat.card H₀ :=
      Subgroup.card_map_of_injective U.subtype_injective
    have hW0 : 0 < Nat.card W := Nat.card_pos
    have hH0 : 0 < Nat.card H := Nat.card_pos
    have : Nat.card W * Nat.card H * Nat.card πE.ker = Nat.card W * Nat.card H * 2 := by
      calc Nat.card W * Nat.card H * Nat.card πE.ker
          = (Nat.card W * Nat.card πE.ker) * Nat.card H := by ring
        _ = Nat.card Y := by rw [← e1, e2]
        _ = Nat.card W * Nat.card U := e3
        _ = Nat.card W * Nat.card H * 2 := by rw [e4, ← e5]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hW0 hH0) this
  exact hND (Y ⧸ H) πE hsurj inferInstance hcardker

end CFSG.RankThree.PartTwo.Sec12.Hering129SP
