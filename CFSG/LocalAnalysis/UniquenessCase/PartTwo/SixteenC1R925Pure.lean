module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Defs
import TauCeti.Algebra.Group.Subgroup.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma r925_natCard_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private lemma r925_natCard_quot_eq_sixty {Y : Type} [Group Y] {Z : Subgroup Y} [Z.Normal]
    (e : Y ⧸ Z ≃* alternatingGroup (Fin 5)) : Nat.card (Y ⧸ Z) = 60 := by
  rw [Nat.card_congr e.toEquiv, r925_natCard_alt_five]

theorem IsPerfA5Cover.exists_card_three {Y : Type} [Group Y] [Finite Y] (h : IsPerfA5Cover Y) :
    ∃ D : Subgroup Y, Nat.card D = 3 := by
  obtain ⟨-, Z, hZn, hZ2, ⟨e⟩⟩ := h
  haveI := hZn
  have hcard : Nat.card Y = Nat.card (Y ⧸ Z) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have h3 : 3 ∣ Nat.card Y := by
    rw [hcard, r925_natCard_quot_eq_sixty e]
    exact ⟨20 * Nat.card Z, by ring⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨Subgroup.zpowers x, by rw [Nat.card_zpowers, hx]⟩

theorem IsPerfA5Cover.exists_subgroup_card_three {Γ : Type} [Group Γ] [Finite Γ]
    {Y : Subgroup Γ} (h : IsPerfA5Cover ↥Y) : ∃ D : Subgroup Γ, D ≤ Y ∧ Nat.card D = 3 := by
  obtain ⟨D, hD⟩ := h.exists_card_three
  exact ⟨D.map Y.subtype, Subgroup.map_subtype_le D, by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]; exact hD⟩

theorem IsPerfA5Cover.closure_orderOf_three {Y : Type} [Group Y] [Finite Y]
    (h : IsPerfA5Cover Y) : Subgroup.closure {y : Y | orderOf y = 3} = ⊤ := by
  obtain ⟨hperf, Z, hZn, hZ2, ⟨e⟩⟩ := h
  haveI := hZn
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (Y ⧸ Z) := e.isSimpleGroup
  let S : Set Y := {y : Y | orderOf y = 3}
  let O : Subgroup Y := Subgroup.closure S
  have hOnorm : O.Normal :=
    Subgroup.closure_normal_of_forall_conj_mem fun g y hy => by
      show orderOf (g * y * g⁻¹) = 3
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hy
  haveI : O.Normal := hOnorm
  haveI hI : (O.map (QuotientGroup.mk' Z)).Normal :=
    hOnorm.map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hne : O.map (QuotientGroup.mk' Z) ≠ ⊥ := by
    intro hbot
    have h3dvd : 3 ∣ Nat.card Y := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, r925_natCard_quot_eq_sixty e]
      exact ⟨20 * Nat.card Z, by ring⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
    have hxS : x ∈ S := hx
    have hxO : x ∈ O := Subgroup.subset_closure hxS
    have hmem : QuotientGroup.mk' Z x ∈ O.map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map_of_mem _ hxO
    rw [hbot] at hmem
    have hone : QuotientGroup.mk' Z x = 1 := Subgroup.mem_bot.mp hmem
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp hone
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hne1 : (⟨x, hxZ⟩ : Z) ≠ 1 := by
      intro h1
      have h1' : orderOf (⟨x, hxZ⟩ : Z) = 1 := by rw [h1, orderOf_one]
      rw [Subgroup.orderOf_mk, hx] at h1'
      omega
    have h23 : (2 : ℕ) ∣ 3 := by
      have hd := hZ2.dvd_orderOf hne1
      rwa [Subgroup.orderOf_mk, hx] at hd
    omega
  have htop : O.map (QuotientGroup.mk' Z) = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (O.map (QuotientGroup.mk' Z)) with hbot | htop
    · exact absurd hbot hne
    · exact htop
  have hsup : O ⊔ Z = ⊤ := by
    apply le_antisymm le_top
    intro y _
    have hy : QuotientGroup.mk' Z y ∈ O.map (QuotientGroup.mk' Z) := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨o, hoO, hoo⟩ := Subgroup.mem_map.mp hy
    have hzy : o⁻¹ * y ∈ Z := by
      have h1 : QuotientGroup.mk' Z (o⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hoo, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    rw [show y = o * (o⁻¹ * y) by group]
    exact mul_mem (Subgroup.mem_sup_left hoO) (Subgroup.mem_sup_right hzy)
  have h2group : IsPGroup 2 (Y ⧸ O) := by
    have hsurj : Function.Surjective ((QuotientGroup.mk' O).comp Z.subtype) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O q
      have hy : y ∈ O ⊔ Z := by rw [hsup]; exact Subgroup.mem_top _
      obtain ⟨o, hoO, z, hzZ, hoz⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      refine ⟨⟨z, hzZ⟩, ?_⟩
      have hzy : o⁻¹ * y = z := by rw [← hoz]; group
      change QuotientGroup.mk' O z = QuotientGroup.mk' O y
      rw [← hzy, map_mul, map_inv]
      have ho : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr hoO
      rw [ho, inv_one, one_mul]
    exact hZ2.of_surjective ((QuotientGroup.mk' O).comp Z.subtype) hsurj
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hperf
  haveI : Group.IsPerfect (Y ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent (Y ⧸ O) := h2group.isNilpotent
  have hsub : Subsingleton (Y ⧸ O) := by
    by_contra hns
    haveI : Nontrivial (Y ⧸ O) := not_subsingleton_iff_nontrivial.mp hns
    exact (Group.IsPerfect.not_isNilpotent (Y ⧸ O)) hnil
  apply le_antisymm le_top
  intro y _
  have hy1 : QuotientGroup.mk' O y = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff y).mp hy1

theorem IsPerfA5Cover.isThreeGen {Γ : Type} [Group Γ] [Finite Γ] {Y : Subgroup Γ}
    (h : IsPerfA5Cover ↥Y) : IsThreeGen Y := by
  let S : Set ↥Y := {y | orderOf y = 3}
  let T : Set Γ := {a | a ∈ Y ∧ ∃ k : ℕ, a ^ 3 ^ k = 1}
  have hS : Subgroup.closure S = ⊤ := h.closure_orderOf_three
  have hmapTop : Subgroup.map Y.subtype (⊤ : Subgroup ↥Y) = Y := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hYeq : Y = Subgroup.closure (Y.subtype '' S) := by
    calc Y = Subgroup.map Y.subtype (⊤ : Subgroup ↥Y) := hmapTop.symm
      _ = Subgroup.map Y.subtype (Subgroup.closure S) := by rw [hS]
      _ = Subgroup.closure (Y.subtype '' S) := MonoidHom.map_closure Y.subtype S
  have himage : (Y.subtype '' S) ⊆ T := by
    rintro a ⟨y, hy, rfl⟩
    refine ⟨y.2, ⟨1, ?_⟩⟩
    have h3 : (y : Γ) ^ 3 = 1 := by
      have : orderOf (y : Γ) = 3 := by rw [Subgroup.orderOf_coe, hy]
      rw [← this, pow_orderOf_eq_one]
    simpa using h3
  have hclT : Subgroup.closure T ≤ Y := by
    rw [Subgroup.closure_le]
    exact fun a ha => ha.1
  have hYle : Y ≤ Subgroup.closure T := by
    rw [hYeq]
    exact Subgroup.closure_mono himage
  exact le_antisymm hclT hYle

theorem IsPerfA5Cover.map {Y Y' : Type} [Group Y] [Group Y'] (h : IsPerfA5Cover Y) (f : Y →* Y')
    (hf : Function.Surjective f) (hker : ∀ y ∈ f.ker, ¬ 3 ∣ orderOf y) : IsPerfA5Cover Y' := by
  obtain ⟨hperf, Z, hZn, hZ2, ⟨e⟩⟩ := h
  haveI := hZn
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (Y ⧸ Z) := e.isSimpleGroup
  haveI : Finite (Y ⧸ Z) := Finite.of_injective e.toEquiv e.toEquiv.injective
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hperf
  have hperfY' : Group.IsPerfect Y' := Group.IsPerfect.ofSurjective (f := f) hf
  have hkerZ : f.ker ≤ Z := by
    haveI hI : (f.ker.map (QuotientGroup.mk' Z)).Normal :=
      (MonoidHom.normal_ker f).map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    have hIne : f.ker.map (QuotientGroup.mk' Z) ≠ ⊤ := by
      intro hItop
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h3dvd : 3 ∣ Nat.card (Y ⧸ Z) := by
        rw [r925_natCard_quot_eq_sixty e]; norm_num
      obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
      have haI : a ∈ f.ker.map (QuotientGroup.mk' Z) := by
        rw [hItop]; exact Subgroup.mem_top _
      obtain ⟨k, hkker, hka⟩ := Subgroup.mem_map.mp haI
      have h3k : 3 ∣ orderOf k := by
        have hd := orderOf_map_dvd (QuotientGroup.mk' Z) k
        rwa [hka, ha] at hd
      exact hker k hkker h3k
    have hIbot : f.ker.map (QuotientGroup.mk' Z) = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (f.ker.map (QuotientGroup.mk' Z)) with hbot | htop
      · exact hbot
      · exact absurd htop hIne
    intro y hy
    have hyI : QuotientGroup.mk' Z y ∈ f.ker.map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map_of_mem _ hy
    rw [hIbot, Subgroup.mem_bot] at hyI
    exact (QuotientGroup.eq_one_iff y).mp hyI
  have hZ'n : (Z.map f).Normal := hZn.map f hf
  haveI : (Z.map f).Normal := hZ'n
  have hZ'2 : IsPGroup 2 (Z.map f) := hZ2.map f
  have hbij : Function.Bijective (QuotientGroup.map Z (Z.map f) f (Subgroup.le_comap_map f Z)) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z x
      rw [MonoidHom.mem_ker, QuotientGroup.map_mk'] at hx
      have hfy : f y ∈ Z.map f := (QuotientGroup.eq_one_iff (f y)).mp hx
      obtain ⟨z, hzZ, hfz⟩ := Subgroup.mem_map.mp hfy
      have hyz : y * z⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfz, mul_inv_cancel]
      have hyZ : y * z⁻¹ ∈ Z := hkerZ hyz
      have hy : y ∈ Z := by
        have h1 : y = (y * z⁻¹) * z := by group
        rw [h1]
        exact mul_mem hyZ hzZ
      exact (QuotientGroup.eq_one_iff y).mpr hy
    · intro q
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Z.map f) q
      obtain ⟨y, rfl⟩ := hf y'
      exact ⟨QuotientGroup.mk' Z y, by rw [QuotientGroup.map_mk']; rfl⟩
  refine ⟨Group.isPerfect_def.mp hperfY', Z.map f, hZ'n, hZ'2, ?_⟩
  exact ⟨(MulEquiv.ofBijective
    (QuotientGroup.map Z (Z.map f) f (Subgroup.le_comap_map f Z)) hbij).symm.trans e⟩

theorem IsPerfA5Cover.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (h : IsPerfA5Cover Y)
    (e : Y ≃* Y') : IsPerfA5Cover Y' :=
  h.map e.toMonoidHom e.surjective fun y hy => by
    have h1 : y = 1 := by simpa using MonoidHom.mem_ker.mp hy
    subst h1
    simp

theorem IsPerfA5Cover.eq_bot_of_odd {Y : Type} [Group Y] [Finite Y] (h : IsPerfA5Cover Y)
    (N : Subgroup Y) [N.Normal] (hN : ∀ x ∈ N, Odd (orderOf x)) : N = ⊥ := by
  obtain ⟨-, Z, hZn, hZ2, ⟨e⟩⟩ := h
  haveI := hZn
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (Y ⧸ Z) := e.isSimpleGroup
  haveI hNm : (N.map (QuotientGroup.mk' Z)).Normal :=
    (inferInstance : N.Normal).map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hNne : N.map (QuotientGroup.mk' Z) ≠ ⊤ := by
    intro hNtop
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2dvd : 2 ∣ Nat.card (Y ⧸ Z) := by
      rw [r925_natCard_quot_eq_sixty e]; norm_num
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have haN : a ∈ N.map (QuotientGroup.mk' Z) := by
      rw [hNtop]; exact Subgroup.mem_top _
    obtain ⟨x, hxN, hxa⟩ := Subgroup.mem_map.mp haN
    have h2x : 2 ∣ orderOf x := by
      have hd := orderOf_map_dvd (QuotientGroup.mk' Z) x
      rwa [hxa, ha] at hd
    obtain ⟨c, hc⟩ := h2x
    obtain ⟨d, hd⟩ := hN x hxN
    omega
  have hNbot : N.map (QuotientGroup.mk' Z) = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (N.map (QuotientGroup.mk' Z)) with hbot | htop
    · exact hbot
    · exact absurd htop hNne
  have hNZ : N ≤ Z := by
    intro x hx
    have hxI : QuotientGroup.mk' Z x ∈ N.map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hNbot, Subgroup.mem_bot] at hxI
    exact (QuotientGroup.eq_one_iff x).mp hxI
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [← orderOf_eq_one_iff]
  have hxZ : x ∈ Z := hNZ hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hZ2.exists_orderOf_eq_pow (⟨x, hxZ⟩ : Z)
  have hkx : orderOf x = 2 ^ k := by
    rw [← Subgroup.orderOf_mk x hxZ]
    exact hk
  have hodd : Odd (2 ^ k) := by rw [← hkx]; exact hN x hx
  have hk0 : k = 0 := by
    by_contra hkne
    have heven : Even (2 ^ k) := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
      rw [pow_succ]
      exact ⟨2 ^ j, by ring⟩
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  rw [hkx, hk0, pow_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
