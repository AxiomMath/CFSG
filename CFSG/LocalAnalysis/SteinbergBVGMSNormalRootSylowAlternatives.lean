module

public import CFSG.LocalAnalysis.SteinbergBVGMSNormalRootFamily

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup CFSG CFSG.LocalAnalysis
open scoped Pointwise

section Cover

theorem card_le_two_mul_of_cover {G : Type*} [Group G] [Finite G] {T S : Subgroup G} (a : G)
    (h : ∀ t ∈ T, t ∈ S ∨ a⁻¹ * t ∈ S) : Nat.card T ≤ 2 * Nat.card S := by
  have hsub : (T : Set G) ⊆ (S : Set G) ∪ (fun s => a * s) '' (S : Set G) := by
    intro t ht
    rcases h t ht with hs | hs
    · exact Or.inl hs
    · exact Or.inr ⟨a⁻¹ * t, hs, by group⟩
  calc Nat.card T = (T : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ((S : Set G) ∪ (fun s => a * s) '' (S : Set G)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (S : Set G).ncard + ((fun s => a * s) '' (S : Set G)).ncard := Set.ncard_union_le _ _
    _ = 2 * Nat.card S := by
      rw [Set.ncard_image_of_injective _ (mul_right_injective a), ← two_mul]
      exact congrArg (2 * ·) (Nat.card_coe_set_eq (S : Set G)).symm

theorem pRank_two_le_two_of_cover {G : Type*} [Group G] [Finite G] (C : Subgroup G) [IsCyclic C]
    (a : G) (h : ∀ x : G, x ∈ C ∨ a⁻¹ * x ∈ C) : CFSG.pRank 2 G ≤ 2 := by
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have hAC : Nat.card ↥(A ⊓ C) ≤ 2 := by
    have : IsCyclic ↥(A ⊓ C) := Subgroup.isCyclic_of_le inf_le_right
    have hexp : Monoid.exponent ↥(A ⊓ C) ∣ 2 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      apply Subtype.ext
      have := hA
      simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) (mem_inf.1 x.2).1
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd two_pos hexp
  have hA2 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ C) := by
    by_cases hAC' : ∀ x ∈ A, x ∈ C
    · rw [inf_of_le_left hAC']
      omega
    · push Not at hAC'
      obtain ⟨b, hbA, hbC⟩ := hAC'
      apply card_le_two_mul_of_cover b
      intro t ht
      rcases h t with htC | htC
      · exact Or.inl (mem_inf.2 ⟨ht, htC⟩)
      · right
        have hb : a⁻¹ * b ∈ C := (h b).resolve_left hbC
        refine mem_inf.2 ⟨mul_mem (inv_mem hbA) ht, ?_⟩
        have e : b⁻¹ * t = (a⁻¹ * b)⁻¹ * (a⁻¹ * t) := by group
        rw [e]
        exact mul_mem (inv_mem hb) htC
  have h4 : 2 ^ r ≤ 2 ^ 2 := by rw [← hcard]; omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4

end Cover

variable {D : Type*} [Group D]

section Fixed

theorem card_sup_inf_centralizer_le_mul [Finite D] {U R : Subgroup D} {x : D}
    (hRU : R ≤ centralizer (U : Set D)) (hdisj : U ⊓ R = ⊥) (hxU : x ∈ normalizer (U : Set D))
    (hxR : x ∈ normalizer (R : Set D)) :
    Nat.card ↥((U ⊔ R) ⊓ centralizer {x}) ≤
      Nat.card ↥(U ⊓ centralizer {x}) * Nat.card ↥(R ⊓ centralizer {x}) := by
  let g : ↥(U ⊓ centralizer {x}) × ↥(R ⊓ centralizer {x}) → D := fun p => (p.1 : D) * p.2
  have hsub : (((U ⊔ R) ⊓ centralizer {x} : Subgroup D) : Set D) ⊆ Set.range g := by
    intro v hv
    obtain ⟨hvV, hvC⟩ := mem_inf.1 hv
    obtain ⟨a, ha, b, hb, rfl⟩ := SteinbergBT.exists_mul_eq_of_mem_sup hRU hvV
    have hc : a * b * x = x * (a * b) := mem_centralizer_singleton_iff.1 hvC
    have ha' : x * a * x⁻¹ ∈ U := (mem_normalizer_iff.1 hxU a).1 ha
    have hb' : x * b * x⁻¹ ∈ R := (mem_normalizer_iff.1 hxR b).1 hb
    have hprod : (x * a * x⁻¹) * (x * b * x⁻¹) = a * b := by
      calc (x * a * x⁻¹) * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
        _ = a * b := by rw [← hc]; group
    have hmem : a⁻¹ * (x * a * x⁻¹) ∈ U ⊓ R := by
      refine mem_inf.2 ⟨mul_mem (inv_mem ha) ha', ?_⟩
      have e : a⁻¹ * (x * a * x⁻¹) = b * (x * b * x⁻¹)⁻¹ := by
        calc a⁻¹ * (x * a * x⁻¹)
            = a⁻¹ * ((x * a * x⁻¹) * (x * b * x⁻¹)) * (x * b * x⁻¹)⁻¹ := by group
          _ = a⁻¹ * (a * b) * (x * b * x⁻¹)⁻¹ := by rw [hprod]
          _ = b * (x * b * x⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem hb (inv_mem hb')
    rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
    have hbx : b = x * b * x⁻¹ := by
      have h1 := hprod
      rw [← hmem] at h1
      exact (mul_left_cancel h1).symm
    have haC : a ∈ U ⊓ centralizer {x} := by
      refine mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 ?_⟩
      calc a * x = (x * a * x⁻¹) * x := by rw [← hmem]
        _ = x * a := by group
    have hbC : b ∈ R ⊓ centralizer {x} := by
      refine mem_inf.2 ⟨hb, mem_centralizer_singleton_iff.2 ?_⟩
      calc b * x = (x * b * x⁻¹) * x := by rw [← hbx]
        _ = x * b := by group
    exact ⟨(⟨a, haC⟩, ⟨b, hbC⟩), rfl⟩
  calc Nat.card ↥((U ⊔ R) ⊓ centralizer {x})
      = (((U ⊔ R) ⊓ centralizer {x} : Subgroup D) : Set D).ncard := Nat.card_coe_set_eq _
    _ ≤ (Set.range g).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (Set.range g) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (↥(U ⊓ centralizer {x}) × ↥(R ⊓ centralizer {x})) :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := g))
    _ = Nat.card ↥(U ⊓ centralizer {x}) * Nat.card ↥(R ⊓ centralizer {x}) := Nat.card_prod _ _

theorem card_sup_inf_centralizer_le_of_swap [Finite D] {U R : Subgroup D} {x : D}
    (hRU : R ≤ centralizer (U : Set D)) (hdisj : U ⊓ R = ⊥)
    (hxU : U.map (MulAut.conj x).toMonoidHom = R) (hxR : R.map (MulAut.conj x).toMonoidHom = U) :
    Nat.card ↥((U ⊔ R) ⊓ centralizer {x}) ≤ Nat.card U := by
  let g : U → D := fun a => (a : D) * (x * a * x⁻¹)
  have hsub : (((U ⊔ R) ⊓ centralizer {x} : Subgroup D) : Set D) ⊆ Set.range g := by
    intro v hv
    obtain ⟨hvV, hvC⟩ := mem_inf.1 hv
    obtain ⟨a, ha, b, hb, rfl⟩ := SteinbergBT.exists_mul_eq_of_mem_sup hRU hvV
    have hc : a * b * x = x * (a * b) := mem_centralizer_singleton_iff.1 hvC
    have ha' : x * a * x⁻¹ ∈ R := by
      rw [← hxU]
      exact ⟨a, ha, rfl⟩
    have hb' : x * b * x⁻¹ ∈ U := by
      rw [← hxR]
      exact ⟨b, hb, rfl⟩
    have hprod : (x * b * x⁻¹) * (x * a * x⁻¹) = a * b := by
      calc (x * b * x⁻¹) * (x * a * x⁻¹) = (x * a * x⁻¹) * (x * b * x⁻¹) :=
            mem_centralizer_iff.1 (hRU ha') _ hb'
        _ = x * (a * b) * x⁻¹ := by group
        _ = a * b := by rw [← hc]; group
    have hmem : a⁻¹ * (x * b * x⁻¹) ∈ U ⊓ R := by
      refine mem_inf.2 ⟨mul_mem (inv_mem ha) hb', ?_⟩
      have e : a⁻¹ * (x * b * x⁻¹) = b * (x * a * x⁻¹)⁻¹ := by
        calc a⁻¹ * (x * b * x⁻¹)
            = a⁻¹ * ((x * b * x⁻¹) * (x * a * x⁻¹)) * (x * a * x⁻¹)⁻¹ := by group
          _ = a⁻¹ * (a * b) * (x * a * x⁻¹)⁻¹ := by rw [hprod]
          _ = b * (x * a * x⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem hb (inv_mem ha')
    rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
    have hb2 : b = x * a * x⁻¹ := by
      have h1 := hprod
      rw [← hmem] at h1
      exact (mul_left_cancel h1).symm
    refine ⟨⟨a, ha⟩, ?_⟩
    change a * (x * a * x⁻¹) = a * b
    rw [← hb2]
  calc Nat.card ↥((U ⊔ R) ⊓ centralizer {x})
      = (((U ⊔ R) ⊓ centralizer {x} : Subgroup D) : Set D).ncard := Nat.card_coe_set_eq _
    _ ≤ (Set.range g).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (Set.range g) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card U := Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := g))

theorem pRank_le_of_le_of_card_le [Finite D] {E F : Subgroup D} (hE : IsElementaryAbelian 2 E)
    (hFE : F ≤ E) {k : ℕ} (hk : Nat.card F ≤ 2 ^ k) : CFSG.pRank 2 F ≤ k := by
  have hEo : CFSG.Open.IsElemAbelian 2 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).1 hE
  have hFo : CFSG.Open.IsElemAbelian 2 F :=
    ⟨⟨⟨fun a b => Subtype.ext (show (a : D) * b = b * a from congrArg Subtype.val
      (hEo.1.is_comm.comm ⟨a, hFE a.2⟩ ⟨b, hFE b.2⟩))⟩⟩, fun y hy => hEo.2 y (hFE hy)⟩
  have := hE
  obtain ⟨c, hc⟩ := ((IsElementaryAbelian.isPGroup 2 E).to_le hFE : IsPGroup 2 F).exists_card_eq
  rw [CFSG.LocalAnalysis.GorensteinLyons.pRank_eq_of_elementary one_lt_two hFo hc]
  rw [hc] at hk
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hk

end Fixed

section Roots

variable {J R X U P : Subgroup D} {n : ℕ}

theorem gms_normalizer_P_le [Finite D] (h : GMSNormalRootData J R X U P n) :
    normalizer (P : Set D) ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) := by
  have hweak := (SteinbergBT.gms_normal_root_singer_action_and_weak_closure h).2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, ⟨-, -, hUP, hRP, -⟩⟩ := h
  intro g hg
  have hle : CFSG.conjugate (U ⊔ R) g ≤ P := by
    rw [CFSG.conjugate]
    calc (U ⊔ R).map (MulAut.conj g⁻¹).toMonoidHom ≤ P.map (MulAut.conj g⁻¹).toMonoidHom :=
          (map_conj_le_map_conj_iff _).2 (sup_le hUP hRP)
      _ = P := map_conj_eq_self_iff.2 (inv_mem hg)
  have h1 := hweak g hle
  rw [CFSG.conjugate, map_conj_eq_self_iff] at h1
  simpa using inv_mem h1

theorem gms_fix_or_swap [Finite D] (h : GMSNormalRootData J R X U P n)
    (hΔ : gmsRootConjugates (U ⊔ R) R = {R, U}) (hUR : U ≠ R) {l : D}
    (hl : l ∈ normalizer ((U ⊔ R : Subgroup D) : Set D)) :
    (U.map (MulAut.conj l).toMonoidHom = U ∧ R.map (MulAut.conj l).toMonoidHom = R) ∨
      (U.map (MulAut.conj l).toMonoidHom = R ∧ R.map (MulAut.conj l).toMonoidHom = U) := by
  have hUΔ : U ∈ gmsRootConjugates (U ⊔ R) R := by
    rw [hΔ]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hR' := map_conj_mem_gmsRootConjugates gms_R_mem hl
  have hU' := map_conj_mem_gmsRootConjugates hUΔ hl
  rw [hΔ] at hR' hU'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR' hU'
  rcases hR' with hR' | hR'
  · left
    exact ⟨map_conj_eq_self_iff.2 (gms_LR_normalizes h hl (map_conj_eq_self_iff.1 hR')).2.1, hR'⟩
  · right
    refine ⟨?_, hR'⟩
    rcases hU' with hU' | hU'
    · exact hU'
    · exact absurd (Subgroup.map_injective (MulAut.conj l).injective (hU'.trans hR'.symm)) hUR

theorem gms_eq_U_of_normalized [Finite D] (h : GMSNormalRootData J R X U P n) {Z : Subgroup D}
    (hZV : Z ≤ U ⊔ R) (hZR : Z ⊓ R = ⊥) (hZ : Z ≠ ⊥)
    (hN : ∀ c ∈ X ⊓ normalizer (U : Set D), c ∈ normalizer (Z : Set D)) : Z = U := by
  have hRU := gms_R_le_centralizer_U h
  obtain ⟨hn3, -, -, ⟨-, -, hXC⟩, -, ⟨-, hqcard, hreg⟩, -⟩ := h
  have : Nontrivial (GMSNormalizerQuotient X U) := by
    apply Finite.one_lt_card_iff_nontrivial.1
    rw [hqcard]
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    norm_num at h8
    omega
  obtain ⟨cq, hcq⟩ := exists_ne (1 : GMSNormalizerQuotient X U)
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cq
  have hfix : ∀ u ∈ U, u ≠ 1 → (c : D) * u * (c : D)⁻¹ ≠ u := by
    intro u hu hu1 heq
    have hu1' : (⟨u, hu⟩ : U) ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
    obtain ⟨d, -, hd⟩ := hreg ⟨u, hu⟩ ⟨u, hu⟩ hu1' hu1'
    exact hcq ((hd (QuotientGroup.mk c) (Subtype.ext heq)).trans
      (hd 1 (show gmsQuotConjAct X U 1 ⟨u, hu⟩ = ⟨u, hu⟩ by
        rw [map_one, MulAut.one_apply])).symm)
  have hcN : (c : D) ∈ normalizer (Z : Set D) := hN c c.2
  have hcR : (c : D) ∈ centralizer (R : Set D) := hXC (mem_inf.1 c.2).1
  have hcU : (c : D) ∈ normalizer (U : Set D) := (mem_inf.1 c.2).2
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  obtain ⟨a, ha, b, hb, rfl⟩ := SteinbergBT.exists_mul_eq_of_mem_sup hRU (hZV hz)
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at hz hz1'
    have hbZR : b ∈ Z ⊓ R := mem_inf.2 ⟨hz, hb⟩
    rw [hZR, mem_bot] at hbZR
    exact hz1' hbZR
  have hwU : (c : D) * a * (c : D)⁻¹ * a⁻¹ ∈ U :=
    mul_mem ((mem_normalizer_iff.1 hcU a).1 ha) (inv_mem ha)
  have hwZ : (c : D) * a * (c : D)⁻¹ * a⁻¹ ∈ Z := by
    have hcz : (c : D) * (a * b) * (c : D)⁻¹ ∈ Z := (mem_normalizer_iff.1 hcN _).1 hz
    have hb' : (c : D) * b * (c : D)⁻¹ = b := by
      rw [← mem_centralizer_iff.1 hcR b hb, mul_inv_cancel_right]
    have e : (c : D) * (a * b) * (c : D)⁻¹ * (a * b)⁻¹ = (c : D) * a * (c : D)⁻¹ * a⁻¹ := by
      calc (c : D) * (a * b) * (c : D)⁻¹ * (a * b)⁻¹
          = (c : D) * a * (c : D)⁻¹ * ((c : D) * b * (c : D)⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = (c : D) * a * (c : D)⁻¹ * a⁻¹ := by rw [hb']; group
    rw [← e]
    exact mul_mem hcz (inv_mem hz)
  have hw1 : (c : D) * a * (c : D)⁻¹ * a⁻¹ ≠ 1 := fun h1 =>
    hfix a ha ha1 (mul_inv_eq_one.1 h1)
  have hUZ : U ≤ Z := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem Z
    have hw1' : (⟨_, hwU⟩ : U) ≠ 1 := fun h1 => hw1 (congrArg Subtype.val h1)
    have hu1' : (⟨u, hu⟩ : U) ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
    obtain ⟨dq, hdq, -⟩ := hreg ⟨_, hwU⟩ ⟨u, hu⟩ hw1' hu1'
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective dq
    have hdu : (d : D) * ((c : D) * a * (c : D)⁻¹ * a⁻¹) * (d : D)⁻¹ = u :=
      congrArg Subtype.val hdq
    rw [← hdu]
    exact (mem_normalizer_iff.1 (hN d d.2) _).1 hwZ
  refine le_antisymm (fun z' hz' => ?_) hUZ
  obtain ⟨a', ha', b', hb', rfl⟩ := SteinbergBT.exists_mul_eq_of_mem_sup hRU (hZV hz')
  have hb'Z : b' ∈ Z := by
    have e : b' = a'⁻¹ * (a' * b') := by group
    rw [e]
    exact mul_mem (inv_mem (hUZ ha')) hz'
  have hb'ZR : b' ∈ Z ⊓ R := mem_inf.2 ⟨hb'Z, hb'⟩
  rw [hZR, mem_bot] at hb'ZR
  rw [hb'ZR, mul_one]
  exact ha'

theorem gms_two_conjugates_interchange [Finite D] (h : GMSNormalRootData J R X U P n)
    (hsyl : ¬∃ T : Sylow 2 D, (T : Subgroup D) = P)
    (hΔ : (gmsRootConjugates (U ⊔ R) R).ncard ≤ 2) :
    gmsRootConjugates (U ⊔ R) R = {R, U} ∧ Nat.card R = 2 ^ n ∧ Nat.card U = 2 ^ n ∧
    (∃ P₁ : Subgroup D, (∃ T : Sylow 2 D, (T : Subgroup D) = P₁) ∧ P ≤ P₁ ∧
      Nat.card P₁ = 2 * Nat.card P ∧ (P.subgroupOf P₁).Normal ∧
      (∀ x ∈ P₁, (U.map (MulAut.conj x).toMonoidHom = U ∧
          R.map (MulAut.conj x).toMonoidHom = R) ∨
        (U.map (MulAut.conj x).toMonoidHom = R ∧ R.map (MulAut.conj x).toMonoidHom = U)) ∧
      (∃ y ∈ P₁, U.map (MulAut.conj y).toMonoidHom = R ∧
        R.map (MulAut.conj y).toMonoidHom = U) ∧
      IsStronglyClosedIn P₁ ((U ⊔ R : Subgroup D) : Set D) ∧
      IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D) ∧
      P ⊓ centralizer (U : Set D) = U ⊔ R ∧ P ⊓ centralizer (R : Set D) = U ⊔ R ∧
      P₁ ⊓ centralizer ((U ⊔ R : Subgroup D) : Set D) = U ⊔ R ∧
      ((U ⊔ R).subgroupOf P₁).Normal ∧
      (∀ [((U ⊔ R).subgroupOf P₁).Normal], CFSG.pRank 2 (P₁ ⧸ (U ⊔ R).subgroupOf P₁) ≤ 2) ∧
      3 ≤ n ∧ ∀ x ∈ P₁, x ∉ U ⊔ R →
        n + CFSG.pRank 2 ↥((U ⊔ R) ⊓ centralizer {x}) ≤ CFSG.pRank 2 ↥(U ⊔ R)) ∧
    (gmsRootConjugateAction (U ⊔ R) R).ker =
      (normalizer (R : Set D)).subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D)) ∧
    ((normalizer (R : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D))).index = 2 := by
  classical
  have h0 := h
  have hBT := SteinbergBT.gms_normal_root_singer_action_and_weak_closure h
  have hCPV := hBT.2.2.2.2.2.1
  have hRU := gms_R_le_centralizer_U h
  have hVel := gms_isElementaryAbelian_V h
  have hcommV := gms_comm_V h
  have hP2 := gms_isPGroup_P h
  have hRne := GMSNormalRootData.ne_bot h
  have hNPL := gms_normalizer_P_le h
  obtain ⟨K, _, _, _, hKcard, e, -, -, φ, hequiv, -, hker'⟩ := hBT.1
  obtain ⟨hn3, -, -, ⟨-, -, hXC⟩, ⟨-, -, -, hUcard⟩, -,
    ⟨hPN, ⟨TP, hTP⟩, hUP, hRP, hPNU, hUR, hCPU, hVn⟩⟩ := h
  have hVP : U ⊔ R ≤ P := sup_le hUP hRP
  have hcycP : IsCyclic (P ⧸ (U ⊔ R).subgroupOf P) := hBT.2.2.1.1
  have hUne : U ≠ R := by
    intro hUR'
    apply hRne
    rw [← hUR, hUR', inf_idem]
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
  have hkle : k ≤ (Nat.card D).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hD0, ← hk]
    exact Subgroup.card_subgroup_dvd_card P
  have hkne : k ≠ (Nat.card D).factorization 2 := by
    intro hkeq
    exact hsyl ⟨Sylow.ofCard P (by rw [hk, hkeq]), rfl⟩
  have hdvd : 2 ^ (k + 1) ∣ Nat.card D :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hD0).2 (by omega)
  obtain ⟨P₁, hP₁card, hPP₁⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hk
  have hP₁2 : IsPGroup 2 P₁ := IsPGroup.of_card hP₁card
  have hcard2 : Nat.card P₁ = 2 * Nat.card P := by
    rw [hP₁card, hk, pow_succ, mul_comm]
  have hPn : (P.subgroupOf P₁).Normal := by
    apply Subgroup.normal_of_index_eq_two
    have h1 := Subgroup.card_mul_index (P.subgroupOf P₁)
    rw [Nat.card_congr (subgroupOfEquivOfLe hPP₁).toEquiv, hcard2, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hP₁NP : P₁ ≤ normalizer (P : Set D) := (normal_subgroupOf_iff_le_normalizer hPP₁).1 hPn
  have hP₁L : P₁ ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) := hP₁NP.trans hNPL
  have hPlt : P < P₁ := lt_of_le_of_ne hPP₁ fun heq => by
    rw [heq] at hcard2
    have h1 : 0 < Nat.card P₁ := Nat.card_pos
    omega
  obtain ⟨y, hyP₁, hyP⟩ := IsConcreteLE.exists_of_lt hPlt
  have hP₁R : P₁ ⊓ normalizer (R : Set D) = P :=
    eq_of_sylow_le TP hTP hPN inf_le_right (le_inf hPP₁ hPN) (hP₁2.to_le inf_le_left)
  have hyR : y ∉ normalizer (R : Set D) := fun hy => hyP (by
    rw [← hP₁R]
    exact mem_inf.2 ⟨hyP₁, hy⟩)
  have hyL := hP₁L hyP₁
  have hZΔ : R.map (MulAut.conj y).toMonoidHom ∈ gmsRootConjugates (U ⊔ R) R :=
    map_conj_mem_gmsRootConjugates gms_R_mem hyL
  have hZR : R.map (MulAut.conj y).toMonoidHom ≠ R := fun h1 => hyR (map_conj_eq_self_iff.1 h1)
  have hΔ2 : gmsRootConjugates (U ⊔ R) R = {R, R.map (MulAut.conj y).toMonoidHom} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · intro S hS
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS
      rcases hS with rfl | rfl
      · exact gms_R_mem
      · exact hZΔ
    · rw [Set.ncard_pair hZR.symm]
      exact hΔ
    · exact Set.toFinite _
  have hZU : R.map (MulAut.conj y).toMonoidHom = U := by
    refine gms_eq_U_of_normalized h0 ?_ (gms_inf_eq_bot h0 hZΔ gms_R_mem hZR) ?_ ?_
    · obtain ⟨-, -, hle⟩ := hZΔ
      exact hle
    · intro hbot
      apply hRne
      have h1 := card_map_conj R y
      rw [hbot, Subgroup.card_bot] at h1
      exact Subgroup.eq_bot_of_card_eq R h1.symm
    · intro c hc
      have hcR : c ∈ normalizer (R : Set D) :=
        centralizer_le_normalizer _ (hXC (mem_inf.1 hc).1)
      have hcZ := map_conj_mem_gmsRootConjugates hZΔ (gms_NXU_le_L h0 hc)
      rw [hΔ2] at hcZ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcZ
      rcases hcZ with hcZ | hcZ
      · exact absurd (Subgroup.map_injective (MulAut.conj c).injective
          (hcZ.trans (map_conj_eq_self_iff.2 hcR).symm)) hZR
      · exact map_conj_eq_self_iff.1 hcZ
  have hΔeq : gmsRootConjugates (U ⊔ R) R = {R, U} := by rw [hΔ2, hZU]
  have hRcard : Nat.card R = 2 ^ n := by rw [← hUcard, ← hZU, card_map_conj]
  have hdich : ∀ l ∈ normalizer ((U ⊔ R : Subgroup D) : Set D),
      (U.map (MulAut.conj l).toMonoidHom = U ∧ R.map (MulAut.conj l).toMonoidHom = R) ∨
        (U.map (MulAut.conj l).toMonoidHom = R ∧ R.map (MulAut.conj l).toMonoidHom = U) :=
    fun l hl => gms_fix_or_swap h0 hΔeq hUne hl
  have hyswap : U.map (MulAut.conj y).toMonoidHom = R ∧
      R.map (MulAut.conj y).toMonoidHom = U := by
    rcases hdich y hyL with ⟨-, hy⟩ | hy
    · exact absurd hy hZR
    · exact hy
  have hP₁cover : ∀ x ∈ P₁, x ∉ P → U.map (MulAut.conj x).toMonoidHom = R ∧
      R.map (MulAut.conj x).toMonoidHom = U := by
    intro x hx hxP
    rcases hdich x (hP₁L hx) with ⟨-, hxR⟩ | hxs
    · refine absurd ?_ hxP
      rw [← hP₁R]
      exact mem_inf.2 ⟨hx, map_conj_eq_self_iff.1 hxR⟩
    · exact hxs
  have hyP_of : ∀ t ∈ P₁, t ∉ P → y⁻¹ * t ∈ P := by
    intro t ht htP
    obtain ⟨-, htR⟩ := hP₁cover t ht htP
    rw [← hP₁R]
    refine mem_inf.2 ⟨mul_mem (inv_mem hyP₁) ht, map_conj_eq_self_iff.1 ?_⟩
    rw [map_conj_mul, htR, ← hyswap.2, map_conj_inv_map_conj]
  have hP₁syl : ∃ T : Sylow 2 (normalizer ((U ⊔ R : Subgroup D) : Set D)),
      (T : Subgroup _) = P₁.subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D)) := by
    have hP₁2' : IsPGroup 2 (P₁.subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D))) :=
      hP₁2.of_equiv (subgroupOfEquivOfLe hP₁L).symm
    obtain ⟨T, hT⟩ := hP₁2'.exists_le_sylow
    refine ⟨T, ?_⟩
    have hT'L : (T : Subgroup _).map (normalizer ((U ⊔ R : Subgroup D) : Set D)).subtype ≤
        normalizer ((U ⊔ R : Subgroup D) : Set D) := by
      rintro _ ⟨t, -, rfl⟩
      exact t.2
    have hP₁T' : P₁ ≤ (T : Subgroup _).map (normalizer ((U ⊔ R : Subgroup D) : Set D)).subtype :=
      fun x hx => ⟨⟨x, hP₁L hx⟩, hT hx, rfl⟩
    have hT'2 : IsPGroup 2
        ((T : Subgroup _).map (normalizer ((U ⊔ R : Subgroup D) : Set D)).subtype) :=
      T.isPGroup'.map _
    have hT'R : (T : Subgroup _).map (normalizer ((U ⊔ R : Subgroup D) : Set D)).subtype ⊓
        normalizer (R : Set D) = P :=
      eq_of_sylow_le TP hTP hPN inf_le_right (le_inf (hPP₁.trans hP₁T') hPN)
        (hT'2.to_le inf_le_left)
    have hT'card : Nat.card ((T : Subgroup _).map
        (normalizer ((U ⊔ R : Subgroup D) : Set D)).subtype) ≤ Nat.card P₁ := by
      rw [hcard2]
      apply card_le_two_mul_of_cover y
      intro t ht
      rcases hdich t (hT'L ht) with ⟨-, htR⟩ | ⟨-, htR⟩
      · left
        rw [← hT'R]
        exact mem_inf.2 ⟨ht, map_conj_eq_self_iff.1 htR⟩
      · right
        rw [← hT'R]
        refine mem_inf.2 ⟨mul_mem (inv_mem (hP₁T' hyP₁)) ht, map_conj_eq_self_iff.1 ?_⟩
        rw [map_conj_mul, htR, ← hyswap.2, map_conj_inv_map_conj]
    have hT'eq := Subgroup.eq_of_le_of_card_ge hP₁T' hT'card
    rw [hT'eq]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm
  have hVP₁ : U ⊔ R ≤ P₁ := hVP.trans hPP₁
  have hVn₁ : ((U ⊔ R).subgroupOf P₁).Normal := (normal_subgroupOf_iff_le_normalizer hVP₁).2 hP₁L
  have hquot₁ : ∀ [((U ⊔ R).subgroupOf P₁).Normal],
      CFSG.pRank 2 (P₁ ⧸ (U ⊔ R).subgroupOf P₁) ≤ 2 := by
    intro _
    let f : P ⧸ (U ⊔ R).subgroupOf P →* P₁ ⧸ (U ⊔ R).subgroupOf P₁ :=
      QuotientGroup.map _ _ (Subgroup.inclusion hPP₁) (fun p hp => hp)
    have : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
    refine pRank_two_le_two_of_cover f.range (QuotientGroup.mk (⟨y, hyP₁⟩ : P₁)) fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H t =>
      by_cases ht : (t : D) ∈ P
      · exact Or.inl ⟨QuotientGroup.mk ⟨t, ht⟩, rfl⟩
      · exact Or.inr ⟨QuotientGroup.mk ⟨y⁻¹ * t, hyP_of t t.2 ht⟩, rfl⟩
  have hVcard : Nat.card ↥(U ⊔ R) = 2 ^ (n + n) := by
    rw [SteinbergBT.card_sup_of_centralizes hRU hUR, hUcard, hRcard, pow_add]
  have hVo : CFSG.Open.IsElemAbelian 2 (U ⊔ R) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).1 hVel
  have hrV : CFSG.pRank 2 ↥(U ⊔ R) = n + n :=
    CFSG.LocalAnalysis.GorensteinLyons.pRank_eq_of_elementary one_lt_two hVo hVcard
  have hCU : ∀ x ∈ P, x ∉ U ⊔ R → Nat.card ↥(U ⊓ centralizer {x}) ^ 2 ≤ 2 ^ n := by
    intro x hx hxV
    have hφx : φ ⟨x, hx⟩ ≠ 1 := fun h1 => hxV (by
      have hmem : (⟨x, hx⟩ : P) ∈ φ.ker := h1
      rw [hker'] at hmem
      exact hmem)
    exact SteinbergBT.card_inf_centralizer_sq_le hKcard e φ hequiv hPNU ⟨x, hx⟩ hφx
  have hgap : ∀ x ∈ P₁, x ∉ U ⊔ R → Nat.card ↥((U ⊔ R) ⊓ centralizer {x}) ≤ 2 ^ n := by
    intro x hx hxV
    by_cases hxP : x ∈ P
    · have hx' : y * x * y⁻¹ ∈ P := (mem_normalizer_iff.1 (hP₁NP hyP₁) x).1 hxP
      have hx'V : y * x * y⁻¹ ∉ U ⊔ R := fun h1 => hxV ((mem_normalizer_iff.1 hyL x).2 h1)
      have hmap : (R ⊓ centralizer {x}).map (MulAut.conj y).toMonoidHom =
          U ⊓ centralizer {y * x * y⁻¹} := by
        ext w
        rw [← hyswap.2]
        simp only [mem_map_conj_iff, mem_inf, mem_centralizer_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          calc w * (y * x * y⁻¹) = y * ((y⁻¹ * w * y) * x) * y⁻¹ := by group
            _ = y * (x * (y⁻¹ * w * y)) * y⁻¹ := by rw [h2]
            _ = y * x * y⁻¹ * w := by group
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          calc y⁻¹ * w * y * x = y⁻¹ * (w * (y * x * y⁻¹)) * y := by group
            _ = y⁻¹ * (y * x * y⁻¹ * w) * y := by rw [h2]
            _ = x * (y⁻¹ * w * y) := by group
      have hCR : Nat.card ↥(R ⊓ centralizer {x}) ^ 2 ≤ 2 ^ n := by
        rw [← card_map_conj (R ⊓ centralizer {x}) y, hmap]
        exact hCU _ hx' hx'V
      have h1 := card_sup_inf_centralizer_le_mul hRU hUR (hPNU hxP) (hPN hxP)
      have h3 : Nat.card ↥((U ⊔ R) ⊓ centralizer {x}) ^ 2 ≤ (2 ^ n) ^ 2 := by
        calc Nat.card ↥((U ⊔ R) ⊓ centralizer {x}) ^ 2
            ≤ (Nat.card ↥(U ⊓ centralizer {x}) * Nat.card ↥(R ⊓ centralizer {x})) ^ 2 :=
              Nat.pow_le_pow_left h1 2
          _ = Nat.card ↥(U ⊓ centralizer {x}) ^ 2 * Nat.card ↥(R ⊓ centralizer {x}) ^ 2 :=
              mul_pow _ _ _
          _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul (hCU x hxP hxV) hCR
          _ = (2 ^ n) ^ 2 := by ring
      exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h3
    · obtain ⟨hxU, hxR⟩ := hP₁cover x hx hxP
      rw [← hUcard]
      exact card_sup_inf_centralizer_le_of_swap hRU hUR hxU hxR
  have hrank : ∀ x ∈ P₁, x ∉ U ⊔ R →
      n + CFSG.pRank 2 ↥((U ⊔ R) ⊓ centralizer {x}) ≤ CFSG.pRank 2 ↥(U ⊔ R) := by
    intro x hx hxV
    have h1 := pRank_le_of_le_of_card_le hVel inf_le_left (hgap x hx hxV)
    rw [hrV]
    omega
  have hcrit := CFSG.LocalAnalysis.GorensteinLyons.elementary_strict_rank_strong_closure_criterion
    hP₁2 hVP₁ hVel fun x hx hxV => by
      have h1 := @hquot₁ hVn₁
      have h2 := hrank x hx hxV
      omega
  obtain ⟨hsylD, hstrong₁⟩ := hcrit.2.1 hP₁syl
  have hstrongP : IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D) :=
    ⟨fun v hv => hVP hv, fun a ha g hg => hstrong₁.2 a ha g (hPP₁ hg)⟩
  have hCPR : P ⊓ centralizer (R : Set D) = U ⊔ R := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxP, hxC⟩ := mem_inf.1 hx
      have hx' : y * x * y⁻¹ ∈ P := (mem_normalizer_iff.1 (hP₁NP hyP₁) x).1 hxP
      have hx'C : y * x * y⁻¹ ∈ centralizer (U : Set D) := by
        rw [mem_centralizer_iff]
        intro u hu
        rw [SetLike.mem_coe, ← hyswap.2, mem_map_conj_iff] at hu
        have h1 := mem_centralizer_iff.1 hxC _ hu
        calc u * (y * x * y⁻¹) = y * ((y⁻¹ * u * y) * x) * y⁻¹ := by group
          _ = y * (x * (y⁻¹ * u * y)) * y⁻¹ := by rw [h1]
          _ = y * x * y⁻¹ * u := by group
      have hmem : y * x * y⁻¹ ∈ U ⊔ R := by
        rw [← hCPU]
        exact mem_inf.2 ⟨hx', hx'C⟩
      exact (mem_normalizer_iff.1 hyL x).2 hmem
    · exact le_inf hVP fun v hv =>
        mem_centralizer_iff.2 fun r hr => hcommV r (mem_sup_right hr) v hv
  have hCP₁V : P₁ ⊓ centralizer ((U ⊔ R : Subgroup D) : Set D) = U ⊔ R := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxP₁, hxC⟩ := mem_inf.1 hx
      by_cases hxP : x ∈ P
      · rw [← hCPV]
        exact mem_inf.2 ⟨hxP, hxC⟩
      · obtain ⟨hxU, -⟩ := hP₁cover x hxP₁ hxP
        refine absurd ?_ hUne
        rw [← hxU]
        exact (map_conj_eq_self_iff.2 (centralizer_le_normalizer _
          (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hxC))).symm
    · exact le_inf hVP₁ (le_centralizer_iff_isMulCommutative.2 hVel.toIsMulCommutative)
  have hkerπ : (gmsRootConjugateAction (U ⊔ R) R).ker =
      (normalizer (R : Set D)).subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D)) := by
    rw [ker_gmsRootConjugateAction]
    ext l
    rw [gmsRootKernel, Subgroup.mem_iInf, mem_subgroupOf]
    constructor
    · intro hl
      have h1 := hl ⟨R, gms_R_mem⟩
      rwa [mem_subgroupOf] at h1
    · intro hl Q
      rw [mem_subgroupOf]
      have hQ : (Q : Subgroup D) ∈ ({R, U} : Set (Subgroup D)) := by
        rw [← hΔeq]
        exact Q.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
      rcases hQ with hQ | hQ
      · rw [hQ]
        exact hl
      · rw [hQ]
        exact (gms_LR_normalizes h0 l.2 hl).2.1
  have hindex : ((normalizer (R : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D))).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hyL⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    change Xor ((b : D) * y ∈ normalizer (R : Set D)) ((b : D) ∈ normalizer (R : Set D))
    have hby : R.map (MulAut.conj ((b : D) * y)).toMonoidHom =
        U.map (MulAut.conj (b : D)).toMonoidHom := by
      rw [map_conj_mul, hyswap.2]
    rcases hdich b b.2 with ⟨hbU, hbR⟩ | ⟨hbU, hbR⟩
    · refine Or.inr ⟨map_conj_eq_self_iff.1 hbR, fun h1 => hUne ?_⟩
      have h2 := map_conj_eq_self_iff.2 h1
      rw [hby, hbU] at h2
      exact h2
    · refine Or.inl ⟨map_conj_eq_self_iff.1 (by rw [hby, hbU]), fun h1 => hUne ?_⟩
      have h2 := map_conj_eq_self_iff.2 h1
      rw [hbR] at h2
      exact h2
  refine ⟨hΔeq, hRcard, hUcard, ⟨P₁, hsylD, hPP₁, hcard2, hPn, fun x hx => ?_,
    ⟨y, hyP₁, hyswap⟩, hstrong₁, hstrongP, hCPU, hCPR, hCP₁V, hVn₁, hquot₁, hn3, hrank⟩,
    hkerπ, hindex⟩
  by_cases hxP : x ∈ P
  · exact Or.inl ⟨map_conj_eq_self_iff.2 (hPNU hxP), map_conj_eq_self_iff.2 (hPN hxP)⟩
  · exact Or.inr (hP₁cover x hx hxP)

end Roots

section Node

variable {J R X U P : Subgroup D} {n : ℕ}

theorem gms_normal_root_at_most_two_conjugates_sylow_alternatives [Finite D]
    (h : GMSNormalRootData J R X U P n) :
    (∀ g : D, CFSG.conjugate (U ⊔ R) g ≤ P → CFSG.conjugate (U ⊔ R) g = U ⊔ R) ∧
    (((∃ T : Sylow 2 D, (T : Subgroup D) = P) ∧
        IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D)) ∨
      (∃ P₁ : Subgroup D, (∃ T : Sylow 2 D, (T : Subgroup D) = P₁) ∧ P ≤ P₁ ∧
        Nat.card P₁ = 2 * Nat.card P ∧ (P.subgroupOf P₁).Normal ∧
        (∀ x ∈ P₁, (U.map (MulAut.conj x).toMonoidHom = U ∧
            R.map (MulAut.conj x).toMonoidHom = R) ∨
          (U.map (MulAut.conj x).toMonoidHom = R ∧ R.map (MulAut.conj x).toMonoidHom = U)) ∧
        (∃ y ∈ P₁, U.map (MulAut.conj y).toMonoidHom = R ∧
          R.map (MulAut.conj y).toMonoidHom = U) ∧
        IsStronglyClosedIn P₁ ((U ⊔ R : Subgroup D) : Set D) ∧
        IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D)) ∨
      ((¬∃ T : Sylow 2 D, (T : Subgroup D) = P) ∧
        3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)) ∧
    ((¬∃ T : Sylow 2 D, (T : Subgroup D) = P) → (gmsRootConjugates (U ⊔ R) R).ncard ≤ 2 →
      gmsRootConjugates (U ⊔ R) R = {R, U} ∧ Nat.card R = 2 ^ n ∧ Nat.card U = 2 ^ n ∧
      (∃ P₁ : Subgroup D, (∃ T : Sylow 2 D, (T : Subgroup D) = P₁) ∧ P ≤ P₁ ∧
        Nat.card P₁ = 2 * Nat.card P ∧ (P.subgroupOf P₁).Normal ∧
        (∀ x ∈ P₁, (U.map (MulAut.conj x).toMonoidHom = U ∧
            R.map (MulAut.conj x).toMonoidHom = R) ∨
          (U.map (MulAut.conj x).toMonoidHom = R ∧ R.map (MulAut.conj x).toMonoidHom = U)) ∧
        (∃ y ∈ P₁, U.map (MulAut.conj y).toMonoidHom = R ∧
          R.map (MulAut.conj y).toMonoidHom = U) ∧
        IsStronglyClosedIn P₁ ((U ⊔ R : Subgroup D) : Set D) ∧
        IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D) ∧
        P ⊓ centralizer (U : Set D) = U ⊔ R ∧ P ⊓ centralizer (R : Set D) = U ⊔ R ∧
        P₁ ⊓ centralizer ((U ⊔ R : Subgroup D) : Set D) = U ⊔ R ∧
        ((U ⊔ R).subgroupOf P₁).Normal ∧
        (∀ [((U ⊔ R).subgroupOf P₁).Normal], CFSG.pRank 2 (P₁ ⧸ (U ⊔ R).subgroupOf P₁) ≤ 2) ∧
        3 ≤ n ∧ ∀ x ∈ P₁, x ∉ U ⊔ R →
          n + CFSG.pRank 2 ↥((U ⊔ R) ⊓ centralizer {x}) ≤ CFSG.pRank 2 ↥(U ⊔ R)) ∧
      (gmsRootConjugateAction (U ⊔ R) R).ker =
        (normalizer (R : Set D)).subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D)) ∧
      ((normalizer (R : Set D)).subgroupOf
        (normalizer ((U ⊔ R : Subgroup D) : Set D))).index = 2) := by
  have hBT := SteinbergBT.gms_normal_root_singer_action_and_weak_closure h
  have hmain := fun hsyl hΔ => gms_two_conjugates_interchange h hsyl hΔ
  refine ⟨hBT.2.2.2.2.2.2.1, ?_, hmain⟩
  by_cases hsyl : ∃ T : Sylow 2 D, (T : Subgroup D) = P
  · exact Or.inl ⟨hsyl, hBT.2.2.2.2.2.2.2.1 hsyl⟩
  · by_cases h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard
    · exact Or.inr (Or.inr ⟨hsyl, h3⟩)
    · obtain ⟨-, -, -, ⟨P₁, h1, h2, h3', h4, h5, h6, h7, h8, -⟩, -⟩ := hmain hsyl (by omega)
      exact Or.inr (Or.inl ⟨P₁, h1, h2, h3', h4, h5, h6, h7, h8⟩)

end Node

end CFSG.LocalAnalysis.SteinbergBV
