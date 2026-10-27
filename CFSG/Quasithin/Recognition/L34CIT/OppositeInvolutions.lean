module

public import CFSG.Quasithin.Recognition.L34CIT.ParabolicInvolutions
public import CFSG.Quasithin.Recognition.L34CIT.PointLineNormal

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

namespace Config

theorem inf_smul_eq_bot_of_not_mem (C : Config A) [Finite A] {u : A}
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huK1 : u ∉ C.K₁) (huK2 : u ∉ C.K₂) :
    (C.T : Subgroup A) ⊓ ((u • C.T : Sylow 2 A) : Subgroup A) = ⊥ := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  by_contra hbot
  set U : Subgroup A := ((u • C.T : Sylow 2 A) : Subgroup A) with hU
  set D : Subgroup A := (C.T : Subgroup A) ⊓ U with hD
  have hDne : D ≠ ⊥ := by rw [hD]; exact hbot
  have hDleT : D ≤ (C.T : Subgroup A) := by rw [hD]; exact inf_le_left
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have huuT : u • (u • C.T) = C.T := by rw [smul_smul, hu2, one_smul]
  have hconj2 : MulAut.conj u * MulAut.conj u = 1 := by
    ext x
    show u * (u * x * u⁻¹) * u⁻¹ = x
    rw [huinv]
    calc u * (u * x * u) * u = (u * u) * (x * (u * u)) := by group
      _ = x := by rw [hu2]; simp
  have hcU : MulAut.conj u • U = (C.T : Subgroup A) := by
    rw [hU, ← Sylow.coe_subgroup_smul (g := u) (P := u • C.T), huuT]
  have huD : MulAut.conj u • D = D := by
    rw [hD, Subgroup.smul_inf,
      show MulAut.conj u • (C.T : Subgroup A) = U from (Sylow.coe_subgroup_smul).symm, hcU]
    exact inf_comm _ _
  have hT2 : IsPGroup 2 ↥(C.T : Subgroup A) :=
    IsPGroup.of_card (n := 6) (by rw [C.card_T]; norm_num)
  have hD2 : IsPGroup 2 ↥D :=
    IsPGroup.of_injective hT2 (Subgroup.inclusion hDleT) (Subgroup.inclusion_injective hDleT)
  haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
  haveI hZnt : Nontrivial ↥(Subgroup.center ↥D) := IsPGroup.center_nontrivial hD2
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥D) := hD2.to_subgroup _
  have hZcard : 2 ∣ Fintype.card ↥(Subgroup.center ↥D) := by
    have hnat : 2 ∣ Nat.card ↥(Subgroup.center ↥D) := by
      rcases hZ2.card_eq_or_dvd with h | h
      · exfalso
        have hbotZ : Subgroup.center ↥D = ⊥ := Subgroup.card_eq_one.mp h
        exact (Subgroup.nontrivial_iff_ne_bot _).mp hZnt hbotZ
      · exact h
    rwa [Nat.card_eq_fintype_card] at hnat
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card (G := ↥(Subgroup.center ↥D)) 2 hZcard
  have hx2 : (x : ↥D) * (x : ↥D) = 1 := by
    have h := congrArg Subtype.val (show x ^ 2 = 1 by rw [← hxord]; exact pow_orderOf_eq_one x)
    simpa [pow_two] using h
  have hx1 : (x : ↥D) ≠ 1 := by
    intro h
    have hxone : x = 1 := Subtype.ext h
    rw [hxone] at hxord
    simp at hxord
  have hxcent : ∀ y : ↥D, y * (x : ↥D) = (x : ↥D) * y := fun y =>
    (Subgroup.mem_center_iff.mp x.2) y
  set v : A := ((x : ↥D) : A) with hv
  have hvD : v ∈ D := (x : ↥D).2
  have hv2 : v * v = 1 := congrArg (fun z : ↥D => (z : A)) hx2
  have hv1 : v ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext (show ((x : ↥D) : A) = ((1 : ↥D) : A) from h))
  have huDmem : MulAut.conj u v ∈ D := by
    have hm : MulAut.conj u v ∈ MulAut.conj u • D := ⟨v, hvD, rfl⟩
    rwa [huD] at hm
  have hcentv : ∀ y ∈ D, y * v = v * y := by
    intro y hy
    exact congrArg (fun z : ↥D => (z : A)) (hxcent ⟨y, hy⟩)
  set c : A := MulAut.conj u v with hc_def
  have hc2 : c * c = 1 := by
    have h := congrArg (MulAut.conj u) hv2
    rw [map_mul, map_one] at h
    exact h
  have hcv : c * v = v * c := hcentv _ huDmem
  have hcc : MulAut.conj u c = v := by
    have h := congrArg (fun f : MulAut A => f v) hconj2
    simpa [c] using h
  have hw2 : (v * c) * (v * c) = 1 := by
    have h1 : (v * c) * (v * c) = v * (c * v) * c := by group
    rw [hcv] at h1
    have h2 : v * (v * c) * c = (v * v) * (c * c) := by group
    rw [h1, h2, hv2, hc2, one_mul]
  have hmulcomm : ∀ {a b : A}, a * a = 1 → MulAut.conj a b = b → a * b = b * a := by
    intro a b ha h
    rw [MulAut.conj_apply] at h
    have h2 := congrArg (· * a) h
    simpa [mul_assoc, ha] using h2
  obtain ⟨w, hwD, hw2', hw1, hwcomm⟩ : ∃ w : A, w ∈ D ∧ w * w = 1 ∧
      w ≠ 1 ∧ u * w = w * u := by
    by_cases hfix : MulAut.conj u v = v
    · exact ⟨v, hvD, hv2, hv1, hmulcomm hu2 hfix⟩
    · refine ⟨v * c, mul_mem hvD huDmem, hw2, ?_, ?_⟩
      · intro h
        apply hfix
        have h1 : c = v⁻¹ * (v * c) := by group
        rw [h, mul_one, inv_eq_of_mul_eq_one_right hv2] at h1
        exact h1
      · exact hmulcomm hu2 (by rw [map_mul, hcc, hcv])
  obtain ⟨P, hP⟩ := C.exists_sylow_eq_centralizer hw2' hw1
  have huP : u ∈ (P : Subgroup A) := by
    rw [← hP, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hwcomm.symm
  have hwT : w ∈ (C.T : Subgroup A) := hDleT hwD
  rcases C.mem_or_mem w hwT hw2' with hwL | hwM
  ·
    have hwZ : w ∉ C.L ⊓ C.M := by
      intro h
      have hZ : w ∈ C.Z := h
      have hCT : Subgroup.centralizer ({w} : Set A) = (C.T : Subgroup A) :=
        C.centralizer_eq_T hZ hw1
      have huC : u ∈ Subgroup.centralizer ({w} : Set A) := by rw [hP]; exact huP
      rw [hCT] at huC
      exact huK1 (C.T_le_normalizer_L huC)
    have hEq : Subgroup.centralizer ({w} : Set A) ⊓ (C.T : Subgroup A) = C.L :=
      C.centralizer_L w hwL hwZ
    have hLP : C.L ≤ (P : Subgroup A) := by
      rw [← hP]
      intro l hl
      exact (hEq ▸ hl).1
    have hpt : C.point P = C.L := C.point_eq_L_of_le hLP
    have huN : u ∈ normalizer (C.point P : Set A) := C.point_normal P huP
    rw [hpt] at huN
    exact huK1 huN
  ·
    have hwZ : w ∉ C.L ⊓ C.M := by
      intro h
      have hZ : w ∈ C.Z := h
      have hCT : Subgroup.centralizer ({w} : Set A) = (C.T : Subgroup A) :=
        C.centralizer_eq_T hZ hw1
      have huC : u ∈ Subgroup.centralizer ({w} : Set A) := by rw [hP]; exact huP
      rw [hCT] at huC
      exact huK2 (C.T_le_normalizer_M huC)
    have hEq : Subgroup.centralizer ({w} : Set A) ⊓ (C.T : Subgroup A) = C.M :=
      C.centralizer_M w hwM hwZ
    have hMP : C.M ≤ (P : Subgroup A) := by
      rw [← hP]
      intro l hl
      exact (hEq ▸ hl).1
    have hpt : C.line P = C.M := C.line_eq_M_of_le hMP
    have huN : u ∈ normalizer (C.line P : Set A) := C.line_normal P huP
    rw [hpt] at huN
    exact huK2 huN

theorem not_mem_K₁_of_inf_smul_eq_bot (C : Config A) [Finite A] {u : A}
    (h : (C.T : Subgroup A) ⊓ ((u • C.T : Sylow 2 A) : Subgroup A) = ⊥) : u ∉ C.K₁ := by
  intro huK1
  have hLuT : C.L ≤ ((u • C.T : Sylow 2 A) : Subgroup A) := by
    rw [Sylow.coe_subgroup_smul]
    intro l hl
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨u⁻¹ * l * u, C.L_le ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa using (Subgroup.mem_normalizer_iff.mp (C.K₁.inv_mem huK1) l).mp hl
  have hle : C.L ≤ (C.T : Subgroup A) ⊓ ((u • C.T : Sylow 2 A) : Subgroup A) :=
    le_inf C.L_le hLuT
  rw [h] at hle
  have hLbot : C.L = ⊥ := le_bot_iff.mp hle
  have hcard := C.card_L
  rw [hLbot] at hcard
  simp at hcard

theorem not_mem_K₂_of_inf_smul_eq_bot (C : Config A) [Finite A] {u : A}
    (h : (C.T : Subgroup A) ⊓ ((u • C.T : Sylow 2 A) : Subgroup A) = ⊥) : u ∉ C.K₂ := by
  intro huK2
  have hMuT : C.M ≤ ((u • C.T : Sylow 2 A) : Subgroup A) := by
    rw [Sylow.coe_subgroup_smul]
    intro l hl
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨u⁻¹ * l * u, C.M_le ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa using (Subgroup.mem_normalizer_iff.mp (C.K₂.inv_mem huK2) l).mp hl
  have hle : C.M ≤ (C.T : Subgroup A) ⊓ ((u • C.T : Sylow 2 A) : Subgroup A) :=
    le_inf C.M_le hMuT
  rw [h] at hle
  have hMbot : C.M = ⊥ := le_bot_iff.mp hle
  have hcard := C.card_M
  rw [hMbot] at hcard
  simp at hcard

@[expose] def fibre (C : Config A) (S' : Sylow 2 A) : Set A :=
  {u | u * u = 1 ∧ u ≠ 1 ∧ u • C.T = S'}

theorem index_subgroupOf_normalizer_T (C : Config A) [Finite A] :
    ((C.T : Subgroup A).subgroupOf (normalizer (C.T : Set A))).index = 3 := by
  haveI : ((C.T : Subgroup A).subgroupOf (normalizer (C.T : Set A))).Normal :=
    Subgroup.normal_in_normalizer
  have hcard : Nat.card ↥((C.T : Subgroup A).subgroupOf (normalizer (C.T : Set A))) = 64 := by
    have hEq : ↥((C.T : Subgroup A).subgroupOf (normalizer (C.T : Set A))) ≃
        ↥(C.T : Subgroup A) :=
      (Subgroup.subgroupOfEquivOfLe (H := (C.T : Subgroup A)) Subgroup.le_normalizer).toEquiv
    rw [Nat.card_congr hEq]
    exact C.card_T
  have hmul := Subgroup.index_mul_card
    ((C.T : Subgroup A).subgroupOf (normalizer (C.T : Set A)))
  rw [hcard, C.card_normalizer_T] at hmul
  omega

theorem ncard_fibre_le_three (C : Config A) [Finite A] (S' : Sylow 2 A)
    (hS' : (C.T : Subgroup A) ⊓ (S' : Subgroup A) = ⊥) : (C.fibre S').ncard ≤ 3 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  rcases Set.eq_empty_or_nonempty (C.fibre S') with hempty | ⟨u₀, hu₀⟩
  · rw [hempty]; simp
  set N : Subgroup A := normalizer (C.T : Set A) with hN
  haveI : ((C.T : Subgroup A).subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hmemN : ∀ u ∈ C.fibre S', u₀⁻¹ * u ∈ N := by
    intro u hu
    rw [hN, ← Sylow.smul_eq_iff_mem_normalizer, ← smul_smul, hu.2.2, ← hu₀.2.2]
    exact inv_smul_smul u₀ C.T
  let f : ↥(C.fibre S') → N ⧸ ((C.T : Subgroup A).subgroupOf N) := fun u =>
    QuotientGroup.mk' ((C.T : Subgroup A).subgroupOf N) ⟨u₀⁻¹ * (u : A), hmemN u u.2⟩
  have hinj : Function.Injective f := by
    intro u u' heq
    by_contra hne
    rw [QuotientGroup.mk'_eq_mk'] at heq
    obtain ⟨z, hzK, hzu⟩ := heq
    have hzT : (z : A) ∈ (C.T : Subgroup A) := hzK
    have hu2 : (u : A) * u = 1 := u.2.1
    have hu'2 : (u' : A) * u' = 1 := u'.2.1
    have huinv : (u : A)⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have hzuA : (u₀⁻¹ * (u : A)) * (z : A) = u₀⁻¹ * (u' : A) := by
      have h := congrArg (Subtype.val) hzu
      simpa using h
    have hzu' : (u : A) * (z : A) = (u' : A) := by
      have h := congrArg (fun x => u₀ * x) hzuA
      simpa [mul_assoc] using h
    have hzeq : (z : A) = (u : A) * u' := by
      have h1 : (z : A) = (u : A)⁻¹ * u' := by
        rw [← hzu']
        group
      rwa [huinv] at h1
    have hz1 : (z : A) ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      rw [h, mul_one] at hzu'
      exact hzu'
    have hZp2 : IsPGroup 2 ↥(Subgroup.zpowers (z : A)) := by
      have hT2 : IsPGroup 2 ↥(C.T : Subgroup A) :=
        IsPGroup.of_card (n := 6) (by rw [C.card_T]; norm_num)
      exact IsPGroup.of_injective hT2
        (Subgroup.inclusion (Subgroup.zpowers_le.mpr hzT))
        (Subgroup.inclusion_injective (Subgroup.zpowers_le.mpr hzT))
    have hZpne : Subgroup.zpowers (z : A) ≠ ⊥ := by
      intro h
      apply hz1
      have hmem : (z : A) ∈ Subgroup.zpowers (z : A) := Subgroup.mem_zpowers (z : A)
      rw [h] at hmem
      exact hmem
    have hZpcard : 2 ∣ Nat.card ↥(Subgroup.zpowers (z : A)) := by
      rcases hZp2.card_eq_or_dvd with h | h
      · exact absurd h (by rw [Subgroup.card_eq_one]; exact hZpne)
      · exact h
    have hZpcard' : 2 ∣ Fintype.card ↥(Subgroup.zpowers (z : A)) := by
      rwa [Nat.card_eq_fintype_card] at hZpcard
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card
      (G := ↥(Subgroup.zpowers (z : A))) 2 hZpcard'
    have hw2 : (y : A) * (y : A) = 1 := by
      have h := congrArg Subtype.val
        (show y ^ 2 = 1 by rw [← hyord]; exact pow_orderOf_eq_one y)
      simpa [pow_two] using h
    have hw1 : (y : A) ≠ 1 := by
      intro h
      have hyone : y = 1 := Subtype.ext h
      rw [hyone] at hyord
      simp at hyord
    have huzu : MulAut.conj (u : A) (z : A) = (z : A)⁻¹ := by
      rw [MulAut.conj_apply, hzeq, mul_inv_rev, huinv,
        inv_eq_of_mul_eq_one_right hu'2]
      calc (u : A) * ((u : A) * u') * (u : A) =
          ((u : A) * (u : A)) * (u' * (u : A)) := by group
        _ = u' * (u : A) := by rw [hu2, one_mul]
    have hconjw : MulAut.conj (u : A) (y : A) = (y : A)⁻¹ := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
      rw [← hm, map_zpow, huzu, inv_zpow]
    have hyfix : MulAut.conj (u : A) (y : A) = (y : A) := by
      rw [hconjw, inv_eq_of_mul_eq_one_right hw2]
    have hcomm : (u : A) * (y : A) = (y : A) * (u : A) := by
      rw [MulAut.conj_apply] at hyfix
      have h2 := congrArg (· * (u : A)) hyfix
      simpa [mul_assoc, hu2] using h2
    have hwT : (y : A) ∈ (C.T : Subgroup A) := Subgroup.zpowers_le.mpr hzT y.2
    have hwS' : (y : A) ∈ (S' : Subgroup A) := by
      have hm : MulAut.conj (u : A) (y : A) ∈ MulAut.conj (u : A) • (C.T : Subgroup A) :=
        ⟨(y : A), hwT, rfl⟩
      rw [← Sylow.coe_subgroup_smul, u.2.2.2] at hm
      rwa [hyfix] at hm
    have hwbot : (y : A) ∈ (C.T : Subgroup A) ⊓ (S' : Subgroup A) := ⟨hwT, hwS'⟩
    rw [hS'] at hwbot
    exact hw1 hwbot

  have hcard_quot : Fintype.card (N ⧸ ((C.T : Subgroup A).subgroupOf N)) = 3 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact C.index_subgroupOf_normalizer_T
  have hle : Nat.card ↥(C.fibre S') ≤ 3 := by
    rw [Nat.card_eq_fintype_card]
    have h := Fintype.card_le_of_injective f hinj
    rwa [hcard_quot] at h
  rw [show (C.fibre S').ncard = Nat.card ↥(C.fibre S') from rfl]
  exact hle

private theorem inf_smul_eq_bot_iff_of_involution (C : Config A) [Finite A] {e : A}
    (he2 : e * e = 1) (he1 : e ≠ 1) :
    (C.T : Subgroup A) ⊓ ((e • C.T : Sylow 2 A) : Subgroup A) = ⊥ ↔
      e ∉ C.K₁ ∧ e ∉ C.K₂ := by
  constructor
  · rintro h
    exact ⟨C.not_mem_K₁_of_inf_smul_eq_bot h, C.not_mem_K₂_of_inf_smul_eq_bot h⟩
  · rintro ⟨h1, h2⟩
    exact C.inf_smul_eq_bot_of_not_mem he2 he1 h1 h2

theorem ncard_fibre_eq_three (C : Config A) [Finite A] (S' : Sylow 2 A)
    (hS' : (C.T : Subgroup A) ⊓ (S' : Subgroup A) = ⊥) : (C.fibre S').ncard = 3 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype (Sylow 2 A) := Fintype.ofFinite _
  have hfin : ({P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥} :
      Set (Sylow 2 A)).Finite := Set.toFinite _
  set S : Finset (Sylow 2 A) := hfin.toFinset with hS
  have hSmem : ∀ P : Sylow 2 A, P ∈ S ↔ (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥ := by
    intro P
    rw [show P ∈ S ↔ P ∈ ({P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥} :
      Set (Sylow 2 A)) from Set.Finite.mem_toFinset hfin]
    rfl
  have hScard : S.card = Nat.card (Sylow 2 A) - 41 := by
    rw [show S.card = ({P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥} :
      Set (Sylow 2 A)).ncard from (Set.ncard_eq_toFinset_card _ hfin).symm]
    exact C.ncard_opposite
  have hXfin : ({e : A | e * e = 1 ∧ e ≠ 1 ∧ e ∉ C.K₁ ∧ e ∉ C.K₂} : Set A).Finite :=
    Set.toFinite _
  have hfib : ∀ P : Sylow 2 A, (C.fibre P).Finite := fun P => Set.toFinite _
  have hdisj : (S : Set (Sylow 2 A)).PairwiseDisjoint (fun P => (hfib P).toFinset) := by
    intro P hP Q hQ hne
    change Disjoint ((hfib P).toFinset) ((hfib Q).toFinset)
    rw [Finset.disjoint_left]
    intro e heP heQ
    rw [Set.Finite.mem_toFinset] at heP heQ
    have h1 : e • C.T = P := heP.2.2
    have h2 : e • C.T = Q := heQ.2.2
    exact hne (h1.symm.trans h2)
  have hunion : S.biUnion (fun P => (hfib P).toFinset) = hXfin.toFinset := by
    ext e
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨P, hP, heP⟩
      rw [Set.Finite.mem_toFinset] at heP
      rw [Set.Finite.mem_toFinset hXfin]
      have he2 : e * e = 1 := heP.1
      have he1 : e ≠ 1 := heP.2.1
      have hPT : (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥ := (hSmem P).1 hP
      rw [← heP.2.2] at hPT
      exact ⟨he2, he1, (C.inf_smul_eq_bot_iff_of_involution he2 he1).1 hPT⟩
    · intro he
      rw [Set.Finite.mem_toFinset hXfin] at he
      have hPT : (C.T : Subgroup A) ⊓ (((e • C.T : Sylow 2 A)) : Subgroup A) = ⊥ :=
        C.inf_smul_eq_bot_of_not_mem he.1 he.2.1 he.2.2.1 he.2.2.2
      exact ⟨e • C.T, (hSmem _).2 hPT, by
        rw [Set.Finite.mem_toFinset]
        exact ⟨he.1, he.2.1, rfl⟩⟩
  have hsum : (∑ P ∈ S, (C.fibre P).ncard) = 3 * S.card := by
    have h := Finset.card_biUnion hdisj
    rw [hunion] at h
    have hXcard : hXfin.toFinset.card = 3 * Nat.card (Sylow 2 A) - 123 := by
      rw [← Set.ncard_eq_toFinset_card _ hXfin]
      exact C.ncard_involutions_not_mem
    have hterms : (∑ P ∈ S, ((hfib P).toFinset).card) = ∑ P ∈ S, (C.fibre P).ncard :=
      Finset.sum_congr rfl fun P _ => (Set.ncard_eq_toFinset_card _ (hfib P)).symm
    calc (∑ P ∈ S, (C.fibre P).ncard) = ∑ P ∈ S, ((hfib P).toFinset).card := hterms.symm
      _ = hXfin.toFinset.card := h.symm
      _ = 3 * Nat.card (Sylow 2 A) - 123 := hXcard
      _ = 3 * S.card := by rw [hScard]; omega
  have hle : ∀ P ∈ S, (C.fibre P).ncard ≤ 3 := fun P hP =>
    C.ncard_fibre_le_three P ((hSmem P).1 hP)
  have hall : ∀ P ∈ S, (C.fibre P).ncard = 3 := by
    intro P hP
    by_contra hne
    have hlt : (C.fibre P).ncard < 3 := lt_of_le_of_ne (hle P hP) hne
    have hlt_sum : (∑ Q ∈ S, (C.fibre Q).ncard) < ∑ Q ∈ S, 3 :=
      Finset.sum_lt_sum (fun Q hQ => hle Q hQ) ⟨P, hP, hlt⟩
    rw [hsum] at hlt_sum
    rw [Finset.sum_const, smul_eq_mul] at hlt_sum
    omega
  exact hall S' ((hSmem S').2 hS')

private theorem conj_mem_normalizer_iff {g x : A} {P Q : Sylow 2 A} (h : g • P = Q) :
    g * x * g⁻¹ ∈ normalizer (Q : Set A) ↔ x ∈ normalizer (P : Set A) := by
  rw [← Sylow.smul_eq_iff_mem_normalizer, ← Sylow.smul_eq_iff_mem_normalizer, ← h,
    show (g * x * g⁻¹) • (g • P) = g • (x • P) by rw [mul_smul, mul_smul, inv_smul_smul],
    smul_left_cancel_iff]

theorem mem_normalizer_of_mem_fibre (C : Config A) [Finite A] {S' : Sylow 2 A} {u : A}
    (hu : u ∈ C.fibre S') :
    u ∈ normalizer (((normalizer (C.T : Set A) ⊓ normalizer (S' : Set A) : Subgroup A) :
      Set A)) := by
  have hu2 : u * u = 1 := hu.1
  have huT : u • C.T = S' := hu.2.2
  have huS' : u • S' = C.T := by rw [← huT, smul_smul, hu2, one_smul]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨(conj_mem_normalizer_iff (x := x) (g := u) (P := S') (Q := C.T) huS').mpr hx.2,
      (conj_mem_normalizer_iff (x := x) (g := u) (P := C.T) (Q := S') huT).mpr hx.1⟩
  · intro hx
    exact ⟨(conj_mem_normalizer_iff (x := x) (g := u) (P := C.T) (Q := S') huT).mp hx.2,
      (conj_mem_normalizer_iff (x := x) (g := u) (P := S') (Q := C.T) huS').mp hx.1⟩

theorem card_normalizer_inf_normalizer (C : Config A) [Finite A] (S' : Sylow 2 A)
    (hS' : (C.T : Subgroup A) ⊓ (S' : Subgroup A) = ⊥) :
    Nat.card ↥(normalizer (C.T : Set A) ⊓ normalizer (S' : Set A)) = 3 := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  set K' : Subgroup A := normalizer (C.T : Set A) ⊓ normalizer (S' : Set A) with hK'
  have hdvd : Nat.card ↥K' ∣ 192 := by
    rw [← C.card_normalizer_T]
    exact Subgroup.card_dvd_of_le (by rw [hK']; exact inf_le_left)
  have hno2 : ∀ x ∈ K', x * x = 1 → x = 1 := by
    intro x hx hx2
    have hxT : x ∈ (C.T : Subgroup A) :=
      mem_of_mem_normalizer_of_pow_eq_one (p := 2) (n := 1) (by simpa [pow_two] using hx2) hx.1
    have hxS' : x ∈ (S' : Subgroup A) :=
      mem_of_mem_normalizer_of_pow_eq_one (p := 2) (n := 1) (by simpa [pow_two] using hx2) hx.2
    have hmem : x ∈ (C.T : Subgroup A) ⊓ (S' : Subgroup A) := ⟨hxT, hxS'⟩
    rwa [hS'] at hmem
  have hnot2 : ¬ 2 ∣ Nat.card ↥K' := by
    intro h2
    have h2' : 2 ∣ Fintype.card ↥K' := by rwa [Nat.card_eq_fintype_card] at h2
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card (G := ↥K') 2 h2'
    have ht2 : ((t : K') : A) * ((t : K') : A) = 1 := by
      have h := congrArg Subtype.val (show t ^ 2 = 1 by rw [← ht]; exact pow_orderOf_eq_one t)
      simpa [pow_two] using h
    have ht1 : ((t : K') : A) = 1 := hno2 _ t.2 ht2
    have hgone : t = 1 := Subtype.ext ht1
    rw [hgone] at ht
    simp at ht
  have hcop : Nat.Coprime (Nat.card ↥K') (2 ^ 6) :=
    (Nat.Coprime.pow_right 6
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnot2).symm)
  have hdvd3 : Nat.card ↥K' ∣ 3 := by
    rw [show (192 : ℕ) = 2 ^ 6 * 3 by norm_num] at hdvd
    exact hcop.dvd_of_dvd_mul_left hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
  · exfalso
    have hfib : (C.fibre S').ncard = 3 := C.ncard_fibre_eq_three S' hS'
    obtain ⟨u, u', hu, hu', hne⟩ :=
      (Set.one_lt_ncard_iff (s := C.fibre S')).mp (by rw [hfib]; norm_num)
    have hu2 : u * u = 1 := hu.1
    have hu'2 : u' * u' = 1 := hu'.1
    have huT : u • C.T = S' := hu.2.2
    have hu'T : u' • C.T = S' := hu'.2.2
    have huS' : u • S' = C.T := by rw [← huT, smul_smul, hu2, one_smul]
    have hu'S' : u' • S' = C.T := by rw [← hu'T, smul_smul, hu'2, one_smul]
    have hprod : u * u' ≠ 1 := by
      intro h
      apply hne
      have h' : u * u' = u * u := by rw [h, hu2]
      exact (mul_left_cancel h').symm
    have hN1 : u * u' ∈ normalizer (C.T : Set A) := by
      rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, hu'T, huS']
    have hN2 : u * u' ∈ normalizer (S' : Set A) := by
      rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, hu'S', huT]
    have hK'mem : u * u' ∈ K' := by rw [hK']; exact ⟨hN1, hN2⟩
    have hK'ne : K' ≠ ⊥ := by
      intro hbot
      apply hprod
      have hm : u * u' ∈ K' := hK'mem
      rwa [hbot] at hm
    exact hK'ne (Subgroup.card_eq_one.mp h1)
  · exact h3

end Config

end CFSG.Quasithin.L34CIT
