module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Basic
import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypesTools
import CFSG.GroupTheory.PerfectCentralExtensionUnique
import CFSG.GH74.GLS.IVK.L2.Lemma19Aux
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof155BXW

open CFSG CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof153Twin2
open scoped commutatorElement

private lemma commutator_sup_le_of_le_center {G : Type*} [Group G] {C Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) : ⁅C ⊔ Z, C ⊔ Z⁆ ≤ ⁅C, C⁆ := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨c', hc', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hcz : c * z = z * c := Subgroup.mem_center_iff.mp (hZ hz) c
  have hcz' : c' * z' = z' * c' := Subgroup.mem_center_iff.mp (hZ hz') c'
  rw [hcz, hcz',
    CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center (hZ hz) (hZ hz')]
  exact Subgroup.commutator_mem_commutator hc hc'

private lemma map_center_le_center_of_commutator_eq_bot {G : Type*} [Group G] {A B : Subgroup G}
    [B.Normal] (hsup : A ⊔ B = ⊤) (hcomm : ⁅A, B⁆ = ⊥) :
    (Subgroup.center ↥A).map A.subtype ≤ Subgroup.center G := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top g
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hza : a * (z : G) = (z : G) * a :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, ha⟩)
  have hzb : b * (z : G) = (z : G) * b :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm z.2) b hb
  calc (a * b) * (z : G) = a * (b * (z : G)) := by group
    _ = a * ((z : G) * b) := by rw [hzb]
    _ = (a * (z : G)) * b := by group
    _ = ((z : G) * a) * b := by rw [hza]
    _ = (z : G) * (a * b) := by group

theorem exists_pow_pElement_map_eq {H Q : Type*} [Group H] [Finite H] [Group Q] {p : ℕ}
    (hp : p.Prime) (f : H →* Q) (x : H) {k : ℕ} (hk : f x ^ p ^ k = 1) :
    ∃ n : ℕ, (∃ a : ℕ, (x ^ n) ^ p ^ a = 1) ∧ f (x ^ n) = f x := by
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, m, hpm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hx0 p hp.ne_one
  have hcop : Nat.Coprime (p ^ a) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left a
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨n, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    have hmn : m ∣ n := Nat.modEq_zero_iff_dvd.mp hn2
    rw [hN]
    calc p ^ a * m ∣ p ^ a * n := Nat.mul_dvd_mul_left _ hmn
      _ = n * p ^ a := by ring
  · have hfx : orderOf (f x) ∣ p ^ a := by
      have hdvdN : orderOf (f x) ∣ orderOf x := orderOf_map_dvd f x
      rw [hN] at hdvdN
      have hdvdP : orderOf (f x) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp hdvdP
      have hcopm : Nat.Coprime (p ^ b) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left b
      have hcopm' : Nat.Coprime (orderOf (f x)) m := by simpa [hb] using hcopm
      exact hcopm'.dvd_of_dvd_mul_right hdvdN
    rw [map_pow]
    conv_rhs => rw [← pow_one (f x)]
    rw [pow_eq_pow_iff_modEq]
    exact Nat.ModEq.of_dvd hfx hn1

variable {T : Type*} [Group T]

theorem eq_top_of_cover [Group.IsPerfect T] {P S : Type*} [Group P] [Group S] [IsSimpleGroup S]
    {ψ : P →* S} (hψ : Function.Surjective ψ) (hk : ψ.ker ≤ Subgroup.center P) {φ : P →* T}
    (hφ : Function.Surjective φ) {V : Subgroup T} (hV : V.IsSubnormal)
    (hVp : Group.IsPerfect V) (hV1 : V ≠ ⊥) : V = ⊤ := by
  refine CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect
    (map_center_le_center hφ) ?_
  exact sup_map_center_eq_top hψ hk hφ hV hVp hV1

theorem exists_split_of_cover [Group.IsPerfect T] {P S : Type*} [Group P] [Group S]
    [IsSimpleGroup S] {ψ : P →* S} (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center P) {φ : P →* T} (hφ : Function.Surjective φ)
    {V : Subgroup T} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V) :
    ∃ E : Subgroup T, ⁅V, E⁆ = ⊥ ∧ Group.IsPerfect ↥E ∧ oPrimeResidualOf 3 E = E ∧
      V ⊔ E = ⊤ := by
  have hVp : Group.IsPerfect ↥V := hVq.1
  have hV1 : V ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot V).mp (CFSG.LocalCores.isQuasisimple_nontrivial hVq)
  have hVtop : V = ⊤ := eq_top_of_cover hψ hk hφ hV hVp hV1
  refine ⟨⊥, ?_, ?_, ?_, ?_⟩
  · rw [hVtop, Subgroup.commutator_bot_right]
  · exact Subgroup.isPerfect_iff.mpr (Subgroup.commutator_bot_left ⊥)
  · exact bot_unique (Subgroup.map_subtype_le _)
  · rw [hVtop, top_sup_eq]

theorem commutator_facts_of_cover [Finite T] {S : Type*} [Group S] [IsSimpleGroup S]
    (hSp : Group.IsPerfect S) (h3 : 3 ∣ Nat.card S) {V₀ : Subgroup T} {ψ : ↥V₀ →* S}
    (hψ : Function.Surjective ψ) (hk : ψ.ker ≤ Subgroup.center ↥V₀) :
    Group.IsPerfect ↥⁅V₀, V₀⁆ ∧ oPrimeResidualOf 3 ⁅V₀, V₀⁆ = ⁅V₀, V₀⁆ ∧
      ⁅V₀, V₀⁆ ⊔ (Subgroup.center ↥V₀).map V₀.subtype = V₀ := by
  classical
  set C_H : Subgroup ↥V₀ := ⁅(⊤ : Subgroup ↥V₀), ⊤⁆ with hC_H
  set C : Subgroup T := ⁅V₀, V₀⁆ with hC
  have hCmap : C_H.map V₀.subtype = C := by
    rw [hC_H, hC, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hCHmapψ : C_H.map ψ = ⊤ := by
    rw [hC_H, Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hψ,
      ← _root_.commutator_def]
    exact hSp.commutator_eq_top
  have hCsupψ : C_H ⊔ ψ.ker = ⊤ := sup_ker_eq_top_of_map_eq_top hCHmapψ
  have hCsup : C_H ⊔ Subgroup.center ↥V₀ = ⊤ :=
    top_le_iff.mp (hCsupψ ▸ sup_le_sup le_rfl hk)
  have hCHcomm : ⁅C_H, C_H⁆ = C_H := by
    refine le_antisymm (Subgroup.commutator_le_self C_H) ?_
    calc C_H = ⁅(⊤ : Subgroup ↥V₀), ⊤⁆ := hC_H
      _ = ⁅C_H ⊔ Subgroup.center ↥V₀, C_H ⊔ Subgroup.center ↥V₀⁆ := by rw [hCsup]
      _ ≤ ⁅C_H, C_H⁆ := commutator_sup_le_of_le_center (le_refl _)
  haveI hCHperfect : Group.IsPerfect ↥C_H := Subgroup.isPerfect_iff.mpr hCHcomm
  have hsupV : C ⊔ (Subgroup.center ↥V₀).map V₀.subtype = V₀ := by
    rw [← hCmap, ← Subgroup.map_sup, hCsup, Subgroup.map_top, Subgroup.range_subtype]
  let f : ↥C_H →* S := ψ.comp C_H.subtype
  have hf : Function.Surjective f := by
    intro y
    have hy : y ∈ C_H.map ψ := by rw [hCHmapψ]; exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, by simpa [f] using hxy⟩
  have hOnorm : (oPrimeResidual 3 ↥C_H).Normal := CFSG.GH74.GLS.IVK.oPrimeResidual_normal_gen 3
  haveI : (oPrimeResidual 3 ↥C_H).Normal := hOnorm
  haveI : Finite S := Finite.of_surjective ψ hψ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨x₀, hx₀C, hx₀s⟩ : ∃ x ∈ C_H, ψ x = s := by
    have hs_mem : s ∈ C_H.map ψ := by rw [hCHmapψ]; exact Subgroup.mem_top s
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs_mem
    exact ⟨x, hx, hxs⟩
  have hy3 : f ⟨x₀, hx₀C⟩ ^ 3 ^ 1 = 1 := by
    rw [pow_one, show f ⟨x₀, hx₀C⟩ = s from by simpa [f] using hx₀s, ← hs,
      pow_orderOf_eq_one]
  obtain ⟨n, ⟨i, hx3⟩, hfx⟩ := exists_pow_pElement_map_eq Nat.prime_three f ⟨x₀, hx₀C⟩ hy3
  set x : ↥C_H := ⟨x₀, hx₀C⟩ ^ n with hxdef
  have hfx' : f x = s := by rw [hfx]; simpa [f] using hx₀s
  have hxO : x ∈ oPrimeResidual 3 ↥C_H := CFSG.GH74.GLS.IVK.mem_oPrimeResidual_of_pow hx3
  have hs_mem_image : s ∈ (oPrimeResidual 3 ↥C_H).map f :=
    Subgroup.mem_map.mpr ⟨x, hxO, hfx'⟩
  have hOmap_ne : (oPrimeResidual 3 ↥C_H).map f ≠ ⊥ := by
    intro hbot
    have h1 : s = 1 := by
      have : s ∈ (⊥ : Subgroup S) := hbot ▸ hs_mem_image
      simpa using this
    rw [h1, orderOf_one] at hs
    norm_num at hs
  have hOmap_top : (oPrimeResidual 3 ↥C_H).map f = ⊤ := by
    haveI hnorm : ((oPrimeResidual 3 ↥C_H).map f).Normal :=
      Subgroup.Normal.map hOnorm f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((oPrimeResidual 3 ↥C_H).map f) with h | h
    · exact absurd h hOmap_ne
    · exact h
  have hsupO : oPrimeResidual 3 ↥C_H ⊔ f.ker = ⊤ := sup_ker_eq_top_of_map_eq_top hOmap_top
  have hker_center : f.ker ≤ Subgroup.center ↥C_H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hzψ : ((z : ↥C_H) : ↥V₀) ∈ ψ.ker := by simpa [f] using hz
    exact Subgroup.mem_center_iff.mp (hk hzψ) (w : ↥V₀)
  have hOcenter : oPrimeResidual 3 ↥C_H ⊔ Subgroup.center ↥C_H = ⊤ :=
    top_le_iff.mp (hsupO ▸ sup_le_sup le_rfl hker_center)
  have hOtop : oPrimeResidual 3 ↥C_H = ⊤ := by
    have hcomm_le := commutator_sup_le_of_le_center
      (C := oPrimeResidual 3 ↥C_H) (Z := Subgroup.center ↥C_H) (le_refl _)
    rw [hOcenter] at hcomm_le
    have htop : (⁅(⊤ : Subgroup ↥C_H), ⊤⁆ : Subgroup ↥C_H) = ⊤ := by
      rw [← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup ↥C_H) = ⁅⊤, ⊤⁆ := htop.symm
      _ ≤ ⁅oPrimeResidual 3 ↥C_H, oPrimeResidual 3 ↥C_H⁆ := hcomm_le
      _ ≤ oPrimeResidual 3 ↥C_H := Subgroup.commutator_le_self _
  have hCO : C ≤ oPrimeResidualOf 3 C := by
    have hFmap : (oPrimeResidual 3 ↥C_H).map (V₀.subtype.comp C_H.subtype) ≤
        oPrimeResidualOf 3 C := by
      rw [CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_eq_closure, oPrimeResidual,
        MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro z ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hx
      refine ⟨?_, k, ?_⟩
      · rw [← hCmap]
        exact Subgroup.mem_map.mpr ⟨(x : ↥V₀), x.2, rfl⟩
      · rw [← map_pow, hk, map_one]
    have hCO2 : C = (⊤ : Subgroup ↥C_H).map (V₀.subtype.comp C_H.subtype) := by
      rw [← hCmap, Subgroup.map_top]
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(y : ↥V₀), y.2, rfl⟩
    calc C = (⊤ : Subgroup ↥C_H).map (V₀.subtype.comp C_H.subtype) := hCO2
      _ = (oPrimeResidual 3 ↥C_H).map (V₀.subtype.comp C_H.subtype) := by rw [hOtop]
      _ ≤ oPrimeResidualOf 3 C := hFmap
  have hCeq : oPrimeResidualOf 3 C = C :=
    le_antisymm (Subgroup.map_subtype_le _) hCO
  have hCperfect : Group.IsPerfect ↥C := by
    rw [← hCmap]
    exact Group.IsPerfect.map V₀.subtype
  exact ⟨hCperfect, hCeq, hsupV⟩

theorem exists_split_of_prod [Finite T] [Group.IsPerfect T] {U₀ V₀ : Subgroup T} [U₀.Normal]
    [V₀.Normal] (hsup : U₀ ⊔ V₀ = ⊤) (hcomm : ⁅U₀, V₀⁆ = ⊥)
    {S₁ : Type*} [Group S₁] [IsSimpleGroup S₁] (hp₁ : Group.IsPerfect S₁)
    (h3₁ : 3 ∣ Nat.card S₁) {ψ₁ : ↥U₀ →* S₁} (hψ₁ : Function.Surjective ψ₁)
    (hk₁ : ψ₁.ker ≤ Subgroup.center ↥U₀)
    {S₂ : Type*} [Group S₂] [IsSimpleGroup S₂] (hp₂ : Group.IsPerfect S₂)
    (h3₂ : 3 ∣ Nat.card S₂) {ψ₂ : ↥V₀ →* S₂} (hψ₂ : Function.Surjective ψ₂)
    (hk₂ : ψ₂.ker ≤ Subgroup.center ↥V₀)
    {V : Subgroup T} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V) :
    ∃ E : Subgroup T, ⁅V, E⁆ = ⊥ ∧ Group.IsPerfect ↥E ∧ oPrimeResidualOf 3 E = E ∧
      V ⊔ E = ⊤ := by
  have hperfV : Group.IsPerfect ↥V := hVq.1
  have hVne : V ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot V).mp (CFSG.LocalCores.isQuasisimple_nontrivial hVq)
  have hcomp : CFSG.IsComponent V := ⟨hVq, hV⟩
  have hZ₁c : (Subgroup.center ↥U₀).map U₀.subtype ≤ Subgroup.center T :=
    map_center_le_center_of_commutator_eq_bot hsup hcomm
  have hZ₂c : (Subgroup.center ↥V₀).map V₀.subtype ≤ Subgroup.center T :=
    map_center_le_center_of_commutator_eq_bot
      (A := V₀) (B := U₀) (by rw [sup_comm]; exact hsup)
      (by rw [Subgroup.commutator_comm]; exact hcomm)
  by_cases hVU₀ : V ≤ U₀
  · refine ⟨⁅V₀, V₀⁆, ?_, ?_, ?_, ?_⟩
    · rw [eq_bot_iff]
      exact (Subgroup.commutator_mono hVU₀ (Subgroup.commutator_le_self V₀)).trans
        (le_of_eq hcomm)
    · exact (commutator_facts_of_cover hp₂ h3₂ hψ₂ hk₂).1
    · exact (commutator_facts_of_cover hp₂ h3₂ hψ₂ hk₂).2.1
    · have hZ₁ : V ⊔ (Subgroup.center ↥U₀).map U₀.subtype = U₀ := by
        have h := sup_eq_of_le_factor (U₀ := U₀) (P := ↥U₀) (S := S₁) hψ₁ hk₁
          (φ := MonoidHom.id ↥U₀) Function.surjective_id hV hperfV hVne hVU₀
        simpa using h
      have hZ₂ : ⁅V₀, V₀⁆ ⊔ (Subgroup.center ↥V₀).map V₀.subtype = V₀ :=
        (commutator_facts_of_cover hp₂ h3₂ hψ₂ hk₂).2.2
      have htop : (V ⊔ ⁅V₀, V₀⁆) ⊔
          ((Subgroup.center ↥U₀).map U₀.subtype ⊔
            (Subgroup.center ↥V₀).map V₀.subtype) = ⊤ := by
        calc (V ⊔ ⁅V₀, V₀⁆) ⊔ ((Subgroup.center ↥U₀).map U₀.subtype ⊔
              (Subgroup.center ↥V₀).map V₀.subtype)
            = (V ⊔ (Subgroup.center ↥U₀).map U₀.subtype) ⊔
              (⁅V₀, V₀⁆ ⊔ (Subgroup.center ↥V₀).map V₀.subtype) := by ac_rfl
          _ = U₀ ⊔ V₀ := by rw [hZ₁, hZ₂]
          _ = ⊤ := hsup
      exact CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect (sup_le hZ₁c hZ₂c) htop
  by_cases hVV₀ : V ≤ V₀
  · refine ⟨⁅U₀, U₀⁆, ?_, ?_, ?_, ?_⟩
    · rw [eq_bot_iff]
      calc ⁅V, ⁅U₀, U₀⁆⁆ ≤ ⁅V₀, U₀⁆ :=
            Subgroup.commutator_mono hVV₀ (Subgroup.commutator_le_self U₀)
        _ = ⁅U₀, V₀⁆ := Subgroup.commutator_comm _ _
        _ = ⊥ := hcomm
    · exact (commutator_facts_of_cover hp₁ h3₁ hψ₁ hk₁).1
    · exact (commutator_facts_of_cover hp₁ h3₁ hψ₁ hk₁).2.1
    · have hZ₂ : V ⊔ (Subgroup.center ↥V₀).map V₀.subtype = V₀ := by
        have h := sup_eq_of_le_factor (U₀ := V₀) (P := ↥V₀) (S := S₂) hψ₂ hk₂
          (φ := MonoidHom.id ↥V₀) Function.surjective_id hV hperfV hVne hVV₀
        simpa using h
      have hZ₁ : ⁅U₀, U₀⁆ ⊔ (Subgroup.center ↥U₀).map U₀.subtype = U₀ :=
        (commutator_facts_of_cover hp₁ h3₁ hψ₁ hk₁).2.2
      have htop : (V ⊔ ⁅U₀, U₀⁆) ⊔
          ((Subgroup.center ↥U₀).map U₀.subtype ⊔
            (Subgroup.center ↥V₀).map V₀.subtype) = ⊤ := by
        calc (V ⊔ ⁅U₀, U₀⁆) ⊔ ((Subgroup.center ↥U₀).map U₀.subtype ⊔
              (Subgroup.center ↥V₀).map V₀.subtype)
            = (V ⊔ (Subgroup.center ↥V₀).map V₀.subtype) ⊔
              (⁅U₀, U₀⁆ ⊔ (Subgroup.center ↥U₀).map U₀.subtype) := by ac_rfl
          _ = V₀ ⊔ U₀ := by rw [hZ₂, hZ₁]
          _ = ⊤ := by rw [sup_comm]; exact hsup
      exact CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect (sup_le hZ₁c hZ₂c) htop
  · exfalso
    have hcU : ⁅V, U₀⁆ = ⊥ :=
      (CFSG.LocalCores.component_normal_subgroup hcomp inferInstance).resolve_left hVU₀
    have hcV : ⁅V, V₀⁆ = ⊥ :=
      (CFSG.LocalCores.component_normal_subgroup hcomp inferInstance).resolve_left hVV₀
    have hVcenter : V ≤ Subgroup.center T := by
      intro v hv
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ U₀ ⊔ V₀ := by rw [hsup]; exact Subgroup.mem_top g
      obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
      have hvu : v * u = u * v :=
        (Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcU) hv) u hu).symm
      have hvw : v * w = w * v :=
        (Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcV) hv) w hw).symm
      calc (u * w) * v = u * (w * v) := by group
        _ = u * (v * w) := by rw [← hvw]
        _ = (u * v) * w := by group
        _ = (v * u) * w := by rw [← hvu]
        _ = v * (u * w) := by group
    exact hVne (eq_bot_of_isPerfect_of_le_center hperfV hVcenter)

theorem exists_split_of_mulEquiv_prod [Finite T] [Group.IsPerfect T] {H₁ H₂ : Type*} [Group H₁]
    [Group H₂] [IsSimpleGroup H₁] [IsSimpleGroup H₂] (hp₁ : Group.IsPerfect H₁)
    (h3₁ : 3 ∣ Nat.card H₁) (hp₂ : Group.IsPerfect H₂) (h3₂ : 3 ∣ Nat.card H₂)
    (e : T ≃* H₁ × H₂) {V : Subgroup T} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V) :
    ∃ E : Subgroup T, ⁅V, E⁆ = ⊥ ∧ Group.IsPerfect ↥E ∧ oPrimeResidualOf 3 E = E ∧
      V ⊔ E = ⊤ := by
  let π₁ : T →* H₁ := (MonoidHom.fst H₁ H₂).comp e.toMonoidHom
  let π₂ : T →* H₂ := (MonoidHom.snd H₁ H₂).comp e.toMonoidHom
  let U₀ : Subgroup T := π₂.ker
  let V₀ : Subgroup T := π₁.ker
  haveI hU₀ : U₀.Normal := MonoidHom.normal_ker π₂
  haveI hV₀ : V₀.Normal := MonoidHom.normal_ker π₁
  have hsup : U₀ ⊔ V₀ = ⊤ := by
    rw [eq_top_iff]
    intro t _
    obtain ⟨a, b, hab⟩ : ∃ a b, e t = (a, b) := ⟨(e t).1, (e t).2, rfl⟩
    have hu : e.symm (a, 1) ∈ U₀ :=
      MonoidHom.mem_ker.mpr (by simp [π₂])
    have hv : e.symm (1, b) ∈ V₀ :=
      MonoidHom.mem_ker.mpr (by simp [π₁])
    have hmul : e.symm (a, 1) * e.symm (1, b) = t := by
      apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hab]
      simp [Prod.mk_mul_mk]
    rw [← hmul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hv)
  have hcomm : ⁅U₀, V₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hu2 : (e (u : T)).2 = 1 := by
      have h : π₂ (u : T) = 1 := MonoidHom.mem_ker.mp hu
      simpa [π₂] using h
    have hv1 : (e (v : T)).1 = 1 := by
      have h : π₁ (v : T) = 1 := MonoidHom.mem_ker.mp hv
      simpa [π₁] using h
    have h : e v * e u = e u * e v := by
      ext <;> simp [hu2, hv1, Prod.fst_mul, Prod.snd_mul]
    have hvu : e (v * u) = e (u * v) := by
      rw [map_mul, map_mul]
      exact h
    exact e.injective hvu
  let ψ₁ : ↥U₀ →* H₁ := (MonoidHom.fst H₁ H₂).comp (e.toMonoidHom.comp U₀.subtype)
  have hψ₁ : Function.Surjective ψ₁ := by
    intro a
    have hu : e.symm (a, 1) ∈ U₀ :=
      MonoidHom.mem_ker.mpr (by simp [π₂])
    refine ⟨⟨e.symm (a, 1), hu⟩, ?_⟩
    simp [ψ₁]
  have hk₁ : ψ₁.ker ≤ Subgroup.center ↥U₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : x = 1 := by
      have h1 : (e (x : T)).1 = 1 := by simpa [ψ₁] using hx
      have h2 : (e (x : T)).2 = 1 := by
        have h : π₂ (x : T) = 1 := MonoidHom.mem_ker.mp x.2
        simpa [π₂] using h
      apply Subtype.ext
      apply e.injective
      have hpair : e (x : T) = (1, 1) := Prod.ext h1 h2
      simp only [Subgroup.coe_one, map_one]
      exact hpair
    rw [hx1]
    simp
  let ψ₂ : ↥V₀ →* H₂ := (MonoidHom.snd H₁ H₂).comp (e.toMonoidHom.comp V₀.subtype)
  have hψ₂ : Function.Surjective ψ₂ := by
    intro b
    have hv : e.symm (1, b) ∈ V₀ :=
      MonoidHom.mem_ker.mpr (by simp [π₁])
    refine ⟨⟨e.symm (1, b), hv⟩, ?_⟩
    simp [ψ₂]
  have hk₂ : ψ₂.ker ≤ Subgroup.center ↥V₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : x = 1 := by
      have h1 : (e (x : T)).2 = 1 := by simpa [ψ₂] using hx
      have h2 : (e (x : T)).1 = 1 := by
        have h : π₁ (x : T) = 1 := MonoidHom.mem_ker.mp x.2
        simpa [π₁] using h
      apply Subtype.ext
      apply e.injective
      have hpair : e (x : T) = (1, 1) := Prod.ext h2 h1
      simp only [Subgroup.coe_one, map_one]
      exact hpair
    rw [hx1]
    simp
  exact exists_split_of_prod (T := T) (U₀ := U₀) (V₀ := V₀) hsup hcomm
    hp₁ h3₁ hψ₁ hk₁ hp₂ h3₂ hψ₂ hk₂ hV hVq

end CFSG.RankThree.PartTwo.Sec15.Proof155BXW
