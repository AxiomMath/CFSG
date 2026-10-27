module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofSeven
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofMemFix
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item134Holds
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof172
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof
open scoped commutatorElement

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def nB177 (A L : Subgroup G) : Subgroup G :=
  xB172 A (A ⊓ L) ⊔ ⨆ (b : G) (_ : b ∈ A ⊓ L) (_ : b ≠ 1) (_ : IsThreeCentralIn L b),
    (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))

end Defs

namespace Proof17Res11

variable {G : Type} [Group G] [Finite G]

theorem card_le_center_of_commutator_le {K B : Subgroup G} (hBK : B ≤ K) (hB3 : IsPGroup 3 B)
    (hcomm : ⁅K, B⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K) :
    Nat.card B ≤ Nat.card (Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥K with hθdef
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.2.1
  set π := QuotientGroup.mk' θ with hπ
  set B' := B.subgroupOf K with hB'def
  have eB : B' ≃* B := Subgroup.subgroupOfEquivOfLe hBK
  have hB'3 : IsPGroup 3 B' := hB3.of_equiv eB.symm
  have hmemθ : ∀ u : ↥K, u ∈ θ ↔ (u : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := fun u =>
    (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have hcen : B'.map π ≤ Subgroup.center (↥K ⧸ θ) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq, hmemθ]
      have h1 := hcomm (Subgroup.commutator_mem_commutator (inv_mem y.2)
        (inv_mem (Subgroup.mem_subgroupOf.mp hx)))
      have e : (((y * x)⁻¹ * (x * y) : ↥K) : G) = ⁅((y : G))⁻¹, ((x : G))⁻¹⁆⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e]
      exact inv_mem h1
  have hinj : Function.Injective (π.comp B'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hB'3 x
    have h1 : orderOf ((x : ↥K)) ∣ Nat.card θ := by
      have := Subgroup.orderOf_dvd_natCard θ hx
      exact this
    have h2 : orderOf ((x : ↥K)) = 3 ^ k := by
      rw [← hk]
      exact (Subgroup.orderOf_coe x)
    have hk0 : k = 0 := by
      by_contra hk0
      exact hθ3 ((dvd_pow_self 3 hk0).trans (h2 ▸ h1))
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    rw [hk]
    exact one_mem _
  have hcard : Nat.card (π.comp B'.subtype).range = Nat.card B' :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hrange : (π.comp B'.subtype).range = B'.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← Nat.card_congr eB.toEquiv, ← hcard, hrange]
  exact Subgroup.card_le_of_le hcen

theorem map_conj_le_of_threeCentral
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {g : G}
    (hg : g ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) :
    (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))).map
      (MulAut.conj g).toMonoidHom ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD13.mem_partTwoE
  have hcA : c ∈ A := hD13.mem_A
  have hc1 : c ≠ 1 := hD13.ne_one
  obtain ⟨hdL, S, hdS, hSd⟩ := id hdc
  set C := Subgroup.centralizer ({d} : Set G) with hCdef
  set O := pPrimeCoreOf 3 C with hOdef
  set Ld := inSubgroup perfectResidual (L ⊓ C) with hLddef
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1 ⟨S, hdS, hSd⟩
  have hG4 : SectionFourHyp ↥C := hD13.toTheoremFourHyp.sectionFourHyp
    (centralizer_singleton_ne_top h.toSec14Std.isSimpleGroup h.toSec14Std.nonabelian hd1)
  obtain ⟨K, hK, hLdK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hdA hc1 hD13.mem_lA.1 hJq
  have hS' := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  obtain ⟨hKeq, hA6⟩ : K = Ld ⊔ inSubgroup (aschbacherSolvableCore 3) K ∧
      Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)) := by
    rcases h134 G A c L hD13 hJ d hdA hd1 ⟨_, hS'⟩ K hK hLdK with
      ⟨hKeq, hA6, -⟩ | ⟨hKeq, hA6, -⟩ | ⟨-, -, -, h12⟩
    · exact ⟨hKeq, hA6⟩
    · exact ⟨hKeq, hA6⟩
    · exfalso
      rw [hΩ, Set.ncard_singleton] at h12
      omega
  have hBLd : A ⊓ L ≤ Ld := fun x hx =>
    Sec13.mem_residual_of_pow_three h415 hJ hdL hd1 ⟨S, hdS, hSd⟩ hx.2
      (Subgroup.mem_centralizer_singleton_iff.mpr (hD13.commute hx.1 hdA)) (k := 1)
      (by rw [pow_one]; exact hA.1.2 x hx.1)
  have hBK : A ⊓ L ≤ K := hBLd.trans hLdK
  have hgC : g ∈ C := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
    (show d ∈ ((A ⊓ L : Subgroup G) : Set G) from ⟨hdA, hdL⟩)) hg
  have hKg : K.map (MulAut.conj g).toMonoidHom = K := by
    by_contra hne
    have hKg' := Sec6.map_conj_mem_thetaComponentsAt hgC hK
    have hcomm := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK hKg' (Ne.symm hne)
    have hBKg : A ⊓ L ≤ K.map (MulAut.conj g).toMonoidHom := fun x hx => by
      refine ⟨x, hBK hx, ?_⟩
      change g * x * g⁻¹ = x
      rw [← Subgroup.mem_centralizer_iff.mp hg x hx]
      group
    have h1 : ⁅K, A ⊓ L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsIn (M := C) hK]
      exact le_inf ((Subgroup.commutator_mono le_rfl hBK).trans (Subgroup.commutator_le_self K))
        ((Subgroup.commutator_mono le_rfl hBKg).trans hcomm)
    have hle := card_le_center_of_commutator_le hBK (hA.isPGroup.to_le inf_le_left) h1
    rw [hA6.1, (j2_point_facts hD13 hJ).2.1] at hle
    omega
  have hKle : K ≤ O ⊔ Ld := by
    rw [hKeq]
    exact sup_le le_sup_right ((Res7MemFix.theta_le_of_mem hK).trans le_sup_left)
  have hgO : g ∈ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 C hgC
  rw [Subgroup.map_sup, Late.map_conj_eq_of_mem_normalizer hgO]
  refine sup_le le_sup_left ?_
  calc Ld.map (MulAut.conj g).toMonoidHom ≤ K.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hLdK
    _ = K := hKg
    _ ≤ O ⊔ Ld := hKle

theorem isThreeCentralIn_of_lB_ne_bot {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c}) (hcL : c ∉ L) {b : G}
    (hb : b ∈ A ⊓ L) {D : Subgroup G} (hDA : D ≤ A) (hbD : b ∈ D) (hD : lB A D ≠ ⊥) :
    IsThreeCentralIn L b := by
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD13.mem_partTwoE
  have hcA : c ∈ A := hD13.mem_A
  have hc3 : orderOf c = 3 := hD13.orderOf_eq
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨b', d, L', hcfg⟩ : ∃ b' d L', IsLBConfig A D b' d L' := by
    by_contra hcon
    push Not at hcon
    exact hD (lB_eq_bot hcon)
  obtain ⟨hDeq, hb'Ω, hLb', -, hd'L, S, hdS, hSd⟩ := hcfg
  have hb'c : Subgroup.zpowers b' = Subgroup.zpowers c := by
    rw [hΩ] at hb'Ω
    exact hb'Ω
  have hLL' : L = L' := by
    have hL' : L ∈ lA A b' := (lA_eq_of_zpowers_eq hb'c) ▸ hD13.mem_lA
    rw [hLb'] at hL'
    exact hL'
  subst hLL'
  have hdD : d ∈ D := by
    rw [hDeq]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton d))
  have hdA : d ∈ A := hDA hdD
  have hDeq' : D = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [hDeq, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, hb'c]
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    Subgroup.zpowers_le.mpr (centralizer_singleton_le_normalizer_zpowers d
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm c hcA d hdA)))
  have hbD' : b ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [← hDeq']
    exact hbD
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hbD'
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hbD'
  have hyL : y ∈ L := (Subgroup.zpowers_le.mpr hd'L) hy
  have hxL : x ∈ L := by
    have : x = b * y⁻¹ := by rw [← hxy]; group
    rw [this]
    exact mul_mem hb.2 (inv_mem hyL)
  have hx1 : x = 1 := by
    have hh := Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc3 hcL
    have hxmem : x ∈ L ⊓ Subgroup.zpowers c := ⟨hxL, hx⟩
    rw [hh, Subgroup.mem_bot] at hxmem
    exact hxmem
  have hbd : b ∈ Subgroup.zpowers d := by
    rw [← hxy, hx1, one_mul]
    exact hy
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hbd
  refine ⟨hb.2, S, ?_, fun s hs => ?_⟩
  · have e : (⟨b, hb.2⟩ : ↥L) = (⟨d, hd'L⟩ : ↥L) ^ n := Subtype.ext (by simp [hn])
    rw [e]
    exact zpow_mem hdS n
  · have hsd := Subgroup.mem_centralizer_iff.mp (hSd hs) _ (Set.mem_singleton _)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    have e : (⟨b, hb.2⟩ : ↥L) = (⟨d, hd'L⟩ : ↥L) ^ n := Subtype.ext (by simp [hn])
    rw [e]
    exact (Commute.zpow_left hsd n).eq

theorem centralizer_le_normalizer_nB177
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (hbal : Step143Balance) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcL : c ∉ L) :
    Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (nB177 A L : Set G) := by
  intro g hg
  refine Proof176Steps.mem_normalizer_of_map_le ?_
  set E := ⨆ (b : G) (_ : b ∈ A ⊓ L) (_ : b ≠ 1) (_ : IsThreeCentralIn L b),
    (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))) with hEdef
  have hEle : E ≤ nB177 A L := le_sup_right
  have hXle : xB172 A (A ⊓ L) ≤ nB177 A L := le_sup_left
  have hWE : ∀ b ∈ A ⊓ L, b ≠ 1 → IsThreeCentralIn L b →
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ E :=
    fun b hb hb1 hbc => le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1
      (le_iSup_of_le hbc le_rfl)))
  have hgN : ∀ b ∈ A ⊓ L, b ≠ 1 → IsThreeCentralIn L b →
      (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))).map
        (MulAut.conj g).toMonoidHom ≤ E := fun b hb hb1 hbc =>
    (map_conj_le_of_threeCentral h134 h48 h hΩ hJ hb.1 hb1 hbc hg).trans (hWE b hb hb1 hbc)
  rw [nB177, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    by_cases hsp : ∃ D : Subgroup G, IsHyperplane A D ∧ b ∈ D ∧ lB A D ≠ ⊥
    · obtain ⟨D, hD, hbD, hDne⟩ := hsp
      have hbc := isThreeCentralIn_of_lB_ne_bot h hΩ hcL hb hD.1 hbD hDne
      exact (Subgroup.map_mono (xb172_le_residual hbal h hΩ h9 hcL hb hb1)).trans
        ((hgN b hb hb1 hbc).trans hEle)
    · push Not at hsp
      have hle := xb172_le_sup hbal h hΩ hcL hb hb1 (X := ⊥) (fun D hD hbD => (hsp D hD hbD).le)
        (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
      have heq : xb172 A b = pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :=
        le_antisymm (hle.trans (by rw [sup_bot_eq])) le_sup_left
      have hgb : g ∈ Subgroup.normalizer
          (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) : Set G) :=
        le_normalizer_pPrimeCoreOf 3 _
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb) hg)
      rw [heq, Late.map_conj_eq_of_mem_normalizer hgb, ← heq]
      exact (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)) :
        xb172 A b ≤ xB172 A (A ⊓ L)).trans hXle
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => iSup_le fun hbc => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact (hgN b hb hb1 hbc).trans hEle

end Proof17Res11

open Proof17Res11 in
theorem step177Contra_of_items
    (h171 : Item171S17)
    (hbal : Step143Balance) (h9 : CardInfNineS17) (hsol : Step177OThreeSolv) (h134 : Item134)
    (h48 : Sec4.Item4_8) : Step177Contra := by
  intro G _ _ A c L Y₀ h h1514 h176 hΩ V hVM hMV hVab hUC hU1 hUB
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have h9' : Nat.card (A ⊓ L : Subgroup G) = 9 := h9 G A c L Y₀ h
  have hB : IsHyperplane A (A ⊓ L) := ⟨inf_le_left, by rw [hA.2, h9']⟩
  have hcL : c ∉ L := not_mem_L_of_config h hMV hVab hUC hU1
  have hsol' : ∀ b ∈ A ⊓ L, b ≠ 1 →
      Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :=
    fun b hb hb1 => hsol G A c L Y₀ h h1514 h176 hΩ V hVM hMV hVab hUC hU1 hUB b hb hb1
  have hcfg := fun {b : G} (hb : b ∈ A ⊓ L) (hb1 : b ≠ 1) =>
    xb172_le_of_config hbal h h176 hΩ h9' hVM hMV hVab hUC hU1 hUB hsol' hb hb1
  have hXM : xB172 A (A ⊓ L) ≤ Subgroup.normalizer (Y₀ : Set G) :=
    iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => (hcfg hb hb1).2
  have hYX : Y₀ ≤ xB172 A (A ⊓ L) :=
    Proof172.le_xB172 hA hB (h171 G A c L Y₀ h Y₀ h.mem_y0Star (A ⊓ L) hB)
  by_cases hlB : ∃ D : Subgroup G, IsHyperplane A D ∧ lB A D ≠ ⊥
  ·
    obtain ⟨D, -, hDne⟩ := hlB
    obtain ⟨b', d, L', hcf⟩ : ∃ b' d L', IsLBConfig A D b' d L' := by
      by_contra hcon
      push Not at hcon
      exact hDne (lB_eq_bot hcon)
    obtain ⟨-, hb'Ω, hLb', hJ2, -⟩ := hcf
    have hLL' : L = L' := by
      have hb'c : Subgroup.zpowers b' = Subgroup.zpowers c := by
        rw [hΩ] at hb'Ω
        exact hb'Ω
      have hL' : L ∈ lA A b' := (lA_eq_of_zpowers_eq hb'c) ▸ h.toSec13Data.mem_lA
      rw [hLb'] at hL'
      exact hL'
    subst hLL'
    have hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
      Sec13.nonempty_thetaQuot_equiv_j2 CFSG.Sporadic.J2.isSimpleGroup_J2 Sec13.sporadicModels131
        hJ2
    have hNM : nB177 A L ≤ Subgroup.normalizer (Y₀ : Set G) := by
      refine sup_le hXM (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => iSup_le fun _ => ?_)
      exact sup_le (hcfg hb hb1).1 ((Subgroup.map_subtype_le _).trans
        (inf_le_left.trans (h.le_y0.trans Subgroup.le_normalizer)))
    exact false_of_le_normalizer h hVM hMV hVab hUC hU1 hUB (hYX.trans le_sup_left) hNM
      (centralizer_le_normalizer_nB177 h134 h48 hbal h hΩ hJ h9' hcL)
  · push Not at hlB
    exact false_of_le_normalizer h hVM hMV hVab hUC hU1 hUB hYX hXM
      (centralizer_le_normalizer_xB172_of_lB_eq_bot hbal h hΩ hcL hlB)

end CFSG.RankThree.PartTwo.Sec17
