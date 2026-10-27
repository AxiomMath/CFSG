module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped commutatorElement

variable {Y : Type} [Group Y]

@[expose] def R891OddCore (R E : Subgroup Y) : Prop :=
  Opp 2 R = R ∧ E ≤ R ∧ (∀ r ∈ R, Odd (orderOf r) → r ∈ E) ∧ (∀ e ∈ E, Odd (orderOf e)) ∧
    ⁅E, R⁆ = E ∧
    ∀ W : Subgroup Y, W ≤ E → W.relIndex E = 3 → ∃ k ∈ R, W.map (MulAut.conj k).toMonoidHom ≠ W


private lemma r891_Opp_le {p : ℕ} (X : Subgroup Y) : Opp p X ≤ X := by
  rw [Opp]
  apply (Subgroup.closure_le X).mpr
  rintro x ⟨hxX, k, hk⟩
  exact hxX

private lemma r891_Opp_mono {p : ℕ} {X Y : Subgroup Y} (h : X ≤ Y) : Opp p X ≤ Opp p Y := by
  rw [Opp]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨hxX, k, hk⟩
  exact Subgroup.subset_closure ⟨h hxX, k, hk⟩

private lemma r891_R_normal_in_F {F R : Subgroup Y} (hRF : R ≤ F)
    (hc : ∀ a ∈ F, ∀ b ∈ F, a * b * a⁻¹ * b⁻¹ ∈ R) :
    ∀ f ∈ F, ∀ r ∈ R, f * r * f⁻¹ ∈ R := by
  intro f hf r hr
  have hc' := hc f hf r (hRF hr)
  have : f * r * f⁻¹ = (f * r * f⁻¹ * r⁻¹) * r := by group
  rw [this]
  exact R.mul_mem hc' hr

private lemma r891_odd_mem_R_of_pow_mem_R [Finite Y] {R : Subgroup Y}
    {o : Y} (hodd : Odd (orderOf o))
    (hpow : ∃ k : ℕ, o ^ (2 ^ k) ∈ R) : o ∈ R := by
  obtain ⟨k, hk⟩ := hpow
  by_cases h1 : orderOf o = 1
  · rw [orderOf_eq_one_iff.mp h1]
    exact R.one_mem
  · have hgt1 : 1 < orderOf o := by
      have hpos := orderOf_pos o
      omega
    have hcop : Nat.Coprime (2 ^ k) (orderOf o) := by
      exact Nat.Coprime.pow_left k (Nat.coprime_two_right.mpr hodd).symm
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hgt1
    have hmod : 2 ^ k * s ≡ 1 [MOD orderOf o] := by
      rw [Nat.ModEq, hs, Nat.mod_eq_of_lt hgt1]
    have h_eq : o = (o ^ (2 ^ k)) ^ s := by
      rw [← pow_mul]
      simpa using (pow_eq_pow_iff_modEq.mpr hmod).symm
    rw [h_eq]
    exact R.pow_mem hk s

private lemma r891_subgroupOf_normal {F R : Subgroup Y}
    (hR_norm : ∀ f ∈ F, ∀ r ∈ R, f * r * f⁻¹ ∈ R) :
    (R.subgroupOf F).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf]
  exact hR_norm (g : Y) g.2 (n : Y) hn

private def r891OddCore_T {F R : Subgroup Y} (hRF : R ≤ F)
    (hc : ∀ a ∈ F, ∀ b ∈ F, a * b * a⁻¹ * b⁻¹ ∈ R) : Subgroup Y :=
  { carrier := {o : Y | o ∈ F ∧ ∃ k : ℕ, o ^ (2 ^ k) ∈ R}
    mul_mem' := by
      rintro a b ha hb
      obtain ⟨haF, k, hk⟩ := ha
      obtain ⟨hbF, l, hl⟩ := hb
      refine ⟨F.mul_mem haF hbF, k + l, ?_⟩
      have hR_normal : (R.subgroupOf F).Normal :=
        r891_subgroupOf_normal (r891_R_normal_in_F hRF hc)
      let π : ↥F →* ↥F ⧸ R.subgroupOf F := QuotientGroup.mk' (R.subgroupOf F)
      have hπa : π ⟨a, haF⟩ ^ (2 ^ k) = 1 := by
        rw [← map_pow]
        change (QuotientGroup.mk' (R.subgroupOf F)) (⟨a, haF⟩ ^ (2 ^ k)) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        simpa [Subgroup.mem_subgroupOf] using hk
      have hπb : π ⟨b, hbF⟩ ^ (2 ^ l) = 1 := by
        rw [← map_pow]
        change (QuotientGroup.mk' (R.subgroupOf F)) (⟨b, hbF⟩ ^ (2 ^ l)) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        simpa [Subgroup.mem_subgroupOf] using hl
      have : IsMulCommutative (↥F ⧸ R.subgroupOf F) := by
        rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
        change ⁅(⊤ : Subgroup ↥F), (⊤ : Subgroup ↥F)⁆ ≤ R.subgroupOf F
        rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [Subgroup.mem_subgroupOf]
        have hcomm : (↑⁅x, y⁆ : Y) = ↑x * ↑y * ↑(x⁻¹) * ↑(y⁻¹) := by
          simp [commutatorElement_def]
        rw [hcomm]
        simpa [Subgroup.coe_inv] using hc x x.2 y y.2
      have hπ_ab : π (⟨a * b, F.mul_mem haF hbF⟩ ^ (2 ^ (k + l))) = 1 := by
        have h_eq : (⟨a * b, F.mul_mem haF hbF⟩ : ↥F) = ⟨a, haF⟩ * ⟨b, hbF⟩ := by
          ext
          rfl
        rw [h_eq, map_pow, map_mul]
        have hcomm : Commute (π ⟨a, haF⟩) (π ⟨b, hbF⟩) := by
          rw [Commute]
          exact mul_comm' _ _
        rw [hcomm.mul_pow]
        rw [pow_add]
        rw [pow_mul, pow_mul']
        rw [hπa, hπb]
        simp
      simpa only [π, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
        using hπ_ab
    one_mem' := by
      refine ⟨F.one_mem, 0, ?_⟩
      simp
    inv_mem' := by
      rintro a ha
      obtain ⟨haF, k, hk⟩ := ha
      refine ⟨F.inv_mem haF, k, ?_⟩
      rw [inv_pow]
      exact R.inv_mem hk }

private lemma r891_Opp_le_T {F R : Subgroup Y} (hRF : R ≤ F)
    (hc : ∀ a ∈ F, ∀ b ∈ F, a * b * a⁻¹ * b⁻¹ ∈ R) :
    Opp 2 F ≤ r891OddCore_T hRF hc := by
  rw [Opp]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨hxF, k, hk⟩
  refine ⟨hxF, k, ?_⟩
  rw [← hk, pow_orderOf_eq_one x]
  exact R.one_mem

private lemma r891_odd_mem_R_of_mem_Opp [Finite Y] {F R : Subgroup Y} (hRF : R ≤ F)
    (hc : ∀ a ∈ F, ∀ b ∈ F, a * b * a⁻¹ * b⁻¹ ∈ R)
    {o : Y} (hoO : o ∈ Opp 2 F) (hodd : Odd (orderOf o)) : o ∈ R := by
  have hoT : o ∈ r891OddCore_T hRF hc := r891_Opp_le_T hRF hc hoO
  obtain ⟨hoF, k, hk⟩ := hoT
  exact r891_odd_mem_R_of_pow_mem_R hodd ⟨k, hk⟩

theorem r891Odd_opp_eq_of_oddCore [Finite Y] {F R E : Subgroup Y} (hRF : R ≤ F)
    (hc : ∀ a ∈ F, ∀ b ∈ F, a * b * a⁻¹ * b⁻¹ ∈ R) (h : R891OddCore R E) :
    R891Odd (Opp 2 F) = E ∧ ⁅E, Opp 2 F⁆ = E ∧
      ∀ W : Subgroup Y, W ≤ E → W.relIndex E = 3 →
        ¬ ∀ k ∈ Opp 2 F, W.map (MulAut.conj k).toMonoidHom = W := by
  obtain ⟨hOppR, hER, hOddR, hOddE, hComm, hNorm3⟩ := h
  have hR_le_Opp : R ≤ Opp 2 F := by
    rw [← hOppR]
    exact r891_Opp_mono hRF
  have hR891Odd_le_E : R891Odd (Opp 2 F) ≤ E := by
    rw [R891Odd]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨hxO, hxOdd⟩
    exact hOddR x (r891_odd_mem_R_of_mem_Opp hRF hc hxO hxOdd) hxOdd
  have hE_le_R891Odd : E ≤ R891Odd (Opp 2 F) := by
    intro e he
    rw [R891Odd]
    apply Subgroup.subset_closure
    exact ⟨hR_le_Opp (hER he), hOddE e he⟩
  have hR891Odd_eq : R891Odd (Opp 2 F) = E := le_antisymm hR891Odd_le_E hE_le_R891Odd
  have hE_normal_in_O : ∀ k ∈ Opp 2 F, ∀ e ∈ E, k * e * k⁻¹ ∈ E := by
    intro k hkO e he
    have hkF : k ∈ F := r891_Opp_le F hkO
    have heR : e ∈ R := hER he
    have hkeR : k * e * k⁻¹ ∈ R := r891_R_normal_in_F hRF hc k hkF e heR
    have hsem : SemiconjBy k e (k * e * k⁻¹) := by
      rw [SemiconjBy]
      group
    have hord : orderOf (k * e * k⁻¹) = orderOf e := by
      exact (SemiconjBy.orderOf_eq k hsem).symm
    exact hOddR _ hkeR (hord ▸ hOddE e he)
  have hE_comm_le_E : ⁅E, Opp 2 F⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he k hk
    have hke : k * e⁻¹ * k⁻¹ ∈ E := hE_normal_in_O k hk e⁻¹ (E.inv_mem he)
    have : ⁅e, k⁆ = e * (k * e⁻¹ * k⁻¹) := by group
    rw [this]
    exact E.mul_mem he hke
  have hE_le_comm : E ≤ ⁅E, Opp 2 F⁆ := by
    calc E = ⁅E, R⁆ := hComm.symm
      _ ≤ ⁅E, Opp 2 F⁆ := Subgroup.commutator_mono le_rfl hR_le_Opp
  have hComm_eq : ⁅E, Opp 2 F⁆ = E := le_antisymm hE_comm_le_E hE_le_comm
  have hLast : ∀ W : Subgroup Y, W ≤ E → W.relIndex E = 3 →
      ¬ ∀ k ∈ Opp 2 F, W.map (MulAut.conj k).toMonoidHom = W := by
    intro W hWE hWrel hforall
    obtain ⟨k, hkR, hkne⟩ := hNorm3 W hWE hWrel
    exact hkne (hforall k (hR_le_Opp hkR))
  exact ⟨hR891Odd_eq, hComm_eq, hLast⟩

theorem R891OddCore.comap_map {Y₀ : Type} [Group Y₀] {F : Subgroup Y} (e : ↥F ≃* Y₀)
    {R₀ E₀ : Subgroup Y₀} (h : R891OddCore R₀ E₀) :
    R891OddCore ((R₀.comap e.toMonoidHom).map F.subtype)
      ((E₀.comap e.toMonoidHom).map F.subtype) := by
  let ι : Y₀ →* Y := F.subtype.comp e.symm.toMonoidHom
  have hι_inj : Function.Injective ι := by
    intro x y hxy
    have h1 : e.symm x = e.symm y := Subtype.ext hxy
    exact e.symm.injective h1
  have hmap_eq : ∀ K : Subgroup Y₀, (K.comap e.toMonoidHom).map F.subtype = K.map ι := by
    intro K
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Subgroup.mem_comap] at hx
      rw [Subgroup.mem_map]
      exact ⟨e.toMonoidHom x, hx, by simp [ι]⟩
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Subgroup.mem_map]
      refine ⟨e.symm k, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        simpa using hk
      · simp [ι]
  obtain ⟨hOpp, hER, hOddR, hOddE, hComm, hNorm3⟩ := h
  rw [hmap_eq R₀, hmap_eq E₀]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hOpp_map : Opp 2 (R₀.map ι) = (Opp 2 R₀).map ι := by
      rw [Opp, Opp, CFSG.RankThree.PartOne.pElementSubgroup,
        CFSG.RankThree.PartOne.pElementSubgroup, MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨hx_map, hx_order⟩
        rw [Subgroup.mem_map] at hx_map
        obtain ⟨z, hz, hxz⟩ := hx_map
        rw [Set.mem_image]
        refine ⟨z, ⟨hz, ?_⟩, hxz⟩
        obtain ⟨k, hk⟩ := hx_order
        rw [← hxz, orderOf_injective ι hι_inj z] at hk
        exact ⟨k, hk⟩
      · rintro ⟨y, hy, rfl⟩
        constructor
        · rw [Subgroup.mem_map]
          exact ⟨y, hy.1, rfl⟩
        · rw [orderOf_injective ι hι_inj y]
          exact hy.2
    rw [hOpp_map, hOpp]
  ·
    exact Subgroup.map_mono hER
  ·
    intro r hr hodd
    rw [Subgroup.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [orderOf_injective ι hι_inj x] at hodd
    exact hOddR x hx hodd
  ·
    intro e he
    rw [Subgroup.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    rw [orderOf_injective ι hι_inj x]
    exact hOddE x hx
  ·
    rw [← Subgroup.map_commutator, hComm]
  ·
    intro W hWE hWrel
    let W₀ := W.comap ι
    have hW₀_le_E₀ : W₀ ≤ E₀ := by
      intro x hx
      rw [Subgroup.mem_comap] at hx
      have hxE : ι x ∈ E₀.map ι := hWE hx
      rw [Subgroup.mem_map] at hxE
      obtain ⟨y, hy, hxy⟩ := hxE
      have : x = y := hι_inj hxy.symm
      rw [this]
      exact hy
    have hW_eq : W₀.map ι = W := by
      ext y
      constructor
      · intro hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [Subgroup.mem_comap] at hx
        exact hx
      · intro hy
        rw [Subgroup.mem_map]
        have hyE : y ∈ E₀.map ι := hWE hy
        rw [Subgroup.mem_map] at hyE
        obtain ⟨x, hx, hxy⟩ := hyE
        refine ⟨x, ?_, hxy⟩
        rw [Subgroup.mem_comap]
        rwa [hxy]
    have hrel : W₀.relIndex E₀ = 3 := by
      rw [← Subgroup.relIndex_map_map_of_injective W₀ E₀ hι_inj]
      rw [hW_eq]
      exact hWrel
    obtain ⟨k₀, hk₀R₀, hk₀ne⟩ := hNorm3 W₀ hW₀_le_E₀ hrel
    refine ⟨ι k₀, ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨k₀, hk₀R₀, rfl⟩
    · have hconj_map : (W₀.map (MulAut.conj k₀).toMonoidHom).map ι =
          W.map (MulAut.conj (ι k₀)).toMonoidHom := by
        rw [← hW_eq]
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj, MonoidHom.comp_apply]
      intro h_eq
      have h_eq' : (W₀.map (MulAut.conj k₀).toMonoidHom).map ι = W₀.map ι := by
        rw [hconj_map, h_eq, hW_eq]
      have h_eq'' : W₀.map (MulAut.conj k₀).toMonoidHom = W₀ := by
        have := congrArg (Subgroup.comap ι) h_eq'
        simpa [Subgroup.comap_map_eq_self_of_injective hι_inj] using this
      exact hk₀ne h_eq''

theorem nonempty_mulEquiv_comap_map {Y₀ : Type} [Group Y₀] {F : Subgroup Y} (e : ↥F ≃* Y₀)
    (E₀ : Subgroup Y₀) : Nonempty (↥((E₀.comap e.toMonoidHom).map F.subtype) ≃* ↥E₀) := by
  let ι : Y₀ →* Y := F.subtype.comp e.symm.toMonoidHom
  have hι_inj : Function.Injective ι := by
    intro x y hxy
    have h1 : e.symm x = e.symm y := Subtype.ext hxy
    exact e.symm.injective h1
  have hmap_eq : (E₀.comap e.toMonoidHom).map F.subtype = E₀.map ι := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Subgroup.mem_comap] at hx
      rw [Subgroup.mem_map]
      exact ⟨e.toMonoidHom x, hx, by simp [ι]⟩
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Subgroup.mem_map]
      refine ⟨e.symm k, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        simpa using hk
      · simp [ι]
  rw [hmap_eq]
  exact ⟨(Subgroup.equivMapOfInjective E₀ ι hι_inj).symm⟩

theorem derInf8_eq_of_perfect {F N : Subgroup Y} (hNF : N ≤ F) (hN : ⁅N, N⁆ = N)
    (hc : ∀ a ∈ F, ∀ b ∈ F, a * b * a⁻¹ * b⁻¹ ∈ N) : DerInf8 F = N := by
  let N' := N.subgroupOf F
  have hN'_perf : ⁅N', N'⁆ = N' := by
    have h1 : (⁅N', N'⁆).map F.subtype = N'.map F.subtype := by
      rw [Subgroup.map_commutator]
      rw [Subgroup.map_subgroupOf_eq_of_le hNF, hN]
    have := congrArg (Subgroup.comap F.subtype) h1
    simpa [Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective F)] using this
  have h1 : derivedSeries ↥F 1 ≤ N' := by
    rw [derivedSeries_succ, derivedSeries_zero]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf]
    exact hc a a.2 b b.2
  have hN'_le_derived : ∀ n, N' ≤ derivedSeries ↥F n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ]
      calc N' = ⁅N', N'⁆ := hN'_perf.symm
        _ ≤ ⁅derivedSeries ↥F k, derivedSeries ↥F k⁆ := Subgroup.commutator_mono ih ih
  have hD_eq_N' : (⨅ n, derivedSeries ↥F n) = N' := by
    apply le_antisymm
    · exact (iInf_le _ 1).trans h1
    · exact le_iInf hN'_le_derived
  unfold DerInf8
  rw [hD_eq_N']
  exact Subgroup.map_subgroupOf_eq_of_le hNF

theorem nonempty_derInf8_mulEquiv {Y₀ : Type} [Group Y₀] {F : Subgroup Y} {P : Subgroup Y₀}
    (e : ↥F ≃* ↥P) : Nonempty (↥(DerInf8 F) ≃* ↥(DerInf8 P)) := by
  let D_F : Subgroup ↥F := ⨅ n, derivedSeries ↥F n
  let D_P : Subgroup ↥P := ⨅ n, derivedSeries ↥P n
  have hmap : D_F.map e.toMonoidHom = D_P := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap]
      rw [Subgroup.mem_iInf]
      intro n
      have hxD : x ∈ D_F := hx
      rw [Subgroup.mem_iInf] at hxD
      have hx_map : e.toMonoidHom x ∈ (derivedSeries ↥F n).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom (hxD n)
      rwa [map_derivedSeries_eq e.surjective n] at hx_map
    · intro y hy
      rw [Subgroup.mem_map]
      refine ⟨e.symm y, ?_, by simp⟩
      rw [Subgroup.mem_iInf]
      intro n
      have hy_n : y ∈ derivedSeries ↥P n := by
        have hy' := hy
        rw [Subgroup.mem_iInf] at hy'
        exact hy' n
      have hmap_n : (derivedSeries ↥F n).map e.toMonoidHom = derivedSeries ↥P n :=
        map_derivedSeries_eq e.surjective n
      have h_eq : (derivedSeries ↥P n).comap e.toMonoidHom = derivedSeries ↥F n := by
        rw [← hmap_n]
        exact Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective
          (derivedSeries ↥F n)
      rw [← h_eq]
      rw [Subgroup.mem_comap]
      simpa using hy_n
  have e_iso : ↥D_F ≃* ↥D_P := by
    rw [← hmap]
    exact Subgroup.equivMapOfInjective D_F e.toMonoidHom e.injective
  have F_iso : ↥D_F ≃* ↥(DerInf8 F) :=
    Subgroup.equivMapOfInjective D_F F.subtype F.subtype_injective
  have P_iso : ↥D_P ≃* ↥(DerInf8 P) :=
    Subgroup.equivMapOfInjective D_P P.subtype P.subtype_injective
  exact ⟨F_iso.symm.trans (e_iso.trans P_iso)⟩

theorem commutator_derInf8_self [Finite Y] (F : Subgroup Y) :
    ⁅DerInf8 F, DerInf8 F⁆ = DerInf8 F := by
  have hperf : Group.IsPerfect ↥((⨅ n : ℕ, derivedSeries ↥F n) : Subgroup ↥F) :=
    CFSG.perfect_residual_characterization.2.2.1
  have := hperf
  have h : Group.IsPerfect ↥(DerInf8 F) := by
    unfold DerInf8
    exact Group.IsPerfect.map F.subtype
  exact Subgroup.isPerfect_iff.mp h

theorem R891SU32.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : R891SU32 A) :
    R891SU32 B := by
  obtain ⟨φ, h_surj, h_extra, h_cent⟩ := h
  let ψ : B →* QuaternionGroup 2 := φ.comp e.symm.toMonoidHom
  have h_surj' : Function.Surjective ψ := by
    intro q
    obtain ⟨a, ha⟩ := h_surj q
    exact ⟨e a, by simp [ψ, ha]⟩
  have hker : ψ.ker = φ.ker.map e.toMonoidHom := by
    ext b
    simp [ψ, MonoidHom.mem_ker]
  have h_extra' : IsExtraspecialExpP 3 1 ↥ψ.ker := by
    rw [hker]
    exact isExtraspecialExpP_of_mulEquiv
      (Subgroup.equivMapOfInjective φ.ker e.toMonoidHom e.injective).symm h_extra
  have h_cent' : centralizer (ψ.ker : Set B) ≤ ψ.ker := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff] at hb
    rw [hker]
    rw [Subgroup.mem_map]
    refine ⟨e.symm b, ?_, by simp⟩
    apply h_cent
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact hb (e x) (by rw [hker]; exact Subgroup.mem_map_of_mem e.toMonoidHom hx)
  exact ⟨ψ, h_surj', h_extra', h_cent'⟩

theorem R891SL3Two.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : R891SL3Two A n) : R891SL3Two B n := by
  rcases h with ⟨hn, hSU⟩ | ⟨h2n, heven, hTC⟩ | ⟨h2n, hodd, hTC⟩
  · exact Or.inl ⟨hn, R891SU32.of_mulEquiv e hSU⟩
  · refine Or.inr (Or.inl ⟨h2n, heven, ?_⟩)
    obtain ⟨h_qs, h_center, h_S⟩ := hTC
    refine ⟨?_, ?_, ?_⟩
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm h_qs
    · rw [← h_center]
      rw [← Subgroup.map_center_eq e]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective (Subgroup.center A) e.toMonoidHom e.injective).toEquiv).symm
    · have e_q : (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
        QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)
      exact LieModel.of_mulEquiv e_q h_S
  · refine Or.inr (Or.inr ⟨h2n, hodd, ?_⟩)
    obtain ⟨h_qs, h_center, h_S⟩ := hTC
    refine ⟨?_, ?_, ?_⟩
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm h_qs
    · rw [← h_center]
      rw [← Subgroup.map_center_eq e]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective (Subgroup.center A) e.toMonoidHom e.injective).toEquiv).symm
    · have e_q : (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
        QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)
      exact LieModel.of_mulEquiv e_q h_S

theorem R891L3Pi.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : R891L3Pi A n) : R891L3Pi B n := by
  obtain ⟨h_even, h_lie⟩ | ⟨h_odd, h_lie⟩ := h
  · exact Or.inl ⟨h_even, LieModel.of_mulEquiv e h_lie⟩
  · exact Or.inr ⟨h_odd, LieModel.of_mulEquiv e h_lie⟩

theorem R891E9.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : R891E9 A) :
    R891E9 B := by
  obtain ⟨φ⟩ := h
  exact ⟨e.symm.trans φ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
