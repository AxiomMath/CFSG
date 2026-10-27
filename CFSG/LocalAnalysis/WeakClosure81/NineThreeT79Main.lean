module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCoreGlue
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Bar
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Class
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Conf
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Thm77
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthHolds
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_eq_one_of_mem_center_of_pCore_eq_bot {Z : Type} [Group Z] [Finite Z]
    {z : Z} (hz : z ∈ Subgroup.center Z) (hpc : CFSG.pCore 2 Z = ⊥)
    (hz2 : ∃ n : ℕ, orderOf z = 2 ^ n) : z = 1 := by
  have hle : Subgroup.zpowers z ≤ Subgroup.center Z := by
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Subgroup.zpow_mem (Subgroup.center Z) hz m
  have hnorm : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hle
  obtain ⟨n, hn⟩ := hz2
  have hp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hleP : Subgroup.zpowers z ≤ CFSG.pCore 2 Z := le_sSup ⟨hnorm, hp⟩
  rw [hpc] at hleP
  have : z ∈ (⊥ : Subgroup Z) := hleP (Subgroup.mem_zpowers z)
  simpa using this

private theorem nine3_eq_one_of_mem_of_odd_card {Z : Type} [Group Z] {O : Subgroup Z}
    {z : Z} (hz : z ∈ O) (hodd : Odd (Nat.card O))
    (hz2 : ∃ n : ℕ, orderOf z = 2 ^ n) : z = 1 := by
  have hdvd : orderOf z ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hz
  have hoddz : Odd (orderOf z) := Odd.of_dvd_nat hodd hdvd
  obtain ⟨m, hm⟩ := hz2
  have hm1 : orderOf z = 1 := by
    rw [hm] at hoddz
    have hm0 : m = 0 := by
      by_contra hmne
      exact (Nat.not_even_iff_odd.mpr hoddz) (Nat.even_pow.mpr ⟨even_two, hmne⟩)
    rw [hm0, pow_zero] at hm
    exact hm
  exact orderOf_eq_one_iff.mp hm1

private theorem nine3_odd_card_fusionOddCore (Z : Type) [Group Z] [Finite Z] :
    Odd (Nat.card (fusionOddCore Z)) := by
  have h : fusionOddCore Z = CFSG.pPrimeCore 2 Z := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext L
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := Z))

private theorem nine3_quotHyp_comp {H₀ : Subgroup G} {Z : Type} [Group Z] [Finite Z]
    {s : Z} {O : Subgroup Z} (hO : O.Normal) (hpc : CFSG.pCore 2 Z = ⊥)
    (hcl : Nine3Classical Z s O) {Ψ : ↥H₀ →* Z} (hΨ : Nine3QuotHyp H₀ Ψ) :
    Nine3QuotHyp H₀ ((QuotientGroup.mk' O).comp Ψ) := by
  letI : O.Normal := hO
  refine ⟨?_, ?_⟩
  · intro k hk
    show (QuotientGroup.mk' O) (Ψ k) = 1
    rw [hΨ.pcore_le k hk]
    exact map_one (QuotientGroup.mk' O)
  · intro k hk n hord
    have hΨkO : Ψ k ∈ O := by
      have hk' : (QuotientGroup.mk' O) (Ψ k) = 1 := by
        simpa only [MonoidHom.comp_apply] using hk
      exact (QuotientGroup.eq_one_iff (Ψ k)).mp hk'
    have hΨk2 : ∃ m : ℕ, orderOf (Ψ k) = 2 ^ m := by
      have hdvd : orderOf (Ψ k) ∣ 2 ^ n := by
        rw [← hord]
        exact orderOf_map_dvd Ψ k
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨m, hm⟩
    have hΨ1 : Ψ k = 1 := by
      rcases hcl with ⟨m, n', _, hOeq⟩ | ⟨m, n', _, hOeq⟩ | ⟨m, n', _, hOeq⟩ |
        ⟨m, n', _, hOeq⟩ | ⟨m, _, hOeq⟩ | h63
      · rw [hOeq] at hΨkO
        exact nine3_eq_one_of_mem_center_of_pCore_eq_bot hΨkO hpc hΨk2
      · rw [hOeq] at hΨkO
        exact nine3_eq_one_of_mem_center_of_pCore_eq_bot hΨkO hpc hΨk2
      · rw [hOeq] at hΨkO
        exact nine3_eq_one_of_mem_center_of_pCore_eq_bot hΨkO hpc hΨk2
      · rw [hOeq] at hΨkO
        exact nine3_eq_one_of_mem_center_of_pCore_eq_bot hΨkO hpc hΨk2
      · rw [hOeq] at hΨkO
        exact nine3_eq_one_of_mem_of_odd_card hΨkO (nine3_odd_card_fusionOddCore Z) hΨk2
      · obtain ⟨F, hFld, hFin, hcardF, b, c, hbc, N, hN1, hN2, φ, hφsurj, hker,
          hcardO, hcen, r, hr, hr1, hrs⟩ := h63
        exact nine3_eq_one_of_mem_of_odd_card hΨkO (by rw [hcardO]; norm_num) hΨk2
    exact hΨ.two_elt k hΨ1 n hord

theorem nine3Thm79_holds (hCore : OddTranspositionCoreInputSCCls)
    (hList : OddTranspListBundleCls)
    (h772 : ∀ (Y : Type) [Group Y] [Finite Y], SevenSevenTwoInput Y) (hIn : OrthReflParabolic) :
    Nine3Thm79 V T A K S X p g x := by
  intro hc hc' hI h35 hN
  let h : Nine3T79Setup V T A K S X p g x := ⟨hc, hc', hI, h35, hN⟩
  obtain ⟨ρ, hρ⟩ := nine3_exists_fibreAct hc
  obtain ⟨Z, hZgrp, Ψ, hΨsurj, hΨquot, hpcoreZ, hsmall⟩ :=
    nine3_bar h hCore hList (h772 (nine3G1 V K g)) hIn
  letI : Group Z := hZgrp
  haveI : Finite Z := Finite.of_surjective Ψ hΨsurj
  obtain ⟨s, hsS, hsne, O, hO, hcl⟩ := nine3_classical_of_smallAlt hsmall
  obtain ⟨hS2, -⟩ := hsmall
  letI : O.Normal := hO
  let π : ↥(nineH0 V K g) →* Z ⧸ O := (QuotientGroup.mk' O).comp Ψ
  have hπ : Nine3QuotHyp (nineH0 V K g) π := nine3_quotHyp_comp hO hpcoreZ hcl hΨquot
  obtain ⟨U, c, a, e, a', v, hU, hUfib, hc0, haA, haR, heU, heR, hvV, hconfig⟩ :=
    nine3_config h hρ hπ
  have hpi_v : π v = QuotientGroup.mk s := by
    have hΨvS : Ψ v ∈ (V.subgroupOf (nineH0 V K g)).map Ψ :=
      Subgroup.mem_map_of_mem Ψ (Subgroup.mem_subgroupOf.mpr hvV)
    have hΨvne : Ψ v ≠ 1 := by
      intro h1
      apply hconfig.ne_v
      show (QuotientGroup.mk' O).comp Ψ v = 1
      simp only [MonoidHom.comp_apply, h1, map_one]
    have hΨveq : Ψ v = s := seven_eleven_small_eq_of_mem hS2 hsS hsne hΨvS hΨvne
    show (QuotientGroup.mk' O).comp Ψ v = QuotientGroup.mk s
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hΨveq]
  have hmks1 : (QuotientGroup.mk' O) s ≠ 1 := by
    intro h
    apply hconfig.ne_v
    rw [hpi_v]
    exact h
  have hconfig' : Nine3Config (QuotientGroup.mk s) (π a) (π e) (π a') (π v) := by
    rw [← hpi_v]
    exact hconfig
  obtain ⟨dY, hdconj, hdne, hdaY, hdeY⟩ := nine3_prop710 hcl hconfig'
  have hdne' : dY ≠ QuotientGroup.mk s := by
    rw [hpi_v] at hdne
    exact hdne
  have hd1 : dY ≠ 1 := by
    intro hdY1
    apply hmks1
    obtain ⟨cc, hcc⟩ := isConj_iff.mp hdconj
    have h1 : cc * QuotientGroup.mk s * cc⁻¹ = 1 := by rw [hcc, hdY1]
    have h2 : (QuotientGroup.mk s : Z ⧸ O) = 1 := by
      calc QuotientGroup.mk s
          = cc⁻¹ * (cc * QuotientGroup.mk s * cc⁻¹) * cc := by group
        _ = cc⁻¹ * 1 * cc := by rw [h1]
        _ = 1 := by group
    exact h2
  obtain ⟨cc, hcc⟩ := isConj_iff.mp hdconj
  have hπsurj : Function.Surjective π := by
    have hcomp : Function.Surjective ((QuotientGroup.mk' O) ∘ Ψ) :=
      (QuotientGroup.mk'_surjective O).comp hΨsurj
    simpa [π, MonoidHom.coe_comp] using hcomp
  obtain ⟨x, hx⟩ := hπsurj cc
  let w : ↥(nineH0 V K g) := x * v * x⁻¹
  have hpi_w : π w = dY := by
    have h1 : π w = π x * π v * (π x)⁻¹ := by
      simp only [w, map_mul, map_inv]
    rw [h1, hx, hpi_v, hcc]
  have hwD : (w : G) ∈ conjSubgroup V x⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have h1 : (x : G)⁻¹ * (w : G) * ((x : G)⁻¹)⁻¹ = (v : G) := by
      simp only [w, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact hvV
  have hD : conjSubgroup V x⁻¹ ∈ nine3Dcal V (nineH0 V K g) :=
    ⟨x⁻¹, (nineH0 V K g).inv_mem x.2, rfl⟩
  have hdV : ∀ w' : ↥(nineH0 V K g), (w' : G) ∈ V → π w' ≠ π w := by
    intro w' hw'V hcon
    have hw'S : Ψ w' ∈ (V.subgroupOf (nineH0 V K g)).map Ψ :=
      Subgroup.mem_map_of_mem Ψ (Subgroup.mem_subgroupOf.mpr hw'V)
    by_cases h1 : Ψ w' = 1
    · have hthis : π w' = 1 := by
        show (QuotientGroup.mk' O).comp Ψ w' = 1
        simp only [MonoidHom.comp_apply, h1, map_one]
      rw [hthis, hpi_w] at hcon
      exact hd1 hcon.symm
    · have hw'eq : Ψ w' = s := seven_eleven_small_eq_of_mem hS2 hsS hsne hw'S h1
      have hthis : π w' = QuotientGroup.mk s := by
        show (QuotientGroup.mk' O).comp Ψ w' = QuotientGroup.mk s
        simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hw'eq]
      rw [hthis, hpi_w] at hcon
      exact hdne' hcon.symm
  have hda : π w * π a = π a * π w := by
    rw [hpi_w]
    exact hdaY
  have hdu : π w * π e = π e * π w := by
    rw [hpi_w]
    exact hdeY
  have hau : π a * π e ≠ π e * π a := Nine3Config.not_comm_ae hconfig
  exact nine3_thm77 h hρ hπ hU hUfib hc0 haA haR heU heR hau hD hwD hdV hda hdu

theorem thm93Syl_of_inputs (hCore : OddTranspositionCoreInputSCCls)
    (hList : OddTranspListBundleCls)
    (h772 : ∀ (Y : Type) [Group Y] [Finite Y], SevenSevenTwoInput Y) (hIn : OrthReflParabolic) :
    Thm93Syl V T :=
  thm93Syl_of_core fun _ _ _ _ _ _ _ _ => nine3Thm79_holds hCore hList h772 hIn

theorem thm93Syl_of_classification (hCore : OddTranspositionCoreInputSCCls)
    (hList : OddTranspListBundleCls)
    (h772 : ∀ (Y : Type) [Group Y] [Finite Y], SevenSevenTwoInput Y) : Thm93Syl V T :=
  thm93Syl_of_inputs hCore hList h772 orthReflParabolic_holds

end CFSG.LocalAnalysis.WeakClosure81
