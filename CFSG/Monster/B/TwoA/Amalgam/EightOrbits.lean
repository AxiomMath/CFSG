module

public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Unitary

theorem native_type_four_pair_eight_neighborhood_orbits
    (v w : CVert) (hw : w ∈ sphereFour v) :
    ∃ (v' : CVert) (Ω : Fin 8 → Set CVert) (R : Fin 5 → Set CVert)
      (φ : Fin 5 → CVert → Submodule F4 V6) (α : ↥(vStab v ⊓ vStab w) →* Usig),
      (∃ s : Shat, v ∈ cPi s ∧ w ∈ cPi s) ∧
      (∀ s s' : Shat, v ∈ cPi s → w ∈ cPi s → v ∈ cPi s' → w ∈ cPi s' → cPi s = cPi s') ∧
      (∀ s : Shat, v ∈ cPi s → w ∈ cPi s → piFibre s v = {v, v'}) ∧ v' ≠ v ∧
      (∀ i, Ω i ⊆ cgraph.neighborSet v) ∧ (∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i) ∧
      (∀ i, ∀ u ∈ Ω i, cvOrbit (vStab v ⊓ vStab w) u = Ω i) ∧
      (∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) ∧
      {O | ∃ u ∈ cgraph.neighborSet v, O = cvOrbit (vStab v ⊓ vStab w) u}.ncard = 8 ∧
      Ω 0 = cgraph.commonNeighbors v w ∧ Ω 3 = {v'} ∧
      (∀ s : Shat, v ∈ cPi s → w ∈ cPi s → cgraph.neighborSet v ∩ cPi s = Ω 0 ∪ Ω 3 ∪ Ω 4) ∧
      (∀ d, R d ⊆ cgraph.neighborSet v) ∧ (∀ u ∈ cgraph.neighborSet v, ∃! d, u ∈ R d) ∧
      (∀ d, ∀ u ∈ R d, cvOrbit (vStab v ⊓ vStab v') u = R d) ∧
      (∀ d, (R d).ncard = ![1, 1782, 44352, 1824768, 2097152] d) ∧
      R 0 = Ω 3 ∧ R 1 = Ω 0 ∪ Ω 4 ∧ R 2 = Ω 1 ∪ Ω 5 ∧ R 3 = Ω 2 ∪ Ω 6 ∧ R 4 = Ω 7 ∧
      (∀ d, ∀ u ∈ R d, (cvOrbit (radV v v') u).ncard = ![1, 2, 64, 2048, 2097152] d) ∧
      (∀ d, d = 0 ∨ d = 4 → ∀ u ∈ R d, cvOrbit (radV v v') u = R d) ∧
      (∀ d, (d = 1 ∨ d = 2 ∨ d = 3) → ∀ u ∈ R d, ∀ u' ∈ R d,
        (φ d u = φ d u' ↔ u' ∈ cvOrbit (radV v v') u)) ∧
      φ 1 '' R 1 = {S | IsMaxIso S} ∧ φ 2 '' R 2 = {S | IsSingPt S} ∧
      φ 3 '' R 3 = {S | IsMaxIso S} ∧
      α.range = Atau ∧
      (∀ d, (d = 1 ∨ d = 2 ∨ d = 3) → ∀ u ∈ R d, ∀ q : ↥(vStab v ⊓ vStab w),
        φ d (cvMul u q) = sigmaAct (φ d u) (phiU (α q))) ∧
      (plOrbit 0).ncard = 324 ∧ (plOrbit 1).ncard = 567 ∧ (ptOrbit 0).ncard = 126 ∧
      (ptOrbit 1).ncard = 567 ∧
      Ω 0 = {u | u ∈ R 1 ∧ φ 1 u ∈ plOrbit 0} ∧ Ω 4 = {u | u ∈ R 1 ∧ φ 1 u ∈ plOrbit 1} ∧
      Ω 1 = {u | u ∈ R 2 ∧ φ 2 u ∈ ptOrbit 0} ∧ Ω 5 = {u | u ∈ R 2 ∧ φ 2 u ∈ ptOrbit 1} ∧
      Ω 2 = {u | u ∈ R 3 ∧ φ 3 u ∈ plOrbit 0} ∧ Ω 6 = {u | u ∈ R 3 ∧ φ 3 u ∈ plOrbit 1} ∧
      Ω 3 ∪ Ω 4 ⊆ sphereFour w := by
  obtain ⟨θ₁, f₁, h1, h2, h3⟩ := short_F4_standard_twisted_E6_quotient
  obtain ⟨θ, f, hadj, -, hfeq, hfB⟩ := exists_normalized_quotient θ₁ f₁ h1 h2 h3
  have hx := map_mk_xhatEam_of_quotient hadj hfeq hfB
  have hinj := vtx_zero_eq_iff_of_quotient hadj hfeq hfB
  have hO := native_unitary_1408_stabilizer_point_plane_orbits
  have huniq := (native_coset_graph_order_four_common_neighbors.1 v w hw).2.2.2.1
  obtain ⟨t, k, rfl, rfl, hk0, hk, hτ⟩ := exists_base_presentation hw
  have hvPi : cvMul cv0 t ∈ cPi t := cvMul_mem_cPi cv0_mem_cPi0 t
  have hwPi : cvMul (cvOf (jhatS k)) t ∈ cPi t := cvMul_mem_cPi (jhatS_mem_cPi0 k) t
  have hR := rootSubB_eq_omegaB hadj hfeq hfB hx hinj t
  have hP := omegaB_eq_parts hx hinj t
  exact ⟨cvMul (cvOf a0S) t, omegaB hx hinj t, rootSubB hx hinj t, quotB hx hinj t,
    pairProj t hk0 hk, ⟨t, hvPi, hwPi⟩, huniq, fun s hs1 hs2 => piFibre_eq hk0 hk hs1 hs2,
    fun e => cv0_ne_partner (cvMul_injective t e).symm, omegaB_subset hx hinj t,
    fun u hu => existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hu,
    fun i u hu => cvOrbit_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ i hu,
    ncard_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ,
    ncard_setOf_cvOrbit_pairStab hadj hfeq hfB hx hinj t hk0 hk hτ,
    omegaB_zero hadj hfeq hfB hx hinj t hk0 hk hτ, omegaB_three hadj hfeq hfB hx hinj t,
    fun s hs1 hs2 => by
      rw [huniq s t hs1 hs2 hvPi hwPi]
      exact neighborSet_inter_cPi_eq hadj hfeq hfB hx hinj t,
    rootSubB_subset hx hinj t, fun u hu => existsUnique_mem_rootSubB hx hinj t hu,
    fun d u hu => cvOrbit_rootSubB hadj hfeq hfB hx hinj t d hu, ncard_rootSubB hx hinj t,
    hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2,
    fun d u hu => ncard_cvOrbit_radV hadj hfeq hfB hx hinj t hk0 hk d hu,
    fun d hd u hu => cvOrbit_radV_of_JJ hadj hfeq hfB hx hinj t hk0 hk hd hu,
    fun d hd u hu u' hu' => quotB_eq_iff hadj hfeq hfB hx hinj t hk0 hk hd hu hu',
    image_quotB hadj hfeq hfB hx hinj t (d := 1) (Or.inl rfl),
    image_quotB hadj hfeq hfB hx hinj t (d := 2) (Or.inr (Or.inl rfl)),
    image_quotB hadj hfeq hfB hx hinj t (d := 3) (Or.inr (Or.inr rfl)),
    range_pairProj t hk0 hk hτ,
    fun d hd u hu q => quotB_cvMul hadj hfeq hfB hx hinj t hk0 hk hd hu q,
    hO.2.2.2.2.2.2.2.2.2.2.1, hO.2.2.2.2.2.2.2.2.2.2.2.1, hO.2.2.2.2.2.1, hO.2.2.2.2.2.2.1,
    hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2,
    omegaB_three_union_four_subset hadj hfeq hfB hx hinj t hk0 hk hτ⟩

end CFSG.Monster.B.TwoA.Amalgam
