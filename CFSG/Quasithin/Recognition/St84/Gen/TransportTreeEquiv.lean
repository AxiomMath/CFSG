module

public import CFSG.Quasithin.Recognition.St84.TreeBase

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H]

private noncomputable def treeEquivOfMap {U : Type} [Group U] {P : Subgroup H}
    {φ : ↥P →* U} (hφ : Function.Injective φ) {E : Subgroup U}
    {A : Subgroup ↥E} {B : Subgroup H} (hB : B ≤ P)
    (hmap : A.map E.subtype = (B.subgroupOf P).map φ) : ↥A ≃* ↥B :=
  (Subgroup.equivMapOfInjective A E.subtype E.subtype_injective).trans
    ((MulEquiv.subgroupCongr hmap).trans
      ((Subgroup.equivMapOfInjective (B.subgroupOf P) φ hφ).symm.trans
        (Subgroup.subgroupOfEquivOfLe hB)))

namespace BaseEdgeData

noncomputable def equivOfA (D : BaseEdgeData H) :
    ↥(D.X.L 0) ≃* ↥(oTwoPrime D.Pα) :=
  treeEquivOfMap (f112Gold D.L1 D.L2 D.S).ofA_injective
    ((oTwoPrime_le D.Pα).trans D.le_Pα) D.L_zero_map

noncomputable def equivOfB (D : BaseEdgeData H) :
    ↥(D.X.L 1) ≃* ↥(oTwoPrime D.Pβ) :=
  treeEquivOfMap (f112Gold D.L1 D.L2 D.S).ofB_injective
    ((oTwoPrime_le D.Pβ).trans D.le_Pβ) D.L_one_map

theorem centerOf_pCoreOf_L_zero_map (D : BaseEdgeData H) :
    (centerOf (pCoreOf 2 (D.X.L 0))).map D.E.subtype =
      f112OfA D.L1 D.L2 D.S (centerOf (pCoreOf 2 (oTwoPrime D.Pα))) := by
  rw [← CFSG.Quasithin.SimsD1.TransGrp.centerOf_map_eq D.E.subtype D.E.subtype_injective,
    D.pCoreOf_L_zero_map]
  exact f112_ofA_centerOf D.L1 D.L2 D.S
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pα)).trans
      ((oTwoPrime_le D.Pα).trans D.le_Pα))

theorem centerOf_pCoreOf_L_one_map (D : BaseEdgeData H) :
    (centerOf (pCoreOf 2 (D.X.L 1))).map D.E.subtype =
      f112OfB D.L1 D.L2 D.S (centerOf (pCoreOf 2 (oTwoPrime D.Pβ))) := by
  rw [← CFSG.Quasithin.SimsD1.TransGrp.centerOf_map_eq D.E.subtype D.E.subtype_injective,
    D.pCoreOf_L_one_map]
  exact f112_ofB_centerOf D.L1 D.L2 D.S
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pβ)).trans
      ((oTwoPrime_le D.Pβ).trans D.le_Pβ))

private theorem conj_mem_comap_of_map {U : Type} [Group U] {P : Subgroup H}
    {φ : ↥P →* U} {E : Subgroup U} {A : Subgroup ↥E} {B : Subgroup H} (hB : B ≤ P)
    (hmapA : A.map E.subtype = (B.subgroupOf P).map φ)
    {N : Subgroup H} (hNnorm : B ≤ Subgroup.normalizer (N : Set H)) :
    ∀ a ∈ A, ∀ n' ∈ Subgroup.comap E.subtype ((N.subgroupOf P).map φ),
      a * n' * a⁻¹ ∈ Subgroup.comap E.subtype ((N.subgroupOf P).map φ) := by
  intro a ha n' hn'
  refine (Subgroup.mem_comap (K := (N.subgroupOf P).map φ) (x := a * n' * a⁻¹)).mpr ?_
  have hn'f : E.subtype n' ∈ (N.subgroupOf P).map φ :=
    (Subgroup.mem_comap (K := (N.subgroupOf P).map φ) (x := n')).mp hn'
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hn'f
  have haN : E.subtype a ∈ (B.subgroupOf P).map φ := by
    rw [← hmapA]
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp haN
  have hconj : (b : H) * (y : H) * (b : H)⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hNnorm (Subgroup.mem_subgroupOf.mp hb))
      (y : H)).mp (Subgroup.mem_subgroupOf.mp hy)
  have heq : E.subtype (a * n' * a⁻¹) = φ (b * y * b⁻¹) := by
    simp only [map_mul, map_inv, ← hbeq, ← hyeq]
  rw [heq]
  exact Subgroup.mem_map.mpr
    ⟨b * y * b⁻¹, Subgroup.mem_subgroupOf.mpr (by simpa using hconj), rfl⟩

private theorem exists_comap_of_map {U : Type} [Group U] {P : Subgroup H}
    {φ : ↥P →* U} (hφ : Function.Injective φ) {E : Subgroup U}
    {A : Subgroup ↥E} {B : Subgroup H} (hB : B ≤ P)
    (hmapA : A.map E.subtype = (B.subgroupOf P).map φ)
    (hmapQ : (pCoreOf 2 A).map E.subtype = ((pCoreOf 2 B).subgroupOf P).map φ)
    {N : Subgroup H} (hNQ : N ≤ pCoreOf 2 B)
    (hNnorm : B ≤ Subgroup.normalizer (N : Set H)) :
    ∃ N' : Subgroup ↥E, N' ≤ pCoreOf 2 A ∧
      A ≤ Subgroup.normalizer (N' : Set ↥E) ∧
      N'.map E.subtype = (N.subgroupOf P).map φ := by
  let N' : Subgroup ↥E := Subgroup.comap E.subtype ((N.subgroupOf P).map φ)
  have hN'mem : ∀ c : ↥E, c ∈ N' ↔ E.subtype c ∈ (N.subgroupOf P).map φ :=
    fun c => Subgroup.mem_comap
  have hN'Q : N' ≤ pCoreOf 2 A := by
    intro n' hn'
    have h1 : E.subtype n' ∈ (pCoreOf 2 A).map E.subtype := by
      rw [hmapQ]
      exact Subgroup.map_mono (f := φ) (Subgroup.subgroupOf_mono P hNQ)
        ((hN'mem n').mp hn')
    exact (Subgroup.mem_map_iff_mem E.subtype_injective).mp h1
  have hNnormE : A ≤ Subgroup.normalizer (N' : Set ↥E) := by
    have step := conj_mem_comap_of_map (A := A) (B := B) hB hmapA hNnorm
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨step g hg x, fun hx => by
      have h := step g⁻¹ (A.inv_mem hg) (g * x * g⁻¹) hx
      have heq : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [heq] at h⟩
  refine ⟨N', hN'Q, hNnormE, ?_⟩
  have hle : (N.subgroupOf P).map φ ≤ E.subtype.range :=
    (Subgroup.map_mono (f := φ) (Subgroup.subgroupOf_mono P hNQ)).trans
      ((hmapQ.symm.le).trans (Subgroup.map_le_range E.subtype (pCoreOf 2 A)))
  exact Subgroup.map_comap_eq_self hle

theorem exists_comap_of_tree (D : BaseEdgeData H) {N : Subgroup H}
    (hNQ : N ≤ pCoreOf 2 (oTwoPrime D.Pα))
    (hNnorm : oTwoPrime D.Pα ≤ Subgroup.normalizer (N : Set H)) :
    ∃ N' : Subgroup ↥D.E, N' ≤ pCoreOf 2 (D.X.L 0) ∧
      D.X.L 0 ≤ Subgroup.normalizer (N' : Set ↥D.E) ∧
      N'.map D.E.subtype = f112OfA D.L1 D.L2 D.S N :=
  exists_comap_of_map (P := f112P1 D.L1 D.L2 D.S) (φ := (f112Gold D.L1 D.L2 D.S).ofA)
    (E := D.E) (A := D.X.L 0) (B := oTwoPrime D.Pα)
    (f112Gold D.L1 D.L2 D.S).ofA_injective ((oTwoPrime_le D.Pα).trans D.le_Pα)
    D.L_zero_map D.pCoreOf_L_zero_map hNQ hNnorm

theorem exists_comap_ofB_of_tree (D : BaseEdgeData H) {N : Subgroup H}
    (hNQ : N ≤ pCoreOf 2 (oTwoPrime D.Pβ))
    (hNnorm : oTwoPrime D.Pβ ≤ Subgroup.normalizer (N : Set H)) :
    ∃ N' : Subgroup ↥D.E, N' ≤ pCoreOf 2 (D.X.L 1) ∧
      D.X.L 1 ≤ Subgroup.normalizer (N' : Set ↥D.E) ∧
      N'.map D.E.subtype = f112OfB D.L1 D.L2 D.S N :=
  exists_comap_of_map (P := f112P2 D.L1 D.L2 D.S) (φ := (f112Gold D.L1 D.L2 D.S).ofB)
    (E := D.E) (A := D.X.L 1) (B := oTwoPrime D.Pβ)
    (f112Gold D.L1 D.L2 D.S).ofB_injective ((oTwoPrime_le D.Pβ).trans D.le_Pβ)
    D.L_one_map D.pCoreOf_L_one_map hNQ hNnorm

private theorem le_iff_of_map_eq_of {U : Type} [Group U] {P : Subgroup H}
    {φ : ↥P →* U} (hφ : Function.Injective φ) {E : Subgroup U}
    {Y N : Subgroup H} {Y' N' : Subgroup ↥E}
    (hY : Y ≤ P) (hN : N ≤ P)
    (hY' : Y'.map E.subtype = (Y.subgroupOf P).map φ)
    (hN' : N'.map E.subtype = (N.subgroupOf P).map φ) :
    Y' ≤ N' ↔ Y ≤ N := by
  constructor
  · intro h
    have hmaple : (Y.subgroupOf P).map φ ≤ (N.subgroupOf P).map φ := by
      have hmono := Subgroup.map_mono (f := E.subtype) h
      rwa [hY', hN'] at hmono
    have hsuble : Y.subgroupOf P ≤ N.subgroupOf P :=
      (Subgroup.map_le_map_iff_of_injective (f := φ) hφ).mp hmaple
    intro x hx
    have hxP : x ∈ P := hY hx
    have hmem : (⟨x, hxP⟩ : ↥P) ∈ Y.subgroupOf P := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp (hsuble hmem)
  · intro h
    have hmaple : (Y.subgroupOf P).map φ ≤ (N.subgroupOf P).map φ :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono P h)
    have hY'le : Y'.map E.subtype ≤ N'.map E.subtype := by
      rwa [hY', hN']
    exact (Subgroup.map_le_map_iff_of_injective E.subtype_injective).mp hY'le

theorem le_iff_of_map_eq (D : BaseEdgeData H) {Y N : Subgroup H} {Y' N' : Subgroup ↥D.E}
    (hY : Y ≤ f112P1 D.L1 D.L2 D.S) (hN : N ≤ f112P1 D.L1 D.L2 D.S)
    (hY' : Y'.map D.E.subtype = f112OfA D.L1 D.L2 D.S Y)
    (hN' : N'.map D.E.subtype = f112OfA D.L1 D.L2 D.S N) :
    Y' ≤ N' ↔ Y ≤ N :=
  le_iff_of_map_eq_of (P := f112P1 D.L1 D.L2 D.S) (φ := (f112Gold D.L1 D.L2 D.S).ofA)
    (E := D.E) (f112Gold D.L1 D.L2 D.S).ofA_injective hY hN hY' hN'

theorem le_iff_of_ofB_map_eq (D : BaseEdgeData H) {Y N : Subgroup H} {Y' N' : Subgroup ↥D.E}
    (hY : Y ≤ f112P2 D.L1 D.L2 D.S) (hN : N ≤ f112P2 D.L1 D.L2 D.S)
    (hY' : Y'.map D.E.subtype = f112OfB D.L1 D.L2 D.S Y)
    (hN' : N'.map D.E.subtype = f112OfB D.L1 D.L2 D.S N) :
    Y' ≤ N' ↔ Y ≤ N :=
  le_iff_of_map_eq_of (P := f112P2 D.L1 D.L2 D.S) (φ := (f112Gold D.L1 D.L2 D.S).ofB)
    (E := D.E) (f112Gold D.L1 D.L2 D.S).ofB_injective hY hN hY' hN'

end BaseEdgeData

end CFSG.Quasithin.F112R.St84

end
