module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineGen
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveKGpEx

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open CFSG.SignalizerFunctorTheorem.Quadratic (LGL)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem conj_eq_self_of_mem_normalizer_of_card_two {X : Type} [Group X]
    {Y : Subgroup X} (hY : Nat.card Y = 2) {g y : X}
    (hg : g ∈ Subgroup.normalizer (Y : Set X)) (hy : y ∈ Y) (hy1 : y ≠ 1) :
    g * y * g⁻¹ = y := by
  obtain ⟨t, _, ht_uniq⟩ := (Nat.card_eq_two_iff' (1 : ↥Y)).1 hY
  have hmem : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  have hyY : (⟨y, hy⟩ : ↥Y) ≠ 1 := fun h => hy1 (Subtype.ext_iff.1 h)
  have hmemY : (⟨g * y * g⁻¹, hmem⟩ : ↥Y) ≠ 1 := by
    intro h
    have h1 : g * y * g⁻¹ = 1 := Subtype.ext_iff.1 h
    exact hy1 (by
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [mul_assoc] using this)
  exact Subtype.ext_iff.1 ((ht_uniq _ hmemY).trans (ht_uniq _ hyY).symm)

theorem barSub_conj_mem {K V : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {d : G} (hdK : d ∈ K) (hdV : d ∈ Subgroup.normalizer (V : Set G)) {y : X}
    (hy : y ∈ SevenK.barSub K φ V) :
    φ ⟨d, hdK⟩ * y * (φ ⟨d, hdK⟩)⁻¹ ∈ SevenK.barSub K φ V := by
  obtain ⟨v, hvV, rfl⟩ := SevenK.mem_barSub.1 hy
  have hdvV : d * (v : G) * d⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hdV (v : G)).1 hvV
  have hmemV : ((⟨d, hdK⟩ : ↥K) * v * (⟨d, hdK⟩ : ↥K)⁻¹ : G) ∈ V := by
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hdvV
  have hmap : φ ((⟨d, hdK⟩ : ↥K) * v * (⟨d, hdK⟩ : ↥K)⁻¹) ∈ SevenK.barSub K φ V :=
    SevenK.mem_barSub.2 ⟨(⟨d, hdK⟩ : ↥K) * v * (⟨d, hdK⟩ : ↥K)⁻¹, hmemV, rfl⟩
  rwa [map_mul, map_mul, map_inv] at hmap

theorem barSub_mem_normalizer {K V : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    {d : G} (hdK : d ∈ K) (hdV : d ∈ Subgroup.normalizer (V : Set G)) :
    φ ⟨d, hdK⟩ ∈ Subgroup.normalizer (SevenK.barSub K φ V : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact barSub_conj_mem hdK hdV hy
  · intro hy
    have hdinvK : d⁻¹ ∈ K := K.inv_mem hdK
    have hdinvV : d⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).inv_mem hdV
    have hmem := barSub_conj_mem hdinvK hdinvV hy
    have hdinv_eq : φ ⟨d⁻¹, hdinvK⟩ = (φ ⟨d, hdK⟩)⁻¹ := by
      have hk : (⟨d, hdK⟩ : ↥K)⁻¹ = ⟨d⁻¹, hdinvK⟩ := rfl
      rw [← hk]
      exact map_inv φ (⟨d, hdK⟩ : ↥K)
    convert hmem using 1
    rw [hdinv_eq]
    group

theorem mem_center_map_subtype_of_sq_mem_center_of_odd {X : Type} [Group X]
    {N : Subgroup X} {g : X} (hgN : g ∈ N)
    (hsq : g ^ 2 ∈ (Subgroup.center ↥N).map N.subtype) (hodd : Odd (orderOf g)) :
    g ∈ (Subgroup.center ↥N).map N.subtype := by
  obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.1 hsq
  have hodd' : Odd (orderOf (⟨g, hgN⟩ : ↥N)) := by
    rw [Subgroup.orderOf_mk]
    exact hodd
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hodd'.coprime_two_left
  have hx2 : (⟨g, hgN⟩ : ↥N) ^ 2 = z := by
    apply Subtype.ext
    show g ^ 2 = (z : X)
    exact hzval.symm
  have hxcenter : (⟨g, hgN⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [← hm, hx2]
    exact (Subgroup.center ↥N).pow_mem hz m
  exact Subgroup.mem_map.mpr ⟨⟨g, hgN⟩, hxcenter, rfl⟩

theorem IsMinFam16.map_mem_center_of_mem_centralizer_V₀ (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ)
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) 1) {p : ℕ} (hp : p.Prime)
    (hN : CFSG.IsExtraspecial p ↥(fusionOddCore X)) (hNc : Nat.card (fusionOddCore X) = p ^ 3)
    {c : ↥(conjClosure V H)} (hodd : Odd (orderOf c)) (hcN : φ c ∈ fusionOddCore X)
    (hc : (c : G) ∈ centralizer (V₀ : Set G)) :
    φ c ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype := by
  let K : Subgroup G := conjClosure V H
  let Y : Subgroup X := SevenK.barSub K φ V
  have hY2 : Nat.card Y = 2 := by simpa [Y, K] using hX.1
  have hY : IsElemAbelian 2 Y := by
    have h := (h.hyp.h6.elemAbelian.subgroupOf K).map φ
    simpa [Y, K, SevenK.barSub] using h
  have hgen : normalClosure (Y : Set X) = ⊤ := by
    simpa [Y, K] using IsMinFam16.normalClosure_barSub_eq_top h1 hS h hH hV hφ
  have hcM : (c : G) ∈ M := by
    have h0 : (c : G) ∈ Subgroup.normalizer (V₀ : Set G) :=
      Subgroup.centralizer_le_normalizer (V₀ : Set G) hc
    rwa [h.hyp.normalizer₀] at h0
  have hcV : (c : G) ∈ Subgroup.normalizer (V : Set G) := by
    rwa [h.hyp.h6.normalizer_eq]
  have hcY : φ c ∈ Subgroup.normalizer (Y : Set X) := by
    have hmm := barSub_mem_normalizer (φ := φ) c.2 hcV
    simpa [Y, K] using hmm
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hY2
    omega
  obtain ⟨tY, htY_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  let t : X := tY
  have ht : t ∈ Y := tY.2
  have ht1 : t ≠ 1 := fun h1' => htY_ne (Subtype.ext h1')
  have hcomm : φ c * t * (φ c)⁻¹ = t :=
    conj_eq_self_of_mem_normalizer_of_card_two hY2 hcY ht ht1
  have hsup : Y ⊔ fusionOddCore X = ⊤ := by
    rcases hX.2 with h | ⟨-, h, -⟩
    · exact absurd h.1 (lt_irrefl 1)
    · exact h
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY2]; norm_num)
  haveI : Finite ↥(fusionOddCore X) :=
    Nat.finite_of_card_ne_zero (by rw [hNc]; exact pow_ne_zero _ hp.ne_zero)
  haveI : Finite X := Finite.of_surjective
    (fun q : ↥Y × ↥(fusionOddCore X) => (q.1 : X) * (q.2 : X)) (by
      rintro x
      have hx : x ∈ (Y : Set X) * (fusionOddCore X : Set X) := by
        rw [← Subgroup.mul_normal Y (fusionOddCore X), hsup]
        exact Subgroup.mem_top x
      rw [Set.mem_mul] at hx
      obtain ⟨y, hy, n, hn, rfl⟩ := hx
      exact ⟨(⟨y, hy⟩, ⟨n, hn⟩), rfl⟩)
  have hsq : (φ c) ^ 2 ∈ (Subgroup.center ↥(fusionOddCore X)).map
      (fusionOddCore X).subtype := by
    have hmem := Shape166.mul_mem_center_of_extraspecial hY hgen hX hp hN hNc ht ht1 hcN
    have htconj : t * φ c * t⁻¹ = φ c := by
      have hct : φ c * t = t * φ c := by
        have := congrArg (fun z => z * φ c) hcomm
        simpa [mul_assoc] using this
      rw [← hct, mul_assoc, mul_inv_cancel, mul_one]
    rw [htconj] at hmem
    rwa [pow_two]
  exact mem_center_map_subtype_of_sq_mem_center_of_odd hcN hsq
    (hodd.of_dvd_nat (orderOf_map_dvd φ c))

theorem conjClosure_V₀_conjClosure_le_iSub16 (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    conjClosure V₀ (conjClosure V H) ≤ iSub16 V H := by
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun k hk z hz => H.mul_mem (H.mul_mem hk (hVH hz)) (H.inv_mem hk)
  exact conjClosure_mono (le_inf h.hyp.h6.le (h.V₀_le_pCoreOf h5 hS hF hV)) hKH

theorem isElemAbelian_conjClosure_V₀_conjClosure (h1 : W16One G) (h5 : W16Five G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H) :
    IsElemAbelian 2 (conjClosure V₀ (conjClosure V H)) :=
  (h.isElemAbelian_iSub16 h1 hS hF).mono (conjClosure_V₀_conjClosure_le_iSub16 h5 hS h hF hV)

theorem conjClosure_le_normalizer_conjClosure_V₀ :
    conjClosure V H ≤ Subgroup.normalizer (conjClosure V₀ (conjClosure V H) : Set G) :=
  le_normalizer_conjClosure V₀ (conjClosure V H)

structure ExCfg (M V₀ V U S H : Subgroup G) {X : Type} [Group X]
    (φ : ↥(conjClosure V H) →* X) (p : ℕ) : Prop where
  one : W16One G
  five : W16Five G
  std : Std15 G
  cex : Cex16 M V₀ V U S
  min : IsMinFam16 M U S H
  not_le : ¬ V ≤ pCoreOf 2 H
  pCore_le : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G)
  bar : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ
  shape : Shape166 X (SevenK.barSub (conjClosure V H) φ V) 1
  prime : p.Prime
  extra : CFSG.IsExtraspecial p ↥(fusionOddCore X)
  card : Nat.card (fusionOddCore X) = p ^ 3

@[expose] noncomputable def tautRep (W : Type) [AddCommGroup W] [Module (ZMod 2) W] :
    Representation (ZMod 2) (LGL 2 W) W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

end CFSG.LocalAnalysis.WeakClosure81

end
