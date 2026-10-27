module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotPositionB
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBLevi
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore map_perfectCore)
open CFSG.SeitzReduction.F4Pilot (HasBLift)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

section Coordinates

variable {G : Type*} [Group G] [Finite G] {φ φ' : unitaryPSU h n →* G}

theorem exists_le_map_comp_conj_rootSU2 (hn : 6 ≤ n) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') {i j : Fin n} (hij : i ≠ j)
    (hΛ : (perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n)))).map φ =
      (perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n)))).map φ')
    {a b : Fin n} (ha : a ∈ ({i, j}ᶜ : Finset (Fin n))) (hb : b ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hab : a ≠ b) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (rootSU2 h a b).map φ) :
    ∃ w : unitaryPSU h n, X ≤ (rootSU2 h a b).map (φ'.comp (MulAut.conj w).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := blockSU h ({i, j}ᶜ : Finset (Fin n)) with hMdef
  obtain ⟨Q, hQp, hΛeq, hQM, hMN, -⟩ := perfectCore_centralizer_stdTransvection h hn hij
  rw [hΛeq] at hΛ
  have hM := forall_normal_isPGroup_eq_bot_blockSU_compl_pair h hn hij
  have hJ : rootSU2 h a b ≤ M := rootSU2_le_blockSU h ha hb
  have hX2 : ¬ 2 ∣ Nat.card X := fun h2 => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h2)
  obtain ⟨hQeq, ι, -, q₀, hq₀, hXq⟩ := EPilot.exists_conj_le_map_of_two_decompositions hφ hφ' hQp
    hQp hM hM hMN hMN (disjoint_iff.2 hQM) (disjoint_iff.2 hQM) hΛ hJ hXJ hX2
  have hcard : ({i, j}ᶜ : Finset (Fin n)).card = n - 2 := card_compl_pair hij
  obtain ⟨g₀, -, hψ⟩ := exists_map_rootSU2_of_mulAut_blockSU h (by omega)
    (fun h3 => by have := h3.1; omega) (by omega) ι ha hb hab
  have hιJ : (((rootSU2 h a b).subgroupOf M).map ι.toMonoidHom).map M.subtype ≤
      (rootSU2 h a b).map (MulAut.conj g₀).toMonoidHom := by
    rw [hψ, subgroupOf_map_subtype]
    exact inf_le_left
  rw [hQeq] at hq₀
  obtain ⟨x₀, -, rfl⟩ := hq₀
  have e : ((MulAut.conj (φ' x₀)).toMonoidHom.comp φ').comp (MulAut.conj g₀).toMonoidHom =
      φ'.comp (MulAut.conj (x₀ * g₀)).toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    change φ' x₀ * φ' (g₀ * x * g₀⁻¹) * (φ' x₀)⁻¹ = φ' (x₀ * g₀ * x * (x₀ * g₀)⁻¹)
    simp only [map_mul, map_inv, _root_.mul_inv_rev]
    group
  refine ⟨x₀ * g₀, hXq.trans ((map_mono (map_mono hιJ)).trans_eq ?_)⟩
  rw [Subgroup.map_map, Subgroup.map_map, e]

end Coordinates

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
private theorem range_subtype_comp_symm' {C : Type*} [Group C] (e : L ≃* C) :
    (L.subtype.comp e.symm.toMonoidHom).range = L := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact (e.symm c).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp⟩

theorem exists_fused_le_map_rootSU2_of_seitzSetting (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSU2 h a b).map e.symm.toMonoidHom).map L.subtype) :
    ∃ g y : G,
      y ∈ ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype ∧
      orderOf y = 2 ∧ g⁻¹ * t * g = t * y ∧ y ∈ CFSG.conjugate L g ∧
      ∃ φ' : unitaryPSU h n →* G, Function.Injective φ' ∧ φ'.range = CFSG.conjugate L g ∧
        X ≤ (rootSU2 h a b).map φ' := by
  have := finite_unitaryPSU h n
  have hKt := inf_centralizer_eq_zpowers hset e (by omega) htC ht
  have hq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hOut := isSolvable_outer_of_mulEquiv h (by omega) hq e
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1
    (show 1 < ({a, b}ᶜ : Finset (Fin n)).card by rw [card_compl_pair hab]; omega)
  have haij : a ∈ ({i, j}ᶜ : Finset (Fin n)) :=
    mem_compl_of_ne (ne_left_of_mem_compl hi).symm (ne_left_of_mem_compl hj).symm
  have hbij : b ∈ ({i, j}ᶜ : Finset (Fin n)) :=
    mem_compl_of_ne (ne_right_of_mem_compl hi).symm (ne_right_of_mem_compl hj).symm
  obtain ⟨g, y, -, hg, ⟨hyL, hye⟩, ⟨hyL', hyT'⟩, hact⟩ :=
    exists_conj_eq_mul_stdTransvection h hset e hn ht hKt hij
  set φ : unitaryPSU h n →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := range_subtype_comp_symm' e
  have hmap : ∀ H : Subgroup (unitaryPSU h n),
      (H.map e.symm.toMonoidHom).map L.subtype = H.map φ := fun H => by rw [Subgroup.map_map]
  rw [hmap] at hXJ ⊢
  have hyφ : φ (stdTransvection h hij) = y := by
    rw [← hye]
    simp [hφdef]
  have hz2 : stdTransvection h hij * stdTransvection h hij = 1 := by
    rw [stdTransvection, ← map_mul, tvTransSU_mul_self, map_one]
  have hy2 : orderOf y = 2 := by
    rw [← hyφ, orderOf_injective φ hφ]
    exact orderOf_eq_prime (by rw [sq]; exact hz2) (stdTransvection_ne_one h hij)
  have hw' : y⁻¹ * t ∈ centralizer (CFSG.conjugate L g : Set G) :=
    EPilot.inv_mul_mem_centralizer_of_conj_eq hact
  have hΛeq := EPilot.perfectCore_inf_centralizer_eq_of_inv_mul_mem hset.standardSetting hOut
    htC ht (Or.inr hg) hw'
  set e' : CFSG.conjugate L g ≃* unitaryPSU h n := (conjugateMulEquiv L g).symm.trans e
    with he'
  obtain ⟨c', hc'⟩ := exists_conj_eq_stdTransvection h (by omega) hyT' hij
  set φ' : unitaryPSU h n →* G :=
    ((CFSG.conjugate L g).subtype.comp e'.symm.toMonoidHom).comp (MulAut.conj c'⁻¹).toMonoidHom
    with hφ'def
  have hφ' : Function.Injective φ' :=
    ((CFSG.conjugate L g).subtype_injective.comp e'.symm.injective).comp
      (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, range_subtype_comp_symm']
  have hconj : (MulAut.conj c'⁻¹) (stdTransvection h hij) = e' ⟨y, hyL'⟩ := by
    rw [← hc', MulAut.conj_apply, inv_inv]
    group
  have hφ'y : φ' (stdTransvection h hij) = y := by
    rw [hφ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hconj, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hΛ : (perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n)))).map φ =
      (perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n)))).map φ' := by
    rw [LinearPilot.map_perfectCore_centralizer_singleton hφ,
      LinearPilot.map_perfectCore_centralizer_singleton hφ', hφr, hφ'r, hyφ, hφ'y, hΛeq]
  obtain ⟨w, hXw⟩ := exists_le_map_comp_conj_rootSU2 h hn hφ hφ' hij hΛ haij hbij hab hXodd hXJ
  refine ⟨g, y, ⟨_, stdTransvection_mem_blockSU h hij hi hj, hyφ⟩, hy2, hg, hyL',
    φ'.comp (MulAut.conj w).toMonoidHom, hφ'.comp (MulAut.conj w).injective, ?_, hXw⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj w).surjective,
    ← MonoidHom.range_eq_map, hφ'r]

end Setting

section BLift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_centralizer_oddCore_of_le_rootSU2_of_seitzSetting (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (unitaryPSU h n)}
    (hX₀ : X₀ ≤ rootSU2 h a b) (hX₀o : Odd (Nat.card X₀)) (hX₀1 : X₀ ≠ ⊥) {X : Subgroup G}
    (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype,
      ∀ d ∈ D, c * d = d * c := by
  have hcard := card_compl_pair (n := n) hab
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have htX : t ∈ centralizer (X : Set G) := hX ▸ LinearPilot.mem_centralizer_map_symm e _ htC
  have hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) := by
    rw [hX, hDe]
    exact (layer_inf_centralizer_of_le_rootSU2 h e hn hab hX₀ hX₀o hX₀1).symm
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_blockSU h e (by omega) (by omega)
  have hZD : Odd (Nat.card (center D)) := by
    subst hDe
    rw [Nat.card_congr (centerCongr (LinearPilot.mapSymmMulEquiv e _)).toEquiv]
    exact odd_card_center_blockSU h (by omega)
  have hXodd : Odd (Nat.card X) := by
    rw [hX, LinearPilot.card_map_symm]
    exact hX₀o
  have hXJ : X ≤ ((rootSU2 h a b).map e.symm.toMonoidHom).map L.subtype :=
    hX ▸ map_mono (map_mono hX₀)
  have hXne : X ≠ ⊥ := by
    rw [hX, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
      map_eq_bot_iff_of_injective _ e.symm.injective]
    exact hX₀1
  obtain ⟨g, y, hyD, hy, hg, hyg, φ', hφ', hφ'r, hXφ'⟩ :=
    exists_fused_le_map_rootSU2_of_seitzSetting h hset e hn htC ht hab hXodd hXJ
  rw [← hDe] at hyD
  set X₀' : Subgroup (unitaryPSU h n) := X.comap φ' with hX₀'
  have hXeq : X = X₀'.map φ' := (map_comap_eq_self (hXφ'.trans (map_le_range _ _))).symm
  have hX₀'J : X₀' ≤ rootSU2 h a b := by
    have h1 := comap_mono (f := φ') hXφ'
    rwa [comap_map_eq_self_of_injective hφ'] at h1
  have hX₀'o : Odd (Nat.card X₀') := by
    rw [← card_map_of_injective hφ', ← hXeq]
    exact hXodd
  have hX₀'1 : X₀' ≠ ⊥ := fun hb => hXne (by rw [hXeq, hb, Subgroup.map_bot])
  have hyX : y ∈ centralizer (X : Set G) :=
    (show D ≤ L ⊓ centralizer (X : Set G) from hD ▸ map_subtype_le _) hyD |>.2
  have hyp : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hA := map_oddCore_range_inf_centralizer_le_centralizer h hφ' hφ'r hn hab hX₀'J hX₀'o hX₀'1
    hXeq hyg hyX hyp
  exact le_centralizer_oddCore_of_fused_of_centralizes htC ht hLt htX hD hDq hZD hyD hy hg hyg hA

theorem bLift_unitaryRootTorus_of_seitzSetting (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((unitaryRootTorus h hab).map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    t ∈ centralizer (X : Set G) ∧
      D.subgroupOf (centralizer (X : Set G)) ≤
          centralizer (oddCore (centralizer (X : Set G)) : Set (centralizer (X : Set G))) ∧
        ∀ K₁ K₂ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
          CFSG.IsComponent K₁ → CFSG.IsComponent K₂ →
          ⁅K₁, (D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))⁆ ≠ ⊥ →
          ⁅K₂, (D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))⁆ ≠ ⊥ →
          HasBLift K₁ ∧ HasBLift (K₁ ⊔ K₂) := by
  have htX : t ∈ centralizer (X : Set G) := hX ▸ LinearPilot.mem_centralizer_map_symm e _ htC
  have hmain := le_centralizer_oddCore_of_le_rootSU2_of_seitzSetting h hset e hn htC ht hab
    (unitaryRootTorus_le_rootSU2 h hab) (odd_card_unitaryRootTorus h hab)
    (unitaryRootTorus_ne_bot h (by omega) hab) hX hDe
  have hDO : D.subgroupOf (centralizer (X : Set G)) ≤
      centralizer (oddCore (centralizer (X : Set G)) : Set (centralizer (X : Set G))) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro c hc
    exact Subtype.ext (hmain c ⟨c, hc, rfl⟩ d (mem_subgroupOf.1 hd))
  exact ⟨htX, hDO, fun K₁ K₂ hK₁ hK₂ h₁ h₂ =>
    LinearPilot.hasBLift_of_isComponent_of_le_centralizer hDO hK₁ hK₂ h₁ h₂⟩

end BLift

end CFSG.SeitzReduction.UnitaryPilot
