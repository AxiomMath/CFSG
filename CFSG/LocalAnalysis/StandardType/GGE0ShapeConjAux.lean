module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem shapeConj_isElemAbelian_map_conj {G : Type} [Group G] {p : ℕ} {B : Subgroup G}
    (h : CFSG.Open.IsElemAbelian p B) (g : G) :
    CFSG.Open.IsElemAbelian p (B.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨IsMulCommutative.of_comm fun x y => ?_, ?_⟩
  · apply Subtype.ext
    obtain ⟨a, ha, hxa⟩ := x.2
    obtain ⟨b, hb, hxb⟩ := y.2
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hxb]
    simp only [MulEquiv.coe_toMonoidHom]
    haveI : IsMulCommutative B := h.1
    have hc : a * b = b * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : B) ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hc]
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [← map_pow, h.2 b hb, map_one]

theorem shapeConj_mem_normalizer_map_conj {G : Type} [Group G] {H : Subgroup G} {b g : G}
    (hb : b ∈ Subgroup.normalizer (H : Set G)) :
    g * b * g⁻¹ ∈ Subgroup.normalizer
      (H.map (MulAut.conj g).toMonoidHom : Set G) := by
  rw [Subgroup.mem_normalizer_iff''] at hb ⊢
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨b⁻¹ * y * b, (hb y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y, hy, hxy⟩
    refine ⟨b * y * b⁻¹, ?_, ?_⟩
    · refine (hb (b * y * b⁻¹)).mpr ?_
      have h1 : b⁻¹ * (b * y * b⁻¹) * b = y := by group
      rw [h1]
      exact hy
    · have hxy' : g * y * g⁻¹ = (g * b * g⁻¹)⁻¹ * x * (g * b * g⁻¹) := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxy
      have hx : x = g * b * g⁻¹ * (g * y * g⁻¹) * (g * b * g⁻¹)⁻¹ := by
        rw [hxy']
        group
      rw [hx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem shapeConj_map_centralizer {G : Type} [Group G] (H : Subgroup G) (g : G) :
    (Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∀ w ∈ H, w * y = y * w := fun w hw =>
      Subgroup.mem_centralizer_iff.mp hy w hw
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := hz
    have h := hy' w hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g * w * g⁻¹) * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
      _ = g * (y * w) * g⁻¹ := by rw [h]
      _ = (g * y * g⁻¹) * (g * w * g⁻¹) := by group
  · intro hx
    have hx' : ∀ w ∈ H.map (MulAut.conj g).toMonoidHom, w * x = x * w := fun w hw =>
      Subgroup.mem_centralizer_iff.mp hx w hw
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have h1 : g * w * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := ⟨w, hw, rfl⟩
      have h := hx' _ h1
      calc w * (g⁻¹ * x * g) = g⁻¹ * ((g * w * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * w * g⁻¹)) * g := by rw [h]
        _ = (g⁻¹ * x * g) * w := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem shapeConj_map_conj_inv_cancel {G : Type} [Group G] (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj, inv_mul_cancel]
  ext x
  simp [MulAut.conj_apply]

theorem shapeConj_map_conj_inv_cancel' {G : Type} [Group G] (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  rw [map_conj_map_conj, mul_inv_cancel,
    show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by ext; simp,
    Subgroup.map_id]

theorem shapeConj_map_center {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ∀ z, z * x = x * z := fun z => Subgroup.mem_center_iff.mp hx z
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hx' w]
  · intro hy
    have hy' : ∀ z, z * y = y * z := fun z => Subgroup.mem_center_iff.mp hy z
    refine ⟨e.symm y, Subgroup.mem_center_iff.mpr fun z => ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy' (e z)

theorem shapeConj_center_eq_bot_map_conj {G : Type} [Group G] (H : Subgroup G) (g : G) :
    (Subgroup.center (H.map (MulAut.conj g).toMonoidHom) = ⊥) ↔
      (Subgroup.center H = ⊥) := by
  rw [← shapeConj_map_center (conjEquivMap H g)]
  exact Subgroup.map_eq_bot_iff_of_injective (Subgroup.center H) (conjEquivMap H g).injective


theorem shapeConj_largeEvenLayer_map_conj {G : Type} [Group G] (H : Subgroup G) (g : G) :
    (LargeEvenLayer H).map (MulAut.conj g).toMonoidHom =
      LargeEvenLayer (H.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · unfold LargeEvenLayer
    rw [(Subgroup.gc_map_comap _).l_sSup]
    exact iSup₂_le fun K hK =>
      le_sSup (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK g)
  · unfold LargeEvenLayer
    refine sSup_le fun K' hK' => ?_
    have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK' g⁻¹
    rw [shapeConj_map_conj_inv_cancel H g] at h1
    rw [← shapeConj_map_conj_inv_cancel' K' g]
    exact Subgroup.map_mono (le_sSup (show K'.map (MulAut.conj g⁻¹).toMonoidHom ∈
      {K : Subgroup G | IsComponentOf K H} from h1))

theorem shapeConj_largeEvenHalfSplit_congr {p : ℕ} {lab : LargeEvenLabel} {P Q : Prop}
    (h : P ↔ Q) : LargeEvenHalfSplit p lab P ↔ LargeEvenHalfSplit p lab Q := by
  unfold LargeEvenHalfSplit
  rw [show P = Q from propext h]

theorem shapeConj_largeEvenIsU42_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    LargeEvenIsU42 X ↔ LargeEvenIsU42 Y := by
  constructor
  · rintro ⟨K, hK, hKfin, hcard, ⟨φ⟩⟩
    exact ⟨K, hK, hKfin, hcard, ⟨e.symm.trans φ⟩⟩
  · rintro ⟨K, hK, hKfin, hcard, ⟨φ⟩⟩
    exact ⟨K, hK, hKfin, hcard, ⟨e.trans φ⟩⟩

theorem shapeConj_largeEvenSmall_map_conj {G : Type} [Group G] (K : Subgroup G) (g : G) :
    LargeEvenSmall (K.map (MulAut.conj g).toMonoidHom) ↔ LargeEvenSmall K := by
  unfold LargeEvenSmall
  constructor
  · rintro (h | hφ)
    · exact Or.inl ((shapeConj_largeEvenIsU42_congr (conjEquivMap K g)).mpr h)
    · exact Or.inr ⟨(conjEquivMap K g).trans hφ.some⟩
  · rintro (h | hφ)
    · exact Or.inl ((shapeConj_largeEvenIsU42_congr (conjEquivMap K g)).mp h)
    · exact Or.inr ⟨(conjEquivMap K g).symm.trans hφ.some⟩

theorem shapeConj_largeEvenIsBmax_map_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} (h : LargeEvenIsBmax p B) (g : G) :
    LargeEvenIsBmax p (B.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hel, hcard, U, hU, hU2, hBU⟩ := h
  refine ⟨shapeConj_isElemAbelian_map_conj hel g, ?_,
    U.map (MulAut.conj g).toMonoidHom, ?_, hU2.map _, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  · intro hbot
    apply hU
    have h1 : (U.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = ⊥ := by
      rw [hbot, Subgroup.map_bot]
    rwa [shapeConj_map_conj_inv_cancel U g] at h1
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    exact shapeConj_mem_normalizer_map_conj (hBU hb)

theorem shapeConj_largeEvenSStar_map_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L : Subgroup G} (h : LargeEvenSStar p B x L) (g : G) :
    LargeEvenSStar p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
      (L.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hBmax, hxB, hx1, hcomp, hcyc⟩ := h
  refine ⟨shapeConj_largeEvenIsBmax_map_conj hBmax g, ⟨x, hxB, rfl⟩, ?_, ?_, ?_⟩
  · intro h1
    apply hx1
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [mul_assoc] using this
  · have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp g
    rwa [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton] at h1
  · intro S' hS' hSp
    have hS'' : S'.map (MulAut.conj g⁻¹).toMonoidHom ≤
        Subgroup.centralizer (L : Set G) := by
      have h1 : S'.map (MulAut.conj g⁻¹).toMonoidHom ≤
          (Subgroup.centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).map
            (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hS'
      rwa [← shapeConj_map_centralizer L g, map_conj_map_conj, inv_mul_cancel,
        show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by ext; simp,
        Subgroup.map_id] at h1
    haveI : IsCyclic ↥(S'.map (MulAut.conj g⁻¹).toMonoidHom) :=
      hcyc (S'.map (MulAut.conj g⁻¹).toMonoidHom) hS'' (hSp.map _)
    exact isCyclic_of_surjective ((conjEquivMap S' g⁻¹).symm).toMonoidHom
      (MulEquiv.surjective _)

theorem shapeConj_largeEvenStdSubPre_map_conj {G : Type} [Group G] {p : ℕ}
    {B : Subgroup G} {x : G} {L D K : Subgroup G} (h : LargeEvenStdSubPre p B x L D K)
    (g : G) :
    LargeEvenStdSubPre p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
      (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
      (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hDB, hel, hcard, hxD, hK, hcomp, hD⟩ := h
  refine ⟨Subgroup.map_mono hDB, shapeConj_isElemAbelian_map_conj hel g, ?_,
    ⟨x, hxD, rfl⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  · rw [hK, shapeConj_largeEvenLayer_map_conj,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective, shapeConj_map_centralizer]
  · have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp g
    rwa [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, shapeConj_map_centralizer] at h1
  · rw [hD, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, shapeConj_map_centralizer]

theorem shapeConj_largeEvenStdSub_map_conj {G : Type} [Group G] {p : ℕ}
    {B : Subgroup G} {x : G} {L D K : Subgroup G} (h : LargeEvenStdSub p B x L D K) (g : G) :
    LargeEvenStdSub p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
      (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
      (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hpre, hsmall⟩ := h
  refine ⟨shapeConj_largeEvenStdSubPre_map_conj hpre g, ?_⟩
  rintro ⟨hp3, D₁, K₁, hpre₁, hnsmall₁⟩
  have hpre₁' : LargeEvenStdSubPre p B x L
      (D₁.map (MulAut.conj g⁻¹).toMonoidHom) (K₁.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have h1 := shapeConj_largeEvenStdSubPre_map_conj hpre₁ g⁻¹
    have hx : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [shapeConj_map_conj_inv_cancel B g, shapeConj_map_conj_inv_cancel L g, hx] at h1
  have hnsmall₁' : ¬ LargeEvenSmall (K₁.map (MulAut.conj g⁻¹).toMonoidHom) := fun hs =>
    hnsmall₁ ((shapeConj_largeEvenSmall_map_conj K₁ g⁻¹).mp hs)
  have hK := hsmall ⟨hp3, _, _, hpre₁', hnsmall₁'⟩
  intro hs
  exact hK ((shapeConj_largeEvenSmall_map_conj K g).mp hs)

theorem shapeConj_largeEvenSHat_map_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {y : G} {K : Subgroup G} (h : LargeEvenSHat p B y K) (g : G) :
    LargeEvenSHat p (B.map (MulAut.conj g).toMonoidHom) (g * y * g⁻¹)
      (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hBmax, hyB, hy1, hKC, hpc, hiff⟩ := h
  have hC := CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g y
  refine ⟨shapeConj_largeEvenIsBmax_map_conj hBmax g, ⟨y, hyB, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hy1
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [mul_assoc] using this
  · rw [← hC]
    exact Subgroup.map_mono hKC
  · rw [← hC]
    exact largeEvenPComponent_map_conj' hpc g
  · intro b
    have hB : b ∈ B.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * b * g ∈ B := by
      constructor
      · rintro ⟨a, ha, haeq⟩
        have h2 : g⁻¹ * b * g = a := by
          rw [← haeq]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rwa [h2]
      · intro hb
        exact ⟨g⁻¹ * b * g, hb, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have hN : b ∈ Subgroup.normalizer
          ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
        g⁻¹ * b * g ∈ Subgroup.normalizer (K : Set G) := by
      rw [mem_normalizer_iff_map_conj, mem_normalizer_iff_map_conj, map_conj_map_conj,
        show b * g = g * (g⁻¹ * b * g) by group, ← map_conj_map_conj]
      exact (map_conj_injective g).eq_iff
    have hC' : (⁅K.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers b⁆ : Subgroup G) ≤
          LargeEvenPPrimeCoreOf p (K.map (MulAut.conj g).toMonoidHom) ↔
        (⁅K, Subgroup.zpowers (g⁻¹ * b * g)⁆ : Subgroup G) ≤
          LargeEvenPPrimeCoreOf p K := by
      rw [show Subgroup.zpowers b =
          (Subgroup.zpowers (g⁻¹ * b * g)).map (MulAut.conj g).toMonoidHom by
        rw [MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group,
        ← Subgroup.map_commutator, largeEvenPPrimeCoreOf_map_conj, map_conj_le_map_conj_iff]
    have hy : b ∈ Subgroup.zpowers (g * y * g⁻¹) ↔
        g⁻¹ * b * g ∈ Subgroup.zpowers y := by
      have hzy : Subgroup.zpowers (g * y * g⁻¹) =
          (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hzy, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [hB, hN, hC', hy]
    exact hiff (g⁻¹ * b * g)

theorem shapeConj_largeEvenNeighbor_map_conj {G : Type} [Group G] {p : ℕ} {x y : G}
    {K D J : Subgroup G} (h : LargeEvenNeighbor p x y K D J) (g : G) :
    LargeEvenNeighbor p (g * x * g⁻¹) (g * y * g⁻¹)
      (K.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
      (J.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hD, hKle, hnc⟩ := h
  have hzx : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨?_, ?_, ?_⟩
  · have hD' : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by rw [hD, closure_pair_eq_sup]
    rw [hD', Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      closure_pair_eq_sup]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · have hPL : LargeEvenPLayer p (Subgroup.centralizer ({g * y * g⁻¹} : Set G)) =
        (LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G))).map
          (MulAut.conj g).toMonoidHom := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g y,
        largeEvenPLayer_map_conj]
    refine (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKle).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    have hmem : g * a * g⁻¹ ∈
        LargeEvenPLayer p (Subgroup.centralizer ({g * y * g⁻¹} : Set G)) := by
      rw [hPL]
      exact ⟨a, ha, rfl⟩
    refine le_trans (le_of_eq ?_) (le_iSup_of_le (g * a * g⁻¹) (le_iSup_of_le hmem le_rfl))
    rw [map_conj_map_conj, map_conj_map_conj]
    congr 1
    group
  · rw [← hzx, ← Subgroup.map_commutator, largeEvenPPrimeCoreOf_map_conj,
      map_conj_le_map_conj_iff]
    exact hnc

theorem shapeConj_largeEvenIsNeighborOf_map_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L : Subgroup G} {y : G} {J : Subgroup G}
    (h : LargeEvenIsNeighborOf p B x L y J) (g : G) :
    LargeEvenIsNeighborOf p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
      (L.map (MulAut.conj g).toMonoidHom) (g * y * g⁻¹)
      (J.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hS, D, K, hsub, hnbr⟩ := h
  exact ⟨shapeConj_largeEvenSHat_map_conj hS g, D.map (MulAut.conj g).toMonoidHom,
    K.map (MulAut.conj g).toMonoidHom, shapeConj_largeEvenStdSub_map_conj hsub g,
    shapeConj_largeEvenNeighbor_map_conj hnbr g⟩

theorem shapeConj_conjEquivMap_symm_apply {G : Type} [Group G] (L : Subgroup G) (g : G)
    (z : ↥(L.map (MulAut.conj g).toMonoidHom)) :
    (((conjEquivMap L g).symm z : ↥L) : G) = g⁻¹ * (z : G) * g := by
  have h1 := Subgroup.coe_equivMapOfInjective_apply L (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective ((conjEquivMap L g).symm z)
  rw [MulEquiv.apply_symm_apply] at h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  rw [h1]
  group

theorem shapeConj_induces_rel_map_conj {G : Type} [Group G] (L : Subgroup G) (x g : G) :
    ∀ l l' : ↥(L.map (MulAut.conj g).toMonoidHom),
      ((l' : G) = (g * x * g⁻¹)⁻¹ * (l : G) * (g * x * g⁻¹)) ↔
        (((conjEquivMap L g).symm l' : G) = x⁻¹ * ((conjEquivMap L g).symm l : G) * x) := by
  intro l l'
  rw [shapeConj_conjEquivMap_symm_apply L g l', shapeConj_conjEquivMap_symm_apply L g l]
  constructor
  · intro hh
    rw [hh]
    group
  · intro hh
    calc (l' : G) = g * (g⁻¹ * (l' : G) * g) * g⁻¹ := by group
      _ = g * (x⁻¹ * (g⁻¹ * (l : G) * g) * x) * g⁻¹ := by rw [hh]
      _ = (g * x * g⁻¹)⁻¹ * (l : G) * (g * x * g⁻¹) := by group

theorem shapeConj_largeEvenMarking_map_conj {G : Type} [Group G] (g : G) {L : Subgroup G}
    {P : LargeEvenMarkProp ↥L} {Pc : LargeEvenMarkProp ↥(L.map (MulAut.conj g).toMonoidHom)}
    (h : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* R), P lab R I F θ →
      Pc lab R I F ((centerQuotCongr (conjEquivMap L g).symm).trans θ))
    (hm : LargeEvenMarking ↥L P) :
    LargeEvenMarking ↥(L.map (MulAut.conj g).toMonoidHom) Pc :=
  largeEvenMarking_congr (conjEquivMap L g).symm h hm

theorem shapeConj_largeEvenStandardType_map_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L : Subgroup G} (h : LargeEvenStandardType p B x L) (g : G) :
    LargeEvenStandardType p (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
      (L.map (MulAut.conj g).toMonoidHom) := by
  unfold LargeEvenStandardType LargeEvenStandardTypeOfLegacy at h ⊢
  obtain ⟨hL, hT, hNbr, hStd⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine shapeConj_largeEvenMarking_map_conj g ?_ hL
    intro lab R _ I F θ hP
    obtain ⟨hsplit, hBnorm, hInd⟩ := hP
    refine ⟨hsplit, ?_, ?_⟩
    · intro b' hb'
      obtain ⟨b, hb, rfl⟩ := hb'
      exact shapeConj_mem_normalizer_map_conj (hBnorm hb)
    · intro b' hb'
      obtain ⟨b, hb, rfl⟩ := hb'
      obtain ⟨φ, hφ, hind⟩ := hInd b hb
      refine ⟨φ, hφ, ?_⟩
      exact (largeEvenInduces_congr_equiv (conjEquivMap L g).symm θ _
        _ (shapeConj_induces_rel_map_conj L b g) φ).mpr hind
  · obtain ⟨T, hTC, hT2, hTB, hTne⟩ := hT
    refine ⟨T.map (MulAut.conj g).toMonoidHom, ?_, hT2.map _, ?_, ?_⟩
    · rw [← CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g x]
      exact Subgroup.map_mono hTC
    · intro b' hb'
      obtain ⟨b, hb, rfl⟩ := hb'
      exact shapeConj_mem_normalizer_map_conj (hTB hb)
    · rw [← Subgroup.map_commutator]
      intro hbot
      exact hTne ((Subgroup.map_eq_bot_iff_of_injective (⁅T, B⁆ : Subgroup G)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mp hbot)
  · intro y' J' hy'
    have hback : LargeEvenIsNeighborOf p B x L (g⁻¹ * y' * g)
        (J'.map (MulAut.conj g⁻¹).toMonoidHom) := by
      have h1 := shapeConj_largeEvenIsNeighborOf_map_conj hy' g⁻¹
      have hx : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      have hy : g⁻¹ * y' * g⁻¹⁻¹ = g⁻¹ * y' * g := by group
      rwa [shapeConj_map_conj_inv_cancel B g, shapeConj_map_conj_inv_cancel L g, hx, hy] at h1
    obtain ⟨hBN, hMark⟩ := hNbr (g⁻¹ * y' * g) (J'.map (MulAut.conj g⁻¹).toMonoidHom) hback
    refine ⟨?_, ?_⟩
    · intro b' hb'
      obtain ⟨b, hb, rfl⟩ := hb'
      have h1 := shapeConj_mem_normalizer_map_conj
        (H := J'.map (MulAut.conj g⁻¹).toMonoidHom) (b := b) (g := g) (hBN hb)
      rwa [shapeConj_map_conj_inv_cancel' J' g] at h1
    · rw [← shapeConj_map_conj_inv_cancel' J' g]
      refine shapeConj_largeEvenMarking_map_conj
        (L := J'.map (MulAut.conj g⁻¹).toMonoidHom) g ?_ hMark
      intro lab R _ I F θ hP
      rcases hP with hP | hP
      · exact Or.inl ((shapeConj_largeEvenHalfSplit_congr
          (shapeConj_center_eq_bot_map_conj (J'.map (MulAut.conj g⁻¹).toMonoidHom) g)).mpr hP)
      · obtain ⟨hne, f, hfF, u, huI, hford, hisα⟩ := hP
        refine Or.inr ⟨hne, f, hfF, u, huI, hford, ?_⟩
        exact (largeEvenInduces_congr_equiv (conjEquivMap
          (J'.map (MulAut.conj g⁻¹).toMonoidHom) g).symm θ _ _
          (shapeConj_induces_rel_map_conj (J'.map (MulAut.conj g⁻¹).toMonoidHom) x g)
          _).mpr hisα
  · intro D' K' hsub
    have hback : LargeEvenStdSub p B x L (D'.map (MulAut.conj g⁻¹).toMonoidHom)
        (K'.map (MulAut.conj g⁻¹).toMonoidHom) := by
      have h1 := shapeConj_largeEvenStdSub_map_conj hsub g⁻¹
      have hx : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [shapeConj_map_conj_inv_cancel B g, shapeConj_map_conj_inv_cancel L g, hx] at h1
    obtain ⟨⟨y, J, hyJ, hnbr⟩, hodd⟩ := hStd _ _ hback
    refine ⟨⟨g * y * g⁻¹, J.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩, ?_⟩
    · exact shapeConj_largeEvenSHat_map_conj hyJ g
    · have h1 := shapeConj_largeEvenNeighbor_map_conj hnbr g
      rwa [shapeConj_map_conj_inv_cancel' D' g, shapeConj_map_conj_inv_cancel' K' g] at h1
    · intro d' hd' hd'1
      rw [← shapeConj_map_conj_inv_cancel' D' g] at hd'
      obtain ⟨d, hd, rfl⟩ := hd'
      have hd1 : d ≠ 1 := by
        intro hh
        apply hd'1
        simp only [hh, map_one]
      have h1 := hodd d hd hd1
      have hmap : (⁅K', LargeEvenPPrimeCoreOf p
            (Subgroup.centralizer ({(MulAut.conj g).toMonoidHom d} : Set G))⁆ : Subgroup G) =
          (⁅K'.map (MulAut.conj g⁻¹).toMonoidHom, LargeEvenPPrimeCoreOf p
            (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G).map
            (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_commutator, shapeConj_map_conj_inv_cancel' K' g,
          ← largeEvenPPrimeCoreOf_map_conj,
          CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact h1

end CFSG.StandardType
