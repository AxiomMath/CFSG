module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

section Transport

theorem isSubnormal_map_hom {H H' : Type*} [Group H] [Group H'] (f : H →* H')
    {A B : Subgroup H} (h : IsSubnormal A B) : IsSubnormal (A.map f) (B.map f) :=
  h.map f

theorem isComponentOf_map_mulEquiv' {H H' : Type*} [Group H] [Group H'] (φ : H ≃* H')
    {K C : Subgroup H} (h : IsComponentOf K C) :
    IsComponentOf (K.map φ.toMonoidHom) (C.map φ.toMonoidHom) := by
  obtain ⟨hKC, hs, hq⟩ := h
  refine ⟨Subgroup.map_mono hKC, isSubnormal_map_hom φ.toMonoidHom hs, ?_⟩
  rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (K.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hq

noncomputable abbrev conjEquivMap (X : Subgroup G) (g : G) :
    ↥X ≃* ↥(X.map (MulAut.conj g).toMonoidHom) :=
  X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

noncomputable abbrev conjQuotEquiv (p : ℕ) (X : Subgroup G) (g : G) :
    ↥X ⧸ LargeEvenPPrimeCore p ↥X ≃*
      ↥(X.map (MulAut.conj g).toMonoidHom) ⧸
        LargeEvenPPrimeCore p ↥(X.map (MulAut.conj g).toMonoidHom) :=
  QuotientGroup.congr _ _ (conjEquivMap X g) (map_largeEvenPPrimeCore p (conjEquivMap X g))

theorem subgroupOf_map_conj (M X : Subgroup G) (g : G) :
    (M.map (MulAut.conj g).toMonoidHom).subgroupOf (X.map (MulAut.conj g).toMonoidHom) =
      (M.subgroupOf X).map (conjEquivMap X g).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, hmy⟩
    obtain ⟨x, hx, hxy⟩ := y.2
    have hmx : m = x := (MulAut.conj g).injective (hmy.trans hxy.symm)
    refine ⟨⟨m, hmx ▸ hx⟩, hm, ?_⟩
    apply Subtype.ext
    exact hmy
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem image_map_conj' (p : ℕ) (M X : Subgroup G) (g : G) :
    ((M.map (MulAut.conj g).toMonoidHom).subgroupOf (X.map (MulAut.conj g).toMonoidHom)).map
        (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥(X.map (MulAut.conj g).toMonoidHom))) =
      ((M.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X))).map
        (conjQuotEquiv p X g).toMonoidHom := by
  rw [subgroupOf_map_conj, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem largeEvenPComponent_map_conj' {p : ℕ} {X K : Subgroup G} (h : LargeEvenPComponent p X K)
    (g : G) :
    LargeEvenPComponent p (X.map (MulAut.conj g).toMonoidHom)
      (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hKX, hsn, hcomp, hmin⟩ := h
  refine ⟨Subgroup.map_mono hKX, isSubnormal_map_conj hsn g, ?_, ?_⟩
  · rw [image_map_conj' p K X g]
    have := isComponentOf_map_mulEquiv' (conjQuotEquiv p X g) hcomp
    rwa [Subgroup.map_top_of_surjective (conjQuotEquiv p X g).toMonoidHom
      (conjQuotEquiv p X g).surjective] at this
  · intro J hJ hJsn heq
    have hJ' : (J.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = J :=
      map_conj_inv_map_conj J g
    have hlt : J.map (MulAut.conj g⁻¹).toMonoidHom < K := by
      rw [← map_conj_lt_map_conj_iff g, hJ']
      exact hJ
    have hsn' : IsSubnormal (J.map (MulAut.conj g⁻¹).toMonoidHom) X := by
      have := isSubnormal_map_conj hJsn g⁻¹
      rwa [map_conj_map_conj, inv_mul_cancel, show (MulAut.conj (1 : G)).toMonoidHom =
        MonoidHom.id G from by ext; simp, Subgroup.map_id] at this
    apply hmin _ hlt hsn'
    refine Subgroup.map_injective (f := (conjQuotEquiv p X g).toMonoidHom)
      (conjQuotEquiv p X g).injective ?_
    rw [← image_map_conj' p, ← image_map_conj' p, hJ']
    exact heq

theorem largeEvenPLayer_map_conj (p : ℕ) (X : Subgroup G) (g : G) :
    (LargeEvenPLayer p X).map (MulAut.conj g).toMonoidHom =
      LargeEvenPLayer p (X.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · unfold LargeEvenPLayer
    rw [(Subgroup.gc_map_comap _).l_sSup]
    exact iSup₂_le fun K hK => le_sSup (largeEvenPComponent_map_conj' hK g)
  · unfold LargeEvenPLayer
    refine sSup_le fun K' hK' => ?_
    have h1 := largeEvenPComponent_map_conj' hK' g⁻¹
    rw [map_conj_map_conj, inv_mul_cancel, show (MulAut.conj (1 : G)).toMonoidHom =
      MonoidHom.id G from by ext; simp, Subgroup.map_id] at h1
    rw [← map_conj_inv_map_conj K' g]
    exact Subgroup.map_mono (le_sSup h1)

end Transport

section Nbr

theorem closure_pair_eq_sup (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem centralizer_singleton_eq_of_zpowers_eq {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  rw [← Subgroup.centralizer_closure {a}, ← Subgroup.centralizer_closure {b},
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, h]

theorem mem_normalizer_inf {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH h, hK h]

variable [Finite G]

theorem largeEvenSHat_map_conj' {p : ℕ} {B : Subgroup G} {y : G} {K : Subgroup G}
    (h : LargeEvenSHat p B y K) {g : G} (hg : g ∈ Subgroup.normalizer (B : Set G)) :
    LargeEvenSHat p B (g * y * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hBmax, hyB, hy1, hKC, hpc, hiff⟩ := h
  have hC : (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) :=
    CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g y
  refine ⟨hBmax, (Subgroup.mem_normalizer_iff.mp hg y).mp hyB, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hy1
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [mul_assoc] using this
  · rw [← hC]
    exact Subgroup.map_mono hKC
  · rw [← hC]
    exact largeEvenPComponent_map_conj' hpc g
  · intro b
    have hbb' : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
    have hB : b ∈ B ↔ g⁻¹ * b * g ∈ B := Subgroup.mem_normalizer_iff''.mp hg b
    have hN : b ∈ Subgroup.normalizer
          ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
        g⁻¹ * b * g ∈ Subgroup.normalizer (K : Set G) := by
      rw [mem_normalizer_iff_map_conj, mem_normalizer_iff_map_conj, map_conj_map_conj,
        show b * g = g * (g⁻¹ * b * g) by group, ← map_conj_map_conj]
      exact (map_conj_injective g).eq_iff
    have hz : Subgroup.zpowers b =
        (Subgroup.zpowers (g⁻¹ * b * g)).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp [mul_assoc]
    have hC' : (⁅K.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers b⁆ : Subgroup G) ≤
          LargeEvenPPrimeCoreOf p (K.map (MulAut.conj g).toMonoidHom) ↔
        (⁅K, Subgroup.zpowers (g⁻¹ * b * g)⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
      rw [hz, ← Subgroup.map_commutator, largeEvenPPrimeCoreOf_map_conj,
        map_conj_le_map_conj_iff]
    have hy : b ∈ Subgroup.zpowers (g * y * g⁻¹) ↔ g⁻¹ * b * g ∈ Subgroup.zpowers y := by
      have hzy : Subgroup.zpowers (g * y * g⁻¹) =
          (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        simp
      rw [hzy, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [hB, hN, hC', hy]
    exact hiff _

omit [Finite G] in
theorem largeEvenNeighbor_map_conj {p : ℕ} {x y : G} {K D J : Subgroup G}
    (h : LargeEvenNeighbor p x y K D J) {g : G}
    (hgx : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hgJ : g ∈ Subgroup.normalizer (J : Set G)) :
    LargeEvenNeighbor p x (g * y * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) D J := by
  obtain ⟨hD, hKle, hnc⟩ := h
  have hzx : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x :=
    map_conj_eq_of_mem_normalizer hgx
  refine ⟨?_, ?_, ?_⟩
  · have hD' : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by rw [hD, closure_pair_eq_sup]
    rw [closure_pair_eq_sup, ← map_conj_eq_of_mem_normalizer hgD, hD', Subgroup.map_sup, hzx,
      MonoidHom.map_zpowers]
    rfl
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
    rw [map_conj_map_conj]
    have hga : g * a⁻¹ = (g * a * g⁻¹)⁻¹ * g := by group
    rw [hga, ← map_conj_map_conj, map_conj_eq_of_mem_normalizer hgJ]
  · rw [largeEvenPPrimeCoreOf_map_conj, ← hzx, ← Subgroup.map_commutator,
      map_conj_le_map_conj_iff]
    exact hnc

theorem ggNbr_map_conj' {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G} {y : G}
    {K : Subgroup G} (h : GGNbr p B x D J y K) {g : G}
    (hgB : g ∈ Subgroup.normalizer (B : Set G))
    (hgx : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hgJ : g ∈ Subgroup.normalizer (J : Set G)) :
    GGNbr p B x D J (g * y * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) :=
  ⟨largeEvenSHat_map_conj' h.1 hgB, largeEvenNeighbor_map_conj h.2 hgx hgD hgJ⟩

theorem map_conj_ggG0_le' {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G} {g : G}
    (hgB : g ∈ Subgroup.normalizer (B : Set G))
    (hgx : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgJ : g ∈ Subgroup.normalizer (J : Set G)) :
    (ggG0 p B x L D J).map (MulAut.conj g).toMonoidHom ≤ ggG0 p B x L D J := by
  unfold ggG0
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hgL]
  refine sup_le le_sup_left ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun y => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun K => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hK => ?_
  exact le_ggG0_of_ggNbr (L := L) (ggNbr_map_conj' hK hgB hgx hgD hgJ)

theorem mem_normalizer_of_sstar' {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) {g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hcomp := hS.2.2.2.1
  have hcomp' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp g
  have hCx : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({x} : Set G) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton]
    apply centralizer_singleton_eq_of_zpowers_eq
    have h1 : Subgroup.zpowers (g * x * g⁻¹) =
        (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp
    rw [h1]
    exact map_conj_eq_of_mem_normalizer hg
  rw [hCx] at hcomp'
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hcomp' hcomp with h | h
  · exact mem_normalizer_iff_map_conj.mpr h
  · exfalso
    obtain ⟨S, hSL, hSp, hSnc⟩ := hnc
    have hle : L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hcyc := hS.2.2.2.2 (S.map (MulAut.conj g).toMonoidHom)
      ((Subgroup.map_mono hSL).trans hle) (hSp.map _)
    exact hSnc (isCyclic_of_surjective
      (S.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
      (MulEquiv.surjective _))

theorem normalizer_inf_le_normalizer_ggG0 {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hDJ : LargeEvenStdSubPre p B x L D J) :
    Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set G) ⊓
        Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hNL : ∀ g ∈ Subgroup.normalizer (B : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers x : Set G) ⊓ Subgroup.normalizer (D : Set G),
      g ∈ Subgroup.normalizer (L : Set G) :=
    fun g hg => mem_normalizer_of_sstar' hS hnc hg.1.2
  have hNJ : Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set G) ⊓
      Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (J : Set G) := by
    rw [hDJ.2.2.2.2.1]
    exact le_normalizer_of_map_conj_le fun g hg => map_conj_largeEvenLayer_le
      (mem_normalizer_inf (hNL g hg) (normalizer_le_normalizer_centralizer D hg.2))
  exact le_normalizer_of_map_conj_le fun g hg =>
    map_conj_ggG0_le' hg.1.1 hg.1.2 hg.2 (hNL g hg) (hNJ hg)

omit [Finite G] in
theorem isQuasisimple_of_largeEvenMarking {K : Subgroup G} {P : LargeEvenMarkProp ↥K}
    (h : LargeEvenMarking ↥K P) : CFSG.Assembly.IsQuasisimple K := by
  obtain ⟨hK, lab, -, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, -, θ, -⟩ := largeEvenRawDatum_exists hraw
  exact ⟨hK, θ.isSimpleGroup⟩

theorem inf_centralizer_eq_zpowers_of_sHat {p : ℕ} {B : Subgroup G} {y : G} {K : Subgroup G}
    (h : LargeEvenSHat p B y K) :
    B ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  obtain ⟨-, hyB, -, hKC, -, hiff⟩ := h
  apply le_antisymm
  · intro b hb
    refine (hiff b).mp ⟨hb.1, Subgroup.centralizer_le_normalizer _ hb.2, ?_⟩
    have hz : Subgroup.zpowers b ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hb.2
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
    exact bot_le
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hyB, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)

theorem isNeighborOf_of_ggNbr {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hDJ : LargeEvenStdSub p B x L D J) (h : GGNbr p B x D J y K) :
    LargeEvenIsNeighborOf p B x L y K :=
  ⟨h.1, D, J, hDJ, h.2⟩

theorem isComponentOf_of_isNeighborOf {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G} {y : G}
    {K : Subgroup G} (hst : LargeEvenStandardType p B x L) (h : LargeEvenIsNeighborOf p B x L y K) :
    IsComponentOf K (Subgroup.centralizer ({y} : Set G)) ∧
      B ≤ Subgroup.normalizer (K : Set G) :=
  ⟨⟨h.1.2.2.2.1, h.1.2.2.2.2.1.2.1, isQuasisimple_of_largeEvenMarking (hst.2.2.1 y K h).2⟩,
    (hst.2.2.1 y K h).1⟩

end Nbr

end CFSG.StandardType
