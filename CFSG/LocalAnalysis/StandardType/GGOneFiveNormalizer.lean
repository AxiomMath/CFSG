module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

section Conj

theorem le_normalizer_of_map_conj_le {S H : Subgroup G}
    (h : ∀ g ∈ S, H.map (MulAut.conj g).toMonoidHom ≤ H) :
    S ≤ Subgroup.normalizer (H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact h g hg ⟨k, hk, rfl⟩
  · intro hk
    have := h g⁻¹ (S.inv_mem hg) ⟨g * k * g⁻¹, hk, rfl⟩
    simpa [mul_assoc] using this

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

theorem map_conj_eq_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H :=
  map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)

theorem map_conj_map_conj (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext k
  simp [mul_assoc]

theorem mem_normalizer_iff_map_conj {H : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ H.map (MulAut.conj g).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem map_conj_inv_map_conj (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  rw [map_conj_map_conj, mul_inv_cancel]
  ext k
  simp

theorem map_conj_injective (g : G) :
    Function.Injective (fun H : Subgroup G => H.map (MulAut.conj g).toMonoidHom) :=
  Subgroup.map_injective (MulAut.conj g).injective

theorem map_conj_le_map_conj_iff {H K : Subgroup G} (g : G) :
    H.map (MulAut.conj g).toMonoidHom ≤ K.map (MulAut.conj g).toMonoidHom ↔ H ≤ K :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem map_conj_lt_map_conj_iff {H K : Subgroup G} (g : G) :
    H.map (MulAut.conj g).toMonoidHom < K.map (MulAut.conj g).toMonoidHom ↔ H < K := by
  simp only [lt_iff_le_not_ge, map_conj_le_map_conj_iff]

theorem zpowers_map_conj_of_commute {b g : G} (h : g * b = b * g) :
    (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers b := by
  rw [MonoidHom.map_zpowers]
  congr 1
  simp [h, mul_assoc]

theorem centralizer_map_conj_of_commute {y g : G} (h : g * y = y * g) :
    (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) := by
  apply map_conj_eq_of_mem
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h

theorem isSubnormal_map_conj {A B : Subgroup G} (h : IsSubnormal A B) (g : G) :
    IsSubnormal (A.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom) :=
  h.map (MulAut.conj g).toMonoidHom

end Conj

section PCore

theorem map_largeEvenPPrimeCore {H H' : Type*} [Group H] [Group H'] (p : ℕ) (e : H ≃* H') :
    (LargeEvenPPrimeCore p H).map e.toMonoidHom = LargeEvenPPrimeCore p H' := by
  unfold LargeEvenPPrimeCore CFSG.pPrimeCore
  rw [(Subgroup.gc_map_comap e.toMonoidHom).l_sSup]
  apply le_antisymm
  · refine iSup₂_le fun N hN => le_sSup ⟨hN.1.map _ e.surjective, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective]
    exact hN.2
  · refine sSup_le fun N' hN' => ?_
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N']
    refine le_iSup₂_of_le (N'.comap e.toMonoidHom) ⟨hN'.1.comap _, ?_⟩ le_rfl
    have hc : N'.comap e.toMonoidHom = N'.map e.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm e N'
    rw [hc, Subgroup.card_map_of_injective e.symm.injective]
    exact hN'.2

theorem largeEvenPPrimeCoreOf_map_conj (p : ℕ) (K : Subgroup G) (g : G) :
    LargeEvenPPrimeCoreOf p (K.map (MulAut.conj g).toMonoidHom) =
      (LargeEvenPPrimeCoreOf p K).map (MulAut.conj g).toMonoidHom := by
  set e : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) :=
    K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  unfold LargeEvenPPrimeCoreOf
  rw [← map_largeEvenPPrimeCore p e, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem image_map_conj (p : ℕ) {X : Subgroup G} {g : G} (hg : g ∈ X) (M : Subgroup G) :
    ((M.map (MulAut.conj g).toMonoidHom).subgroupOf X).map
        (QuotientGroup.mk' (LargeEvenPPrimeCore p X)) =
      ((M.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p X))).map
        (MulAut.conj (QuotientGroup.mk' (LargeEvenPPrimeCore p X) ⟨g, hg⟩)).toMonoidHom := by
  have hsub : (M.map (MulAut.conj g).toMonoidHom).subgroupOf X =
      (M.subgroupOf X).map (MulAut.conj (⟨g, hg⟩ : ↥X)).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨m, hm, hmy⟩
      refine ⟨⟨g⁻¹ * y * g, X.mul_mem (X.mul_mem (X.inv_mem hg) y.2) hg⟩, ?_, ?_⟩
      · change g⁻¹ * (y : G) * g ∈ M
        rw [← hmy]
        simpa [mul_assoc] using hm
      · apply Subtype.ext
        simp [mul_assoc]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [hsub, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem largeEvenPComponent_map_conj {p : ℕ} {X K : Subgroup G} (h : LargeEvenPComponent p X K)
    {g : G} (hg : g ∈ X) : LargeEvenPComponent p X (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hKX, hsn, hcomp, hmin⟩ := h
  have hX : X.map (MulAut.conj g).toMonoidHom = X := map_conj_eq_of_mem hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hX ▸ Subgroup.map_mono hKX
  · have := isSubnormal_map_conj hsn g
    rwa [hX] at this
  · rw [image_map_conj p hg K]
    have := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp
      (QuotientGroup.mk' (LargeEvenPPrimeCore p X) ⟨g, hg⟩)
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj _).surjective] at this
  · intro J hJ hJsn heq
    have hJ' : (J.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = J :=
      map_conj_inv_map_conj J g
    have hlt : J.map (MulAut.conj g⁻¹).toMonoidHom < K := by
      rw [← map_conj_lt_map_conj_iff g, hJ']
      exact hJ
    have hsn' : IsSubnormal (J.map (MulAut.conj g⁻¹).toMonoidHom) X := by
      have := isSubnormal_map_conj hJsn g⁻¹
      rwa [map_conj_eq_of_mem (X.inv_mem hg)] at this
    apply hmin _ hlt hsn'
    refine map_conj_injective (QuotientGroup.mk' (LargeEvenPPrimeCore p X) ⟨g, hg⟩) ?_
    dsimp only
    rw [← image_map_conj p hg, ← image_map_conj p hg, hJ']
    exact heq

theorem largeEvenPLayer_map_conj_le {p : ℕ} {X : Subgroup G} {g : G} (hg : g ∈ X) :
    (LargeEvenPLayer p X).map (MulAut.conj g).toMonoidHom ≤ LargeEvenPLayer p X := by
  unfold LargeEvenPLayer
  rw [(Subgroup.gc_map_comap _).l_sSup]
  exact iSup₂_le fun K hK => le_sSup (largeEvenPComponent_map_conj hK hg)

theorem conj_mem_largeEvenPLayer {p : ℕ} {X : Subgroup G} {g a : G} (hg : g ∈ X)
    (ha : a ∈ LargeEvenPLayer p X) : g * a * g⁻¹ ∈ LargeEvenPLayer p X :=
  largeEvenPLayer_map_conj_le hg ⟨a, ha, rfl⟩

theorem map_conj_largeEvenLayer_le {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    (LargeEvenLayer H).map (MulAut.conj g).toMonoidHom ≤ LargeEvenLayer H := by
  unfold LargeEvenLayer
  rw [(Subgroup.gc_map_comap _).l_sSup]
  refine iSup₂_le fun K hK => le_sSup ?_
  have := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK g
  rwa [map_conj_eq_of_mem_normalizer hg] at this

end PCore

section Nbr

variable [Finite G]

theorem largeEvenSHat_map_conj {p : ℕ} {B : Subgroup G} {y : G} {K : Subgroup G}
    (h : LargeEvenSHat p B y K) {g : G} (hg : g ∈ Subgroup.centralizer (B : Set G)) :
    LargeEvenSHat p B y (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hBmax, hyB, hy1, hKC, hpc, hiff⟩ := h
  have hcomm : ∀ b ∈ B, g * b = b * g := fun b hb =>
    ((Subgroup.mem_centralizer_iff.mp hg) b hb).symm
  have hgC : g ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hyB)
  refine ⟨hBmax, hyB, hy1, ?_, largeEvenPComponent_map_conj hpc hgC, ?_⟩
  · rw [← map_conj_eq_of_mem hgC]
    exact Subgroup.map_mono hKC
  · intro b
    by_cases hb : b ∈ B
    · rw [← hiff b]
      have hgb := hcomm b hb
      have hN : b ∈ Subgroup.normalizer
            ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
          b ∈ Subgroup.normalizer (K : Set G) := by
        rw [mem_normalizer_iff_map_conj, mem_normalizer_iff_map_conj, map_conj_map_conj, ← hgb,
          ← map_conj_map_conj]
        exact (map_conj_injective g).eq_iff
      have hC : (⁅K.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers b⁆ : Subgroup G) ≤
            LargeEvenPPrimeCoreOf p (K.map (MulAut.conj g).toMonoidHom) ↔
          (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
        rw [largeEvenPPrimeCoreOf_map_conj]
        conv_lhs => rw [← zpowers_map_conj_of_commute hgb, ← Subgroup.map_commutator]
        exact map_conj_le_map_conj_iff g
      rw [hN, hC]
    · exact ⟨fun h => absurd h.1 hb, fun h => absurd ((hiff b).mpr h).1 hb⟩

theorem ggNbr_map_conj {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G} {y : G}
    {K : Subgroup G} (h : GGNbr p B x D J y K) (hx : x ∈ B) {g : G}
    (hg : g ∈ Subgroup.centralizer (B : Set G)) (hgJ : g ∈ Subgroup.normalizer (J : Set G)) :
    GGNbr p B x D J y (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hS, hD, hKle, hnc⟩ := h
  have hcomm : ∀ b ∈ B, g * b = b * g := fun b hb =>
    ((Subgroup.mem_centralizer_iff.mp hg) b hb).symm
  have hgC : g ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hS.2.1)
  refine ⟨largeEvenSHat_map_conj hS hg, hD, ?_, ?_⟩
  · refine (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKle).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    have hmem : g * a * g⁻¹ ∈ LargeEvenPLayer p (Subgroup.centralizer ({y} : Set G)) :=
      conj_mem_largeEvenPLayer hgC ha
    refine le_trans (le_of_eq ?_) (le_iSup_of_le (g * a * g⁻¹) (le_iSup_of_le hmem le_rfl))
    rw [map_conj_map_conj]
    have hga : g * a⁻¹ = (g * a * g⁻¹)⁻¹ * g := by group
    rw [hga, ← map_conj_map_conj, map_conj_eq_of_mem_normalizer hgJ]
  · rw [largeEvenPPrimeCoreOf_map_conj, ← zpowers_map_conj_of_commute (hcomm x hx),
      ← Subgroup.map_commutator, map_conj_le_map_conj_iff]
    exact hnc

theorem map_conj_ggG0_le {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G} (hx : x ∈ B)
    {g : G} (hg : g ∈ Subgroup.centralizer (B : Set G))
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgJ : g ∈ Subgroup.normalizer (J : Set G)) :
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
  exact le_ggG0_of_ggNbr (L := L) (ggNbr_map_conj hK hx hg hgJ)

theorem mem_normalizer_of_sstar {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) {g : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) : g ∈ Subgroup.normalizer (L : Set G) := by
  have hcomp := hS.2.2.2.1
  have hcomp' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcomp g
  rw [map_conj_eq_of_mem hg] at hcomp'
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

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {L D : Subgroup G} {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgD : g ∈ Subgroup.centralizer (D : Set G)) :
    g ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hgL ⊢
  have hgD' := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hgD)
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hgL h, hgD' h]

theorem centralizer_le_normalizer_ggG0 {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hDJ : LargeEvenStdSubPre p B x L D J) :
    Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hx : x ∈ B := hS.2.1
  have hCx : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)
  have hCD : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le hDJ.1
  have hNL : ∀ g ∈ Subgroup.centralizer (B : Set G), g ∈ Subgroup.normalizer (L : Set G) :=
    fun g hg => mem_normalizer_of_sstar hS hnc (hCx hg)
  have hNJ : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (J : Set G) := by
    rw [hDJ.2.2.2.2.1]
    exact le_normalizer_of_map_conj_le fun g hg =>
      map_conj_largeEvenLayer_le (mem_normalizer_inf_centralizer (hNL g hg) (hCD hg))
  exact le_normalizer_of_map_conj_le fun g hg => map_conj_ggG0_le hx hg (hNL g hg) (hNJ hg)

theorem bstar_le_normalizer_ggG0 {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hDJ : LargeEvenStdSubPre p B x L D J) (hBs : GGBstar p B Bs) :
    Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
  hBs.le_centralizer.trans (centralizer_le_normalizer_ggG0 hS hnc hDJ)

end Nbr

section Frattini

open scoped Pointwise

variable [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (B : Subgroup G) :
    Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun k hk => ?_
  rintro _ ⟨h, hh, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hh
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : k⁻¹ * b * k ∈ B := (Subgroup.mem_normalizer_iff''.mp hk b).mp hb
  have hc := hh _ hb'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc b * (k * h * k⁻¹) = k * ((k⁻¹ * b * k) * h) * k⁻¹ := by group
    _ = k * (h * (k⁻¹ * b * k)) * k⁻¹ := by rw [hc]
    _ = k * h * k⁻¹ * b := by group

theorem normalizer_le_of_frattini {p : ℕ} (hp : p.Prime) {B Bs H : Subgroup G}
    (hBs : GGBstar p B Bs)
    (hΩ : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (B : Set G) → IsPGroup p P → Bs ≤ P →
      ∀ g ∈ P, g ^ p = 1 → g ∈ Bs)
    (hC : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (H : Set G))
    (hN : Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (H : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  intro g hg
  set C := Subgroup.centralizer (B : Set G) with hCdef
  have hgC : C.map (MulAut.conj g).toMonoidHom = C :=
    map_conj_eq_of_mem_normalizer (normalizer_le_normalizer_centralizer B hg)
  have hBsC : Bs ≤ C := hBs.le_centralizer
  have hBsG : IsPGroup p Bs := fun b => ⟨1, Subtype.ext (by simpa using hBs.2.1.2 b b.2)⟩
  have hBsp : IsPGroup p (Bs.subgroupOf C) :=
    hBsG.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨Q, hQ⟩ := hBsp.exists_le_sylow
  let φ : MulAut ↥C := ((MulAut.conj g).subgroupMap C).trans (MulEquiv.subgroupCongr hgC)
  have hφ : ∀ c : ↥C, ((φ c : ↥C) : G) = g * c * g⁻¹ := fun _ => rfl
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C (φ • Q) Q
  set P : Subgroup G := (Q : Subgroup ↥C).map C.subtype with hPdef
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := Q.isPGroup'.map C.subtype
  have hBsP : Bs ≤ P := fun b hb => ⟨⟨b, hBsC hb⟩, hQ hb, rfl⟩
  have hmemP : ∀ b ∈ Bs, (c : G) * g * b * ((c : G) * g)⁻¹ ∈ P := by
    intro b hb
    have h1 : φ • (⟨b, hBsC hb⟩ : ↥C) ∈ φ • (Q : Subgroup ↥C) :=
      Subgroup.smul_mem_pointwise_smul _ φ _ (hQ hb)
    have h2 : MulAut.conj c • (φ • (⟨b, hBsC hb⟩ : ↥C)) ∈
        MulAut.conj c • (φ • (Q : Subgroup ↥C)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    have h3 : MulAut.conj c • (φ • (⟨b, hBsC hb⟩ : ↥C)) ∈ ((c • φ • Q : Sylow p ↥C) :
        Subgroup ↥C) := h2
    rw [hc] at h3
    refine ⟨_, h3, ?_⟩
    simp only [Subgroup.coe_subtype, MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, hφ]
    group
  have hcg : (c : G) * g ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [mem_normalizer_iff_map_conj]
    have hle : Bs.map (MulAut.conj ((c : G) * g)).toMonoidHom ≤ Bs := by
      rintro _ ⟨b, hb, rfl⟩
      refine hΩ P hPC hPp hBsP _ (hmemP b hb) ?_
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hBs.2.1.2 b hb, mul_one, mul_inv_cancel]
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj ((c : G) * g)).injective).ge
  have := (Subgroup.normalizer (H : Set G)).mul_mem
    ((Subgroup.normalizer (H : Set G)).inv_mem (hC c.2)) (hN hcg)
  simpa [mul_assoc] using this

end Frattini

end CFSG.StandardType
