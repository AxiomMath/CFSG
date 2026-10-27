module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Orbits
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Numerics
import CFSG.GH74.GLS.IVK.L2.BorelSylow
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Dim
public import CFSG.Sporadic.Schreier.J4SSylowBase
import CFSG.CharacterTheory.PSL2Table.Classes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open Subgroup CFSG.Quasithin
open scoped MatrixGroups
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {p e : ℕ}

omit [Finite G] in
private theorem model_psl2 (hM : LieModel ↥L .PSL 2 p e) :
    p.Prime ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ e ∧
      Nonempty (↥L ≃* CFSG.GorensteinWalter.PSL2 F) := by
  obtain ⟨hp, -, -, -, F, hF, hFin, hcard, hφ⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hM
  exact ⟨hp, F, hF, hFin, hcard, hφ⟩

theorem exists_isSylowIn (hM : LieModel ↥L .PSL 2 p e) : ∃ E : Subgroup G, IsSylowIn p E L := by
  obtain ⟨hp, -⟩ := model_psl2 hM
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p ↥L := default
  have hle : P.toSubgroup.map L.subtype ≤ L := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  refine ⟨P.toSubgroup.map L.subtype, hle, P.isPGroup'.map L.subtype, ?_⟩
  have hidx : (P.toSubgroup.map L.subtype).index = P.toSubgroup.index * L.index :=
    Subgroup.index_map_subtype (H := L) P.toSubgroup
  have hrel :
      (P.toSubgroup.map L.subtype).relIndex L * L.index = P.toSubgroup.index * L.index := by
    rw [Subgroup.relIndex_mul_index hle, hidx]
  have hL : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpd : (P.toSubgroup.map L.subtype).relIndex L = P.toSubgroup.index :=
    Nat.mul_right_cancel (Nat.pos_of_ne_zero hL) hrel
  have : P.toSubgroup.FiniteIndex := Subgroup.FiniteIndex.mk Subgroup.index_ne_zero_of_finite
  rw [hpd]
  exact P.not_dvd_index

private theorem unip_pow' {F : Type} [Field F] (t : F) (n : ℕ) :
    CFSG.PSL2Table.unip t ^ n = CFSG.PSL2Table.unip ((n : F) * t) := by
  induction n with
  | zero => simp [CFSG.PSL2Table.unip_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← CFSG.PSL2Table.unip_add]
    push_cast
    congr 1
    ring

private theorem isElemAbelian_unipotent {F : Type} [Field F] {p : ℕ} [CharP F p] :
    CFSG.Open.IsElemAbelian p (CFSG.PSL2Table.unipotent F) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (CFSG.PSL2Table.unipotent_mul_comm a.2 b.2)
  · obtain ⟨t, rfl⟩ :=
      (CFSG.PSL2Table.mem_unipotent_iff_exists (x : CFSG.GorensteinWalter.PSL2 F)).mp hx
    rw [← map_pow, unip_pow' t p, CharP.cast_eq_zero, zero_mul, CFSG.PSL2Table.unip_zero,
      map_one]

private theorem exists_conj_sylow_image {F : Type} [Field F] [Finite F] {p n : ℕ}
    [Fact p.Prime] (hcard : Nat.card F = p ^ n) (φ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F)
    {E : Subgroup G} (hE : IsSylowIn p E L) :
    ∃ c : CFSG.GorensteinWalter.PSL2 F,
      Subgroup.map (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F) (hE.toSylow : Subgroup ↥L) =
        Subgroup.map (MulAut.conj c).toMonoidHom (CFSG.PSL2Table.unipotent F) := by
  have hWpg : IsPGroup p (Subgroup.map (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F)
      (hE.toSylow : Subgroup ↥L)) := (hE.toSylow).isPGroup'.map _
  have hidx : ¬ p ∣ (Subgroup.map (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F)
      (hE.toSylow : Subgroup ↥L)).index := by
    rw [Subgroup.index_map_equiv]
    exact Sylow.not_dvd_index hE.toSylow
  let W : Sylow p (CFSG.GorensteinWalter.PSL2 F) := hWpg.toSylow hidx
  have hWcoe : (W : Subgroup (CFSG.GorensteinWalter.PSL2 F)) =
      Subgroup.map (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F) (hE.toSylow : Subgroup ↥L) :=
    IsPGroup.toSylow_coe hWpg hidx
  obtain ⟨c, hc⟩ := CFSG.GH74.GLS.IVK.L2Borel.exists_conj_eq_unipotent hcard W
  exact ⟨c, by rw [← hWcoe]; exact hc⟩

private theorem diag_conj_unipotent_pow {F : Type} [Field F] {a : Fˣ} {m : ℕ}
    (hm : (m : F) = (a : F) ^ 2) {u : CFSG.GorensteinWalter.PSL2 F}
    (hu : u ∈ CFSG.PSL2Table.unipotent F) :
    CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a) * u *
        (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a))⁻¹ = u ^ m := by
  obtain ⟨t, rfl⟩ := (CFSG.PSL2Table.mem_unipotent_iff_exists u).mp hu
  rw [← map_pow, unip_pow' t m, CFSG.PSL2Table.mk_conj, CFSG.PSL2Table.diag_conj_unip, ← hm]

theorem isElemAbelian_of_isSylowIn (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2)
    {E : Subgroup G} (hE : IsSylowIn p E L) :
    CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ e := by
  obtain ⟨hp, F, hF, hFin, hcard, ⟨φ⟩⟩ := model_psl2 hM
  let := hF
  let := hFin
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hFcard : Fintype.card F = p ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have : CharP F p := charP_of_card_eq_prime_pow hFcard
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hle hp.two_le)
  let P : Sylow p ↥L := hE.toSylow
  have hPcoe : (P : Subgroup ↥L) = E.subgroupOf L :=
    IsSylowIn.coe_toSylow (p := p) (P := E) (H := L) hE
  have hEeq : (P : Subgroup ↥L).map L.subtype = E := by
    rw [hPcoe]
    exact Subgroup.map_subgroupOf_eq_of_le hE.le
  let Wsub : Subgroup (CFSG.GorensteinWalter.PSL2 F) :=
    (P : Subgroup ↥L).map (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F)
  have hWpg : IsPGroup p Wsub := P.isPGroup'.map (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F)
  have hWidx : ¬ p ∣ Wsub.index := by
    show ¬ p ∣ (Subgroup.map (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F)
      (P : Subgroup ↥L)).index
    rw [Subgroup.index_map_equiv]
    exact Sylow.not_dvd_index P
  let W : Sylow p (CFSG.GorensteinWalter.PSL2 F) := hWpg.toSylow hWidx
  have hWcoe : (W : Subgroup (CFSG.GorensteinWalter.PSL2 F)) = Wsub :=
    IsPGroup.toSylow_coe hWpg hWidx
  obtain ⟨c, hc⟩ :=
    CFSG.GH74.GLS.IVK.L2Borel.exists_conj_eq_unipotent (F := F) (p := p) (n := e) hcard W
  have hWsub_eq : Wsub = (CFSG.PSL2Table.unipotent F).map
      (MulAut.conj c).toMonoidHom := by
    rw [← hWcoe]
    exact hc
  have hcardW : Nat.card Wsub = p ^ e := by
    rw [hWsub_eq, Subgroup.card_map_of_injective (MulAut.conj c).injective,
      CFSG.PSL2Table.card_unipotent h2, hFcard]
  have hcardP : Nat.card (P : Subgroup ↥L) = p ^ e := by
    rw [← hcardW]
    exact (Subgroup.card_map_of_injective
      (f := (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F)) φ.injective).symm
  have hcardE : Nat.card E = p ^ e := by
    rw [← hEeq, Subgroup.card_map_of_injective L.subtype_injective, hcardP]
  have hWsub_el : CFSG.Open.IsElemAbelian p Wsub := by
    rw [hWsub_eq]
    exact CFSG.Open.IsElemAbelian.map (isElemAbelian_unipotent (F := F) (p := p))
      (MulAut.conj c).toMonoidHom
  have hmap : Wsub.map (φ.symm : CFSG.GorensteinWalter.PSL2 F →* ↥L) =
      (P : Subgroup ↥L) := by
    rw [show Wsub = (P : Subgroup ↥L).map
      (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F) from rfl, Subgroup.map_map,
      show ((φ.symm : CFSG.GorensteinWalter.PSL2 F →* ↥L).comp
        (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F)) = MonoidHom.id ↥L from ?_,
      Subgroup.map_id]
    ext x
    simp
  have hP_el : CFSG.Open.IsElemAbelian p (P : Subgroup ↥L) := by
    have h := CFSG.Open.IsElemAbelian.map hWsub_el
      (φ.symm : CFSG.GorensteinWalter.PSL2 F →* ↥L)
    rw [hmap] at h
    exact h
  refine ⟨?_, hcardE⟩
  have h := CFSG.Open.IsElemAbelian.map hP_el L.subtype
  rw [hEeq] at h
  exact h

omit [Finite G] in
private theorem sylow_eq_map {p : ℕ} [Fact p.Prime] {E : Subgroup G} (hE : IsSylowIn p E L) :
    Subgroup.map L.subtype (hE.toSylow : Subgroup ↥L) = E := by
  rw [IsSylowIn.coe_toSylow (p := p) (P := E) (H := L) hE]
  exact Subgroup.map_subgroupOf_eq_of_le hE.le

private theorem slDHom_apply {F : Type} [Field F] (a : Fˣ) :
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.slDHom a =
      CFSG.SectionRank.OddCover.slD a := rfl

private theorem pslU_eq_mk_unip {F : Type} [Field F] (t : Multiplicative F) :
    CFSG.SectionRank.OddCover.pslU t = CFSG.PSL2Table.mk (CFSG.PSL2Table.unip t.toAdd) := rfl

private theorem pslU_range_eq_unipotent {F : Type} [Field F] :
    (CFSG.SectionRank.OddCover.pslU (K := F)).range = CFSG.PSL2Table.unipotent F := by
  ext x
  rw [MonoidHom.mem_range, CFSG.PSL2Table.mem_unipotent_iff_exists]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.toAdd, by rw [← ht, pslU_eq_mk_unip]⟩
  · rintro ⟨t, ht⟩
    exact ⟨Multiplicative.ofAdd t, by rw [pslU_eq_mk_unip, toAdd_ofAdd]; exact ht.symm⟩

private noncomputable def modelIota {F : Type} [Field F]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) : CFSG.GorensteinWalter.PSL2 F →* G :=
  L.subtype.comp θ.symm.toMonoidHom

private noncomputable def modelU {F : Type} [Field F]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) (c : CFSG.GorensteinWalter.PSL2 F) :
    Multiplicative F →* G :=
  (modelIota θ).comp
    ((MulAut.conj c).toMonoidHom.comp (CFSG.SectionRank.OddCover.pslU (K := F)))

private noncomputable def modelD {F : Type} [Field F]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) (c : CFSG.GorensteinWalter.PSL2 F) :
    Fˣ →* G :=
  (modelIota θ).comp ((MulAut.conj c).toMonoidHom.comp
    (CFSG.SectionRank.OddCover.pslMk.comp
      CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.slDHom))

omit [Finite G] in
private theorem modelIota_injective {F : Type} [Field F]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) : Function.Injective (modelIota (L := L) θ) :=
  L.subtype_injective.comp θ.symm.injective

omit [Finite G] in
private theorem modelIota_comp {F : Type} [Field F]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) :
    (modelIota (L := L) θ).comp (θ : ↥L →* CFSG.GorensteinWalter.PSL2 F) = L.subtype := by
  ext x
  simp [modelIota]

omit [Finite G] in
private theorem modelU_injective {F : Type} [Field F]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) (c : CFSG.GorensteinWalter.PSL2 F) :
    Function.Injective (modelU (L := L) θ c) := by
  intro x y hxy
  simp only [modelU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hxy
  exact CFSG.SectionRank.OddCover.pslU_injective
    ((MulAut.conj c).injective (modelIota_injective θ hxy))

private theorem conjD_conjU {F : Type} [Field F] (c : CFSG.GorensteinWalter.PSL2 F) (a : Fˣ)
    (t : F) :
    (MulAut.conj c) (CFSG.SectionRank.OddCover.pslMk (CFSG.SectionRank.OddCover.slD a)) *
        (MulAut.conj c) (CFSG.SectionRank.OddCover.pslU (Multiplicative.ofAdd t)) *
        ((MulAut.conj c) (CFSG.SectionRank.OddCover.pslMk
          (CFSG.SectionRank.OddCover.slD a)))⁻¹ =
      (MulAut.conj c) (CFSG.SectionRank.OddCover.pslU
        (Multiplicative.ofAdd ((a : F) ^ 2 * t))) := by
  simp only [MulAut.conj_apply]
  have h : (c * CFSG.SectionRank.OddCover.pslMk (CFSG.SectionRank.OddCover.slD a) * c⁻¹) *
      (c * CFSG.SectionRank.OddCover.pslU (Multiplicative.ofAdd t) * c⁻¹) *
      (c * CFSG.SectionRank.OddCover.pslMk (CFSG.SectionRank.OddCover.slD a) * c⁻¹)⁻¹ =
      c * (CFSG.SectionRank.OddCover.pslMk (CFSG.SectionRank.OddCover.slD a) *
        CFSG.SectionRank.OddCover.pslU (Multiplicative.ofAdd t) *
        (CFSG.SectionRank.OddCover.pslMk (CFSG.SectionRank.OddCover.slD a))⁻¹) * c⁻¹ := by
    group
  rw [h, CFSG.SectionRank.OddCover.pslD_conj_pslU]

omit [Finite G] in
private theorem modelD_conj_modelU {F : Type} [Field F]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) (c : CFSG.GorensteinWalter.PSL2 F) (a : Fˣ)
    (t : Multiplicative F) :
    modelD (L := L) θ c a * modelU (L := L) θ c t * (modelD (L := L) θ c a)⁻¹ =
      modelU (L := L) θ c (Multiplicative.ofAdd ((a : F) ^ 2 * t.toAdd)) := by
  conv_lhs => rw [show t = Multiplicative.ofAdd t.toAdd from (ofAdd_toAdd t).symm]
  simp only [modelD, modelU, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, slDHom_apply]
  rw [← map_inv, ← map_mul, ← map_mul, conjD_conjU]

omit [Finite G] in
private theorem modelU_range {F : Type} [Field F] {p : ℕ} [Fact p.Prime]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) (c : CFSG.GorensteinWalter.PSL2 F)
    {E : Subgroup G} (hE : IsSylowIn p E L)
    (hEimg : Subgroup.map (θ : ↥L →* CFSG.GorensteinWalter.PSL2 F)
        (hE.toSylow : Subgroup ↥L) =
      Subgroup.map (MulAut.conj c).toMonoidHom (CFSG.PSL2Table.unipotent F)) :
    (modelU (L := L) θ c).range = E := by
  calc (modelU (L := L) θ c).range
      = Subgroup.map (modelIota (L := L) θ)
          (Subgroup.map (MulAut.conj c).toMonoidHom (CFSG.PSL2Table.unipotent F)) := by
        rw [modelU, MonoidHom.range_comp, MonoidHom.range_comp, pslU_range_eq_unipotent]
    _ = Subgroup.map L.subtype (hE.toSylow : Subgroup ↥L) := by
        rw [← hEimg, Subgroup.map_map, modelIota_comp]
    _ = E := sylow_eq_map hE

omit [Finite G] in
private theorem modelD_mem {F : Type} [Field F]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) (c : CFSG.GorensteinWalter.PSL2 F) (a : Fˣ) :
    modelD (L := L) θ c a ∈ L := by
  show L.subtype (θ.symm ((MulAut.conj c) (CFSG.SectionRank.OddCover.pslMk
    (CFSG.SectionRank.OddCover.slD a)))) ∈ L
  exact (θ.symm _).2

omit [Finite G] in
private theorem modelD_normalizes {F : Type} [Field F] {p : ℕ} [Fact p.Prime]
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) (c : CFSG.GorensteinWalter.PSL2 F)
    {E : Subgroup G} (hE : IsSylowIn p E L)
    (hEimg : Subgroup.map (θ : ↥L →* CFSG.GorensteinWalter.PSL2 F)
        (hE.toSylow : Subgroup ↥L) =
      Subgroup.map (MulAut.conj c).toMonoidHom (CFSG.PSL2Table.unipotent F)) (a : Fˣ) :
    modelD (L := L) θ c a ∈ Subgroup.normalizer (E : Set G) := by
  have hmem : ∀ (b : Fˣ) (y : G),
      y ∈ E → modelD (L := L) θ c b * y * (modelD (L := L) θ c b)⁻¹ ∈ E := by
    intro b y hy
    rw [← modelU_range θ c hE hEimg] at hy ⊢
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [modelD_conj_modelU]
    exact MonoidHom.mem_range.mpr
      ⟨Multiplicative.ofAdd ((b : F) ^ 2 * t.toAdd), rfl⟩
  refine Subgroup.mem_normalizer_iff.mpr (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
  · exact hmem a x hx
  · have h := hmem a⁻¹ (modelD (L := L) θ c a * x * (modelD (L := L) θ c a)⁻¹) hx
    have he : (modelD (L := L) θ c a⁻¹) * (modelD (L := L) θ c a * x *
        (modelD (L := L) θ c a)⁻¹) * (modelD (L := L) θ c a⁻¹)⁻¹ = x := by
      rw [map_inv]
      group
    rw [he] at h
    exact h

private theorem subgroup_map_conj_mul {G : Type*} [Group G] (D : Subgroup G) (x y : G) :
    Subgroup.map (MulAut.conj (x * y)).toMonoidHom D =
      Subgroup.map (MulAut.conj x).toMonoidHom
        (Subgroup.map (MulAut.conj y).toMonoidHom D) := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

theorem orbLen_le_ncard_hypOrbit (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2)
    {E : Subgroup G} (hE : IsSylowIn p E L) {D : Subgroup G} (hD : D ∈ hyperplanes p E) :
    orbLen p e ≤ (hypOrbit (L ⊓ normalizer (E : Set G)) D).ncard := by
  classical
  obtain ⟨hp, F, hF, hFin, hcard, ⟨θ⟩⟩ := model_psl2 hM
  let := hF
  let := hFin
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hFcard : Fintype.card F = p ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have : CharP F p := charP_of_card_eq_prime_pow hFcard
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hle hp.two_le)
  obtain ⟨hDE, hDrel⟩ : D ≤ E ∧ D.relIndex E = p := hD
  obtain ⟨c, hEimg⟩ := exists_conj_sylow_image hcard θ hE
  have hDrange : D ≤ (modelU (L := L) θ c).range := by
    rw [modelU_range θ c hE hEimg]
    exact hDE
  let D' : Subgroup (Multiplicative F) := D.comap (modelU (L := L) θ c)
  have hD'map : Subgroup.map (modelU (L := L) θ c) D' = D := by
    show Subgroup.map (modelU (L := L) θ c) (D.comap (modelU (L := L) θ c)) = D
    exact Subgroup.map_comap_eq_self hDrange
  have hD'idx : D'.index = p := by
    rw [← Subgroup.relIndex_top_right,
      ← Subgroup.relIndex_map_map_of_injective D' ⊤ (modelU_injective θ c), hD'map,
      ← MonoidHom.range_eq_map, modelU_range θ c hE hEimg]
    exact hDrel
  let D'' : AddSubgroup F := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.addOfMul D'
  have hD''idx : D''.index = p := by
    show (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.addOfMul D').index = p
    exact (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.index_addOfMul D').trans hD'idx
  set f : Fˣ → Subgroup G :=
    fun a => D.map (MulAut.conj (modelD (L := L) θ c a)).toMonoidHom with hf
  have hf_mem : ∀ a : Fˣ, f a ∈ hypOrbit (L ⊓ normalizer (E : Set G)) D := by
    intro a
    exact ⟨modelD (L := L) θ c a,
      ⟨modelD_mem θ c a, modelD_normalizes θ c hE hEimg a⟩, rfl⟩
  have hf_mul : ∀ a b : Fˣ, f (a * b) =
      Subgroup.map (MulAut.conj (modelD (L := L) θ c a)).toMonoidHom (f b) := by
    intro a b
    simp only [hf]
    rw [map_mul, subgroup_map_conj_mul]
  have hfiber : ∀ a₀ : Fˣ, Nat.card {a : Fˣ // f a = f a₀} ≤
      Nat.card {b : Fˣ // f b = D} := by
    intro a₀
    have key : ∀ a : Fˣ, f a = (f (a₀⁻¹ * a)).map
        (MulAut.conj (modelD (L := L) θ c a₀)).toMonoidHom := by
      intro a
      rw [← hf_mul a₀ (a₀⁻¹ * a), mul_inv_cancel_left]
    refine Nat.card_le_card_of_injective
      (fun a : {a : Fˣ // f a = f a₀} => (⟨a₀⁻¹ * a.1, ?_⟩ : {b : Fˣ // f b = D})) ?_
    · have h1 : (f (a₀⁻¹ * a.1)).map
          (MulAut.conj (modelD (L := L) θ c a₀)).toMonoidHom =
          D.map (MulAut.conj (modelD (L := L) θ c a₀)).toMonoidHom := by
        rw [← key, a.2]
      exact Subgroup.map_injective
        (MulEquiv.injective (MulAut.conj (modelD (L := L) θ c a₀))) h1
    · intro a b hab
      apply Subtype.ext
      have h : a₀⁻¹ * (a : Fˣ) = a₀⁻¹ * (b : Fˣ) :=
        congrArg (fun x : {b : Fˣ // f b = D} => (x : Fˣ)) hab
      exact mul_left_cancel h
  have hP : ∀ b : Fˣ, f b = D → ((b : F) ^ 2) ^ p = (b : F) ^ 2 := by
    intro b hb
    refine CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.pow_char_eq_self_of_mul_mem hD''idx ?_
    intro x hx
    have hxD : modelU (L := L) θ c (Multiplicative.ofAdd x) ∈ D := hx
    have hinv : modelD (L := L) θ c b * modelU (L := L) θ c (Multiplicative.ofAdd x) *
        (modelD (L := L) θ c b)⁻¹ ∈ D := by
      rw [← hb]
      exact Subgroup.mem_map_of_mem (MulAut.conj (modelD (L := L) θ c b)).toMonoidHom hxD
    rw [modelD_conj_modelU] at hinv
    exact hinv
  have hstab : Nat.card {b : Fˣ // f b = D} ≤
      Nat.card {a : Fˣ // ((a : F) ^ 2) ^ p = (a : F) ^ 2} :=
    Nat.card_le_card_of_injective
      (fun b : {b : Fˣ // f b = D} =>
        (⟨b.1, hP b.1 b.2⟩ : {a : Fˣ // ((a : F) ^ 2) ^ p = (a : F) ^ 2}))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hstab_odd (heo : Odd e) : Nat.card {b : Fˣ // f b = D} ≤
      Nat.card {a : Fˣ // (a : F) ^ p = (a : F)} :=
    Nat.card_le_card_of_injective
      (fun b : {b : Fˣ // f b = D} =>
        (⟨b.1, CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.pow_char_eq_self_of_sq hp2 hcard heo
          (hP b.1 b.2)⟩ : {a : Fˣ // (a : F) ^ p = (a : F)}))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hcount : ∀ c' : ℕ, Nat.card {b : Fˣ // f b = D} ≤ c' →
      Nat.card Fˣ ≤ c' * (hypOrbit (L ⊓ normalizer (E : Set G)) D).ncard := by
    intro c' hc'
    have hsub : Set.range f ⊆ hypOrbit (L ⊓ normalizer (E : Set G)) D := by
      rintro - ⟨a, rfl⟩
      exact hf_mem a
    have himg : ((Finset.univ : Finset Fˣ).image f).card ≤
        (hypOrbit (L ⊓ normalizer (E : Set G)) D).ncard := by
      rw [← Set.ncard_coe_finset]
      have heq : ((↑((Finset.univ : Finset Fˣ).image f) : Set (Subgroup G)) = Set.range f) := by
        ext x
        simp [Set.mem_range]
      rw [heq]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have hstep : (Finset.univ : Finset Fˣ).card ≤
        c' * ((Finset.univ : Finset Fˣ).image f).card := by
      refine Finset.card_le_mul_card_image _ c' (fun b hb => ?_)
      obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.mp hb
      calc (Finset.univ.filter (fun a : Fˣ => f a = f a₀)).card
          = Nat.card {a : Fˣ // f a = f a₀} := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        _ ≤ Nat.card {b : Fˣ // f b = D} := hfiber a₀
        _ ≤ c' := hc'
    calc Nat.card Fˣ = (Finset.univ : Finset Fˣ).card := by
          rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ c' * ((Finset.univ : Finset Fˣ).image f).card := hstep
      _ ≤ c' * (hypOrbit (L ⊓ normalizer (E : Set G)) D).ncard :=
          Nat.mul_le_mul_left c' himg
  have hunits : Nat.card Fˣ = p ^ e - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hFcard]
  have hmain : ∀ c' : ℕ, Nat.card {b : Fˣ // f b = D} ≤ c' →
      (p ^ e - 1) / c' ≤ (hypOrbit (L ⊓ normalizer (E : Set G)) D).ncard := by
    intro c' hc'
    have h := hcount c' hc'
    rw [hunits] at h
    exact Nat.div_le_of_le_mul h
  rcases Nat.even_or_odd e with he | he
  · rw [orbLen, if_pos he]
    exact hmain (2 * (p - 1)) (le_trans hstab
      (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.card_sq_pow_char_le (K := F) (p := p)))
  · have hne : ¬ Even e := by
      rintro ⟨k, hk⟩
      obtain ⟨j, hj⟩ := he
      omega
    rw [orbLen, if_neg hne]
    exact hmain (p - 1) (le_trans (hstab_odd he)
      (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.card_pow_char_units_le (K := F) (p := p)))

private theorem sq_eq_neg_one_of_orderOf {F : Type} [Field F] (_h2 : (2 : F) ≠ 0) {a : Fˣ}
    (ha : orderOf (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a)) = 2) : (a : F) ^ 2 = -1 := by
  have h1 : (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a)) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a))
    rwa [ha] at h
  rcases (CFSG.PSL2Table.mk_eq_one_iff (CFSG.PSL2Table.diag (a * a))).mp
    (by rw [CFSG.PSL2Table.diag_mul, map_mul, ← pow_two]; exact h1) with h | h
  · have hval : ((a * a : Fˣ) : F) = 1 := by
      have hc := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simpa [CFSG.PSL2Table.coe_diag] using hc
    rw [Units.val_mul] at hval
    have hone : CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a) = 1 := by
      rw [CFSG.PSL2Table.mk_diag_eq_one_iff, pow_two]
      exact hval
    rw [hone, orderOf_one] at ha
    exact absurd ha (by norm_num)
  · have hval : ((a * a : Fˣ) : F) = -1 := by
      have hc := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simpa [CFSG.PSL2Table.coe_diag] using hc
    rw [Units.val_mul] at hval
    rwa [pow_two]

private theorem isSylowIn_comap_of_sylow {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (φ : ↥L ≃* CFSG.GorensteinWalter.PSL2 F) {W : Subgroup (CFSG.GorensteinWalter.PSL2 F)}
    (hpg : IsPGroup p W) (hidx : ¬ p ∣ W.index) :
    IsSylowIn p (Subgroup.map L.subtype
      (Subgroup.comap (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F) W)) L := by
  set A : Subgroup ↥L := Subgroup.comap (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F) W with hA
  have hle : Subgroup.map L.subtype A ≤ L := Subgroup.map_subtype_le A
  have hpgA : IsPGroup p A := by
    intro y
    obtain ⟨n, hn⟩ := hpg ⟨φ y, y.2⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply φ.injective
    rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
    exact congrArg (fun z : W => (z : CFSG.GorensteinWalter.PSL2 F)) hn
  refine ⟨hle, hpgA.map L.subtype, ?_⟩
  have hrel : (Subgroup.map L.subtype A).relIndex L * L.index = A.index * L.index := by
    rw [Subgroup.relIndex_mul_index hle, Subgroup.index_map_subtype (H := L) A]
  have hL : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpd : (Subgroup.map L.subtype A).relIndex L = A.index :=
    Nat.mul_right_cancel (Nat.pos_of_ne_zero hL) hrel
  have hidxA : A.index = W.index := by
    rw [hA]
    exact Subgroup.index_comap_of_surjective (H := W)
      (f := (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F)) φ.surjective
  rw [hpd, hidxA]
  exact hidx

private theorem diag_conj_unipotent_inv {F : Type} [Field F] {a : Fˣ} (ha : (a : F) ^ 2 = -1)
    {u : CFSG.GorensteinWalter.PSL2 F} (hu : u ∈ CFSG.PSL2Table.unipotent F) :
    CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a) * u *
      (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a))⁻¹ = u⁻¹ := by
  obtain ⟨t, rfl⟩ := (CFSG.PSL2Table.mem_unipotent_iff_exists u).mp hu
  rw [CFSG.PSL2Table.mk_conj, CFSG.PSL2Table.diag_conj_unip, ha, neg_one_mul, ← map_inv,
    CFSG.PSL2Table.unip_neg]

private theorem orderOf_mk_diag_eq_two {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {a : Fˣ}
    (ha : (a : F) ^ 2 = -1) : orderOf (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a)) = 2 := by
  have hunit : a * a = -1 :=
    Units.ext (by rw [Units.val_mul, ← pow_two, ha, Units.val_neg, Units.val_one])
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← map_mul, ← CFSG.PSL2Table.diag_mul, hunit, CFSG.PSL2Table.diag_neg_one,
      CFSG.PSL2Table.mk_neg, map_one]
  · intro h
    have h1 : (a : F) ^ 2 = 1 := (CFSG.PSL2Table.mk_diag_eq_one_iff a).mp h
    rw [ha] at h1
    have hz : (2 : F) = 0 := by
      have h := congrArg (fun x : F => x + 1) h1
      rw [neg_add_cancel] at h
      rw [show (2 : F) = 1 + 1 from by norm_num]
      exact h.symm
    exact h2 hz

theorem exists_inverted_isSylowIn (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2)
    (hq4 : p ^ e % 4 = 1) {t : G} (htL : t ∈ L) (ht : orderOf t = 2) :
    ∃ E : Subgroup G, IsSylowIn p E L ∧ ∀ x ∈ E, t * x * t⁻¹ = x⁻¹ := by
  classical
  obtain ⟨hp, he1, h2e, h3e, F, hF, hFin, hcard, ⟨φ⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hM
  let := hF
  let := hFin
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hFcard : Fintype.card F = p ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have : CharP F p := charP_of_card_eq_prime_pow hFcard
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hle hp.two_le)
  have hring : ringChar F ≠ 2 := by
    intro h
    have hcp : CharP F 2 := h ▸ ringChar.charP (R := F)
    exact h2 (CharP.cast_eq_zero F 2)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq5 : 5 ≤ Fintype.card F := by
    rw [hFcard]
    have hge : 3 ≤ p ^ e := by
      calc 3 ≤ p := hp3
        _ = p ^ 1 := by rw [pow_one]
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he1
    have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
    rcases hodd with ⟨k, hk⟩
    omega
  have hsq : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  have ht' : orderOf (φ ⟨t, htL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ht
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare (F := F) hring
  obtain ⟨x, hxT, hconj⟩ :=
    (CFSG.PSL2Table.involution_conj_torus hring hq5 hν ht').1 hsq
  have hxord : orderOf x = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ht'
  obtain ⟨a, rfl⟩ := (CFSG.PSL2Table.mem_splitTorus_iff_exists x).mp hxT
  have ha : (a : F) ^ 2 = -1 := sq_eq_neg_one_of_orderOf h2 hxord
  obtain ⟨d, hd⟩ := isConj_iff.mp hconj.symm
  have hd' : (MulAut.conj d).toMonoidHom (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a)) =
      φ ⟨t, htL⟩ := by
    show MulAut.conj d (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a)) = φ ⟨t, htL⟩
    rw [MulAut.conj_apply]
    exact hd
  obtain ⟨Q, hQ⟩ :=
    CFSG.GH74.GLS.IVK.L2Borel.exists_sylow_unipotent (F := F) (p := p) (n := e) hcard
  have hUpg : IsPGroup p (CFSG.PSL2Table.unipotent F) := by
    rw [← hQ]
    exact Q.isPGroup'
  have hUidx : ¬ p ∣ (CFSG.PSL2Table.unipotent F).index := by
    rw [← hQ]
    exact Sylow.not_dvd_index Q
  set W : Subgroup (CFSG.GorensteinWalter.PSL2 F) :=
    (CFSG.PSL2Table.unipotent F).map (MulAut.conj d).toMonoidHom with hW
  have hWpg : IsPGroup p W := by
    rw [hW]
    exact hUpg.map _
  have hidxconj : W.index = (CFSG.PSL2Table.unipotent F).index := by
    have hcard : Nat.card W = Nat.card (CFSG.PSL2Table.unipotent F) := by
      rw [hW]
      exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj d))
    have h1 : Nat.card W * W.index = Nat.card (CFSG.GorensteinWalter.PSL2 F) :=
      Subgroup.card_mul_index W
    have h2c : Nat.card (CFSG.PSL2Table.unipotent F) *
        (CFSG.PSL2Table.unipotent F).index = Nat.card (CFSG.GorensteinWalter.PSL2 F) :=
      Subgroup.card_mul_index _
    have h1' : Nat.card (CFSG.PSL2Table.unipotent F) * W.index =
        Nat.card (CFSG.GorensteinWalter.PSL2 F) := by
      rw [← hcard]
      exact h1
    have key : Nat.card (CFSG.PSL2Table.unipotent F) * W.index =
        Nat.card (CFSG.PSL2Table.unipotent F) * (CFSG.PSL2Table.unipotent F).index :=
      h1'.trans h2c.symm
    have hpos : 0 < Nat.card (CFSG.PSL2Table.unipotent F) := by
      rw [CFSG.PSL2Table.card_unipotent h2, hFcard]
      exact Nat.pow_pos hp.pos
    exact Nat.mul_left_cancel hpos key
  have hWidx : ¬ p ∣ W.index := by
    rw [hidxconj]
    exact hUidx
  have hinvW : ∀ y ∈ W, φ ⟨t, htL⟩ * y * (φ ⟨t, htL⟩)⁻¹ = y⁻¹ := by
    intro y hy
    rw [hW] at hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← hd', ← map_inv, ← map_mul, ← map_mul, diag_conj_unipotent_inv ha hu, map_inv]
  refine ⟨Subgroup.map L.subtype
    (Subgroup.comap (φ : ↥L →* CFSG.GorensteinWalter.PSL2 F) W),
    isSylowIn_comap_of_sylow φ hWpg hWidx, ?_⟩
  intro x₀ hx₀
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx₀
  have hkey : (⟨t, htL⟩ : ↥L) * y * (⟨t, htL⟩ : ↥L)⁻¹ = y⁻¹ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, map_inv]
    exact hinvW (φ y) hy
  calc t * L.subtype y * t⁻¹
      = L.subtype ⟨t, htL⟩ * L.subtype y * (L.subtype ⟨t, htL⟩)⁻¹ := by
        rw [show L.subtype ⟨t, htL⟩ = t from rfl]
    _ = L.subtype ((⟨t, htL⟩ : ↥L) * y * (⟨t, htL⟩ : ↥L)⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = L.subtype (y⁻¹) := by rw [hkey]
    _ = (L.subtype y)⁻¹ := by rw [map_inv]

theorem exists_inverting_of_isSylowIn (hM : LieModel ↥L .PSL 2 p e) (hp2 : p ≠ 2)
    (hq4 : p ^ e % 4 = 1) {E : Subgroup G} (hE : IsSylowIn p E L) :
    ∃ s ∈ L, orderOf s = 2 ∧ ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨hp, F, hF, hFin, hcard, ⟨φ⟩⟩ := model_psl2 hM
  let := hF
  let := hFin
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hFcard : Fintype.card F = p ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have : CharP F p := charP_of_card_eq_prime_pow hFcard
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hle hp.two_le)
  have hsq : IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨i, hi⟩ := hsq
  have hi' : i * i = -1 := by simpa [pow_two] using hi.symm
  have hi0 : i ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hi'
    exact (neg_ne_zero.mpr one_ne_zero) hi'.symm
  set a : Fˣ := Units.mk0 i hi0 with ha_def
  have ha : (a : F) ^ 2 = -1 := by
    rw [ha_def, Units.val_mk0, pow_two, hi']
  have hord : orderOf (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a)) = 2 :=
    orderOf_mk_diag_eq_two h2 ha
  obtain ⟨c₀, hc₀⟩ := exists_conj_sylow_image hcard φ hE
  set s' : CFSG.GorensteinWalter.PSL2 F :=
    (MulAut.conj c₀).toMonoidHom (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag a)) with hs'
  have hs'ord : orderOf s' = 2 := by
    rw [hs']
    exact (MulEquiv.orderOf_eq (MulAut.conj c₀) _).trans hord
  have hsinv : ∀ y ∈ Subgroup.map (MulAut.conj c₀).toMonoidHom (CFSG.PSL2Table.unipotent F),
      s' * y * s'⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hs', ← map_inv, ← map_mul, ← map_mul, diag_conj_unipotent_inv ha hu, map_inv]
  refine ⟨L.subtype (φ.symm s'), (φ.symm s').2, ?_, ?_⟩
  · rw [orderOf_injective L.subtype L.subtype_injective, MulEquiv.orderOf_eq, hs'ord]
  · intro x hx
    have hxL : x ∈ L := hE.le hx
    have hxP : (⟨x, hxL⟩ : ↥L) ∈ (hE.toSylow : Subgroup ↥L) := by
      rw [IsSylowIn.coe_toSylow (p := p) (P := E) (H := L) hE]
      exact hx
    have hkey : φ.symm s' * (⟨x, hxL⟩ : ↥L) * (φ.symm s')⁻¹ = (⟨x, hxL⟩ : ↥L)⁻¹ := by
      apply φ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_inv]
      exact hsinv (φ ⟨x, hxL⟩) (by rw [← hc₀]; exact Subgroup.mem_map_of_mem _ hxP)
    have hxl : L.subtype (⟨x, hxL⟩ : ↥L) = x := rfl
    calc L.subtype (φ.symm s') * x * (L.subtype (φ.symm s'))⁻¹
        = L.subtype (φ.symm s') * L.subtype ⟨x, hxL⟩ * (L.subtype (φ.symm s'))⁻¹ := by
          rw [hxl]
      _ = L.subtype (φ.symm s' * ⟨x, hxL⟩ * (φ.symm s')⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = L.subtype ((⟨x, hxL⟩ : ↥L)⁻¹) := by rw [hkey]
      _ = x⁻¹ := by rw [map_inv, hxl]

theorem exists_conj_eq_pow_sq (hM : LieModel ↥L .PSL 2 p 1) (_hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsSylowIn p E L) {c : ℕ} (hc : ¬ p ∣ c) :
    ∃ n ∈ L, ∀ x ∈ E, n * x * n⁻¹ = x ^ (c ^ 2) := by
  obtain ⟨hp, F, hF, hFin, hcard, ⟨φ⟩⟩ := model_psl2 hM
  let := hF
  let := hFin
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hFcard : Fintype.card F = p ^ 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have : CharP F p := charP_of_card_eq_prime_pow hFcard
  have hne : (c : F) ≠ 0 := by
    intro h0
    exact hc ((CharP.cast_eq_zero_iff F p c).1 h0)
  obtain ⟨c₀, hc₀⟩ := exists_conj_sylow_image hcard φ hE
  have hm : ((c ^ 2 : ℕ) : F) = ((Units.mk0 (c : F) hne : Fˣ) : F) ^ 2 := by
    rw [Units.val_mk0]
    push_cast
    ring
  set n' : CFSG.GorensteinWalter.PSL2 F :=
    (MulAut.conj c₀).toMonoidHom
      (CFSG.PSL2Table.mk (CFSG.PSL2Table.diag (Units.mk0 (c : F) hne))) with hn'
  have hpow : ∀ y ∈ Subgroup.map (MulAut.conj c₀).toMonoidHom (CFSG.PSL2Table.unipotent F),
      n' * y * n'⁻¹ = y ^ (c ^ 2) := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hn', ← map_inv, ← map_mul, ← map_mul, diag_conj_unipotent_pow hm hu, map_pow]
  have hkey : ∀ z : ↥L, z ∈ (hE.toSylow : Subgroup ↥L) →
      φ.symm n' * z * (φ.symm n')⁻¹ = z ^ (c ^ 2) := by
    intro z hz
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_pow]
    exact hpow (φ z) (by rw [← hc₀]; exact Subgroup.mem_map_of_mem _ hz)
  have hPcoe : (hE.toSylow : Subgroup ↥L) = E.subgroupOf L :=
    IsSylowIn.coe_toSylow (p := p) (P := E) (H := L) hE
  refine ⟨L.subtype (φ.symm n'), (φ.symm n').2, ?_⟩
  intro x hx
  have hxL : x ∈ L := hE.le hx
  have hxP : (⟨x, hxL⟩ : ↥L) ∈ (hE.toSylow : Subgroup ↥L) := by
    rw [hPcoe]
    exact hx
  have hxl : L.subtype (⟨x, hxL⟩ : ↥L) = x := rfl
  calc L.subtype (φ.symm n') * x * (L.subtype (φ.symm n'))⁻¹
      = L.subtype (φ.symm n') * L.subtype ⟨x, hxL⟩ * (L.subtype (φ.symm n'))⁻¹ := by
        rw [hxl]
    _ = L.subtype (φ.symm n' * ⟨x, hxL⟩ * (φ.symm n')⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = L.subtype ((⟨x, hxL⟩ : ↥L) ^ (c ^ 2)) := by rw [hkey ⟨x, hxL⟩ hxP]
    _ = x ^ (c ^ 2) := by rw [map_pow, hxl]

omit [Finite G] in
theorem exists_involution (hM : LieModel ↥L .PSL 2 p e) : ∃ t ∈ L, orderOf t = 2 := by
  obtain ⟨-, F, hF, hFin, -, ⟨φ⟩⟩ := model_psl2 hM
  let := hF
  let := hFin
  have hord : orderOf (CFSG.PSL2Table.splitWeyl F) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, CFSG.PSL2Table.splitWeyl_mul_self]
    · intro h
      exact CFSG.PSL2Table.splitWeyl_not_mem (h ▸ Subgroup.one_mem _)
  refine ⟨L.subtype (φ.symm (CFSG.PSL2Table.splitWeyl F)), (φ.symm _).2, ?_⟩
  rw [orderOf_injective L.subtype L.subtype_injective, MulEquiv.orderOf_eq, hord]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
