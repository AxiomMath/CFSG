module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.SteinbergBSEscapingOvergroup

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] noncomputable def conjQuotientHom (L : Subgroup G) (K : Subgroup L) [K.Characteristic] :
    normalizer (L : Set G) →* MulAut (L ⧸ K) where
  toFun g := QuotientGroup.congr K K (normalizerMonoidHom L g)
    (show K.map (normalizerMonoidHom L g : L →* L) = K from
      characteristic_iff_map_eq.mp inferInstance _)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H l => ?_
    rw [QuotientGroup.congr_mk, map_one]
    rfl
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with | H l => ?_
    rw [QuotientGroup.congr_mk, map_mul]
    rfl

theorem normalizer_le_normalizer_map_characteristic (L : Subgroup G) (K : Subgroup L)
    [hK : K.Characteristic] :
    normalizer (L : Set G) ≤ normalizer (K.map L.subtype : Set G) := by
  refine le_normalizer_iff.2 fun g hg x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨normalizerMonoidHom L ⟨g, hg⟩ y, ?_, normalizerMonoidHom_apply_apply_coe L ⟨g, hg⟩ y⟩
  rw [← characteristic_iff_map_eq.mp hK (normalizerMonoidHom L ⟨g, hg⟩)]
  exact mem_map_of_mem _ hy

@[expose] noncomputable def quotientCentralizer (X L : Subgroup G) (K : Subgroup L)
    [K.Characteristic] : Subgroup G :=
  ((conjQuotientHom L K).comp
    (inclusion (inf_le_right : X ⊓ normalizer (L : Set G) ≤ _))).ker.map
      (X ⊓ normalizer (L : Set G)).subtype

theorem mem_quotientCentralizer_iff {X L : Subgroup G} (K : Subgroup L) [K.Characteristic]
    {x : G} : x ∈ quotientCentralizer X L K ↔
      x ∈ X ∧ x ∈ normalizer (L : Set G) ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ K.map L.subtype := by
  rw [quotientCentralizer, mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(mem_inf.1 y.2).1, (mem_inf.1 y.2).2, fun l hl => ?_⟩
    rw [MonoidHom.mem_ker] at hy
    have h1 := DFunLike.congr_fun hy ((⟨l, hl⟩ : L) : L ⧸ K)
    change ((normalizerMonoidHom L ⟨y, (mem_inf.1 y.2).2⟩ ⟨l, hl⟩ : L) : L ⧸ K) =
      ((⟨l, hl⟩ : L) : L ⧸ K) at h1
    rw [QuotientGroup.eq_iff_div_mem] at h1
    refine ⟨_, h1, ?_⟩
    simp [div_eq_mul_inv, normalizerMonoidHom_apply_apply_coe]
  · rintro ⟨hxX, hxL, hxK⟩
    refine ⟨⟨x, mem_inf.2 ⟨hxX, hxL⟩⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with | H l => ?_
    change ((normalizerMonoidHom L ⟨x, hxL⟩ l : L) : L ⧸ K) = (l : L ⧸ K)
    rw [QuotientGroup.eq_iff_div_mem]
    obtain ⟨k, hk, hkx⟩ := hxK l l.2
    have hkx' : (k : G) = x * l * x⁻¹ * (l : G)⁻¹ := hkx
    have hkl : normalizerMonoidHom L ⟨x, hxL⟩ l / l = k := by
      apply Subtype.ext
      simp [div_eq_mul_inv, normalizerMonoidHom_apply_apply_coe, hkx']
    rw [hkl]
    exact hk

theorem conj_mem_quotientCentralizer {X L : Subgroup G} (K : Subgroup L) [K.Characteristic]
    {x c : G} (hx : x ∈ X) (hxL : x ∈ normalizer (L : Set G))
    (hc : c ∈ quotientCentralizer X L K) : x * c * x⁻¹ ∈ quotientCentralizer X L K := by
  rw [mem_quotientCentralizer_iff] at hc ⊢
  obtain ⟨hcX, hcL, hcK⟩ := hc
  refine ⟨mul_mem (mul_mem hx hcX) (inv_mem hx), mul_mem (mul_mem hxL hcL) (inv_mem hxL),
    fun l hl => ?_⟩
  have hl' : x⁻¹ * l * x ∈ L := by
    have := (mem_normalizer_iff.mp (inv_mem hxL) l).mp hl
    simpa using this
  have h1 := (mem_normalizer_iff.mp (normalizer_le_normalizer_map_characteristic L K hxL)
    _).mp (hcK _ hl')
  convert h1 using 1
  group

theorem le_normalizer_quotientCentralizer {X L : Subgroup G} (K : Subgroup L) [K.Characteristic]
    (hXL : X ≤ normalizer (L : Set G)) :
    X ≤ normalizer (quotientCentralizer X L K : Set G) :=
  le_normalizer_iff.2 fun _ hx _ hc => conj_mem_quotientCentralizer K hx (hXL hx) hc

theorem le_inSubgroup_pCore {p : ℕ} {N X : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ normalizer (N : Set G)) (hN : IsPGroup p N) : N ≤ inSubgroup (pCore p) X := by
  have : (N.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hNX).2 hXN
  have h1 : N.subgroupOf X ≤ pCore p X :=
    le_pCore_of_normal (hN.of_equiv (subgroupOfEquivOfLe hNX).symm)
  rw [← map_subgroupOf_eq_of_le hNX]
  exact map_mono h1

theorem centerless_two_residual_has_original_two_core_centralizer [Finite G]
    {E L B T : Subgroup G} (hLE : L ≤ E) [(L.subgroupOf E).Normal]
    (hE2 : IsPGroup 2 (E ⧸ L.subgroupOf E)) (hTE : T ≤ E) (hTB : IsSylowOf 2 T B)
    (hPT : inSubgroup (pCore 2) E ≤ T) (hcl : center (L ⧸ pCore 2 L) = ⊥)
    (hBL : B ≤ normalizer (L : Set G)) :
    inSubgroup (pCore 2) L = inSubgroup (pCore 2) E ⊓ L ∧
      quotientCentralizer E L (pCore 2 L) = inSubgroup (pCore 2) E ∧
      quotientCentralizer B L (pCore 2 L) ≤ B ∧
      ((quotientCentralizer B L (pCore 2 L)).subgroupOf B).Normal ∧
      quotientCentralizer B L (pCore 2 L) ⊓ T = inSubgroup (pCore 2) E ∧
      IsSylowOf 2 (inSubgroup (pCore 2) E) (quotientCentralizer B L (pCore 2 L)) := by
  classical
  set P := inSubgroup (pCore 2) E with hPdef
  set R := inSubgroup (pCore 2) L with hRdef
  set C := quotientCentralizer E L (pCore 2 L) with hCdef
  set D := quotientCentralizer B L (pCore 2 L) with hDdef
  have hEN : E ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLE).1 inferInstance
  have hPp : IsPGroup 2 P := (pCore_isPGroup (p := 2) (G := E)).map E.subtype
  have hRp : IsPGroup 2 R := (pCore_isPGroup (p := 2) (G := L)).map L.subtype
  have hPE : P ≤ E := map_subtype_le _
  have hRL : R ≤ L := map_subtype_le _
  have hNR : normalizer (L : Set G) ≤ normalizer (R : Set G) :=
    normalizer_le_normalizer_map_characteristic L (pCore 2 L)
  have hEP : E ≤ normalizer (P : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic E (pCore 2 E))
  have hRP : R ≤ P := le_inSubgroup_pCore (hRL.trans hLE) (hEN.trans hNR) hRp
  have hPLR : P ⊓ L ≤ R := le_inSubgroup_pCore inf_le_right
    (fun l hl => inf_normalizer_le_normalizer_inf ⟨hEP (hLE hl), le_normalizer hl⟩)
    hPp.to_inf_left
  have h1 : R = P ⊓ L := le_antisymm (le_inf hRP hRL) hPLR
  have hPC : P ≤ C := by
    intro x hx
    rw [hCdef, mem_quotientCentralizer_iff]
    refine ⟨hPE hx, hEN (hPE hx), fun l hl => hPLR (mem_inf.2 ⟨?_, ?_⟩)⟩
    · have h := le_normalizer_iff.1 hEP l (hLE hl) _ (inv_mem hx)
      simpa [mul_assoc] using mul_mem hx h
    · have h := (mem_normalizer_iff.mp (hEN (hPE hx)) l).mp hl
      exact mul_mem h (inv_mem hl)
  have hCL : C ⊓ L ≤ R := by
    intro y hy
    obtain ⟨hyC, hyL⟩ := mem_inf.1 hy
    rw [hCdef, mem_quotientCentralizer_iff] at hyC
    have hz : ((⟨y, hyL⟩ : L) : L ⧸ pCore 2 L) ∈ center (L ⧸ pCore 2 L) := by
      rw [mem_center_iff]
      intro q
      induction q using QuotientGroup.induction_on with | H l => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
      obtain ⟨k, hk, hkx⟩ := hyC.2.2 l l.2
      have hkx' : (k : G) = y * l * y⁻¹ * (l : G)⁻¹ := hkx
      have hkl : l * ⟨y, hyL⟩ / (⟨y, hyL⟩ * l) = k⁻¹ := by
        apply Subtype.ext
        simp only [div_eq_mul_inv, coe_mul, coe_inv, hkx']
        group
      rw [hkl]
      exact inv_mem hk
    rw [hcl, mem_bot, QuotientGroup.eq_one_iff] at hz
    exact ⟨_, hz, rfl⟩
  have hCE : C ≤ E := fun x hx => ((mem_quotientCentralizer_iff _).1 hx).1
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨k, hk⟩ := hE2 (⟨c, hCE c.2⟩ : E)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf] at hk
    have hcL : (c : G) ^ 2 ^ k ∈ C ⊓ L := mem_inf.2 ⟨pow_mem c.2 _, by simpa using hk⟩
    obtain ⟨m, hm⟩ := hRp ⟨_, hCL hcL⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' : ((c : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simpa [pow_add, pow_mul] using hm'
  have hCP : C ≤ P :=
    le_inSubgroup_pCore hCE (le_normalizer_quotientCentralizer _ hEN) hCp
  have h2 : C = P := le_antisymm hCP hPC
  have hDB : D ≤ B := fun x hx => ((mem_quotientCentralizer_iff _).1 hx).1
  have hBD : B ≤ normalizer (D : Set G) := le_normalizer_quotientCentralizer _ hBL
  have h3 : (D.subgroupOf B).Normal := (normal_subgroupOf_iff_le_normalizer hDB).2 hBD
  have h4 : D ⊓ T = P := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxD, hxT⟩ := mem_inf.1 hx
      rw [hDdef, mem_quotientCentralizer_iff] at hxD
      rw [← h2, hCdef, mem_quotientCentralizer_iff]
      exact ⟨hTE hxT, hxD.2⟩
    · intro x hx
      have hxC := hPC hx
      rw [hCdef, mem_quotientCentralizer_iff] at hxC
      refine mem_inf.2 ⟨?_, hPT hx⟩
      rw [hDdef, mem_quotientCentralizer_iff]
      exact ⟨hTB.le (hPT hx), hxC.2⟩
  have h5 : IsSylowOf 2 P D := by
    have h := hTB.inf_of_le_normalizer hDB hBD
    rwa [inf_comm, h4] at h
  exact ⟨h1, h2, hDB, h3, h4, h5⟩

end CFSG.Quasithin.SteinbergBS
