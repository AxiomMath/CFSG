module

public import CFSG.LocalAnalysis.WeakClosure81.W16POneSetup
public import CFSG.LocalAnalysis.WeakClosure81.W18PackMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace ModDataE

variable {J E : Subgroup G} (D : ModDataE J E)

@[expose] def conjImgFam (V : Subgroup G) : Set (Subgroup (LGL 2 D.W)) :=
  {B | ∃ x ∈ J, B = D.img (conjSubgroup V x)}

@[expose] noncomputable def conjImgSpace (V₀ V : Subgroup G) (B : Subgroup (LGL 2 D.W)) :
    Submodule (ZMod 2) D.W :=
  ⨆ x : {x : G // x ∈ J ∧ D.img (conjSubgroup V x) = B}, D.sp (conjSubgroup V₀ x.1)

theorem le_centralizer_of_img_eq_bot {S : Subgroup G} (hS : S ≤ J) (h : D.img S = ⊥) :
    S ≤ centralizer (E : Set G) := by
  intro s hs
  have hmem : D.ρ ⟨s, hS hs⟩ ∈ D.img S := D.mem_img.2 ⟨⟨s, hS hs⟩, hs, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  simpa using (D.ρ_eq_one_iff ⟨s, hS hs⟩).1 hmem

theorem le_sup_of_img_eq {S₀ S : Subgroup G} (hS₀S : S₀ ≤ S) (hS : S ≤ J)
    (h : D.img S₀ = D.img S) : S ≤ S₀ ⊔ (S ⊓ centralizer (E : Set G)) := by
  intro s hs
  have hmem : D.ρ ⟨s, hS hs⟩ ∈ D.img S₀ := by
    rw [h]
    exact D.mem_img.2 ⟨⟨s, hS hs⟩, hs, rfl⟩
  obtain ⟨j, hjS₀, hj⟩ := D.mem_img.1 hmem
  have hz_mem : (j : G)⁻¹ * s ∈ S ⊓ centralizer (E : Set G) := by
    refine ⟨S.mul_mem (S.inv_mem (hS₀S hjS₀)) hs, ?_⟩
    have hz : D.ρ (j⁻¹ * ⟨s, hS hs⟩ : ↥J) = 1 := by
      rw [map_mul, map_inv, hj]
      group
    have hmem2 := (D.ρ_eq_one_iff (j⁻¹ * ⟨s, hS hs⟩ : ↥J)).1 hz
    simpa using hmem2
  have hmul : (j : G) * ((j : G)⁻¹ * s) ∈ S₀ ⊔ (S ⊓ centralizer (E : Set G)) :=
    Subgroup.mul_mem_sup hjS₀ hz_mem
  simpa [mul_assoc] using hmul

end ModDataE

section QuotientFixed

private theorem map_normalizerMonoidHom_subgroupOf {R K : Subgroup G}
    [(K.subgroupOf R).Normal] {y : Subgroup.normalizer (R : Set G)}
    (hy : (y : G) ∈ Subgroup.normalizer (K : Set G)) :
    (K.subgroupOf R).map (R.normalizerMonoidHom y : R →* R) = K.subgroupOf R := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (z : G) ∈ K := hz
    show (y : G) * z * (y : G)⁻¹ ∈ K
    exact (Subgroup.mem_normalizer_iff.mp hy z).mp hz'
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨⟨(y : G)⁻¹ * x * y, (Subgroup.mem_normalizer_iff''.mp y.2 x).mp x.2⟩,
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff''.mp hy x).mp hx),
      Subtype.ext ?_⟩
    change (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ = x
    group

private noncomputable def conjQuotHom (R K T : Subgroup G) [(K.subgroupOf R).Normal]
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    T →* MulAut (R ⧸ K.subgroupOf R) where
  toFun t := QuotientGroup.congr (K.subgroupOf R) (K.subgroupOf R)
    (R.normalizerMonoidHom ⟨t, hTR t.2⟩) (map_normalizerMonoidHom_subgroupOf (hTK t.2))
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    rw [QuotientGroup.congr_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change ((1 : T) : G) * x * ((1 : T) : G)⁻¹ = x
    simp
  map_mul' y y' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    congr 1
    apply Subtype.ext
    change ((y * y' : T) : G) * x * ((y * y' : T) : G)⁻¹ =
      (y : G) * ((y' : G) * x * (y' : G)⁻¹) * (y : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

private theorem conjQuotHom_mk (R K T : Subgroup G) [(K.subgroupOf R).Normal]
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (t : T) (x : R) :
    conjQuotHom R K T hTR hTK t (x : R ⧸ K.subgroupOf R) =
      ((⟨(t : G) * x * (t : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hTR t.2) x).mp x.2⟩ : R) :
        R ⧸ K.subgroupOf R) := rfl

private theorem exists_nonidentity_fixed_coset {R K T : Subgroup G} [(K.subgroupOf R).Normal]
    [Finite (R ⧸ K.subgroupOf R)] (hev : 2 ∣ Nat.card (R ⧸ K.subgroupOf R))
    (hT : IsPGroup 2 T) (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ∃ x ∈ R, x ∉ K ∧ ∀ v ∈ T, x⁻¹ * (v * x * v⁻¹) ∈ K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction T (R ⧸ K.subgroupOf R) :=
    MulAction.compHom (R ⧸ K.subgroupOf R) (conjQuotHom R K T hTR hTK)
  have h1 : (1 : R ⧸ K.subgroupOf R) ∈ MulAction.fixedPoints T (R ⧸ K.subgroupOf R) := by
    intro v
    change conjQuotHom R K T hTR hTK v 1 = 1
    exact map_one _
  obtain ⟨b, hb, hb1⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hev h1
  induction b using QuotientGroup.induction_on with | H x => ?_
  refine ⟨x, x.2, fun hxK => hb1 ?_, fun v hv => ?_⟩
  · exact ((QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hxK)).symm
  · have h2 : conjQuotHom R K T hTR hTK ⟨v, hv⟩ (x : R ⧸ K.subgroupOf R) = x := hb ⟨v, hv⟩
    rw [conjQuotHom_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    have h3 := inv_mem h2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] using h3

end QuotientFixed

private theorem isSylowIn_img'' {J E : Subgroup G} (M : ModDataE J E) {T : Subgroup G}
    (hT : IsSylowIn 2 T J) : IsSylowIn 2 (M.img T) (M.img J) := by
  have hrelidx : (M.img T).relIndex (M.img J) = ((T.subgroupOf J) ⊔ M.ρ.ker).index := by
    unfold ModDataE.img
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_map_map]
    simp
  have hdvd : ((T.subgroupOf J) ⊔ M.ρ.ker).index ∣ T.relIndex J :=
    Subgroup.index_dvd_of_le (H := T.subgroupOf J)
      (K := (T.subgroupOf J) ⊔ M.ρ.ker) le_sup_left
  refine ⟨M.img_mono hT.le, M.isPGroup_img hT.isPGroup, ?_⟩
  rw [hrelidx]
  exact fun h => hT.not_dvd_relIndex (h.trans hdvd)

private theorem conjGenerated_conjSubgroup {M V₀ V : Subgroup G} (hgen : ConjGenerated M V₀ V)
    (g : G) : ConjGenerated (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) := by
  intro a ha ha0
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 ha
  have hv0 : v ∉ V₀ := by
    intro hv0
    exact ha0 (Subgroup.mem_map.2 ⟨v, hv0, rfl⟩)
  rw [hgen v hv hv0]
  change (Subgroup.closure {x | ∃ m ∈ M, x = m * v * m⁻¹}).map
      (MulAut.conj g⁻¹).toMonoidHom =
    Subgroup.closure {x | ∃ m ∈ conjSubgroup M g, x = m * ((MulAut.conj g⁻¹) v) * m⁻¹}
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨m, hm, rfl⟩, hxy⟩
    refine ⟨(MulAut.conj g⁻¹) m, Subgroup.mem_map.2 ⟨m, hm, rfl⟩, ?_⟩
    rw [← hxy]
    simp [map_mul, map_inv]
  · rintro ⟨m, hm, hx⟩
    obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.1 hm
    refine ⟨m' * v * m'⁻¹, ⟨m', hm', rfl⟩, ?_⟩
    rw [hx]
    simp [map_mul, map_inv]

namespace Cfg161

variable {M V₀ V U : Subgroup G} {g : G}

private theorem conjSubgroup_V0_eq_of_img_eq (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (D : ModDataE (conjSubgroup M g) (conjSubgroup V g))
    {x y : G} (hx : x ∈ conjSubgroup M g) (hy : y ∈ conjSubgroup M g)
    (hxy : D.img (conjSubgroup V x) = D.img (conjSubgroup V y)) :
    conjSubgroup V₀ x = conjSubgroup V₀ y := by
  have hVJ : V ≤ conjSubgroup M g := c.le_conjSubgroup h152
  have hJnorm : conjSubgroup M g ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    calc conjSubgroup M g ≤ conjSubgroup (Subgroup.normalizer (V : Set G)) g :=
          Subgroup.map_mono (le_of_eq c.hyp.h6.normalizer_eq.symm)
      _ = Subgroup.normalizer (conjSubgroup V g : Set G) := E3.conjSubgroup_normalizer V g
  have hcomm : ⁅conjSubgroup V g, V⁆ ≤ V₀ :=
    Subgroup.commutator_le.2 fun a ha v hv => by
      simpa [commutatorElement_def] using
        (Subgroup.mem_inf.1 (commutator_mem h152 c v hv a ha)).1
  have hcomm_ne : ⁅conjSubgroup V g, V⁆ ≠ ⊥ := by
    intro hbot
    apply c.not_comm
    intro v hv a ha
    have h1 : ⁅V, conjSubgroup V g⁆ = ⊥ := by rwa [Subgroup.commutator_comm] at hbot
    have h2 : V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    exact (Subgroup.mem_centralizer_iff.1 (h2 hv) a ha).symm
  have hconj_le : ∀ z ∈ conjSubgroup M g, conjSubgroup V z ≤ conjSubgroup M g := by
    intro z hz
    calc conjSubgroup V z ≤ conjSubgroup (conjSubgroup M g) z := Subgroup.map_mono hVJ
      _ = conjSubgroup M g :=
          conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hz)
  have hcomm_conj : ∀ z ∈ conjSubgroup M g,
      ⁅conjSubgroup V g, conjSubgroup V z⁆ = conjSubgroup ⁅conjSubgroup V g, V⁆ z := by
    intro z hz
    have hE_map : (conjSubgroup V g).map (MulAut.conj z⁻¹).toMonoidHom = conjSubgroup V g :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hJnorm hz)
    calc ⁅conjSubgroup V g, conjSubgroup V z⁆
        = ⁅(conjSubgroup V g).map (MulAut.conj z⁻¹).toMonoidHom,
            V.map (MulAut.conj z⁻¹).toMonoidHom⁆ := by rw [hE_map]; rfl
      _ = (⁅conjSubgroup V g, V⁆).map (MulAut.conj z⁻¹).toMonoidHom :=
            (Subgroup.map_commutator (H₁ := conjSubgroup V g) (H₂ := V)
              (MulAut.conj z⁻¹).toMonoidHom).symm
      _ = conjSubgroup ⁅conjSubgroup V g, V⁆ z := rfl
  have hcomm_eq : ⁅conjSubgroup V g, conjSubgroup V x⁆ =
      ⁅conjSubgroup V g, conjSubgroup V y⁆ := by
    apply le_antisymm <;> intro e he
    · have heE : e ∈ conjSubgroup V g := D.commutator_le_E (hconj_le x hx) he
      have hmem : D.ι e ∈ commSub (D.img (conjSubgroup V y)) := by
        rw [← hxy]
        exact (D.mem_commSub_img_iff (hconj_le x hx) heE).2 he
      exact (D.mem_commSub_img_iff (hconj_le y hy) heE).1 hmem
    · have heE : e ∈ conjSubgroup V g := D.commutator_le_E (hconj_le y hy) he
      have hmem : D.ι e ∈ commSub (D.img (conjSubgroup V x)) := by
        rw [hxy]
        exact (D.mem_commSub_img_iff (hconj_le y hy) heE).2 he
      exact (D.mem_commSub_img_iff (hconj_le x hx) heE).1 hmem
  have hDconj : conjSubgroup ⁅conjSubgroup V g, V⁆ x =
      conjSubgroup ⁅conjSubgroup V g, V⁆ y := by
    rw [← hcomm_conj x hx, ← hcomm_conj y hy, hcomm_eq]
  obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcomm_ne
  have hdmem : (d : G) ∈ ⁅conjSubgroup V g, V⁆ := d.2
  have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdx_mem : x⁻¹ * (d : G) * x ∈ conjSubgroup ⁅conjSubgroup V g, V⁆ x := by
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hdmem
  have hdx_mem_y : x⁻¹ * (d : G) * x ∈ conjSubgroup ⁅conjSubgroup V g, V⁆ y :=
    hDconj ▸ hdx_mem
  have hdx_ne : x⁻¹ * (d : G) * x ≠ 1 := by
    intro h
    apply hd1'
    have := congrArg (fun z => x * z * x⁻¹) h
    simpa [mul_assoc] using this
  have hle_x : conjSubgroup ⁅conjSubgroup V g, V⁆ x ≤ conjSubgroup V₀ x :=
    Subgroup.map_mono hcomm
  have hle_y : conjSubgroup ⁅conjSubgroup V g, V⁆ x ≤ conjSubgroup V₀ y := by
    rw [hDconj]
    exact Subgroup.map_mono hcomm
  have hinf_ne : conjSubgroup V₀ x ⊓ conjSubgroup V₀ y ≠ ⊥ := by
    intro hbot
    exact hdx_ne (Subgroup.mem_bot.1 (hbot ▸ (le_inf hle_x hle_y hdx_mem)))
  have hyxM : y * x⁻¹ ∈ M := by
    by_contra hg
    have hTI := c.hyp.conj_inf_eq_bot hg
    rw [inf_comm] at hTI
    have hbot : conjSubgroup V₀ x ⊓ conjSubgroup V₀ y = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      have hzx : x * z * x⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hz.1
      have hzy : y * z * y⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hz.2
      have hz' : x * z * x⁻¹ ∈ conjSubgroup V₀ (y * x⁻¹) := by
        rw [mem_conjSubgroup_iff]
        have heq : (y * x⁻¹) * (x * z * x⁻¹) * (y * x⁻¹)⁻¹ = y * z * y⁻¹ := by group
        rw [heq]
        exact hzy
      have hmem : x * z * x⁻¹ ∈ V₀ ⊓ conjSubgroup V₀ (y * x⁻¹) := ⟨hzx, hz'⟩
      rw [hTI] at hmem
      have h1 : x * z * x⁻¹ = 1 := Subgroup.mem_bot.1 hmem
      have hz1 : z = x⁻¹ * (x * z * x⁻¹) * x := by group
      rw [hz1, h1]
      group
    exact hinf_ne hbot
  have hV0eq : conjSubgroup V₀ (y * x⁻¹) = V₀ :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (by rw [c.hyp.normalizer₀]; exact hyxM)
  have h := conjSubgroup_conjSubgroup V₀ (y * x⁻¹) x
  rw [show y * x⁻¹ * x = y by group] at h
  rw [hV0eq] at h
  exact h

theorem inf_pCoreOf_img (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (D : ModDataE (conjSubgroup M g) (conjSubgroup V g)) :
    D.img V ⊓ pCoreOf 2 (D.img (conjSubgroup M g)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVJ : V ≤ conjSubgroup M g := c.le_conjSubgroup h152
  have hV0V : V₀ ≤ V := c.hyp.h6.le
  have hJnormE : conjSubgroup M g ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    calc conjSubgroup M g ≤ conjSubgroup (Subgroup.normalizer (V : Set G)) g :=
          Subgroup.map_mono (le_of_eq c.hyp.h6.normalizer_eq.symm)
      _ = Subgroup.normalizer (conjSubgroup V g : Set G) := E3.conjSubgroup_normalizer V g
  have hJnormV0 : conjSubgroup M g ≤ Subgroup.normalizer (conjSubgroup V₀ g : Set G) := by
    calc conjSubgroup M g ≤ conjSubgroup (Subgroup.normalizer (V₀ : Set G)) g :=
          Subgroup.map_mono (le_of_eq c.hyp.normalizer₀.symm)
      _ = Subgroup.normalizer (conjSubgroup V₀ g : Set G) := E3.conjSubgroup_normalizer V₀ g
  set X : Subgroup (LGL 2 D.W) := pCoreOf 2 (D.img (conjSubgroup M g)) with hXdef
  have hXJ : X ≤ D.img (conjSubgroup M g) := by
    rw [hXdef]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hXpg : IsPGroup 2 X := by
    rw [hXdef]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hXnorm : (X.subgroupOf (D.img (conjSubgroup M g))).Normal :=
    (Subgroup.normal_subgroupOf_iff hXJ).mpr fun h k hh hk =>
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (D.img (conjSubgroup M g)) hk) h).1 hh
  have hXnormal : ∀ y ∈ D.img (conjSubgroup M g),
      X.map (MulAut.conj y).toMonoidHom = X := by
    intro y hy
    rw [hXdef]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (D.img (conjSubgroup M g))) hy)
  obtain ⟨T, hT, -⟩ := CFSG.Quasithin.exists_isSylowIn_ge 2
    (bot_le : (⊥ : Subgroup G) ≤ conjSubgroup M g) IsPGroup.of_bot
  have hTsyl : IsSylowIn 2 (D.img T) (D.img (conjSubgroup M g)) := isSylowIn_img'' D hT
  have hXT : X ≤ D.img T :=
    CFSG.Quasithin.IsSylowIn.le_of_normal hTsyl hXJ hXnorm hXpg
  have hUinv : ∀ y ∈ D.img (conjSubgroup M g),
      ∀ u ∈ D.sp (conjSubgroup V₀ g), y u ∈ D.sp (conjSubgroup V₀ g) := by
    intro y hy u hu
    obtain ⟨j, hjJ, rfl⟩ := D.mem_img.1 hy
    have h := D.conjSub_sp (conjSubgroup V₀ g) j
    have hV0' : conjSubgroup (conjSubgroup V₀ g) ((j : G)⁻¹) = conjSubgroup V₀ g :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormV0 ((conjSubgroup M g).inv_mem hjJ))
    rw [hV0'] at h
    change (D.ρ j) u ∈ D.sp (conjSubgroup V₀ g)
    rw [← h]
    exact Submodule.mem_map.2 ⟨u, hu, rfl⟩
  have hV0'_ne : conjSubgroup V₀ g ≠ conjSubgroup V g := by
    intro heq
    apply c.hyp.h6.ne_top c.hyp.ne_bot
    have h := congrArg (fun H => conjSubgroup H g⁻¹) heq
    simpa only [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] using h
  have hEab : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup c.hyp.h6.elemAbelian g
  haveI : IsMulCommutative ↥(conjSubgroup V g) := hEab.1
  have hev : 2 ∣ Nat.card (conjSubgroup V g ⧸
      (conjSubgroup V₀ g).subgroupOf (conjSubgroup V g)) := by
    rw [← Subgroup.index_eq_card]
    obtain ⟨n, hn⟩ := (B2F.isPGroup_of_isElemAbelian hEab).index
      ((conjSubgroup V₀ g).subgroupOf (conjSubgroup V g))
    rw [hn]
    refine dvd_pow_self 2 ?_
    intro h0
    rw [h0, pow_zero, Subgroup.index_eq_one] at hn
    exact hV0'_ne (le_antisymm (Subgroup.map_mono hV0V) (Subgroup.subgroupOf_eq_top.1 hn))
  obtain ⟨x, hxE, hxK, hxfix⟩ := exists_nonidentity_fixed_coset
    (R := conjSubgroup V g) (K := conjSubgroup V₀ g) (T := T) hev hT.isPGroup
    (hT.le.trans hJnormE) (hT.le.trans hJnormV0)
  let W : Subgroup G :=
    { carrier := {b | b ∈ conjSubgroup V g ∧
        ∀ y ∈ X, y (D.ι b) - D.ι b ∈ D.sp (conjSubgroup V₀ g)}
      one_mem' := ⟨(conjSubgroup V g).one_mem, by
        intro y hy; rw [D.ι_one, map_zero, sub_zero]; exact Submodule.zero_mem _⟩
      mul_mem' := fun {b b'} hb hb' => ⟨(conjSubgroup V g).mul_mem hb.1 hb'.1, by
        intro y hy
        have h := (D.sp (conjSubgroup V₀ g)).add_mem (hb.2 y hy) (hb'.2 y hy)
        convert h using 1
        rw [D.ι_mul b hb.1 b' hb'.1, map_add]
        abel⟩
      inv_mem' := fun {b} hb => ⟨(conjSubgroup V g).inv_mem hb.1, by
        intro y hy
        have h := (D.sp (conjSubgroup V₀ g)).neg_mem (hb.2 y hy)
        convert h using 1
        rw [D.ι_inv hb.1, map_neg]
        abel⟩ }
  have hxW : x⁻¹ ∈ W := by
    refine ⟨(conjSubgroup V g).inv_mem hxE, ?_⟩
    intro y hy
    obtain ⟨t, htT, hty⟩ := D.mem_img.1 (hXT hy)
    rw [← hty]
    have hmem : t * x⁻¹ * t⁻¹ * x ∈ conjSubgroup V₀ g := by
      have h := (conjSubgroup V₀ g).inv_mem (hxfix t htT)
      simpa only [mul_inv_rev, inv_inv, mul_assoc, Subgroup.coe_inv, Subgroup.coe_zpow,
        zpow_neg_one] using h
    have h1 : t * x⁻¹ * t⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 (hJnormE (hT.le htT)) x⁻¹).1
        ((conjSubgroup V g).inv_mem hxE)
    have hmemE : t * x⁻¹ * t⁻¹ * x ∈ conjSubgroup V g :=
      (conjSubgroup V g).mul_mem h1 hxE
    have hmul : D.ρ t (D.ι x⁻¹) - D.ι x⁻¹ = D.ι (t * x⁻¹ * t⁻¹ * x) := by
      rw [D.ρ_ι ⟨t, hT.le htT⟩ x⁻¹ ((conjSubgroup V g).inv_mem hxE), D.ι_inv hxE,
        D.ι_mul (t * x⁻¹ * t⁻¹) h1 x hxE]
      simp only [Subgroup.coe_mk, Subgroup.coe_inv, Subgroup.coe_zpow, zpow_neg_one, sub_neg_eq_add]
    change D.ρ t (D.ι x⁻¹) - D.ι x⁻¹ ∈ D.sp (conjSubgroup V₀ g)
    rw [hmul]
    exact D.mem_sp.2 ⟨_, ⟨hmem, hmemE⟩, rfl⟩
  have hJWforward : ∀ j ∈ conjSubgroup M g, ∀ b ∈ W, j * b * j⁻¹ ∈ W := by
    intro j hj b hb
    have hbE : b ∈ conjSubgroup V g := hb.1
    have hbW : ∀ y ∈ X, y (D.ι b) - D.ι b ∈ D.sp (conjSubgroup V₀ g) := hb.2
    have hjb : j * b * j⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 (hJnormE hj) b).1 hbE
    refine ⟨hjb, ?_⟩
    rw [← D.ρ_ι ⟨j, hj⟩ b hbE]
    intro y hy
    have hy' : (D.ρ ⟨j, hj⟩)⁻¹ * y * D.ρ ⟨j, hj⟩ ∈ X := by
      have h := hXnormal ((D.ρ ⟨j, hj⟩)⁻¹)
        ((D.img (conjSubgroup M g)).inv_mem (D.mem_img.2 ⟨⟨j, hj⟩, hj, rfl⟩))
      rw [← h]
      exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    have hycom : y * D.ρ ⟨j, hj⟩ =
        D.ρ ⟨j, hj⟩ * ((D.ρ ⟨j, hj⟩)⁻¹ * y * D.ρ ⟨j, hj⟩) := by group
    have hval : y (D.ρ ⟨j, hj⟩ (D.ι b)) =
        D.ρ ⟨j, hj⟩ (((D.ρ ⟨j, hj⟩)⁻¹ * y * D.ρ ⟨j, hj⟩) (D.ι b)) := by
      have hc := congrArg (fun f : LGL 2 D.W => f (D.ι b)) hycom
      simpa only [LinearEquiv.mul_apply] using hc
    have hdiff : y (D.ρ ⟨j, hj⟩ (D.ι b)) - D.ρ ⟨j, hj⟩ (D.ι b) =
        D.ρ ⟨j, hj⟩ (((D.ρ ⟨j, hj⟩)⁻¹ * y * D.ρ ⟨j, hj⟩) (D.ι b) - D.ι b) := by
      rw [map_sub, hval]
    rw [hdiff]
    exact hUinv (D.ρ ⟨j, hj⟩) (D.mem_img.2 ⟨⟨j, hj⟩, hj, rfl⟩) _
      (hbW _ hy')
  have hJW : conjSubgroup M g ≤ Subgroup.normalizer (W : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro b
    exact ⟨fun hb => hJWforward j hj b hb, fun hb => by
      have h := hJWforward j⁻¹ ((conjSubgroup M g).inv_mem hj) (j * b * j⁻¹) hb
      simpa [mul_assoc] using h⟩
  have hWE : W ≤ conjSubgroup V g := fun b hb => hb.1
  have hWnotle : ¬ W ≤ conjSubgroup V₀ g := fun hle =>
    hxK (by simpa using (conjSubgroup V₀ g).inv_mem (hle hxW))
  have hgen : ConjGenerated (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) :=
    conjGenerated_conjSubgroup (c.hyp.h6.conjGenerated c.hyp.ne_bot) g
  have hWeq : W = conjSubgroup V g :=
    eq_of_normalizer_of_not_le_of_conjGenerated hgen hWE hJW hWnotle
  have hV0inf : V₀ ⊓ conjSubgroup V₀ g = ⊥ := by
    rw [inf_comm]; exact c.hyp.conj_inf_eq_bot c.not_mem
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  obtain ⟨hrV, hrX⟩ := Subgroup.mem_inf.1 hr
  obtain ⟨j, hjV, hrj⟩ := D.mem_img.1 hrV
  have hrX' : D.ρ j ∈ X := by rw [hrj]; exact hrX
  have hcent : conjSubgroup V g ≤ Subgroup.centralizer ({(j : G)} : Set G) := by
    intro b hbE
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbW : b ∈ W := (le_of_eq hWeq.symm) hbE
    have hjbV0' : j * b * j⁻¹ * b⁻¹ ∈ conjSubgroup V₀ g := by
      have hmem : D.ρ j (D.ι b) - D.ι b ∈ D.sp (conjSubgroup V₀ g) :=
        hbW.2 (D.ρ j) hrX'
      have hdiff : D.ρ j (D.ι b) - D.ι b = D.ι (j * b * j⁻¹ * b⁻¹) := by
        have hjE : (j : G) * b * (j : G)⁻¹ ∈ conjSubgroup V g :=
          (Subgroup.mem_normalizer_iff.1 (hJnormE j.2) b).1 hbE
        rw [sub_eq_add_neg, D.ρ_ι j b hbE, ← D.ι_inv hbE]
        simp only [Subgroup.coe_inv, Subgroup.coe_zpow, zpow_neg_one]
        have hmul := D.ι_mul ((j : G) * b * (j : G)⁻¹) hjE b⁻¹
          ((conjSubgroup V g).inv_mem hbE)
        rw [← hmul]
      rw [hdiff] at hmem
      obtain ⟨e, he, heq⟩ := D.mem_sp.1 hmem
      have hbe : j * b * j⁻¹ * b⁻¹ ∈ conjSubgroup V g := by
        have h1 : j * b * j⁻¹ ∈ conjSubgroup V g :=
          (Subgroup.mem_normalizer_iff.1 (hJnormE j.2) b).1 hbE
        exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem hbE)
      rw [← D.ι_injOn he.2 hbe heq]
      exact he.1
    have hjbV0 : j * b * j⁻¹ * b⁻¹ ∈ V₀ := by
      have h := (Subgroup.mem_inf.1 (commutator_mem h152 c (j : G) hjV b hbE)).1
      have hinv : (b * (j : G) * b⁻¹ * (j : G)⁻¹)⁻¹ ∈ V₀ := V₀.inv_mem h
      have h1 : (b * (j : G) * b⁻¹ * (j : G)⁻¹)⁻¹ =
          (j : G) * b * (j : G)⁻¹ * b⁻¹ := by group
      rw [h1] at hinv
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, zpow_neg_one] using hinv
    have hinf : j * b * j⁻¹ * b⁻¹ ∈ V₀ ⊓ conjSubgroup V₀ g := ⟨hjbV0, hjbV0'⟩
    rw [hV0inf, Subgroup.mem_bot] at hinf
    calc b * (j : G) = (j * b * j⁻¹ * b⁻¹) * (b * (j : G)) := by rw [hinf]; group
      _ = (j : G) * b := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, zpow_neg_one]
            group
  have hjcent : (j : G) ∈ Subgroup.centralizer (conjSubgroup V g : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.1 (hcent hb)
  have hrho : D.ρ j = 1 := (D.ρ_eq_one_iff j).2 hjcent
  rw [← hrj, hrho]

private theorem mem_M_of_conjSubgroup_V0_inf_ne_bot (c : Cfg161 M V₀ V U g)
    {x y : G} (h : conjSubgroup V₀ x ⊓ conjSubgroup V₀ y ≠ ⊥) : y * x⁻¹ ∈ M := by
  by_contra hg
  have hTI := c.hyp.conj_inf_eq_bot hg
  rw [inf_comm] at hTI
  apply h
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzx : x * z * x⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hz.1
  have hzy : y * z * y⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hz.2
  have hz' : x * z * x⁻¹ ∈ conjSubgroup V₀ (y * x⁻¹) := by
    rw [mem_conjSubgroup_iff]
    have heq : (y * x⁻¹) * (x * z * x⁻¹) * (y * x⁻¹)⁻¹ = y * z * y⁻¹ := by group
    rw [heq]
    exact hzy
  have hmem : x * z * x⁻¹ ∈ V₀ ⊓ conjSubgroup V₀ (y * x⁻¹) := ⟨hzx, hz'⟩
  rw [hTI] at hmem
  have h1 : x * z * x⁻¹ = 1 := Subgroup.mem_bot.1 hmem
  have hz1 : z = x⁻¹ * (x * z * x⁻¹) * x := by group
  rw [hz1, h1]
  group

theorem assumption131 (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (D : ModDataE (conjSubgroup M g) (conjSubgroup V g)) :
    Assumption131 (D.img (conjSubgroup M g)) (D.conjImgFam V) (D.conjImgSpace V₀ V)
      (mRank (D.img V)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVJ : V ≤ conjSubgroup M g := c.le_conjSubgroup h152
  have hV0V : V₀ ≤ V := c.hyp.h6.le
  have hV0J : V₀ ≤ conjSubgroup M g := hV0V.trans hVJ
  have hE : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup c.hyp.h6.elemAbelian g
  have hJnormE : conjSubgroup M g ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    calc conjSubgroup M g ≤ conjSubgroup (Subgroup.normalizer (V : Set G)) g :=
          Subgroup.map_mono (le_of_eq c.hyp.h6.normalizer_eq.symm)
      _ = Subgroup.normalizer (conjSubgroup V g : Set G) := E3.conjSubgroup_normalizer V g
  have hJnormV0 : conjSubgroup M g ≤ Subgroup.normalizer (conjSubgroup V₀ g : Set G) := by
    calc conjSubgroup M g ≤ conjSubgroup (Subgroup.normalizer (V₀ : Set G)) g :=
          Subgroup.map_mono (le_of_eq c.hyp.normalizer₀.symm)
      _ = Subgroup.normalizer (conjSubgroup V₀ g : Set G) := E3.conjSubgroup_normalizer V₀ g
  have hconj_le : ∀ x ∈ conjSubgroup M g, conjSubgroup V x ≤ conjSubgroup M g := by
    intro z hz
    calc conjSubgroup V z ≤ conjSubgroup (conjSubgroup M g) z := Subgroup.map_mono hVJ
      _ = conjSubgroup M g :=
          conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hz)
  have hEab_conj : ∀ x ∈ conjSubgroup M g, IsElemAbelian 2 (conjSubgroup V x) :=
    fun x _ => E3.isElemAbelian_conjSubgroup c.hyp.h6.elemAbelian x
  have hcommI_V : ⁅conjSubgroup V g, V⁆ ≤ V₀ :=
    Subgroup.commutator_le.2 fun a ha v hv => by
      simpa [commutatorElement_def] using
        (Subgroup.mem_inf.1 (commutator_mem h152 c v hv a ha)).1
  have hcomm_ne : ⁅conjSubgroup V g, V⁆ ≠ ⊥ := by
    intro hbot
    apply c.not_comm
    intro v hv a ha
    have h1 : ⁅V, conjSubgroup V g⁆ = ⊥ := by rwa [Subgroup.commutator_comm] at hbot
    have h2 : V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    exact (Subgroup.mem_centralizer_iff.1 (h2 hv) a ha).symm
  have hcomm_conj_eq : ∀ z ∈ conjSubgroup M g,
      ⁅conjSubgroup V g, conjSubgroup V z⁆ = conjSubgroup ⁅conjSubgroup V g, V⁆ z := by
    intro z hz
    have hE_map : (conjSubgroup V g).map (MulAut.conj z⁻¹).toMonoidHom = conjSubgroup V g :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormE hz)
    calc ⁅conjSubgroup V g, conjSubgroup V z⁆
        = ⁅(conjSubgroup V g).map (MulAut.conj z⁻¹).toMonoidHom,
            V.map (MulAut.conj z⁻¹).toMonoidHom⁆ := by rw [hE_map]; rfl
      _ = (⁅conjSubgroup V g, V⁆).map (MulAut.conj z⁻¹).toMonoidHom :=
            (Subgroup.map_commutator (H₁ := conjSubgroup V g) (H₂ := V)
              (MulAut.conj z⁻¹).toMonoidHom).symm
      _ = conjSubgroup ⁅conjSubgroup V g, V⁆ z := rfl
  have hcomm_conj_le : ∀ z ∈ conjSubgroup M g,
      ⁅conjSubgroup V g, conjSubgroup V z⁆ ≤ conjSubgroup V₀ z := fun z hz =>
    (le_of_eq (hcomm_conj_eq z hz)).trans (Subgroup.map_mono hcommI_V)
  have hsingle : ∀ {x y : G}, x ∈ conjSubgroup M g → y ∈ conjSubgroup M g →
      D.img (conjSubgroup V x) = D.img (conjSubgroup V y) →
      conjSubgroup V₀ x = conjSubgroup V₀ y :=
    fun hx hy hxy => conjSubgroup_V0_eq_of_img_eq h152 c D hx hy hxy
  have hVA_eq : ∀ z : G, z ∈ conjSubgroup M g →
      D.conjImgSpace V₀ V (D.img (conjSubgroup V z)) = D.sp (conjSubgroup V₀ z) := by
    intro z hzJ
    rw [ModDataE.conjImgSpace]
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      rintro ⟨w, hwJ, hwEq⟩
      rw [hsingle hwJ hzJ hwEq]
    · exact le_iSup (fun w : {w : G // w ∈ conjSubgroup M g ∧
        D.img (conjSubgroup V w) = D.img (conjSubgroup V z)} => D.sp (conjSubgroup V₀ w.1))
        ⟨z, hzJ, rfl⟩
  have hVA_ne : ∀ A ∈ D.conjImgFam V, D.conjImgSpace V₀ V A ≠ ⊥ := by
    rintro A ⟨z, hzJ, rfl⟩
    rw [hVA_eq z hzJ]
    intro hbot
    have hinf : conjSubgroup V₀ z ⊓ conjSubgroup V g = ⊥ := D.sp_eq_bot_iff.mp hbot
    have hz' : conjSubgroup ⁅conjSubgroup V g, V⁆ z ≤ conjSubgroup V₀ z :=
      Subgroup.map_mono hcommI_V
    have hzE : conjSubgroup ⁅conjSubgroup V g, V⁆ z ≤ conjSubgroup V g := by
      calc conjSubgroup ⁅conjSubgroup V g, V⁆ z ≤ conjSubgroup (conjSubgroup V g) z :=
            Subgroup.map_mono (D.commutator_le_E hVJ)
        _ = conjSubgroup V g := conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormE hzJ)
    have hne : conjSubgroup ⁅conjSubgroup V g, V⁆ z ≠ ⊥ := by
      intro h
      apply hcomm_ne
      have h2 := congrArg (fun H => conjSubgroup H z⁻¹) h
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h2
      have hbot : conjSubgroup (⊥ : Subgroup G) z⁻¹ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        rw [mem_conjSubgroup_iff] at hx
        rw [inv_inv] at hx
        calc x = z * (z⁻¹ * x * z) * z⁻¹ := by group
          _ = z * 1 * z⁻¹ := by rw [hx]
          _ = 1 := by group
      rw [hbot] at h2
      exact h2
    refine hne (le_bot_iff.mp ?_)
    calc conjSubgroup ⁅conjSubgroup V g, V⁆ z ≤ conjSubgroup V₀ z ⊓ conjSubgroup V g :=
          le_inf hz' hzE
      _ = ⊥ := hinf
  have hinv : ∀ A ∈ D.conjImgFam V, ∀ r ∈ D.img (conjSubgroup M g),
      cj r A ∈ D.conjImgFam V := by
    rintro A ⟨x, hxJ, rfl⟩ r hr
    obtain ⟨y, hyJ, rfl⟩ := D.mem_img.1 hr
    refine ⟨x * (y : G)⁻¹, (conjSubgroup M g).mul_mem hxJ
      ((conjSubgroup M g).inv_mem y.2), ?_⟩
    rw [D.img_conj (hconj_le x hxJ) y, conjSubgroup_conjSubgroup]
  have hequiv : ∀ A ∈ D.conjImgFam V, ∀ r ∈ D.img (conjSubgroup M g),
      D.conjImgSpace V₀ V (cj r A) = conjSub r (D.conjImgSpace V₀ V A) := by
    rintro A ⟨x, hxJ, rfl⟩ r hr
    obtain ⟨y, hyJ, rfl⟩ := D.mem_img.1 hr
    rw [D.img_conj (hconj_le x hxJ) y, conjSubgroup_conjSubgroup,
      hVA_eq (x * (y : G)⁻¹) ((conjSubgroup M g).mul_mem hxJ
        ((conjSubgroup M g).inv_mem y.2)),
      hVA_eq x hxJ, D.conjSub_sp (conjSubgroup V₀ x) y, conjSubgroup_conjSubgroup]
  have hdisj : ∀ A ∈ D.conjImgFam V, ∀ B ∈ D.conjImgFam V, A ≠ B →
      D.conjImgSpace V₀ V A ⊓ D.conjImgSpace V₀ V B = ⊥ := by
    rintro A ⟨x, hxJ, rfl⟩ B ⟨y, hyJ, rfl⟩ hne
    have hbot : conjSubgroup V₀ x ⊓ conjSubgroup V₀ y = ⊥ := by
      by_contra hinf_ne
      have hyxM : y * x⁻¹ ∈ M := mem_M_of_conjSubgroup_V0_inf_ne_bot c hinf_ne
      have hV0eq : conjSubgroup V₀ (y * x⁻¹) = V₀ :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (by rw [c.hyp.normalizer₀]; exact hyxM)
      have hV0xy : conjSubgroup V₀ x = conjSubgroup V₀ y := by
        have h := conjSubgroup_conjSubgroup V₀ (y * x⁻¹) x
        rw [show y * x⁻¹ * x = y by group] at h
        rw [hV0eq] at h
        exact h
      have hVeq : conjSubgroup V (y * x⁻¹) = V :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (by rw [c.hyp.h6.normalizer_eq]; exact hyxM)
      have hVxy : conjSubgroup V x = conjSubgroup V y := by
        have h := conjSubgroup_conjSubgroup V (y * x⁻¹) x
        rw [show y * x⁻¹ * x = y by group] at h
        rw [hVeq] at h
        exact h
      exact hne (by rw [hVxy])
    rw [hVA_eq x hxJ, hVA_eq y hyJ, ← D.sp_inf, hbot]
    exact D.sp_eq_bot_iff.2 (by simp)
  have hVnt : D.img V ≠ ⊥ := by
    intro hbot
    apply c.not_comm
    intro x hx y hy
    have hcent : V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
      D.le_centralizer_of_img_eq_bot hVJ hbot
    exact (Subgroup.mem_centralizer_iff.1 (hcent hx) y hy).symm
  have hcardV : 1 < Nat.card (D.img V) := by
    have hne1 : Nat.card (D.img V) ≠ 1 := fun hc => hVnt (Subgroup.card_eq_one.mp hc)
    have hpos : 0 < Nat.card (D.img V) := Nat.card_pos
    omega
  refine
    { pos_i := ?_
      le_G := ?_
      isElemAb := ?_
      invariant := hinv
      ne_bot := ?_
      inf_pCore := ?_
      normalizer_eq := ?_
      disjoint := hdisj
      cond2 := ?_
      quadratic := ?_
      equivariant := hequiv }
  · show 0 < mRank (D.img V)
    rw [mRank]
    exact Nat.log_pos (by norm_num) hcardV
  · rintro A ⟨x, hxJ, rfl⟩
    exact D.img_mono (hconj_le x hxJ)
  · rintro A ⟨x, hxJ, rfl⟩
    exact D.isElemAbelian_img (hEab_conj x hxJ)
  · rintro A ⟨x, hxJ, rfl⟩ hbot
    have hcard : Nat.card (D.img (conjSubgroup V x)) = Nat.card (D.img V) := by
      have h1 := D.img_conj hVJ (⟨x⁻¹, (conjSubgroup M g).inv_mem hxJ⟩ :
        ↥(conjSubgroup M g))
      simp only [Subgroup.coe_inv, Subgroup.coe_zpow, zpow_neg_one, inv_inv] at h1
      rw [← h1]
      exact card_cj (A := D.img V)
        (D.ρ (⟨x⁻¹, (conjSubgroup M g).inv_mem hxJ⟩ : ↥(conjSubgroup M g)))
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos : 0 < Nat.card (D.img V) := Nat.card_pos
    omega
  · rintro A ⟨x, hxJ, rfl⟩
    have himg : D.img (conjSubgroup V x) =
        cj (D.ρ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g))) (D.img V) := by
      have h := D.img_conj hVJ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g))
      simp only [Subgroup.coe_inv, Subgroup.coe_zpow, zpow_neg_one, inv_inv] at h
      exact h.symm
    have hX : cj (D.ρ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g)))
        (pCoreOf 2 (D.img (conjSubgroup M g))) = pCoreOf 2 (D.img (conjSubgroup M g)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (D.img (conjSubgroup M g)))
          (D.mem_img.2 ⟨⟨x, hxJ⟩⁻¹, (conjSubgroup M g).inv_mem hxJ, rfl⟩))
    have hmapinf : cj (D.ρ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g)))
        (D.img V ⊓ pCoreOf 2 (D.img (conjSubgroup M g))) =
        cj (D.ρ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g))) (D.img V) ⊓
          cj (D.ρ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g)))
            (pCoreOf 2 (D.img (conjSubgroup M g))) :=
      Subgroup.map_inf (D.img V) (pCoreOf 2 (D.img (conjSubgroup M g)))
        (MulAut.conj (D.ρ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g)))).toMonoidHom
        (MulAut.conj (D.ρ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g)))).injective
    rw [himg, ← hX, ← hmapinf, inf_pCoreOf_img h152 c D]
    simp only [cj, Subgroup.map_bot]
  · rintro A ⟨x, hxJ, rfl⟩
    ext g
    constructor
    · rintro ⟨hgG, hgN⟩
      refine ⟨hgG, ?_⟩
      have hcj : cj g (D.img (conjSubgroup V x)) = D.img (conjSubgroup V x) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
      have h := hequiv (D.img (conjSubgroup V x)) ⟨x, hxJ, rfl⟩ g hgG
      rw [hcj] at h
      exact h.symm
    · rintro ⟨hgG, hgS⟩
      refine ⟨hgG, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
      by_contra hne
      have hmem : cj g (D.img (conjSubgroup V x)) ∈ D.conjImgFam V :=
        hinv (D.img (conjSubgroup V x)) ⟨x, hxJ, rfl⟩ g hgG
      have hdis := hdisj (D.img (conjSubgroup V x)) ⟨x, hxJ, rfl⟩
        (cj g (D.img (conjSubgroup V x))) hmem (Ne.symm hne)
      have hVAg : D.conjImgSpace V₀ V (cj g (D.img (conjSubgroup V x))) =
          D.conjImgSpace V₀ V (D.img (conjSubgroup V x)) := by
        rw [hequiv (D.img (conjSubgroup V x)) ⟨x, hxJ, rfl⟩ g hgG, hgS]
      rw [hVAg, inf_idem] at hdis
      exact hVA_ne (D.img (conjSubgroup V x)) ⟨x, hxJ, rfl⟩ hdis
  · rintro A ⟨x, hxJ, rfl⟩ B hBA _
    obtain ⟨B₀, hB₀Vx, -, hB₀img⟩ :=
      D.exists_preimage (A := conjSubgroup V x) (hconj_le x hxJ) (B' := B) hBA
    have hB₀_le : B₀ ≤ conjSubgroup M g := hB₀Vx.trans (hconj_le x hxJ)
    rw [hVA_eq x hxJ, ← hB₀img, D.fixSub_img hB₀_le]
    refine D.commSpace_img_sp_le (hconj_le x hxJ) ?_
    exact (Subgroup.commutator_mono inf_le_right le_rfl).trans (hcomm_conj_le x hxJ)
  · rintro A ⟨x, hxJ, rfl⟩
    refine D.commSpace_commSub_img_eq_bot (hconj_le x hxJ) ?_
    have h2 : ⁅conjSubgroup V₀ x, conjSubgroup V x⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (B2F.isElemAbelian_comm (hEab_conj x hxJ) (Subgroup.map_mono hV0V ha) hb).symm
    exact le_bot_iff.mp ((Subgroup.commutator_mono (hcomm_conj_le x hxJ) le_rfl).trans
      (le_of_eq h2))


theorem mRank_le (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (D : ModDataE (conjSubgroup M g) (conjSubgroup V g)) :
    ∀ B ∈ D.conjImgFam V, mRank B ≤ mRank (D.img V) := by
  rintro B ⟨x, hxJ, rfl⟩
  have hVJ : V ≤ conjSubgroup M g := c.le_conjSubgroup h152
  have hconj := D.img_conj hVJ (⟨x, hxJ⟩⁻¹ : ↥(conjSubgroup M g))
  simp only [Subgroup.coe_inv, inv_inv] at hconj
  rw [← hconj]
  simp only [mRank, card_cj]
  exact le_refl _

theorem conjImgSpace_le_fixSub (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (D : ModDataE (conjSubgroup M g) (conjSubgroup V g)) :
    ∀ B ∈ D.conjImgFam V, D.conjImgSpace V₀ V B ≤ fixSub B := by
  rintro B ⟨x, hxJ, rfl⟩
  rw [ModDataE.conjImgSpace]
  refine iSup_le ?_
  rintro ⟨y, hyJ, hyEq⟩
  intro w hw b hb
  rw [ModDataE.mem_sp] at hw
  obtain ⟨e, ⟨heV₀y, heE⟩, rfl⟩ := hw
  have hb' : b ∈ D.img (conjSubgroup V y) := hyEq ▸ hb
  obtain ⟨j, hjVy, rfl⟩ := D.mem_img.1 hb'
  rw [D.ρ_ι j e heE]
  congr 1
  have heVy : e ∈ conjSubgroup V y := (Subgroup.map_mono c.hyp.h6.le) heV₀y
  have hEab : IsElemAbelian 2 (conjSubgroup V y) :=
    E3.isElemAbelian_conjSubgroup c.hyp.h6.elemAbelian y
  exact mul_inv_eq_iff_eq_mul.mpr (B2F.isElemAbelian_comm hEab hjVy heVy)

theorem normalizer_img_le (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (D : ModDataE (conjSubgroup M g) (conjSubgroup V g)) :
    D.img (conjSubgroup M g) ⊓ Subgroup.normalizer (D.img V : Set (LGL 2 D.W)) ≤
      Subgroup.normalizer (D.img V₀ : Set (LGL 2 D.W)) := by
  intro r hr
  obtain ⟨hrJ, hrN⟩ := Subgroup.mem_inf.1 hr
  obtain ⟨x, hxJ, hrx⟩ := D.mem_img.1 hrJ
  rw [← hrx] at hrN ⊢
  have hVJ : V ≤ conjSubgroup M g := c.le_conjSubgroup h152
  have hV0J : V₀ ≤ conjSubgroup M g := c.hyp.h6.le.trans hVJ
  have hcj : cj (D.ρ x) (D.img V) = D.img V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hrN
  have himg := D.img_conj hVJ x
  rw [hcj] at himg
  have hsingle := conjSubgroup_V0_eq_of_img_eq h152 c D (x := x⁻¹)
    ((conjSubgroup M g).inv_mem hxJ) ((conjSubgroup M g).one_mem)
    (by rw [conjSubgroup_one]; exact himg.symm)
  rw [conjSubgroup_one] at hsingle
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  change cj (D.ρ x) (D.img V₀) = D.img V₀
  rw [D.img_conj hV0J x, hsingle]

end Cfg161

end CFSG.LocalAnalysis.WeakClosure81

end
