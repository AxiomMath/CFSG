module

public import CFSG.RankThree.PartTwo.Sec18.Item187F10Wsub
public import CFSG.RankThree.PartTwo.Sec18.Item187F2OTwoFiveSup
public import CFSG.RankThree.PartTwo.Sec18.Item187F5Pair
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centerOf tripleOf)

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

@[expose] noncomputable def actOn (W₁ Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (W₁ : Set G)) :
    ↥Y →* MulAut ↥W₁ :=
  letI := CFSG.ABGTheoremB.TotallyInverted.Omnibus.conjActOn Y W₁ hY
  MulDistribMulAction.toMulAut ↥Y ↥W₁

private theorem actOn_apply_coe (W₁ Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (W₁ : Set G))
    (y : ↥Y) (w : ↥W₁) : ((actOn W₁ Y hY y) w : G) = (y : G) * (w : G) * (y : G)⁻¹ := rfl

theorem ker_actOn (W₁ Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (W₁ : Set G)) :
    (actOn W₁ Y hY).ker = (Subgroup.centralizer (W₁ : Set G)).subgroupOf Y := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    have h1 : actOn W₁ Y hY y ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [h, MulAut.one_apply]
    have h2 := congrArg Subtype.val h1
    rw [actOn_apply_coe] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · intro h
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [actOn_apply_coe, MulAut.one_apply]
    have hw := h (w : G) w.2
    rw [← hw, mul_inv_cancel_right]

private theorem mem_Fix_iff {V : Type} [Group V] (F : Subgroup (MulAut V)) (v : V) :
    v ∈ Fix F ↔ ∀ f ∈ F, f v = v :=
  ⟨fun h f hf => (FixedPoints.mem_subgroup _ _ _).mp h ⟨f, hf⟩,
    fun h => (FixedPoints.mem_subgroup _ _ _).mpr fun m => h m.1 m.2⟩

theorem card_Fix_actOn (W₁ Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (W₁ : Set G))
    {E : Subgroup G} (hEY : E ≤ Y) :
    Nat.card (Fix ((E.subgroupOf Y).map (actOn W₁ Y hY))) =
      Nat.card ↥(W₁ ⊓ Subgroup.centralizer (E : Set G)) := by
  have hmap : (Fix ((E.subgroupOf Y).map (actOn W₁ Y hY))).map W₁.subtype =
      W₁ ⊓ Subgroup.centralizer (E : Set G) := by
    ext g
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
      have hf : actOn W₁ Y hY ⟨e, hEY he⟩ ∈ (E.subgroupOf Y).map (actOn W₁ Y hY) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr he)
      have h1 := congrArg Subtype.val ((mem_Fix_iff _ _).mp hw _ hf)
      rw [actOn_apply_coe] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    · intro hg
      obtain ⟨hgW, hgC⟩ := Subgroup.mem_inf.mp hg
      refine ⟨⟨g, hgW⟩, (mem_Fix_iff _ _).mpr ?_, rfl⟩
      rintro f hf
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hf
      refine Subtype.ext ?_
      have hyg : (y : G) * g = g * (y : G) :=
        Subgroup.mem_centralizer_iff.mp hgC (y : G) (Subgroup.mem_subgroupOf.mp hy)
      rw [actOn_apply_coe]
      show (y : G) * g * (y : G)⁻¹ = g
      rw [hyg, mul_inv_cancel_right]
  rw [← Subgroup.card_map_of_injective W₁.subtype_injective, hmap]

@[expose] noncomputable def MinCex.psi (hX : MinCex A M H c X) :
    ↥(X ⊔ Subgroup.zpowers c) →* MulAut ↥(W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) :=
  actOn _ _ (MinCex.sup_zpowers_le_normalizer_W1 hX)

private theorem psi_apply_coe (hX : MinCex A M H c X) (z : ↥(X ⊔ Subgroup.zpowers c))
    (w : ↥(W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)))) :
    ((MinCex.psi hX z) w : G) = (z : G) * (w : G) * (z : G)⁻¹ := rfl

theorem MinCex.image_eq (h186 : Item186H) (hX : MinCex A M H c X) (hsol : Group.IsSolvable ↥X)
    (h5 : 5 ∣ Nat.card X) {Y : Type} [Group Y] (ψ : ↥(X ⊔ Subgroup.zpowers c) →* Y) :
    (X.subgroupOf (X ⊔ Subgroup.zpowers c)).map ψ =
      ((oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c)).map ψ ⊔
        ((CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf (X ⊔ Subgroup.zpowers c)).map ψ := by
  have hsup := MinCex.sup_oTwoFive_eq h186 hX hsol h5
  have hPX : oTwoFive X ≤ X := oTwoFive_le X
  have hSX : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ X := hX.pCoreOf_le
  have hsub : X.subgroupOf (X ⊔ Subgroup.zpowers c) =
      (oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c) ⊔
        (CFSG.Open.pCoreOf 2 (H ⊓ M)).subgroupOf (X ⊔ Subgroup.zpowers c) := by
    rw [← Subgroup.subgroupOf_sup (hPX.trans le_sup_left) (hSX.trans le_sup_left), hsup]
  rw [hsub, Subgroup.map_sup]

private theorem pCoreOf_le_centralizer_W1 (h186 : Item186H) (hX : MinCex A M H c X) :
    CFSG.Open.pCoreOf 2 X ≤
      Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwW : w ∈ Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) := Sec3.omegaG_le _ hw
  exact (mem_centerOf_iff.mp (MinCex.Wsub_le h186 hX hwW)).2 q hq

private theorem psi_eq_one_of_mem_pCoreOf (h186 : Item186H) (hX : MinCex A M H c X)
    {z : ↥(X ⊔ Subgroup.zpowers c)} (hz : (z : G) ∈ CFSG.Open.pCoreOf 2 X) :
    MinCex.psi hX z = 1 := by
  refine MulEquiv.ext fun w => Subtype.ext ?_
  rw [psi_apply_coe, MulAut.one_apply]
  have hw := Subgroup.mem_centralizer_iff.mp (pCoreOf_le_centralizer_W1 h186 hX hz) (w : G) w.2
  rw [← hw, mul_inv_cancel_right]

theorem MinCex.isPGroup_five_image (h186 : Item186H) (hX : MinCex A M H c X)
    (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X) :
    IsPGroup 5 (((oTwoFive X).subgroupOf (X ⊔ Subgroup.zpowers c)).map (MinCex.psi hX)) := by
  intro g
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp g.2
  obtain ⟨n, hn⟩ := exists_pow_mem_pCoreOf (Subgroup.mem_subgroupOf.mp hy)
  refine ⟨n, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyg, ← map_pow]
  exact psi_eq_one_of_mem_pCoreOf h186 hX (by rw [Subgroup.coe_pow]; exact hn)

private theorem actOn_eq_one_iff (W₁ Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (W₁ : Set G))
    (y : ↥Y) : actOn W₁ Y hY y = 1 ↔ (y : G) ∈ Subgroup.centralizer (W₁ : Set G) := by
  rw [← MonoidHom.mem_ker, ker_actOn, Subgroup.mem_subgroupOf]

private theorem normalizerMonoidHom_apply_coe (W : Subgroup G)
    (γ : ↥(Subgroup.normalizer (W : Set G))) (w : ↥W) :
    ((Subgroup.normalizerMonoidHom W γ w : ↥W) : G) = (γ : G) * (w : G) * (γ : G)⁻¹ := rfl

private theorem conj_actOn_eq (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (γ : ↥(Subgroup.normalizer (W : Set G))) (hγX : (γ : G) ∈ Subgroup.normalizer (X : Set G))
    (x : ↥X) :
    Subgroup.normalizerMonoidHom W γ * actOn W X hXW x *
        (Subgroup.normalizerMonoidHom W γ)⁻¹ =
      actOn W X hXW ⟨(γ : G) * (x : G) * (γ : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hγX (x : G)).mp x.2⟩ := by
  rw [← map_inv]
  refine MulEquiv.ext fun w => Subtype.ext ?_
  simp only [MulAut.mul_apply, normalizerMonoidHom_apply_coe, actOn_apply_coe,
    Subgroup.coe_inv, inv_inv]
  group

private theorem normalizerMonoidHom_mem_normalizer_range (W X : Subgroup G)
    (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (γ : ↥(Subgroup.normalizer (W : Set G))) (hγX : (γ : G) ∈ Subgroup.normalizer (X : Set G)) :
    Subgroup.normalizerMonoidHom W γ ∈
      Subgroup.normalizer ((actOn W X hXW).range : Set (MulAut ↥W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hk
    exact MonoidHom.mem_range.mpr ⟨_, (conj_actOn_eq W X hXW γ hγX x).symm⟩
  · intro hk
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hk
    have key := conj_actOn_eq W X hXW γ⁻¹ (inv_mem hγX) y
    rw [map_inv, inv_inv] at key
    refine MonoidHom.mem_range.mpr ⟨_, key.symm.trans ?_⟩
    rw [hy]
    group

private noncomputable abbrev imO2 (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    Subgroup (MulAut ↥W) :=
  (CFSG.pCore 2 ↥(actOn W X hXW).range).map (actOn W X hXW).range.subtype

private noncomputable abbrev preO2 (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    Subgroup G :=
  ((imO2 W X hXW).comap (actOn W X hXW)).map X.subtype

private theorem imO2_isPGroup (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    {t : MulAut ↥W} (ht : t ∈ imO2 W X hXW) : ∃ n : ℕ, t ^ 2 ^ n = 1 := by
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(actOn W X hXW).range)) ⟨γ, hγ⟩
  refine ⟨n, ?_⟩
  have h1 := congrArg (fun z : ↥(CFSG.pCore 2 ↥(actOn W X hXW).range) =>
    ((z : ↥(actOn W X hXW).range) : MulAut ↥W)) hn
  simpa using h1

private theorem normalizer_imO2 (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    Subgroup.normalizerMonoidHom W ⟨g, hgW⟩ ∈
      Subgroup.normalizer (imO2 W X hXW : Set (MulAut ↥W)) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (CFSG.pCore 2 ↥(actOn W X hXW).range)
    (normalizerMonoidHom_mem_normalizer_range W X hXW ⟨g, hgW⟩ hgX)

private theorem preO2_conj_mem (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) {h : G} (hh : h ∈ preO2 W X hXW) :
    g * h * g⁻¹ ∈ preO2 W X hXW := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hh
  refine Subgroup.mem_map.mpr
    ⟨⟨g * (u : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgX (u : G)).mp u.2⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap] at hu ⊢
  have key := conj_actOn_eq W X hXW ⟨g, hgW⟩ hgX u
  have hmem := (Subgroup.mem_normalizer_iff.mp (normalizer_imO2 W X hXW hgX hgW) _).mp hu
  rw [key] at hmem
  exact hmem

private theorem le_normalizer_preO2 (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer (preO2 W X hXW : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact preO2_conj_mem W X hXW hgX hgW
  · intro hh
    have := preO2_conj_mem W X hXW (inv_mem hgX) (inv_mem hgW) hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

private theorem conj_mem_inf_centralizer (W X : Subgroup G)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) {g h : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgW : g ∈ Subgroup.normalizer (W : Set G))
    (hh : h ∈ X ⊓ Subgroup.centralizer (W : Set G)) :
    g * h * g⁻¹ ∈ X ⊓ Subgroup.centralizer (W : Set G) := by
  obtain ⟨hhX, hhC⟩ := Subgroup.mem_inf.mp hh
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgX h).mp hhX, ?_⟩
  have key := conj_actOn_eq W X hXW ⟨g, hgW⟩ hgX ⟨h, hhX⟩
  rw [(actOn_eq_one_iff W X hXW ⟨h, hhX⟩).mpr hhC, mul_one, mul_inv_cancel] at key
  exact (actOn_eq_one_iff W X hXW ⟨g * h * g⁻¹, _⟩).mp key.symm

private theorem le_normalizer_inf_centralizer (W X : Subgroup G)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_inf_centralizer W X hXW hgX hgW
  · intro hh
    have := conj_mem_inf_centralizer W X hXW (inv_mem hgX) (inv_mem hgW) hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

private theorem inf_centralizer_le_preO2 (W X : Subgroup G)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    X ⊓ Subgroup.centralizer (W : Set G) ≤ preO2 W X hXW := by
  intro z hz
  obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.mp hz
  have h1 : actOn W X hXW ⟨z, hzX⟩ = 1 := (actOn_eq_one_iff W X hXW ⟨z, hzX⟩).mpr hzC
  exact Subgroup.mem_map.mpr ⟨⟨z, hzX⟩, Subgroup.mem_comap.mpr (by rw [h1]; exact one_mem _), rfl⟩

private theorem preO2_pow_mem (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    ∀ u ∈ preO2 W X hXW, ∃ n : ℕ, u ^ 2 ^ n ∈ X ⊓ Subgroup.centralizer (W : Set G) := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨n, hn⟩ := imO2_isPGroup W X hXW (Subgroup.mem_comap.mp hv)
  refine ⟨n, ?_⟩
  have h1 : actOn W X hXW (v ^ 2 ^ n) = 1 := by rw [map_pow]; exact hn
  rw [← map_pow]
  exact Subgroup.mem_inf.mpr ⟨(v ^ 2 ^ n).2, (actOn_eq_one_iff W X hXW (v ^ 2 ^ n)).mp h1⟩

private theorem imO2_le_bot (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (hU : preO2 W X hXW ≤ X ⊓ Subgroup.centralizer (W : Set G)) : imO2 W X hXW ≤ ⊥ := by
  intro t ht
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp γ.2
  have hxU : x ∈ (imO2 W X hXW).comap (actOn W X hXW) :=
    Subgroup.mem_comap.mpr (by rw [hx]; exact Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)
  have hxC : (x : G) ∈ Subgroup.centralizer (W : Set G) :=
    (Subgroup.mem_inf.mp (hU (Subgroup.mem_map_of_mem X.subtype hxU))).2
  rw [Subgroup.mem_bot]
  show (γ : MulAut ↥W) = 1
  rw [← hx, (actOn_eq_one_iff W X hXW x).mpr hxC]

private theorem le_imO2_of_normal (W X : Subgroup G) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    {N : Subgroup (MulAut ↥W)} (hNΓ : N ≤ (actOn W X hXW).range)
    (hn : (actOn W X hXW).range ≤ Subgroup.normalizer (N : Set (MulAut ↥W))) (hN2 : IsPGroup 2 N) :
    N ≤ imO2 W X hXW := by
  intro t ht
  have hK : (N.subgroupOf (actOn W X hXW).range).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNΓ).mpr hn
  have hK2 : IsPGroup 2 ↥(N.subgroupOf (actOn W X hXW).range) := by
    intro g
    obtain ⟨k, hk⟩ :=
      hN2 ⟨((g : ↥(actOn W X hXW).range) : MulAut ↥W), Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa using h1
  have hKle : N.subgroupOf (actOn W X hXW).range ≤ CFSG.pCore 2 ↥(actOn W X hXW).range :=
    le_sSup (show N.subgroupOf (actOn W X hXW).range ∈
      {K : Subgroup ↥(actOn W X hXW).range | K.Normal ∧ IsPGroup 2 K} from ⟨hK, hK2⟩)
  exact Subgroup.mem_map.mpr ⟨⟨t, hNΓ ht⟩, hKle (Subgroup.mem_subgroupOf.mpr ht), rfl⟩

private theorem omegaG_le_centerOf' (S : Subgroup G) : Sec3.omegaG S ≤ centerOf S := by
  intro t ht
  exact mem_centerOf_iff.mpr ⟨(Sec3.mem_omegaG.mp ht).1, (Sec3.mem_omegaG.mp ht).2.1⟩

private theorem le_centralizer_centerOf' (S : Subgroup G) :
    S ≤ Subgroup.centralizer (centerOf S : Set G) := by
  intro s hs
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact (mem_centerOf_iff.mp hz).2 s hs

private theorem centerOf_le_Wsub' (X S : Subgroup G) : centerOf S ≤ Wsub X S := by
  intro z hz
  unfold Wsub
  exact Subgroup.subset_closure ⟨1, one_mem X, z, hz, by group⟩

private theorem le_normalizer_of_le_centralizer {T W K : Subgroup G} (hTW : T ≤ W)
    (hKW : K ≤ Subgroup.centralizer (W : Set G)) : K ≤ Subgroup.normalizer (T : Set G) := by
  intro v hv
  have hvT : v ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_iff.mp (hKW hv) t (hTW ht)
  exact Subgroup.centralizer_le_normalizer (T : Set G) hvT

private theorem omegaG_le_W1' (h186 : Item186H) (hX : MinCex A M H c X) :
    Sec3.omegaG (CFSG.Open.pCoreOf 2 (H ⊓ M)) ≤ W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) := by
  intro t ht
  have htW : t ∈ Wsub X (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
    centerOf_le_Wsub' X _ (omegaG_le_centerOf' _ ht)
  refine Sec3.mem_omegaG.mpr ⟨htW, fun w hw => ?_, (Sec3.mem_omegaG.mp ht).2.2⟩
  have hwQ := (mem_centerOf_iff.mp (MinCex.Wsub_le h186 hX hw)).1
  exact (mem_centerOf_iff.mp (MinCex.Wsub_le h186 hX htW)).2 w hwQ

private theorem tripleOf_two_eq_omegaG' (S : Subgroup G) : tripleOf S 2 = Sec3.omegaG S :=
  (tripleOf_two_eq S).trans (Item181ThreeProof.fourChar_zero S)

theorem MinCex.image_O2_trivial (h186 : Item186H) (hX : MinCex A M H c X)
    (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X) (hbad : BadCase A M H X)
    (N : Subgroup (MulAut ↥(W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)))))
    (hNΓ : N ≤ (X.subgroupOf (X ⊔ Subgroup.zpowers c)).map (MinCex.psi hX))
    (hn : (X.subgroupOf (X ⊔ Subgroup.zpowers c)).map (MinCex.psi hX) ≤
      Subgroup.normalizer (N : Set _))
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold BadCase at hbad
  obtain ⟨-, -, hbad2⟩ := hbad
  have hXW : X ≤ Subgroup.normalizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    le_sup_left.trans (MinCex.sup_zpowers_le_normalizer_W1 hX)
  have hΓeq : (X.subgroupOf (X ⊔ Subgroup.zpowers c)).map (MinCex.psi hX) =
      (actOn (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW).range := by
    ext γ
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine MonoidHom.mem_range.mpr ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
      exact MulEquiv.ext fun w => Subtype.ext
        ((actOn_apply_coe _ _ _ ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩ w).trans
          (psi_apply_coe hX y w).symm)
    · intro hγ
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hγ
      refine Subgroup.mem_map.mpr
        ⟨⟨(x : G), (le_sup_left : X ≤ X ⊔ Subgroup.zpowers c) x.2⟩,
          Subgroup.mem_subgroupOf.mpr x.2, ?_⟩
      exact MulEquiv.ext fun w => Subtype.ext
        ((psi_apply_coe hX _ w).trans (actOn_apply_coe _ _ _ x w).symm)
  rw [hΓeq] at hNΓ hn
  have hN_T₀ := le_imO2_of_normal _ X hXW hNΓ hn hN2
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) X :=
    isSylowOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_sup_left.trans hX.le_normalizer
  have hAW : A ≤ Subgroup.normalizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
    (le_sup_left.trans (MinCex.le_normalizer_Wsub hX).2).trans
      (Item181ThreeProof.normalizer_le_normalizer_omegaG _)
  have hUX : preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW ≤ X :=
    Subgroup.map_subtype_le _
  have hXU : X ≤ Subgroup.normalizer
      (preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW : Set G) :=
    fun x hx => le_normalizer_preO2 _ X hXW (Subgroup.le_normalizer hx) (hXW hx)
  have hAU : A ≤ Subgroup.normalizer
      (preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW : Set G) :=
    fun a ha => le_normalizer_preO2 _ X hXW (hAX ha) (hAW ha)
  have hCU : X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) ≤
      preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW :=
    inf_centralizer_le_preO2 _ X hXW
  have hXC : X ≤ Subgroup.normalizer
      ((X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) : Subgroup G) :
        Set G) :=
    fun x hx => le_normalizer_inf_centralizer _ X hXW (Subgroup.le_normalizer hx) (hXW hx)
  have hUN := hUX.trans hXC
  obtain ⟨n, hn'⟩ := (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux.twoMod_iff
    hCU hUN).mpr (preO2_pow_mem _ X hXW)
  have h1 := Subgroup.relIndex_mul_card
    (X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G))
    (preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW)
  rw [inf_eq_left.mpr hCU, hn'] at h1
  have hCi : (X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)).relIndex
      (preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW) = 2 ^ n := by
    have hpos : 0 < Nat.card ↥(X ⊓ Subgroup.centralizer
        (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) := Nat.card_pos
    have h2 : (X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)).relIndex
        (preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW) *
        Nat.card ↥(X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) =
        2 ^ n * Nat.card ↥(X ⊓ Subgroup.centralizer
          (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) := by
      rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hTS := hS.inf_of_le_normalizer hUX hXU
  have hT := (CFSG.ABGLocalTools.isSylowOf_iff.mp hTS).2.2
  have hUsup := le_sup_of_two_pow_relIndex hCU
    (inf_le_right : CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓
      preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW ≤
        preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW) ⟨n, hCi⟩ hT
  have hUle : preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW ≤
      X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) := by
    rcases hX.sup_eq_or_inf_le hS hUX hXU hAU with hsup | hinf
    · exfalso
      have h : preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW ⊔
          CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
          (X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) ⊔
            CFSG.Open.pCoreOf 2 (H ⊓ M) :=
        sup_le (hUsup.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right))) le_sup_right
      rw [hsup] at h
      have hCN : (X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G)) ⊔
          CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
          Subgroup.normalizer (Sec3.omegaG (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
        sup_le (le_normalizer_of_le_centralizer (omegaG_le_W1' h186 hX) inf_le_right)
          (le_normalizer_of_le_centralizer (omegaG_le_centerOf' _) (le_centralizer_centerOf' _))
      apply hbad2
      rw [tripleOf_two_eq_omegaG']
      exact h.trans hCN
    · have hST : CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓
          preO2 (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M))) X hXW ≤
          X ⊓ Subgroup.centralizer (W1 X (CFSG.Open.pCoreOf 2 (H ⊓ M)) : Set G) :=
        ((inf_comm _ _).le.trans hinf).trans
          (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X) (pCoreOf_le_centralizer_W1 h186 hX))
      exact hUsup.trans (sup_le le_rfl hST)
  exact eq_bot_iff.mpr (hN_T₀.trans (imO2_le_bot _ X hXW hUle))

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
