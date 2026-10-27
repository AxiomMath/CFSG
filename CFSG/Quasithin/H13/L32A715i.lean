module

public import CFSG.Quasithin.EmptyFaithful.S146zHCls
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32A714b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open scoped commutatorElement

section Rho

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

@[expose] noncomputable def rhoDot (h : HypF91 T V L V₁ Vp H) :
    (↥H ⧸ CFSG.pCore 2 ↥H) →* MulAut (UMod h) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥H) (rhoH h) (fun g hg => by
    rw [MonoidHom.mem_ker, rhoH_eq_one_iff h g, pCoreOf]
    exact ⟨g, hg, rfl⟩)

theorem rhoDot_mk (h : HypF91 T V L V₁ Vp H) (g : ↥H) :
    rhoDot h (QuotientGroup.mk g) = rhoH h g := rfl

theorem rhoDot_injective (h : HypF91 T V L V₁ Vp H) : Function.Injective (rhoDot h) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective n
  rw [rhoDot_mk, rhoH_eq_one_iff, pCoreOf] at hn
  obtain ⟨g', hg', hg'g⟩ := hn
  have : g' = g := Subtype.ext hg'g
  subst this
  exact (QuotientGroup.eq_one_iff _).mpr hg'

theorem umod_sq (h : HypF91 T V L V₁ Vp H) (w : UMod h) : w * w = 1 := by
  rw [← sq]
  exact IntMod.sq_eq_one w

theorem fpf_of_commutator (h : HypF91 T V L V₁ Vp H) {Y : Subgroup G} (hYH : Y ≤ H)
    {c : ↥H ⧸ CFSG.pCore 2 ↥H} (hc3 : c ^ 3 = 1)
    (hY : ∀ y (hy : y ∈ Y), ∃ n : ℕ, QuotientGroup.mk (⟨y, hYH hy⟩ : ↥H) = c ^ n)
    (hU : ⁅conjClosure Vp H, Y⁆ ⊔ V₁ = conjClosure Vp H) :
    ∀ w : UMod h, rhoDot h c w = w → w = 1 := by
  set φ := rhoDot h c with hφ
  have hφ3 : φ ^ 3 = 1 := by rw [hφ, ← map_pow, hc3, map_one]
  have hcube : ∀ w, φ (φ (φ w)) = w := S153Q.Q4A.z_cube_apply hφ3
  let N : UMod h →* UMod h :=
    { toFun := fun w => w * φ w * φ (φ w)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul]
        ac_rfl }
  have hN : ∀ w, N w = w * φ w * φ (φ w) := fun _ => rfl
  have hNφ : ∀ w, N (φ w) = N w := by
    intro w
    rw [hN, hN, hcube]
    ac_rfl
  have hNφn : ∀ (n : ℕ) w, N ((φ ^ n) w) = N w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ']
      change N (φ ((φ ^ n) w)) = N w
      rw [hNφ, ih]
  let K : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ conjClosure Vp H, N (clsU h hg) = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨(conjClosure Vp H).mul_mem ha hb, ?_⟩
        rw [← clsU_mul h ha hb, map_mul, ha1, hb1, one_mul]
      one_mem' := ⟨(conjClosure Vp H).one_mem, by rw [clsU_one, map_one]⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        refine ⟨(conjClosure Vp H).inv_mem ha, ?_⟩
        rw [← clsU_inv h ha, map_inv, ha1, inv_one] }
  have hcomm : ⁅conjClosure Vp H, Y⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    obtain ⟨n, hn⟩ := hY y hy
    have hyH : y ∈ H := hYH hy
    have h1 : y * u⁻¹ * y⁻¹ ∈ conjClosure Vp H :=
      conj_mem_UH hyH ((conjClosure Vp H).inv_mem hu)
    have hmem : ⁅u, y⁆ ∈ conjClosure Vp H := by
      have e : ⁅u, y⁆ = u * (y * u⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact (conjClosure Vp H).mul_mem hu h1
    refine ⟨hmem, ?_⟩
    have e1 : clsU h hmem = clsU h hu * clsU h h1 := by
      rw [clsU_mul]
      exact clsU_congr h _ _ (by rw [commutatorElement_def]; group)
    have e2 : clsU h h1 = (φ ^ n) (clsU h hu)⁻¹ := by
      calc clsU h h1 = rhoH h ⟨y, hyH⟩ (clsU h ((conjClosure Vp H).inv_mem hu)) :=
            (rhoH_clsU h ⟨y, hyH⟩ _).symm
        _ = rhoDot h (QuotientGroup.mk ⟨y, hyH⟩) (clsU h hu)⁻¹ := by
            rw [rhoDot_mk, clsU_inv]
        _ = (φ ^ n) (clsU h hu)⁻¹ := by rw [hn, map_pow]
    rw [e1, e2, map_mul, hNφn, map_inv, mul_inv_cancel]
  have hV1 : V₁ ≤ K := by
    intro v hv
    have hvU : v ∈ conjClosure Vp H := le_conjClosure Vp H (h.V₁_lt_Vp.le hv)
    exact ⟨hvU, by rw [(clsU_eq_one_iff h hvU).mpr hv, map_one]⟩
  have hUK : conjClosure Vp H ≤ K := hU ▸ sup_le hcomm hV1
  intro w hw
  obtain ⟨u, hu, rfl⟩ := exists_clsU h w
  obtain ⟨hu', hN1⟩ := hUK hu
  have hN1' : N (clsU h hu) = 1 := hN1
  rw [hN, hw, hw, umod_sq, one_mul] at hN1'
  exact hN1'

theorem card_commV_le (h : HypF91 T V L V₁ Vp H) (s : ↥H) (hs2 : rhoH h s * rhoH h s = 1) :
    Nat.card (commV (Subgroup.zpowers (rhoH h s))) ≤
      ((Subgroup.centralizer ({(s : G)} : Set G)).subgroupOf (conjClosure Vp H)).index := by
  set t := rhoH h s with ht
  have hW2 := umod_sq h
  rw [HeisMod.commV_zpowers_eq_range hW2 hs2, ← Subgroup.index_ker,
    ← HeisMod.fixV_zpowers_eq_ker hW2]
  let π : ↥(conjClosure Vp H) →* UMod h :=
    { toFun := fun u => clsU h u.2
      map_one' := clsU_one h
      map_mul' := fun u u' => (clsU_mul h u.2 u'.2).symm }
  have hπ : Function.Surjective π := fun w => by
    obtain ⟨u, hu, rfl⟩ := exists_clsU h w
    exact ⟨⟨u, hu⟩, rfl⟩
  set C := (Subgroup.centralizer ({(s : G)} : Set G)).subgroupOf (conjClosure Vp H) with hC
  have hle : C.map π ≤ fixV (Subgroup.zpowers t) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [HeisMod.mem_fixV_zpowers]
    have hsu : (s : G) * u = u * s :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hu)).symm
    change t (clsU h u.2) = clsU h u.2
    rw [ht, rhoH_clsU]
    exact clsU_congr h _ _ (by rw [hsu, mul_inv_cancel_right])
  calc (fixV (Subgroup.zpowers t)).index ≤ (C.map π).index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hle)
    _ ≤ C.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_map_dvd C hπ)

end Rho

section Index

variable {G : Type} [Group G] [Finite G]

theorem relIndex_centralizer_le {U A Z : Subgroup G} (hD : (centralizerMod Z U A).relIndex U = 2)
    (hZ : Nat.card Z = 2) {s : G} (hs : s ∈ A) :
    ((Subgroup.centralizer ({s} : Set G)).subgroupOf U).index ≤ 4 := by
  set D := centralizerMod Z U A with hDdef
  have hDU : D ≤ U := centralizerMod_le_left _ _ _
  have hZc : Subgroup.normalizer (Z : Set G) = Subgroup.centralizer (Z : Set G) :=
    normalizer_eq_centralizer_of_card_eq_two hZ
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    have hab : a ∈ Subgroup.centralizer (Z : Set G) := by
      rw [← hZc]
      exact Subgroup.le_normalizer ha
    exact (Subgroup.mem_centralizer_iff.mp hab b hb).symm
  have hmemZ : ∀ d ∈ D, d * s * d⁻¹ * s⁻¹ ∈ Z := fun d hd => hd.2.2 s hs
  let f : ↥D →* ↥Z :=
    { toFun := fun d => ⟨(d : G) * s * (d : G)⁻¹ * s⁻¹, hmemZ d d.2⟩
      map_one' := by ext; simp
      map_mul' := fun d e => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hdN : (d : G) ∈ Subgroup.centralizer (Z : Set G) := by
          rw [← hZc]
          exact d.2.2.1
        have h1 : (d : G) * ((e : G) * s * (e : G)⁻¹ * s⁻¹) * (d : G)⁻¹ =
            (e : G) * s * (e : G)⁻¹ * s⁻¹ := by
          rw [(Subgroup.mem_centralizer_iff.mp hdN _ (hmemZ e e.2)).symm, mul_inv_cancel_right]
        calc (d : G) * e * s * ((d : G) * e)⁻¹ * s⁻¹ =
            ((d : G) * ((e : G) * s * (e : G)⁻¹ * s⁻¹) * (d : G)⁻¹) *
              ((d : G) * s * (d : G)⁻¹ * s⁻¹) := by group
          _ = ((e : G) * s * (e : G)⁻¹ * s⁻¹) * ((d : G) * s * (d : G)⁻¹ * s⁻¹) := by rw [h1]
          _ = ((d : G) * s * (d : G)⁻¹ * s⁻¹) * ((e : G) * s * (e : G)⁻¹ * s⁻¹) :=
            hZcomm _ (hmemZ e e.2) _ (hmemZ d d.2) }
  have hker : (Subgroup.centralizer ({s} : Set G)).subgroupOf D = f.ker := by
    ext d
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_ker]
    constructor
    · intro hd
      apply Subtype.ext
      change (d : G) * s * (d : G)⁻¹ * s⁻¹ = 1
      rw [hd, mul_inv_cancel_right, mul_inv_cancel]
    · intro hd
      have h1 : (d : G) * s * (d : G)⁻¹ * s⁻¹ = 1 := congrArg Subtype.val hd
      calc (d : G) * s = ((d : G) * s * (d : G)⁻¹ * s⁻¹) * (s * d) := by group
        _ = s * d := by rw [h1, one_mul]
  have h2 : (Subgroup.centralizer ({s} : Set G)).relIndex D ≤ 2 := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker, ← hZ]
    exact Subgroup.card_le_card_group f.range
  have h3 := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer ({s} : Set G)) D U
  rw [inf_eq_left.mpr hDU, hD] at h3
  have h4 := Subgroup.relIndex_dvd_of_le_left U
    (inf_le_left : Subgroup.centralizer ({s} : Set G) ⊓ D ≤ Subgroup.centralizer ({s} : Set G))
  have hne : (Subgroup.centralizer ({s} : Set G) ⊓ D).relIndex U ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  change (Subgroup.centralizer ({s} : Set G)).relIndex U ≤ 4
  calc (Subgroup.centralizer ({s} : Set G)).relIndex U ≤
        (Subgroup.centralizer ({s} : Set G) ⊓ D).relIndex U :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h4
    _ = (Subgroup.centralizer ({s} : Set G)).relIndex D * 2 := h3.symm
    _ ≤ 4 := by omega

end Index

end CFSG.Quasithin.H13.L32A
