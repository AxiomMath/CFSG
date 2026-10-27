module

public import CFSG.Quasithin.EmptyFaithful.S152He8Wr
public import CFSG.Quasithin.Background.C1PackS15212B
public import CFSG.Quasithin.EmptyFaithful.S152He8Rep

public section

namespace CFSG.Quasithin.He8

open CFSG.Open CFSG.QuasithinUnique Matrix
open CFSG.Quasithin.C1Pack12

section

variable {G : Type} [Group G] [Finite G]

theorem pCore_characteristic' (A : Type) [Group A] : (CFSG.Open.pCore 2 A).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e

variable {K Mc : Subgroup G}

@[expose] noncomputable def kAct (hKn : Mc ≤ Subgroup.normalizer (K : Set G)) :
    ↥Mc →* MulAut (OTwoQuot K) :=
  haveI := pCore_characteristic' ↥K
  (quotAut (CFSG.Open.pCore 2 ↥K)).comp (Quasithin.A4.actionOn K Mc hKn)

omit [Finite G] in
theorem kAct_mk (hKn : Mc ≤ Subgroup.normalizer (K : Set G)) (g : ↥Mc) (y : ↥K) :
    kAct hKn g (QuotientGroup.mk y : OTwoQuot K) =
      (QuotientGroup.mk (Quasithin.A4.actionOn K Mc hKn g y) : OTwoQuot K) := rfl

variable {H : Subgroup G} (φ : OTwoQuot H ≃* S152N.W3)

@[expose] noncomputable def kappa : ↥(oTwoUpper H) →* S152N.W3 :=
  (φ : OTwoQuot H →* S152N.W3).comp
    ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)).comp (Subgroup.inclusion (oTwoUpper_le H)))

omit [Finite G] in
theorem kappa_apply (y : ↥(oTwoUpper H)) :
    kappa φ y = φ (QuotientGroup.mk ⟨(y : G), oTwoUpper_le H y.2⟩ : OTwoQuot H) := rfl

theorem kappa_eq_one_iff (y : ↥(oTwoUpper H)) :
    kappa φ y = 1 ↔ (y : G) ∈ pCoreOf 2 (oTwoUpper H) := by
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  rw [hpK, kappa_apply, φ.map_eq_one_iff]
  constructor
  · intro h
    exact ⟨y.2, (mk_eq_one_iff_mem_pCoreOf (⟨(y : G), oTwoUpper_le H y.2⟩ : ↥H)).mp h⟩
  · intro h
    exact (mk_eq_one_iff_mem_pCoreOf (⟨(y : G), oTwoUpper_le H y.2⟩ : ↥H)).mpr h.2

theorem kappa_mem_N0 (y : ↥(oTwoUpper H)) : kappa φ y ∈ S152N.W3.N0 := by
  rw [kappa_apply]
  have hmem : (QuotientGroup.mk ⟨(y : G), oTwoUpper_le H y.2⟩ : OTwoQuot H) ∈
      imageOTwoQuot H (oTwoUpper H) :=
    mem_imageOTwoQuot_iff.mpr ⟨y, oTwoUpper_le H y.2, y.2, rfl⟩
  rw [← map_imageOTwoQuot_oTwoUpper φ]
  exact Subgroup.mem_map_of_mem (φ : OTwoQuot H →* S152N.W3) hmem

@[expose] noncomputable def kappaBar : OTwoQuot (oTwoUpper H) →* S152N.W3 :=
  QuotientGroup.lift (CFSG.Open.pCore 2 ↥(oTwoUpper H)) (kappa φ) (fun y hy =>
    (kappa_eq_one_iff φ y).mpr
      ((mk_eq_one_iff_mem_pCoreOf y).mp ((QuotientGroup.eq_one_iff y).mpr hy)))

theorem kappaBar_mk (y : ↥(oTwoUpper H)) :
    kappaBar φ (QuotientGroup.mk y : OTwoQuot (oTwoUpper H)) = kappa φ y := rfl

theorem kappaBar_injective : Function.Injective (kappaBar φ) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [kappaBar_mk] at hq
    exact (mk_eq_one_iff_mem_pCoreOf y).mpr ((kappa_eq_one_iff φ y).mp hq)

theorem kappaBar_mem_N0 (q : OTwoQuot (oTwoUpper H)) : kappaBar φ q ∈ S152N.W3.N0 := by
  induction q using QuotientGroup.induction_on with
  | H y => exact kappa_mem_N0 φ y

theorem kappaBar_surjective_N0 {n : S152N.W3} (hn : n ∈ S152N.W3.N0) :
    ∃ q : OTwoQuot (oTwoUpper H), kappaBar φ q = n := by
  rw [← map_imageOTwoQuot_oTwoUpper φ] at hn
  obtain ⟨u, hu, rfl⟩ := hn
  obtain ⟨x, hxH, hxK, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  exact ⟨QuotientGroup.mk ⟨x, hxK⟩, rfl⟩

theorem exists_coords_K : ∃ fK : Multiplicative (Fin 2 → ZMod 3) ≃* OTwoQuot (oTwoUpper H),
    ∀ v, kappaBar φ (fK v) = WCoord.fW (Multiplicative.toAdd v) := by
  classical
  have hs : ∀ v : Fin 2 → ZMod 3, ∃ q : OTwoQuot (oTwoUpper H), kappaBar φ q = WCoord.fW v :=
    fun v => kappaBar_surjective_N0 φ (WCoord.fW_mem v)
  choose g hg using hs
  let f0 : Multiplicative (Fin 2 → ZMod 3) → OTwoQuot (oTwoUpper H) :=
    fun v => g (Multiplicative.toAdd v)
  have hmul : ∀ a b, f0 (a * b) = f0 a * f0 b := by
    intro a b
    apply kappaBar_injective φ
    rw [map_mul]
    simp only [f0]
    rw [hg, hg, hg]
    exact WCoord.fW_add _ _
  let f1 : Multiplicative (Fin 2 → ZMod 3) →* OTwoQuot (oTwoUpper H) := MonoidHom.mk' f0 hmul
  have hinj : Function.Injective f1 := by
    intro a b hab
    have h1 := congrArg (kappaBar φ) hab
    simp only [f1, MonoidHom.mk'_apply, f0] at h1
    rw [hg, hg] at h1
    exact WCoord.fW_injective _ _ h1
  have hsurj : Function.Surjective f1 := by
    intro q
    obtain ⟨v, hv⟩ := WCoord.fW_surjective _ (kappaBar_mem_N0 φ q)
    refine ⟨Multiplicative.ofAdd v, kappaBar_injective φ ?_⟩
    simp only [f1, MonoidHom.mk'_apply, f0]
    rw [toAdd_ofAdd, hg, hv]
  exact ⟨MulEquiv.ofBijective f1 ⟨hinj, hsurj⟩, fun v => hg _⟩

theorem kappaBar_kAct {Mc : Subgroup G} (hKn : Mc ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hHMc : H ≤ Mc) (h : ↥H) (q : OTwoQuot (oTwoUpper H)) :
    kappaBar φ (kAct hKn ⟨h, hHMc h.2⟩ q) =
      φ (QuotientGroup.mk h : OTwoQuot H) * kappaBar φ q * (φ (QuotientGroup.mk h : OTwoQuot H))⁻¹ := by
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [kAct_mk, kappaBar_mk, kappaBar_mk, kappa_apply, kappa_apply, ← map_inv, ← map_mul,
      ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2

@[expose] noncomputable def repK {Mc : Subgroup G} (hKn : Mc ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (fK : Multiplicative (Fin 2 → ZMod 3) ≃* OTwoQuot (oTwoUpper H)) :
    ↥Mc →* GL (Fin 2) (ZMod 3) :=
  (repGL fK).comp (kAct hKn)

theorem repK_eq_of_conj {Mc : Subgroup G} (hKn : Mc ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hHMc : H ≤ Mc) (fK : Multiplicative (Fin 2 → ZMod 3) ≃* OTwoQuot (oTwoUpper H))
    (hfK : ∀ v, kappaBar φ (fK v) = WCoord.fW (Multiplicative.toAdd v)) (h : ↥H)
    (M : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hM : ∀ v : Fin 2 → ZMod 3, φ (QuotientGroup.mk h : OTwoQuot H) * WCoord.fW v *
      (φ (QuotientGroup.mk h : OTwoQuot H))⁻¹ = WCoord.fW (M *ᵥ v)) :
    ((repK hKn fK ⟨h, hHMc h.2⟩ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = M := by
  apply matrix_ext_mulVec
  intro v
  rw [repK, MonoidHom.comp_apply, repGL_mulVec]
  have h1 : fK.symm (kAct hKn ⟨h, hHMc h.2⟩ (fK (Multiplicative.ofAdd v))) =
      Multiplicative.ofAdd (M *ᵥ v) := by
    rw [MulEquiv.symm_apply_eq]
    apply kappaBar_injective φ
    rw [kappaBar_kAct φ hKn hHMc, hfK, hfK, toAdd_ofAdd, toAdd_ofAdd, hM]
  rw [h1, toAdd_ofAdd]

theorem repK_mon_of_mem {Mc : Subgroup G} (hKn : Mc ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hHMc : H ≤ Mc) (fK : Multiplicative (Fin 2 → ZMod 3) ≃* OTwoQuot (oTwoUpper H))
    (hfK : ∀ v, kappaBar φ (fK v) = WCoord.fW (Multiplicative.toAdd v)) (h : ↥H) :
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod 3), IsMon M ∧
      ((repK hKn fK ⟨h, hHMc h.2⟩ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = M := by
  obtain ⟨M, hM, hMv⟩ := WCoord.exists_mon_of_conj (φ (QuotientGroup.mk h : OTwoQuot H))
  exact ⟨M, hM, repK_eq_of_conj φ hKn hHMc fK hfK h M hMv⟩

theorem exists_mem_repK_eq_mon {Mc : Subgroup G} (hKn : Mc ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    (hHMc : H ≤ Mc) (fK : Multiplicative (Fin 2 → ZMod 3) ≃* OTwoQuot (oTwoUpper H))
    (hfK : ∀ v, kappaBar φ (fK v) = WCoord.fW (Multiplicative.toAdd v))
    {M : Matrix (Fin 2) (Fin 2) (ZMod 3)} (hM : IsMon M) :
    ∃ h : ↥H, ((repK hKn fK ⟨h, hHMc h.2⟩ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      M := by
  obtain ⟨w, hw⟩ := WCoord.exists_conj_of_mon M hM
  obtain ⟨q, rfl⟩ := φ.surjective w
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨h, repK_eq_of_conj φ hKn hHMc fK hfK h M hw⟩

end

end CFSG.Quasithin.He8
