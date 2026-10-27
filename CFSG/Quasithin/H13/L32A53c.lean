module

public import CFSG.Quasithin.H13.L32A53b
public import CFSG.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem perm3_sq (s : Equiv.Perm (Fin 3)) :
    s * s = 1 ∨ s * s = finRotate 3 ∨ s * s = finRotate 3 * finRotate 3 := by
  revert s
  decide

theorem perm3_gen (s : Equiv.Perm (Fin 3)) (hs : s ≠ 1) :
    ∃ g h : Equiv.Perm (Fin 3), finRotate 3 = (g * s * g⁻¹) * (h * s * h⁻¹) ∨
      finRotate 3 = g * s * g⁻¹ := by
  revert s
  decide

omit [Finite G] in
theorem oTwoUpper_sup_le_of_two {K P : Subgroup G} (hP : IsPGroup 2 P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) : oTwoUpper (K ⊔ P) ≤ K := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  obtain ⟨a, ha, p, hp, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hPK).1 hx
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq ha (hPK hp) (2 ^ k)
  exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩

theorem le_pCoreOf_of_normal_of_S3 {P K : Subgroup G}
    (hP : quasithinO2QuotientIso P (Equiv.Perm (Fin 3))) (hKP : K ≤ P)
    (hKn : P ≤ Subgroup.normalizer (K : Set G)) (hno : ¬ oTwoUpper P ≤ K) : K ≤ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := hP
  have hker : ∀ x : ↥P, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 P := by
    intro x
    rw [← MonoidHom.mem_ker, hφk]
    exact C2Six.mem_pCore_two_iff
  by_contra hK
  obtain ⟨k, hk, hkO⟩ := IsConcreteLE.not_le_iff_exists.mp hK
  set N : Subgroup (Equiv.Perm (Fin 3)) := (K.subgroupOf P).map φ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨x, rfl⟩ := hφs g
    refine ⟨x * y * x⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hKn x.2) y).mp hy
  have hk1 : φ ⟨k, hKP hk⟩ ≠ 1 := fun h => hkO ((hker _).mp h)
  have hkN : φ ⟨k, hKP hk⟩ ∈ N := ⟨⟨k, hKP hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hcN : finRotate 3 ∈ N := by
    obtain ⟨g, h, hgh | hgh⟩ := perm3_gen _ hk1
    · rw [hgh]
      exact mul_mem (hNn.conj_mem _ hkN g) (hNn.conj_mem _ hkN h)
    · rw [hgh]
      exact hNn.conj_mem _ hkN g
  have hsq : ∀ s : Equiv.Perm (Fin 3), s * s ∈ N := fun s => by
    rcases perm3_sq s with h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hcN
    · rw [h]; exact mul_mem hcN hcN
  have hO2 : IsPGroup 2 (pCoreOf 2 P) := pCoreOf_isPGroup 2 P
  have hO2K : pCoreOf 2 P ≤ Subgroup.normalizer (K : Set G) :=
    (pCoreOf_le 2 P).trans hKn
  have hle : oTwoUpper P ≤ K ⊔ pCoreOf 2 P := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxP, hxo⟩ := hx
    have hxN : φ ⟨x, hxP⟩ ∈ N := by
      have hodd : Odd (orderOf (φ ⟨x, hxP⟩)) := by
        have := orderOf_map_dvd φ ⟨x, hxP⟩
        rw [Subgroup.orderOf_mk] at this
        exact hxo.of_dvd_nat this
      have hz : φ ⟨x, hxP⟩ ∈ Subgroup.zpowers (φ ⟨x, hxP⟩ ^ 2) :=
        A4.mem_zpowers_pow_of_coprime (Nat.coprime_two_left.mpr hodd)
      refine (Subgroup.zpowers_le.mpr ?_) hz
      rw [pow_two]
      exact hsq _
    obtain ⟨y, hy, hyx⟩ := hxN
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    have h1 : φ (y⁻¹ * ⟨x, hxP⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have h2 := (hker _).mp h1
    have e : x = (y : G) * ((y⁻¹ * ⟨x, hxP⟩ : ↥P) : G) := by simp
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right h2)
  apply hno
  calc oTwoUpper P = oTwoUpper (oTwoUpper P) := (oTwoUpper_oTwoUpper P).symm
    _ ≤ oTwoUpper (K ⊔ pCoreOf 2 P) := oTwoUpper_mono hle
    _ ≤ K := oTwoUpper_sup_le_of_two hO2 hO2K

namespace T53

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

theorem charTwo_hY (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) : CharTwo (hY T L V₂ Y) := by
  have hT := C.hyp.fsu.sylow
  refine charTwo_of_inH C.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2) ⟨?_, hQ⟩
  rw [IsPGroup.toSylow_coe]
  exact le_sup_right

omit C [Finite G] in
theorem V1_le_Z : fsuV1 T V ≤ quasithinOmegaOneCenter T := inf_le_right

theorem vH_le_center (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) :
    vH T L V V₂ Y ≤ centerOf (pCoreOf 2 (hY T L V₂ Y)) ∧ IsElemAbelian 2 (vH T L V V₂ Y) := by
  have hS := C.isSylowTwoOf_T (K := hY T L V₂ Y) le_sup_right
  exact conjClosure_le_centerOf_pCoreOf_of_sylowIn hS.1 hS.2.1 hS.2.2 (C.charTwo_hY hQ) V1_le_Z

theorem isTwoReducedIn_vH (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) :
    IsTwoReducedIn (hY T L V₂ Y) (vH T L V V₂ Y) := by
  have hS := C.isSylowTwoOf_T (K := hY T L V₂ Y) le_sup_right
  exact isTwoReducedIn_conjClosure_of_sylowIn hS.1 hS.2.1 hS.2.2 (C.charTwo_hY hQ) V1_le_Z

omit C [Finite G] in
theorem le_normalizer_centralizer_vH {K : Subgroup G} (hK : K ≤ hY T L V₂ Y) :
    K ≤ Subgroup.normalizer (Subgroup.centralizer (vH T L V V₂ Y : Set G) : Set G) :=
  (hK.trans (le_normalizer_conjClosure _ _)).trans (normalizer_le_normalizer_centralizer _)

theorem xL_not_le_centralizer : ¬ xL L V₂ ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  intro h
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have S := C.set14
  have hle : conjClosure (fsuV1 T V) (xL L V₂) ≤ fsuV1 T V := conjClosure_le fun x hx z hz => by
    have hz' : z ∈ vH T L V V₂ Y := le_conjClosure _ _ hz
    rw [← Subgroup.mem_centralizer_iff.mp (h hx) z hz', mul_inv_cancel_right]
    exact hz
  rw [C.conjClosure_V1_X] at hle
  have h1 := Subgroup.card_le_of_le hle
  rw [C.hV2.2.2.2, S.card_V1] at h1
  omega

theorem inf_xT_le (h4 : Lemma14_7_4_two_three) :
    (xL L V₂ ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
  have hXH : xL L V₂ ⊔ T ≤ hY T L V₂ Y :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  refine le_pCoreOf_of_normal_of_S3 (C.quot_xT h4).1 inf_le_left ?_ ?_
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_centralizer_vH hXH hx⟩
  · rw [C.oTwoUpper_xT]
    intro h
    exact C.xL_not_le_centralizer (h.trans inf_le_right)

theorem inf_yT_le :
    (Y ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) ≤ pCoreOf 2 (Y ⊔ T) := by
  have hYH : Y ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  refine le_pCoreOf_of_normal_of_S3 C.hS3 inf_le_left ?_ ?_
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_centralizer_vH hYH hx⟩
  · rw [C.oTwoUpper_yT]
    intro h
    have hYC : Y ≤ cH T L V V₂ Y :=
      le_inf (le_sup_right.trans le_sup_left) (h.trans inf_le_right)
    apply C.not_le_normalizer
    intro y hy
    have hyC := hYC hy
    rw [Subgroup.mem_normalizer_iff]
    have hCn : hY T L V₂ Y ≤ Subgroup.normalizer (cH T L V V₂ Y : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        le_normalizer_centralizer_vH le_rfl hg⟩
    have hXC := xL_le_normalizer_cH (T := T) (L := L) (V := V) (V₂ := V₂) (Y := Y)
    have hset : ((xL L V₂ ⊔ cH T L V V₂ Y : Subgroup G) : Set G) =
        (xL L V₂ : Set G) * (cH T L V V₂ Y : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXC
    have hyH : y ∈ hY T L V₂ Y := hyC.1
    intro w
    constructor
    · intro hw
      rw [← SetLike.mem_coe, hset] at hw ⊢
      obtain ⟨x, hx, c, hc, rfl⟩ := hw
      refine ⟨x, hx, (x⁻¹ * y * x) * c * y⁻¹, ?_, by group⟩
      have h1 : x⁻¹ * y * x ∈ cH T L V V₂ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (hXC (inv_mem hx)) y).mp hyC
        simpa [mul_assoc] using this
      exact mul_mem (mul_mem h1 hc) (inv_mem hyC)
    · intro hw
      rw [← SetLike.mem_coe, hset] at hw ⊢
      obtain ⟨x, hx, c, hc, hxc⟩ := hw
      have hxc' : x * c = y * w * y⁻¹ := hxc
      refine ⟨x, hx, x⁻¹ * y⁻¹ * x * c * y, ?_, ?_⟩
      · have h1 : x⁻¹ * y⁻¹ * x ∈ cH T L V V₂ Y := by
          have := (Subgroup.mem_normalizer_iff.mp (hXC (inv_mem hx)) y⁻¹).mp (inv_mem hyC)
          simpa [mul_assoc] using this
        exact mul_mem (mul_mem h1 hc) hyC
      · show x * (x⁻¹ * y⁻¹ * x * c * y) = w
        calc x * (x⁻¹ * y⁻¹ * x * c * y) = y⁻¹ * (x * c) * y := by group
          _ = w := by rw [hxc']; group

theorem pCoreOf_hY_eq (h4 : Lemma14_7_4_two_three) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) :
    pCoreOf 2 (hY T L V₂ Y) = T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ hY T L V₂ Y := le_sup_right
  apply le_antisymm
  · refine le_inf (pCoreOf_le_of_le C.hyp hTH) fun q hq => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (((C.vH_le_center hQ).1 hv).2 q hq).symm
  · set R := T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G)
    have hXT : (xL L V₂ ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) = R := by
      refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ le_sup_right)
      exact (C.inf_xT_le h4).trans (pCoreOf_le_of_le C.hyp le_sup_right)
    have hYT : (Y ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) = R := by
      refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ le_sup_right)
      exact C.inf_yT_le.trans (pCoreOf_le_of_le C.hyp le_sup_right)
    have hXN : xL L V₂ ⊔ T ≤ Subgroup.normalizer (R : Set G) := by
      rw [← hXT]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
        le_normalizer_centralizer_vH (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hx⟩
    have hYN : Y ⊔ T ≤ Subgroup.normalizer (R : Set G) := by
      rw [← hYT]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
        le_normalizer_centralizer_vH (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hx⟩
    have hHN : hY T L V₂ Y ≤ Subgroup.normalizer (R : Set G) := by
      exact sup_le (sup_le (le_sup_left.trans hXN) (le_sup_left.trans hYN))
        (le_sup_right.trans hXN)
    exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTH) hHN
      (C.hyp.fsu.sylow.1.to_le inf_le_left)

end Ctx

@[expose] def Contra14_5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ Y : Subgroup G), Ctx G T L V V₂ Y → False

theorem thm14_5_3_of (h : Contra14_5_3) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : Thm14_5_3 := by
  intro G _ _ T L V hyp Y V₂ hV2 hYo hYG1 hTY hS3
  by_contra hc
  exact h G T L V V₂ Y ⟨hyp, h1222, h1332, h1334, hV2, hYo, hYG1, hTY, hS3, hc⟩

end T53

end CFSG.Quasithin.H13.L32A
