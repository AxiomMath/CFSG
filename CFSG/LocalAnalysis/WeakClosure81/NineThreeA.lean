module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSetup
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nineThree_sq_mul {y₁ y₂ : G} (hc : y₁ * y₂ = y₂ * y₁) (h1 : y₁ ^ 2 = 1)
    (h2 : y₂ ^ 2 = 1) : (y₁ * y₂) ^ 2 = 1 := by
  calc (y₁ * y₂) ^ 2 = y₁ ^ 2 * y₂ ^ 2 := Commute.mul_pow hc 2
    _ = 1 := by rw [h1, h2, one_mul]

private theorem nineThree_conjSubgroup_iSup {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

private theorem nineThree_conjSubgroup_eq_self {N : Subgroup G} {y : G}
    (hy : y ∈ normalizer (N : Set G)) : conjSubgroup N y = N := by
  ext z
  rw [mem_conjSubgroup_iff]
  exact (Subgroup.mem_normalizer_iff.mp hy z).symm

namespace Nine3Core

theorem S_le_K (h : Nine3Core V T A K S X p) : S ≤ K :=
  h.hyp.base.sylowTwo.le

theorem pCoreOf_le_S (h : Nine3Core V T A K S X p) : pCoreOf 2 K ≤ S :=
  h.hyp.base.toTwoPTwo.pCoreOf_le_sylowTwo

theorem V_le_pCoreOf (h : Nine3Core V T A K S X p) : V ≤ pCoreOf 2 K :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.V_le_S.trans h.S_le_K)
    h.hyp.base.le (B2F.isPGroup_of_isElemAbelian h.hyp7.1)

theorem commutator_V (h : Nine3Core V T A K S X p) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) : ⁅U, V⁆ = ⊥ :=
  commutator_eq_bot_of_mem_omegaSet h.hyp7 h.rk_gt hU.1
    ⟨1, (CFSG.Quasithin.conjSubgroup_one V).symm⟩ h.V_le_pCoreOf

theorem nineH_le_centralizer (h : Nine3Core V T A K S X p) :
    nineH V K ≤ centralizer (V : Set G) :=
  iSup₂_le fun _ hU => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h.commutator_V hU)

theorem nineI_le_centralizer (h : Nine3Core V T A K S X p) :
    nineI V K ≤ centralizer (V : Set G) :=
  iSup₂_le fun _ hU => inf_le_left.trans
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h.commutator_V hU))

theorem conjSubgroup_mem_nineOmegaIn (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) {r : G} (hr : r ∈ pCoreOf 2 K) :
    conjSubgroup B r ∈ nineOmegaIn V K S := by
  have hrK : r ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hr
  have hEK : nineE V K ≤ K := (nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  refine ⟨conjSubgroup_mem_omegaSet hEK (nineE_subgroupOf_normal V K) hB.1 hrK, ?_⟩
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have hrS : r ∈ S := h.pCoreOf_le_S hr
  have h2 : r⁻¹ * (r * y * r⁻¹) * r ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hrS) (hB.2 hy)) hrS
  simpa [mul_assoc] using h2

theorem mem_nineOmegaIn_iff (h : Nine3Core V T A K S X p) {B : Subgroup G} :
    B ∈ nineOmegaIn V K S ↔ ∃ r ∈ pCoreOf 2 K, B = conjSubgroup A r := by
  constructor
  · intro hB
    exact nine_two_two_R h.hyp7 h.rk_gt h.hyp h.A_mem_nineOmegaIn hB
  · rintro ⟨r, hr, rfl⟩
    exact conjSubgroup_mem_nineOmegaIn h h.A_mem_nineOmegaIn hr

theorem card_nineOmegaIn (h : Nine3Core V T A K S X p) :
    ∃ n : ℕ, Nat.card ↥(nineOmegaIn V K S) = 2 ^ n ∧
      Nat.card ↥(nineDelta V S) = 2 ^ n + 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI act : MulAction ↥(pCoreOf 2 K) (Subgroup G) :=
    { smul := fun r B => conjSubgroup B (r : G)⁻¹
      one_smul := fun B => by
        show conjSubgroup B ((1 : ↥(pCoreOf 2 K)) : G)⁻¹ = B
        simp [CFSG.Quasithin.conjSubgroup_one]
      mul_smul := fun r s B => by
        show conjSubgroup B (((r * s : ↥(pCoreOf 2 K)) : G)⁻¹) =
          conjSubgroup (conjSubgroup B (s : G)⁻¹) (r : G)⁻¹
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
        simp [mul_inv_rev] }
  have horb : nineOmegaIn V K S = MulAction.orbit ↥(pCoreOf 2 K) A := by
    ext B
    rw [MulAction.mem_orbit_iff]
    constructor
    · intro hB
      obtain ⟨r, hr, rfl⟩ := (h.mem_nineOmegaIn_iff).mp hB
      refine ⟨⟨r⁻¹, (pCoreOf 2 K).inv_mem hr⟩, ?_⟩
      show conjSubgroup A ((r⁻¹ : G))⁻¹ = conjSubgroup A r
      simp
    · rintro ⟨r, rfl⟩
      refine (h.mem_nineOmegaIn_iff).mpr ⟨(r : G)⁻¹, (pCoreOf 2 K).inv_mem r.2, rfl⟩
  have hcard : Nat.card ↥(nineOmegaIn V K S) =
      (MulAction.stabilizer ↥(pCoreOf 2 K) A).index := by
    rw [horb, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).index
    (MulAction.stabilizer ↥(pCoreOf 2 K) A)
  refine ⟨n, hcard.trans hn, ?_⟩
  have hΔ : nineDelta V S = insert V (nineOmegaIn V K S) := by
    ext B
    rw [h.mem_nineDelta_iff]
    simp
  rw [hΔ, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h.V_not_mem_nineOmegaIn,
    ← Nat.card_coe_set_eq, hcard.trans hn]

theorem nineW_eq (h : Nine3Core V T A K S X p) : nineW V S = V ⊔ nineZ V K S := by
  apply le_antisymm
  · refine iSup₂_le fun B hB => ?_
    rcases (h.mem_nineDelta_iff).mp hB with rfl | hB'
    · exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le B hB' le_rfl)
  · refine sup_le ?_ (iSup₂_le fun B hB => ?_)
    · exact le_iSup₂_of_le V h.V_mem_nineDelta le_rfl
    · exact le_iSup₂_of_le B ((h.mem_nineDelta_iff).mpr (Or.inr hB)) le_rfl

theorem nineW_mul_comm (h : Nine3Core V T A K S X p) {y z : G} (hy : y ∈ nineW V S)
    (hz : z ∈ nineW V S) : y * z = z * y :=
  congrArg Subtype.val ((nine_three_six h).is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)

theorem nineW_isElemAbelian (h : Nine3Core V T A K S X p) : IsElemAbelian 2 (nineW V S) := by
  have hcomm : IsMulCommutative ↥(nineW V S) := nine_three_six h
  have hmul : ∀ y ∈ nineW V S, ∀ z ∈ nineW V S, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  refine ⟨hcomm, fun w hw => ?_⟩
  have key : w ∈ nineW V S ∧ w ^ 2 = 1 := by
    refine Subgroup.iSup_induction (C := fun w => w ∈ nineW V S ∧ w ^ 2 = 1)
      (fun B : Subgroup G => ⨆ (_ : B ∈ nineDelta V S), B) hw ?_ ⟨Subgroup.one_mem _, one_pow 2⟩ ?_
    · intro B y hy
      refine Subgroup.iSup_induction (C := fun w => w ∈ nineW V S ∧ w ^ 2 = 1)
        (fun _ : B ∈ nineDelta V S => B) hy ?_ ⟨Subgroup.one_mem _, one_pow 2⟩ ?_
      · intro hB z hz
        have hle : B ≤ nineW V S := le_iSup₂_of_le B hB le_rfl
        refine ⟨hle hz, ?_⟩
        obtain ⟨g, rfl⟩ : IsGConj V B := hB.1
        exact (isElemAbelian_conjSubgroup' h.hyp7.1 g).2 z hz
      · rintro y₁ y₂ ⟨h1, h1'⟩ ⟨h2, h2'⟩
        exact ⟨(nineW V S).mul_mem h1 h2, nineThree_sq_mul (hmul y₁ h1 y₂ h2) h1' h2'⟩
    · rintro y₁ y₂ ⟨h1, h1'⟩ ⟨h2, h2'⟩
      exact ⟨(nineW V S).mul_mem h1 h2, nineThree_sq_mul (hmul y₁ h1 y₂ h2) h1' h2'⟩
  exact key.2

theorem nineZ_eq_iSup (h : Nine3Core V T A K S X p) :
    nineZ V K S = ⨆ r ∈ pCoreOf 2 K, conjSubgroup A r := by
  apply le_antisymm
  · refine iSup₂_le fun B hB => ?_
    obtain ⟨r, hr, rfl⟩ := (h.mem_nineOmegaIn_iff).mp hB
    exact le_iSup₂_of_le r hr le_rfl
  · refine iSup₂_le fun r hr => ?_
    exact le_iSup₂_of_le (conjSubgroup A r) ((h.mem_nineOmegaIn_iff).mpr ⟨r, hr, rfl⟩) le_rfl

theorem conjSubgroup_pCoreOf (K : Subgroup G) {y : G} (hy : y ∈ K) :
    conjSubgroup (pCoreOf 2 K) y = pCoreOf 2 K :=
  nineThree_conjSubgroup_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hy)

theorem mem_pCoreOf_conj_iff (K : Subgroup G) {y : G} (hy : y ∈ K) {r : G} :
    r ∈ pCoreOf 2 K ↔ y * r * y⁻¹ ∈ pCoreOf 2 K := by
  rw [← mem_conjSubgroup_iff, conjSubgroup_pCoreOf K hy]

theorem nineDp_eq (h : Nine3Core V T A K S X p) (hx : x ∈ X) :
    nineDp K A x = nineZ V K S ⊓ pCoreOf 2 K := by
  have hxK : x ∈ K := h.hyp.base.toTwoPTwo.sylowP.le hx
  have hR : ∀ y ∈ K, ∀ r, r ∈ pCoreOf 2 K ↔ y * r * y⁻¹ ∈ pCoreOf 2 K := fun y hy r => by
    rw [← mem_conjSubgroup_iff, conjSubgroup_pCoreOf K hy]
  unfold nineDp nineD
  rw [E3.conjSubgroup_inf, nineThree_conjSubgroup_iSup, conjSubgroup_pCoreOf K (K.inv_mem hxK),
    h.nineZ_eq_iSup]
  congr 1
  simp only [nineThree_conjSubgroup_iSup, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun hr => ?_
    exact le_iSup₂_of_le (x * r * x⁻¹) ((hR x hxK r).mp hr) le_rfl
  · refine iSup₂_le fun r hr => ?_
    refine le_iSup_of_le (x⁻¹ * r * x) (le_iSup_of_le ?_ ?_)
    · have := (hR x⁻¹ (K.inv_mem hxK) r).mp hr
      simpa using this
    · simp [mul_assoc]

theorem nineD_eq (h : Nine3Core V T A K S X p) (hx : x ∈ X) :
    nineD K A x = conjSubgroup (nineZ V K S) x ⊓ pCoreOf 2 K := by
  have hxK : x ∈ K := h.hyp.base.toTwoPTwo.sylowP.le hx
  have h1 : nineD K A x = conjSubgroup (nineDp K A x) x := by
    unfold nineDp
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel, CFSG.Quasithin.conjSubgroup_one]
  rw [h1, h.nineDp_eq hx, E3.conjSubgroup_inf, conjSubgroup_pCoreOf K hxK]

theorem nineD_le_pCoreOf : nineD K A x ≤ pCoreOf 2 K :=
  inf_le_right

theorem nineD_isElemAbelian (h : Nine3Core V T A K S X p) (hx : x ∈ X) :
    IsElemAbelian 2 (nineD K A x) := by
  have hZ : nineZ V K S ≤ nineW V S := by
    rw [h.nineW_eq]
    exact le_sup_right
  rw [h.nineD_eq hx]
  exact CFSG.Open.IsElemAbelian.mono (E3.isElemAbelian_conjSubgroup
    (CFSG.Open.IsElemAbelian.mono h.nineW_isElemAbelian hZ) x) inf_le_left

theorem nineD_le_centralizer (h : Nine3Core V T A K S X p) (hx : x ∈ X) :
    nineD K A x ≤ centralizer (V : Set G) := by
  have hxK : x ∈ K := h.hyp.base.toTwoPTwo.sylowP.le hx
  have hEK : nineE V K ≤ K := (nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  rw [h.nineD_eq hx]
  refine inf_le_left.trans ?_
  unfold nineZ
  rw [nineThree_conjSubgroup_iSup]
  refine iSup_le fun B => ?_
  rw [nineThree_conjSubgroup_iSup]
  refine iSup_le fun hB => ?_
  have hBK : conjSubgroup B x ≤ K := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem hxK) (h.S_le_K (hB.2 hy))) hxK
    simpa [mul_assoc] using h2
  have hU : conjSubgroup B x ∈ omegaIn V K (nineE V K) :=
    ⟨conjSubgroup_mem_omegaSet hEK (nineE_subgroupOf_normal V K) hB.1 hxK, hBK⟩
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h.commutator_V hU)

end Nine3Core

end CFSG.LocalAnalysis.WeakClosure81
