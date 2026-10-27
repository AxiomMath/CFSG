module

public import CFSG.Quasithin.MS93.ML3Sec
public import CFSG.Quasithin.MS93.S32Basic
public import CFSG.Quasithin.MS93.S4AVtx

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix commutatorElement

section Dict

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

theorem mem_centralizer_iff_natVec (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1)
    {A : Subgroup G} (hA : A ≤ K) (v : ↥V) :
    (v : G) ∈ Subgroup.centralizer (A : Set G) ↔ natVec h v ∈ fixN (natImage φ A) := by
  rw [Subgroup.mem_centralizer_iff, mem_fixN]
  constructor
  · intro hv g hg
    obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
    exact (commute_iff_natVec h a v).mp (hv _ haA)
  · intro hv a haA
    have := hv _ (mem_natImage.mpr ⟨⟨a, hA haA⟩, haA, rfl⟩)
    exact (commute_iff_natVec h ⟨a, hA haA⟩ v).mpr this

theorem mem_commutator_iff_natVec (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1)
    {A : Subgroup G} (hA : A ≤ K) (v : ↥V) :
    (v : G) ∈ ⁅V, A⁆ ↔ natVec h v ∈ commN (natImage φ A) := by
  have hVA : ⁅V, A⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hA.trans h.1)
  constructor
  · intro hv
    have hp : ∀ y ∈ ⁅V, A⁆, ∃ hy : y ∈ V, natVec h ⟨y, hy⟩ ∈ commN (natImage φ A) := by
      intro y hy
      rw [Subgroup.commutator_def] at hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨v, hv, a, ha, rfl⟩ := hy
        have hmem : ⁅v, a⁆ ∈ V := hVA (Subgroup.commutator_mem_commutator hv ha)
        refine ⟨hmem, ?_⟩
        rw [natVec_commutator h ⟨a, hA ha⟩ ⟨v, hv⟩ ⟨_, hmem⟩ rfl]
        have hg : toSL3 φ ⟨a, hA ha⟩ ∈ natImage φ A := mem_natImage.mpr ⟨_, ha, rfl⟩
        have := sub_mem_commN hg (natVec h ⟨v, hv⟩)
        rw [← neg_sub]
        exact Submodule.neg_mem _ this
      | one =>
        refine ⟨V.one_mem, ?_⟩
        rw [show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, natVec_one]
        exact Submodule.zero_mem _
      | mul a b _ _ iha ihb =>
        obtain ⟨ha, ha'⟩ := iha
        obtain ⟨hb, hb'⟩ := ihb
        refine ⟨V.mul_mem ha hb, ?_⟩
        rw [show (⟨a * b, V.mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, natVec_mul]
        exact Submodule.add_mem _ ha' hb'
      | inv a _ iha =>
        obtain ⟨ha, ha'⟩ := iha
        refine ⟨V.inv_mem ha, ?_⟩
        rw [show (⟨a⁻¹, V.inv_mem ha⟩ : ↥V) = (⟨a, ha⟩ : ↥V)⁻¹ from rfl, natVec_inv]
        exact Submodule.neg_mem _ ha'
    obtain ⟨_, hv'⟩ := hp v hv
    exact hv'
  · intro hv
    have hcl : natVec h v ∈ (commN (natImage φ A)).toAddSubgroup := hv
    rw [commN_eq_closure] at hcl
    have hp : ∀ x ∈ AddSubgroup.closure {y | ∃ g ∈ natImage φ A, ∃ x : Fin 3 → F,
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x = y},
        ∀ w : ↥V, natVec h w = x → (w : G) ∈ ⁅V, A⁆ := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        intro w hw
        obtain ⟨g, hg, x, rfl⟩ := hy
        obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
        obtain ⟨u, rfl⟩ := natVec_surjective h x
        have hmem : ⁅(u : G), (a : G)⁆ ∈ V := hVA (Subgroup.commutator_mem_commutator u.2 haA)
        have hc := natVec_commutator h a u ⟨_, hmem⟩ rfl
        have hw' : w = (⟨_, hmem⟩ : ↥V)⁻¹ := by
          apply natVec_injective h
          rw [hw, natVec_inv, hc, neg_sub]
        rw [hw']
        exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator u.2 haA)
      | zero =>
        intro w hw
        have : w = 1 := natVec_injective h (by rw [hw, natVec_one])
        rw [this]
        exact Subgroup.one_mem _
      | add x y _ _ ihx ihy =>
        intro w hw
        obtain ⟨u, hu⟩ := natVec_surjective h x
        obtain ⟨u', hu'⟩ := natVec_surjective h y
        have : w = u * u' := natVec_injective h (by rw [hw, natVec_mul, hu, hu'])
        rw [this]
        exact Subgroup.mul_mem _ (ihx u hu) (ihy u' hu')
      | neg x _ ihx =>
        intro w hw
        obtain ⟨u, hu⟩ := natVec_surjective h x
        have : w = u⁻¹ := natVec_injective h (by rw [hw, natVec_inv, hu])
        rw [this]
        exact Subgroup.inv_mem _ (ihx u hu)
    exact hp _ hcl v rfl

@[expose] noncomputable def natVecG (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (x : G) :
    Fin 3 → F := by
  classical
  exact if hx : x ∈ V then natVec h ⟨x, hx⟩ else 0

theorem natVecG_of_mem (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {x : G} (hx : x ∈ V) :
    natVecG h x = natVec h ⟨x, hx⟩ := by
  simp [natVecG, hx]

theorem natVecG_mul (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {x y : G} (hx : x ∈ V)
    (hy : y ∈ V) : natVecG h (x * y) = natVecG h x + natVecG h y := by
  rw [natVecG_of_mem h hx, natVecG_of_mem h hy, natVecG_of_mem h (V.mul_mem hx hy), ← natVec_mul]
  rfl

theorem natVecG_one (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) : natVecG h (1 : G) = 0 := by
  rw [natVecG_of_mem h V.one_mem, show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, natVec_one]

theorem natVecG_conj (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) (a : ↥K) {x : G}
    (hx : x ∈ V) :
    natVecG h ((a : G) * x * (a : G)⁻¹) =
      ((toSL3 φ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVecG h x := by
  have hmem : (a : G) * x * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (h.1 a.2) x).mp hx
  rw [natVecG_of_mem h hx, natVecG_of_mem h hmem]
  exact natVec_conj h a ⟨x, hx⟩ ⟨_, hmem⟩ rfl

theorem natVecG_injective (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {x y : G}
    (hx : x ∈ V) (hy : y ∈ V) (hxy : natVecG h x = natVecG h y) : x = y := by
  rw [natVecG_of_mem h hx, natVecG_of_mem h hy] at hxy
  exact congrArg Subtype.val (natVec_injective h hxy)

end Dict

section Proj

variable {Γ : Type*} [Group Γ]

@[expose] noncomputable def uProj (U Z : Subgroup Γ) (x : Γ) : Γ := by
  classical
  exact if hx : ∃ u ∈ U, u⁻¹ * x ∈ Z then Classical.choose hx else 1

theorem uProj_spec {U Z : Subgroup Γ} {x : Γ} (hx : ∃ u ∈ U, u⁻¹ * x ∈ Z) :
    uProj U Z x ∈ U ∧ (uProj U Z x)⁻¹ * x ∈ Z := by
  simp only [uProj, hx, dite_true]
  exact Classical.choose_spec hx

theorem uProj_eq {U Z : Subgroup Γ} (hUZ : U ⊓ Z = ⊥) {x u : Γ} (hu : u ∈ U)
    (hux : u⁻¹ * x ∈ Z) : uProj U Z x = u := by
  obtain ⟨h1, h2⟩ := uProj_spec ⟨u, hu, hux⟩
  have hmem : (uProj U Z x)⁻¹ * u ∈ U ⊓ Z := by
    refine ⟨U.mul_mem (U.inv_mem h1) hu, ?_⟩
    have := Z.mul_mem h2 (Z.inv_mem hux)
    simpa [mul_assoc] using this
  rw [hUZ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem

end Proj

section TwoElt

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem mem_pCoreOf_of_centralizer_Uq {m : G} (hm : m ∈ M)
    (hc : m ∈ Subgroup.centralizer (Uq M T L : Set G)) (h2 : ∃ e : ℕ, m ^ 2 ^ e = 1) :
    m ∈ pCoreOf 2 M := by
  have hDn : M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (Uq M T L : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (le_normalizer_centralizer (le_normalizer_Uq h.le_normalizer))
  refine h.mem_pCoreOf_of_rel hDn (fun hLD => h.not_le_centralizer_of_Uq_le le_rfl
    (hLD.trans inf_le_right)) hm h2 fun l hl => ?_
  have hlm : l * m⁻¹ * l⁻¹ ∈ M ⊓ Subgroup.centralizer (Uq M T L : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (hDn (h.L_le hl)) _).mp
      ⟨M.inv_mem hm, Subgroup.inv_mem _ hc⟩
  have hrw : ⁅m, l⁆ = m * (l * m⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hrw]
  exact Subgroup.mul_mem _ ⟨hm, hc⟩ hlm

theorem mem_qv_of_centralizer_uloc {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {k : (puAmalgam h.le).Universal} (hk : k ∈ stab _ δ)
    (hc : k ∈ Subgroup.centralizer (Uloc h.le L δ : Set (puAmalgam h.le).Universal))
    (h2 : ∃ e : ℕ, k ^ 2 ^ e = 1) : k ∈ Qv _ δ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  rw [stab_eq_map_vEmb h.le g] at hk
  obtain ⟨m, -, rfl⟩ := hk
  have hU := puTrans_eq_map_vEmb h.le (S4A.Uq_normal h) g
  have hmc : (m : G) ∈ Subgroup.centralizer (Uq M T L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : vEmb h.le g ⟨u, Uq_le h.L_le hu⟩ ∈ Uloc h.le L (g • baseA _) := by
      rw [Uloc, hU]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc _ hu'
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (vEmb_injective h.le g this)
  obtain ⟨e, he⟩ := h2
  have hm2 : (m : G) ^ 2 ^ e = 1 := by
    rw [← map_pow] at he
    have := vEmb_injective h.le g (he.trans (map_one _).symm)
    exact congrArg Subtype.val this
  have hmO := mem_pCoreOf_of_centralizer_Uq h m.2 hmc ⟨e, hm2⟩
  rw [h.qv_eq ((PU.isMVtx_smul _ g _).2 (PU.isMVtx_baseA _)),
    puTrans_eq_map_vEmb h.le (Subgroup.normal_subgroupOf_iff_le_normalizer
      (pCoreOf_le' M) |>.2 (le_normalizer_pCoreOf M)) g]
  exact ⟨m, Subgroup.mem_subgroupOf.mpr hmO, rfl⟩

end TwoElt

section Closure

variable {G : Type*} [Group G]

theorem commutator_closure_le_of {S : Set G} {H N : Subgroup G}
    (hS : ∀ s ∈ S, ∀ x ∈ H, ⁅s, x⁆ ∈ N)
    (hN : Subgroup.closure S ≤ Subgroup.normalizer (N : Set G)) :
    ⁅Subgroup.closure S, H⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  induction hx using Subgroup.closure_induction with
  | mem z hz => exact hS z hz y hy
  | one => simp
  | mul a b ha hb iha ihb =>
    have hrw : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN ha) _).mp ihb) iha
  | inv a ha iha =>
    have hrw : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN ha)) _).mp (N.inv_mem iha)

end Closure

section Vec

variable {F : Type} [Field F]

theorem eq_top_of_forall_mulVec_mem {W : Submodule F (Fin 3 → F)} {v : Fin 3 → F} (hv : v ≠ 0)
    (hW : ∀ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) : W = ⊤ := by
  rw [eq_top_iff]
  intro u _
  by_cases hu : u = 0
  · rw [hu]
    exact W.zero_mem
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_e0_eq hv
  obtain ⟨g₂, hg₂⟩ := exists_mulVec_e0_eq hu
  have hgu : ((g₂ * g₁⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = u := by
    rw [← hg₁, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right,
      hg₂]
  rw [← hgu]
  exact hW _

theorem odd_nsmul_eq [CharP F 2] {n : ℕ} (hn : Odd n) (v : Fin 3 → F) : n • v = v := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero, nsmul_zero,
    zero_add]

theorem exists_pow_involution {Γ : Type*} [Monoid Γ] {s : Γ} (hs : s ≠ 1) {e : ℕ}
    (he : s ^ 2 ^ e = 1) : ∃ j : ℕ, (s ^ 2 ^ j) * (s ^ 2 ^ j) = 1 ∧ s ^ 2 ^ j ≠ 1 := by
  classical
  have hex : ∃ i, s ^ 2 ^ i = 1 := ⟨e, he⟩
  set i := Nat.find hex with hi
  have hi1 : s ^ 2 ^ i = 1 := Nat.find_spec hex
  have hi0 : i ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hi1
    exact hs hi1
  refine ⟨i - 1, ?_, Nat.find_min hex (by omega)⟩
  rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)]
  exact hi1

end Vec

end CFSG.Quasithin.MS93.S4A
