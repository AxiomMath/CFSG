module

public import CFSG.Quasithin.H13.U3L15A
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.H13.A6S1372L76G
public import CFSG.Quasithin.H13.A6S13812

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace A6L76N3

theorem perm_stab_W2_pow : ∀ σ : Perm (Fin 6), (∀ x, InW2 x → InW2 (act4f σ x)) →
    act4f σ e0123 = e0123 → σ ^ 16 = 1 := by
  decide +kernel

theorem c012_not_W2 : ¬ InW2 (dv ((swap 0 1 * swap 1 2 : Perm (Fin 6)) 0)
    ((swap 0 1 * swap 1 2 : Perm (Fin 6)) 1)) := by
  decide +kernel

theorem a6s3_moves_z : act4f U3.a6s3 e0123 ≠ e0123 ∧ act4f (U3.a6s3 * U3.a6s3) e0123 ≠ e0123 := by
  decide +kernel

end A6L76N3

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem isPGroup_cLT (hhat : ¬ IsHatA6 L) :
    IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  have hCL : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) :=
    (pCoreOf_isPGroup 2 L).to_le (S.inf_centralizer_le_pCoreOf hhat)
  rintro ⟨x, hxLT, hxC⟩
  have hx : x ∈ ((L : Set G) * (T : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T S.T_le_NL]
    exact hxLT
  obtain ⟨l, hl, t, ht, rfl⟩ := hx
  obtain ⟨a, ha⟩ := S.h13.sylow.1 ⟨t, ht⟩
  have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨l', hl', he⟩ := U3.pow_mem_mul_of_normalizes' hl (S.T_le_NL ht) (2 ^ a)
  rw [hta, mul_one] at he
  have hC : (l * t) ^ 2 ^ a ∈ Subgroup.centralizer (V : Set G) := Subgroup.pow_mem _ hxC _
  rw [he] at hC
  obtain ⟨k, hk⟩ := hCL ⟨l', hl', hC⟩
  refine ⟨a + k, Subtype.ext ?_⟩
  have hk' : l' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk']

theorem inf_M_le_NV' {H : Subgroup G} (hH : H ∈ S.Hz) :
    H ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rw [← S.conjClosure_V1_L]
  refine A5.le_normalizer_of_forall_conj_mem fun g hg v hv => ?_
  have hgz : g * S.z * g⁻¹ = S.z := by
    have h1 : g ∈ S.G1 := hH.2.1 hg.1
    rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, w, hw, rfl⟩ := hx
    have hlg : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg.2 l).mp hl
    have hwg : g * w * g⁻¹ ∈ fsuV1 T V := by
      rcases S.mem_V1_iff.1 hw with h | h
      · rw [h, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h, hgz]
        exact S.mem_V1_iff.2 (Or.inr rfl)
    have e : g * (l * w * l⁻¹) * g⁻¹ = (g * l * g⁻¹) * (g * w * g⁻¹) * (g * l * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure hlg hwg
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem isPGroup_triple (hhat : ¬ IsHatA6 L) {H : Subgroup G}
    (hH : H ∈ S.Hz) :
    IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.normalizer (S.V2 : Set G) ⊓ H) := by
  rintro ⟨x, ⟨hxLT, hxN⟩, hxH⟩
  have hxM : x ∈ Subgroup.normalizer (L : Set G) :=
    (sup_le Subgroup.le_normalizer S.T_le_NL) hxLT
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.inf_M_le_NV' hH ⟨hxH, hxM⟩
  set xn : ↥(Subgroup.normalizer (V : Set G)) := ⟨x, hxV⟩ with hxn
  have hW2 : ∀ y, InW2 y → InW2 (act4f (S.frame.ρ xn) y) := by
    intro y hy
    have hyW : y ∈ W4 := by
      rcases hy with h | h | h | h <;> rw [h]
      · exact W4.one_mem
      · exact dv_mem 0 1
      · exact dv_mem 2 3
      · exact e0123_mem_W4
    set v : ↥V := S.frame.ψ.symm ⟨y, hyW⟩ with hv
    have hvV2 : (v : G) ∈ S.V2 := by
      refine S.mem_pre.2 ⟨v.2, ?_⟩
      show InW2 ((S.frame.ψ v : ↥W4) : P6)
      rw [hv, MulEquiv.apply_symm_apply]
      exact hy
    have h1 : x * v * x⁻¹ ∈ S.V2 := (Subgroup.mem_normalizer_iff.mp hxN _).mp hvV2
    obtain ⟨hh, h2⟩ := S.mem_pre.1 h1
    have h3 := S.psi_conj xn v
    rw [hv, MulEquiv.apply_symm_apply] at h3
    rw [show act4f (S.frame.ρ xn) y = ((act4 (S.frame.ρ xn) ⟨y, hyW⟩ : ↥W4) : P6) from rfl,
      ← h3]
    exact h2
  have hz : act4f (S.frame.ρ xn) e0123 = e0123 := by
    have hzc : x * S.z * x⁻¹ = S.z := by
      have h1 : x ∈ S.G1 := hH.2.1 hxH
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
      rw [h1, mul_inv_cancel_right]
    have h3 := S.psi_conj xn ⟨S.z, S.z_mem_V⟩
    have e : (⟨x * S.z * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxV _).mp S.z_mem_V⟩ : ↥V) =
        ⟨S.z, S.z_mem_V⟩ := Subtype.ext hzc
    rw [e, S.psi_z] at h3
    exact (congrArg Subtype.val h3).symm
  have h16 := A6L76N3.perm_stab_W2_pow _ hW2 hz
  have hC : x ^ 16 ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨(L ⊔ T).pow_mem hxLT _, ?_⟩
    have : S.frame.ρ (xn ^ 16) = 1 := by rw [map_pow, h16]
    exact (S.rho_eq_one_iff (xn ^ 16)).1 this
  obtain ⟨k, hk⟩ := S.isPGroup_cLT hhat ⟨_, hC⟩
  refine ⟨4 + k, Subtype.ext ?_⟩
  have hk' : (x ^ 16) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
  simpa using hk'

theorem cLT_eq (hhat : ¬ IsHatA6 L) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  refine le_antisymm (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (S.isPGroup_cLT hhat)) ?_
  · intro g hg
    refine mem_normalizer_inf_of (Subgroup.le_normalizer hg) ?_
    exact normalizes_of_conj_mem (X := L ⊔ T)
      (fun l hl y hy => conj_centralizer_mem (hLTV hl) hy) hg
  · rw [← S.cT]
    exact inf_le_inf_right _ le_sup_right

theorem d1_LT (hhat : ¬ IsHatA6 L) :
    quasithinO2QuotientIso (L ⊔ T) ↥(alternatingGroup (Fin 6)) ∨
      quasithinO2QuotientIso (L ⊔ T) (Perm (Fin 6)) := by
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  set ρLT : ↥(L ⊔ T) →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hLTV) with hρLT
  have hker : ρLT.ker = CFSG.Open.pCore 2 ↥(L ⊔ T) := by
    have e1 : CFSG.Open.pCore 2 ↥(L ⊔ T) = (pCoreOf 2 (L ⊔ T)).subgroupOf (L ⊔ T) :=
      (Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective _).symm
    rw [e1, ← S.cLT_eq hhat]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨x.2, (S.rho_eq_one_iff (Subgroup.inclusion hLTV x)).1 h⟩
    · intro h
      exact (S.rho_eq_one_iff (Subgroup.inclusion hLTV x)).2 h.2
  have hA6 : alternatingGroup (Fin 6) ≤ ρLT.range := by
    intro σ hσ
    obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
    exact ⟨⟨g, Subgroup.mem_sup_left hgL⟩, hg⟩
  have hdvd : ρLT.range.index ∣ 2 :=
    alternatingGroup.index_eq_two (α := Fin 6) ▸ Subgroup.index_dvd_of_le hA6
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · right
    refine ⟨ρLT, ?_, hker⟩
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.index_eq_one.1 h1
  · left
    have heq : ρLT.range = alternatingGroup (Fin 6) := by
      refine (Subgroup.eq_of_le_of_card_ge hA6 ?_).symm
      have h3 := ρLT.range.card_mul_index
      have h4 := (alternatingGroup (Fin 6)).card_mul_index
      rw [h2] at h3
      rw [alternatingGroup.index_eq_two] at h4
      omega
    refine ⟨ρLT.codRestrict (alternatingGroup (Fin 6)) fun x => heq ▸ ⟨x, rfl⟩, ?_, ?_⟩
    · rintro ⟨σ, hσ⟩
      obtain ⟨x, hx⟩ := heq ▸ hσ
      exact ⟨x, Subtype.ext hx⟩
    · rw [MonoidHom.ker_codRestrict, hker]

theorem d4_of (h139 : Stmt13_3_9) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H)
    (N : Subgroup G) (hN2 : IsPGroup 2 ↥N) (hLT : L ⊔ T ≤ Subgroup.normalizer (N : Set G))
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) : N = ⊥ := by
  by_contra hN1
  have hloc : IsTwoLocal (Subgroup.normalizer (N : Set G)) := ⟨N, hN1, hN2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM := S.uniqueM.2 M' ⟨hM', hLT.trans hle⟩
  apply (S.lem13812_one h139 h37 h38 hH hK).1
  rw [← hM]
  exact hKN.trans hle

theorem cL1_not_mem_NV2 (hhat : ¬ IsHatA6 L) :
    (S.cL1 hhat : G) ∉ Subgroup.normalizer (S.V2 : Set G) := by
  intro hN
  have hv2 : S.v2 ∈ S.V2 := S.v2_mem_V2
  have h1 : (S.cL1 hhat : G) * S.v2 * (S.cL1 hhat : G)⁻¹ ∈ S.V2 :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp hv2
  obtain ⟨hh, h2⟩ := S.mem_pre.1 h1
  apply A6L76N3.c012_not_W2
  rw [← S.cL1_rho hhat, ← S.psi_conj_v2 (S.cL1 hhat)]
  exact h2

theorem exists_L2_three (hhat : ¬ IsHatA6 L) :
    ∃ ℓ ∈ L₁Of L S.V2, ℓ ^ 3 = 1 ∧ ℓ * S.z * ℓ⁻¹ ≠ S.z := by
  obtain ⟨x, hx, hx3, -, hxN, hρx⟩ := U3.L15A.exists_X_nonhat S hhat
  refine ⟨x, hx, hx3, fun hz => ?_⟩
  set xn : ↥(Subgroup.normalizer (V : Set G)) := ⟨x, hxN⟩ with hxn
  have h3 := S.psi_conj xn ⟨S.z, S.z_mem_V⟩
  have e : (⟨x * S.z * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN _).mp S.z_mem_V⟩ : ↥V) =
      ⟨S.z, S.z_mem_V⟩ := Subtype.ext hz
  rw [e, S.psi_z] at h3
  have h4 : e0123 = act4f (S.frame.ρ xn) e0123 := congrArg Subtype.val h3
  rcases hρx with h | h
  · exact A6L76N3.a6s3_moves_z.1 (by rw [← h]; exact h4.symm)
  · exact A6L76N3.a6s3_moves_z.2 (by rw [← h]; exact h4.symm)

end Setting4

end CFSG.Quasithin.H13.A6
