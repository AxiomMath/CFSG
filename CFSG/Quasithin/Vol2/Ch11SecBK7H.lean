module

public import CFSG.Quasithin.Vol2.Ch11SecBK7G
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecA12Out2
public import CFSG.Quasithin.Vol2.Ch11SecAKA19
public import CFSG.Quasithin.Vol2.Ch11SecBK7A
public import CFSG.Quasithin.Vol2.Ch11SecBK7E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp)
open scoped IsMulCommutative

namespace K7

variable {K : Type} [Field K]

theorem eq_qSp_of_shape {T : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)}
    (hadd : ∀ x y, T (x + y) = T x + T y) (hsmul : ∀ (c : K) x, T (c • x) = c • T x)
    (hP : ∀ x ∈ spPlane K, T x = x) (hQ : ∀ x, T x - x ∈ spPlane K)
    (hB : Matrix.toBilin' (spJ K) (T (vec4 0 0 1 0)) (T (vec4 0 0 0 1)) = 0) (v : _) :
    T v = mat 2 K (qSp (T (vec4 0 0 1 0) (.inl 0)) (T (vec4 0 0 0 1) (.inl 0))
      (T (vec4 0 0 0 1) (.inl 1))) *ᵥ v := by
  have q0 := hQ (vec4 0 0 1 0)
  have q1 := hQ (vec4 0 0 0 1)
  simp only [mem_spPlane, Pi.sub_apply, vec4_apply_inr0, vec4_apply_inr1, sub_zero,
    sub_eq_zero] at q0 q1
  have hf0 : T (vec4 0 0 1 0) = vec4 (T (vec4 0 0 1 0) (.inl 0)) (T (vec4 0 0 1 0) (.inl 1)) 1 0 :=
    vec4_eq rfl rfl q0.1 q0.2
  have hf1 : T (vec4 0 0 0 1) = vec4 (T (vec4 0 0 0 1) (.inl 0)) (T (vec4 0 0 0 1) (.inl 1)) 0 1 :=
    vec4_eq rfl rfl q1.1 q1.2
  have hsym : T (vec4 0 0 1 0) (.inl 1) = T (vec4 0 0 0 1) (.inl 0) := by
    rw [hf0, hf1, toBilin'_spJ_apply] at hB
    simp only [Fin.sum_univ_two, vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
      vec4_apply_inr1] at hB
    linear_combination hB
  have hTv : T v = v (.inl 0) • vec4 1 0 0 0 + v (.inl 1) • vec4 0 1 0 0 +
      v (.inr 0) • T (vec4 0 0 1 0) + v (.inr 1) • T (vec4 0 0 0 1) := by
    conv_lhs => rw [KA.eq_basis v]
    rw [hadd, hadd, hadd, hsmul, hsmul, hsmul, hsmul, hP _ ⟨rfl, rfl⟩, hP _ ⟨rfl, rfl⟩]
  rw [hTv, qSp_mulVec]
  conv_lhs => rw [hf0, hf1]
  rw [← hsym]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl0, vec4_apply_inl1,
      vec4_apply_inr0, vec4_apply_inr1] <;> ring

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem exists_qSp_of_mem_r2 (hfl : Flag24 L V X T V₁ V₂ n) [IsMulCommutative ↥V] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ n) {π : ↥(StatedSp 2 K) →* ↥(autOn L V)}
    {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) {g : StatedSp 2 K}
    (hV₂ : V₂.subgroupOf V = hf.pre (gmapSp g (spPlane K)).toAddSubgroup) {r : G}
    (hr : r ∈ pCoreOf 2 (LOf L V₂ ⊔ T)) :
    ∃ x y z : K, SecA.conjV V r (r2_le_normalizer hfl hr) =
      ((π (g * qSp x y z * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : ∃ s : Finset K, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hfl.two_le hK)
  obtain ⟨⟨⟨hrV, hrL⟩, hrV₂⟩, -⟩ := r2_le hfl hr
  set k := SecA.conjV V r hrV with hk
  have hkZ' : ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, k z ∈
      (Subgroup.centralizer (L : Set G)).subgroupOf V := fun z hz =>
    G2Q8.conjV_mem_centralizer hrL hrV hz
  have hkinv : k⁻¹ = SecA.conjV V r⁻¹ (Subgroup.inv_mem _ hrV) := (SecA.conjV_inv V hrV).symm
  have hkZ : k ∈ SecA.stabW ((Subgroup.centralizer (L : Set G)).subgroupOf V) :=
    SecA.mem_stabW.mpr fun u => ⟨hkZ' u, fun hu => by
      have := G2Q8.conjV_mem_centralizer (Subgroup.inv_mem _ hrL) (Subgroup.inv_mem _ hrV) hu
      rwa [← hkinv, MulAut.inv_apply_self] at this⟩
  have hkH : ∀ h ∈ autOn L V, k * h * k⁻¹ ∈ autOn L V := fun h hh =>
    G2Q8.conjV_mul_conjV_inv_mem hrL hrV hh
  have hkU : k ∈ SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup) := by
    rw [← hV₂]
    exact (SecA.conjV_mem_stabW_iff hfl.le₂ hrV).mpr hrV₂
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hkc : ∀ s ∈ perfectCore (autOn L V ⊓
      SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)),
      k * s * k⁻¹ * s⁻¹ ∈ pCoreOf 2 (perfectCore (autOn L V ⊓
        SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup))) := by
    rw [← hV₂, ← SecA.autOn_lOf hfl.le_normalizer hfl.le₂,
      ← SecA.autOn_pCoreOf (hL₂L.trans hfl.le_normalizer)
        (hfl.cL_two.to_le (inf_le_inf_right _ hL₂L))]
    intro s hs
    obtain ⟨y, hyL₂, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hs
    rw [hkinv, ← SecA.conjV_inv V hyV, ← SecA.conjV_mul, ← SecA.conjV_mul, ← SecA.conjV_mul]
    exact SecA.conjV_mem_autOn (comm_mem_pCoreOf hfl hr hyL₂) _
  obtain ⟨hadd, hsmul, -, μ, ν, -, h0, h1, h2, h3, h4, h5⟩ :=
    KA.tf_shape hK4 hf g hkZ hkH hkU hkc
  set Tk := KA.tf hf g k with hTk
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (LOf L V₂ ⊔ T) ⟨r, hr⟩
  have hrm : r ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hit : ∀ x, Tk^[2 ^ m] x = x := fun x => by
    rw [← tf_pow hf g hkZ', SecA.conjV_pow_eq_one V hrV hrm, ← pow_zero k, tf_pow hf g hkZ',
      Function.iterate_zero, id_eq]
  have hμ : μ = 1 := by
    have hiter : ∀ j : ℕ, Tk^[j] (vec4 1 0 0 0) = μ ^ j • vec4 1 0 0 0 := by
      intro j
      induction j with
      | zero => rw [Function.iterate_zero, id_eq, pow_zero, one_smul]
      | succ j ih => rw [Function.iterate_succ_apply', ih, hsmul, h0, smul_smul, pow_succ]
    have h := congrFun ((hiter (2 ^ m)).symm.trans (hit _)) (.inl 0)
    simp only [Pi.smul_apply, vec4_apply_inl0, smul_eq_mul, mul_one] at h
    exact KA.eq_one_of_pow_two_pow h
  have hinr := KA.shape_inr hadd hsmul h0 h1 h2 h3 h4 h5
  have hν : ν = 1 := by
    have hiter : ∀ j : ℕ, ∀ v, (Tk^[j] v) (.inr 0) = ν ^ j * v (.inr 0) := by
      intro j
      induction j with
      | zero => intro v; rw [Function.iterate_zero, id_eq, pow_zero, one_mul]
      | succ j ih =>
        intro v
        rw [Function.iterate_succ_apply', (hinr _).1, ih, pow_succ]
        ring
    have h := hiter (2 ^ m) (vec4 0 0 1 0)
    rw [hit, vec4_apply_inr0, mul_one] at h
    exact KA.eq_one_of_pow_two_pow h.symm
  have hP : ∀ x ∈ spPlane K, Tk x = x := fun x hx => by
    rw [KA.shape_plane hadd hsmul h0 h1 hx, hμ, one_smul]
  have hQ : ∀ x, Tk x - x ∈ spPlane K := fun x => by
    obtain ⟨e0, e1⟩ := hinr x
    rw [hν, one_mul] at e0 e1
    exact ⟨by rw [Pi.sub_apply, e0, sub_self], by rw [Pi.sub_apply, e1, sub_self]⟩
  let TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := Tk, map_add' := hadd, map_smul' := hsmul }
  obtain ⟨c, hc⟩ := exists_similitude TL fun γ => by
    obtain ⟨γ', hγ'⟩ := tf_conj hf g hkZ' hkH γ
    exact ⟨γ', fun x => hγ' x⟩
  have hc1 : c = 1 := by
    have e : Matrix.toBilin' (spJ K) (Tk (vec4 1 0 0 0)) (Tk (vec4 0 0 1 0)) =
        c * Matrix.toBilin' (spJ K) (vec4 1 0 0 0) (vec4 0 0 1 0) := hc _ _
    rw [hP _ ⟨rfl, rfl⟩, spB_e0, spB_e0, h2, hν, vec4_apply_inr0, mul_one] at e
    exact e.symm
  have hB : Matrix.toBilin' (spJ K) (Tk (vec4 0 0 1 0)) (Tk (vec4 0 0 0 1)) = 0 := by
    have e : Matrix.toBilin' (spJ K) (Tk (vec4 0 0 1 0)) (Tk (vec4 0 0 0 1)) =
        c * Matrix.toBilin' (spJ K) (vec4 0 0 1 0) (vec4 0 0 0 1) := hc _ _
    rw [e, toBilin'_spJ_apply]
    simp [Fin.sum_univ_two, vec4]
  have hT := eq_qSp_of_shape hadd hsmul hP hQ hB
  refine ⟨Tk (vec4 0 0 1 0) (.inl 0), Tk (vec4 0 0 0 1) (.inl 0), Tk (vec4 0 0 0 1) (.inl 1),
    eq_pi_of_modZ hf fix_of_autOn (commV_autOn_eq_top hfl.le_normalizer hfl.commutator_eq) hkH
      fun w => ?_⟩
  have e := KA.tf_mk hf g hkZ' w
  rw [← hTk, hT] at e
  rw [KA.gconj_mulVec_sp, e, mat_mulVec_inv]

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
