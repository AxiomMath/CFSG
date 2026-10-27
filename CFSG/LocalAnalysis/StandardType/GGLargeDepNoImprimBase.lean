module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNineDepDefs
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
import CFSG.LocalAnalysis.StandardType.GGRCMonomial
import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGLargeLinHyp.toNineLinHyp {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGLargeLinHyp p N h α r s x) : GGNineLinHyp p N h α r s x :=
  ⟨L.p_ne_two, by have := L.N_ge; omega, L.p_dvd, L.dim_le, L.pair, L.refl_form, L.finT,
    L.s_refl, L.conn, L.x_ne, L.fix_s, L.x_not_fix, L.no_transv⟩

lemma l04fD4_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
  have hp2 : p = 2 := by
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact hp hp2

lemma l04fD4_pair_diag {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) (i : Fin (N - 1)) : α i (h i) = 2 := by
  rw [L.pair i i]
  simp [CartanMatrix.A]

lemma l04fD4_h_ne_zero {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) (i : Fin (N - 1)) : h i ≠ 0 := by
  intro h0
  have hp := l04fD4_pair_diag L i
  rw [h0, map_zero] at hp
  exact (l04fD4_two_ne_zero L.p_ne_two) hp.symm

lemma l04fD4_rsq {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) (i : Fin (N - 1)) : r i * r i = 1 := by
  ext v
  change r i (r i v) = v
  rw [L.refl_form i (r i v), L.refl_form i v, map_sub, map_smul,
    l04fD4_pair_diag L i]
  module

lemma l04fD4_coxeter_relation {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) (i j : Fin (N - 1)) :
    (r i * r j) ^ (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (N - 1))).M i j = 1 := by
  rw [CFSG.StandardType.coxeterMatrix_A_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, pow_one]
    exact l04fD4_rsq L i
  · rw [if_neg hij]
    by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · rw [if_pos hadj]
      have hpij : α i (h j) = -1 := by
        rw [L.pair i j]
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij, if_pos hadj]
        norm_num
      have hpji : α j (h i) = -1 := by
        rw [L.pair j i]
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg (Ne.symm hij), if_pos hadj.symm]
        norm_num
      have hpii : α i (h i) = 2 := l04fD4_pair_diag L i
      have hpjj : α j (h j) = 2 := l04fD4_pair_diag L j
      have hbraid : r i * r j * r i = r j * r i * r j := by
        apply LinearEquiv.ext
        intro v
        simp only [LinearEquiv.mul_apply, L.refl_form, map_sub, map_smul]
        rw [hpij, hpji, hpii, hpjj]
        module
      have hsq_i := l04fD4_rsq L i
      have hsq_j := l04fD4_rsq L j
      calc (r i * r j) ^ 3
          = (r i * r j * r i) * (r j * r i * r j) := by
            rw [pow_succ, pow_succ, pow_one]; group
        _ = (r i * r j * r i) * (r i * r j * r i) := by rw [hbraid]
        _ = 1 := by
            calc (r i * r j * r i) * (r i * r j * r i)
                = r i * r j * (r i * r i) * r j * r i := by group
              _ = r i * r j * 1 * r j * r i := by rw [hsq_i]
              _ = r i * (r j * r j) * r i := by group
              _ = r i * 1 * r i := by rw [hsq_j]
              _ = 1 := by rw [mul_one, hsq_i]
    · rw [if_neg hadj]
      have hpij : α i (h j) = 0 := by
        rw [L.pair i j]
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij, if_neg hadj]
        norm_num
      have hpji : α j (h i) = 0 := by
        rw [L.pair j i]
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg (Ne.symm hij)]
        have hnot : ¬ ((j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)) := by
          rintro (h | h)
          · exact hadj (Or.inr h)
          · exact hadj (Or.inl h)
        rw [if_neg hnot]
        norm_num
      have hpii : α i (h i) = 2 := l04fD4_pair_diag L i
      have hpjj : α j (h j) = 2 := l04fD4_pair_diag L j
      have hcomm : r i * r j = r j * r i := by
        apply LinearEquiv.ext
        intro v
        simp only [LinearEquiv.mul_apply, L.refl_form, map_sub, map_smul]
        rw [hpij, hpji]
        module
      have hsi := l04fD4_rsq L i
      have hsj := l04fD4_rsq L j
      calc (r i * r j) ^ 2 = (r i * r j) * (r i * r j) := by rw [pow_two]
        _ = r i * (r j * r i) * r j := by group
        _ = r i * (r i * r j) * r j := by rw [← hcomm]
        _ = (r i * r i) * (r j * r j) := by group
        _ = 1 := by rw [hsi, hsj, mul_one]

lemma l04fD4_restrict_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (T : Submodule (ZMod p) V) (g : ↥(ggLinStab T)) (v : ↥T) :
    (((ggLinRestrictHom T g) v : ↥T) : V) = (g : V ≃ₗ[ZMod p] V) (v : V) := by
  simp [ggLinRestrictHom, LinearEquiv.ofSubmodules_apply]

noncomputable def l04fD4_phiCox {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) : Equiv.Perm (Fin (N - 1 + 1)) →* (V ≃ₗ[ZMod p] V) :=
  ((CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (N - 1))).toCoxeterSystem.lift
    ⟨fun i => r i, fun i j => l04fD4_coxeter_relation L i j⟩).comp
    (typeAWeylEquiv (N - 1)).toMonoidHom

lemma l04fD4_phiCox_swap {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) (k : Fin (N - 1)) :
    l04fD4_phiCox L (Equiv.swap k.castSucc k.succ) = r k := by
  simp only [l04fD4_phiCox, MonoidHom.comp_apply]
  rw [show (typeAWeylEquiv (N - 1)).toMonoidHom (Equiv.swap k.castSucc k.succ) =
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (N - 1))).toCoxeterSystem.simple k from
    typeAWeylEquiv_swap (N - 1) k]
  exact CoxeterSystem.lift_apply_simple _ _ k

lemma l04fD4_perm_normal_abelian_bot {N : ℕ} (hN : 5 ≤ N)
    (H : Subgroup (Equiv.Perm (Fin N))) [H.Normal]
    (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : H = ⊥ := by
  by_contra hne
  have hnt : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have hle : alternatingGroup (Fin N) ≤ H :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin N) (N := H) (by simpa using hN)
      (inferInstance : Nontrivial ↥H)
  have : Nontrivial (Fin N) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hcomm : ⁅alternatingGroup (Fin N), alternatingGroup (Fin N)⁆ = ⊥ := by
    rw [Subgroup.commutator_self_eq_bot_iff]
    exact isMulCommutative_iff.mpr (fun (a b : ↥(alternatingGroup (Fin N))) =>
      Subtype.ext (hab a.1 (hle a.2) b.1 (hle b.2)))
  have hA : alternatingGroup (Fin N) = ⊥ := by
    have h := commutator_alternatingGroup_eq_self (α := Fin N) (by simpa using hN)
    rw [hcomm] at h
    exact h.symm
  have hfac : 120 ≤ N.factorial := by
    have h := Nat.factorial_le hN
    norm_num at h
    exact h
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin N)
  rw [hA] at h2
  have hbot : Nat.card (⊥ : Subgroup (Equiv.Perm (Fin N))) = 1 := by simp
  rw [hbot, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h2
  omega

lemma l04fD4_adjacent_ne_one {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) {i j : Fin (N - 1)}
    (hadj : (i : ℕ) + 1 = j) (hk : (j : ℕ) + 1 < N - 1) :
    r i * r j ≠ 1 := by
  intro hprod
  have hri : r i = r j := by
    have hj := l04fD4_rsq L j
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e * r j) hprod
    rwa [mul_assoc, hj, mul_one, one_mul] at h
  let k : Fin (N - 1) := ⟨(j : ℕ) + 1, hk⟩
  have hk_i : α i (h k) = 0 := by
    rw [L.pair i k]
    simp only [CartanMatrix.A, Matrix.of_apply]
    have hik : i ≠ k := by
      intro hh
      have := congrArg Fin.val hh
      simp only [k] at this
      omega
    rw [if_neg hik]
    have hnot : ¬ ((i : ℕ) + 1 = (k : ℕ) ∨ (k : ℕ) + 1 = (i : ℕ)) := by
      simp only [k]; omega
    rw [if_neg hnot]
    norm_num
  have hk_j : α j (h k) = -1 := by
    rw [L.pair j k]
    simp only [CartanMatrix.A, Matrix.of_apply]
    have hjk : j ≠ k := by
      intro hh
      have := congrArg Fin.val hh
      simp only [k] at this
      omega
    rw [if_neg hjk]
    have hjk1 : (j : ℕ) + 1 = (k : ℕ) := by simp only [k]
    rw [if_pos (Or.inl hjk1)]
    norm_num
  have hv : r i (h k) = r j (h k) := by rw [hri]
  rw [L.refl_form i (h k), L.refl_form j (h k), hk_i, hk_j] at hv
  have hzero : h j = 0 := by
    have h1 : h k - (0 : ZMod p) • h i = h k - (-1 : ZMod p) • h j := hv
    rw [zero_smul, sub_zero, neg_one_smul, sub_neg_eq_add] at h1
    have h2 : h j = h k + h j - h k := by abel
    rw [h2, ← h1]; abel
  exact l04fD4_h_ne_zero L j hzero

lemma l04fD4_eq_swap_of {n : ℕ} (τ : Equiv.Perm (Fin n)) {p q : Fin n}
    (hp : τ p = q) (hq : τ q = p)
    (hfix : ∀ k, τ k ≠ k → k = p ∨ k = q) : τ = Equiv.swap p q := by
  ext k
  by_cases hk : k = p
  · subst hk
    rw [hp, Equiv.swap_apply_left]
  · by_cases hk' : k = q
    · subst hk'
      rw [hq, Equiv.swap_apply_right]
    · have hfixk : τ k = k := by
        by_contra hne
        rcases hfix k hne with h | h
        · exact hk h
        · exact hk' h
      rw [hfixk, Equiv.swap_apply_of_ne_of_ne hk hk']

lemma l04fD4_ri_ne_one {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) (i : Fin (N - 1)) : r i ≠ 1 := by
  intro hri
  have h1 : r i (h i) = h i := by rw [hri]; rfl
  rw [L.refl_form i (h i), l04fD4_pair_diag L i] at h1
  have h2 : (2 : ZMod p) • h i = 0 := sub_eq_self.mp h1
  exact l04fD4_h_ne_zero L i
    ((smul_eq_zero.mp h2).resolve_left (l04fD4_two_ne_zero L.p_ne_two))

lemma l04fD4_h_mem_T {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x) (i : Fin (N - 1)) : h i ∈ ggFixLineT r s := by
  have h2 : (2 : ZMod p) ≠ 0 := l04fD4_two_ne_zero L.p_ne_two
  have hc2 : (-(2 : ZMod p)⁻¹) * 2 = -1 := by rw [neg_mul, inv_mul_cancel₀ h2]
  have heq : h i = (-(2 : ZMod p)⁻¹) • (r i (h i) - h i) := by
    rw [L.refl_form i (h i), l04fD4_pair_diag L i, smul_sub, smul_sub, smul_smul, hc2,
      neg_one_smul]
    module
  rw [heq]
  exact (ggFixLineT r s).smul_mem _ (Submodule.mem_sup_left
    ((le_iSup (fun j => ggLinMove (r j)) i) (by
      rw [ggLinMove]
      exact LinearMap.mem_range.mpr ⟨h i, rfl⟩)))

lemma l04fD4_move_rank_one {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (L : GGNineLinHyp p N h α r s x)
    (A : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)))
    (Afun : Fin (N - 1) → ↥(A))
    (hcoord : ∀ (i : Fin (N - 1)) (u : ↥(ggFixLineT r s)),
      (((Afun i) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) u : V) = r i (u : V))
    (i : Fin (N - 1)) :
    Module.finrank (ZMod p) (ggLinMove
      ((Afun i) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))) = 1 := by
  classical
  have : Finite ι := L.finT
  have : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) s L.s_refl L.fix_s
  let T : Submodule (ZMod p) V := ggFixLineT r s
  have hhiT : h i ∈ T := l04fD4_h_mem_T L i
  let hi : ↥T := ⟨h i, hhiT⟩
  have hhi_ne : hi ≠ 0 := by
    intro h0
    exact l04fD4_h_ne_zero L i (by simpa [hi] using congrArg Subtype.val h0)
  have hval : ∀ u : ↥T,
      (((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) u - u : ↥T) = (-α i (u : V)) • hi := by
    intro u
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul, hcoord i u, L.refl_form i (u : V)]
    module
  have hle : ggLinMove ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) ≤
      Submodule.span (ZMod p) {hi} := by
    intro w hw
    rw [ggLinMove, LinearMap.mem_range] at hw
    obtain ⟨u, hu⟩ := hw
    rw [Submodule.mem_span_singleton]
    refine ⟨-α i (u : V), ?_⟩
    rw [← hu, LinearMap.sub_apply, LinearMap.id_apply]
    exact Subtype.ext (by
      simpa [Submodule.coe_smul] using congrArg Subtype.val (hval u).symm)
  have h1 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {hi}) = 1 :=
    finrank_span_singleton hhi_ne
  have h2 : 1 ≤ Module.finrank (ZMod p)
      (ggLinMove ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T)) := by
    have hw0 : ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) hi - hi ≠ 0 := by
      intro h0
      have hz : ((-α i (hi : V)) • hi : ↥T) = 0 := by
        rw [← hval hi, h0]
      have hcoef : (-α i (h i)) • h i = 0 := by
        have := congrArg Subtype.val hz
        simpa [hi] using this
      have hcoef' : (α i (h i)) • h i = 0 := by
        have := congrArg Neg.neg hcoef
        simpa using this
      have h2 : (2 : ZMod p) • h i = 0 := by
        simpa [l04fD4_pair_diag L i] using hcoef'
      exact (l04fD4_two_ne_zero L.p_ne_two) ((smul_eq_zero.mp h2).resolve_right (l04fD4_h_ne_zero L i))
    have hmem : ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) hi - hi ∈
        ggLinMove ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) := by
      rw [ggLinMove, LinearMap.mem_range]
      exact ⟨hi, rfl⟩
    have hspan_le : Submodule.span (ZMod p)
        {((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) hi - hi} ≤
        ggLinMove ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T) := by
      rw [Submodule.span_le]
      rintro w (rfl : w = _)
      exact hmem
    have hfin := Submodule.finrank_mono hspan_le
    rwa [finrank_span_singleton hw0] at hfin
  have h3 : Module.finrank (ZMod p)
      (ggLinMove ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T)) ≤ 1 := by
    have hfin := Submodule.finrank_mono hle
    rwa [h1] at hfin
  show Module.finrank (ZMod p)
      (ggLinMove ((Afun i : ↥(A)) : ↥T ≃ₗ[ZMod p] ↥T)) = 1
  omega

end CFSG.StandardType

end
