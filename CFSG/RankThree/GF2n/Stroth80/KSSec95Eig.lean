module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.KS95

open Polynomial Module

theorem iSup_eigenspace_eq_top_of_pow_card {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] (f : Module.End K V) (hf : f ^ Fintype.card K = f) :
    ⨆ c : K, f.eigenspace c = ⊤ := by
  classical
  have key : ∀ s : Finset K,
      LinearMap.ker (aeval f (∏ c ∈ s, (X - C c))) = ⨆ c ∈ s, f.eigenspace c := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, map_one, Finset.notMem_empty, iSup_false, iSup_bot]
      exact LinearMap.ker_id
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime f ?_, ih,
        Finset.iSup_insert]
      · congr 1
        ext v
        simp [Module.End.mem_eigenspace_iff, sub_eq_zero]
      · refine IsCoprime.prod_right fun c hc => ?_
        have hac : a ≠ c := fun h => ha (h ▸ hc)
        exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hac).isUnit
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hmon : (X ^ Fintype.card K - X : K[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hq)
  have hroots := FiniteField.roots_X_pow_card_sub_X K
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
    (by rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq K hq]; simp)
  rw [hroots] at hprod
  have htop : LinearMap.ker (aeval f (X ^ Fintype.card K - X : K[X])) = ⊤ := by
    rw [LinearMap.ker_eq_top, map_sub, map_pow, aeval_X, hf, sub_self]
  rw [← hprod, ← Finset.prod_eq_multiset_prod, key] at htop
  simpa using htop

theorem iSupIndep_and_iSup_eq_of_ringHom {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] (W : Submodule K V) (κ : K → Module.End K V)
    (hW : ∀ a, ∀ y ∈ W, κ a y ∈ W) (hadd : ∀ a b, ∀ y ∈ W, κ (a + b) y = κ a y + κ b y)
    (hmul : ∀ a b, ∀ y ∈ W, κ (a * b) y = κ a (κ b y)) (hone : ∀ y ∈ W, κ 1 y = y) :
    iSupIndep (fun σ : K ≃+* K => W ⊓ ⨅ a, (κ a).eigenspace (σ a)) ∧
      ⨆ σ : K ≃+* K, W ⊓ ⨅ a, (κ a).eigenspace (σ a) = W := by
  classical
  have := Fintype.ofFinite K
  set Y : (K ≃+* K) → Submodule K V := fun σ => W ⊓ ⨅ a, (κ a).eigenspace (σ a) with hYdef
  have hmemY : ∀ σ y, y ∈ Y σ ↔ y ∈ W ∧ ∀ a, κ a y = σ a • y := by
    intro σ y
    simp [Y, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  set α : K := (g : K) with hαdef
  have hpowα : ∀ a : K, a ≠ 0 → ∃ n : ℕ, α ^ n = a := by
    intro a ha
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 a ha))
    exact ⟨n, by rw [hαdef, ← Units.val_pow_eq_pow_val, hn, Units.val_mk0]⟩
  have hzero : ∀ y ∈ W, κ 0 y = 0 := fun y hy => by
    have h := hadd 0 0 y hy
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  set A : Module.End K V := κ α with hAdef
  have hApow : ∀ n : ℕ, ∀ y ∈ W, κ (α ^ n) y = (A ^ n) y := by
    intro n
    induction n with
    | zero => intro y hy; rw [pow_zero, hone y hy, pow_zero, Module.End.one_apply]
    | succ n ih =>
      intro y hy
      rw [pow_succ', hmul _ _ y hy, ih y hy, pow_succ', Module.End.mul_apply]
  let A' : Module.End K W := A.restrict (hW α)
  have hA'apply : ∀ n (v : W), ((A' ^ n) v : V) = (A ^ n) v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, LinearMap.restrict_coe_apply, ih, pow_succ',
        Module.End.mul_apply]
  have hA'pow : A' ^ Fintype.card K = A' := by
    ext v
    rw [hA'apply, ← hApow _ _ v.2, FiniteField.pow_card]
    rfl
  have htop := iSup_eigenspace_eq_top_of_pow_card A' hA'pow
  have hpiece : ∀ c : K, (A'.eigenspace c).map W.subtype ≤ ⨆ σ, Y σ := by
    intro c
    have heig : ∀ v : W, v ∈ A'.eigenspace c → A v = c • (v : V) := fun v hv => by
      have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hv)
      simpa [A'] using h
    have hpowv : ∀ v : V, A v = c • v → ∀ n : ℕ, (A ^ n) v = c ^ n • v := by
      intro v hv n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
    let s : K → K := fun a => if h : a = 0 then 0 else c ^ Classical.choose (hpowα a h)
    have hs : ∀ v : W, v ∈ A'.eigenspace c → ∀ a, κ a v = s a • (v : V) := by
      intro v hv a
      by_cases ha : a = 0
      · subst ha
        simp [s, hzero _ v.2]
      · have hn := Classical.choose_spec (hpowα a ha)
        simp only [s, dif_neg ha]
        conv_lhs => rw [← hn]
        rw [hApow _ _ v.2]
        exact hpowv _ (heig v hv) _
    by_cases hne : ∃ v₀ : W, v₀ ∈ A'.eigenspace c ∧ v₀ ≠ 0
    · obtain ⟨v₀, hv₀, hv₀ne⟩ := hne
      have hw₀ : (v₀ : V) ≠ 0 := fun h => hv₀ne (Subtype.ext h)
      have huniq : ∀ x y : K, x • (v₀ : V) = y • (v₀ : V) → x = y :=
        fun x y h => smul_left_injective K hw₀ h
      let sHom : K →+* K :=
        { toFun := s
          map_one' := huniq _ _ (by rw [← hs v₀ hv₀, hone _ v₀.2, one_smul])
          map_mul' := fun a b => huniq _ _ (by
            rw [← hs v₀ hv₀, hmul _ _ _ v₀.2, hs v₀ hv₀ b, map_smul, hs v₀ hv₀ a, smul_smul,
              mul_comm])
          map_zero' := by simp [s]
          map_add' := fun a b => huniq _ _ (by
            rw [← hs v₀ hv₀, hadd _ _ _ v₀.2, hs v₀ hv₀ a, hs v₀ hv₀ b, add_smul]) }
      have hbij : Function.Bijective sHom :=
        ⟨sHom.injective, Finite.surjective_of_injective sHom.injective⟩
      let σ : K ≃+* K := RingEquiv.ofBijective sHom hbij
      refine le_trans ?_ (le_iSup Y σ)
      rintro _ ⟨v, hv, rfl⟩
      refine (hmemY σ v).2 ⟨v.2, fun a => ?_⟩
      rw [hs v hv a]
      rfl
    · have hbot : A'.eigenspace c = ⊥ := by
        refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
        by_contra h
        exact hne ⟨v, hv, h⟩
      rw [hbot, Submodule.map_bot]
      exact bot_le
  have hinj : Function.Injective fun σ : K ≃+* K => σ α := by
    intro σ τ h
    refine RingEquiv.ext fun a => ?_
    by_cases ha : a = 0
    · simp [ha]
    · obtain ⟨n, rfl⟩ := hpowα a ha
      simp only at h
      rw [map_pow, map_pow, h]
  refine ⟨((Module.End.eigenspaces_iSupIndep A).comp hinj).mono fun σ y hy => ?_, ?_⟩
  · exact Module.End.mem_eigenspace_iff.2 (((hmemY σ y).1 hy).2 α)
  · refine le_antisymm (iSup_le fun σ => inf_le_left) fun y hy => ?_
    have hmem : y ∈ (⨆ c, A'.eigenspace c).map W.subtype := by
      rw [htop]
      exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [Submodule.map_iSup] at hmem
    exact (iSup_le hpiece) hmem

end CFSG.RankThree.GF2n.Stroth80.KS95

end
