module

public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartDefs
public import CFSG.LocalAnalysis.StandardType.GGKGWeylReflOn
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LocalAnalysis.StandardType.GGQ2HeartJRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private theorem ggQ2HeartJDictAux_symm_one (j : Fin Tag.E6.rank) : Tag.E6.symmetrizer j j = 1 :=
  Matrix.one_apply_eq j

private theorem ggQ2HeartJDictAux_iform_self {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    iform β β = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hβ
  rw [hj, ggQ2HeartJDictAux_symm_one, mul_one]

private theorem ggQ2HeartJDictAux_corootPair {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (v : Fin Tag.E6.rank → ℤ) : corootPair β v = iform β v := by
  have h := corootPair_mul hβ v
  rw [ggQ2HeartJDictAux_iform_self hβ] at h
  omega

private theorem ggQ2HeartJDictAux_symC (k l : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan k l = CartanMatrix.E 6 k l := by
  rw [symmetrizedCartan_apply, ggQ2HeartJDictAux_symm_one, one_mul]
  change Tag.cartanE 6 k l = CartanMatrix.E 6 k l
  rw [cartanE_eq]

private theorem ggQ2HeartJDictAux_iform_single (γ : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    iform γ (Pi.single i 1) = ∑ k, γ k * Tag.E6.symmetrizedCartan k i := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

private theorem ggQ2HeartJDictAux_pr_iform (γ γ' : Fin Tag.E6.rank → ℤ) :
    ∑ j, (γ' j : ZMod 3) * (iform γ (Pi.single j 1) : ZMod 3) = (iform γ γ' : ZMod 3) := by
  rw [show iform γ γ' = ∑ k, ∑ j, γ k * Tag.E6.symmetrizedCartan k j * γ' j from rfl]
  simp only [ggQ2HeartJDictAux_iform_single]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem ggQ2HeartJDictAux_excRefl {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (t : Fin Tag.E6.rank → ZMod 3) :
    ExcSplitRootGen.excRefl (p := 3) β t =
      t - (∑ j, (β j : ZMod 3) * t j) • fun i => (iform β (Pi.single i 1) : ZMod 3) := by
  funext i
  rw [ExcSplitRootGen.excRefl_apply hβ, ggQ2HeartJDictAux_corootPair hβ]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem ggQ2HeartJDictAux_iform_self_nonneg (z : Fin Tag.E6.rank → ℤ) : 0 ≤ iform z z := by
  by_cases h : z = 0
  · rw [h]; simp [iform]
  · exact (iform_self_pos h).le

private theorem ggQ2HeartJDictAux_eq_of_iform_eq_two {β γ : Fin Tag.E6.rank → ℤ}
    (hβ : iform β β = 2) (hγ : iform γ γ = 2) (h : iform β γ = 2) : β = γ := by
  by_contra hne
  have h1 := iform_self_pos (sub_ne_zero.2 hne)
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm γ β, hβ, hγ, h] at h1
  omega

private theorem ggQ2HeartJDictAux_iform_bound {β γ : Fin Tag.E6.rank → ℤ}
    (hβ : iform β β = 2) (hγ : iform γ γ = 2) : -2 ≤ iform β γ ∧ iform β γ ≤ 2 := by
  have h1 := ggQ2HeartJDictAux_iform_self_nonneg (β + γ)
  have h2 := ggQ2HeartJDictAux_iform_self_nonneg (β - γ)
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm γ β, hβ, hγ] at h1
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm γ β, hβ, hγ] at h2
  constructor <;> omega

private theorem ggQ2HeartJDictAux_C_diag : ∀ k : Fin 6, (CartanMatrix.E 6 k k : ℤ) = 2 := by
  decide

private theorem ggQ2HeartJDictAux_C_off :
    ∀ k l : Fin 6, k = l ∨ (CartanMatrix.E 6 k l : ℤ) * ((CartanMatrix.E 6 k l : ℤ) + 1) = 0 := by
  decide

private theorem ggQ2HeartJDictAux_C_rows :
    ∀ k l : Fin 6, k = l ∨ ∃ m : Fin 6,
      ((CartanMatrix.E 6 k m : ℤ) : ZMod 3) ≠ ((CartanMatrix.E 6 l m : ℤ) : ZMod 3) := by decide

private theorem ggQ2HeartJDictAux_card_fix {V : Type} [AddCommGroup V] [Finite V]
    (κ : V →+ (Fin Tag.E6.rank → ZMod 3))
    (hrange : ∀ t, t ∈ NoOffRest.hypE6 ↔ t ∈ κ.range) (hker : Nat.card κ.ker = 3)
    (α : V →+ ZMod 3) (hle : κ.ker ≤ α.ker) {h : V} (hαh : α h = 2)
    (f : (Fin Tag.E6.rank → ZMod 3) → Fin Tag.E6.rank → ZMod 3)
    (hf : ∀ v, f (κ v) = fun m => κ v m - α v * κ h m) :
    Nat.card {t : Fin Tag.E6.rank → ZMod 3 // t ∈ (NoOffRest.hypE6 : Set _) ∧ f t = t} * 3 =
      Nat.card (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) := by
  classical
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have hκh : κ h ≠ 0 := by
    intro h0
    have h1 : α h = 0 := AddMonoidHom.mem_ker.1 (hle (AddMonoidHom.mem_ker.2 h0))
    exact h20 (hαh.symm.trans h1)
  obtain ⟨m₀, hm₀⟩ : ∃ m, κ h m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hκh (funext hcon)
  have hiff : ∀ t, (t ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) ∧ f t = t) ↔
      t ∈ (κ.comp α.ker.subtype).range := by
    intro t
    rw [SetLike.mem_coe, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨ht, hft⟩
      obtain ⟨v, rfl⟩ := AddMonoidHom.mem_range.1 ((hrange t).1 ht)
      have h1 : κ v m₀ - α v * κ h m₀ = κ v m₀ := by
        have h3 := congrFun hft m₀
        rw [hf] at h3
        exact h3
      have h2 : α v * κ h m₀ = 0 := by linear_combination -h1
      exact ⟨⟨v, AddMonoidHom.mem_ker.2 ((mul_eq_zero.1 h2).resolve_right hm₀)⟩, rfl⟩
    · rintro ⟨⟨v, hv⟩, rfl⟩
      refine ⟨(hrange _).2 ⟨v, rfl⟩, ?_⟩
      change f (κ v) = κ v
      rw [hf, AddMonoidHom.mem_ker.1 hv]
      funext m
      show κ v m - 0 * κ h m = κ v m
      ring
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),
    show Nat.card (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) = 3 ^ 5 from
      NoOffRest.card_hypE6]
  have hR : Nat.card κ.range = 3 ^ 5 := by
    rw [← NoOffRest.card_hypE6]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun t => (hrange t).symm)
  have hV := AddSubgroup.card_ker_mul_card_range κ
  have hαtop : α.range = ⊤ := by
    refine AddMonoidHom.range_eq_top.2 fun c => ⟨c.val • (2 • h), ?_⟩
    rw [map_nsmul, map_nsmul, hαh, show (2 : ℕ) • (2 : ZMod 3) = 1 by decide, nsmul_eq_mul,
      mul_one, ZMod.natCast_zmod_val]
  have hα := AddSubgroup.card_ker_mul_card_range α
  rw [hαtop, AddSubgroup.card_top, Nat.card_zmod] at hα
  have hg := AddSubgroup.card_ker_mul_card_range (κ.comp α.ker.subtype)
  have hgker : Nat.card (κ.comp α.ker.subtype).ker = 3 := by
    refine Eq.trans ?_ hker
    exact Nat.card_congr
      { toFun := fun k => ⟨k.1.1, AddMonoidHom.mem_ker.2 (AddMonoidHom.mem_ker.1 k.2)⟩
        invFun := fun v => ⟨⟨v.1, hle v.2⟩, AddMonoidHom.mem_ker.2 (AddMonoidHom.mem_ker.1 v.2)⟩
        left_inv := fun k => rfl
        right_inv := fun v => rfl }
  rw [hgker] at hg
  rw [hker, hR] at hV
  have h243 : (3 : ℕ) ^ 5 = 243 := by norm_num
  rw [h243] at hV ⊢
  omega

private theorem ggQ2HeartJDictAux_node {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hx0 : M.xV ≠ 0) (κ : M.V →ₗ[ZMod 3] (Fin Tag.E6.rank → ZMod 3))
    (hker : LinearMap.ker κ = Submodule.span (ZMod 3) {M.xV})
    (hrange : ∀ t, t ∈ NoOffRest.hypE6 ↔ t ∈ LinearMap.range κ)
    (hW : ∀ φ ∈ ggAutomizer L Bs, ∃ u : WeylGroup Tag.E6, ∀ v,
      κ (ggLin (p := 3) M.model φ v) = TableBExc.E6Three.adAct Tag.E6 3 u (κ v))
    (i : M.Λ) :
    ∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧
      (∀ v, ∑ j, (β j : ZMod 3) * κ v j = M.root i v) ∧
      ∀ m, κ (M.coroot i) m = (iform β (Pi.single m 1) : ZMod 3) := by
  classical
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h30 : (3 : ZMod 3) = 0 := by decide
  have hαh : M.root i (M.coroot i) = 2 := by
    rw [M.pairing i i, M.isCartan.1 i]
    norm_num
  have hc : M.coroot i ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hαh
    exact h20 hαh.symm
  have hsi : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hαx : M.root i M.xV = 0 := by
    have hxmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [M.fixed_x]
      exact Submodule.subset_span (Set.mem_singleton M.xV)
    have h1 := (mem_ggFixedSubmodule_iff (p := 3) (ι := M.model) (N := ggAutomizer L Bs)
      (v := M.xV)).mp hxmem (M.simple i) hsi
    rw [M.simple_apply i M.xV] at h1
    exact (smul_eq_zero.mp (sub_eq_self.mp h1)).resolve_right hc
  have hle : LinearMap.ker κ ≤ LinearMap.ker (M.root i) := by
    intro v hv
    rw [hker] at hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [LinearMap.mem_ker, map_smul, hαx, smul_zero]
  have hκh : κ (M.coroot i) ≠ 0 := by
    intro h0
    have h1 : M.root i (M.coroot i) = 0 := hle (LinearMap.mem_ker.2 h0)
    exact h20 (hαh.symm.trans h1)
  have hker3 : Nat.card κ.toAddMonoidHom.ker = 3 := by
    have h1 : Nat.card (Submodule.span (ZMod 3) {M.xV}) = 3 := by
      rw [← FiniteField.pow_finrank_eq_natCard 3 (Submodule.span (ZMod 3) {M.xV}),
        finrank_span_singleton hx0, pow_one]
    refine Eq.trans ?_ h1
    rw [← hker]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      rw [AddMonoidHom.mem_ker, LinearMap.mem_ker, LinearMap.toAddMonoidHom_coe])
  obtain ⟨u, hu⟩ := hW _ hsi
  have hf : ∀ v, TableBExc.E6Three.adAct Tag.E6 3 u (κ v) =
      fun m => κ v m - M.root i v * κ (M.coroot i) m := by
    intro v
    rw [← hu, M.simple_apply, map_sub, map_smul]
    exact funext fun m => rfl
  have hsq : ∀ t ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)),
      TableBExc.E6Three.adAct Tag.E6 3 u (TableBExc.E6Three.adAct Tag.E6 3 u t) = t := by
    intro t ht
    obtain ⟨v, rfl⟩ := (hrange t).1 ht
    have e1 : TableBExc.E6Three.adAct Tag.E6 3 u (κ v) =
        κ (v - M.root i v • M.coroot i) := by
      rw [hf, map_sub, map_smul]
      exact funext fun m => rfl
    have e2 : M.root i (v - M.root i v • M.coroot i) = -(M.root i v) := by
      rw [map_sub, map_smul, hαh]
      show M.root i v - M.root i v * 2 = -(M.root i v)
      ring
    rw [e1, hf, e2]
    funext m
    show κ (v - M.root i v • M.coroot i) m - -(M.root i v) * κ (M.coroot i) m = κ v m
    rw [map_sub, map_smul]
    show κ v m - M.root i v * κ (M.coroot i) m - -(M.root i v) * κ (M.coroot i) m = κ v m
    ring
  have hfix := ggQ2HeartJDictAux_card_fix κ.toAddMonoidHom
    (fun t => (hrange t).trans (by simp only [LinearMap.mem_range, AddMonoidHom.mem_range,
      LinearMap.toAddMonoidHom_coe]))
    hker3 (M.root i).toAddMonoidHom (fun v hv => hle hv) hαh _ hf
  obtain ⟨γ, hγ, hγu⟩ := E6ThreeRootGen.exists_root_of_adAct_refl
    (V := (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3))) (Or.inr rfl) u hsq hfix
  have hS3 : ∀ v m, M.root i v * κ (M.coroot i) m =
      (∑ j, (γ j : ZMod 3) * κ v j) * (iform γ (Pi.single m 1) : ZMod 3) := by
    intro v m
    have h1 := congrFun (hγu (κ v) ((hrange _).2 ⟨v, rfl⟩)) m
    rw [hf, ExcSplitRootGen.excRefl_apply hγ, ggQ2HeartJDictAux_corootPair hγ] at h1
    linear_combination -h1
  obtain ⟨m₀, hm₀⟩ : ∃ m, κ (M.coroot i) m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hκh (funext hcon)
  obtain ⟨lam, hlam⟩ : ∃ lam : ZMod 3, lam = ∑ j, (γ j : ZMod 3) * κ (M.coroot i) j :=
    ⟨_, rfl⟩
  have hlam2 : ∀ m, 2 * κ (M.coroot i) m = lam * (iform γ (Pi.single m 1) : ZMod 3) := by
    intro m
    have h1 := hS3 (M.coroot i) m
    rw [hαh, ← hlam] at h1
    exact h1
  have hκc : ∀ m, κ (M.coroot i) m = 2 * lam * (iform γ (Pi.single m 1) : ZMod 3) := by
    intro m
    linear_combination 2 * hlam2 m - κ (M.coroot i) m * h30
  have hc0 : (iform γ (Pi.single m₀ 1) : ZMod 3) ≠ 0 := by
    intro h0
    rw [hκc, h0, mul_zero] at hm₀
    exact hm₀ rfl
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [hκc, h0, mul_zero, zero_mul] at hm₀
    exact hm₀ rfl
  have hlam12 : lam = 1 ∨ lam = 2 := by
    have key : ∀ z : ZMod 3, z ≠ 0 → z = 1 ∨ z = 2 := by decide
    exact key lam hlam0
  obtain ⟨s, hs, hs1, hs2⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (s : ZMod 3) = 2 * lam ∧
      (s : ZMod 3) * (2 * lam) = 1 := by
    rcases hlam12 with h | h
    · subst h
      exact ⟨-1, Or.inr rfl, by decide, by decide⟩
    · subst h
      exact ⟨1, Or.inl rfl, by decide, by decide⟩
  refine ⟨s • γ, ?_, ?_, ?_⟩
  · rcases hs with rfl | rfl
    · rwa [one_smul]
    · have h1 := IsRoot.smul hγ (rootReflection γ)
      rw [rootReflection_smul_self hγ] at h1
      rwa [neg_one_smul]
  · intro v
    have h1 := hS3 v m₀
    rw [hκc] at h1
    have h2 : M.root i v * (2 * lam) = ∑ j, (γ j : ZMod 3) * κ v j :=
      mul_right_cancel₀ hc0 (by rw [← h1]; ring)
    calc ∑ j, (((s • γ) j : ℤ) : ZMod 3) * κ v j
        = (s : ZMod 3) * ∑ j, (γ j : ZMod 3) * κ v j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
          ring
      _ = M.root i v := by
          rw [← h2, mul_comm (M.root i v), ← mul_assoc, hs2, one_mul]
  · intro m
    rw [hκc, ← hs1, iform_smul_left, Int.cast_mul]

theorem ggQ2HeartJ_dict {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (D : GGHeartDict M) (hx0 : M.xV ≠ 0)
    (κ : M.V →ₗ[ZMod 3] (Fin Tag.E6.rank → ZMod 3))
    (hker : LinearMap.ker κ = Submodule.span (ZMod 3) {M.xV})
    (hrange : ∀ t, t ∈ NoOffRest.hypE6 ↔ t ∈ LinearMap.range κ)
    (hW : ∀ φ ∈ ggAutomizer L Bs, ∃ u : WeylGroup Tag.E6, ∀ v,
      κ (ggLin (p := 3) M.model φ v) = TableBExc.E6Three.adAct Tag.E6 3 u (κ v)) :
    ∃ Γ : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ,
      (∀ a b, iform (Γ a) (Γ b) = iform a b) ∧
      (∀ a, IsRoot Tag.E6 a → IsRoot Tag.E6 (Γ a)) ∧
      (∀ γ, IsRoot Tag.E6 γ → ∃ a, IsRoot Tag.E6 a ∧ Γ a = γ) ∧
      (∀ a b, IsRoot Tag.E6 a → IsRoot Tag.E6 b → Γ a = Γ b → a = b) ∧
      ∀ (a : Fin Tag.E6.rank → ℤ) (v : M.V),
        ∑ j, ((Γ a j : ℤ) : ZMod 3) * κ v j = M.rootForm (fun i => a (D.e.symm i)) v := by
  classical
  have hMC : ∀ k l : Fin Tag.E6.rank, M.cartan (D.e k) (D.e l) = Tag.E6.symmetrizedCartan k l :=
    fun k l => by
      rw [ggQ2HeartJDictAux_symC]
      exact D.cartan_eq k l
  have hBd : ∀ k, Tag.E6.symmetrizedCartan k k = 2 := fun k => by
    rw [ggQ2HeartJDictAux_symC]
    exact ggQ2HeartJDictAux_C_diag k
  have hBo : ∀ k l, k = l ∨ Tag.E6.symmetrizedCartan k l = 0 ∨
      Tag.E6.symmetrizedCartan k l = -1 := fun k l => by
    rw [ggQ2HeartJDictAux_symC]
    rcases ggQ2HeartJDictAux_C_off k l with h | h
    · exact Or.inl h
    · rcases mul_eq_zero.1 h with h0 | h1
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (by omega))
  have hBr : ∀ k l, k = l ∨ ∃ m, ((Tag.E6.symmetrizedCartan k m : ℤ) : ZMod 3) ≠
      ((Tag.E6.symmetrizedCartan l m : ℤ) : ZMod 3) := fun k l => by
    simp only [ggQ2HeartJDictAux_symC]
    exact ggQ2HeartJDictAux_C_rows k l
  choose β hβ hβv hβc using fun k : Fin Tag.E6.rank =>
    ggQ2HeartJDictAux_node M hx0 κ hker hrange hW (D.e k)
  have hβ2 : ∀ k, iform (β k) (β k) = 2 := fun k => ggQ2HeartJDictAux_iform_self (hβ k)
  have hmod : ∀ k l,
      ((iform (β k) (β l) : ℤ) : ZMod 3) = ((Tag.E6.symmetrizedCartan k l : ℤ) : ZMod 3) := by
    intro k l
    have h1 := hβv k (M.coroot (D.e l))
    simp only [hβc l] at h1
    rw [ggQ2HeartJDictAux_pr_iform, M.pairing, hMC, iform_comm] at h1
    exact h1
  have hiso : ∀ k l, iform (β k) (β l) = Tag.E6.symmetrizedCartan k l := by
    intro k l
    rcases hBo k l with hkl | h0 | h1
    · subst hkl
      rw [hβ2, hBd]
    · have hb := ggQ2HeartJDictAux_iform_bound (hβ2 k) (hβ2 l)
      have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).1 (hmod k l).symm
      rw [h0] at hd ⊢
      push_cast at hd
      omega
    · have hb := ggQ2HeartJDictAux_iform_bound (hβ2 k) (hβ2 l)
      have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).1 (hmod k l).symm
      rw [h1] at hd ⊢
      push_cast at hd
      have h2 : iform (β k) (β l) ≠ 2 := by
        intro h2
        have heq := ggQ2HeartJDictAux_eq_of_iform_eq_two (hβ2 k) (hβ2 l) h2
        rcases hBr k l with hkl | ⟨m, hm⟩
        · subst hkl
          rw [hBd] at h1
          omega
        · apply hm
          have e1 := hβv k (M.coroot (D.e m))
          have e2 := hβv l (M.coroot (D.e m))
          rw [heq, e2, M.pairing, M.pairing, hMC, hMC] at e1
          exact e1.symm
      omega
  let Γ : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ := fun a => ∑ k, a k • β k
  have hΓsingle : ∀ j, Γ (Pi.single j 1) = β j := by
    intro j
    show ∑ k, (Pi.single j (1 : ℤ) : Fin Tag.E6.rank → ℤ) k • β k = β j
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
      (by simp), Pi.single_eq_same, one_smul]
  have hΓsub : ∀ a b, Γ (a - b) = Γ a - Γ b := by
    intro a b
    simp only [Γ, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have hΓsmul : ∀ (c : ℤ) a, Γ (c • a) = c • Γ a := by
    intro c a
    simp only [Γ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hΓiso : ∀ a b, iform (Γ a) (Γ b) = iform a b := by
    intro a b
    simp only [Γ]
    rw [iform_finset_sum_left]
    simp only [iform_smul_left, iform_finset_sum_right, iform_smul_right, hiso]
    rw [show iform a b = ∑ k, ∑ l, a k * Tag.E6.symmetrizedCartan k l * b l from rfl]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hΓroot : ∀ a, IsRoot Tag.E6 a → IsRoot Tag.E6 (Γ a) := by
    intro a ha
    induction ha with
    | basis j =>
        rw [hΓsingle]
        exact hβ j
    | @reflect i v hv ih =>
        have h1 : Γ (reflect Tag.E6 i v) = rootReflection (β i) • Γ v := by
          rw [rootReflection_smul (hβ i), ggQ2HeartJDictAux_corootPair (hβ i), ← hΓsingle i,
            hΓiso, iform_single_left, ggQ2HeartJDictAux_symm_one, one_mul]
          change Γ (v - (∑ j, Tag.E6.cartan i j * v j) • Pi.single i 1) = _
          rw [hΓsub, hΓsmul]
        rw [h1]
        exact IsRoot.smul ih _
  have hΓinj : ∀ a b, IsRoot Tag.E6 a → IsRoot Tag.E6 b → Γ a = Γ b → a = b := by
    intro a b ha hb hab
    have h1 := hΓiso a b
    rw [hab, hΓiso, ggQ2HeartJDictAux_iform_self hb] at h1
    exact ggQ2HeartJDictAux_eq_of_iform_eq_two (ggQ2HeartJDictAux_iform_self ha)
      (ggQ2HeartJDictAux_iform_self hb) h1.symm
  have hΓsurj : ∀ γ, IsRoot Tag.E6 γ → ∃ a, IsRoot Tag.E6 a ∧ Γ a = γ := by
    intro γ hγ
    have hsub : (rootFinset Tag.E6).image Γ ⊆ rootFinset Tag.E6 := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hz
      exact mem_rootFinset.2 (hΓroot a (mem_rootFinset.1 ha))
    have hcard : ((rootFinset Tag.E6).image Γ).card = (rootFinset Tag.E6).card :=
      Finset.card_image_of_injOn fun a ha b hb hab =>
        hΓinj a b (mem_rootFinset.1 ha) (mem_rootFinset.1 hb) hab
    have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
    have hγm : γ ∈ (rootFinset Tag.E6).image Γ := by
      rw [heq]
      exact mem_rootFinset.2 hγ
    obtain ⟨a, ha, hΓa⟩ := Finset.mem_image.1 hγm
    exact ⟨a, mem_rootFinset.1 ha, hΓa⟩
  refine ⟨Γ, hΓiso, hΓroot, hΓsurj, hΓinj, fun a v => ?_⟩
  have h1 : ∑ j, ((Γ a j : ℤ) : ZMod 3) * κ v j =
      ∑ k, (a k : ZMod 3) * ∑ j, (β k j : ZMod 3) * κ v j := by
    simp only [Γ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1]
  simp only [hβv, GGQ2LDatum.rootForm, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Fintype.sum_equiv (D.e : Fin Tag.E6.rank ≃ M.Λ) _ _ fun k => by
    simp only [Equiv.symm_apply_apply]

theorem ggQ2HeartJ_rootMap {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (D : GGHeartDict M) (hx0 : M.xV ≠ 0)
    (κ : M.V →ₗ[ZMod 3] (Fin Tag.E6.rank → ZMod 3))
    (hker : LinearMap.ker κ = Submodule.span (ZMod 3) {M.xV})
    (hrange : ∀ t, t ∈ NoOffRest.hypE6 ↔ t ∈ LinearMap.range κ)
    (hW : ∀ φ ∈ ggAutomizer L Bs, ∃ u : WeylGroup Tag.E6, ∀ v,
      κ (ggLin (p := 3) M.model φ v) = TableBExc.E6Three.adAct Tag.E6 3 u (κ v)) :
    ∃ Φ : (M.Λ → ℤ) → Fin Tag.E6.rank → ℤ,
      (∀ a, CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a → IsRoot Tag.E6 (Φ a)) ∧
      (∀ γ, IsRoot Tag.E6 γ →
        ∃ a, CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ∧ Φ a = γ) ∧
      (∀ a b, CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a →
        CFSG.ClassicalInvolution.RouteD.RRoot M.cartan b → Φ a = Φ b → a = b) ∧
      (∀ a b, ∑ i, ∑ j, a i * M.cartan i j * b j = iform (Φ a) (Φ b)) ∧
      ∀ a v, M.rootForm a v = ∑ j, ((Φ a j : ℤ) : ZMod 3) * κ v j := by
  classical
  obtain ⟨Γ, hΓiso, hΓroot, hΓsurj, hΓinj, hΓform⟩ := ggQ2HeartJ_dict M D hx0 κ hker hrange hW
  have hrr : ∀ a : M.Λ → ℤ, CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ↔
      IsRoot Tag.E6 (fun k : Fin 6 => a (D.e k)) := by
    intro a
    refine Iff.trans ?_ (QTwoHeartJ.rroot_E6_iff_isRoot (v := fun k => a (D.e k)))
    constructor
    · intro ha
      exact CFSG.ClassicalInvolution.RouteD.RRoot.comp_equiv D.e
        (fun i j => (D.cartan_eq i j).symm) ha
    · intro ha
      have h3 := CFSG.ClassicalInvolution.RouteD.RRoot.comp_equiv D.e.symm
        (fun i j => by simpa using D.cartan_eq (D.e.symm i) (D.e.symm j)) ha
      simpa [Function.comp_def] using h3
  have hMC : ∀ k l : Fin Tag.E6.rank,
      Tag.E6.symmetrizedCartan k l = M.cartan (D.e k) (D.e l) := fun k l => by
    rw [ggQ2HeartJDictAux_symC]
    exact (D.cartan_eq k l).symm
  refine ⟨fun a => Γ (fun k : Fin 6 => a (D.e k)), fun a ha => hΓroot _ ((hrr a).1 ha),
    fun γ hγ => ?_, fun a b ha hb hab => ?_, fun a b => ?_, fun a v => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := hΓsurj γ hγ
    refine ⟨fun l => c (D.e.symm l), (hrr _).2 ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]
      exact hc
    · simp only [Equiv.symm_apply_apply]
  · have h1 := hΓinj _ _ ((hrr a).1 ha) ((hrr b).1 hb) hab
    funext l
    have h2 := congrFun h1 (D.e.symm l)
    simp only [Equiv.apply_symm_apply] at h2
    exact h2
  · beta_reduce
    rw [hΓiso (fun k : Fin 6 => a (D.e k)) (fun k : Fin 6 => b (D.e k))]
    refine Eq.trans ?_ (show (∑ k, ∑ l, a (D.e k) * Tag.E6.symmetrizedCartan k l * b (D.e l) : ℤ) =
      iform (τ := Tag.E6) (fun k : Fin 6 => a (D.e k)) (fun k : Fin 6 => b (D.e k)) from rfl)
    refine (Fintype.sum_equiv (D.e : Fin Tag.E6.rank ≃ M.Λ) _ _ fun k => ?_).symm
    exact Fintype.sum_equiv (D.e : Fin Tag.E6.rank ≃ M.Λ) _ _ fun l =>
      congrArg (fun z => a (D.e k) * z * b (D.e l)) (hMC k l)
  · beta_reduce
    rw [hΓform (fun k : Fin 6 => a (D.e k)) v]
    simp only [Equiv.apply_symm_apply]

end CFSG.StandardType

end
