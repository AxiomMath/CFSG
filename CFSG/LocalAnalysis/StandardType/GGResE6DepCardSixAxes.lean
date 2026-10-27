module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixDefs
public import CFSG.LocalAnalysis.StandardType.GGK2E6E6OriginalSpanTwo
public import CFSG.LocalAnalysis.StandardType.GGE6DepNbrFacts
public import CFSG.LocalAnalysis.StandardType.GGDepAConfig

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem cs6_axes_facts
    {G : Type} [Group G] [Finite G] {B Bs L D J K : Subgroup G} {x y : G} [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K) (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    {Λ : Type} {S : Finset Λ} {Λa : Type}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ∉ S} ⊕ Λa) ({i : Λ // i ∉ S} ⊕ Λa) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V}
    {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hCLL : GGIntCartan ML CL) (hCKK : GGIntCartan MK CK)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpairL : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hpairK : ∀ o o' : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod 3))
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a))) :
    ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ≠ 0 ∧
      (∀ i : Λ, α (Sum.inl i) (ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) = 0) ∧
      (∀ o : {i : Λ // i ∉ S} ⊕ Λa,
        α (o.map Subtype.val id) (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) = 0) ∧
      (∀ c : ZMod 3, ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ≠ c • ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) := by
  classical
  have hx' : ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨x, hxBs⟩ : ↥Bs) = 1 := congrArg Additive.toMul h1
    exact l05nDD1_x_ne_one hH (congrArg (fun z : ↥Bs => (z : G)) h2)
  have hxker : ∀ i : Λ, α (Sum.inl i) (ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) = 0 := by
    let φ' : Option Λ → MulAut ↥Bs := fun o => match o with
      | none => 1
      | some i => φ (Sum.inl i)
    let h' : Option Λ → V := fun o => match o with
      | none => 0
      | some i => h (Sum.inl i)
    let α' : Option Λ → Module.Dual (ZMod 3) V := fun o => match o with
      | none => 0
      | some i => α (Sum.inl i)
    have hφ' : ∀ o w, ggLin (p := 3) ι (φ' o) w = w - α' o w • h' o := by
      intro o w
      cases o with
      | none => simp [φ', h', α']
      | some i => simpa [φ', h', α'] using hlin (Sum.inl i) w
    have hL' : ∀ i j : Λ, α' (some i) (h' (some j)) = (CL i j : ZMod 3) := by
      intro i j
      simpa [φ', h', α'] using hpairL i j
    have hAL' : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)) := by
      simpa [φ'] using hclosL
    intro i
    exact l05nDD1_alpha_x (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hH hxBs hφ' hL' hCLL hAL' i
  have hyker : ∀ o : {i : Λ // i ∉ S} ⊕ Λa,
      α (o.map Subtype.val id) (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) = 0 := by
    refine GGResHyp.K_simple_roots_kill_y hH ι hyBs
      (fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id))
      (fun o : {i : Λ // i ∉ S} ⊕ Λa => h (o.map Subtype.val id))
      (fun o : {i : Λ // i ∉ S} ⊕ Λa => α (o.map Subtype.val id)) ?_ ?_ ?_
    · intro o
      rw [hclosK]
      rcases o with ⟨i, hi⟩ | a
      · exact Subgroup.subset_closure (Or.inl ⟨⟨i, hi⟩, rfl⟩)
      · exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
    · intro o
      rw [hpairK o o, hCKK.1 o]
      norm_num
    · intro o w
      exact hlin (o.map Subtype.val id) w
  have hy_not : ∀ c : ZMod 3,
      ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ≠ c • ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by
    obtain ⟨_, hy_nzp, -, -⟩ := ggE6Dep_nbr_facts hH.1 hH.2.2.2.2.1
    intro c hc
    apply hy_nzp
    have hpow : (⟨y, hyBs⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs) ^ c.val := by
      apply Additive.ofMul.injective
      apply ι.injective
      have h1 : ι (Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ c.val)) =
          c • ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by
        rw [ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3) c.val,
          ZMod.natCast_zmod_val]
      exact hc.trans h1.symm
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(c.val : ℤ), ?_⟩
    rw [zpow_natCast]
    simpa using (congrArg Subtype.val hpow).symm
  exact ⟨hx', hxker, hyker, hy_not⟩

end CFSG.StandardType
