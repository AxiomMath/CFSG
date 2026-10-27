module

public import CFSG.LocalAnalysis.StandardType.GGLatFixedRoot
import CFSG.LocalAnalysis.StandardType.GGLatPermExc

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section FixedRoot

@[expose] def GGLatFixedRootExc : Prop :=
  ∀ (τ : StatedLieTag) (f : ℕ), GGExcFive τ →
    ∀ (S : Matrix (Fin (ggU (absTag τ) 6 f).D.rank) (Fin (ggU (absTag τ) 6 f).D.rank) ℤ)
      (π : Equiv.Perm (Fin (ggU (absTag τ) 6 f).D.rank)),
      IsRootGram (ggU (absTag τ) 6 f).D S → IsDiagAut (ggU (absTag τ) 6 f).D π →
      (τ = .F4 ∨ τ = .E7 ∨ τ = .E8 → π = 1) →
      ∀ (p : ℕ) (g : Fin (ggU (absTag τ) 6 f).D.rank → ZMod p), (∀ i, g (π i) = g i) →
        ∀ O, IsCompOrbit S π (latPhi (ggU (absTag τ) 6 f).D.roots p g) O →
          IsSingleComp S (latPhi (ggU (absTag τ) 6 f).D.roots p g) O →
          ∃ γ ∈ O, γ ∈ (ggU (absTag τ) 6 f).D.roots ∧ latPerm π γ = γ

private lemma latChar_add {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (α β : Fin N → ℤ) :
    latChar p f (α + β) = latChar p f α + latChar p f β := by
  simp only [latChar, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

private lemma latChar_neg {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (α : Fin N → ℤ) :
    latChar p f (-α) = -latChar p f α := by
  simp only [latChar, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

private lemma latChar_sub {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (α β : Fin N → ℤ) :
    latChar p f (α - β) = latChar p f α - latChar p f β := by
  rw [sub_eq_add_neg, latChar_add, latChar_neg, sub_eq_add_neg]

private lemma latChar_smul {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (c : ℤ) (α : Fin N → ℤ) :
    latChar p f (c • α) = (c : ZMod p) * latChar p f α := by
  simp only [latChar, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma latPerm_latChar {N : ℕ} (p : ℕ) (g : Fin N → ZMod p) (π : Equiv.Perm (Fin N))
    (hg : ∀ i, g (π i) = g i) (α : Fin N → ℤ) :
    latChar p g (latPerm π α) = latChar p g α := by
  have h1 : (∑ i, (α (π.symm i) : ZMod p) * g i)
      = ∑ j, (α j : ZMod p) * g (π j) := by
    rw [← Equiv.sum_comp π.symm (fun j => (α j : ZMod p) * g (π j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Equiv.apply_symm_apply]
  have h2 : (∑ j, (α j : ZMod p) * g (π j)) = ∑ j, (α j : ZMod p) * g j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg j]
  simp only [latChar, latPerm]
  rw [h1, h2]

private lemma latPerm_mem_latPhi {N : ℕ} {R : Set (Fin N → ℤ)} (p : ℕ) (g : Fin N → ZMod p)
    (π : Equiv.Perm (Fin N)) (hg : ∀ i, g (π i) = g i)
    (hroots : ∀ β ∈ R, latPerm π β ∈ R) {β : Fin N → ℤ}
    (hβ : β ∈ latPhi R p g) : latPerm π β ∈ latPhi R p g :=
  ⟨hroots β hβ.1, by rw [latPerm_latChar p g π hg β, hβ.2]⟩

private lemma latLinked_iff_mem {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {Φ : Set (Fin N → ℤ)}
    {α β : Fin N → ℤ} (h : latLinked S Φ α β) : (α ∈ Φ ↔ β ∈ Φ) := by
  letI : IsEquiv (Fin N → ℤ) (fun x y => x ∈ Φ ↔ y ∈ Φ) :=
    { refl := fun x => Iff.rfl
      symm := fun _ _ h => h.symm
      trans := fun _ _ _ h1 h2 => h1.trans h2 }
  exact Relation.EqvGen.eqvGen_le
    (r := fun x y : Fin N → ℤ => x ∈ Φ ∧ y ∈ Φ ∧ latGram S x y ≠ 0)
    (r' := fun x y : Fin N → ℤ => x ∈ Φ ↔ y ∈ Φ)
    (fun x y hxy => ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩) α β h

private lemma iterate_latPerm_mem {N : ℕ} {Φ : Set (Fin N → ℤ)} {π : Equiv.Perm (Fin N)}
    (hΦperm : ∀ β ∈ Φ, latPerm π β ∈ Φ) {α : Fin N → ℤ} (hα : α ∈ Φ) (k : ℕ) :
    (latPerm π)^[k] α ∈ Φ := by
  induction k with
  | zero => simpa using hα
  | succ k ih => rw [Function.iterate_succ_apply']; exact hΦperm _ ih

private lemma latPerm_latLinked {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {Φ : Set (Fin N → ℤ)}
    {π : Equiv.Perm (Fin N)} (hΦperm : ∀ β ∈ Φ, latPerm π β ∈ Φ)
    (hgram : ∀ x y, latGram S (latPerm π x) (latPerm π y) = latGram S x y)
    {a b : Fin N → ℤ} (h : latLinked S Φ a b) :
    latLinked S Φ (latPerm π a) (latPerm π b) := by
  let r : (Fin N → ℤ) → (Fin N → ℤ) → Prop :=
    fun x y => x ∈ Φ ∧ y ∈ Φ ∧ latGram S x y ≠ 0
  change Relation.EqvGen r a b at h
  change Relation.EqvGen r (latPerm π a) (latPerm π b)
  induction h with
  | rel x y hxy =>
    exact Relation.EqvGen.rel _ _ ⟨hΦperm x hxy.1, hΦperm y hxy.2.1,
      fun hz => hxy.2.2 (by rw [hgram x y] at hz; exact hz)⟩
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private lemma single_comp_base {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {Φ O : Set (Fin N → ℤ)}
    {π : Equiv.Perm (Fin N)}
    (hΦperm : ∀ β ∈ Φ, latPerm π β ∈ Φ)
    (hlink : ∀ a b, latLinked S Φ a b → latLinked S Φ (latPerm π a) (latPerm π b))
    (hOrb : IsCompOrbit S π Φ O) (hsingle : IsSingleComp S Φ O) :
    (∃ α ∈ Φ, O = {β | latLinked S Φ α β}) ∧ (∀ γ ∈ O, latPerm π γ ∈ O) := by
  obtain ⟨α, hαΦ, hOeq⟩ := hOrb
  obtain ⟨α₀, hα₀O, hα₀link⟩ := hsingle
  have hα₀O' : α₀ ∈ {β | ∃ k, latLinked S Φ ((latPerm π)^[k] α) β} := hOeq ▸ hα₀O
  have hα₀Φ : α₀ ∈ Φ := by
    obtain ⟨k, hk⟩ := hα₀O'
    exact (latLinked_iff_mem hk).mp (iterate_latPerm_mem hΦperm hαΦ k)
  refine ⟨⟨α₀, hα₀Φ, ?_⟩, ?_⟩
  · ext β
    constructor
    · intro hβ; exact hα₀link β hβ
    · intro hβ
      rw [hOeq]
      obtain ⟨k₀, hk₀⟩ := hα₀O'
      exact ⟨k₀, Relation.EqvGen.trans _ _ _ hk₀ hβ⟩
  · intro γ hγO
    rw [hOeq]
    have hγ : γ ∈ {β | ∃ k, latLinked S Φ ((latPerm π)^[k] α) β} := hOeq ▸ hγO
    obtain ⟨k, hk⟩ := hγ
    exact ⟨k + 1, by rw [Function.iterate_succ_apply']; exact hlink _ _ hk⟩

private lemma exists_fixed_root_of_pi_one {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ}
    {Φ O : Set (Fin N → ℤ)} {π : Equiv.Perm (Fin N)} (hπ1 : π = 1)
    (hOrb : IsCompOrbit S π Φ O) :
    ∃ γ ∈ O, γ ∈ Φ ∧ latPerm π γ = γ := by
  obtain ⟨α, hαΦ, hOeq⟩ := hOrb
  refine ⟨α, ?_, hαΦ, ?_⟩
  · rw [hOeq]
    exact ⟨0, by rw [Function.iterate_zero_apply]; exact Relation.EqvGen.refl _⟩
  · subst hπ1
    ext i
    rfl

private def e6RootVec : List (Fin Tag.E6.rank → ℤ) :=
  (List.range Tag.E6.rootCertificate.roots.length).map Tag.E6.rootCertificate.root

private def e6SelfChk : Bool :=
  e6RootVec.all (fun α => decide (latGram (Tag.cartan .E6) α α = 2))

private def e6ReflChk : Bool :=
  e6RootVec.all (fun α =>
    e6RootVec.all (fun β =>
      decide (β - latGram (Tag.cartan .E6) α β • α ∈ e6RootVec)))

private lemma e6SelfChk_eq : e6SelfChk = true := by decide +kernel

private lemma e6ReflChk_eq : e6ReflChk = true := by decide +kernel

private lemma rootFinset_E6_eq : rootFinset Tag.E6 = e6RootVec.toFinset := rfl

private lemma mem_e6RootVec_iff_rootFinset {α : Fin Tag.E6.rank → ℤ} :
    α ∈ e6RootVec ↔ α ∈ rootFinset Tag.E6 := by
  rw [rootFinset_E6_eq, List.mem_toFinset]

private lemma mem_e6RootVec_iff_isRoot {α : Fin Tag.E6.rank → ℤ} :
    α ∈ e6RootVec ↔ IsRoot .E6 α := by
  rw [mem_e6RootVec_iff_rootFinset, mem_rootFinset]

private lemma e6_latGram_self {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ e6RootVec) :
    latGram (Tag.cartan .E6) α α = 2 := by
  have h := e6SelfChk_eq
  rw [e6SelfChk, List.all_eq_true] at h
  exact of_decide_eq_true (h α hα)

private lemma e6_refl_mem {α β : Fin Tag.E6.rank → ℤ} (hα : α ∈ e6RootVec)
    (hβ : β ∈ e6RootVec) : β - latGram (Tag.cartan .E6) α β • α ∈ e6RootVec := by
  have h := e6ReflChk_eq
  rw [e6ReflChk, List.all_eq_true] at h
  exact of_decide_eq_true ((List.all_eq_true.mp (h α hα)) β hβ)

private lemma e6_refl_isRoot {α β : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) :
    IsRoot .E6 (β - latGram (Tag.cartan .E6) α β • α) :=
  (mem_e6RootVec_iff_isRoot).mp
    (e6_refl_mem ((mem_e6RootVec_iff_isRoot).mpr hα) ((mem_e6RootVec_iff_isRoot).mpr hβ))

private lemma latGram_smul_mat {N : ℕ} (c : ℤ) (T : Matrix (Fin N) (Fin N) ℤ)
    (α β : Fin N → ℤ) : latGram (c • T) α β = c * latGram T α β := by
  simp only [latGram, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma latRefl_E6_eq {f : ℕ}
    (S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E6 6 f).D S)
    {α β : Fin (ggU .E6 6 f).D.rank → ℤ}
    (hα : α ∈ (ggU .E6 6 f).D.roots) :
    latRefl S α β = β - latGram (Tag.cartan .E6) α β • α := by
  obtain ⟨k, hk, hSeq⟩ := isRootGram_E6 6 f S hS
  let A : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ :=
    (Tag.cartan .E6 : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ)
  have hsym : (Tag.symmetrizedCartan .E6 :
        Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ) = A := by
    rw [Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]
  have hS' : S = (k : ℤ) • A := by
    rw [hSeq, hsym]
    rfl
  have hIα : IsRoot .E6 α := (mem_rootFinset (τ := .E6)).mp ((mem_roots_E6 6 f α).mp hα)
  have hαvec : α ∈ e6RootVec := (mem_e6RootVec_iff_isRoot).mpr hIα
  have hαself : latGram A α α = 2 := e6_latGram_self hαvec
  have hgram : latGram S α β = (k : ℤ) * latGram A α β := by
    rw [hS', latGram_smul_mat]
  have hself : latGram S α α = 2 * (k : ℤ) := by
    rw [hS', latGram_smul_mat, hαself]
    ring
  have hcoef : 2 * latGram S α β / latGram S α α = latGram (Tag.cartan .E6) α β := by
    rw [hgram, hself]
    rw [show 2 * ((k : ℤ) * latGram A α β)
          = (2 * (k : ℤ)) * latGram A α β by ring]
    exact Int.mul_ediv_cancel_left _ (by omega)
  rw [latRefl, hcoef]

private lemma refl_mem_latPhi_E6 (f : ℕ)
    (S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E6 6 f).D S)
    (p : ℕ) (g : Fin (ggU .E6 6 f).D.rank → ZMod p)
    {α β : Fin (ggU .E6 6 f).D.rank → ℤ}
    (hα : α ∈ latPhi (ggU .E6 6 f).D.roots p g)
    (hβ : β ∈ latPhi (ggU .E6 6 f).D.roots p g) :
    latRefl S α β ∈ latPhi (ggU .E6 6 f).D.roots p g := by
  have hIα : IsRoot .E6 α := (mem_rootFinset (τ := .E6)).mp ((mem_roots_E6 6 f α).mp hα.1)
  have hIβ : IsRoot .E6 β := (mem_rootFinset (τ := .E6)).mp ((mem_roots_E6 6 f β).mp hβ.1)
  have hrefl_eq := latRefl_E6_eq (α := α) (β := β) S hS hα.1
  refine ⟨?_, ?_⟩
  · rw [hrefl_eq]
    exact (mem_roots_E6 6 f _).mpr
      ((mem_rootFinset (τ := .E6)).mpr (e6_refl_isRoot hIα hIβ))
  · rw [hrefl_eq, latChar_sub, latChar_smul, hβ.2, hα.2]
    simp

private lemma fixed_root_E6_case (f : ℕ)
    (S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E6 6 f).D S)
    (π : Equiv.Perm (Fin (ggU .E6 6 f).D.rank)) (hπ : IsDiagAut (ggU .E6 6 f).D π)
    (p : ℕ) (g : Fin (ggU .E6 6 f).D.rank → ZMod p) (hg : ∀ i, g (π i) = g i)
    (O : Set (Fin (ggU .E6 6 f).D.rank → ℤ))
    (hOrb : IsCompOrbit S π (latPhi (ggU .E6 6 f).D.roots p g) O)
    (hsingle : IsSingleComp S (latPhi (ggU .E6 6 f).D.roots p g) O) :
    ∃ γ ∈ O, γ ∈ (ggU .E6 6 f).D.roots ∧ latPerm π γ = γ := by
  let Φ : Set (Fin (ggU .E6 6 f).D.rank → ℤ) := latPhi (ggU .E6 6 f).D.roots p g
  have hτE6 : GGExcFive .E6 := by unfold GGExcFive; exact Or.inr (Or.inl rfl)
  have hΦperm : ∀ β ∈ Φ, latPerm π β ∈ Φ :=
    fun β hβ => latPerm_mem_latPhi p g π hg
      (fun γ hγ => latPerm_mem_roots_exc .E6 f hτE6 π hπ hγ) hβ
  have hlink : ∀ a b, latLinked S Φ a b → latLinked S Φ (latPerm π a) (latPerm π b) :=
    fun a b h => latPerm_latLinked hΦperm
      (fun x y => latGram_latPerm_exc .E6 f hτE6 S hS π hπ x y) h
  obtain ⟨hO, hstab⟩ := single_comp_base hΦperm hlink hOrb hsingle
  obtain ⟨γ, hγO, hγfix⟩ :=
    exists_fixed_root_of_stable_component_E6 (Φ := Φ) (O := O) 6 f S hS π hπ
      (fun α hα => hα.1)
      (fun α hα β hβ => refl_mem_latPhi_E6 f S hS p g hα hβ)
      (fun α hα β hβ hab => ⟨hab, by
        have h := latChar_add p g α β
        rw [h, hα.2, hβ.2]; simp⟩)
      hO hstab
  obtain ⟨α₀, hα₀Φ, hOeq⟩ := hO
  have hγΦ : γ ∈ Φ := (latLinked_iff_mem (hOeq ▸ hγO)).mp hα₀Φ
  exact ⟨γ, hγO, hγΦ.1, hγfix⟩

theorem ggLatFixedRootExc_holds : GGLatFixedRootExc := by
  intro τ f hτ
  unfold GGExcFive at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · intro S π hS hπ hπ1 p g hg O hOrb hsingle
    have hpi : π = 1 := hπ1 (Or.inl rfl)
    obtain ⟨γ, hγO, hγΦ, hγfix⟩ := exists_fixed_root_of_pi_one hpi hOrb
    exact ⟨γ, hγO, hγΦ.1, hγfix⟩
  · intro S π hS hπ hπ1 p g hg O hOrb hsingle
    exact fixed_root_E6_case f S hS π hπ p g hg O hOrb hsingle
  · intro S π hS hπ hπ1 p g hg O hOrb hsingle
    have hpi : π = 1 := hπ1 (Or.inr (Or.inl rfl))
    obtain ⟨γ, hγO, hγΦ, hγfix⟩ := exists_fixed_root_of_pi_one hpi hOrb
    exact ⟨γ, hγO, hγΦ.1, hγfix⟩
  · intro S π hS hπ hπ1 p g hg O hOrb hsingle
    have hpi : π = 1 := hπ1 (Or.inr (Or.inr rfl))
    obtain ⟨γ, hγO, hγΦ, hγfix⟩ := exists_fixed_root_of_pi_one hpi hOrb
    exact ⟨γ, hγO, hγΦ.1, hγfix⟩
  · intro S π hS hπ hπ1 p g hg O hOrb hsingle
    exact fixed_root_E6_case f S hS π hπ p g hg O hOrb hsingle

end FixedRoot

end CFSG.StandardType
