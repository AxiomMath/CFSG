module

public import CFSG.RankThree.PartOne.SLB4A.WeylWord

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk

section WW3

variable {τ : Tag} {K : Type} [Field K]

@[expose] def opOf (g : adjointGroup τ K) : Module.End K (RootModule τ K) :=
  (((g : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))

theorem opOf_mul (g h : adjointGroup τ K) : opOf (g * h) = opOf g * opOf h := rfl

theorem opOf_one : opOf (1 : adjointGroup τ K) = 1 := rfl

theorem opOf_pow (g : adjointGroup τ K) (n : ℕ) : opOf (g ^ n) = opOf g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, opOf_mul, ih, pow_succ]

theorem opOf_dElt (i : Fin τ.rank) (t : Kˣ) :
    opOf (dElt i t : adjointGroup τ K) = (torusElt τ K i t : Module.End K (RootModule τ K)) := rfl

def HasEig (A : Module.End K (RootModule τ K)) (v : RootModule τ K) : Prop :=
  ∃ c : K, A v = c • v

theorem HasEig.mul {A B : Module.End K (RootModule τ K)} {v : RootModule τ K} (hA : HasEig A v)
    (hB : HasEig B v) : HasEig (A * B) v := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a * b, by rw [Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]⟩

theorem HasEig.one (v : RootModule τ K) : HasEig (1 : Module.End K (RootModule τ K)) v :=
  ⟨1, by simp⟩

theorem HasEig.pow {A : Module.End K (RootModule τ K)} {v : RootModule τ K} (hA : HasEig A v)
    (n : ℕ) : HasEig (A ^ n) v := by
  induction n with
  | zero => simpa using HasEig.one v
  | succ n ih => rw [pow_succ]; exact ih.mul hA

theorem dElt_pow_hasEig (i : Fin τ.rank) (t : Kˣ) (n : ℕ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    HasEig (opOf ((dElt i t : adjointGroup τ K) ^ n)) (rootVec τ K α) := by
  rw [opOf_pow, opOf_dElt]
  exact HasEig.pow ⟨_, torusElt_rootVec i t hα⟩ n

theorem rootVec_ne_smul_rootVec {k k' : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (hk' : k' < τ.rootCertificate.roots.length) (hne : k ≠ k') (c : K) :
    rootVec τ K (τ.rootCertificate.root k) ≠ c • rootVec τ K (τ.rootCertificate.root k') := by
  intro h
  rw [rootVec_eq_single_of_isRoot (isRoot_rootCertificate_root hk),
    rootVec_eq_single_of_isRoot (isRoot_rootCertificate_root hk')] at h
  have h1 := congrArg (fun f => f (Sum.inr ⟨τ.rootCertificate.root k, isRoot_rootCertificate_root hk⟩)) h
  have hne' : (Sum.inr ⟨τ.rootCertificate.root k, isRoot_rootCertificate_root hk⟩ : Label τ) ≠
      Sum.inr ⟨τ.rootCertificate.root k', isRoot_rootCertificate_root hk'⟩ := by
    intro h2
    exact hne (rootCertificate_root_injOn hk hk' (Subtype.mk.inj (Sum.inr.inj h2)))
  simp [hne'.symm] at h1

theorem no_torus_mul_wElt (D : adjointGroup τ K) (ω : List (Fin τ.rank)) {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) (hne : (walk τ ω k).1 ≠ k)
    (hD : HasEig (opOf D) (rootVec τ K (τ.rootCertificate.root (walk τ ω k).1))) :
    D * wElt ω ≠ 1 := by
  intro h
  have h1 := prod_weylElt_rootVec_root K ω hk
  obtain ⟨c, hc⟩ := hD
  have h2 : opOf (D * wElt ω) (rootVec τ K (τ.rootCertificate.root k)) =
      rootVec τ K (τ.rootCertificate.root k) := by
    rw [h, opOf_one]
    rfl
  rw [opOf_mul, Module.End.mul_apply] at h2
  have h3 : opOf (wElt ω : adjointGroup τ K) (rootVec τ K (τ.rootCertificate.root k)) =
      ((-1 : K) ^ (walk τ ω k).2) • rootVec τ K (τ.rootCertificate.root (walk τ ω k).1) := h1
  rw [h3, map_smul, hc, smul_smul] at h2
  exact rootVec_ne_smul_rootVec hk (walk_fst_lt ω hk) (Ne.symm hne) _ h2.symm

end WW3

end CFSG.RankThree.PartOne.SLB4A
