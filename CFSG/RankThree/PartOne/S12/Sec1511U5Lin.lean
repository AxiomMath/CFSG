module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

namespace U5L

open Module Module.End Polynomial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def IsCE {ι : Type*} (f : ι → End K V) (v : V) : Prop :=
  v ≠ 0 ∧ ∀ i, ∃ μ : K, f i v = μ • v

open _root_.Classical in
@[expose] noncomputable def chr {ι : Type*} (f : ι → End K V) (v : V) : ι → K :=
  fun i => if h : ∃ μ : K, f i v = μ • v then h.choose else 0

theorem chr_spec {ι : Type*} {f : ι → End K V} {v : V} (hv : IsCE f v) (i : ι) :
    f i v = chr f v i • v := by
  have h := hv.2 i
  have hc : chr f v i = h.choose := by simp [chr, h]
  rw [hc]
  exact h.choose_spec

theorem chr_eq_of_eq {ι : Type*} {f : ι → End K V} {v : V} (hv : IsCE f v) {i : ι} {μ : K}
    (h : f i v = μ • v) : chr f v i = μ := by
  have h1 := chr_spec hv i
  rw [h] at h1
  exact (smul_left_injective K hv.1 h1).symm

theorem isCE_smul {ι : Type*} {f : ι → End K V} {v : V} (hv : IsCE f v) {c : K} (hc : c ≠ 0) :
    IsCE f (c • v) := by
  refine ⟨smul_ne_zero hc hv.1, fun i => ⟨chr f v i, ?_⟩⟩
  rw [map_smul, chr_spec hv i, smul_comm]

theorem chr_smul {ι : Type*} {f : ι → End K V} {v : V} (hv : IsCE f v) {c : K} (hc : c ≠ 0) :
    chr f (c • v) = chr f v := by
  funext i
  exact chr_eq_of_eq (isCE_smul hv hc) (by rw [map_smul, chr_spec hv i, smul_comm])

section Five

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {ι : Type*} (f : ι → End K V)

include hζ in
theorem iSupIndep_joint (hcomm : ∀ i j, Commute (f i) (f j)) (hpow : ∀ i, f i ^ 5 = 1) :
    iSupIndep fun χ : ι → K => ⨅ i, (f i).eigenspace (χ i) := by
  have hss := fun i => isSemisimple_of_pow_eq_one hζ (hpow i)
  have hW : ∀ (χ : ι → K) (i : ι), (f i).maxGenEigenspace (χ i) = (f i).eigenspace (χ i) :=
    fun χ i => (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace _
  have hind : iSupIndep fun χ : ι → K => ⨅ i, (f i).maxGenEigenspace (χ i) :=
    independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      fun i j φ => mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have : (fun χ : ι → K => ⨅ i, (f i).maxGenEigenspace (χ i)) =
      fun χ : ι → K => ⨅ i, (f i).eigenspace (χ i) :=
    funext fun χ => iInf_congr fun i => hW χ i
  rwa [this] at hind

include hζ in
theorem ce_linearIndependent (hcomm : ∀ i j, Commute (f i) (f j)) (hpow : ∀ i, f i ^ 5 = 1)
    {κ : Type*} (u : κ → V) (hu : ∀ k, IsCE f (u k))
    (hinj : ∀ j k, chr f (u j) = chr f (u k) → j = k) : LinearIndependent K u := by
  have hind := iSupIndep_joint hζ f hcomm hpow
  have hinj' : Function.Injective fun k => chr f (u k) := fun j k h => hinj j k h
  refine iSupIndep.linearIndependent _ (hind.comp hinj') (v := u) (fun k => ?_)
    fun k => (hu k).1
  show u k ∈ ⨅ i, (f i).eigenspace (chr f (u k) i)
  rw [Submodule.mem_iInf]
  exact fun i => mem_eigenspace_iff.2 (chr_spec (hu k) i)

include hζ in
theorem exists_ce_mem [Finite ι] [FiniteDimensional K V] (hcomm : ∀ i j, Commute (f i) (f j))
    (hpow : ∀ i, f i ^ 5 = 1) (W : Submodule K V) (hW : ∀ i, ∀ w ∈ W, f i w ∈ W)
    (hne : W ≠ ⊥) : ∃ w ∈ W, IsCE f w := by
  classical
  let g : ι → End K W := fun i => (f i).restrict (hW i)
  have hgcomm : ∀ i j, Commute (g i) (g j) := fun i j => by
    show g i * g j = g j * g i
    ext w
    have := congr_arg (fun F => F (w : V)) (hcomm i j).eq
    simpa [g, Module.End.mul_apply] using this
  have hgpow : ∀ i, g i ^ 5 = 1 := fun i => by
    show (f i).restrict (hW i) ^ 5 = 1
    rw [Module.End.pow_restrict]
    ext w
    simp [hpow i]
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ g hgcomm hgpow
  have hpos : 0 < finrank K W := Submodule.one_le_finrank_iff.2 hne
  let j : Fin (finrank K W) := ⟨0, hpos⟩
  refine ⟨(b j : V), (b j).2, fun h0 => b.ne_zero j (Subtype.ext h0), fun i => ⟨μ i j, ?_⟩⟩
  have := congrArg Subtype.val (hb i j)
  simpa [g] using this

include hζ in
theorem exists_ce_basis [Finite ι] [FiniteDimensional K V] (hdim : finrank K V = 5)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hpow : ∀ i, f i ^ 5 = 1) :
    ∃ b : Basis (Fin 5) K V, ∀ k, IsCE f (b k) := by
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one hζ f hcomm hpow
  refine ⟨b.reindex (finCongr hdim), fun k => ⟨?_, fun i => ⟨μ i ((finCongr hdim).symm k), ?_⟩⟩⟩
  · rw [Basis.reindex_apply]
    exact b.ne_zero _
  · rw [Basis.reindex_apply]
    exact hb i _

end Five

theorem ce_eq_smul_basis {ι κ : Type*} [Fintype κ] [DecidableEq κ] (f : ι → End K V)
    (b : Basis κ K V) (hb : ∀ k, IsCE f (b k))
    (hdist : ∀ j k, chr f (b j) = chr f (b k) → j = k) {v : V} (hv : IsCE f v) :
    ∃ (k : κ) (d : K), v = d • b k := by
  obtain ⟨k₀, hk₀⟩ : ∃ k, b.repr v k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv.1
    apply b.repr.injective
    ext k
    simp [hcon k]
  have key : ∀ k i, b.repr v k * chr f (b k) i = chr f v i * b.repr v k := by
    intro k i
    have h1 : f i v = ∑ l, (b.repr v l * chr f (b l) i) • b l := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, chr_spec (hb l) i, smul_smul]
    have h2 := congrArg (fun w => b.repr w k) h1
    have h3 := congrArg (fun w => b.repr w k) (chr_spec hv i)
    simp only [Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2 h3
    rw [← h2, h3]
  have hchr : ∀ k, b.repr v k ≠ 0 → chr f (b k) = chr f v := fun k hk => by
    funext i
    have := key k i
    exact mul_right_cancel₀ hk (by rw [mul_comm (chr f (b k) i)]; exact this)
  refine ⟨k₀, b.repr v k₀, ?_⟩
  conv_lhs => rw [← b.sum_repr v]
  rw [Finset.sum_eq_single k₀]
  · intro k _ hk
    by_cases hz : b.repr v k = 0
    · rw [hz, zero_smul]
    · exact absurd (hdist k k₀ ((hchr k hz).trans (hchr k₀ hk₀).symm)) hk
  · intro h
    exact absurd (Finset.mem_univ k₀) h

end U5L

end Sec1511

end CFSG.RankThree.PartOne
