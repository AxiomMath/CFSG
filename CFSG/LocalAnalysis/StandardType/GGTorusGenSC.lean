module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRTransfer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusGenR_of_torusSC {p : ℕ} {R : Type} [Group R] (hcent : GGTorusCentSC p R)
    (hgen : GGTorusCompGenSC p R) : GGTorusGenR p 3 R := by
  intro E hE h3 hsc x hx hx1 J hJ c hc hcp
  refine ⟨J ⊓ E, Subgroup.normalizer (E : Set R), fun g => ⟨1, ?_⟩, fun s hs => ?_,
    inf_le_left, subset_rfl, hgen E hE h3 hsc x hx hx1 J hJ
      (hcent E hE h3 hsc c (fun e he => (Subgroup.mem_centralizer_iff.mp hc e he).symm) hcp)⟩
  · exact Subtype.ext (by simpa using hE.2 g g.2.2)
  · exact Subgroup.mem_centralizer_iff.mpr fun e he =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨s, hs.2⟩)

theorem ggTorusGenTableB_of_torusSC {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (hcent : GGTorusCentSC p R)
    (hgen : GGTorusCompGenSC p R) : GGTorusGenTableB p R I := by
  exact ggTorusGenTableB_of_torusGenR hp hI hZ hcp (ggTorusGenR_of_torusSC hcent hgen)

private theorem mem_normalizer_range_of_conj {M G : Type*} [Group M] [Group G] (f : M →* G)
    (n : G) (φ : M ≃* M) (h : ∀ m, n * f m * n⁻¹ = f (φ m)) :
    n ∈ Subgroup.normalizer (f.range : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨φ v, (h v).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨φ.symm v, ?_⟩
    have h1 := h (φ.symm v)
    rw [φ.apply_symm_apply, hv] at h1
    have h2 := congrArg (fun y => n⁻¹ * y * n) h1
    simpa [mul_assoc] using h2

private theorem conj_mem_closure_conj {R : Type} [Group R] (N : Subgroup R) (T : Set R) {n : R}
    (hn : n ∈ N) {c : R} (hc : c ∈ Subgroup.closure (⋃ m ∈ N, (fun s => m * s * m⁻¹) '' T)) :
    n * c * n⁻¹ ∈ Subgroup.closure (⋃ m ∈ N, (fun s => m * s * m⁻¹) '' T) := by
  refine Subgroup.closure_induction
    (p := fun c _ => n * c * n⁻¹ ∈ Subgroup.closure (⋃ m ∈ N, (fun s => m * s * m⁻¹) '' T))
    ?_ ?_ ?_ ?_ hc
  · intro u hu
    simp only [Set.mem_iUnion, Set.mem_image] at hu
    obtain ⟨m, hm, j, hj, rfl⟩ := hu
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨n * m, N.mul_mem hn hm, j, hj, by group⟩
  · simp
  · intro u v _ _ ihu ihv
    simpa [mul_assoc] using Subgroup.mul_mem _ ihu ihv
  · intro u _ ihu
    simpa [mul_assoc] using Subgroup.inv_mem _ ihu

private theorem mem_comap_of_conj {p k : ℕ} {R : Type} [Group R] {E C : Subgroup R}
    {τ : (Fin k → Multiplicative (ZMod p)) →* R} (hτE : τ.range = E)
    (hC : ∀ n ∈ Subgroup.normalizer (E : Set R), ∀ c ∈ C, n * c * n⁻¹ ∈ C)
    {φ : (Fin k → Multiplicative (ZMod p)) ≃* (Fin k → Multiplicative (ZMod p))} {w : R}
    (hw : ∀ f, w * τ f * w⁻¹ = τ (φ f)) {f : Fin k → Multiplicative (ZMod p)}
    (hf : f ∈ C.comap τ) : φ f ∈ C.comap τ := by
  have hwN : w ∈ Subgroup.normalizer (E : Set R) := by
    rw [← hτE]
    exact mem_normalizer_range_of_conj τ w φ hw
  have h := hC w hwN (τ f) hf
  rw [hw f] at h
  exact h

theorem ggTorusCompGenSC_of_signedEltSC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type}
    [Group R] (hsg : GGTorusSignedEltSC p R) (hmeet : GGTorusCompMeetSC p R) :
    GGTorusCompGenSC p R := by
  intro E hEab hcard hsc x hx hx1 J hJ
  obtain ⟨k, τ, -, hτE, hsgn, hperm, -⟩ := hsg E hEab hcard hsc
  let C : Subgroup R := Subgroup.closure (⋃ n ∈ Subgroup.normalizer (E : Set R),
    (fun s => n * s * n⁻¹) '' ((J ⊓ E : Subgroup R) : Set R))
  have hC : ∀ n ∈ Subgroup.normalizer (E : Set R), ∀ c ∈ C, n * c * n⁻¹ ∈ C :=
    fun n hn c hc => conj_mem_closure_conj _ _ hn hc
  have hFne : C.comap τ ≠ ⊥ := by
    obtain ⟨w, hwJ, hwE, hw1⟩ := hmeet E hEab hcard hsc x hx hx1 J hJ
    obtain ⟨f, rfl⟩ : w ∈ τ.range := hτE ▸ hwE
    refine fun hbot => hw1 ?_
    have hfC : f ∈ C.comap τ := Subgroup.subset_closure (Set.mem_biUnion
      (Subgroup.one_mem _) ⟨τ f, ⟨hwJ, hwE⟩, by group⟩)
    rw [hbot, Subgroup.mem_bot] at hfC
    rw [hfC, map_one]
  have hFtop : C.comap τ = ⊤ := by
    refine (NbrSp.eq_bot_or_eq_top_of_signed hp hp2 (C.comap τ) (fun i f hf => ?_)
      (fun σ f hf => ?_)).resolve_left hFne
    · obtain ⟨w, hw⟩ := hsgn i
      exact mem_comap_of_conj hτE hC hw hf
    · obtain ⟨w, hw⟩ := hperm σ
      exact mem_comap_of_conj hτE hC hw hf
  intro e he
  obtain ⟨f, rfl⟩ : e ∈ τ.range := hτE ▸ he
  exact Subgroup.mem_comap.mp (hFtop ▸ Subgroup.mem_top f : f ∈ C.comap τ)

end CFSG.StandardType
