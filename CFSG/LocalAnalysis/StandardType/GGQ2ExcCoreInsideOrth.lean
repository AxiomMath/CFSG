module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientRefl
import CFSG.Blueprint.ChevalleyPinnedLemmas
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LieType.Chevalley.CorootCoordinates
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyQuad
import CFSG.LieType.Chevalley.RootCommutator

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem rootChar_eq_one_of_mem_rootSpan
    {τ : Tag} {L : Type} [Field L] {Ψ : Set (Fin τ.rank → ℤ)}
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hcomm : ∀ β ∈ Ψ, ∀ x ∈ rootSubgroup τ L β, ∀ y ∈ rootSubgroup τ L δ, Commute x y)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ rootSpan τ L Ψ) : rootChar b δ = 1 := by
  have hx0 : pinnedX τ L δ 1 ∈ rootSubgroup τ L δ :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have hle : rootSpan τ L Ψ ≤ Subgroup.centralizer ({pinnedX τ L δ 1} : Set _) := by
    rw [rootSpan]
    refine iSup₂_le fun β hβ => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm β hβ x hx (pinnedX τ L δ 1) hx0
  have hcentral : Commute (rootDiagUnit τ b) (pinnedX τ L δ 1) := by
    have h := hle hb
    rwa [Subgroup.mem_centralizer_singleton_iff] at h
  have hconj : rootDiagUnit τ b * pinnedX τ L δ 1 * (rootDiagUnit τ b)⁻¹
      = pinnedX τ L δ 1 := by
    rw [hcentral.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hp : pinnedX τ L δ ((rootChar b δ : L) * 1) = pinnedX τ L δ 1 := by
    rw [← rootDiagUnit_conj_pinnedX b hδ 1, hconj]
  have h1 : (rootChar b δ : L) * 1 = 1 := pinnedX_injective τ L δ hp
  rw [mul_one] at h1
  exact Units.ext h1

theorem ggLinImage_rootSpan_codeRoots_le_ker
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} {S : LangSetup τ L p} {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}
    (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)) {k : ExcRaw.Root m}
    (hk : ∀ i ∈ c, ¬ ExcRaw.Adj m k i) :
    ggLinImage (p := 3) d.coord (rootSpan τ L (codeRoots d.γ c)) ≤
      LinearMap.ker (ExcRaw.root m k) := by
  intro v hv
  rw [mem_ggLinImage] at hv
  obtain ⟨b, hb⟩ := d.exists_rootDiagUnit (Additive.toMul (d.coord.symm v))
  have hcoord : d.coord (Additive.ofMul (Additive.toMul (d.coord.symm v))) = v := by
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hbroot : rootDiagUnit τ b ∈ rootSpan τ L (codeRoots d.γ c) := by
    rw [← hb]
    exact hv
  have hpair : ∀ i ∈ c, ExcRaw.pairing m k i = 0 := by
    intro i hi
    have h := hk i hi
    simp only [ExcRaw.Adj, ne_eq, not_or, not_not] at h
    exact h.1
  have hiform : ∀ i ∈ c, CFSG.LieType.Steinberg.Adjoint.iform (d.γ i) (d.γ k) = 0 := by
    intro i hi
    have hcp : corootPair (d.γ i) (d.γ k) = 0 := by
      rw [← d.pairing_eq k i]
      exact hpair i hi
    rwa [corootPair_eq_iform_of_simplyLaced hτ (d.isRoot i) (d.γ k)] at hcp
  have hknotc : k ∉ c := by
    intro hkc
    have h := hk k hkc
    refine h (Or.inl ?_)
    rw [ExcRaw.pairing_self]
    norm_num
  have hne : ∀ i ∈ c, d.γ k ≠ d.γ i := by
    intro i hi h
    exact hknotc (by rw [d.eq_of_eq k i (Or.inl h)]; exact hi)
  have hne' : ∀ i ∈ c, d.γ k ≠ -d.γ i := by
    intro i hi h
    exact hknotc (by rw [d.eq_of_eq k i (Or.inr h)]; exact hi)
  have hnot_pos : ∀ i ∈ c, ¬ IsRoot τ (d.γ i + d.γ k) :=
    fun i hi => not_isRoot_add_of_orth hτ (d.isRoot i) (d.isRoot k) (hiform i hi)
  have hcomm_pos : ∀ i ∈ c, ∀ x ∈ rootSubgroup τ L (d.γ i),
      ∀ y ∈ rootSubgroup τ L (d.γ k), Commute x y := by
    intro i hi x hx y hy
    exact (simply_laced_root_commutator_unit τ hτ (d.isRoot i) (d.isRoot k)
      (Ne.symm (hne i hi)) (fun h => hne' i hi (by rw [h, neg_neg]) )).2
      (hnot_pos i hi) L x hx y hy
  have hnot_neg : ∀ i ∈ c, ¬ IsRoot τ (-d.γ i + d.γ k) := by
    intro i hi h
    refine not_isRoot_sub_of_orth hτ (d.isRoot i) (d.isRoot k) (hiform i hi) ?_
    have h' := IsRoot.neg h
    rwa [neg_add, neg_neg, ← sub_eq_add_neg] at h'
  have hcomm_neg : ∀ i ∈ c, ∀ x ∈ rootSubgroup τ L (-d.γ i),
      ∀ y ∈ rootSubgroup τ L (d.γ k), Commute x y := by
    intro i hi x hx y hy
    exact (simply_laced_root_commutator_unit τ hτ (IsRoot.neg (d.isRoot i)) (d.isRoot k)
      (fun h => hknotc (by rw [d.eq_of_eq k i (Or.inr h.symm)]; exact hi))
      (fun h => hne i hi (neg_injective h.symm))).2 (hnot_neg i hi) L x hx y hy
  have hcomm : ∀ β ∈ codeRoots d.γ c, ∀ x ∈ rootSubgroup τ L β,
      ∀ y ∈ rootSubgroup τ L (d.γ k), Commute x y := by
    rintro β ⟨i, hi, hβ⟩ x hx y hy
    rcases hβ with rfl | rfl
    · exact hcomm_pos i hi x hx y hy
    · exact hcomm_neg i hi x hx y hy
  have hroot : rootChar b (d.γ k) = 1 :=
    rootChar_eq_one_of_mem_rootSpan (d.isRoot k) hcomm hbroot
  have hchar : d.ζ ^ (ExcRaw.root m k v).val = 1 := by
    rw [← hcoord, ← d.rootChar_eq (Additive.toMul (d.coord.symm v)) b hb k]
    exact hroot
  have hzero : ExcRaw.root m k v = 0 :=
    zeta_pow_val_injective d.ζ_pow_three d.ζ_ne_one (by simpa using hchar)
  simpa using hzero

theorem ggLinImage_codeComponent_le_ker
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}
    (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)) {k : ExcRaw.Root m}
    (hk : ∀ i ∈ c, ¬ ExcRaw.Adj m k i) :
    ggLinImage (p := 3) d.coord (codeComponent S d.γ c) ≤ LinearMap.ker (ExcRaw.root m k) := by
  refine (ggLinImage_mono d.coord ?_).trans
    (ggLinImage_rootSpan_codeRoots_le_ker hτ d c hk)
  exact (Subgroup.commutator_le_self _).trans inf_le_left

theorem ggLinImage_codeComponent_le_inside_of_orth
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}
    (d : ExcCoordDatum S T₀ m) (c : Finset (ExcRaw.Root m)) {k : ExcRaw.Root m}
    (hk : ∀ i ∈ c, ¬ ExcRaw.Adj m k i)
    (hΓ : ggLinImage (p := 3) d.coord S.Γ ≤
      ExcRaw.inside m c ⊔ Submodule.span (ZMod 3) {ExcRaw.coroot m k}) :
    ggLinImage (p := 3) d.coord (codeComponent S d.γ c) ≤ ExcRaw.inside m c := by
  intro v hv
  have hvΓ : v ∈ ggLinImage (p := 3) d.coord S.Γ :=
    ggLinImage_mono d.coord (codeComponent_le_Γ S d.γ c) hv
  have h0 : ExcRaw.root m k v = 0 := ggLinImage_codeComponent_le_ker hτ S d c hk hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp (hΓ hvΓ)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hin : ExcRaw.inside m c ≤ LinearMap.ker (ExcRaw.root m k) := by
    rw [ExcRaw.inside, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have h := hk i hi
    simp only [ExcRaw.Adj, ne_eq, not_or, not_not] at h
    change ExcRaw.root m k (ExcRaw.coroot m i) = 0
    rw [ExcRaw.pairing_eq, h.1, Int.cast_zero]
  have hu0 : ExcRaw.root m k u = 0 := hin hu
  rw [map_add, map_smul, hu0, ExcRaw.root_coroot, zero_add, smul_eq_mul] at h0
  have ha : a = 0 := (mul_eq_zero.mp h0).resolve_right (by decide)
  rw [ha, zero_smul, add_zero]
  exact hu

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
