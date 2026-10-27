module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpNatTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisOrbit
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpSpin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6NatType

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.Quasithin.SmithCurtis
open scoped Matrix

private theorem finrank_range_conj {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g y : G) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (g * y * g⁻¹) - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  have hconj : ρ (g * y * g⁻¹) - 1 = ρ g * (ρ y - 1) * ρ (g⁻¹) := by
    rw [map_mul, map_mul]
    have h2 : ρ g * ρ (g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g * ρ y * ρ (g⁻¹) - 1 = (ρ g * ρ y - ρ g) * ρ (g⁻¹) := by rw [sub_mul, h2]
      _ = ρ g * (ρ y - 1) * ρ (g⁻¹) := by rw [mul_sub, mul_one]
  have hsurj : Function.Surjective (ρ (g⁻¹)) := fun b =>
    ⟨ρ g b, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]⟩
  have hrange : LinearMap.range (ρ g * (ρ y - 1) * ρ (g⁻¹)) =
      (LinearMap.range (ρ y - 1)).map (ρ g) := by
    rw [show ρ g * (ρ y - 1) * ρ (g⁻¹) =
      (ρ g).comp ((ρ y - 1).comp (ρ (g⁻¹))) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hleft : Function.LeftInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩
  rw [hconj, hrange]
  exact e.finrank_map_eq (LinearMap.range (ρ y - 1))

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem sp_two_empty {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp n (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) {y₀ : V} {χ : StatedSp n (ZMod 2) → ZMod 2} {μ : Fin n → ZMod 2}
    (ht : (spCurtisDatum n (ZMod 2)).IsCurtisType ρ y₀ χ μ) (hχ : χ 1 = 1)
    (hμ01 : ∀ s, μ s = 0 ∨ μ s = 1) (hμ1 : ∀ s, μ s ≠ 1) : False := by
  have hμ : μ = 0 := by
    funext s
    exact (hμ01 s).elim id (fun h1 => absurd h1 (hμ1 s))
  have htriv := isCurtisType_sp_two_trivial (k := ZMod 2) (n := n) hχ
  rw [hμ] at ht
  obtain ⟨β, hβ⟩ := (spCurtisDatum n (ZMod 2)).iso_of_isCurtisType hρ
    (isSimpleRep_representation_trivial (k := ZMod 2) (StatedSp n (ZMod 2))) ht htriv
  obtain ⟨g, hg⟩ := hρ1
  exact hg (by
    ext v
    exact β.injective (by simpa using hβ g v))

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
  CFSG.QuasithinUnique.Setup.X7 in
private theorem sp_two_singleton {n : ℕ} (hn : 2 ≤ n) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp n (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp n (ZMod 2) → ZMod 2} {μ : Fin n → ZMod 2}
    (ht : (spCurtisDatum n (ZMod 2)).IsCurtisType ρ y₀ χ μ) (hχ : χ 1 = 1)
    (hμ01 : ∀ s, μ s = 0 ∨ μ s = 1) {S : Finset (Fin n)}
    (hS : ∀ s, s ∈ S ↔ μ s = 1) (hS1 : ∀ s, s ∈ S ↔ s.val = 0) :
    ∃ β : V ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2),
      ∀ (g : StatedSp n (ZMod 2)) (v : V), β (ρ g v) = mat n (ZMod 2) g *ᵥ β v := by
  have hμ : μ = fun s : Fin n => if s.val = 0 then 1 else 0 := by
    funext s
    have hiff : μ s = 1 ↔ s.val = 0 := (hS s).symm.trans (hS1 s)
    rcases hμ01 s with h0 | h1
    · rw [h0, if_neg (fun hs => zero_ne_one (h0 ▸ hiff.mpr hs))]
    · rw [h1, if_pos (hiff.mp h1)]
  rw [hμ] at ht
  obtain ⟨β, hβ⟩ := (spCurtisDatum n (ZMod 2)).iso_of_isCurtisType hρ
    (isSimpleRep_sp_matMap (n := n) (by omega : 1 ≤ n) (RingHom.id (ZMod 2))) ht
    (isCurtisType_sp_two_natural (n := n) (by omega : 2 ≤ n) (RingHom.id (ZMod 2)) hχ)
  exact ⟨β, fun g v => by
    simpa [matRep_apply, matMap_apply, Matrix.map_id, RingHom.coe_id] using hβ g v⟩

open CFSG.LieType.RootSystem CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem sp_two_four_le {n : ℕ} (hn : 3 ≤ n) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp n (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp n (ZMod 2) → ZMod 2} {μ : Fin n → ZMod 2}
    (ht : (spCurtisDatum n (ZMod 2)).IsCurtisType ρ y₀ χ μ) (hχ : χ 1 = 1)
    {S : Finset (Fin n)} (hS0 : S ≠ ∅) (hS1 : ¬ (∀ s, s ∈ S ↔ s.val = 0))
    (hspin : n = 3 → S ≠ {⟨2, by omega⟩})
    (hS : ∀ s, s ∈ S ↔ μ s = 1)
    {y : StatedSp n (ZMod 2)} (hy : y * y = 1) (hy1 : y ≠ 1) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  let D : CurtisDatum (StatedSp n (ZMod 2))
      (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem 2 := spCurtisDatum n (ZMod 2)
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
  have hS1' : S ≠ {⟨0, by omega⟩} := fun h => hS1 fun s => by rw [h]; simp [Fin.ext_iff]
  obtain ⟨g, π, σ, hσ, hx, hg⟩ :=
    exists_conj_mat_eq_spMonoPerm (n := n) (K := ZMod 2) (by omega) hy hy1
  obtain ⟨x, hxr, hxw⟩ := exists_nW_eq_of_mat_eq hσ hg
  obtain ⟨u, hu_mem, hu_inj, hu_move⟩ :=
    exists_four_orbit_spWeight2 (n := n) (by omega : 3 ≤ n) (S := S) hSne hS1' hspin hxr hx
  let cs := (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem
  let : MulAction (coxeterMatrix (isFiniteType_cartanC n)).Group (Fin n → ℤ) :=
    MulAction.compHom (Fin n → ℤ) (weylAction (isFiniteType_cartanC n))
  have hv : ∀ t : Fin n, μ t ≠ (spCurtisDatum n (ZMod 2)).dScalar χ t →
      cs.simple t • spWeight2 S = spWeight2 S := by
    intro t htne
    have hnot : t ∉ S := by
      intro hmem
      exact htne (by
        rw [show μ t = 1 from (hS t).mp hmem]
        exact (spCurtisDatum_two_dScalar hχ t).symm)
    simpa [cs, MulAction.compHom_smul_def, Module.End.smul_def]
      using weylAction_simple_spWeight2 (n := n) (S := S) hnot
  have hu : ∀ i, u i ∈ MulAction.orbit
      (coxeterMatrix (isFiniteType_cartanC n)).Group (spWeight2 S) := by
    intro i
    obtain ⟨w, hw⟩ := hu_mem i
    exact MulAction.mem_orbit_iff.mpr ⟨w, by
      simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hw.symm⟩
  have horbit := le_finrank_range_sub_one_of_mem_orbit (D := D) hρ ht hv
    x u hu hu_inj (by simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hu_move)
  have hfin := finrank_range_conj ρ g y
  rw [← hxw] at hfin
  rw [← hfin]
  exact horbit

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem sp_spin_support_not_empty {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp 3 (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    (hdim : Module.finrank (ZMod 2) V = 8)
    {y₀ : V} {χ : StatedSp 3 (ZMod 2) → ZMod 2} {μ : Fin 3 → ZMod 2}
    (ht : (spCurtisDatum 3 (ZMod 2)).IsCurtisType ρ y₀ χ μ) (hχ : χ 1 = 1)
    (hμ01 : ∀ s, μ s = 0 ∨ μ s = 1) {S : Finset (Fin 3)}
    (hS : ∀ s, s ∈ S ↔ μ s = 1) : S ≠ ∅ := by
  intro h0
  have hμ1 : ∀ s : Fin 3, μ s ≠ 1 := fun s h =>
    (Finset.eq_empty_iff_forall_notMem.mp h0 s) ((hS s).mpr h)
  have hμ : μ = 0 := by
    funext s
    exact (hμ01 s).elim id (fun h1 => absurd h1 (hμ1 s))
  have htriv := isCurtisType_sp_two_trivial (k := ZMod 2) (n := 3) hχ
  rw [hμ] at ht
  obtain ⟨β, -⟩ := (spCurtisDatum 3 (ZMod 2)).iso_of_isCurtisType hρ
    (isSimpleRep_representation_trivial (k := ZMod 2) (StatedSp 3 (ZMod 2))) ht htriv
  have h1 : Module.finrank (ZMod 2) V = 1 := by rw [β.finrank_eq, Module.finrank_self]
  omega

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem sp_spin_support_ne_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp 3 (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    (hdim : Module.finrank (ZMod 2) V = 8)
    {y₀ : V} {χ : StatedSp 3 (ZMod 2) → ZMod 2} {μ : Fin 3 → ZMod 2}
    (ht : (spCurtisDatum 3 (ZMod 2)).IsCurtisType ρ y₀ χ μ) (hχ : χ 1 = 1)
    (hμ01 : ∀ s, μ s = 0 ∨ μ s = 1) {S : Finset (Fin 3)}
    (hS : ∀ s, s ∈ S ↔ μ s = 1) : S ≠ {⟨0, by omega⟩} := by
  intro h1
  have hS1' : ∀ s : Fin 3, s ∈ S ↔ s.val = 0 := by
    intro s
    rw [h1, Finset.mem_singleton]
    exact Fin.ext_iff
  obtain ⟨β, -⟩ := sp_two_singleton (n := 3) (by omega) hρ ht hχ hμ01 hS hS1'
  have h6 : Module.finrank (ZMod 2) V = 6 := by
    rw [β.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

open CFSG.LieType.RootSystem CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem sp_spin_support {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp 3 (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    (hdim : Module.finrank (ZMod 2) V = 8)
    {y : V} {χ : StatedSp 3 (ZMod 2) → ZMod 2} {μ : Fin 3 → ZMod 2}
    (ht : (spCurtisDatum 3 (ZMod 2)).IsCurtisType ρ y χ μ) (hχ : χ 1 = 1)
    (hμ01 : ∀ s, μ s = 0 ∨ μ s = 1) {S : Finset (Fin 3)}
    (hS : ∀ s, s ∈ S ↔ μ s = 1) : S = {⟨2, by omega⟩} := by
  have hne : S ≠ ∅ := sp_spin_support_not_empty hρ hdim ht hχ hμ01 hS
  have h0 : S ≠ {⟨0, by omega⟩} := sp_spin_support_ne_zero hρ hdim ht hχ hμ01 hS
  by_contra h2
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨u, hu_mem, hu_inj⟩ := exists_nine_orbit_spWeight2 hSne h0 h2
  let D : CurtisDatum (StatedSp 3 (ZMod 2))
      (coxeterMatrix (isFiniteType_cartanC 3)).toCoxeterSystem 2 := spCurtisDatum 3 (ZMod 2)
  let cs := (coxeterMatrix (isFiniteType_cartanC 3)).toCoxeterSystem
  let : MulAction (coxeterMatrix (isFiniteType_cartanC 3)).Group (Fin 3 → ℤ) :=
    MulAction.compHom (Fin 3 → ℤ) (weylAction (isFiniteType_cartanC 3))
  have hv : ∀ t : Fin 3, μ t ≠ D.dScalar χ t → cs.simple t • spWeight2 S = spWeight2 S := by
    intro t htne
    have hnot : t ∉ S := by
      intro hmem
      exact htne (by
        rw [show μ t = 1 from (hS t).mp hmem]
        exact (spCurtisDatum_two_dScalar hχ t).symm)
    simpa [cs, MulAction.compHom_smul_def, Module.End.smul_def]
      using weylAction_simple_spWeight2 (n := 3) (S := S) hnot
  have hu : ∀ i, u i ∈ MulAction.orbit
      (coxeterMatrix (isFiniteType_cartanC 3)).Group (spWeight2 S) := by
    intro i
    obtain ⟨w, hw⟩ := hu_mem i
    exact MulAction.mem_orbit_iff.mpr ⟨w, by
      simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hw.symm⟩
  have hnine := card_le_finrank_of_mem_orbit (D := D) hρ ht hv u hu hu_inj
  omega

private theorem spRep_spin_mu_eq {μ μ₁ : Fin 3 → ZMod 2}
    (hμ01 : ∀ s, μ s = 0 ∨ μ s = 1) (hμ₁01 : ∀ s, μ₁ s = 0 ∨ μ₁ s = 1)
    {S : Finset (Fin 3)} (hS : ∀ s, s ∈ S ↔ μ s = 1) (hS2 : S = {⟨2, by omega⟩})
    {S₀ : Finset (Fin 3)} (hS₀ : ∀ s, s ∈ S₀ ↔ μ₁ s = 1)
    (hS₀2 : S₀ = {⟨2, by omega⟩}) : μ₁ = μ := by
  have hμ2 : ∀ s : Fin 3, μ s = 1 ↔ s = ⟨2, by omega⟩ := by
    intro s
    rw [← hS s, hS2]
    exact Finset.mem_singleton
  funext s
  have hiff : μ₁ s = 1 ↔ μ s = 1 := by
    rw [← hS₀ s, hS₀2]
    exact Finset.mem_singleton.trans (hμ2 s).symm
  rcases hμ01 s with h0 | h1
  · rcases hμ₁01 s with h0' | h1'
    · rw [h0, h0']
    · exact absurd (hiff.mp h1') (by rw [h0]; exact zero_ne_one)
  · exact (hiff.mpr h1).trans h1.symm

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem spRep_spin_isCurtisType {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp 3 (ZMod 2)) V}
    {y₁ : V} {χ χ₁ : StatedSp 3 (ZMod 2) → ZMod 2} {μ μ₁ : Fin 3 → ZMod 2}
    (ht₁ : (spCurtisDatum 3 (ZMod 2)).IsCurtisType ρ y₁ χ₁ μ₁)
    (hχ : χ 1 = 1) (hμ₁eq : μ₁ = μ) :
    (spCurtisDatum 3 (ZMod 2)).IsCurtisType ρ y₁ χ μ := by
  refine ⟨ht₁.1, ht₁.2.1, ?_, ?_⟩
  · intro h hh
    have hmem : h ∈ (spCurtisDatum 3 (ZMod 2)).H := hh
    rw [spCurtisDatum_two_H 3] at hmem
    have h1 : h = 1 := by simpa using hmem
    subst h1
    rw [map_one, Module.End.one_apply, hχ, one_smul]
  · intro s
    rw [ht₁.2.2.2 s, hμ₁eq]

open CFSG.LieType.RootSystem CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem sp_two_spin {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp 3 (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : StatedSp 3 (ZMod 2) → ZMod 2} {μ : Fin 3 → ZMod 2}
    (ht : (spCurtisDatum 3 (ZMod 2)).IsCurtisType ρ y₀ χ μ) (hχ : χ 1 = 1)
    (hμ01 : ∀ s, μ s = 0 ∨ μ s = 1) {S : Finset (Fin 3)}
    (hS : ∀ s, s ∈ S ↔ μ s = 1) (hS2 : S = {⟨2, by omega⟩}) :
    Module.finrank (ZMod 2) V = 8 := by
  let D : CurtisDatum (StatedSp 3 (ZMod 2))
      (coxeterMatrix (isFiniteType_cartanC 3)).toCoxeterSystem 2 := spCurtisDatum 3 (ZMod 2)
  have : Fintype (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanC 3)).Group :=
    @Fintype.ofFinite _ (CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanC 3))
  have hsplit : SplitOver (ZMod 2) D.H :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.spCurtisDatum_splitOver
      (n := 3) (K := ZMod 2) (k := ZMod 2)
  obtain ⟨V₀, hACG₀, hMod₀, hFin₀, ρ₀, hρ₀, hdim₀⟩ := exists_spinRep_statedSp
  have : Finite V₀ := hFin₀
  obtain ⟨y₁, χ₁, μ₁, ht₁⟩ := D.exists_isCurtisType hsplit hρ₀
  have hχ₁ : χ₁ 1 = 1 := ht₁.chi_one
  have hμ₁01 : ∀ s : Fin 3, μ₁ s = 0 ∨ μ₁ s = 1 := fun s =>
    (ht₁.mu_eq s).imp id (fun h => by rw [h]; exact spCurtisDatum_two_d'Scalar hχ₁ s)
  let S₀ : Finset (Fin 3) := Finset.univ.filter (fun s => μ₁ s = 1)
  have hS₀ : ∀ s : Fin 3, s ∈ S₀ ↔ μ₁ s = 1 := fun s => by simp [S₀]
  have hS₀2 : S₀ = {⟨2, by omega⟩} := sp_spin_support hρ₀ hdim₀ ht₁ hχ₁ hμ₁01 hS₀
  have hμ₁eq : μ₁ = μ := spRep_spin_mu_eq hμ01 hμ₁01 hS hS2 hS₀ hS₀2
  have ht₁' : D.IsCurtisType ρ₀ y₁ χ μ := spRep_spin_isCurtisType ht₁ hχ hμ₁eq
  obtain ⟨β, -⟩ := D.iso_of_isCurtisType hρ hρ₀ ht ht₁'
  rw [β.finrank_eq, hdim₀]

theorem sp_two_natural_or_four_le {n : ℕ} (hn : 3 ≤ n) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (StatedSp n (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) {y : StatedSp n (ZMod 2)} (hy : y * y = 1) (hy1 : y ≠ 1) :
    (∃ β : V ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2),
        ∀ (g : StatedSp n (ZMod 2)) (v : V), β (ρ g v) = mat n (ZMod 2) g *ᵥ β v) ∨
      (n = 3 ∧ Module.finrank (ZMod 2) V = 8) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  let D : CurtisDatum (StatedSp n (ZMod 2))
      (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem 2 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.spCurtisDatum n (ZMod 2)
  have : Fintype (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanC n)).Group :=
    @Fintype.ofFinite _ (CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanC n))
  have hsplit : SplitOver (ZMod 2) D.H :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.spCurtisDatum_splitOver
      (n := n) (K := ZMod 2) (k := ZMod 2)
  obtain ⟨y₀, χ, μ, ht⟩ := D.exists_isCurtisType hsplit hρ
  have hχ : χ 1 = 1 := ht.chi_one
  let S : Finset (Fin n) := Finset.univ.filter (fun s => μ s = 1)
  have hS : ∀ s : Fin n, s ∈ S ↔ μ s = 1 := fun s => by simp [S]
  have hμ01 : ∀ s : Fin n, μ s = 0 ∨ μ s = 1 := fun s =>
    (ht.mu_eq s).imp id (fun h => by
      rw [h]
      exact spCurtisDatum_two_d'Scalar hχ s)
  by_cases hS0 : S = ∅
  · have hμ1 : ∀ s : Fin n, μ s ≠ 1 := fun s h =>
      (Finset.eq_empty_iff_forall_notMem.mp hS0 s) ((hS s).mpr h)
    exact (sp_two_empty hρ hρ1 ht hχ hμ01 hμ1).elim
  · by_cases hS1 : S = {⟨0, by omega⟩}
    · have hS1' : ∀ s : Fin n, s ∈ S ↔ s.val = 0 := by
        intro s
        rw [hS1]
        simp [Fin.ext_iff]
      left
      exact sp_two_singleton (by omega) hρ ht hχ hμ01 hS hS1'
    · by_cases hspinCase : n = 3 ∧ S = {⟨2, by omega⟩}
      · obtain ⟨hn3, hS2⟩ := hspinCase
        subst hn3
        right
        left
        exact ⟨rfl, sp_two_spin hρ ht hχ hμ01 hS hS2⟩
      · right
        right
        have hS1'' : ¬ (∀ s : Fin n, s ∈ S ↔ s.val = 0) := fun h =>
          hS1 (Finset.ext fun s => (h s).trans (by simp [Fin.ext_iff]))
        have hspin : n = 3 → S ≠ {⟨2, by omega⟩} := fun h3 hSe => hspinCase ⟨h3, hSe⟩
        exact sp_two_four_le hn hρ ht hχ hS0 hS1'' hspin hS hy hy1

end CFSG.LocalAnalysis.WeakClosure81
