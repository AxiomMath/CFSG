module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientRefl
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientSep
import CFSG.LocalAnalysis.StandardType.GGL45NtLattice
import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
import CFSG.LieType.Chevalley.E6EvenRootTorus
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav


section Torus


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

omit [IsAlgClosed L] in
theorem adjointGroup_inf_centralizer_of_le_torusGroup {T₀ : Subgroup (ModGL τ L)}
    (hT : T₀ ≤ torusGroup τ L)
    (hker : ∀ δ, IsRoot τ δ → ∃ b, rootDiagUnit τ b ∈ T₀ ∧ rootChar b δ ≠ 1)
    (hstab : ∀ w : WeylGroup τ,
      (∀ b, rootDiagUnit τ b ∈ T₀ → ∀ v, rootChar b (w • v) = rootChar b v) → w = 1) :
    adjointGroup τ L ⊓ Subgroup.centralizer (T₀ : Set (ModGL τ L)) = torusGroup τ L := by
  classical
  choose a ha using fun t : ↥T₀ => exists_rootDiagUnit_eq_of_mem_torusGroup (hT t.2)
  have ha' : ∀ b (hb : rootDiagUnit τ b ∈ T₀), a ⟨_, hb⟩ = b := fun b hb =>
    rootDiagUnit_injective (ha ⟨_, hb⟩).symm
  have hcentral : Subgroup.centralizer (T₀ : Set (ModGL τ L)) =
      ⨅ t : ↥T₀, Subgroup.centralizer {rootDiagUnit τ (a t)} := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_iInf]
    constructor
    · intro h t
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h _ (ha t ▸ t.2)).symm
    · intro h y hy
      have ht := h ⟨y, hy⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← ha ⟨y, hy⟩] at ht
      exact ht.symm
  have hstab' : CFSG.HardMathSupport.Timmesfeld.Torality.familyStabilizerSubgroup a ≤
      CFSG.HardMathSupport.C14Lattice.familyReflectionGroup a := by
    intro w hw
    have hw' := CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyStabilizerSubgroup.1 hw
    rw [hstab w fun b hb v => by simpa only [ha' b hb] using hw' ⟨_, hb⟩ v]
    exact one_mem _
  have hker' : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro δ ⟨hδ, hall⟩
    obtain ⟨b, hb, hne⟩ := hker δ hδ
    exact hne (by simpa only [ha' b hb] using hall ⟨_, hb⟩)
  have hfam : adjointGroup τ L ⊓ Subgroup.centralizer (T₀ : Set (ModGL τ L)) =
      CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ L a := by
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer, hcentral]
  rw [hfam, CFSG.HardMathSupport.C14Lattice.familyCentralizer_eq_familyGroup a hstab',
    CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup, hker']
  simp [rootSpan]

theorem exists_weylTuple_of_mem_normalizer {T₀ : Subgroup (ModGL τ L)}
    (hT : T₀ ≤ torusGroup τ L)
    (hC : adjointGroup τ L ⊓ Subgroup.centralizer (T₀ : Set (ModGL τ L)) = torusGroup τ L)
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L ⊓ Subgroup.normalizer (T₀ : Set (ModGL τ L))) :
    ∃ w : WeylGroup τ, ∀ b, g * rootDiagUnit τ b * g⁻¹ = rootDiagUnit τ (weylTuple w b) := by
  obtain ⟨h, hh, w, rfl⟩ :=
    CFSG.RankThree.Chevalley.exists_eq_mul_canonicalRep_of_mem_normalizer
      (V := (T₀ : Set (ModGL τ L))) hT hC hg
  refine ⟨w, fun b => ?_⟩
  rw [show h * canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
        (h * canonicalRep (coxeterSystem τ) L w)⁻¹ =
      h * (canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) L w)⁻¹) * h⁻¹ by group,
    canonicalRep_conj_rootDiagUnit,
    CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm hh
      (rootDiagUnit_mem_torusGroup (τ := τ) (K := L) (weylTuple w b)),
    mul_inv_cancel_right]

end Torus

namespace ExcCoordDatum

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} (d : ExcCoordDatum S T₀ m)
include d

theorem eq_one_of_forall_rootChar (hsep : ExcRaw.RootSep m) {w : WeylGroup τ}
    (hw : ∀ t : ↥T₀, ∃ b, (t : ModGL τ L) = rootDiagUnit τ b ∧
      ∀ v, rootChar b (w • v) = rootChar b v) :
    w = 1 := by
  have root_single : ∀ (i : ExcRaw.Root m) (k : Fin (ExcRaw.dim m)),
      ExcRaw.root m i (Pi.single k 1) = ((ExcRaw.F m i k : ℤ) : ZMod 3) := by
    intro i k
    rw [ExcRaw.root_apply, Finset.sum_eq_single k]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have key : ∀ (i j : ExcRaw.Root m), w • d.γ i = d.γ j →
      ∀ x : ExcRaw.V m, ExcRaw.root m i x = ExcRaw.root m j x := by
    intro i j h x
    set t : ↥T₀ := Additive.toMul (d.coord.symm x)
    obtain ⟨b, hb, hfix⟩ := hw t
    have hx : d.coord (Additive.ofMul t) = x := by simp [t]
    have h1 : rootChar b (d.γ j) = rootChar b (d.γ i) := by
      rw [← h]
      exact hfix (d.γ i)
    rw [d.rootChar_eq t b hb j, d.rootChar_eq t b hb i, hx] at h1
    exact (zeta_pow_val_injective d.ζ_pow_three d.ζ_ne_one h1).symm
  have keyneg : ∀ (i j : ExcRaw.Root m), w • d.γ i = -d.γ j →
      ∀ x : ExcRaw.V m, ExcRaw.root m i x = - ExcRaw.root m j x := by
    intro i j h x
    set t : ↥T₀ := Additive.toMul (d.coord.symm x)
    obtain ⟨b, hb, hfix⟩ := hw t
    have hx : d.coord (Additive.ofMul t) = x := by simp [t]
    have hneg : rootChar b (-d.γ j) = (rootChar b (d.γ j))⁻¹ := by
      rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]
    have h1 : (rootChar b (d.γ j))⁻¹ = rootChar b (d.γ i) := by
      have h2 := hfix (d.γ i)
      rw [h] at h2
      rwa [hneg] at h2
    rw [d.rootChar_eq t b hb j, d.rootChar_eq t b hb i, hx] at h1
    have hinv : (d.ζ ^ (ExcRaw.root m j x).val)⁻¹ =
        d.ζ ^ (- ExcRaw.root m j x).val := by
      have h := zeta_pow_val_sub_mul (G := Lˣ) d.ζ_pow_three (0 : ZMod 3)
        (ExcRaw.root m j x) 1
      have h0 : (0 : ZMod 3) - ExcRaw.root m j x * ((1 : ℤ) : ZMod 3) =
          - ExcRaw.root m j x := by
        rw [Int.cast_one]
        ring
      rw [h0] at h
      rw [show d.ζ ^ (0 : ZMod 3).val = 1 by simp, one_mul, zpow_neg_one] at h
      exact h.symm
    rw [hinv] at h1
    exact (zeta_pow_val_injective d.ζ_pow_three d.ζ_ne_one h1).symm
  have hfixγ : ∀ i, w • d.γ i = d.γ i := by
    intro i
    obtain ⟨j, hj⟩ := d.exists_eq (w • d.γ i) (IsRoot.smul (d.isRoot i) w)
    rcases hj with h | h
    · have hx := key i j h
      have hF : ∀ k, ((ExcRaw.F m i k : ℤ) : ZMod 3) =
          (1 : ZMod 3) * ((ExcRaw.F m j k : ℤ) : ZMod 3) := by
        intro k
        have hk := hx (Pi.single k 1)
        rw [root_single, root_single] at hk
        simpa [one_mul] using hk
      obtain ⟨hij, -⟩ := hsep i j 1 (Or.inl rfl) hF
      rw [h, hij]
    · have hx := keyneg i j h
      have hF : ∀ k, ((ExcRaw.F m i k : ℤ) : ZMod 3) =
          (-1 : ZMod 3) * ((ExcRaw.F m j k : ℤ) : ZMod 3) := by
        intro k
        have hk := hx (Pi.single k 1)
        rw [root_single, root_single] at hk
        simpa [neg_one_mul] using hk
      obtain ⟨-, hε⟩ := hsep i j (-1) (Or.inr rfl) hF
      exact absurd hε (by decide)
  apply ext_single
  intro k
  obtain ⟨i, hi⟩ := d.exists_eq (Pi.single k 1) (isRoot_single τ k)
  rcases hi with h | h
  · rw [h, hfixγ i, one_smul]
  · rw [h, smul_neg, hfixγ i, one_smul]

section Centralizer


theorem adjointGroup_inf_centralizer (hsep : ExcRaw.RootSep m) :
    adjointGroup τ L ⊓ Subgroup.centralizer (T₀ : Set (ModGL τ L)) = torusGroup τ L := by
  refine adjointGroup_inf_centralizer_of_le_torusGroup d.le_torusGroup (fun δ hδ => ?_)
    fun w hw => d.eq_one_of_forall_rootChar hsep fun t => ?_
  · have hζ2 : d.ζ ^ 2 ≠ 1 := by
      intro h2
      have h' : d.ζ ^ 3 = d.ζ ^ 2 * d.ζ := pow_succ d.ζ 2
      rw [d.ζ_pow_three, h2, one_mul] at h'
      exact d.ζ_ne_one h'.symm
    obtain ⟨i, hi⟩ := d.exists_eq δ hδ
    obtain ⟨b, hb⟩ := d.exists_rootDiagUnit ⟨_, d.coroot_mem i⟩
    have hchar : rootChar b (d.γ i) = d.ζ ^ 2 := by
      have h := d.rootChar_eq _ b hb i
      rw [d.coord_coroot i, ExcRaw.root_coroot] at h
      rwa [show (2 : ZMod 3).val = 2 by decide] at h
    refine ⟨b, hb ▸ d.coroot_mem i, ?_⟩
    rcases hi with rfl | rfl
    · rw [hchar]
      exact hζ2
    · rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul, hchar, Ne, inv_eq_one]
      exact hζ2
  · obtain ⟨b, hb⟩ := d.exists_rootDiagUnit t
    exact ⟨b, hb, hw b (hb ▸ t.2)⟩

theorem map_ggAutomizer_le (hsep : ExcRaw.RootSep m) :
    (ggAutomizer S.Γ T₀).map (ggLin (p := 3) d.coord) ≤ ExcRaw.ambientNormalizer m := by
  rw [ggAutomizer, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨φ, ⟨g, hgΓ, hgN, hgφ⟩, rfl⟩
  obtain ⟨w, hw⟩ := exists_weylTuple_of_mem_normalizer d.le_torusGroup
    (d.adjointGroup_inf_centralizer hsep) ⟨(S.Γ_le_model.trans inf_le_left) hgΓ, hgN⟩
  obtain ⟨M, hM, hMw⟩ := d.exists_weylTuple_mem w
  suffices ggLin (p := 3) d.coord φ = M from this ▸ hM
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨t, rfl⟩ := d.coord.surjective v
  rw [← ofMul_toMul t, ggLin_apply_ofMul]
  obtain ⟨b, hb⟩ := d.exists_rootDiagUnit (Additive.toMul t)
  have hbT : rootDiagUnit τ b ∈ T₀ := hb ▸ (Additive.toMul t).2
  obtain ⟨hmem, hcoord⟩ := hMw b hbT
  have h1 : φ (Additive.toMul t) = ⟨_, hmem⟩ := Subtype.ext (by rw [hgφ, hb, hw])
  have h2 : Additive.toMul t = ⟨_, hbT⟩ := Subtype.ext hb
  rw [h1, hcoord, ← h2]

end Centralizer

end ExcCoordDatum

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
