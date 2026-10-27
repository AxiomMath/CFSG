module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Quasithin.Background.HSL
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise Matrix

theorem s16c167_natAct_fixed_eq_one {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n)
    {m : Multiplicative (Fin n → K)}
    (hm : ∀ γ : ↥(StatedSL n K), natAct (StatedSL n K) γ m = m) : m = 1 := by
  show Multiplicative.toAdd m = 0
  by_contra hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hne : ∃ i : Fin n, i ≠ j := by
    by_cases h : j = (⟨0, by omega⟩ : Fin n)
    · exact ⟨(⟨1, by omega⟩ : Fin n), by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨(⟨0, by omega⟩ : Fin n), Ne.symm h⟩
  obtain ⟨i, hij⟩ := hne
  let A : Matrix.GeneralLinearGroup (Fin n) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j (1 : K))
      (by rw [Matrix.det_transvection_of_ne i j hij (1 : K)]; exact one_ne_zero)
  have hmem : A ∈ StatedSL n K :=
    Subgroup.subset_closure (by
      change (Matrix.transvection i j (1 : K)).det = 1
      exact Matrix.det_transvection_of_ne i j hij (1 : K))
  have hfix : Matrix.transvection i j (1 : K) *ᵥ Multiplicative.toAdd m =
      Multiplicative.toAdd m := by
    have h2 := congrArg Multiplicative.toAdd (hm ⟨A, hmem⟩)
    simpa [natAct, A, Matrix.GeneralLinearGroup.mkOfDetNeZero] using h2
  have hsum : Multiplicative.toAdd m +
      Pi.single i (1 * Multiplicative.toAdd m j) = Multiplicative.toAdd m := by
    rw [← CFSG.Quasithin.H.transvection_mulVec i j (1 : K) (Multiplicative.toAdd m)]
    exact hfix
  have hco := congrFun hsum i
  simp only [Pi.add_apply, Pi.single_eq_same, one_mul] at hco
  have h0 : Multiplicative.toAdd m j = 0 := by
    have h4 : Multiplicative.toAdd m i + Multiplicative.toAdd m j =
        Multiplicative.toAdd m i + (0 : K) := by rw [hco, add_zero]
    exact add_left_cancel_iff.1 h4
  exact hj h0

theorem s16c167_inf_fixV_eq_bot_of_binaryNaturalSL {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U : Subgroup W} {n : ℕ} (hn : 2 ≤ n)
    (h : BinaryNaturalSL H U ⊥ n 1) : U ⊓ fixV H = ⊥ := by
  obtain ⟨K, hK, hKf, hK2, π, hπ⟩ := h
  letI := hK
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, -, hβk, hβe⟩ := R.exists_β
  refine le_bot_iff.1 fun w hw => ?_
  obtain ⟨hwU, hwfix⟩ := Subgroup.mem_inf.1 hw
  have hbeta : β ⟨w, hwU⟩ = 1 := by
    apply s16c167_natAct_fixed_eq_one hn
    intro γ
    have hfix : ((π γ : ↥H) : MulAut W) w = w :=
      (mem_fixV.1 hwfix) (π γ) (π γ).2
    have hu : ((π γ : ↥H) : MulAut W) w ∈ U := by rw [hfix]; exact hwU
    have he := hβe γ ⟨w, hwU⟩ hu
    have hsub : β ⟨((π γ : ↥H) : MulAut W) (⟨w, hwU⟩ : ↥U), hu⟩ = β ⟨w, hwU⟩ :=
      congrArg β (Subtype.ext hfix)
    exact he.symm.trans hsub
  exact (hβk ⟨w, hwU⟩).1 hbeta

private theorem stable_of_binaryNaturalSL {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {n a : ℕ} (h : BinaryNaturalSL H U Z n a) :
    ∀ x : ↥H, ∀ u ∈ U, (x : MulAut W) u ∈ U := by
  obtain ⟨K, hK, hKf, hK2, π, hπ⟩ := h
  exact (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).U_inv

private theorem iSup_stable_of_stable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {ι : Sort*} {f : ι → Subgroup W}
    (hf : ∀ i, ∀ x : ↥H, ∀ u ∈ f i, (x : MulAut W) u ∈ f i) :
    ∀ x : ↥H, ∀ u ∈ (⨆ i, f i), (x : MulAut W) u ∈ (⨆ i, f i) := by
  intro x u hu
  refine Subgroup.iSup_induction f hu (C := fun z => (x : MulAut W) z ∈ ⨆ i, f i) ?_ ?_ ?_
  · intro i z hz
    exact le_iSup f i (hf i x z hz)
  · rw [map_one]
    exact Subgroup.one_mem (⨆ i, f i)
  · intro a b ha hb
    rw [map_mul]
    exact Subgroup.mul_mem (⨆ i, f i) ha hb

theorem s16c167_inf_fixV_eq_bot_of_sumOfNat {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U : Subgroup W} {n k : ℕ} (hn : 2 ≤ n)
    (h : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) H U ⊥ k) : U ⊓ fixV H = ⊥ := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have hIstable : ∀ i, ∀ x : ↥H, ∀ u ∈ I i, (x : MulAut W) u ∈ I i :=
    fun i => stable_of_binaryNaturalSL (hnat i)
  have hIinf : ∀ i, I i ⊓ fixV H = ⊥ :=
    fun i => s16c167_inf_fixV_eq_bot_of_binaryNaturalSL hn (hnat i)
  have hfin : ∀ s : Finset (Fin k), (⨆ i ∈ s, I i) ⊓ fixV H = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hbot : (⨆ i ∈ (∅ : Finset (Fin k)), I i) = ⊥ := by
          refine iSup_eq_bot.2 fun i => iSup_eq_bot.2 fun hi => ?_
          exact absurd hi (Finset.notMem_empty i)
        rw [hbot, bot_inf_eq]
    | insert a s has ih =>
        rw [Finset.iSup_insert]
        have hTstable : ∀ x : ↥H, ∀ u ∈ (⨆ i ∈ s, I i),
            (x : MulAut W) u ∈ ⨆ i ∈ s, I i :=
          iSup_stable_of_stable (f := fun i : Fin k => ⨆ (_ : i ∈ s), I i)
            (fun i => iSup_stable_of_stable (f := fun _ : (i ∈ s) => I i)
              (fun _ => hIstable i))
        have hTX : (⨆ i ∈ s, I i) ≤ ⨆ (j : Fin k) (_ : j ≠ a), I j := by
          refine iSup_le fun i => iSup_le fun his => ?_
          exact le_iSup₂ (f := fun j (_ : j ≠ a) => I j) i (fun hia => has (hia ▸ his))
        have hhind : I a ⊓ (⨆ (j : Fin k) (_ : j ≠ a), I j) ≤ ⊥ := by
          have hh := hind a
          rwa [bot_sup_eq] at hh
        refine le_bot_iff.1 fun x hx => ?_
        obtain ⟨hxU, hxfix⟩ := Subgroup.mem_inf.1 hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hxU
        have hy_eq : ∀ h : MulAut W, h ∈ H → h y = y := by
          intro h hh
          have h1 : h y * h z = y * z := by
            rw [← map_mul]
            exact (mem_fixV.1 hxfix) h hh
          have hcomm : (h y)⁻¹ * y = h z * z⁻¹ := by
            have h2 : h z = (h y)⁻¹ * (y * z) := by rw [← h1]; group
            rw [h2]; group
          have hmemIT : (h y)⁻¹ * y ∈ I a ⊓ (⨆ i ∈ s, I i) := by
            refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
            · exact Subgroup.mul_mem (I a) (Subgroup.inv_mem (I a) (hIstable a ⟨h, hh⟩ y hy)) hy
            · rw [hcomm]
              exact Subgroup.mul_mem (⨆ i ∈ s, I i) (hTstable ⟨h, hh⟩ z hz)
                (Subgroup.inv_mem (⨆ i ∈ s, I i) hz)
          have hleX : I a ⊓ (⨆ i ∈ s, I i) ≤ I a ⊓ (⨆ (j : Fin k) (_ : j ≠ a), I j) :=
            le_inf inf_le_left (le_trans inf_le_right hTX)
          exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 (hhind (hleX hmemIT)))
        have hz_eq : ∀ h : MulAut W, h ∈ H → h z = z := by
          intro h hh
          have h1 : h y * h z = y * z := by
            rw [← map_mul]
            exact (mem_fixV.1 hxfix) h hh
          rw [hy_eq h hh] at h1
          exact mul_left_cancel_iff.1 h1
        have hyfix : y ∈ fixV H := mem_fixV.2 hy_eq
        have hzfix : z ∈ fixV H := mem_fixV.2 hz_eq
        have hybot : y ∈ (⊥ : Subgroup W) := by
          rw [← hIinf a]
          exact Subgroup.mem_inf.2 ⟨hy, hyfix⟩
        have hzbot : z ∈ (⊥ : Subgroup W) := by
          rw [← ih]
          exact Subgroup.mem_inf.2 ⟨hz, hzfix⟩
        have hprod : y * z = 1 := by
          rw [Subgroup.mem_bot.1 hybot, Subgroup.mem_bot.1 hzbot, mul_one]
        rw [hprod]
        exact Subgroup.one_mem (⊥ : Subgroup W)
  have huniv : (⨆ i ∈ (Finset.univ : Finset (Fin k)), I i) = ⨆ i, I i := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i => iSup_le fun _ => le_iSup (fun i => I i) i
    · exact iSup_le fun i =>
        le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => I i) i
          (Finset.mem_univ i)
  have hsup' : U = ⨆ i, I i := by rw [← hsup, bot_sup_eq]
  rw [hsup', ← huniv]
  exact hfin Finset.univ

variable {G : Type} [Group G] [Finite G]

theorem s16c167_v1Sub_eq_bot_of_case9 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h0 : V₀ = ⊥) (h9 : Case168_9 D V₀ V hV L) :
    v1Sub D.M V₀ V hV L = ⊥ := by
  subst h0
  obtain ⟨-, -, -, hsum, -⟩ := h9
  have hwTil : wTil (⊥ : Subgroup G) V hV L ⊓ fixV (lBar (⊥ : Subgroup G) V hV L) = ⊥ :=
    s16c167_inf_fixV_eq_bot_of_sumOfNat (n := 3) (k := 3) (by norm_num) hsum
  have hwSub : wSub (⊥ : Subgroup G) V hV L ⊓ centralizer (L : Set G) = ⊥ := by
    refine le_bot_iff.1 fun w hw => ?_
    obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨x, rfl, hx⟩ :=
      (mem_preTil (⊥ : Subgroup G) V hV (wTil (⊥ : Subgroup G) V hV L)).1 hwW
    have hxfix : mkTil (⊥ : Subgroup G) V hV x ∈ fixV (lBar (⊥ : Subgroup G) V hV L) := by
      rw [mem_fixV]
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := (mem_barSub (⊥ : Subgroup G) V hV L φ).1 hφ
      rw [actTil_mk]
      have hxfixval : actStab (⊥ : Subgroup G) V hV g x = x := by
        refine IntMod.val_injective ?_
        rw [actStab_apply_val]
        have hcomm : (g : G) * x.val = x.val * (g : G) :=
          (Subgroup.mem_centralizer_iff.1 hwC) (g : G) hg
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [hxfixval]
    have hxbot : mkTil (⊥ : Subgroup G) V hV x ∈
        (⊥ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) := by
      rw [← hwTil]
      exact Subgroup.mem_inf.2 ⟨hx, hxfix⟩
    have hone : mkTil (⊥ : Subgroup G) V hV x = 1 := Subgroup.mem_bot.1 hxbot
    have h1 : mkTil (⊥ : Subgroup G) V hV x =
        mkTil (⊥ : Subgroup G) V hV (1 : IntMod V hV) := by
      rw [map_one]
      exact hone
    have h2 := (mkTil_eq_iff (⊥ : Subgroup G) V hV x 1).1 h1
    simpa using h2
  rw [v1Sub_of_eq_bot D.M (⊥ : Subgroup G) V hV L rfl]
  exact iSup_eq_bot.2 fun m => conjSubgroup_eq_bot_iff.2 hwSub

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
