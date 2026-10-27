module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Nat

variable {W : Type} [CommGroup W]

theorem s16e_inf_fixV_eq_bot_of_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut W)} {U : Subgroup W}
    (h : (FFModel.nat Γ).Realizes H U ⊥)
    (hΓ : ∀ m : Multiplicative (ι → K), (∀ γ : ↥Γ, natAct Γ γ m = m) → m = 1) :
    U ⊓ fixV H = ⊥ := by
  obtain ⟨π, hπ⟩ := h
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, -, hβk, hβe⟩ := R.exists_β
  refine le_bot_iff.1 fun w hw => ?_
  obtain ⟨hwU, hwfix⟩ := Subgroup.mem_inf.1 hw
  have hbeta : β ⟨w, hwU⟩ = 1 := by
    apply hΓ
    intro γ
    have hfix : ((π γ : ↥H) : MulAut W) w = w :=
      (mem_fixV.1 hwfix) (π γ) (π γ).2
    have hu : ((π γ : ↥H) : MulAut W) w ∈ U := by rw [hfix]; exact hwU
    have he := hβe γ ⟨w, hwU⟩ hu
    have hsub : β ⟨((π γ : ↥H) : MulAut W) (⟨w, hwU⟩ : ↥U), hu⟩ = β ⟨w, hwU⟩ :=
      congrArg β (Subtype.ext hfix)
    exact he.symm.trans hsub
  exact (hβk ⟨w, hwU⟩).1 hbeta

end Nat

section Sum

variable {W : Type} [CommGroup W]

private theorem s16e_sum_iSup_stable {H : Subgroup (MulAut W)} {ι : Sort*} {f : ι → Subgroup W}
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

theorem s16e_inf_fixV_eq_bot_of_sumOfNat
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    {U : Subgroup W} {k : ℕ}
    (hstab : ∀ I : Subgroup W, N H I ⊥ → ∀ x : ↥H, ∀ u ∈ I, (x : MulAut W) u ∈ I)
    (hfix : ∀ I : Subgroup W, N H I ⊥ → I ⊓ fixV H = ⊥) (h : SumOfNat N H U ⊥ k) :
    U ⊓ fixV H = ⊥ := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have hIstable : ∀ i, ∀ x : ↥H, ∀ u ∈ I i, (x : MulAut W) u ∈ I i :=
    fun i => hstab _ (hnat i)
  have hIinf : ∀ i, I i ⊓ fixV H = ⊥ := fun i => hfix _ (hnat i)
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
        have hTstable : ∀ x : ↥H, ∀ u ∈ (⨆ i ∈ s, I i), (x : MulAut W) u ∈ ⨆ i ∈ s, I i :=
          s16e_sum_iSup_stable (f := fun i : Fin k => ⨆ (_ : i ∈ s), I i)
            (fun i => s16e_sum_iSup_stable (f := fun _ : (i ∈ s) => I i)
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

end Sum

section Rank

variable {W : Type} [CommGroup W] [Finite W]

theorem s16e_rk_sumOfNat_ge
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    {U : Subgroup W} {k b : ℕ} (hN : ∀ I : Subgroup W, N H I ⊥ → b ≤ rk ↥I)
    (h : SumOfNat N H U ⊥ k) : k * b ≤ rk ↥U := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have hfin : ∀ s : Finset (Fin k), s.card * b ≤ rk ↥(⨆ i ∈ s, I i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hbot : (⨆ i ∈ (∅ : Finset (Fin k)), I i) = ⊥ := by
          refine iSup_eq_bot.2 fun i => iSup_eq_bot.2 fun hi => ?_
          exact absurd hi (Finset.notMem_empty i)
        rw [hbot]
        simp
    | insert a s has ih =>
        rw [Finset.iSup_insert, Finset.card_insert_of_notMem has]
        have hTX : (⨆ i ∈ s, I i) ≤ ⨆ (j : Fin k) (_ : j ≠ a), I j := by
          refine iSup_le fun i => iSup_le fun his => ?_
          exact le_iSup₂ (f := fun j (_ : j ≠ a) => I j) i (fun hia => has (hia ▸ his))
        have hhind : I a ⊓ (⨆ (j : Fin k) (_ : j ≠ a), I j) ≤ ⊥ := by
          have hh := hind a
          rwa [bot_sup_eq] at hh
        have hinf : I a ⊓ (⨆ i ∈ s, I i) = ⊥ :=
          le_bot_iff.1 (le_trans (inf_le_inf_left _ hTX) hhind)
        have h2 := rk_sup_add_rk_inf (I a) (⨆ i ∈ s, I i)
        rw [hinf, rk_bot] at h2
        have h3 := hN _ (hnat a)
        have h4 : (s.card + 1) * b = s.card * b + b := by ring
        omega
  have huniv : (⨆ i ∈ (Finset.univ : Finset (Fin k)), I i) = ⨆ i, I i := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i => iSup_le fun _ => le_iSup (fun i => I i) i
    · exact iSup_le fun i =>
        le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => I i) i
          (Finset.mem_univ i)
  have hsup' : U = ⨆ i, I i := by rw [← hsup, bot_sup_eq]
  have h5 := hfin Finset.univ
  rw [huniv, ← hsup', Finset.card_univ, Fintype.card_fin] at h5
  exact h5

end Rank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
