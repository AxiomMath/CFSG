module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.B2FactorizationBridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section Baumann

variable {G : Type} [Group G] [Finite G] {V R : Subgroup G} (hV : IsElemAbelian 2 V)

theorem thompsonJ_le (R : Subgroup G) : thompsonJ R ≤ R :=
  iSup_le fun _ => iSup_le fun hA => hA.1

theorem thompsonJ_le_baum (R : Subgroup G) : thompsonJ R ≤ baum R := by
  refine le_inf (thompsonJ_le R) ?_
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  exact (Subgroup.closure_le (centerOf (thompsonJ R))).mpr (fun _ hy => hy.1) hx |>.2

theorem autI_baum_fix (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    {s : MulAut (IntMod V hV)} (hs : s ∈ autI hV (baum R)) {v : IntMod V hV}
    (hv : v ∈ fixV (autI hV (thompsonJ R))) : s v = v := by
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hs
  have hJN : thompsonJ R ≤ Subgroup.normalizer (V : Set G) := (thompsonJ_le R).trans hRN
  have hvC : v.val ∈ Subgroup.centralizer (thompsonJ R : Set G) := (mem_fixV_autI hV hJN v).1 hv
  have hvmem : v.val ∈ omegaOneCenterOf (thompsonJ R) := by
    rw [← (omegaOne_centralizer_thompsonJ R).1]
    exact Subgroup.subset_closure ⟨⟨hVR v.val_mem, hvC⟩, by
      simpa [pow_two] using hV.2 v.val v.val_mem⟩
  refine IntMod.val_injective ?_
  rw [convI_apply_val]
  have := Subgroup.mem_centralizer_iff.1 hg.2 v.val hvmem
  rw [← this, mul_inv_cancel_right]

end Baumann

section FixV

variable {W : Type*} [CommGroup W]

theorem mem_fixV_iSup {ι : Sort*} (A : ι → Subgroup (MulAut W)) {u : W}
    (h : ∀ i, u ∈ fixV (A i)) : u ∈ fixV (⨆ i, A i) := by
  intro g hg
  refine Subgroup.iSup_induction A (C := fun g => g u = u) hg (fun i x hx => h i x hx) ?_ ?_
  · rfl
  · intro x y hx hy
    rw [MulAut.mul_apply, hy, hx]

theorem apply_mem_commV {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) {u : W} (hu : u ∈ commV L) :
    g u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hg hu

theorem card_le_card_mul_inf [Finite W] (U : Subgroup W) (A : Subgroup (MulAut W))
    (h : Nat.card W ≤ Nat.card A * Nat.card (fixV A)) :
    Nat.card U ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U) := by
  have hprod : Nat.card ↥(U ⊔ fixV A) * Nat.card ↥(U ⊓ fixV A) =
      Nat.card U * Nat.card (fixV A) :=
    B2F.card_sup_mul_card_inf_of_commute fun a ha b hb => mul_comm a b
  have hle : Nat.card ↥(U ⊔ fixV A) ≤ Nat.card W := Subgroup.card_le_card_group _
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  rw [inf_comm] at hprod
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card U * Nat.card (fixV A) = Nat.card ↥(U ⊔ fixV A) * Nat.card ↥(fixV A ⊓ U) :=
        hprod.symm
    _ ≤ Nat.card W * Nat.card ↥(fixV A ⊓ U) := Nat.mul_le_mul_right _ hle
    _ ≤ (Nat.card A * Nat.card (fixV A)) * Nat.card ↥(fixV A ⊓ U) :=
        Nat.mul_le_mul_right _ h
    _ = Nat.card A * Nat.card ↥(fixV A ⊓ U) * Nat.card (fixV A) := by ring

end FixV

section Transport

variable {W : Type*} [CommGroup W] {m : ℕ} {Xs : Subgroup (MulAut W)}

@[expose] def Bmap (ι : ↥Xs →* Perm (Fin m)) (A : Subgroup (MulAut W)) : Subgroup (Perm (Fin m)) :=
  (A.subgroupOf Xs).map ι

theorem mem_Bmap {ι : ↥Xs →* Perm (Fin m)} {A : Subgroup (MulAut W)} {σ : Perm (Fin m)} :
    σ ∈ Bmap ι A ↔ ∃ g : ↥Xs, (g : MulAut W) ∈ A ∧ ι g = σ := by
  unfold Bmap
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem Bmap_mono (ι : ↥Xs →* Perm (Fin m)) {A A' : Subgroup (MulAut W)} (h : A ≤ A') :
    Bmap ι A ≤ Bmap ι A' := Subgroup.map_mono fun _ hx => h hx

theorem Bmap_bot (ι : ↥Xs →* Perm (Fin m)) :
    Bmap ι (⊥ : Subgroup (MulAut W)) = ⊥ := by
  ext σ
  rw [mem_Bmap, Subgroup.mem_bot]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have : g = 1 := Subtype.ext (Subgroup.mem_bot.1 hg)
    rw [this, map_one]
  · rintro rfl
    exact ⟨1, Subgroup.one_mem _, map_one _⟩

theorem Bmap_iSup (ι : ↥Xs →* Perm (Fin m)) {ι' : Sort*} (A : ι' → Subgroup (MulAut W))
    (hA : ∀ i, A i ≤ Xs) : Bmap ι (⨆ i, A i) = ⨆ i, Bmap ι (A i) := by
  unfold Bmap
  have h : (⨆ i, A i).subgroupOf Xs = ⨆ i, (A i).subgroupOf Xs := by
    apply Subgroup.map_injective Xs.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hA), Subgroup.map_iSup]
    exact iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hA i)).symm
  rw [h, Subgroup.map_iSup]

theorem card_Bmap (ι : ↥Xs →* Perm (Fin m)) (hι : Function.Injective ι)
    {A : Subgroup (MulAut W)} (hA : A ≤ Xs) : Nat.card (Bmap ι A) = Nat.card A := by
  unfold Bmap
  rw [Subgroup.card_map_of_injective hι]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

end Transport

end CFSG.Quasithin.C124.YZ
