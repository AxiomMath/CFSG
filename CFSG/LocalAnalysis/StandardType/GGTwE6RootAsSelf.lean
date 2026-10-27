module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcRootAsElt
public import CFSG.LocalAnalysis.StandardType.GGIOneExcLift
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdLayer
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicModelToral
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Assembly CFSG.StandardType TableBSymp

@[expose] def GGEndNodeRootAsSelf (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ A As : Subgroup (MulAut R), IsElemAbelian p A → A < As → IsElemAbelian p As →
    Nat.card As ≤ p * Nat.card A → (As : Set (MulAut R)) ⊆ I →
    p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) →
    GGNoTwoBetween A As →
      ∃ a, GGIsEndNode A a ∧ (p = 3 → GGBigLayer (LargeEvenLayer (ggFix a))) ∧
        ∃ U : Subgroup R, U ≤ LargeEvenLayer (ggFix a) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
          ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U

section Generic

variable {G : Type*} [Group G]

theorem map_ggFix_of_commute {a b : MulAut G} (hab : a * b = b * a) :
    (ggFix b).map a.toMonoidHom = ggFix b := by
  have hab' : a⁻¹ * b = b * a⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hab, mul_assoc, mul_inv_cancel, mul_one]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change b (a y) = a y
    have h := congrArg (fun φ : MulAut G => φ y) hab
    simp only [MulAut.mul_apply] at h
    rw [← h]
    exact congrArg a hy
  · intro hx
    refine ⟨a⁻¹ x, ?_, by simp⟩
    change b (a⁻¹ x) = a⁻¹ x
    have h := congrArg (fun φ : MulAut G => φ x) hab'
    simp only [MulAut.mul_apply] at h
    rw [← h]
    exact congrArg (⇑a⁻¹) hx

theorem apply_mem_largeEvenLayer_ggFix {a b : MulAut G} (hab : a * b = b * a) {x : G}
    (hx : x ∈ LargeEvenLayer (ggFix b)) : a x ∈ LargeEvenLayer (ggFix b) := by
  have h := largeEvenLayer_map_of_injective a.toMonoidHom a.injective (ggFix b)
  rw [map_ggFix_of_commute hab] at h
  rw [h]
  exact ⟨x, hx, rfl⟩

end Generic

theorem ggEndNodeRootAsInn_of_self {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥) (h : GGEndNodeRootAsSelf p r R I) :
    GGEndNodeRootAsInn p r R I := by
  intro L' _ _ ψ hψ hker hperf A As hA hAAs hAs hcardAs hAsI hr h3 hα hnone
  set ρ := ggIE_indAutHom hψ hZ hker with hρ
  have hρinj : Function.Injective ρ := ggIE_indAutHom_injective hψ hZ hker hperf
  have hρapp : ∀ (a : MulAut L') (l : L'), ρ a (ψ l) = ψ (a l) := fun a l =>
    ggIE_indAut_apply hψ hZ hker a l
  set Ab := A.map ρ with hAb
  set Abs := As.map ρ with hAbs
  have hcardAb : Nat.card Ab = Nat.card A := Subgroup.card_map_of_injective hρinj
  have hcardAbs : Nat.card Abs = Nat.card As := Subgroup.card_map_of_injective hρinj
  have hAbAbs : Ab < Abs := lt_of_le_of_ne (Subgroup.map_mono hAAs.le) fun heq =>
    hAAs.ne (Subgroup.map_injective hρinj heq)
  have hAbsI : (Abs : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφI, hφ⟩ := hAsI a ha
    change ggIE_indAut hψ hZ hker a ∈ I
    rwa [← ggIE_eq_indAut_of_forall hψ hZ hker hφ]
  have hUAb : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ Ab, ∀ u ∈ U, a u ∈ U := by
    obtain ⟨U, hU1, hU2, hUA⟩ := hα
    refine ⟨U, hU1, hU2, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    rw [hρapp]
    exact hUA a ha l hu
  have hnoneb : GGNoTwoBetween Ab Abs := by
    intro Eb hAbE hEAbs V hV2 hEV
    by_contra hV1
    set E : Subgroup (MulAut L') := As ⊓ Eb.comap ρ with hE
    have hAE : A ≤ E := fun a ha => ⟨hAAs.le ha, hAbE.le ⟨a, ha, rfl⟩⟩
    obtain ⟨eb, heb, hebA⟩ := SetLike.exists_of_lt hAbE
    obtain ⟨a, ha, rfl⟩ := hEAbs heb
    have hAE' : A < E := lt_of_le_of_ne hAE fun heq => hebA ⟨a, heq ▸ ⟨ha, heb⟩, rfl⟩
    have hVX : V ≤ (⊤ : Subgroup L').map ψ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ]
      exact le_top
    obtain ⟨P, -, hP1, hP2, hPE⟩ := exists_twoSubgroup_lift (S := (E : Set (MulAut L'))) hker
      hV1 hV2 hVX (fun _ _ _ _ => Subgroup.mem_top _) fun e he l hl => by
        rw [← hρapp]
        exact hEV (ρ e) he.2 (ψ l) hl
    exact hP1 (hnone E hAE' inf_le_left P hP2 hPE)
  obtain ⟨ab, ⟨habA, hab1, hcomp, hcent⟩, hbig, V, hVL, hV1, hV2, hVA⟩ :=
    h Ab Abs (ggIE_isElemAbelian_map ρ hA) hAbAbs (ggIE_isElemAbelian_map ρ hAs)
      (by rw [hcardAb, hcardAbs]; exact hcardAs) hAbsI (hcardAb ▸ hr) (hcardAb ▸ h3) hUAb hnoneb
  obtain ⟨a₀, ha₀A, rfl⟩ := habA
  obtain ⟨-, hcompL⟩ := TableBUD.layer_ggFix_lift hψ hker (hρapp a₀) hcomp
  have hmapL : (LargeEvenLayer (ggFix a₀)).map ψ = LargeEvenLayer (ggFix (ρ a₀)) :=
    LayerCC.map_largeEvenLayer_ggFix hψ hker fun x => (hρapp a₀ x).symm
  refine ⟨a₀, ⟨ha₀A, fun h1 => hab1 (by rw [h1, map_one]), hcompL, fun a' ha' => ?_⟩,
    fun hp3 _ => not_largeEvenSmall_of_map_big ψ _ (by rw [hmapL]; exact hbig hp3), ?_⟩
  · constructor
    · intro hfix
      have h1 : ∀ j ∈ LargeEvenLayer (ggFix (ρ a₀)), ρ a' j = j := by
        intro j hj
        rw [← hmapL] at hj
        obtain ⟨k, hk, rfl⟩ := hj
        rw [hρapp, hfix k hk]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ((hcent (ρ a') ⟨a', ha', rfl⟩).mp h1)
      rw [← map_zpow] at hm
      exact Subgroup.mem_zpowers_iff.mpr ⟨m, hρinj hm⟩
    · intro hmem j hj
      exact TableBUD.apply_eq_of_mem_zpowers hmem (hcompL.1 hj)
  · obtain ⟨P, hPX, hP1, hP2, hPA⟩ := exists_twoSubgroup_lift (S := (A : Set (MulAut L'))) hker
      hV1 hV2 (hmapL ▸ hVL)
      (fun a ha x hx => apply_mem_largeEvenLayer_ggFix
        (TableB.IsElemAbelian.comm hA ha ha₀A) hx)
      fun a ha l hl => by
        rw [← hρapp]
        exact hVA (ρ a) ⟨a, ha, rfl⟩ (ψ l) hl
    exact ⟨P, hPX, hP1, hP2, hPA⟩

end CFSG.StandardType.TwE6RootAs

end
