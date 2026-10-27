module

public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6
public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6Quot
public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Auto
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelClassify
public import CFSG.RankThree.E6.LargePrimeStabilizers

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem mulAut_conj_conj {G : Type*} [Group G] (φ : MulAut G) (v : G) :
    φ * MulAut.conj v * φ⁻¹ = MulAut.conj (φ v) := by
  ext x
  simp [MulAut.conj_apply]

private theorem diag_eq_ad {R : Type} [Group R] (D : E6ThreeModel.FrameData R)
    (m : Multiplicative (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ZMod 3)) :
    D.diag m = D.ad (Multiplicative.toAdd m) := by
  simp [E6ThreeModel.FrameData.ad, ofAdd_toAdd]

private theorem relIndex_inf_eq_relIndex_sup {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) [A.Normal] :
    B.relIndex A = B.relIndex (A ⊔ B) := by
  set S := A ⊔ B
  have hA : A.relIndex B = A.relIndex S :=
    (Subgroup.relIndex_sup_left (K := A) (H := B)).symm
  have h1 := Subgroup.index_inf (H := B) (K := A)
  have h2 := Subgroup.index_inf (H := A) (K := B)
  rw [inf_comm] at h1
  have hAi : A.relIndex S * S.index = A.index := Subgroup.relIndex_mul_index le_sup_left
  have hBi : B.relIndex S * S.index = B.index := Subgroup.relIndex_mul_index le_sup_right
  have key : B.relIndex A * A.index = A.relIndex B * B.index := by rw [← h1, h2]
  rw [hA, ← hAi, ← hBi] at key
  have key2 : B.relIndex A * (A.relIndex S * S.index) =
      B.relIndex S * (A.relIndex S * S.index) := by
    rw [key]
    ac_rfl
  have hne : A.relIndex S * S.index ≠ 0 := by
    refine Nat.mul_ne_zero ?_ ?_
    · exact Subgroup.index_ne_zero_of_finite
    · exact Subgroup.index_ne_zero_of_finite
  exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hne) key2

private theorem card_mul_card_range_dvd_of_le_ker {G : Type*} [Group G] (N X : Subgroup G)
    {α : Type*} (ρ : N →* Equiv.Perm α) (hXN : X ≤ N) (hX : X.subgroupOf N ≤ ρ.ker) :
    Nat.card X * Nat.card ρ.range ∣ Nat.card N := by
  have hdvd : Nat.card (X.subgroupOf N) ∣ Nat.card ρ.ker := Subgroup.card_dvd_of_le hX
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv] at hdvd
  rw [← Subgroup.card_ker_mul_card_range ρ]
  exact mul_dvd_mul_right hdvd _

theorem not_three_dvd_relIndex_automizer_twE6
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) {A : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hA : IsElemAbelian 3 A)
    (hI : (A : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n) (hr : Nat.card A = 3 ^ 6) :
    ¬ 3 ∣ ((MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range ⊓
        Subgroup.normalizer (A : Set (MulAut (TwE6Delta.RecipeR K n)))).relIndex
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range := by
  classical
  let R := TwE6Delta.RecipeR K n
  let G := MulAut R
  haveI : Finite R := by dsimp [R]; exact TwE6Delta.finite_recipeR hK
  haveI : Fintype R := Fintype.ofFinite R
  haveI : Finite G := by dsimp [G]; infer_instance
  obtain ⟨D, X, hGood, hDH, hHnum, hH3R, hXH, hXcard, hXcent, hXnotInn, -⟩ :=
    exists_langFrame_recipeR n hn hK h3
  have hAH : A ≤ D.H := by
    intro x hx
    have hxI : x ∈ (D.H : Set G) := by
      rw [hDH]
      exact hI hx
    exact hxI
  obtain ⟨γ, hγH, hγshape⟩ := hGood.shape A hAH hA (by rw [hr]; norm_num)
  set V : Subgroup G := D.diag.range with hVdef
  set A' : Subgroup G := A.map (MulAut.conj γ).toMonoidHom with hA'def
  have hA'V : A' ≤ V := by
    intro a' ha'
    rw [hA'def] at ha'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 ha'
    simpa [MulAut.conj_apply] using hγshape a ha
  have hcardA' : Nat.card A' = 3 ^ 6 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective, hr]
  have hVcard : Nat.card V = 3 ^ 6 := by
    rw [hVdef]
    have h : Nat.card D.diag.range =
        Nat.card (Multiplicative (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ZMod 3)) := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hGood.faithful,
        Subgroup.card_top]
    rw [h, Nat.card_congr Multiplicative.toAdd]
    norm_num [Nat.card_fun, ZMod.card, CFSG.Blueprint.Chevalley.Tag.rank]
  have hA'eq : A' = V :=
    Subgroup.eq_of_le_of_card_ge hA'V (le_of_eq (hVcard.trans hcardA'.symm))
  have hnbH : ∀ i, MulAut.conj (D.nb i) ∈ D.H := by
    intro i
    have hmem : MulAut.conj (D.nb i) ∈ (D.H : Set G) := by
      rw [hDH]
      exact Subgroup.subset_closure (Set.mem_union_left _ ⟨D.nb i, rfl⟩)
    exact hmem
  have hVnorm : ∀ i, MulAut.conj (D.nb i) ∈ Subgroup.normalizer (V : Set G) := by
    intro i
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : V.map (MulAut.conj (MulAut.conj (D.nb i))).toMonoidHom ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      rw [hVdef] at hv ⊢
      obtain ⟨m, rfl⟩ := hv
      rw [show (MulAut.conj (MulAut.conj (D.nb i))).toMonoidHom (D.diag m) =
          D.ad (TableBExc.E6Three.adRefl .E6 3 i (Multiplicative.toAdd m)) by
        rw [diag_eq_ad]
        exact hGood.weyl.2.2.1 i (Multiplicative.toAdd m)]
      exact ⟨Multiplicative.ofAdd _, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective
        (MulAut.conj (MulAut.conj (D.nb i))).injective).symm)
  have hXnormV : X ≤ Subgroup.normalizer (V : Set G) := by
    refine Subgroup.le_normalizer_iff.2 ?_
    intro x hx v hv
    have hcomm := hXcent x hx v hv
    have heq : x * v * x⁻¹ = v := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [heq]
    exact hv
  set Nbig : Subgroup G :=
    Subgroup.closure ((X : Set G) ∪ Set.range (fun i : Fin (CFSG.Blueprint.Chevalley.Tag.E6.rank) => MulAut.conj (D.nb i)))
    with hNbigdef
  have hXNbig : X ≤ Nbig := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hnbNbig : ∀ i, MulAut.conj (D.nb i) ∈ Nbig := fun i =>
    Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hNbigH : Nbig ≤ D.H := by
    refine (Subgroup.closure_le D.H).2 ?_
    rintro z (hz | hz)
    · exact hXH hz
    · obtain ⟨i, rfl⟩ := hz
      exact hnbH i
  have hNbigNormV : Nbig ≤ Subgroup.normalizer (V : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro z (hz | hz)
    · exact hXnormV hz
    · obtain ⟨i, rfl⟩ := hz
      exact hVnorm i
  have hXnormA' : X ≤ Subgroup.normalizer (A' : Set G) := by
    refine Subgroup.le_normalizer_iff.2 ?_
    intro x hx a' ha'
    have ha'V : a' ∈ V := hA'V ha'
    have hcomm := hXcent x hx a' ha'V
    have heq : x * a' * x⁻¹ = a' := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [heq]
    exact ha'
  have hNbigNormA' : Nbig ≤ Subgroup.normalizer (A' : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro z (hz | hz)
    · exact hXnormA' hz
    · obtain ⟨i, rfl⟩ := hz
      rw [hA'eq]
      exact hVnorm i
  let f : (Fin (CFSG.Blueprint.Chevalley.Tag.E6.rank) → ZMod 3) → V :=
    fun x => ⟨D.ad x, ⟨Multiplicative.ofAdd x, rfl⟩⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : D.ad x = D.ad y := Subtype.ext_iff.mp hxy
    exact Multiplicative.ofAdd.injective (hGood.faithful h1)
  have hfsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rw [hVdef] at hv
    obtain ⟨m, rfl⟩ := hv
    refine ⟨Multiplicative.toAdd m, ?_⟩
    apply Subtype.ext
    change D.ad (Multiplicative.toAdd m) = D.diag m
    exact (diag_eq_ad D m).symm
  let e : (Fin (CFSG.Blueprint.Chevalley.Tag.E6.rank) → ZMod 3) ≃ V := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  let ρ : Nbig →* Equiv.Perm (Fin (CFSG.Blueprint.Chevalley.Tag.E6.rank) → ZMod 3) :=
    (e.permCongrHom.symm).toMonoidHom.comp
      ((MulAut.toPerm V : MulAut V →* Equiv.Perm V).comp
        ((Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hNbigNormV)))
  have hρapply : ∀ (n : Nbig) (y : Fin (CFSG.Blueprint.Chevalley.Tag.E6.rank) → ZMod 3),
      ρ n y = e.symm ((Subgroup.normalizerMonoidHom V (Subgroup.inclusion hNbigNormV n)) (e y)) := by
    intro n y
    rfl
  have hXker : X.subgroupOf Nbig ≤ ρ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro y
    have hn' : (n : G) ∈ X := Subgroup.mem_subgroupOf.1 hn
    have hcy : (Subgroup.normalizerMonoidHom V (Subgroup.inclusion hNbigNormV n)) (e y) = e y := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change (n : G) * (e y) * (n : G)⁻¹ = e y
      have hcomm := hXcent (n : G) hn' (e y) (e y).2
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hρapply n y, hcy, Equiv.symm_apply_apply]
    rfl
  have hρnb : ∀ (i : Fin (CFSG.Blueprint.Chevalley.Tag.E6.rank)),
      ρ ⟨MulAut.conj (D.nb i), hnbNbig i⟩ =
      TableBExc.E6Three.adPerm .E6 3 (CFSG.LieType.Chevalley.simple .E6 i) := by
    intro i
    apply Equiv.ext
    intro y
    have hcy : (Subgroup.normalizerMonoidHom V
        (Subgroup.inclusion hNbigNormV ⟨MulAut.conj (D.nb i), hnbNbig i⟩)) (e y) =
        e (TableBExc.E6Three.adRefl .E6 3 i y) := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change MulAut.conj (D.nb i) * D.ad y * (MulAut.conj (D.nb i))⁻¹ =
        D.ad (TableBExc.E6Three.adRefl .E6 3 i y)
      exact hGood.weyl.2.2.1 i y
    rw [hρapply ⟨MulAut.conj (D.nb i), hnbNbig i⟩ y, hcy]
    have hs : e.symm (e (TableBExc.E6Three.adRefl .E6 3 i y)) =
        TableBExc.E6Three.adRefl .E6 3 i y := Equiv.symm_apply_apply e _
    rw [hs]
    change TableBExc.E6Three.adRefl .E6 3 i y =
      TableBExc.E6Three.adAct .E6 3 (CFSG.LieType.Chevalley.simple .E6 i) y
    rw [TableBExc.E6Three.adAct_simple]
  have hWle : (TableBExc.E6Three.adPerm .E6 3).range ≤ ρ.range := by
    rintro z ⟨w, rfl⟩
    refine TableBExc.E6Three.weyl_induction
      (P := fun w => TableBExc.E6Three.adPerm .E6 3 w ∈ ρ.range) ?_ ?_ w
    · refine ⟨1, ?_⟩
      rw [map_one, map_one]
    · intro i w hw
      obtain ⟨n, hn⟩ := hw
      refine ⟨⟨MulAut.conj (D.nb i), hnbNbig i⟩ * n, ?_⟩
      calc ρ (⟨MulAut.conj (D.nb i), hnbNbig i⟩ * n)
          = ρ ⟨MulAut.conj (D.nb i), hnbNbig i⟩ * ρ n := map_mul ρ _ _
        _ = TableBExc.E6Three.adPerm .E6 3 (CFSG.LieType.Chevalley.simple .E6 i) *
              TableBExc.E6Three.adPerm .E6 3 w := by
          rw [hρnb i, hn]
        _ = TableBExc.E6Three.adPerm .E6 3
              (CFSG.LieType.Chevalley.simple .E6 i * w) := (map_mul _ _ _).symm
  have hInj : Function.Injective (TableBExc.E6Three.adPerm .E6 3) := by
    intro w w' h
    have h1 : TableBExc.E6Three.adPerm .E6 3 (w'⁻¹ * w) = 1 := by
      rw [map_mul, map_inv, h]
      exact inv_mul_cancel _
    have h2 : w'⁻¹ * w = 1 := by
      apply TableBExc.E6Three.eq_one_of_adAct_eq_on_hypE6
      intro x hx
      rw [← TableBExc.E6Three.adPerm_apply]
      exact Equiv.Perm.congr_fun h1 x
    exact (inv_mul_eq_one.mp h2).symm
  have hWcard : Nat.card (TableBExc.E6Three.adPerm .E6 3).range = 51840 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hInj, Subgroup.card_top]
    exact CFSG.RankThree.E6.card_weylGroup_E6
  have hcount : Nat.card X * Nat.card ρ.range ∣ Nat.card Nbig :=
    card_mul_card_range_dvd_of_le_ker Nbig X ρ hXNbig hXker
  have hWrange_dvd : 51840 ∣ Nat.card ρ.range := by
    have h := Subgroup.card_dvd_of_le hWle
    rwa [hWcard] at h
  have hNbigbig : (2 ^ n + 1) ^ 6 * 51840 ∣ Nat.card Nbig := by
    rw [← hXcard]
    exact (mul_dvd_mul_left _ hWrange_dvd).trans hcount
  set N' : Subgroup G := D.H ⊓ Subgroup.normalizer (A' : Set G) with hN'def
  have hNbigN' : Nbig ≤ N' := le_inf hNbigH hNbigNormA'
  have hN'big : (2 ^ n + 1) ^ 6 * 51840 ∣ Nat.card N' :=
    hNbigbig.trans (Subgroup.card_dvd_of_le hNbigN')
  set K : Subgroup G := D.H ⊓ Subgroup.normalizer (A : Set G) with hKdef
  have hmapH : D.H.map (MulAut.conj γ).toMonoidHom = D.H := by
    have hle : D.H.map (MulAut.conj γ).toMonoidHom ≤ D.H := by
      rintro _ ⟨x, hx, rfl⟩
      have happ : (MulAut.conj γ).toMonoidHom x = γ * x * γ⁻¹ := by
        simpa [MulAut.conj_apply]
      rw [happ]
      exact D.H.mul_mem (D.H.mul_mem hγH hx) (D.H.inv_mem hγH)
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj γ).injective).symm)
  have hmapNorm : (Subgroup.normalizer (A : Set G)).map (MulAut.conj γ).toMonoidHom =
      Subgroup.normalizer (A' : Set G) := by
    rw [hA'def]
    exact Subgroup.map_equiv_normalizer_eq A (MulAut.conj γ)
  have hmapK : K.map (MulAut.conj γ).toMonoidHom = N' := by
    rw [hKdef, hN'def, Subgroup.map_inf _ _ _ (MulAut.conj γ).injective, hmapH, hmapNorm]
  have hidxmap : N'.relIndex D.H = K.relIndex D.H := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj γ).toMonoidHom)
      K D.H (MulAut.conj γ).injective
    rwa [hmapK, hmapH] at h
  have hnot3idx : ¬ 3 ∣ N'.relIndex D.H := by
    intro h3idx
    have hidxrel := Subgroup.relIndex_mul_card N' D.H
    rw [inf_of_le_left (show N' ≤ D.H from inf_le_left)] at hidxrel
    have h3M : 3 * Nat.card N' ∣ Nat.card D.H := by
      rw [← hidxrel]
      exact Nat.mul_dvd_mul_right h3idx _
    have hbigK : (2 ^ n + 1) ^ 6 * 51840 * 3 ∣ SeitzReduction.E6Pilot.numTwistedE6 (2 ^ n) := by
      rw [← hHnum]
      refine (Nat.mul_dvd_mul_right hN'big 3).trans ?_
      rw [Nat.mul_comm (Nat.card N') 3]
      exact h3M
    have h35 : (2 ^ n + 1) ^ 6 * 3 ^ 5 ∣ SeitzReduction.E6Pilot.numTwistedE6 (2 ^ n) := by
      have hpow : 3 ^ 5 ∣ 51840 * 3 := by norm_num
      have h1 : (2 ^ n + 1) ^ 6 * 3 ^ 5 ∣ (2 ^ n + 1) ^ 6 * 51840 * 3 := by
        simpa only [Nat.mul_assoc] using Nat.mul_dvd_mul_left ((2 ^ n + 1) ^ 6) hpow
      exact h1.trans hbigK
    exact E6ThreeModel.not_dvd_numTwistedE6 (q := 2 ^ n)
      (by have := Nat.one_lt_two_pow (n := n) (by omega); omega) h3 h35
  have hnot3K : ¬ 3 ∣ K.relIndex D.H := by
    rw [← hidxmap]
    exact hnot3idx
  let Inn : Subgroup G := (MulAut.conj : R →* MulAut R).range
  have hInnH : Inn ≤ D.H := by
    intro x hx
    change x ∈ (MulAut.conj : R →* MulAut R).range at hx
    obtain ⟨r, rfl⟩ := hx
    have hmem : MulAut.conj r ∈ (D.H : Set G) := by
      rw [hDH]
      exact Subgroup.subset_closure (Set.mem_union_left _ ⟨r, rfl⟩)
    exact hmem
  have hInnNormal : Inn.Normal := by
    refine ⟨fun x hx g => ?_⟩
    change x ∈ (MulAut.conj : R →* MulAut R).range at hx
    obtain ⟨r, rfl⟩ := hx
    change g * MulAut.conj r * g⁻¹ ∈ (MulAut.conj : R →* MulAut R).range
    exact ⟨g r, (mulAut_conj_conj g r).symm⟩
  have h2iso : (Inn ⊓ K).relIndex Inn = K.relIndex (Inn ⊔ K) := by
    rw [Subgroup.inf_relIndex_left]
    exact relIndex_inf_eq_relIndex_sup Inn K
  have hsupH : Inn ⊔ K ≤ D.H := sup_le hInnH inf_le_left
  have hmulrel := Subgroup.relIndex_mul_relIndex K (Inn ⊔ K) D.H le_sup_right hsupH
  have hdvd : K.relIndex (Inn ⊔ K) ∣ K.relIndex D.H := ⟨_, hmulrel.symm⟩
  have hInnK : Inn ⊓ K = Inn ⊓ Subgroup.normalizer (A : Set G) := by
    rw [hKdef, ← inf_assoc, inf_of_le_left hInnH]
  intro h3t
  have h3Ksup : 3 ∣ K.relIndex (Inn ⊔ K) := by
    rw [← h2iso]
    rwa [hInnK]
  exact hnot3K (h3Ksup.trans hdvd)

end CFSG.StandardType
