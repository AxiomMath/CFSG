module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Rad

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

private theorem isSolvable_ker_of_mem_ker {K Y M : Type} [Group K] [Group Y] [Group M]
    {π : K →* Y} (hker : Group.IsSolvable ↥π.ker) {X : Subgroup K} (f : ↥X →* M)
    (h : ∀ x : ↥X, f x = 1 → π x = 1) : Group.IsSolvable f.ker := by
  let ι : ↥f.ker →* ↥π.ker :=
    { toFun := fun x => ⟨((x : ↥X) : K), MonoidHom.mem_ker.mpr (h x (MonoidHom.mem_ker.mp x.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := ι) fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥π.ker => (z : K)) hab))

variable {K Y : Type} [Group K] [Group Y] [Finite K] {P : ∀ (X : Type) [Group X], Prop}

theorem isCompositionFactor_of_comap_of_surjective (π : K →* Y) (hπ : Function.Surjective π)
    (hker : Group.IsSolvable ↥π.ker) (Xb : Subgroup Y) {L : Type} [Group L]
    (h : E1.IsCompositionFactor ↥(Xb.comap π) L) (hnab : ∃ a b : L, a * b ≠ b * a) :
    E1.IsCompositionFactor ↥Xb L :=
  isCompositionFactor_of_surjective_of_isSolvable_ker (π.subgroupComap Xb)
    (MonoidHom.subgroupComap_surjective π Xb hπ)
    (isSolvable_ker_of_mem_ker hker _ fun _ hx => congrArg Subtype.val hx) h hnab

theorem isCompositionFactor_map_of_isSolvable_ker (π : K →* Y) (hker : Group.IsSolvable ↥π.ker)
    (X : Subgroup K) {L : Type} [Group L] (h : E1.IsCompositionFactor ↥X L)
    (hnab : ∃ a b : L, a * b ≠ b * a) : E1.IsCompositionFactor ↥(X.map π) L :=
  isCompositionFactor_of_surjective_of_isSolvable_ker (π.subgroupMap X)
    (MonoidHom.subgroupMap_surjective π X)
    (isSolvable_ker_of_mem_ker hker _ fun _ hx => congrArg Subtype.val hx) h hnab

theorem comap_mem_calLT_of_surjective
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    (π : K →* Y) (hπ : Function.Surjective π) (hker : Group.IsSolvable ↥π.ker) {S : Subgroup K}
    {Xb : Subgroup Y} (hXb : Xb ∈ calLT P ⊤ (S.map π)) : Xb.comap π ∈ calLT P ⊤ S := by
  obtain ⟨hSX, hXt, hXcf⟩ := hXb
  refine ⟨Subgroup.map_le_iff_le_comap.mp hSX, lt_top_iff_ne_top.mpr fun h => hXt.ne ?_, ?_⟩
  · rw [← Subgroup.map_comap_eq_self_of_surjective hπ Xb, h, Subgroup.map_top_of_surjective π hπ]
  · rintro ⟨L, hL, hcf, hPL⟩
    have : Finite L := isCompositionFactor_finite hcf
    exact hXcf ⟨L, hL, isCompositionFactor_of_comap_of_surjective π hπ hker Xb hcf (hP L hPL), hPL⟩

theorem lGen_le_map_lGen_of_surjective
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    (π : K →* Y) (hπ : Function.Surjective π) (hker : Group.IsSolvable ↥π.ker) (S : Subgroup K) :
    lGen P ⊤ (S.map π) ≤ (lGen P ⊤ S).map π := by
  refine iSup₂_le fun Xb hXb => ?_
  calc Xb = (Xb.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ Xb).symm
    _ ≤ (lGen P ⊤ S).map π := Subgroup.map_mono
      (le_iSup₂_of_le (f := fun X _ => X) _ (comap_mem_calLT_of_surjective hP π hπ hker hXb) le_rfl)

theorem lGen_eq_top_of_map
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    (π : K →* Y) (hπ : Function.Surjective π) (hker : Group.IsSolvable ↥π.ker) (S : Subgroup K)
    (hY : Nontrivial Y) (h : lGen P ⊤ (S.map π) = ⊤) : lGen P ⊤ S = ⊤ := by
  obtain ⟨Xb, hXb⟩ : (calLT P ⊤ (S.map π)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hbot : lGen P ⊤ (S.map π) = ⊥ := by simp [lGen, hempty]
    exact bot_ne_top (hbot.symm.trans h)
  have hkerle : π.ker ≤ lGen P ⊤ S := (MonoidHom.ker_le_comap π Xb).trans
    (le_iSup₂_of_le (f := fun X _ => X) _ (comap_mem_calLT_of_surjective hP π hπ hker hXb) le_rfl)
  have htop : (lGen P ⊤ S).map π = ⊤ := by
    rw [eq_top_iff, ← h]
    exact lGen_le_map_lGen_of_surjective hP π hπ hker S
  have h1 := Subgroup.comap_map_eq π (lGen P ⊤ S)
  rw [htop, Subgroup.comap_top, sup_of_le_left hkerle] at h1
  exact h1.symm

theorem uniqueMax_comap
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    (π : K →* Y) (hπ : Function.Surjective π) (hker : Group.IsSolvable ↥π.ker) {S : Subgroup K}
    (hS : IsSylowIn 2 S ⊤) (hno : ¬ HasCompFactor (⊤ : Subgroup K) P) (hne : lGen P ⊤ S ≠ ⊤)
    (hns : ¬ Group.IsSolvable K) {M : Subgroup Y} (hM : M < ⊤)
    (hMax : ∀ X : Subgroup Y, S.map π ≤ X → X < ⊤ → X ≤ M) (hM0 : ¬ HasCompFactor M P) :
    M.comap π < ⊤ ∧ (∀ X : Subgroup K, S ≤ X → X < ⊤ → X ≤ M.comap π) ∧
      ¬ HasCompFactor (M.comap π) P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_surjective π hπ
  refine ⟨lt_top_iff_ne_top.mpr fun h => hM.ne ?_, fun X hSX hXt => ?_, ?_⟩
  · rw [← Subgroup.map_comap_eq_self_of_surjective hπ M, h, Subgroup.map_top_of_surjective π hπ]
  · have hXmap : X.map π ≠ ⊤ := by
      intro hXY
      have hXmem : X ∈ calLT P ⊤ S := by
        refine ⟨hSX, hXt, ?_⟩
        rintro ⟨L, hL, hcf, hPL⟩
        have : Finite L := isCompositionFactor_finite hcf
        have h1 := isCompositionFactor_map_of_isSolvable_ker π hker X hcf (hP L hPL)
        rw [hXY] at h1
        have h2 : E1.IsCompositionFactor K L :=
          CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective π hπ
            ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr Subgroup.topEquiv).1 h1)
        exact hno ⟨L, hL, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
          Subgroup.topEquiv.symm).1 h2, hPL⟩
      have hSm : IsPGroup 2 ↥(S.map π) := hS.isPGroup.map π
      have : Group.IsSolvable ↥(S.map π) := by
        have := hSm.isNilpotent
        infer_instance
      have hSt : S.map π ≠ ⊤ := by
        intro hSY
        apply hns
        have hY2 : IsPGroup 2 Y := (hSY ▸ hSm).of_equiv Subgroup.topEquiv
        have := hY2.isNilpotent
        exact Group.isSolvable_of_ker_le_range π.ker.subtype π (Subgroup.range_subtype π.ker).ge
      have hSle : (S.map π).comap π ≤ lGen P ⊤ S :=
        comap_le_lGen hP hno π hπ hker le_rfl hSt fun L _ h hnab => by
          obtain ⟨a, b, hab⟩ := hnab
          exact absurd (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
            inferInstance h a b) hab
      have hXk : X ⊔ π.ker = ⊤ := by
        rw [← Subgroup.comap_map_eq π X, hXY, Subgroup.comap_top]
      apply hne
      refine top_le_iff.mp ?_
      calc (⊤ : Subgroup K) = X ⊔ π.ker := hXk.symm
        _ ≤ lGen P ⊤ S := sup_le (le_iSup₂_of_le (f := fun X _ => X) X hXmem le_rfl)
          ((MonoidHom.ker_le_comap π _).trans hSle)
    exact Subgroup.map_le_iff_le_comap.mp
      (hMax _ (Subgroup.map_mono hSX) (lt_top_iff_ne_top.mpr hXmap))
  · rintro ⟨L, hL, hcf, hPL⟩
    have : Finite L := isCompositionFactor_finite hcf
    exact hM0 ⟨L, hL, isCompositionFactor_of_comap_of_surjective π hπ hker M hcf (hP L hPL), hPL⟩

end CFSG.LocalAnalysis.WeakClosure81

end
