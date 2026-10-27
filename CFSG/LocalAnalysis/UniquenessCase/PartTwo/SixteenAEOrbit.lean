module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEBasic
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeThompson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private def s16ae_orbit_stab {T : Type} [CommGroup T] (U : Subgroup T) :
    Subgroup (MulAut T) where
  carrier := {g | U.map g.toMonoidHom = U}
  one_mem' := by
    change U.map (MulEquiv.toMonoidHom (1 : MulAut T)) = U
    rw [show MulEquiv.toMonoidHom (1 : MulAut T) = MonoidHom.id T from
      MulEquiv.toMonoidHom_refl]
    exact Subgroup.map_id (G := T) (K := U)
  mul_mem' := by
    intro a b ha hb
    have h : (U.map b.toMonoidHom).map a.toMonoidHom = U := by rw [hb, ha]
    change U.map (a * b).toMonoidHom = U
    rw [MulAut.mul_def]
    rw [show (MulEquiv.trans b a).toMonoidHom = a.toMonoidHom.comp b.toMonoidHom from
      MulEquiv.toMonoidHom_trans b a]
    rw [← Subgroup.map_map]
    exact h
  inv_mem' := by
    intro a ha
    exact (Subgroup.map_symm_eq_iff_map_eq (H := U) (K := U) (e := a)).2 ha

theorem s16ae_exists_index_two_fix_ne_of_moved {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} {Y : ι → Subgroup T} (hind : iSupIndep Y)
    (hY : ∀ i, Y i ≠ ⊥) {A : Subgroup (MulAut T)} (hA : IsElemAbelian2 A)
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (Y i).map a.toMonoidHom = Y j)
    (hmove : ∃ a ∈ A, ∃ i, (Y i).map a.toMonoidHom ≠ Y i) :
    ∃ B : Subgroup (MulAut T), B ≤ A ∧ E3.mQuot A B = 1 ∧ fixV B ≠ fixV A := by
  classical
  haveI : Finite ι := Finite.of_injective Y (hind.injective hY)
  obtain ⟨a₀, ha₀A, i₀, hi₀⟩ := hmove
  let S : Subgroup (MulAut T) := A ⊓ s16ae_orbit_stab (Y i₀)
  have hSA : S ≤ A := inf_le_left
  have hSne : S ≠ A := by
    intro h
    have ha₀S : a₀ ∈ S := by rw [h]; exact ha₀A
    exact hi₀ ha₀S.2
  have hSlt : S < A := lt_of_le_of_ne hSA hSne
  obtain ⟨B, hSB, hBA, hq⟩ := s16ae_exists_index_two_ge hA hSlt
  have hBne : B ≠ A := by
    intro hEq
    have h0 : E3.mQuot A A = 0 := by
      unfold E3.mQuot Subgroup.relIndex
      simp
    rw [hEq, h0] at hq
    exact Nat.zero_ne_one hq
  have hnotle : ¬ A ≤ B := fun hle => hBne (le_antisymm hBA hle)
  obtain ⟨c, hcA, hcB⟩ := Set.not_subset.mp hnotle
  choose j hj using fun b : B => hperm (b : MulAut T) (hBA b.2) i₀
  choose k hk using fun b : B => hperm c hcA (j b)
  let Z : Subgroup T := ⨆ b : B, (Y i₀).map (b : MulAut T).toMonoidHom
  have hZdef : Z = ⨆ b : B, (Y i₀).map (b : MulAut T).toMonoidHom := rfl
  have hZeq : Z = ⨆ b : B, Y (j b) := by
    rw [hZdef]
    exact iSup_congr fun b => hj b
  have hZinv : ∀ p ∈ B, ∀ d ∈ Z, p d ∈ Z := by
    intro p hp d hd
    have hmap : Z.map p.toMonoidHom ≤ Z := by
      rw [hZdef, Subgroup.map_iSup]
      refine iSup_le fun b : B => ?_
      simpa [Subgroup.map_map, MulAut.mul_def, MulEquiv.toMonoidHom_trans] using
        le_iSup (fun b : B => (Y i₀).map (b : MulAut T).toMonoidHom)
          ⟨p * (b : MulAut T), B.mul_mem hp b.2⟩
    exact hmap (Subgroup.mem_map_of_mem p.toMonoidHom hd)
  have hZ1 : Z ≠ ⊥ := by
    intro hbot
    have hle : Y i₀ ≤ Z := by
      have hmap : (Y i₀).map ((1 : B) : MulAut T).toMonoidHom = Y i₀ := by
        rw [show ((1 : B) : MulAut T) = (1 : MulAut T) from rfl]
        change (Y i₀).map (MulEquiv.toMonoidHom (1 : MulAut T)) = Y i₀
        rw [show MulEquiv.toMonoidHom (1 : MulAut T) = MonoidHom.id T from
          MulEquiv.toMonoidHom_refl]
        exact Subgroup.map_id (G := T) (K := Y i₀)
      rw [← hmap]
      exact le_iSup (fun b : B => (Y i₀).map (b : MulAut T).toMonoidHom) (1 : B)
    rw [hbot] at hle
    exact hY i₀ (le_bot_iff.mp hle)
  have hB2 : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hA.1 a (hBA ha) b (hBA hb),
      fun a ha => hA.2 a (hBA ha)⟩
  have hpB : IsPGroup 2 ↥B := E3.isPGroup_of_isElemAbelian2 hB2
  obtain ⟨z, hzZ, hz1, hzfix⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.exists_fixed_of_isPGroup
      hT hpB Z hZinv hZ1
  have hzB : z ∈ fixV B := hzfix
  have hJK : Disjoint (Set.range j) (Set.range k) := by
    rw [Set.disjoint_left]
    intro x hxJ hxK
    obtain ⟨b, rfl⟩ := hxJ
    obtain ⟨b', hb'⟩ := hxK
    have hjk : j b = k b' := hb'.symm
    have hEq : (Y i₀).map (b : MulAut T).toMonoidHom =
        (Y i₀).map (c * (b' : MulAut T)).toMonoidHom := by
      calc
        (Y i₀).map (b : MulAut T).toMonoidHom = Y (j b) := hj b
        _ = Y (k b') := by rw [hjk]
        _ = (Y (j b')).map c.toMonoidHom := (hk b').symm
        _ = ((Y i₀).map (b' : MulAut T).toMonoidHom).map c.toMonoidHom := by rw [hj b']
        _ = (Y i₀).map (c * (b' : MulAut T)).toMonoidHom := by
          rw [Subgroup.map_map, MulAut.mul_def]
          exact (congrArg (fun f : T →* T => (Y i₀).map f)
            (MulEquiv.toMonoidHom_trans (b' : MulAut T) c)).symm
    have hEq' : (Y i₀).map
        ((b : MulAut T)⁻¹ * (c * (b' : MulAut T))).toMonoidHom = Y i₀ := by
      have hmain : ((Y i₀).map (c * (b' : MulAut T))).map
          ((b : MulAut T).symm).toMonoidHom = Y i₀ := by
        refine (Subgroup.map_symm_eq_iff_map_eq
          (H := (Y i₀).map (c * (b' : MulAut T))) (K := Y i₀)
          (e := (b : MulAut T))).2 ?_
        simpa using hEq
      have hcomp : ((b : MulAut T).symm).toMonoidHom.comp
          (c * (b' : MulAut T)).toMonoidHom =
          ((b : MulAut T)⁻¹ * (c * (b' : MulAut T))).toMonoidHom := by
        ext x
        simp [MulAut.mul_apply]
      rw [← hcomp, ← Subgroup.map_map]
      exact hmain
    let t : MulAut T := (b : MulAut T)⁻¹ * (c * (b' : MulAut T))
    have htA : t ∈ A :=
      A.mul_mem (A.inv_mem (hBA b.2)) (A.mul_mem hcA (hBA b'.2))
    have htS : t ∈ S := ⟨htA, hEq'⟩
    have htB : t ∈ B := hSB htS
    have hcB' : c ∈ B := by
      have hmem : (b : MulAut T) * t * (b' : MulAut T)⁻¹ ∈ B :=
        B.mul_mem (B.mul_mem b.2 htB) (B.inv_mem b'.2)
      have hct : c = (b : MulAut T) * t * (b' : MulAut T)⁻¹ := by
        dsimp [t]
        group
      rwa [← hct] at hmem
    exact hcB hcB'
  have hZJ : Z = ⨆ jj ∈ Set.range j, Y jj := by
    rw [hZeq, ← iSup_range]
  have hcZ : Z.map c.toMonoidHom = ⨆ kk ∈ Set.range k, Y kk := by
    rw [hZeq, Subgroup.map_iSup]
    rw [show (⨆ b : B, (Y (j b)).map c.toMonoidHom) = ⨆ b : B, Y (k b) from
      iSup_congr fun b => hk b]
    rw [← iSup_range]
  have hdisj : Disjoint Z (Z.map c.toMonoidHom) := by
    rw [hcZ, hZJ]
    exact hind.disjoint_biSup_biSup' hJK (Set.toFinite (Set.range j))
  have hzA : z ∉ fixV A := by
    intro hzfixA
    have hcz : c z = z := hzfixA c hcA
    have hzmap : z ∈ Z.map c.toMonoidHom := by
      rw [← hcz]
      exact Subgroup.mem_map_of_mem c.toMonoidHom hzZ
    have hzIn : z ∈ Z ⊓ Z.map c.toMonoidHom := ⟨hzZ, hzmap⟩
    have hbot : Z ⊓ Z.map c.toMonoidHom = ⊥ := disjoint_iff.mp hdisj
    have hzbot : z ∈ (⊥ : Subgroup T) := by
      rw [← hbot]
      exact hzIn
    exact hz1 (by simpa using hzbot)
  refine ⟨B, hBA, hq, ?_⟩
  intro hfix
  exact hzA (hfix ▸ hzB)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
