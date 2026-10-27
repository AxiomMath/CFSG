module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagModel
public import CFSG.LocalAnalysis.StandardType.PhanEFlagExch
public import CFSG.LocalAnalysis.StandardType.PhanEFlagAbs
import CFSG.LocalAnalysis.StandardType.PhanEDMBuilding

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {m : ℕ} {d : List ℕ}

private lemma q2cFIn_intrSet_restrict_eq {K : Type} [Field K] {m : ℕ}
    (R : Set (FlagK K (m + 1))) (ψ : FlagK K (m + 1) → FlagK K (m + 1)) (D : ℕ) :
    Subtype.val '' IntrSet ((buildingOver (symCox m) (flagδ (K := K) m) Set.univ).restrict
        (residue (symCox m) (flagδ (K := K) m) Set.univ (stdFlag K (m + 1))))
        {c | (c : FlagK K (m + 1)) ∈ R}
        (fun c => ⟨ψ c.1, by
          exact Eq.mpr (congrArg (fun s => ψ c.1 ∈ s)
            (residue_univ (isWeylDistanceBuilding_flag (K := K) (m := m))
              (stdFlag K (m + 1)))) (Set.mem_univ (ψ c.1))⟩) D =
      IntrSet (flagSys K m) R ψ D := by
  let RJ := residue (symCox m) (flagδ (K := K) m) Set.univ (stdFlag K (m + 1))
  let X := (buildingOver (symCox m) (flagδ (K := K) m) Set.univ).restrict RJ
  have hmem : ∀ x : FlagK K (m + 1), x ∈ RJ := fun x => by
    change x ∈ residue (symCox m) (flagδ (K := K) m) Set.univ (stdFlag K (m + 1))
    exact Eq.mpr (congrArg (fun s => x ∈ s)
      (residue_univ (isWeylDistanceBuilding_flag (K := K) (m := m))
        (stdFlag K (m + 1)))) (Set.mem_univ x)
  let ψ' : ↥RJ → ↥RJ := fun c => ⟨ψ c.1, hmem (ψ c.1)⟩
  let e : ↥(Set.univ : Set (Fin m)) ≃ Fin m :=
    { toFun := fun j => j.1
      invFun := fun i => ⟨i, Set.mem_univ i⟩
      left_inv := fun j => Subtype.ext rfl
      right_inv := fun i => rfl }
  let Φ : ↥RJ ≃ FlagK K (m + 1) :=
    { toFun := fun c => c.1
      invFun := fun x => ⟨x, hmem x⟩
      left_inv := fun c => Subtype.ext rfl
      right_inv := fun x => rfl }
  let Θ : ChamberIso X (flagSys K m) :=
    { e := e
      Φ := Φ
      adj_iff := by
        intro j u v
        change panelRel (symCox m) (flagδ (K := K) m) j.1 u.1 v.1 ↔
          (flagSys K m).adj (e j) (Φ u) (Φ v)
        have he : (e j : Fin m) = j.1 := rfl
        have hu : (Φ u : FlagK K (m + 1)) = u.1 := rfl
        have hv : (Φ v : FlagK K (m + 1)) = v.1 := rfl
        rw [he, hu, hv, flagSys_adj_iff]
        simpa [panelRel, buildingSystem] using
          (buildingSystem_adj_iff (cs := symCox m) (δ := flagδ (K := K) m)
            (isWeylDistanceBuilding_flag (K := K) (m := m))
            (i := j.1) (x := u.1) (y := v.1)) }
  have hψ : ∀ g ∈ {c : ↥RJ | (c : FlagK K (m + 1)) ∈ R}, Φ (ψ' g) = ψ (Φ g) := by
    intro g _
    rfl
  have himg : Φ '' {c : ↥RJ | (c : FlagK K (m + 1)) ∈ R} = R := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hx
      exact ⟨⟨x, hmem x⟩, hx, rfl⟩
  change Φ '' IntrSet X {c : ↥RJ | (c : FlagK K (m + 1)) ∈ R} ψ' D =
    IntrSet (flagSys K m) R ψ D
  ext E
  constructor
  · rintro ⟨c, hc, rfl⟩
    have h := (IntrSet_chamberIso Θ (R₀ := {c : ↥RJ | (c : FlagK K (m + 1)) ∈ R})
      (ψ := ψ') (ψ' := ψ) hψ D c).mpr hc
    rwa [himg] at h
  · intro hE
    let c : ↥RJ := Φ.symm E
    have hcΦ : Φ c = E := Φ.apply_symm_apply E
    have hmem' : Φ c ∈ IntrSet (flagSys K m) (Φ '' {c : ↥RJ | (c : FlagK K (m + 1)) ∈ R})
        ψ D := by
      rw [himg, hcΦ]
      exact hE
    have hc : c ∈ IntrSet X {c : ↥RJ | (c : FlagK K (m + 1)) ∈ R} ψ' D :=
      (IntrSet_chamberIso Θ (R₀ := {c : ↥RJ | (c : FlagK K (m + 1)) ∈ R})
        (ψ := ψ') (ψ' := ψ) hψ D c).mp hmem'
    exact ⟨c, hc, hcΦ⟩

theorem flagSys_connected (K : Type) [Field K] (m : ℕ) : (flagSys K m).Connected := by
  intro x y
  have hB := isWeylDistanceBuilding_flag (K := K) (m := m)
  have hy : y ∈ residue (symCox m) (flagδ (K := K) m) Set.univ x := by
    rw [residue_univ hB x]
    exact Set.mem_univ y
  rw [residue_flagδ_eq] at hy
  obtain ⟨γ, hγ, -, hend⟩ := hy
  exact ⟨γ, hγ, hend⟩

theorem intrSet_flagSys_eq_genSet (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (hn : m + 1 ≤ 4) (hd : IsCut (m + 1) d) (pol : List Bool) :
    IntrSet (flagSys K m) (refSet K (m + 1) d) (flagPsi hK hd pol) ((m + 1) * m / 2) =
      genSet K f (m + 1) d pol := by
  have hB := isWeylDistanceBuilding_flag (K := K) (m := m)
  have hstd : stdFlag K (m + 1) ∈ refSet K (m + 1) d := stdFlag_mem_refSet hd
  have hres : residue (symCox m) (flagδ (K := K) m) (cutTypes m d) (stdFlag K (m + 1)) =
      refSet K (m + 1) d := residue_cutTypes_eq hd hstd
  have hψ : ∀ x ∈ residue (symCox m) (flagδ (K := K) m) (cutTypes m d)
      (stdFlag K (m + 1)), flagPsi hK hd pol x ∈
        residue (symCox m) (flagδ (K := K) m) (cutTypes m d) (stdFlag K (m + 1)) := by
    intro x hx
    rw [hres] at hx ⊢
    exact flagPsi_mem hK hd pol hx
  have hex : ∃ x ∈ residue (symCox m) (flagδ (K := K) m) (cutTypes m d)
        (stdFlag K (m + 1)),
      (symCox m).length (flagδ (K := K) m x (flagPsi hK hd pol x)) =
        (symCox m).length (longest (symCox m) (cutTypes m d)) := by
    obtain ⟨z, hz, hzlong⟩ := exists_opp_flagPsi hK hq hn hd pol
    exact ⟨z, by rwa [hres], by rw [hzlong]⟩
  let RJ := residue (symCox m) (flagδ (K := K) m) Set.univ (stdFlag K (m + 1))
  have hmemRJ : ∀ x : FlagK K (m + 1), x ∈ RJ := fun x => by
    change x ∈ residue (symCox m) (flagδ (K := K) m) Set.univ (stdFlag K (m + 1))
    exact Eq.mpr (congrArg (fun s => x ∈ s)
      (residue_univ hB (stdFlag K (m + 1)))) (Set.mem_univ x)
  let ψ' : ↥RJ → ↥RJ := fun c => ⟨flagPsi hK hd pol c.1, hmemRJ _⟩
  have hset := setOf_isFar_eq_image_intrSet (cs := symCox m) (δ := flagδ (K := K) m)
    (I := cutTypes m d) (J := Set.univ) (a := stdFlag K (m + 1)) (x₁ := stdFlag K (m + 1))
    (ψ := flagPsi hK hd pol) hB (Set.subset_univ _) (self_mem_residue Set.univ _) hψ hex
    (ψ' := ψ') (by intro c hc; rfl)
  have hLHS : {c | c ∈ residue (symCox m) (flagδ (K := K) m) Set.univ
        (stdFlag K (m + 1)) ∧
      Gate.IsFar (symCox m) (flagδ (K := K) m) (cutTypes m d) Set.univ
        (stdFlag K (m + 1)) c ∧
      resProj (symCox m) (flagδ (K := K) m) (cutTypes m d) (stdFlag K (m + 1)) c ∈
        {x | x ∈ residue (symCox m) (flagδ (K := K) m) (cutTypes m d)
            (stdFlag K (m + 1)) ∧
          ∀ y ∈ residue (symCox m) (flagδ (K := K) m) (cutTypes m d)
            (stdFlag K (m + 1)),
            (symCox m).length (flagδ (K := K) m y (flagPsi hK hd pol y)) ≤
              (symCox m).length (flagδ (K := K) m x (flagPsi hK hd pol x))}} =
      genSet K f (m + 1) d pol := by
    rw [genSet_eq_flipSet hK hq hn hd pol]
    ext E
    simp only [Set.mem_setOf_eq, flagPsiMax]
    rw [residue_univ hB (stdFlag K (m + 1)), hres]
    simp only [Set.mem_univ, true_and]
  have hgen : genSet K f (m + 1) d pol =
      Subtype.val '' IntrSet ((buildingOver (symCox m) (flagδ (K := K) m) Set.univ).restrict
        RJ) {c | (c : FlagK K (m + 1)) ∈ residue (symCox m) (flagδ (K := K) m)
          (cutTypes m d) (stdFlag K (m + 1))} ψ' ((m + 1) * m / 2) := by
    rw [← hLHS, hset, length_longest_symCox_univ m]
  rw [hgen, hres]
  exact (q2cFIn_intrSet_restrict_eq (R := refSet K (m + 1) d)
    (ψ := flagPsi hK hd pol) ((m + 1) * m / 2)).symm

theorem intrSet_flagSys_eq_set22x (hK : Nat.card K = (2 ^ f) ^ 2) :
    IntrSet (flagSys K 3) (refSet K 4 [0, 2, 4]) (flagPsiX hK) 6 = set22x K f := by
  have hB := isWeylDistanceBuilding_flag (K := K) (m := 3)
  have hstd : stdFlag K 4 ∈ refSet K 4 [0, 2, 4] := stdFlag_mem_refSet isCut_22
  have hres : residue (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4]) (stdFlag K 4) =
      refSet K 4 [0, 2, 4] := residue_cutTypes_eq isCut_22 hstd
  have hψ : ∀ x ∈ residue (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4])
      (stdFlag K 4), flagPsiX hK x ∈
        residue (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4]) (stdFlag K 4) := by
    intro x hx
    rw [hres] at hx ⊢
    exact flagPsiX_mem hK hx
  have hex : ∃ x ∈ residue (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4])
        (stdFlag K 4),
      (symCox 3).length (flagδ (K := K) 3 x (flagPsiX hK x)) =
        (symCox 3).length (longest (symCox 3) (cutTypes 3 [0, 2, 4])) := by
    obtain ⟨z, hz, hzlong⟩ := exists_opp_flagPsiX hK
    exact ⟨z, by rwa [hres], by rw [hzlong]⟩
  let RJ := residue (symCox 3) (flagδ (K := K) 3) Set.univ (stdFlag K 4)
  have hmemRJ : ∀ x : FlagK K 4, x ∈ RJ := fun x => by
    change x ∈ residue (symCox 3) (flagδ (K := K) 3) Set.univ (stdFlag K 4)
    exact Eq.mpr (congrArg (fun s => x ∈ s)
      (residue_univ hB (stdFlag K 4))) (Set.mem_univ x)
  let ψ' : ↥RJ → ↥RJ := fun c => ⟨flagPsiX hK c.1, hmemRJ _⟩
  have hset := setOf_isFar_eq_image_intrSet (cs := symCox 3) (δ := flagδ (K := K) 3)
    (I := cutTypes 3 [0, 2, 4]) (J := Set.univ) (a := stdFlag K 4) (x₁ := stdFlag K 4)
    (ψ := flagPsiX hK) hB (Set.subset_univ _) (self_mem_residue Set.univ _) hψ hex
    (ψ' := ψ') (by intro c hc; rfl)
  have hLHS : {c | c ∈ residue (symCox 3) (flagδ (K := K) 3) Set.univ (stdFlag K 4) ∧
      Gate.IsFar (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4]) Set.univ
        (stdFlag K 4) c ∧
      resProj (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4]) (stdFlag K 4) c ∈
        {x | x ∈ residue (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4])
            (stdFlag K 4) ∧
          ∀ y ∈ residue (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4])
            (stdFlag K 4),
            (symCox 3).length (flagδ (K := K) 3 y (flagPsiX hK y)) ≤
              (symCox 3).length (flagδ (K := K) 3 x (flagPsiX hK x))}} =
      set22x K f := by
    rw [set22x_eq_flipSet hK]
    ext E
    simp only [Set.mem_setOf_eq, flagPsiXMax]
    rw [residue_univ hB (stdFlag K 4), hres]
    simp only [Set.mem_univ, true_and]
  have hgen : set22x K f =
      Subtype.val '' IntrSet ((buildingOver (symCox 3) (flagδ (K := K) 3) Set.univ).restrict
        RJ) {c | (c : FlagK K 4) ∈ residue (symCox 3) (flagδ (K := K) 3)
          (cutTypes 3 [0, 2, 4]) (stdFlag K 4)} ψ' 6 := by
    rw [← hLHS, hset, length_longest_symCox_univ 3]
  rw [hgen, hres]
  exact (q2cFIn_intrSet_restrict_eq (m := 3) (R := refSet K 4 [0, 2, 4])
    (ψ := flagPsiX hK) 6).symm

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
