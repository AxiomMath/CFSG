module

public import CFSG.Quasithin.EmptyFaithful.S145Facts
public import CFSG.Quasithin.H13.L32A712

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement Pointwise

namespace L32A

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

structure Not1471 (T L V H : Subgroup G) (γ γ' : F8.Geom T L H) (g h : ↥((L ⊔ T) ⊔ H)) :
    Prop where
  setup : F8Setup T V L H γ γ' g
  pos : 0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G))
  le : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) ≤
    mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G))
  mem : (h : G) ∈ H
  geo : ∃ γ₂ ∈ nbrs (F8.γ₁ T L H), CosetGeom.dist γ γ₂ + 2 = F8.b T V L H ∧
    h • γ₂ = F8.γ₀ T L H

theorem exists_not1471 (hF : HypF98 T V L (fsuV1 T V) V H) {γ γ' : F8.Geom T L H}
    {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hlt : F8.Dγ V (fsuV1 T V) H (g : G) < F8.Uγ V H (g : G)) :
    ∃ (δ δ' : F8.Geom T L H) (k h : ↥((L ⊔ T) ⊔ H)), Not1471 T L V H δ δ' k h := by
  obtain ⟨δ, δ', k, sk, hpos, hle, -⟩ := hF.lemma_14_5_18_four s hlt
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := hF.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic hF.amalgamHypV.gen sk.critical.geodesic (by omega : 2 ≤ _)
  obtain ⟨y, hy1, hy2⟩ := exists_stab_smul_eq (γ := F8.γ₁ T L H) hγ₂nb
    (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H) (G₁ := L ⊔ T) (G₂ := H)).symm
  have hyH : (y : G) ∈ H := by
    have := mem_stab_of_smul_eq hy1
    rwa [stab_γ₁ hF.amalgamHypV.le₂] at this
  exact ⟨δ, δ', k, y, sk, hpos, hle, hyH, γ₂, hγ₂nb, hd, hy2⟩

namespace Not1471

variable {γ γ' : F8.Geom T L H} {g h : ↥((L ⊔ T) ⊔ H)}

theorem uα_le (N : Not1471 T L V H γ γ' g h) (hF : HypF98 T V L (fsuV1 T V) V H) :
    conjSub (h : G) (F8.Uγ V H (g : G)) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  obtain ⟨γ₂, hγ₂nb, hd, hγ₂⟩ := N.geo
  have h1 := conjSub_mono (h : G) ((hF.F913_2 N.setup).2 γ₂ hγ₂nb hd)
  have hhγ₁ : h • F8.γ₁ T L H = F8.γ₁ T L H :=
    smul_eq_of_mem_stab (by rw [stab_γ₁ hF.amalgamHypV.le₂]; exact N.mem)
  rw [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, hhγ₁, hγ₂, inf_comm,
    hF.F913_1] at h1
  exact h1

theorem commutator_le (N : Not1471 T L V H γ γ' g h) (hF : HypF98 T V L (fsuV1 T V) V H) :
    ⁅conjClosure V H, conjSub (h : G) (F8.Uγ V H (g : G))⁆ ≤
      conjClosure V H ⊓ conjSub (h : G) (F8.Uγ V H (g : G)) := by
  have h1 := conjSub_mono (h : G) (hF.F913_3 N.setup (Or.inr rfl) (Or.inr rfl))
  have hU : conjSub (h : G) (conjClosure V H) = conjClosure V H :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V H N.mem)
  rwa [conjSub_inf, ← conjSub_commutator, hU] at h1

theorem le_normalizer (N : Not1471 T L V H γ γ' g h) (hF : HypF98 T V L (fsuV1 T V) V H) :
    conjClosure V H ≤ Subgroup.normalizer (conjSub (h : G) (F8.Uγ V H (g : G)) : Set G) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ {u x : G}, u ∈ conjClosure V H → x ∈ conjSub (h : G) (F8.Uγ V H (g : G)) →
      u * x * u⁻¹ ∈ conjSub (h : G) (F8.Uγ V H (g : G)) := fun {u x} hu hx => by
    have hc := (N.commutator_le hF (Subgroup.commutator_mem_commutator hu hx)).2
    have e : u * x * u⁻¹ = ⁅u, x⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hc hx
  refine ⟨key hu, fun hx => ?_⟩
  have := key (inv_mem hu) hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem uα_ne (N : Not1471 T L V H γ γ' g h) (hF : HypF98 T V L (fsuV1 T V) V H) :
    conjSub (h : G) (F8.Uγ V H (g : G)) ≠ conjClosure V H := by
  intro heq
  have hγ : F8.Uγ V H (g : G) = conjClosure V H := by
    have h1 := congrArg (conjSub (h : G)⁻¹) heq
    rw [conjSub_conjSub_inv] at h1
    rw [h1]
    exact conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V H (inv_mem N.mem))
  have hD : F8.Dγ V (fsuV1 T V) H (g : G) = F8.Uγ V H (g : G) := by
    refine le_antisymm (centralizerMod_le_left _ _ _) fun x hx => ?_
    have hx' : x ∈ conjClosure V H := hγ ▸ hx
    refine ⟨hx, F8.le_normalizer_of_le hF.F911_2 (inf_le_left.trans (le_conjClosure V H)) hx',
      fun u hu => ?_⟩
    rw [F7.isElemAbelian_comm hF.F911_2 hx' hu, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have := N.pos
  rw [hD] at this
  simp [mIdx] at this

theorem lemma14_7_12_two (N : Not1471 T L V H γ γ' g h) (hF : HypF98 T V L (fsuV1 T V) V H)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hb : F8.b T V L H = 3) :
    ∃ l ∈ L, conjSub (h : G) (F8.Uγ V H (g : G)) = conjSub l (conjClosure V H) := by
  obtain ⟨γ₂, -, hd, hγ₂⟩ := N.geo
  have hd1 : CosetGeom.dist γ γ₂ = 1 := by omega
  have hadj : (graph ((L ⊔ T) ⊔ H) (L ⊔ T) H).Adj (F8.γ₀ T L H) (h • γ) := by
    rw [← hγ₂]
    exact (smul_adj h).mpr (dist_eq_one_iff_adj.mp hd1).symm
  obtain ⟨k, hk0, hk1⟩ :=
    exists_stab_smul_eq (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H) (G₁ := L ⊔ T) (G₂ := H)) hadj
  have hkLT : (k : G) ∈ L ⊔ T := by
    have := mem_stab_of_smul_eq hk0
    rwa [stab_γ₀ hF.amalgamHypV.le₁] at this
  have hkH : ((k⁻¹ * h * g : ↥((L ⊔ T) ⊔ H)) : G) ∈ H := by
    have h1 : (k⁻¹ * h * g) • F8.γ₁ T L H = F8.γ₁ T L H := by
      rw [mul_smul, mul_smul, N.setup.edge₁, ← hk1, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rwa [stab_γ₁ hF.amalgamHypV.le₂] at this
  have hk' : (k : G) ∈ (L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]
    exact hkLT
  obtain ⟨l, hl, t, ht, hlt⟩ := hk'
  refine ⟨l, hl, ?_⟩
  have hTU : conjSub t (conjClosure V H) = conjClosure V H :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V H (hF.T_le_H ht))
  have hHU : conjSub ((k⁻¹ * h * g : ↥((L ⊔ T) ⊔ H)) : G) (conjClosure V H) = conjClosure V H :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V H hkH)
  calc conjSub (h : G) (F8.Uγ V H (g : G)) =
        conjSub (k : G) (conjSub ((k⁻¹ * h * g : ↥((L ⊔ T) ⊔ H)) : G) (conjClosure V H)) := by
        rw [F8.Uγ, ← conjSub_mul, ← conjSub_mul]
        congr 1
        push_cast
        group
    _ = conjSub l (conjClosure V H) := by rw [hHU, ← hlt, conjSub_mul, hTU]

end Not1471

end L32A

end CFSG.Quasithin.H13
