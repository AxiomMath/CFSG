module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

theorem secHom_mem_fixPerp (g : stabE k) :
    secHom g ∈ fixPerp (Pi.single 0 1 : Fin 4 → k) (Pi.single 3 1) := by
  intro x h0 h3
  rw [bil_single] at h0 h3
  rw [act_secHom, act_sec]
  ext i
  fin_cases i <;> simp_all [Fin.rev]

theorem proj_act (g : stabE k) {x : Fin 4 → k} (hx : x 2 = 0) :
    proj (natAct (g : antiSp k) x) = natAct (secHom g) (proj x) := by
  have h1 := glMat_one_col g.2 0
  have h3 := glMat_one_col g.2 3
  rw [act_secHom, act_sec]
  ext i
  fin_cases i <;>
    simp [proj, natAct, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hx, eOne] at h1 h3 ⊢
  · rw [h1]; ring
  · rw [h3]; ring

@[expose] def liftGrp (Z : Set (Fin 4 → k)) : Subgroup (stabE k) :=
  Subgroup.closure {g | ∃ z ∈ Z, (g : antiSp k) = trv z 1}

theorem liftGrp_le {Z : Set (Fin 4 → k)} {G₀ : Subgroup (antiSp k)} (hZ : ∀ z ∈ Z, trv z 1 ∈ G₀)
    {g : stabE k} (hg : g ∈ liftGrp Z) : (g : antiSp k) ∈ G₀ := by
  have h : liftGrp Z ≤ G₀.comap (stabE k).subtype :=
    (Subgroup.closure_le _).mpr fun x ⟨z, hz, he⟩ => by
      change (x : antiSp k) ∈ G₀
      rw [he]
      exact hZ z hz
  exact h hg

@[expose] noncomputable def secGrp (Z : Set (Fin 4 → k)) : Subgroup (antiSp k) :=
  (liftGrp Z).map secHom

theorem secGrp_eq {Z : Set (Fin 4 → k)} (hZ : ∀ z ∈ Z, z 2 = 0) :
    secGrp Z = Subgroup.closure {g | ∃ z ∈ Z, g = trv (proj z) 1} := by
  rw [secGrp, liftGrp, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨g', ⟨z, hz, hg'⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    have he : g' = ⟨trv z 1, trv_mem_stabE (hZ z hz) 1⟩ := Subtype.ext hg'
    rw [he, secHom_trv (hZ z hz)]
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨trv z 1, trv_mem_stabE (hZ z hz) 1⟩, ⟨z, hz, rfl⟩, secHom_trv (hZ z hz) 1⟩

theorem trv_proj_mem_secGrp {Z : Set (Fin 4 → k)} (hZ : ∀ z ∈ Z, z 2 = 0) {z : Fin 4 → k}
    (hz : z ∈ Z) : trv (proj z) 1 ∈ secGrp Z := by
  rw [secGrp_eq hZ]
  exact Subgroup.subset_closure ⟨z, hz, rfl⟩

theorem secGrp_le_fixPerp (Z : Set (Fin 4 → k)) :
    secGrp Z ≤ fixPerp (Pi.single 0 1 : Fin 4 → k) (Pi.single 3 1) := by
  rintro _ ⟨g, -, rfl⟩
  exact secHom_mem_fixPerp g

theorem exists_lift {Z : Set (Fin 4 → k)} {h : antiSp k} (hh : h ∈ secGrp Z) :
    ∃ g ∈ liftGrp Z, secHom g = h ∧
      ∀ x : Fin 4 → k, x 2 = 0 → proj (natAct (g : antiSp k) x) = natAct h (proj x) := by
  obtain ⟨g, hg, rfl⟩ := hh
  exact ⟨g, hg, rfl, fun x hx => proj_act g hx⟩

theorem exists_act_eOne {ρ : Fin 4 → k} (hρ : ρ ≠ 0) : ∃ g : antiSp k, natAct g (eOne k) = ρ :=
  CFSG.QuasithinUnique.Setup.X7b.antiSp_exists_mulVec_eq (by simp [eOne]) hρ

end CFSG.Quasithin.Ch3E213M.G41.Big
