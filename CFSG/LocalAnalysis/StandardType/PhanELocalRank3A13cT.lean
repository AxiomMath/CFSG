module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A13cDef

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def D13c : TData K where
  okL p L := p ⊓ sgS K f 4 L = ⊥ ∧ L ⊓ sgS K f 4 p = ⊥

private theorem plh_tailProj_sgv (v : Fin 4 → K) :
    tailProj (sgv K f 4 v) = sgv K f 4 (tailProj v) := by
  funext j
  by_cases h : j = 0
  · subst h
    simp [sgv, tailProj]
  · simp [sgv, tailProj, h]

private theorem plh_sgS_comap_tailProj (X : Submodule K (Fin 4 → K)) :
    sgS K f 4 (X.comap tailProj) = (sgS K f 4 X).comap tailProj := by
  ext v
  simp only [sgS, Submodule.mem_comap]
  rw [plh_tailProj_sgv]

private theorem plh_sgS_le_Vtail {Y : Submodule K (Fin 4 → K)} (hY : Y ≤ Vtail) :
    sgS K f 4 Y ≤ Vtail := by
  intro v hv
  have h0 : sg K f (v 0) = 0 := by
    have hmem := hY hv
    simp only [Vtail, Set.mem_setOf_eq] at hmem
    simpa [sgv] using hmem
  exact (sg K f).map_eq_zero_iff.mp h0

private theorem plh_map_tailProj_le_Vtail (A : Submodule K (Fin 4 → K)) :
    A.map tailProj ≤ Vtail := by
  rintro w ⟨a, -, rfl⟩
  exact tailProj_mem a

private theorem plh_comap_eq_Vsub_iff {Z : Submodule K (Fin 4 → K)} (hZ : Z ≤ Vtail) :
    Z.comap tailProj = Vsub 4 1 ↔ Z = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro z hz
    have hz1 : z ∈ Vsub 4 1 := by
      have hzmem : z ∈ Z.comap tailProj := by
        rw [Submodule.mem_comap, tailProj_of_mem (hZ hz)]
        exact hz
      rwa [h] at hzmem
    have hmem : z ∈ (Vtail : Submodule K (Fin 4 → K)) ⊓ Vsub 4 1 := ⟨hZ hz, hz1⟩
    rw [Vtail_inf_Vsub] at hmem
    simpa using hmem
  · intro h
    rw [h, Submodule.comap_bot, ker_tailProj]

private theorem plh_key {A B : Submodule K (Fin 4 → K)} :
    (A ⊔ Vsub 4 1) ⊓ sgS K f 4 (B ⊔ Vsub 4 1) = Vsub 4 1 ↔
      A.map tailProj ⊓ sgS K f 4 (B.map tailProj) = ⊥ := by
  have hZle : A.map tailProj ⊓ sgS K f 4 (B.map tailProj) ≤ Vtail :=
    (inf_le_right : _ ⊓ sgS K f 4 (B.map tailProj) ≤ sgS K f 4 (B.map tailProj)).trans
      (plh_sgS_le_Vtail f (plh_map_tailProj_le_Vtail B))
  have hcomap : (A.map tailProj ⊓ sgS K f 4 (B.map tailProj)).comap tailProj =
      (A.map tailProj).comap tailProj ⊓ (sgS K f 4 (B.map tailProj)).comap tailProj :=
    rfl
  rw [sup_Vsub_eq_comap (S := A), sup_Vsub_eq_comap (S := B), plh_sgS_comap_tailProj f,
    ← hcomap]
  exact plh_comap_eq_Vsub_iff hZle

theorem adm13c_iff_admT (hK : Nat.card K = (2 ^ f) ^ 2) {p L H : Submodule K (Fin 4 → K)}
    (hf : IsFlag p L H) : Adm13c f p L H ↔ AdmT (D13c (K := K) f) p L H := by
  have h1 := plh_key (K := K) f (A := p) (B := L)
  have h2 := plh_key (K := K) f (A := L) (B := p)
  simp only [Adm13c, AdmT, D13c]
  exact and_congr_right (fun _ => and_congr h1 h2)

theorem admSet_a3_13c_eq (hK : Nat.card K = (2 ^ f) ^ 2) :
    admSet (Adm13c (K := K) f) = admSet (AdmT (D13c (K := K) f)) := by
  ext x
  simp only [admSet, Set.mem_setOf_eq]
  exact adm13c_iff_admT f hK
    ⟨FlagK.finrank_E_one x, FlagK.finrank_E_two x, FlagK.finrank_E_three x,
      FlagK.E_one_le_two x, FlagK.E_two_le_three x⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
