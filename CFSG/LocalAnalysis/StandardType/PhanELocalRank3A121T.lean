module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A121Def

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def D121 : TData K where
  okL p L := p ⊓ Vsub 4 3 = ⊥ ∧ (L ⊓ Vsub 4 3) ⊓ sgS K f 4 (L ⊓ Vsub 4 3) = ⊥

private theorem plh_mem_Vsub_three_iff (v : Fin 4 → K) : v ∈ Vsub 4 3 ↔ v 3 = 0 := by
  constructor
  · intro hv
    exact hv 3 (by norm_num)
  · intro hv j hj
    have hj3 : j = 3 := Fin.ext (by omega)
    subst hj3
    exact hv

private theorem plh_tailProj_mem_Vsub_three_iff (v : Fin 4 → K) :
    tailProj v ∈ Vsub 4 3 ↔ v ∈ Vsub 4 3 := by
  rw [plh_mem_Vsub_three_iff, plh_mem_Vsub_three_iff]
  show (tailProj v) 3 = 0 ↔ v 3 = 0
  simp [tailProj]

private theorem plh_comap_Vsub_three :
    (Vsub 4 3 : Submodule K (Fin 4 → K)).comap tailProj = Vsub 4 3 := by
  ext v
  rw [Submodule.mem_comap]
  exact plh_tailProj_mem_Vsub_three_iff v

private theorem plh_map_tailProj_le_Vtail (A : Submodule K (Fin 4 → K)) :
    A.map tailProj ≤ Vtail := by
  rintro w ⟨a, -, rfl⟩
  exact tailProj_mem a

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

private theorem plh_inf_Vsub_three_iff_map {X : Submodule K (Fin 4 → K)}
    (hX : X ⊓ Vsub 4 1 = ⊥) :
    X ⊓ Vsub 4 3 = ⊥ ↔ X.map tailProj ⊓ Vsub 4 3 = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro w hw
    obtain ⟨hwX, hwV⟩ := Submodule.mem_inf.mp hw
    obtain ⟨v, hv, rfl⟩ := hwX
    have hvV : v ∈ Vsub 4 3 := (plh_tailProj_mem_Vsub_three_iff v).mp hwV
    have hvbot : v ∈ X ⊓ Vsub 4 3 := ⟨hv, hvV⟩
    rw [h] at hvbot
    have hv0 : v = 0 := by simpa using hvbot
    subst hv0
    simp
  · intro h
    rw [eq_bot_iff]
    rintro v hv
    obtain ⟨hvX, hvV⟩ := Submodule.mem_inf.mp hv
    have htv : tailProj v ∈ X.map tailProj ⊓ Vsub 4 3 :=
      ⟨Submodule.mem_map_of_mem hvX, (plh_tailProj_mem_Vsub_three_iff v).mpr hvV⟩
    rw [h] at htv
    have hker : v ∈ Vsub 4 1 := by
      rw [← ker_tailProj, LinearMap.mem_ker]
      simpa using htv
    have hvbot : v ∈ X ⊓ Vsub 4 1 := ⟨hvX, hker⟩
    rw [hX] at hvbot
    simpa using hvbot

private theorem plh_key121 (L : Submodule K (Fin 4 → K)) :
    ((L ⊓ Vsub 4 3) ⊔ Vsub 4 1) ⊓ sgS K f 4 ((L ⊓ Vsub 4 3) ⊔ Vsub 4 1) = Vsub 4 1 ↔
      (L.map tailProj ⊓ Vsub 4 3) ⊓ sgS K f 4 (L.map tailProj ⊓ Vsub 4 3) = ⊥ := by
  have h13 : Vsub (K := K) 4 1 ≤ Vsub 4 3 := Vsub_mono (by norm_num)
  have hmod : (L ⊓ Vsub 4 3) ⊔ Vsub 4 1 = (L ⊔ Vsub 4 1) ⊓ Vsub 4 3 := by
    rw [sup_comm L (Vsub 4 1), sup_comm (L ⊓ Vsub 4 3) (Vsub 4 1)]
    exact (sup_inf_assoc_of_le L h13).symm
  have hcomap : (L ⊔ Vsub 4 1) ⊓ Vsub 4 3 =
      (L.map tailProj ⊓ Vsub 4 3).comap tailProj := by
    calc (L ⊔ Vsub 4 1) ⊓ Vsub 4 3
        = (L.map tailProj).comap tailProj ⊓ Vsub 4 3 := by rw [sup_Vsub_eq_comap]
      _ = (L.map tailProj).comap tailProj ⊓ (Vsub 4 3).comap tailProj := by
            rw [plh_comap_Vsub_three]
      _ = (L.map tailProj ⊓ Vsub 4 3).comap tailProj := by
            rw [Submodule.comap_inf]
  have hstep : (L ⊓ Vsub 4 3) ⊔ Vsub 4 1 =
      (L.map tailProj ⊓ Vsub 4 3).comap tailProj := hmod.trans hcomap
  have hMle : L.map tailProj ⊓ Vsub 4 3 ≤ Vtail :=
    inf_le_left.trans (plh_map_tailProj_le_Vtail L)
  have hZle : (L.map tailProj ⊓ Vsub 4 3) ⊓
      sgS K f 4 (L.map tailProj ⊓ Vsub 4 3) ≤ Vtail :=
    inf_le_left.trans hMle
  rw [hstep, plh_sgS_comap_tailProj f, ← Submodule.comap_inf]
  exact plh_comap_eq_Vsub_iff hZle

theorem adm121_iff_admT (hK : Nat.card K = (2 ^ f) ^ 2) {p L H : Submodule K (Fin 4 → K)}
    (hf : IsFlag p L H) : Adm121 f p L H ↔ AdmT (D121 (K := K) f) p L H := by
  by_cases hH : H ⊓ Vsub 4 1 = ⊥
  · have hp1 : p ⊓ Vsub 4 1 = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right (Vsub 4 1) hf.pL).trans
        ((inf_le_inf_right (Vsub 4 1) hf.LH).trans (le_of_eq hH)))
    have hp3 := plh_inf_Vsub_three_iff_map (X := p) hp1
    have hkey := plh_key121 f L
    simp only [Adm121, AdmT, D121]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨hH, hp3.mp h1, hkey.mp h3⟩
    · rintro ⟨-, h1, h3⟩
      exact ⟨hp3.mpr h1, hH, hkey.mpr h3⟩
  · simp only [Adm121, AdmT, D121]
    exact ⟨fun h => absurd h.2.1 hH, fun h => absurd h.1 hH⟩

theorem admSet_a3_121_eq (hK : Nat.card K = (2 ^ f) ^ 2) :
    admSet (Adm121 (K := K) f) = admSet (AdmT (D121 (K := K) f)) := by
  ext x
  simp only [admSet, Set.mem_setOf_eq]
  exact adm121_iff_admT f hK
    ⟨FlagK.finrank_E_one x, FlagK.finrank_E_two x, FlagK.finrank_E_three x,
      FlagK.E_one_le_two x, FlagK.E_two_le_three x⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
