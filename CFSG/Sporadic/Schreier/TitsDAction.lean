module

public import CFSG.Sporadic.Schreier.TitsAction

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def titsDFlagAct :
    titsD →* Equiv.Perm (Fin 8775) :=
  titsFlagHom.comp (Subgroup.inclusion titsD_le_titsA)

@[expose] def titsDLineAct :
    titsD →* Equiv.Perm (Fin 2925) :=
  titsLineHom.comp (Subgroup.inclusion titsD_le_titsA)

theorem titsFlagHom_word
    (w : List ℤ) (hw : wordIn 4 titsGen w ∈ titsA) :
    titsFlagHom ⟨wordIn 4 titsGen w, hw⟩ = wordIn 4 titsP w :=
  hom_wordIn titsFlagHom (fun _ hi => titsGen_mem_titsA hi) (fun _ hi => titsFlagHom_gen hi) w hw

theorem titsLineHom_word
    (w : List ℤ) (hw : wordIn 4 titsGen w ∈ titsA) :
    titsLineHom ⟨wordIn 4 titsGen w, hw⟩ = wordIn 4 titsAStar w :=
  hom_wordIn titsLineHom (fun _ hi => titsGen_mem_titsA hi) (fun _ hi => titsLineHom_gen hi) w hw

theorem tcomm_mk {K : Subgroup (Equiv.Perm (Fin 1755))} {x y : Equiv.Perm (Fin 1755)} (hx : x ∈ K)
    (hy : y ∈ K) (h : tcomm x y ∈ K) : (⟨tcomm x y, h⟩ : K) = tcomm ⟨x, hx⟩ ⟨y, hy⟩ :=
  Subtype.ext (by simp [tcomm])

theorem titsFlagHom_dGen
    (j : ℕ) :
    titsFlagHom ⟨titsDGen j, titsDGen_mem_titsA j⟩ = titsDFlag j := by
  have hu := wordIn_mem (K := titsA) (fun _ hi => titsGen_mem_titsA hi) (titsU j)
  have hv := wordIn_mem (K := titsA) (fun _ hi => titsGen_mem_titsA hi) (titsV j)
  have e : (⟨titsDGen j, titsDGen_mem_titsA j⟩ : titsA) =
      tcomm ⟨wordIn 4 titsGen (titsU j), hu⟩ ⟨wordIn 4 titsGen (titsV j), hv⟩ :=
    Subtype.ext (by simp [titsDGen, tcomm])
  rw [e, map_tcomm, titsFlagHom_word, titsFlagHom_word]
  rfl

theorem titsLineHom_dGen
    (j : ℕ) :
    titsLineHom ⟨titsDGen j, titsDGen_mem_titsA j⟩ = titsDStar j := by
  have hu := wordIn_mem (K := titsA) (fun _ hi => titsGen_mem_titsA hi) (titsU j)
  have hv := wordIn_mem (K := titsA) (fun _ hi => titsGen_mem_titsA hi) (titsV j)
  have e : (⟨titsDGen j, titsDGen_mem_titsA j⟩ : titsA) =
      tcomm ⟨wordIn 4 titsGen (titsU j), hu⟩ ⟨wordIn 4 titsGen (titsV j), hv⟩ :=
    Subtype.ext (by simp [titsDGen, tcomm])
  rw [e, map_tcomm, titsLineHom_word, titsLineHom_word]
  rfl

theorem titsDFlagAct_dGen
    {j : ℕ} (hj : j < 2) :
    titsDFlagAct ⟨titsDGen j, titsDGen_mem_titsD hj⟩ = titsDFlag j :=
  titsFlagHom_dGen j

theorem titsDLineAct_dGen
    {j : ℕ} (hj : j < 2) :
    titsDLineAct ⟨titsDGen j, titsDGen_mem_titsD hj⟩ = titsDStar j :=
  titsLineHom_dGen j

theorem titsDFlagAct_t
    {i : ℕ} (hi : i < 13) :
    titsDFlagAct ⟨titsT i, titsT_mem_titsD hi⟩ = titsTFlag i := by
  have h := hom_strongOf titsDFlagAct (fun _ hj => titsDGen_mem_titsD hj)
    (fun _ hj => titsDFlagAct_dGen hj) titsDerivedDerivations i
    (titsT_eq_strongOf hi ▸ titsT_mem_titsD hi)
  exact (congrArg _ (Subtype.ext (titsT_eq_strongOf hi))).trans h

theorem titsDLineAct_t
    {i : ℕ} (hi : i < 13) :
    titsDLineAct ⟨titsT i, titsT_mem_titsD hi⟩ = titsTStar i := by
  have h := hom_strongOf titsDLineAct (fun _ hj => titsDGen_mem_titsD hj)
    (fun _ hj => titsDLineAct_dGen hj) titsDerivedDerivations i
    (titsT_eq_strongOf hi ▸ titsT_mem_titsD hi)
  exact (congrArg _ (Subtype.ext (titsT_eq_strongOf hi))).trans h

theorem titsDFlagAct_word
    (w : List ℤ) :
    titsDFlagAct ⟨wordIn 13 titsT w, wordIn_titsT_mem_titsD w⟩ = wordIn 13 titsTFlag w :=
  hom_wordIn titsDFlagAct (fun _ hi => titsT_mem_titsD hi) (fun _ hi => titsDFlagAct_t hi) w _

theorem titsDLineAct_word
    (w : List ℤ) :
    titsDLineAct ⟨wordIn 13 titsT w, wordIn_titsT_mem_titsD w⟩ = wordIn 13 titsTStar w :=
  hom_wordIn titsDLineAct (fun _ hi => titsT_mem_titsD hi) (fun _ hi => titsDLineAct_t hi) w _

theorem titsBeta_dflag
    (g : titsD) (j : Fin 8775) :
    titsBeta (titsDFlagAct g j) = (g : Equiv.Perm (Fin 1755)) (titsBeta j) :=
  titsBeta_flag _ j

theorem titsKappa_dflag
    (g : titsD) (j : Fin 8775) :
    titsKappa (titsDFlagAct g j) = titsDLineAct g (titsKappa j) :=
  titsKappa_flag _ j

end CFSG.Sporadic.Schreier.Tits
