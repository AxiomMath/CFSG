module

public import CFSG.Sporadic.SuzRecog.LevelTwoCoverDefs
public import CFSG.Sporadic.SuzRecog.TitsTwoType
import CFSG.Certificates.Kernel.RankElimSound

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwoCover

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.ElimCert CFSG.Sporadic.SuzRecog.LevelTwo
  CFSG.Sporadic.SuzRecog.TitsTwo CFSG.Sporadic.Co1Patterson

attribute [local irreducible] nbr nbrC vtab vtabs aPts wPts trips aIdx vIdx cells p1 cellReps deck

theorem pr_val (u : Fin 8991) : (pr u).1 = u.1 % 2997 := rfl

@[expose] def admTC (S : Set (Fin 8991)) : Prop :=
  ∃ v ∈ S, 2835 ≤ (pr v).1 ∧ ∀ w ∈ S, w ≠ v → (pr w).1 < 2835

theorem pr_smul_lt_iff (g : F)
    (v : Fin 8991) : (pr (g • v)).1 < 2835 ↔ (pr v).1 < 2835 := by
  rw [pr_smul]
  exact smul_lt_iff _ _

theorem admTC_smul (g : F)
    (S : Set (Fin 8991)) (h : admTC S) : admTC ((g • ·) '' S) := by
  obtain ⟨v, hv, hv2, hw⟩ := h
  refine ⟨g • v, ⟨v, hv, rfl⟩, ?_, ?_⟩
  · by_contra hlt
    exact absurd ((pr_smul_lt_iff g v).1 (by omega)) (by omega)
  · rintro _ ⟨w, hw', rfl⟩ hne
    exact (pr_smul_lt_iff g w).2 (hw w hw' fun e => hne (e ▸ rfl))

theorem adjB_neC {x y : ℕ} (h : adjB nbrC x y = true) : x ≠ y := by
  simp only [adjB, Bool.and_eq_true, bne_iff_ne] at h
  exact h.1

theorem admTC_of_triC {x y z : Fin 8991} (h : triC nbrC x y z = true) : admTC {x, y, z} := by
  simp only [triC, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hxy, hyz⟩, hxz⟩, hc⟩ := h
  have nxy : x ≠ y := fun e => adjB_neC hxy (congrArg Fin.val e)
  have nyz : y ≠ z := fun e => adjB_neC hyz (congrArg Fin.val e)
  have nxz : x ≠ z := fun e => adjB_neC hxz (congrArg Fin.val e)
  simp only [admTC, pr_val]
  by_cases hx : 2835 ≤ x.1 % 2997 <;> by_cases hy : 2835 ≤ y.1 % 2997 <;>
    by_cases hz : 2835 ≤ z.1 % 2997 <;> simp only [hx, hy, hz, ↓reduceIte] at hc <;>
    norm_num at hc
  · refine ⟨x, Set.mem_insert _ _, hx, ?_⟩
    rintro w hw hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact absurd rfl hne
    · omega
    · omega
  · refine ⟨y, Set.mem_insert_of_mem _ (Set.mem_insert _ _), hy, ?_⟩
    rintro w hw hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · omega
    · exact absurd rfl hne
    · omega
  · refine ⟨z, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl), hz, ?_⟩
    rintro w hw hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · omega
    · omega
    · exact absurd rfl hne

theorem triangulableBy_Γc : TriangulableBy Γc admTC := by
  obtain ⟨_, _, _, _, _, h⟩ := cover_elim_check
  exact CFSG.KC.RankElim.triangulableBy_of_ok (fun _ _ _ h => admTC_of_triC h) h

@[expose] noncomputable def Fp : Subgroup F := MulAction.stabilizer F pt

@[expose] noncomputable def Fq : Subgroup F :=
  MulAction.stabilizer F qt

@[expose] noncomputable def Fe : Subgroup F where
  carrier := {g | (g • pt = pt ∧ g • pt1 = pt1) ∨ (g • pt = pt1 ∧ g • pt1 = pt)}
  one_mem' := Or.inl ⟨one_smul _ _, one_smul _ _⟩
  mul_mem' := by
    rintro g h (⟨ga, gb⟩ | ⟨ga, gb⟩) (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      simp only [Set.mem_ofPred_eq, mul_smul, ha, hb, ga, gb, and_self, true_or, or_true]
  inv_mem' := by
    rintro g (⟨ga, gb⟩ | ⟨ga, gb⟩)
    · exact Or.inl ⟨inv_smul_eq_iff.2 ga.symm, inv_smul_eq_iff.2 gb.symm⟩
    · exact Or.inr ⟨inv_smul_eq_iff.2 gb.symm, inv_smul_eq_iff.2 ga.symm⟩

theorem mem_Fp (g : F) : g ∈ Fp ↔ g • pt = pt :=
  MulAction.mem_stabilizer_iff

theorem mem_Fq (g : F) : g ∈ Fq ↔ g • qt = qt :=
  MulAction.mem_stabilizer_iff

theorem mem_Fe (g : F) :
    g ∈ Fe ↔ (g • pt = pt ∧ g • pt1 = pt1) ∨ (g • pt = pt1 ∧ g • pt1 = pt) :=
  Iff.rfl

theorem smul_qt_ne_pt (g : F) :
    g • qt ≠ pt := by
  intro h
  have := (pr_smul_lt_iff g qt).1 (by rw [h]; show (0 : ℕ) < 2835; norm_num)
  rw [pr_qt] at this
  exact absurd this (by show ¬ (2835 : ℕ) < 2835; norm_num)

theorem smul_eq_of_adj {g : F}
    {u w y : Fin 8991} (hu : g • u = u) (huw : Γc.Adj u w) (huy : Γc.Adj u y)
    (hp : projX g • pr w = pr y) : g • w = y := by
  have h1 : Γc.Adj u (g • w) := by
    have := adjC_smul g huw
    rwa [hu] at this
  exact adjC_inj h1 huy (by rw [pr_smul, hp])

theorem locpC (y : Fin 8991)
    (hy : Γc.Adj pt y) : (∃ g ∈ Fp, g • pt1 = y) ∨ ∃ g ∈ Fp, g • qt = y := by
  have hb := adj_pr hy
  rw [pr_pt] at hb
  rcases locp (pr y) hb with ⟨h, hh, e⟩ | ⟨h, hh, e⟩
  · obtain ⟨g, hg, hgp⟩ := exists_lift h (u := pt) (v := pt) (by rw [pr_pt]; exact (mem_Xp h).1 hh)
    exact Or.inl ⟨g, (mem_Fp g).2 hgp, smul_eq_of_adj hgp adj_pt_pt1 hy (by rw [hg, pr_pt1, e])⟩
  · obtain ⟨g, hg, hgp⟩ := exists_lift h (u := pt) (v := pt) (by rw [pr_pt]; exact (mem_Xp h).1 hh)
    exact Or.inr ⟨g, (mem_Fp g).2 hgp, smul_eq_of_adj hgp adj_pt_qt hy (by rw [hg, pr_qt, e])⟩

theorem locqC (y : Fin 8991)
    (hy : Γc.Adj qt y) : ∃ g ∈ Fq, g • pt = y := by
  have hb := adj_pr hy
  rw [pr_qt] at hb
  obtain ⟨h, hh, e⟩ := locq (pr y) hb
  obtain ⟨g, hg, hgq⟩ := exists_lift h (u := qt) (v := qt) (by rw [pr_qt]; exact (mem_Xq h).1 hh)
  exact ⟨g, (mem_Fq g).2 hgq, smul_eq_of_adj hgq adj_pt_qt.symm hy (by rw [hg, pr_pt, e])⟩

theorem exists_swapC :
    ∃ g : F, projX g = sX ∧ g • pt = pt1 :=
  exists_lift sX (by rw [pr_pt, pr_pt1]; exact sX_spec.1)

@[expose] noncomputable def sC :
    F :=
  Classical.choose exists_swapC

theorem sC_spec :
    sC • pt = pt1 ∧ sC • pt1 = pt := by
  obtain ⟨h1, h2⟩ := Classical.choose_spec exists_swapC
  refine ⟨h2, ?_⟩
  have hA : Γc.Adj pt1 (sC • pt1) := by
    have := adjC_smul sC adj_pt_pt1
    rwa [show sC • pt = pt1 from h2] at this
  refine adjC_inj hA adj_pt_pt1.symm ?_
  rw [pr_smul, show projX sC = sX from h1, pr_pt1, pr_pt]
  exact sX_spec.2

theorem exists_cellC (k : Fin 4) :
    ∃ g : F, projX g = cX k ∧ g • pt = pt :=
  exists_lift (cX k) (by rw [pr_pt]; exact (mem_Xp _).1 (cX_mem k))

theorem exists_cellC' (k : Fin 4) :
    ∃ g : F, projX g = c'X k ∧ g • pt = pt :=
  exists_lift (c'X k) (by rw [pr_pt]; exact (mem_Xp _).1 (c'X_mem k))

@[expose] noncomputable def cAll
    (k : Fin 4) : F :=
  Classical.choose (exists_cellC k)

@[expose] noncomputable def c'All
    (k : Fin 4) : F :=
  Classical.choose (exists_cellC' k)

theorem cAll_spec (k : Fin 4) :
    projX (cAll k) = cX k ∧ cAll k • pt = pt :=
  Classical.choose_spec (exists_cellC k)

theorem c'All_spec (k : Fin 4) :
    projX (c'All k) = c'X k ∧ c'All k • pt = pt :=
  Classical.choose_spec (exists_cellC' k)

theorem adj_pt_smul_qt {g : F} (hg : g • pt = pt) :
    Γc.Adj pt (g • qt) := by
  have := adjC_smul g adj_pt_qt
  rwa [hg] at this

theorem cAll_smul_qt (k : Fin 4) :
    cAll k • qt = ⟨cellc k.1, (liftAt0_spec (coverLocOK_parts.2.2.1 k.1 k.2).1).1⟩ := by
  have hl := liftAt0_spec (coverLocOK_parts.2.2.1 k.1 k.2).1
  refine adjC_inj (adj_pt_smul_qt (cAll_spec k).2) hl.2.2 (Fin.ext ?_)
  rw [pr_smul, (cAll_spec k).1, pr_qt, cX_smul_q]
  exact hl.2.1.symm

theorem c'All_smul_qt (k : Fin 4) :
    c'All k • qt = ⟨cellc' k.1, (liftAt0_spec (coverLocOK_parts.2.2.1 k.1 k.2).2).1⟩ := by
  have hl := liftAt0_spec (coverLocOK_parts.2.2.1 k.1 k.2).2
  refine adjC_inj (adj_pt_smul_qt (c'All_spec k).2) hl.2.2 (Fin.ext ?_)
  rw [pr_smul, (c'All_spec k).1, pr_qt, show c'X k • qV = _ from (cellC'_parts k).2.2.2]
  exact hl.2.1.symm

@[expose] def mixK (j : Fin 2) : Fin 4 := ⟨2 * j.1, by omega⟩

@[expose] noncomputable def cC
    (j : Fin 2) : F :=
  cAll (mixK j)

@[expose] noncomputable def c'C
    (j : Fin 2) : F :=
  c'All (mixK j)

theorem projX_sC :
    projX sC = sX :=
  (Classical.choose_spec exists_swapC).1

theorem projX_cC (j : Fin 2) :
    projX (cC j) = cX (mixK j) :=
  (cAll_spec _).1

theorem projX_c'C (j : Fin 2) :
    projX (c'C j) = c'X (mixK j) :=
  (c'All_spec _).1

theorem cC_mem (j : Fin 2) :
    cC j ∈ Fp :=
  (mem_Fp _).2 (cAll_spec _).2

theorem c'C_mem (j : Fin 2) :
    c'C j ∈ Fp :=
  (mem_Fp _).2 (c'All_spec _).2

theorem adj_pt1_c'C (j : Fin 2) :
    Γc.Adj pt1 (c'C j • qt) := by
  rw [c'C, c'All_smul_qt]
  refine nbrGraph_adj_iff.2 ?_
  show adjB nbrC p1c (cellc' (2 * j.1)) = true
  rcases (by omega : j.1 = 0 ∨ j.1 = 1) with h | h <;> rw [h]
  · exact coverLocOK_parts.2.2.2.2.2.2.2.1
  · exact coverLocOK_parts.2.2.2.2.2.2.2.2

theorem cellC_spec (j : Fin 2) :
    sC • (c'C j • qt) = cC j • qt := by
  have hA : Γc.Adj pt (sC • (c'C j • qt)) := by
    have := adjC_smul sC (adj_pt1_c'C j)
    rwa [sC_spec.2] at this
  refine adjC_inj hA (adj_pt_smul_qt (cAll_spec _).2) ?_
  rw [pr_smul, pr_smul, pr_smul, show projX sC = sX from (Classical.choose_spec exists_swapC).1,
    show projX (c'C j) = c'X (mixK j) from (c'All_spec _).1,
    show projX (cC j) = cX (mixK j) from (cAll_spec _).1, pr_qt, cell_spec]

theorem not_adj_root (k : Fin 4)
    (h : Γc.Adj pt1 (cAll k • qt)) : ∃ j : Fin 2, mixK j = k := by
  rw [cAll_smul_qt] at h
  have hb : adjB nbrC p1c (cellc k.1) = true := nbrGraph_adj_iff.1 h
  rcases (by omega : k.1 = 0 ∨ k.1 = 1 ∨ k.1 = 2 ∨ k.1 = 3) with e | e | e | e
  · exact ⟨0, Fin.ext (by simp [mixK, e])⟩
  · rw [e, coverLocOK_parts.2.2.2.2.2.1] at hb
    exact absurd hb (by simp)
  · exact ⟨1, Fin.ext (by simp [mixK, e])⟩
  · rw [e, coverLocOK_parts.2.2.2.2.2.2.1] at hb
    exact absurd hb (by simp)

theorem admTC_pair {y₁ y₂ : Fin 8991} (h12 : y₁ ≠ y₂) (h : admTC {pt, y₁, y₂}) :
    ((pr y₁).1 < 2835 ∧ 2835 ≤ (pr y₂).1) ∨ (2835 ≤ (pr y₁).1 ∧ (pr y₂).1 < 2835) := by
  obtain ⟨v, hv, hv2, hw⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · exact absurd hv2 (by show ¬ 2835 ≤ (0 : ℕ) % 2997; norm_num)
  · exact Or.inr ⟨hv2, hw y₂ (by simp) (Ne.symm h12)⟩
  · exact Or.inl ⟨hw y₁ (by simp) h12, hv2⟩

theorem admT_pr {y₁ y₂ : Fin 8991} (h12 : y₁ ≠ y₂) (h : admTC {pt, y₁, y₂}) :
    admT {pV, pr y₁, pr y₂} := by
  rcases admTC_pair h12 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨pr y₂, by simp, h2, ?_⟩
    rintro w hw hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · show (0 : ℕ) < 2835; norm_num
    · exact h1
    · exact absurd rfl hne
  · refine ⟨pr y₁, by simp, h1, ?_⟩
    rintro w hw hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · show (0 : ℕ) < 2835; norm_num
    · exact absurd rfl hne
    · exact h2

theorem triC_spec
    (y₁ y₂ : Fin 8991) (h1 : Γc.Adj pt y₁) (h12 : Γc.Adj y₁ y₂) (h2 : Γc.Adj y₂ pt)
    (hT : admTC {pt, y₁, y₂}) :
    (∃ j : Empty, ∃ g ∈ Fp, g • pt1 = y₁ ∧ g • (fun j : Empty => j.elim) j = y₂) ∨
    (∃ k, ∃ g ∈ Fp, g • pt1 = y₁ ∧ g • (cC k • qt) = y₂) ∨
    (∃ k, ∃ g ∈ Fp, g • (cC k • qt) = y₁ ∧ g • pt1 = y₂) := by
  have b1 := adj_pr h1
  have b12 := adj_pr h12
  have b2 := adj_pr h2
  rw [pr_pt] at b1 b2
  rcases tri_spec (pr y₁) (pr y₂) b1 b12 b2 (admT_pr h12.ne hT) with
    ⟨k, h, hh, e1, e2⟩ | ⟨k, h, hh, e1, e2⟩
  · obtain ⟨g, hg, hgp⟩ := exists_lift h (u := pt) (v := pt) (by rw [pr_pt]; exact (mem_Xp h).1 hh)
    have f1 : g • pt1 = y₁ := smul_eq_of_adj hgp adj_pt_pt1 h1 (by rw [hg, pr_pt1, e1])
    have f2 : g • (cAll k • qt) = y₂ := smul_eq_of_adj hgp (adj_pt_smul_qt (cAll_spec k).2)
      h2.symm (by rw [hg, pr_smul, (cAll_spec k).1, pr_qt, e2])
    have hk : Γc.Adj pt1 (cAll k • qt) := by
      have := adjC_smul g⁻¹ h12
      rwa [← f1, ← f2, inv_smul_smul, inv_smul_smul] at this
    obtain ⟨j, rfl⟩ := not_adj_root k hk
    exact Or.inr (Or.inl ⟨j, g, (mem_Fp g).2 hgp, f1, f2⟩)
  · obtain ⟨g, hg, hgp⟩ := exists_lift h (u := pt) (v := pt) (by rw [pr_pt]; exact (mem_Xp h).1 hh)
    have f1 : g • (cAll k • qt) = y₁ := smul_eq_of_adj hgp (adj_pt_smul_qt (cAll_spec k).2) h1
      (by rw [hg, pr_smul, (cAll_spec k).1, pr_qt, e1])
    have f2 : g • pt1 = y₂ := smul_eq_of_adj hgp adj_pt_pt1 h2.symm (by rw [hg, pr_pt1, e2])
    have hk : Γc.Adj pt1 (cAll k • qt) := by
      have := adjC_smul g⁻¹ h12.symm
      rwa [← f1, ← f2, inv_smul_smul, inv_smul_smul] at this
    obtain ⟨j, rfl⟩ := not_adj_root k hk
    exact Or.inr (Or.inr ⟨j, g, (mem_Fp g).2 hgp, f1, f2⟩)

@[expose] noncomputable def coverData :
    TitsDataTwo Γc admTC F Empty (Fin 2) where
  p := pt
  p₁ := pt1
  q := qt
  u := fun j => j.elim
  Xp := Fp
  Xq := Fq
  Xe := Fe
  Xt := fun j => j.elim
  hadj := adjC_smul
  hTinv := admTC_smul
  hconn := preconnected_Γc
  hΓ := triangulableBy_Γc
  hpp₁ := adj_pt_pt1
  hpq := adj_pt_qt
  hsep := smul_qt_ne_pt
  hlocp := locpC
  hlocq := locqC
  hXp := mem_Fp
  hXq := mem_Fq
  hXe := mem_Fe
  hXt := fun j => j.elim
  hτ := fun j => j.elim
  hρ := fun j => j.elim
  s := sC
  hs := sC_spec
  c := cC
  c' := c'C
  hc := cC_mem
  hc' := c'C_mem
  hcell := cellC_spec
  htri := triC_spec

theorem d_pow_three : d ^ 3 = 1 :=
  Subtype.ext (Prod.ext (by simp [d]) (by
    show deck ^ 3 = 1
    exact deck_cube))

end CFSG.Sporadic.SuzRecog.LevelTwoCover
