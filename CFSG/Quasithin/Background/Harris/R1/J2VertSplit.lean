module

public import CFSG.Quasithin.Background.Harris.R1.J2VertTab
public import CFSG.Quasithin.Background.Harris.R1.J2VertHom
public import CFSG.Quasithin.Background.Harris.R1.J2VertPres
public import Certificates.Certificate300203

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] noncomputable def sGen (i : Fin 8) : Equiv.Perm (Fin 64) :=
  permOfArr 64 (sArrs.getD i.val (idA 64))

@[expose] noncomputable def tsGen (j : Fin 3) : Equiv.Perm (Fin 64) :=
  permOfArr 64 (tsArrs.getD j.val (idA 64))

@[expose] noncomputable def zs : Equiv.Perm (Fin 64) := sGen 0

@[expose] noncomputable def x1s : Equiv.Perm (Fin 64) := sGen 1

@[expose] noncomputable def Qs : Subgroup (Equiv.Perm (Fin 64)) :=
  Subgroup.closure (sGen '' {i : Fin 8 | i.val < 5})

@[expose] noncomputable def Ts : Subgroup (Equiv.Perm (Fin 64)) :=
  Subgroup.closure (Set.range tsGen)

theorem sArrs_size : ∀ i < 8, (sArrs.getD i (idA 64)).size = 64 := by decide

theorem tsArrs_size : ∀ i < 3, (tsArrs.getD i (idA 64)).size = 64 := by decide

theorem sArrs_size' : sArrs.size = 8 := by decide

theorem tsArrs_size' : tsArrs.size = 3 := by decide

theorem sArrs5_getD {i : ℕ} (hi : i < 5) :
    (sArrs.extract 0 5).getD i (idA 64) = sArrs.getD i (idA 64) := by
  have hs : i < sArrs.size := by rw [sArrs_size']; omega
  simp [Array.getD_eq_getD_getElem?, hi, hs]

section Cert

theorem sGen_relCheck :
    relCheck 64 sArrs (vRels false) = true :=
  Certificates.certificate300203.1

theorem sGen_tabLower :
    tabLower 64 sArrs tabS 3840 = true :=
  Certificates.certificate300203.2.1

theorem tsGen_tabMem :
    tabMem 64 sArrs tabS tsArrs 3 = true :=
  Certificates.certificate300203.2.2.1

theorem tsGen_tabLower :
    tabLower 64 tsArrs tabTs 256 = true :=
  Certificates.certificate300203.2.2.2.1

theorem tsGen_tabClosed :
    tabClosed 64 tsArrs 3 tabTs = true :=
  Certificates.certificate300203.2.2.2.2.1

theorem qsGen_tabClosed :
    tabClosed 64 (sArrs.extract 0 5) 5 tabQs = true :=
  Certificates.certificate300203.2.2.2.2.2.1

theorem normalLine_check :
    normalLineCheck 64 sArrs tsArrs 3 (buildTab 64 (sArrs.extract 0 5) tabQs) = true :=
  Certificates.certificate300203.2.2.2.2.2.2.1

theorem root_count_z_check :
    rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64))
      (sArrs.getD 0 (idA 64)) = 28 :=
  Certificates.certificate300203.2.2.2.2.2.2.2.2.1

theorem root_count_x_check :
    rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) (sArrs.getD 1 (idA 64)) = 12 :=
  Certificates.certificate300203.2.2.2.2.2.2.2.2.2.1

theorem root_count_zx_check :
    rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64))
      (compA 64 (sArrs.getD 0 (idA 64)) (sArrs.getD 1 (idA 64))) = 12 :=
  Certificates.certificate300203.2.2.2.2.2.2.2.2.2.2

theorem rep_sGen (i : Fin 8) : Rep 64 (sArrs.getD i.val (idA 64)) (sGen i) :=
  (rep_permOfArr (genCheck_spec (genCheck_of_relCheck sGen_relCheck) i.val i.isLt)).1

theorem rep_tsGen (j : Fin 3) : Rep 64 (tsArrs.getD j.val (idA 64)) (tsGen j) :=
  (rep_permOfArr (genCheck_spec (genCheck_of_tabClosed tsGen_tabClosed) j.val j.isLt)).1

theorem sGen_rels :
    ∀ r ∈ vRels false, (r.map fun p => if p.2 then sGen p.1 else (sGen p.1)⁻¹).prod = 1 :=
  prod_eq_one_of_relCheck rep_sGen sGen_relCheck

@[expose] noncomputable def sHom : PG 8 (vRels false) →* Equiv.Perm (Fin 64) :=
  pgHom sGen_rels

theorem sHom_of (i : Fin 8) : sHom (PresentedGroup.of i) = sGen i :=
  pgHom_of sGen_rels i

theorem range_sHom_eq : sHom.range = Subgroup.closure (Set.range sGen) :=
  range_pgHom sGen_rels

theorem good_sGen : ∀ x ∈ sArrs, Good (Subgroup.closure (Set.range sGen)) x :=
  good_of_getD (k := 8) sArrs_size' fun i hi =>
    ⟨sArrs_size i hi, sGen ⟨i, hi⟩, Subgroup.subset_closure ⟨_, rfl⟩, rep_sGen ⟨i, hi⟩⟩

theorem le_card_closure_sGen : 3840 ≤ Nat.card (Subgroup.closure (Set.range sGen)) :=
  le_card_of_tabLower good_sGen sGen_tabLower

theorem card_range_sHom : Nat.card sHom.range = 3840 :=
  card_range_pgHom sGen_rels (card_PG_le false).1 (card_PG_le false).2 le_card_closure_sGen

theorem sHom_injective : Function.Injective sHom :=
  pgHom_injective sGen_rels (card_PG_le false).1 (card_PG_le false).2 le_card_closure_sGen

theorem tsGen_mem_range (j : Fin 3) : tsGen j ∈ sHom.range := by
  rw [range_sHom_eq]
  have hmem := tsGen_tabMem
  unfold tabMem at hmem
  simp only [List.all_eq_true, List.mem_range, List.contains_iff_mem] at hmem
  obtain ⟨-, σ, hσ, rσ⟩ := good_buildTab good_sGen tabS _ (hmem j.val j.isLt)
  have := rσ.unique (rep_tsGen j)
  rwa [this] at hσ

theorem Ts_le : Ts ≤ sHom.range := by
  rw [Ts, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact tsGen_mem_range j

theorem good_tsGen : ∀ x ∈ tsArrs, Good Ts x :=
  good_of_getD (k := 3) tsArrs_size' fun i hi =>
    ⟨tsArrs_size i hi, tsGen ⟨i, hi⟩, Subgroup.subset_closure ⟨_, rfl⟩, rep_tsGen ⟨i, hi⟩⟩

theorem tsTab_complete : ∀ τ ∈ Ts, ∃ x ∈ buildTab 64 tsArrs tabTs, Rep 64 x τ :=
  tab_complete (k := 3) (by
    rintro _ ⟨j, rfl⟩
    exact ⟨j.val, j.isLt, rep_tsGen j⟩) tsGen_tabClosed

theorem Ts_spec :
    (∀ x ∈ buildTab 64 tsArrs tabTs, Good Ts x) ∧ (buildTab 64 tsArrs tabTs).Nodup ∧
      (buildTab 64 tsArrs tabTs).length = 256 ∧
      ∀ τ ∈ Ts, ∃ x ∈ buildTab 64 tsArrs tabTs, Rep 64 x τ := by
  obtain ⟨hl, hnd⟩ := length_of_tabLower tsGen_tabLower
  exact ⟨good_buildTab good_tsGen tabTs, hnd, hl, tsTab_complete⟩

theorem card_Ts : Nat.card Ts = 256 := by
  obtain ⟨hg, hnd, hl, hc⟩ := Ts_spec
  rw [card_eq_length hg hnd hc, hl]

theorem rep_zs : Rep 64 (sArrs.getD 0 (idA 64)) zs := rep_sGen 0

theorem rep_x1s : Rep 64 (sArrs.getD 1 (idA 64)) x1s := rep_sGen 1

private theorem card_root {s : Array ℕ} {s' : Equiv.Perm (Fin 64)} (rs : Rep 64 s s') {N : ℕ}
    (h : rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) s = N) :
    Nat.card {y : Ts // (y : Equiv.Perm (Fin 64)) * x1s = x1s * y ∧
      (y : Equiv.Perm (Fin 64)) * y = s'} = N := by
  obtain ⟨hg, hnd, hl, hc⟩ := Ts_spec
  rw [card_subtype_eq hg hnd hc (fun σ => σ * x1s = x1s * σ ∧ σ * σ = s')
    (fun x => eqA 64 (compA 64 x (sArrs.getD 1 (idA 64))) (compA 64 (sArrs.getD 1 (idA 64)) x) &&
      eqA 64 (compA 64 x x) s)
    (fun x σ rx => rep_root_iff rep_x1s rs rx)]
  exact h

theorem card_root_z_Ts :
    Nat.card {y : Ts // (y : Equiv.Perm (Fin 64)) * x1s = x1s * y ∧
      (y : Equiv.Perm (Fin 64)) * y = zs} = 28 :=
  card_root rep_zs root_count_z_check

theorem card_root_x_Ts :
    Nat.card {y : Ts // (y : Equiv.Perm (Fin 64)) * x1s = x1s * y ∧
      (y : Equiv.Perm (Fin 64)) * y = x1s} = 12 :=
  card_root rep_x1s root_count_x_check

theorem card_root_zx_Ts :
    Nat.card {y : Ts // (y : Equiv.Perm (Fin 64)) * x1s = x1s * y ∧
      (y : Equiv.Perm (Fin 64)) * y = zs * x1s} = 12 :=
  card_root (rep_compA rep_zs rep_x1s) root_count_zx_check

theorem qsTab_complete : ∀ τ ∈ Qs, ∃ x ∈ buildTab 64 (sArrs.extract 0 5) tabQs, Rep 64 x τ :=
  tab_complete (k := 5) (by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i.val, hi, by rw [sArrs5_getD hi]; exact rep_sGen i⟩)
    qsGen_tabClosed

theorem normalLine_Ts : ∀ v ∈ Qs, v * v = 1 → v ≠ 1 → v ≠ zs →
    (∀ g ∈ Ts, g * v * g⁻¹ = v ∨ g * v * g⁻¹ = zs * v) → v = x1s ∨ v = zs * x1s := by
  intro v hv hsq h1 hz hn
  obtain ⟨x, hx, rx⟩ := qsTab_complete v hv
  have hall := normalLine_check
  unfold normalLineCheck at hall
  simp only [List.all_eq_true] at hall
  have h := hall x hx
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  have e1 : eqA 64 (compA 64 x x) (idA 64) = true :=
    (eqA_iff (rep_compA rx rx) rep_idA).2 hsq
  have e2 : eqA 64 x (idA 64) = false := by
    rw [Bool.eq_false_iff]
    exact fun h' => h1 ((eqA_iff rx rep_idA).1 h')
  have e3 : eqA 64 x (sArrs.getD 0 (idA 64)) = false := by
    rw [Bool.eq_false_iff]
    exact fun h' => hz ((eqA_iff rx rep_zs).1 h')
  have e4 : ((List.range 3).all fun j =>
      eqA 64 (compA 64 (compA 64 (tsArrs.getD j (idA 64)) x) (invCand 64 (tsArrs.getD j (idA 64)))) x
        || eqA 64 (compA 64 (compA 64 (tsArrs.getD j (idA 64)) x)
          (invCand 64 (tsArrs.getD j (idA 64)))) (compA 64 (sArrs.getD 0 (idA 64)) x)) = true := by
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    have rj := rep_tsGen ⟨j, hj⟩
    have rji : Rep 64 (invCand 64 (tsArrs.getD j (idA 64))) (tsGen ⟨j, hj⟩)⁻¹ :=
      (rep_permOfArr (genCheck_spec (genCheck_of_tabClosed tsGen_tabClosed) j hj)).2
    have rc := rep_compA (rep_compA rj rx) rji
    have hg : tsGen ⟨j, hj⟩ ∈ Ts := Subgroup.subset_closure ⟨_, rfl⟩
    rw [Bool.or_eq_true, eqA_iff rc rx, eqA_iff rc (rep_compA rep_zs rx)]
    exact hn _ hg
  rcases h with (((((h | h) | h) | h) | h) | h)
  · rw [e1] at h; exact absurd h (by decide)
  · rw [e2] at h; exact absurd h (by decide)
  · rw [e3] at h; exact absurd h (by decide)
  · rw [e4] at h; exact absurd h (by decide)
  · exact Or.inl ((eqA_iff rx rep_x1s).1 h)
  · exact Or.inr ((eqA_iff rx (rep_compA rep_zs rep_x1s)).1 h)

end Cert

end CFSG.Quasithin.Background.Harris.R1.J2Vert
