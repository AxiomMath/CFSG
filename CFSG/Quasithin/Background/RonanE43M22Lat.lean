module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import CFSG.Quasithin.Background.RonanE43FamilyS5
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  CFSG.QuasithinUnique.Unc25K1.Six Equiv

section Joins

variable {G : Type} [Group G] [Finite G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  {enc : G → R}

theorem join_spec (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.joinsOK enc = true) (a b d : ℕ)
    (hj : c.joins.any (fun j => j.1 == a && j.2.1 == b && j.2.2.1 == d) = true) :
    Subgroup.closure {g | g ∈ (c.tGens :: c.lat).getD a []} ⊔
        Subgroup.closure {g | g ∈ (c.tGens :: c.lat).getD b []} =
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat).getD d []} := by
  simp only [LatCert.joinsOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_range] at hc
  obtain ⟨-, hjoin⟩ := hc
  obtain ⟨⟨j1, j2, j3, ws⟩, hjmem, hja⟩ := List.any_eq_true.mp hj
  simp only [Bool.and_eq_true, beq_iff_eq] at hja
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hja
  have h1 := hjoin _ hjmem
  simp only at h1
  cases hma : (c.members enc)[j1]? with
  | none => simp [hma] at h1
  | some pa =>
  cases hmb : (c.members enc)[j2]? with
  | none => simp [hma, hmb] at h1
  | some pb =>
  cases hmc : (c.members enc)[j3]? with
  | none => simp [hma, hmb, hmc] at h1
  | some pc =>
  have hlt : j3 < (c.tGens :: c.lat).length := by
    have := (List.getElem?_eq_some_iff.mp hmc).1
    simpa [LatCert.members] using this
  rw [hma, hmb, hmc] at h1
  simp only at h1
  have hmem : ∀ i (p : List G × Std.HashSet R), (c.members enc)[i]? = some p →
      p = ((c.tGens :: c.lat).getD i [], elts enc c.depth ((c.tGens :: c.lat).getD i [])) := by
    intro i p hp
    simp only [LatCert.members, List.getElem?_map] at hp
    cases hi : (c.tGens :: c.lat)[i]? with
    | none => simp [hi] at hp
    | some L =>
      rw [hi] at hp
      simp only [Option.map_some, Option.some.injEq] at hp
      subst hp
      simp [List.getD_eq_getElem?_getD, hi]
  have hpa := hmem _ _ hma
  have hpb := hmem _ _ hmb
  have hpc := hmem _ _ hmc
  subst hpa hpb hpc
  have hcl' : closedH (((c.tGens :: c.lat).getD j3 []).map enc)
      (elts enc c.depth ((c.tGens :: c.lat).getD j3 [])) = true := by
    have hL : (c.tGens :: c.lat).getD j3 [] ∈ c.tGens :: c.lat := by
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    exact c.members_closed hcl _ hL
  have := closure_eq_of_eqCert h hcl' h1
  rw [← this]
  have hset : {g : G | g ∈ (c.tGens :: c.lat).getD j1 [] ++ (c.tGens :: c.lat).getD j2 []} =
      {g | g ∈ (c.tGens :: c.lat).getD j1 []} ∪ {g | g ∈ (c.tGens :: c.lat).getD j2 []} := by
    ext g
    simp
  rw [hset, Subgroup.closure_union]

theorem joinsOK_of_check {c : LatCert G} (hc : c.check enc = true) : c.joinsOK enc = true := by
  simp only [LatCert.check, Bool.and_eq_true] at hc
  exact hc.1.1.2

end Joins

section M22


abbrev Lm (j : ℕ) : List (Perm (Fin 22)) := (cert.tGens :: cert.lat).getD j []

abbrev Cm (j : ℕ) : Subgroup (Perm (Fin 22)) := Subgroup.closure {g | g ∈ Lm j}

abbrev Pm (j : ℕ) : Subgroup ↥Mgrp := (Cm j).subgroupOf Mgrp

theorem m22_len : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]

theorem m22_Cm_card (j : ℕ) (hj : j < 6) : Nat.card (Cm j) = cert.sizes.getD j 0 := by
  have hcl := LatCert.closedOK_of_check cert_check
  have hsz := LatCert.sizesOK_of_check cert_check
  have hj' : j < (cert.tGens :: cert.lat).length := by rw [m22_len]; exact hj
  have := cert.card_member_idx (rawIsEnc 22) hcl hsz j hj'
  have h2 : Lm j = (cert.tGens :: cert.lat)[j] := List.getD_eq_getElem _ _ hj'
  show Nat.card (Subgroup.closure {g | g ∈ Lm j}) = _
  rw [h2]
  exact this

theorem m22_join (a b d : ℕ)
    (hj : cert.joins.any (fun j => j.1 == a && j.2.1 == b && j.2.2.1 == d) = true) :
    Cm a ⊔ Cm b = Cm d :=
  join_spec (rawIsEnc 22) cert (LatCert.closedOK_of_check cert_check)
    (joinsOK_of_check cert_check) a b d hj

theorem m22_sizes_four : ∀ j : ℕ, j < 6 → cert.sizes.getD j 0 = 443520 → j = 4 := by decide

theorem m22_sizes_1920 : ∀ j : ℕ, j < 6 → cert.sizes.getD j 0 = 1920 → j = 2 := by decide

theorem m22_sizes_384 : ∀ j : ℕ, j < 6 → cert.sizes.getD j 0 = 384 → j = 1 ∨ j = 5 := by decide

theorem m22_Cm_four : Cm 4 = Mgrp := by
  have hck := cert_check
  obtain ⟨j, hj0, hLM, hYL, hcard⟩ :=
    cert.overgroup_cases_idx (rawIsEnc 22) hck (⊤ : Subgroup ↥Mgrp) le_top
  have hj : j < 6 := by rw [← m22_len]; exact hj0
  have hMle : Mgrp ≤ Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[j]} := fun g hg => by
    have : (⟨g, hg⟩ : ↥Mgrp) ∈ (⊤ : Subgroup ↥Mgrp) := Subgroup.mem_top _
    rw [hYL] at this
    exact this
  have heq := le_antisymm hLM hMle
  have hM : Nat.card Mgrp = 443520 :=
    cert.card_m (rawIsEnc 22) (LatCert.closedOK_of_check hck) (LatCert.sizesOK_of_check hck)
  rw [heq, hM] at hcard
  have hj4 := m22_sizes_four j hj hcard.symm
  subst hj4
  have h4 : Lm 4 = (cert.tGens :: cert.lat)[4]'hj0 := List.getD_eq_getElem _ _ hj0
  show Subgroup.closure {g | g ∈ Lm 4} = Mgrp
  rw [h4]
  exact heq

theorem m22_Cm_le (j : ℕ) (hj : j < 6) : Cm j ≤ Mgrp := by
  rw [← m22_Cm_four]
  have : Cm j ⊔ Cm 4 = Cm 4 := by
    interval_cases j <;> exact m22_join _ 4 4 (by decide +kernel)
  exact (le_sup_left : Cm j ≤ Cm j ⊔ Cm 4).trans this.le

theorem m22_U_le (j : ℕ) (hj : j < 6) : Cm 0 ≤ Cm j := by
  have : Cm 0 ⊔ Cm j = Cm j := by
    interval_cases j <;> exact m22_join 0 _ _ (by decide +kernel)
  exact (le_sup_left : Cm 0 ≤ Cm 0 ⊔ Cm j).trans this.le

theorem m22_one_le_two : Cm 1 ≤ Cm 2 := by
  have : Cm 1 ⊔ Cm 2 = Cm 2 := m22_join 1 2 2 (by decide +kernel)
  exact (le_sup_left : Cm 1 ≤ Cm 1 ⊔ Cm 2).trans this.le

theorem m22_two_sup_five : Cm 2 ⊔ Cm 5 = Mgrp := by
  rw [← m22_Cm_four]
  exact m22_join 2 5 4 (by decide +kernel)

theorem m22_Pm_card (j : ℕ) (hj : j < 6) : Nat.card (Pm j) = cert.sizes.getD j 0 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (m22_Cm_le j hj)).toEquiv]
  exact m22_Cm_card j hj

theorem m22_isSylow : IsSylowTwoOf Ugrp ⊤ :=
  cert.isSylowTwoOf_top (rawIsEnc 22) cert_check (k := 7) (m := 3465) (by decide) (by decide)
    (by omega)

theorem m22_Pm_zero : Ugrp = Pm 0 := rfl

theorem m22_U_le_Pm (j : ℕ) (hj : j < 6) : Ugrp ≤ Pm j :=
  Subgroup.subgroupOf_mono Mgrp (m22_U_le j hj)

theorem m22_overgroup (Y : Subgroup ↥Mgrp) (hY : Ugrp ≤ Y) : ∃ j : ℕ, j < 6 ∧ Y = Pm j := by
  obtain ⟨j, hj0, hLM, hYL, hcard⟩ := cert.overgroup_cases_idx (rawIsEnc 22) cert_check Y hY
  have hj : j < 6 := by rw [← m22_len]; exact hj0
  have h2 : Lm j = (cert.tGens :: cert.lat)[j] := List.getD_eq_getElem _ _ hj0
  refine ⟨j, hj, ?_⟩
  rw [hYL]
  show _ = (Subgroup.closure {g | g ∈ Lm j}).subgroupOf Mgrp
  rw [h2]
  rfl

theorem map_map_symm {X : Type*} [Group X] (α : MulAut X) (H : Subgroup X) :
    (H.map α.toMonoidHom).map α.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : α.symm.toMonoidHom.comp α.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem m22_symm_normalizes (α : MulAut ↥Mgrp) (hα : Ugrp.map α.toMonoidHom = Ugrp) :
    Ugrp.map α.symm.toMonoidHom = Ugrp := by
  calc Ugrp.map α.symm.toMonoidHom = (Ugrp.map α.toMonoidHom).map α.symm.toMonoidHom := by
        rw [hα]
    _ = Ugrp := map_map_symm α Ugrp

theorem m22_inv_two (α : MulAut ↥Mgrp) (hα : Ugrp.map α.toMonoidHom = Ugrp) :
    (Pm 2).map α.toMonoidHom = Pm 2 := by
  have hY : Ugrp ≤ (Pm 2).map α.toMonoidHom := by
    rw [← hα]
    exact Subgroup.map_mono (m22_U_le_Pm 2 (by norm_num))
  obtain ⟨j, hj, hYj⟩ := m22_overgroup _ hY
  have hcard : cert.sizes.getD j 0 = 1920 := by
    rw [← m22_Pm_card j hj, ← hYj, Subgroup.card_map_of_injective α.injective,
      m22_Pm_card 2 (by norm_num)]
    rfl
  have : j = 2 := m22_sizes_1920 j hj hcard
  subst this
  exact hYj

theorem m22_inv_five (α : MulAut ↥Mgrp) (hα : Ugrp.map α.toMonoidHom = Ugrp) :
    (Pm 5).map α.toMonoidHom = Pm 5 := by
  have hY : Ugrp ≤ (Pm 5).map α.toMonoidHom := by
    rw [← hα]
    exact Subgroup.map_mono (m22_U_le_Pm 5 (by norm_num))
  obtain ⟨j, hj, hYj⟩ := m22_overgroup _ hY
  have hcard : cert.sizes.getD j 0 = 384 := by
    rw [← m22_Pm_card j hj, ← hYj, Subgroup.card_map_of_injective α.injective,
      m22_Pm_card 5 (by norm_num)]
    rfl
  rcases m22_sizes_384 j hj hcard with rfl | rfl
  · exfalso
    have h12 : Pm 1 ≤ Pm 2 := Subgroup.subgroupOf_mono Mgrp m22_one_le_two
    have h1 : (Pm 5).map α.toMonoidHom ≤ Pm 2 := by
      rw [hYj]
      exact h12
    have h2 : Pm 5 ≤ Pm 2 := by
      have := Subgroup.map_mono (f := α.symm.toMonoidHom) h1
      rwa [map_map_symm, m22_inv_two α.symm (m22_symm_normalizes α hα)] at this
    have h3 : Cm 5 ≤ Cm 2 := by
      have := Subgroup.map_mono (f := Mgrp.subtype) h2
      rwa [Subgroup.map_subgroupOf_eq_of_le (m22_Cm_le 5 (by norm_num)),
        Subgroup.map_subgroupOf_eq_of_le (m22_Cm_le 2 (by norm_num))] at this
    have h4 : Cm 2 ⊔ Cm 5 = Cm 2 := sup_eq_left.mpr h3
    have h5 := m22_two_sup_five
    rw [h4, ← m22_Cm_four] at h5
    have h6 := congrArg (fun H : Subgroup (Perm (Fin 22)) => Nat.card H) h5
    rw [m22_Cm_card 2 (by norm_num), m22_Cm_card 4 (by norm_num)] at h6
    exact absurd h6 (by decide)
  · exact hYj

theorem m22_hAL : Subgroup.closure {g | g ∈ p5Gens} ≤ Cm 2 := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have h1920 : cert.sizes.getD 2 0 = 1920 := rfl
  have ha := List.all_eq_true.mp incl5 2 (by simp)
  simp only [h1920, bne_self_eq_false, Bool.false_or] at ha
  have hlen2 : 2 < (cert.tGens :: cert.lat).length := by rw [m22_len]; norm_num
  have hmem : (cert.tGens :: cert.lat)[2] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen2
  have h2 : Lm 2 = (cert.tGens :: cert.lat)[2] := List.getD_eq_getElem _ _ hlen2
  show _ ≤ Subgroup.closure {g | g ∈ Lm 2}
  rw [h2, Subgroup.closure_le]
  intro g hg
  have := List.all_eq_true.mp ha g hg
  rw [List.getD_eq_getElem _ _ hlen2] at this
  exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth (cert.members_closed hcl _ hmem) g).mpr
    (Std.HashSet.contains_iff_mem.mp this)

theorem m22_Acard : Nat.card (Subgroup.closure {g | g ∈ p5Gens}) = 960 := ext5.1

theorem m22_comm : ⁅Cm 2, Cm 2⁆ = Subgroup.closure {g | g ∈ p5Gens} := by
  have hAL := m22_hAL
  have h1 : ⁅Cm 2, Cm 2⁆ ≤ Subgroup.closure {g | g ∈ p5Gens} :=
    commutator_le_of_card_eq_two_mul hAL (by
      rw [m22_Cm_card 2 (by norm_num), m22_Acard]
      rfl)
  have hperf : ⁅Subgroup.closure {g | g ∈ p5Gens}, Subgroup.closure {g | g ∈ p5Gens}⁆ =
      Subgroup.closure {g | g ∈ p5Gens} := perfect_of_perfOK (rawIsEnc 22) perf5_ok
  refine le_antisymm h1 ?_
  calc Subgroup.closure {g | g ∈ p5Gens}
      = ⁅Subgroup.closure {g | g ∈ p5Gens}, Subgroup.closure {g | g ∈ p5Gens}⁆ := hperf.symm
    _ ≤ ⁅Cm 2, Cm 2⁆ := Subgroup.commutator_mono hAL hAL

abbrev Am : Subgroup ↥Mgrp := (Subgroup.closure {g | g ∈ p5Gens}).subgroupOf Mgrp

theorem m22_hAM : Subgroup.closure {g | g ∈ p5Gens} ≤ Mgrp :=
  m22_hAL.trans (m22_Cm_le 2 (by norm_num))

theorem m22_Am_le : Am ≤ Pm 2 := Subgroup.subgroupOf_mono Mgrp m22_hAL

theorem m22_Am_card : Nat.card Am = 960 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m22_hAM).toEquiv]
  exact m22_Acard

theorem m22_Am_eq_comm : ⁅Pm 2, Pm 2⁆ = Am := by
  apply Subgroup.map_injective Mgrp.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (m22_Cm_le 2 (by norm_num)),
    Subgroup.map_subgroupOf_eq_of_le m22_hAM]
  exact m22_comm

theorem m22_inv_Am (α : MulAut ↥Mgrp) (hα : Ugrp.map α.toMonoidHom = Ugrp) :
    Am.map α.toMonoidHom = Am := by
  rw [← m22_Am_eq_comm, Subgroup.map_commutator, m22_inv_two α hα]

theorem m22_Am_sup_U : Am ⊔ Ugrp = Pm 2 := by
  have hle : Am ⊔ Ugrp ≤ Pm 2 := sup_le m22_Am_le (m22_U_le_Pm 2 (by norm_num))
  have hcP : Nat.card (Pm 2) = 1920 := by rw [m22_Pm_card 2 (by norm_num)]; rfl
  have hcU : Nat.card Ugrp = 128 := by rw [m22_Pm_zero, m22_Pm_card 0 (by norm_num)]; rfl
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : Am ≤ Am ⊔ Ugrp)
  have hSdvd := Subgroup.card_dvd_of_le hle
  rw [m22_Am_card] at hm
  rw [hm, hcP] at hSdvd
  have hm2 : m ∣ 2 := by
    have : 960 * m ∣ 960 * 2 := by simpa using hSdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with rfl | rfl
  · exfalso
    have h1 : Am = Am ⊔ Ugrp :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, m22_Am_card])
    have h2 : Ugrp ≤ Am := by
      rw [h1]
      exact le_sup_right
    have h3 := Subgroup.card_dvd_of_le h2
    rw [hcU, m22_Am_card] at h3
    exact absurd h3 (by decide)
  · exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem m22_two_sup_five' : Pm 2 ⊔ Pm 5 = ⊤ := by
  apply Subgroup.map_injective Mgrp.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (m22_Cm_le 2 (by norm_num)),
    Subgroup.map_subgroupOf_eq_of_le (m22_Cm_le 5 (by norm_num)), m22_two_sup_five,
    Subgroup.map_top, Subgroup.range_subtype]

theorem m22_A5 : ∃ V' : Subgroup (Perm (Fin 22)),
    IsA5Ext (Subgroup.closure {g | g ∈ p5Gens}) V' := by
  obtain ⟨-, V₀, hV₀n, hVc, hVsq, hVcard, ⟨e⟩⟩ := ext5
  refine ⟨V₀.map (Subgroup.closure {g | g ∈ p5Gens}).subtype, Subgroup.map_subtype_le _,
    (IsPGroup.of_card (n := 4) hVcard).map _, ?_⟩
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' V₀), e.surjective.comp (QuotientGroup.mk'_surjective V₀),
    ?_⟩
  have h1 : (V₀.map (Subgroup.closure {g | g ∈ p5Gens}).subtype).subgroupOf
      (Subgroup.closure {g | g ∈ p5Gens}) = V₀ :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) V₀
  rw [h1]
  ext x
  simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

theorem m22_data : ∃ A V P : Subgroup ↥Mgrp, IsSylowTwoOf Ugrp ⊤ ∧ IsA5Ext A V ∧ Ugrp ≤ P ∧
    Nat.card P = 3 * Nat.card Ugrp ∧ (A ⊔ Ugrp) ⊔ P = ⊤ ∧
    ∀ α : MulAut ↥Mgrp, Ugrp.map α.toMonoidHom = Ugrp →
      A.map α.toMonoidHom = A ∧ P.map α.toMonoidHom = P := by
  obtain ⟨V', hV'⟩ := m22_A5
  refine ⟨Am, V'.subgroupOf Mgrp, Pm 5, m22_isSylow, ?_, m22_U_le_Pm 5 (by norm_num), ?_, ?_, ?_⟩
  · exact IsA5Ext.subgroupOf hV' m22_hAM
  · have hcU : Nat.card Ugrp = 128 := by rw [m22_Pm_zero, m22_Pm_card 0 (by norm_num)]; rfl
    rw [m22_Pm_card 5 (by norm_num), hcU]
    rfl
  · rw [m22_Am_sup_U]
    exact m22_two_sup_five'
  · intro α hα
    exact ⟨m22_inv_Am α hα, m22_inv_five α hα⟩

end M22

end CFSG.Quasithin.RonanE43
