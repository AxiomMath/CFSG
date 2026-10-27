module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Def

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

theorem map_transvection_wedgeBasis_fix {R : Type*} [CommRing R] {n k : ℕ} {a b : Fin n}
    (hab : a ≠ b) (c : R) (I : Set.powersetCard (Fin n) k) (h : ¬ (b ∈ I.val ∧ a ∉ I.val)) :
    exteriorPower.map k (CFSG.LieType.Chevalley.ExteriorCube.transvLin a b c)
      (CFSG.LieType.Chevalley.ExteriorCube.wedgeBasis I) =
      CFSG.LieType.Chevalley.ExteriorCube.wedgeBasis I := by
  unfold CFSG.LieType.Chevalley.ExteriorCube.wedgeBasis
  rw [exteriorPower.map_apply_ιMulti_family]
  simp only [ιMulti_family]
  set v : Fin k → Fin n → R := (fun i : Fin n => (Pi.single i 1 : Fin n → R)) ∘
    CFSG.LieType.Chevalley.ExteriorCube.enum I with hv
  by_cases hb : b ∈ I.val
  · have ha : a ∈ I.val := by
      by_contra ha
      exact h ⟨hb, ha⟩
    obtain ⟨t₀, ht₀⟩ := CFSG.LieType.Chevalley.ExteriorCube.exists_enum_eq hb
    have hcomp : (CFSG.LieType.Chevalley.ExteriorCube.transvLin a b c ∘
        fun i : Fin n => (Pi.single i 1 : Fin n → R)) ∘
          CFSG.LieType.Chevalley.ExteriorCube.enum I =
        Function.update v t₀ (Pi.single b 1 + c • Pi.single a 1) := by
      funext t
      by_cases ht : t = t₀
      · subst ht
        rw [Function.update_self]
        change CFSG.LieType.Chevalley.ExteriorCube.transvLin a b c
          (Pi.single (CFSG.LieType.Chevalley.ExteriorCube.enum I t) 1) = _
        rw [CFSG.LieType.Chevalley.ExteriorCube.transvLin_single, ht₀]
        simp
      · rw [Function.update_of_ne ht]
        have hne : CFSG.LieType.Chevalley.ExteriorCube.enum I t ≠ b := fun h' =>
          ht ((CFSG.LieType.Chevalley.ExteriorCube.enum I).injective (h'.trans ht₀.symm))
        change CFSG.LieType.Chevalley.ExteriorCube.transvLin a b c
          (Pi.single (CFSG.LieType.Chevalley.ExteriorCube.enum I t) 1) = v t
        rw [CFSG.LieType.Chevalley.ExteriorCube.transvLin_single]
        simp [hne, hv]
    rw [hcomp, AlternatingMap.map_update_add, AlternatingMap.map_update_smul]
    have hself : Function.update v t₀ (Pi.single b 1) = v := by
      rw [← ht₀]
      exact Function.update_eq_self t₀ v
    rw [hself]
    obtain ⟨t₁, ht₁⟩ := CFSG.LieType.Chevalley.ExteriorCube.exists_enum_eq ha
    have hne : t₀ ≠ t₁ := fun h' => hab (by rw [← ht₁, ← ht₀, h'])
    have hzero : ιMulti R k (Function.update v t₀ (Pi.single a 1)) = 0 := by
      refine AlternatingMap.map_eq_zero_of_eq _ _ (i := t₀) (j := t₁) ?_ hne
      rw [Function.update_self, Function.update_of_ne hne.symm]
      simp [hv, ht₁]
    rw [hzero, smul_zero, add_zero]
  · have hvec : (CFSG.LieType.Chevalley.ExteriorCube.transvLin a b c ∘
        fun i : Fin n => (Pi.single i 1 : Fin n → R)) ∘
          CFSG.LieType.Chevalley.ExteriorCube.enum I = v := by
      funext t
      have hne : CFSG.LieType.Chevalley.ExteriorCube.enum I t ≠ b := fun h' =>
        hb (h' ▸ CFSG.LieType.Chevalley.ExteriorCube.enum_mem I t)
      change CFSG.LieType.Chevalley.ExteriorCube.transvLin a b c
        (Pi.single (CFSG.LieType.Chevalley.ExteriorCube.enum I t) 1) = v t
      rw [CFSG.LieType.Chevalley.ExteriorCube.transvLin_single]
      simp [hne, hv]
    rw [hvec]

theorem rho_transvGL_cubeBasis_fix {a b : Fin 6} (hne : a ≠ b) (c : K)
    (I : Set.powersetCard (Fin 6) 3) (h : ¬ (b ∈ I.val ∧ a ∉ I.val)) :
    rho K (transvGL K a b hne c) (cubeBasis K I) = cubeBasis K I := by
  rw [rho_apply_eq_map, transvGL_val, cubeBasis_eq_wedgeBasis]
  exact map_transvection_wedgeBasis_fix hne c I h

theorem transvGL_mem_StatedSL {a b : Fin 6} (hne : a ≠ b) (c : K) :
    transvGL K a b hne c ∈ StatedSL 6 K := by
  apply Subgroup.subset_closure
  show (transvGL K a b hne c : Matrix (Fin 6) (Fin 6) K).det = 1
  rw [transvGL_val]
  exact Matrix.det_transvection_of_ne a b hne c

theorem rootSet_ne {a b : Fin 6} (hab : a.val % 2 = 0 ∧ b.val % 2 = 1) : a ≠ b := by
  rintro rfl
  obtain ⟨h1, h2⟩ := hab
  omega

theorem U0_le_Gam : U0 K ≤ Gam K := by
  show Subgroup.closure (rootSet K) ≤ Gam K
  rw [Subgroup.closure_le]
  rintro x ⟨a, b, hab, c, rfl⟩
  exact Subgroup.mem_map_of_mem (rhoEquiv K) (transvGL_mem_StatedSL (rootSet_ne hab) c)

theorem p0_fix_of_odd {a b : Fin 6} (hne : a ≠ b) (c : K) (hb : b.val % 2 = 1) :
    rho K (transvGL K a b hne c) (p0 K) = p0 K := by
  show rho K (transvGL K a b hne c) (cubeBasis K S024) = cubeBasis K S024
  refine rho_transvGL_cubeBasis_fix hne c S024 ?_
  rintro ⟨hbI, -⟩
  have key : ∀ y : Fin 6, y.val % 2 = 1 → y ∉ ({0, 2, 4} : Finset (Fin 6)) := by
    decide
  have hS : S024.val = ({0, 2, 4} : Finset (Fin 6)) := rfl
  rw [hS] at hbI
  exact key b hb hbI

theorem rhoEquiv_p0_fix {a b : Fin 6} (hne : a ≠ b) (c : K) (hb : b.val % 2 = 1) :
    rhoEquiv K (transvGL K a b hne c) (p0 K) = p0 K :=
  (rhoEquiv_apply _ _).trans (p0_fix_of_odd hne c hb)

theorem U0_fix : ∀ u ∈ U0 K, u (p0 K) = p0 K := by
  intro u hu
  refine Subgroup.closure_induction (p := fun u _ => u (p0 K) = p0 K) ?_ ?_ ?_ ?_ hu
  · rintro x ⟨a, b, hab, c, rfl⟩
    exact rhoEquiv_p0_fix (rootSet_ne hab) c hab.2
  · rfl
  · intro x y _ _ hx hy
    have hx' : x (p0 K) = p0 K := hx
    have hy' : y (p0 K) = p0 K := hy
    show x (y (p0 K)) = p0 K
    rw [hy', hx']
  · intro x _ hx
    have hx' : x (p0 K) = p0 K := hx
    have h1 : (x⁻¹ * x) (p0 K) = p0 K := by simp
    have h2 : x⁻¹ (x (p0 K)) = p0 K := h1
    rw [hx'] at h2
    exact h2

theorem rho_transvGL_r0 (c : K) :
    rho K (transvGL K 2 3 (by decide) c) (r0 K) = r0 K + c • p0 K := by
  have h : (3 : Fin 6) ∈ S034.val ∧ (2 : Fin 6) ∉ S034.val := by decide
  have hrep : replSet S034 2 3 h.1 h.2 = S024 := by
    apply Subtype.ext
    show insert (2 : Fin 6) (S034.val.erase (3 : Fin 6)) = S024.val
    decide
  unfold r0 p0
  rw [rho_transvGL_cubeBasis (a := 2) (b := 3) (Or.inl (by decide)) (by decide) c S034,
    dif_pos h, hrep]

theorem r0_fix_of_ne {a b : Fin 6} (hne : a ≠ b) (c : K) (ha : a.val % 2 = 0)
    (hb : b.val % 2 = 1) (h23 : ¬ (a = 2 ∧ b = 3)) :
    rho K (transvGL K a b hne c) (r0 K) = r0 K := by
  show rho K (transvGL K a b hne c) (cubeBasis K S034) = cubeBasis K S034
  refine rho_transvGL_cubeBasis_fix hne c S034 ?_
  rintro ⟨hbI, haI⟩
  have key : ∀ x y : Fin 6, x.val % 2 = 0 → y.val % 2 = 1 → ¬ (x = 2 ∧ y = 3) →
      ¬ (y ∈ ({0, 3, 4} : Finset (Fin 6)) ∧ x ∉ ({0, 3, 4} : Finset (Fin 6))) := by
    decide
  have hS : S034.val = ({0, 3, 4} : Finset (Fin 6)) := rfl
  rw [hS] at hbI haI
  exact key a b ha hb h23 ⟨hbI, haI⟩

theorem span_fix {g : Cube K ≃ₗ[K] Cube K} (hg : g (p0 K) = p0 K) {v : Cube K}
    (hv : v ∈ Submodule.span K {p0 K}) : g v ∈ Submodule.span K {p0 K} := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, hg]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

theorem rootSet_r0 (u : Cube K ≃ₗ[K] Cube K) (hu : u ∈ rootSet K) :
    u (r0 K) - r0 K ∈ Submodule.span K {p0 K} := by
  obtain ⟨a, b, hab, c, rfl⟩ := hu
  rw [rhoEquiv_apply]
  by_cases h23 : a = 2 ∧ b = 3
  · obtain ⟨rfl, rfl⟩ := h23
    have hd : rho K (transvGL K 2 3 (by decide) c) (r0 K) - r0 K = c • p0 K := by
      rw [rho_transvGL_r0]
      abel
    rw [hd]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · rw [r0_fix_of_ne (rootSet_ne hab) c hab.1 hab.2 h23, sub_self]
    exact Submodule.zero_mem _

theorem r0_mem_W0 : r0 K ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  rw [mem_Wsp]
  intro u hu
  refine Subgroup.closure_induction
    (p := fun u _ => u (r0 K) - r0 K ∈ Submodule.span K {p0 K}) ?_ ?_ ?_ ?_ hu
  · intro x hx
    exact rootSet_r0 x hx
  · simp
  · intro x y hx hy hxp hyp
    have hxp' : x (r0 K) - r0 K ∈ Submodule.span K {p0 K} := hxp
    have hyp' : y (r0 K) - r0 K ∈ Submodule.span K {p0 K} := hyp
    have hsplit : (x * y) (r0 K) - r0 K = x (y (r0 K) - r0 K) + (x (r0 K) - r0 K) := by
      show x (y (r0 K)) - r0 K = _
      rw [map_sub]
      abel
    show (x * y) (r0 K) - r0 K ∈ Submodule.span K {p0 K}
    rw [hsplit]
    exact add_mem (span_fix (U0_fix (K := K) x hx) hyp') hxp'
  · intro x hx hxp
    have hxp' : x (r0 K) - r0 K ∈ Submodule.span K {p0 K} := hxp
    have hxU : x ∈ U0 K := hx
    have hinvp : x⁻¹ (p0 K) = p0 K := U0_fix (K := K) x⁻¹ (inv_mem hxU)
    have hxr : x⁻¹ (x (r0 K)) = r0 K := by
      have h1 : (x⁻¹ * x) (r0 K) = r0 K := by simp
      exact h1
    have hsplit : x⁻¹ (r0 K) - r0 K = x⁻¹ (-(x (r0 K) - r0 K)) := by
      rw [map_neg, map_sub, hxr]
      abel
    show x⁻¹ (r0 K) - r0 K ∈ Submodule.span K {p0 K}
    rw [hsplit]
    exact span_fix hinvp (neg_mem hxp')

theorem exists_adj_of_two_odd (s : Finset (Fin 6)) (hs : s.card = 3)
    (h2 : 2 ≤ (s.filter (fun i : Fin 6 => i.val % 2 = 1)).card) :
    ∃ a b c : Fin 6, a.val % 2 = 0 ∧ b.val % 2 = 1 ∧ c.val % 2 = 1 ∧
      (a.val + 1 = b.val ∨ b.val + 1 = a.val) ∧ b ∈ s ∧ c ∈ s ∧ b ≠ c ∧ a ∉ s := by
  revert s
  decide

theorem odd_not_mem_S024 (c : Fin 6) (hc : c.val % 2 = 1) : c ∉ S024.val := by
  show c ∉ ({0, 2, 4} : Finset (Fin 6))
  revert c
  decide

theorem coord_eq_zero_of_mem_W0 {v : Cube K}
    (hv : v ∈ Wsp (Submodule.span K {p0 K}) (U0 K)) (I : Set.powersetCard (Fin 6) 3)
    (hI : 2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card) : coord K v I = 0 := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hbI, hcI, hbc, haI⟩ :=
    exists_adj_of_two_odd I.val I.prop hI
  have hne : a ≠ b := fun h => by subst h; omega
  have hmem : rhoEquiv K (transvGL K a b hne 1) ∈ rootSet K := ⟨a, b, ⟨ha, hb⟩, 1, rfl⟩
  have hu : rhoEquiv K (transvGL K a b hne 1) ∈ U0 K := Subgroup.subset_closure hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (mem_Wsp.mp hv _ hu)
  obtain ⟨J, hJ⟩ : ∃ J, replSet I a b hbI haI = J := ⟨_, rfl⟩
  obtain ⟨haJ, hbJ⟩ := replSet_eq_imp hne hbI haI hJ
  have hIJ : I = replSet J b a haJ hbJ := (replSet_eq_iff hbI haI haJ hbJ).mp hJ
  have hcJ : c ∈ J.val := by
    rw [← hJ]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hbc.symm, hcI⟩)
  have hSJ : S024 ≠ J := by
    intro h
    have hcS : c ∈ S024.val := by rw [h]; exact hcJ
    exact odd_not_mem_S024 c hc hcS
  have hp0 : coord K (p0 K) J = 0 := by
    rw [p0, coord_cubeBasis, if_neg hSJ]
  have hJc : a ∈ J.val ∧ b ∉ J.val := ⟨haJ, hbJ⟩
  have key := coord_rho_transvGL hab hne 1 v J
  rw [dif_pos hJc, one_mul] at key
  have hW : coord K v (replSet J b a hJc.1 hJc.2) = coord K v I := by rw [hIJ]
  have ht' : rho K (transvGL K a b hne 1) v - v = t • p0 K := ht.symm
  have h1 : coord K (rho K (transvGL K a b hne 1) v - v) J = coord K (t • p0 K) J := by
    rw [ht']
  rw [coord_sub, coord_smul, hp0, mul_zero] at h1
  linear_combination h1 - key - hW

abbrev W0Idx : Type :=
  {s : Finset (Fin 6) // s.card = 3 ∧ (s.filter (fun i : Fin 6 => i.val % 2 = 1)).card ≤ 1}

theorem card_W0Idx : Nat.card W0Idx = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_W0_le [Finite K] :
    Nat.card (Wsp (Submodule.span K {p0 K}) (U0 K)) ≤ Nat.card K ^ 10 := by
  have hΦ : Function.Injective (fun (v : Wsp (Submodule.span K {p0 K}) (U0 K)) (s : W0Idx) =>
      coord K (v : Cube K) ⟨s.1, s.2.1⟩) := by
    intro v w hvw
    apply Subtype.ext
    rw [← sub_eq_zero]
    apply eq_zero_of_coord_eq_zero
    intro I
    rw [coord_sub]
    by_cases hI : (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card ≤ 1
    · exact sub_eq_zero.mpr (congrFun hvw ⟨I.val, I.prop, hI⟩)
    · have hI2 : 2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by omega
      rw [coord_eq_zero_of_mem_W0 v.2 I hI2, coord_eq_zero_of_mem_W0 w.2 I hI2, sub_zero]
  calc Nat.card (Wsp (Submodule.span K {p0 K}) (U0 K))
      ≤ Nat.card (W0Idx → K) := Nat.card_le_card_of_injective _ hΦ
    _ = Nat.card K ^ Nat.card W0Idx := Nat.card_fun
    _ = Nat.card K ^ 10 := by rw [card_W0Idx]

theorem S024_ne_S034 : S024 ≠ S034 := by
  intro h
  have h2 : (2 : Fin 6) ∈ S024.val := by simp [S024, tripleSet]
  rw [congrArg Subtype.val h] at h2
  simp [S034, tripleSet] at h2

theorem p0_ne_zero : p0 K ≠ 0 := by
  intro h
  have h1 : coord K (p0 K) S024 = 1 := by
    unfold p0
    rw [coord_cubeBasis, if_pos rfl]
  rw [h, coord_zero] at h1
  exact zero_ne_one h1

theorem p0_eq : p0 K = ιMulti K 3 ![e K 0, e K 2, e K 4] := by
  have hs : ∀ s : Fin 3, enum S024 s = ![(0 : Fin 6), 2, 4] s := fun s =>
    enum_tripleSet (by decide) (by decide) s
  unfold p0 cubeBasis
  rw [exteriorPower.basis_apply]
  unfold ιMulti_family
  congr 1
  funext s
  rw [Function.comp_apply, hs s]
  fin_cases s <;> simp [e]

theorem r0_eq : r0 K = ιMulti K 3 ![e K 0, e K 3, e K 4] := by
  have hs : ∀ s : Fin 3, enum S034 s = ![(0 : Fin 6), 3, 4] s := fun s =>
    enum_tripleSet (by decide) (by decide) s
  unfold r0 cubeBasis
  rw [exteriorPower.basis_apply]
  unfold ιMulti_family
  congr 1
  funext s
  rw [Function.comp_apply, hs s]
  fin_cases s <;> simp [e]

theorem r0_not_mem_span : r0 K ∉ Submodule.span K {p0 K} := by
  intro h
  rw [Submodule.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  have h1 : coord K (r0 K) S034 = 1 := by
    unfold r0
    rw [coord_cubeBasis, if_pos rfl]
  have h2 : coord K (p0 K) S034 = 0 := by
    unfold p0
    rw [coord_cubeBasis, if_neg S024_ne_S034]
  have h3 : coord K (r0 K) S034 = t * coord K (p0 K) S034 := by
    rw [← ht, coord_smul]
  rw [h1, h2, mul_zero] at h3
  exact one_ne_zero h3

theorem exists_gam_plane (a b : K) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ g ∈ Gam K, g (p0 K) = a • p0 K + b • r0 K := by
  have hv : LinearIndependent K ![e K 0, e K 2, e K 4] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 := congrFun hc 0
    have h2 := congrFun hc 2
    have h4 := congrFun hc 4
    simp [Fin.sum_univ_three, e, Pi.single_apply] at h0 h2 h4
    intro i
    fin_cases i <;> simp_all
  have hw : LinearIndependent K ![e K 0, a • e K 2 + b • e K 3, e K 4] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 := congrFun hc 0
    have h2 := congrFun hc 2
    have h3 := congrFun hc 3
    have h4 := congrFun hc 4
    simp [Fin.sum_univ_three, e, Pi.single_apply] at h0 h2 h3 h4
    have hc1 : c 1 = 0 := by
      rcases h with ha | hb
      · exact h2.resolve_right ha
      · exact h3.resolve_right hb
    intro i
    fin_cases i <;> simp_all
  obtain ⟨g, hdet, hgv⟩ := exists_sl_of_linearIndependent (by norm_num : 3 < 6) hv hw
  have hg0 : g.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  set G : GL (Fin 6) K := Matrix.GeneralLinearGroup.mkOfDetNeZero g hg0 with hG_def
  have hGval : (G : Matrix (Fin 6) (Fin 6) K) = g := rfl
  have hGdet : G ∈ {A : GL (Fin 6) K | (A : Matrix (Fin 6) (Fin 6) K).det = 1} := by
    show (G : Matrix (Fin 6) (Fin 6) K).det = 1
    rw [hGval]
    exact hdet
  have hGS : G ∈ StatedSL 6 K := Subgroup.subset_closure hGdet
  have key : rhoEquiv K G (p0 K) = ιMulti K 3 ![e K 0, a • e K 2 + b • e K 3, e K 4] := by
    rw [rhoEquiv_apply, p0_eq, rho_ιMulti, hGval]
    congr 1
    funext i
    exact hgv i
  refine ⟨rhoEquiv K G, Subgroup.mem_map_of_mem _ hGS, ?_⟩
  rw [key, p0_eq, r0_eq, ι3_add_snd, ι3_smul_snd, ι3_smul_snd]

theorem a5MinuscGeom [Finite K] : MinuscGeom (Gam K) (p0 K) (U0 K) 10 := by
  refine ⟨p0_ne_zero, U0_le_Gam, U0_fix, card_W0_le, ?_⟩
  obtain ⟨g₁, hg₁, hg₁r⟩ := exists_gam_plane (K := K) 0 1 (Or.inr one_ne_zero)
  have hr : g₁ (p0 K) = r0 K := by simpa using hg₁r
  refine ⟨g₁, hg₁, ?_, ?_, ?_⟩
  · rw [hr]
    exact r0_mem_W0
  · rw [hr]
    exact r0_not_mem_span
  · intro a b hab
    obtain ⟨g, hg, hgp⟩ := exists_gam_plane a b hab
    exact ⟨g, hg, by rw [hgp, hr]⟩

end CFSG.RankThree.GF2n.Smith81.A5Cube
