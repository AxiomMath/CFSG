module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Rank

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open CFSG.RankThree.GF2n.Smith81.EGeom Module

variable {K : Type} [Field K]

@[expose] def Special (K : Type) [Field K] (g : Cube K ≃ₗ[K] Cube K) : Prop :=
  beta K (p0 K) (g (p0 K)) = 0 ∧ g (p0 K) ∉ Wsp (Submodule.span K {p0 K}) (U0 K)

private theorem range_vec2 {α : Type*} (x y : α) : Set.range ![x, y] = {x, y} :=
  Matrix.range_cons_cons_empty x y _

private theorem range_vec3 {α : Type*} (x y z : α) : Set.range ![x, y, z] = {x, y, z} := by
  rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]

private theorem range_vec5 {α : Type*} (a b c d e : α) :
    Set.range ![a, b, c, d, e] = {a, b, c, d, e} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons_cons_empty,
    Set.singleton_union, Set.singleton_union, Set.singleton_union]

private theorem finrank_span_li {m : ℕ} {w : Fin m → (Fin 6 → K)} (hw : LinearIndependent K w) :
    finrank K ↥(Submodule.span K (Set.range w)) = m := by
  rw [finrank_span_eq_card hw, Fintype.card_fin]

private theorem li_of_comp {n m : ℕ} {v : Fin n → (Fin 6 → K)} (hv : LinearIndependent K v)
    {f : Fin m → Fin n} (hf : Function.Injective f) {w : Fin m → (Fin 6 → K)}
    (hw : ∀ i, w i = v (f i)) : LinearIndependent K w := by
  have h : w = v ∘ f := funext hw
  rw [h]
  exact hv.comp f hf

private theorem finrank_span_pair_le (a b : Fin 6 → K) :
    finrank K ↥(Submodule.span K {a, b}) ≤ 2 := by
  have h := finrank_range_le_card (R := K) ![a, b]
  rw [range_vec2, Fintype.card_fin] at h
  exact h

private theorem finrank_span_lt_of_mem {s t : Set (Fin 6 → K)} (hst : s ⊆ t) {x : Fin 6 → K}
    (hx : x ∈ t) (hxs : x ∉ Submodule.span K s) :
    finrank K ↥(Submodule.span K s) < finrank K ↥(Submodule.span K t) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (Submodule.span_mono hst) ?_
  intro h
  apply hxs
  rw [h]
  exact Submodule.subset_span hx

private theorem exists_mem_not_mem_of_finrank_lt {W U : Submodule K (Fin 6 → K)}
    (h : finrank K ↥W < finrank K ↥U) : ∃ u ∈ U, u ∉ W := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  have hle : U ≤ W := fun x hx => hc x hx
  have := Submodule.finrank_mono hle
  omega

private theorem two_le_finrank_inf {x y : Fin 6 → K} {X Y : Submodule K (Fin 6 → K)}
    (hx : x ∈ X) (hy : y ∈ X) (hx' : x ∈ Y) (hy' : y ∈ Y)
    (h2 : finrank K ↥(Submodule.span K {x, y}) = 2) :
    2 ≤ finrank K ↥(X ⊓ Y) := by
  have hle : Submodule.span K {x, y} ≤ X ⊓ Y := by
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨hx, hx'⟩
    · exact ⟨hy, hy'⟩
  have := Submodule.finrank_mono hle
  omega

private theorem exists_five_vectors {S T : Submodule K (Fin 6 → K)} (hS : finrank K S = 3)
    (hT : finrank K T = 3) (hST : finrank K ↥(S ⊓ T) = 1) :
    ∃ a b c d e : Fin 6 → K, LinearIndependent K ![a, b, c, d, e] ∧
      S = Submodule.span K {a, b, c} ∧ T = Submodule.span K {a, d, e} := by
  obtain ⟨a, haST, ha0⟩ : ∃ a ∈ S ⊓ T, a ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    rw [h, finrank_bot] at hST
    exact zero_ne_one hST
  have haS : a ∈ S := (Submodule.mem_inf.mp haST).1
  have haT : a ∈ T := (Submodule.mem_inf.mp haST).2
  have hfa : finrank K ↥(Submodule.span K {a}) = 1 := finrank_span_singleton ha0
  obtain ⟨b, hbS, hb⟩ := exists_mem_not_mem_of_finrank_lt
    (W := Submodule.span K {a}) (U := S) (by omega)
  obtain ⟨d, hdT, hd⟩ := exists_mem_not_mem_of_finrank_lt
    (W := Submodule.span K {a}) (U := T) (by omega)
  have hab : 1 < finrank K ↥(Submodule.span K {a, b}) := by
    have := finrank_span_lt_of_mem (s := {a}) (t := {a, b}) (by simp) (by simp) hb
    omega
  have had : 1 < finrank K ↥(Submodule.span K {a, d}) := by
    have := finrank_span_lt_of_mem (s := {a}) (t := {a, d}) (by simp) (by simp) hd
    omega
  obtain ⟨c, hcS, hc⟩ := exists_mem_not_mem_of_finrank_lt
    (W := Submodule.span K {a, b}) (U := S) (by have := finrank_span_pair_le (K := K) a b; omega)
  obtain ⟨e, heT, he⟩ := exists_mem_not_mem_of_finrank_lt
    (W := Submodule.span K {a, d}) (U := T) (by have := finrank_span_pair_le (K := K) a d; omega)
  have hleS : Submodule.span K {a, b, c} ≤ S := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [haS, hbS, hcS]
  have hleT : Submodule.span K {a, d, e} ≤ T := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [haT, hdT, heT]
  have habc : finrank K ↥(Submodule.span K {a, b, c}) = 3 := by
    have h1 := finrank_span_lt_of_mem (s := {a, b}) (t := {a, b, c}) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) (by simp) hc
    have h2 := Submodule.finrank_mono hleS
    omega
  have hade : finrank K ↥(Submodule.span K {a, d, e}) = 3 := by
    have h1 := finrank_span_lt_of_mem (s := {a, d}) (t := {a, d, e}) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) (by simp) he
    have h2 := Submodule.finrank_mono hleT
    omega
  have hSeq : S = Submodule.span K {a, b, c} :=
    (Submodule.eq_of_le_of_finrank_eq hleS (habc.trans hS.symm)).symm
  have hTeq : T = Submodule.span K {a, d, e} :=
    (Submodule.eq_of_le_of_finrank_eq hleT (hade.trans hT.symm)).symm
  have hsup : Submodule.span K {a, b, c} ⊔ Submodule.span K {a, d, e} =
      Submodule.span K {a, b, c, d, e} := by
    rw [← Submodule.span_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hinf : finrank K ↥(Submodule.span K {a, b, c} ⊓ Submodule.span K {a, d, e}) = 1 := by
    rw [← hSeq, ← hTeq]
    exact hST
  have hfin5 : finrank K ↥(Submodule.span K {a, b, c} ⊔ Submodule.span K {a, d, e}) = 5 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {a, b, c})
      (Submodule.span K {a, d, e})
    rw [habc, hade, hinf] at h
    omega
  have hli : LinearIndependent K ![a, b, c, d, e] := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, range_vec5, Set.finrank,
      ← hsup, hfin5]
  exact ⟨a, b, c, d, e, hli, hSeq, hTeq⟩

private theorem exists_two_planes {S T : Submodule K (Fin 6 → K)} (hS : finrank K S = 3)
    (hT : finrank K T = 3) (hST : finrank K ↥(S ⊓ T) = 1) :
    ∃ W₁ W₂ : Submodule K (Fin 6 → K), finrank K W₁ = 3 ∧ finrank K W₂ = 3 ∧
      2 ≤ finrank K ↥(W₁ ⊓ S) ∧ 2 ≤ finrank K ↥(W₂ ⊓ S) ∧
      2 ≤ finrank K ↥(W₁ ⊓ T) ∧ 2 ≤ finrank K ↥(W₂ ⊓ T) ∧ finrank K ↥(W₁ ⊓ W₂) = 1 := by
  obtain ⟨a, b, c, d, e, hli, hSabc, hTade⟩ := exists_five_vectors hS hT hST
  subst hSabc hTade
  have h3abd : LinearIndependent K ![a, b, d] :=
    li_of_comp hli (f := (![0, 1, 3] : Fin 3 → Fin 5)) (by decide)
      (fun i => by fin_cases i <;> rfl)
  have h3ace : LinearIndependent K ![a, c, e] :=
    li_of_comp hli (f := (![0, 2, 4] : Fin 3 → Fin 5)) (by decide)
      (fun i => by fin_cases i <;> rfl)
  have h2ab : LinearIndependent K ![a, b] :=
    li_of_comp hli (f := (![0, 1] : Fin 2 → Fin 5)) (by decide)
      (fun i => by fin_cases i <;> rfl)
  have h2ac : LinearIndependent K ![a, c] :=
    li_of_comp hli (f := (![0, 2] : Fin 2 → Fin 5)) (by decide)
      (fun i => by fin_cases i <;> rfl)
  have h2ad : LinearIndependent K ![a, d] :=
    li_of_comp hli (f := (![0, 3] : Fin 2 → Fin 5)) (by decide)
      (fun i => by fin_cases i <;> rfl)
  have h2ae : LinearIndependent K ![a, e] :=
    li_of_comp hli (f := (![0, 4] : Fin 2 → Fin 5)) (by decide)
      (fun i => by fin_cases i <;> rfl)
  have hfabd : finrank K ↥(Submodule.span K {a, b, d}) = 3 := by
    have h := finrank_span_li h3abd
    rw [range_vec3] at h
    exact h
  have hface : finrank K ↥(Submodule.span K {a, c, e}) = 3 := by
    have h := finrank_span_li h3ace
    rw [range_vec3] at h
    exact h
  have hfab : finrank K ↥(Submodule.span K {a, b}) = 2 := by
    have h := finrank_span_li h2ab
    rw [range_vec2] at h
    exact h
  have hfac : finrank K ↥(Submodule.span K {a, c}) = 2 := by
    have h := finrank_span_li h2ac
    rw [range_vec2] at h
    exact h
  have hfad : finrank K ↥(Submodule.span K {a, d}) = 2 := by
    have h := finrank_span_li h2ad
    rw [range_vec2] at h
    exact h
  have hfae : finrank K ↥(Submodule.span K {a, e}) = 2 := by
    have h := finrank_span_li h2ae
    rw [range_vec2] at h
    exact h
  have hfive : finrank K ↥(Submodule.span K {a, b, c, d, e}) = 5 := by
    have h := finrank_span_li hli
    rw [range_vec5] at h
    exact h
  refine ⟨Submodule.span K {a, b, d}, Submodule.span K {a, c, e}, hfabd, hface, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact two_le_finrank_inf (x := a) (y := b) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) hfab
  · exact two_le_finrank_inf (x := a) (y := c) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) hfac
  · exact two_le_finrank_inf (x := a) (y := d) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) hfad
  · exact two_le_finrank_inf (x := a) (y := e) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp)) hfae
  · have hsup : Submodule.span K {a, b, d} ⊔ Submodule.span K {a, c, e} =
        Submodule.span K {a, b, c, d, e} := by
      rw [← Submodule.span_union]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {a, b, d})
      (Submodule.span K {a, c, e})
    rw [hsup, hfive, hfabd, hface] at h
    omega

private theorem exists_S0_basis : ∃ v : Fin 3 → Fin 6 → K, LinearIndependent K v ∧
    S0 K = Submodule.span K (Set.range v) := by
  have hf : Function.Injective (![(0 : Fin 6), 2, 4]) := by decide
  have hv : LinearIndependent K
      (fun i : Fin 3 => (Pi.single (![(0 : Fin 6), 2, 4] i) (1 : K) : Fin 6 → K)) :=
    (Pi.linearIndependent_single_one (Fin 6) K).comp _ hf
  refine ⟨fun i : Fin 3 => (Pi.single (![(0 : Fin 6), 2, 4] i) (1 : K) : Fin 6 → K), hv, ?_⟩
  have hle : Submodule.span K
      (Set.range fun i : Fin 3 => (Pi.single (![(0 : Fin 6), 2, 4] i) (1 : K) : Fin 6 → K))
      ≤ S0 K := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact s81A12_single_mem_S0 (by fin_cases i <;> decide) 1
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_li hv, finrank_S0])).symm

private theorem exists_imgS0_eq {W : Submodule K (Fin 6 → K)} (hW : finrank K W = 3) :
    ∃ H : GL (Fin 6) K, (H : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ imgS0 H = W := by
  obtain ⟨v, hv, hS0v⟩ := exists_S0_basis (K := K)
  let bW := Module.finBasisOfFinrankEq K W hW
  have hw : LinearIndependent K (fun i => (bW i : Fin 6 → K)) :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hwspan : Submodule.span K (Set.range (fun i => (bW i : Fin 6 → K))) = W := by
    have h1 : Submodule.map W.subtype (Submodule.span K (Set.range bW)) = W := by
      rw [bW.span_eq, Submodule.map_subtype_top]
    rw [Submodule.map_span] at h1
    refine Eq.trans ?_ h1
    congr 1
    rw [← Set.range_comp]
    rfl
  obtain ⟨g, hdet, hgv⟩ := exists_sl_of_linearIndependent (by norm_num : 3 < 6) hv hw
  have hg0 : g.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg0, hdet, ?_⟩
  have hGval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero g hg0 : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = g := rfl
  unfold imgS0
  rw [hGval, hS0v, Submodule.map_span]
  refine Eq.trans ?_ hwspan
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext i
  rw [Function.comp_apply, Matrix.mulVecLin_apply]
  exact hgv i

private theorem imgS0_mul' (H G : GL (Fin 6) K) :
    imgS0 (H * G) = (imgS0 G).map (Matrix.mulVecLin (H : Matrix (Fin 6) (Fin 6) K)) := by
  unfold imgS0
  rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

private theorem finrank_map_inf_conj (G : GL (Fin 6) K) (X : Submodule K (Fin 6 → K)) :
    finrank K ↥(X.map (Matrix.mulVecLin ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ⊓ S0 K) =
      finrank K ↥(X ⊓ imgS0 G) := by
  have hinj : Function.Injective (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)) := by
    rw [Matrix.coe_mulVecLin]
    exact Matrix.mulVec_injective_iff_isUnit.2 G.isUnit
  have hcomp : (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)).comp
      (Matrix.mulVecLin ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one]
  have key : ((X.map (Matrix.mulVecLin ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ⊓
      S0 K).map (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K))) = X ⊓ imgS0 G := by
    rw [Submodule.map_inf _ hinj, ← Submodule.map_comp, hcomp, Submodule.map_id, imgS0]
  rw [(Submodule.equivMapOfInjective (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)) hinj
    (X.map (Matrix.mulVecLin ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ⊓ S0 K)).finrank_eq,
    key]

theorem special_rhoEquiv_iff {G : GL (Fin 6) K} (hG : (G : Matrix (Fin 6) (Fin 6) K).det = 1) :
    Special K (rhoEquiv K G) ↔ finrank K ↥(imgS0 G ⊓ S0 K) = 1 := by
  unfold Special
  rw [rhoEquiv_apply, beta_rho_p0_eq_zero_iff hG, rho_p0_mem_W0_iff hG]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem a5_special_common_collinear {g : Cube K ≃ₗ[K] Cube K} (hg : g ∈ Gam K)
    (hs : Special K g) :
    ∃ h₁ ∈ Gam K, ∃ h₂ ∈ Gam K,
      h₁ (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ∧
      h₂ (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ∧
      g⁻¹ (h₁ (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ∧
      g⁻¹ (h₂ (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ∧
      Special K (h₁⁻¹ * h₂) := by
  obtain ⟨G, hGS, rfl⟩ := Subgroup.mem_map.mp hg
  have hdetG : (G : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp hGS
  have hk : finrank K ↥(imgS0 G ⊓ S0 K) = 1 := (special_rhoEquiv_iff hdetG).mp hs
  obtain ⟨W₁, W₂, hW₁, hW₂, hW₁S, hW₂S, hW₁T, hW₂T, hW₁₂⟩ :=
    exists_two_planes (S := S0 K) (T := imgS0 G) (finrank_S0 (K := K)) (finrank_imgS0 G)
      (by rw [inf_comm]; exact hk)
  obtain ⟨H₁, hdet₁, hH₁⟩ := exists_imgS0_eq hW₁
  obtain ⟨H₂, hdet₂, hH₂⟩ := exists_imgS0_eq hW₂
  have hmem₁ : rhoEquiv K H₁ ∈ Gam K :=
    Subgroup.mem_map_of_mem _ (CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hdet₁)
  have hmem₂ : rhoEquiv K H₂ ∈ Gam K :=
    Subgroup.mem_map_of_mem _ (CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hdet₂)
  have hGinv : G⁻¹ ∈ CFSG.Open.StatedSL 6 K := Subgroup.inv_mem _ hGS
  have hdetGH₁ : ((G⁻¹ * H₁ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp
      (Subgroup.mul_mem _ hGinv (CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hdet₁))
  have hdetGH₂ : ((G⁻¹ * H₂ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp
      (Subgroup.mul_mem _ hGinv (CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hdet₂))
  have hdet12 : ((H₁⁻¹ * H₂ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hdet₁))
        (CFSG.Open.StatedAPI.mem_statedSL_iff.mpr hdet₂))
  have hA₁ : rhoEquiv K H₁ (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
    rw [rhoEquiv_apply, rho_p0_mem_W0_iff hdet₁, hH₁]
    exact hW₁S
  have hA₂ : rhoEquiv K H₂ (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
    rw [rhoEquiv_apply, rho_p0_mem_W0_iff hdet₂, hH₂]
    exact hW₂S
  have hB₁ : (rhoEquiv K G)⁻¹ (rhoEquiv K H₁ (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
    have hkey : (rhoEquiv K G)⁻¹ (rhoEquiv K H₁ (p0 K)) = rhoEquiv K (G⁻¹ * H₁) (p0 K) := by
      rw [map_mul, map_inv, LinearEquiv.mul_apply]
    rw [hkey, rhoEquiv_apply, rho_p0_mem_W0_iff hdetGH₁, imgS0_mul', hH₁,
      finrank_map_inf_conj G W₁]
    exact hW₁T
  have hB₂ : (rhoEquiv K G)⁻¹ (rhoEquiv K H₂ (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
    have hkey : (rhoEquiv K G)⁻¹ (rhoEquiv K H₂ (p0 K)) = rhoEquiv K (G⁻¹ * H₂) (p0 K) := by
      rw [map_mul, map_inv, LinearEquiv.mul_apply]
    rw [hkey, rhoEquiv_apply, rho_p0_mem_W0_iff hdetGH₂, imgS0_mul', hH₂,
      finrank_map_inf_conj G W₂]
    exact hW₂T
  have hD : Special K ((rhoEquiv K H₁)⁻¹ * rhoEquiv K H₂) := by
    have hkey : (rhoEquiv K H₁)⁻¹ * rhoEquiv K H₂ = rhoEquiv K (H₁⁻¹ * H₂) := by
      rw [map_mul, map_inv]
    rw [hkey, special_rhoEquiv_iff hdet12, imgS0_mul', hH₂, finrank_map_inf_conj H₁ W₂, hH₁,
      inf_comm]
    exact hW₁₂
  exact ⟨rhoEquiv K H₁, hmem₁, rhoEquiv K H₂, hmem₂, hA₁, hA₂, hB₁, hB₂, hD⟩

private theorem a5_conj_transvec_aux {A B N : Matrix (Fin 6) (Fin 6) K} (hBA : B * A = 1)
    (hdA : IsUnit A.det) (hdB : IsUnit B.det) (hN2 : N * N = 0)
    (hr : Matrix.rank N = 1) : (A * N * B) * (A * N * B) = 0 ∧ Matrix.rank (A * N * B) = 1 := by
  refine ⟨?_, ?_⟩
  · have e : (A * N * B) * (A * N * B) = A * (N * (B * A) * N) * B := by
      simp only [Matrix.mul_assoc]
    rw [e, hBA, Matrix.mul_one, hN2, Matrix.mul_zero, Matrix.zero_mul]
  · rw [Matrix.rank_mul_eq_left_of_isUnit_det B (A * N) hdB,
      Matrix.rank_mul_eq_right_of_isUnit_det A N hdA, hr]

theorem IsTransvec.conj' {τ : GL (Fin 6) K} (h : IsTransvec K τ) (G : GL (Fin 6) K) :
    IsTransvec K (G * τ * G⁻¹) := by
  unfold IsTransvec at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hval : ((G * τ * G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) - 1 =
      (G : Matrix (Fin 6) (Fin 6) K) * ((τ : Matrix (Fin 6) (Fin 6) K) - 1) *
        ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Units.mul_inv]
  rw [hval]
  exact a5_conj_transvec_aux (Units.inv_mul G)
    (Matrix.isUnit_det_of_right_inverse (Units.mul_inv G))
    (Matrix.isUnit_det_of_right_inverse (Units.inv_mul G)) h1 h2

private theorem a5_isTransvec_of_inter {S S' : Submodule K (Fin 6 → K)} {τ : GL (Fin 6) K}
    (hτ : τ ∈ UnipGL K S ⊓ UnipGL K S') (hL : Module.finrank K ↥(S ⊓ S') = 1) (hne : τ ≠ 1) :
    IsTransvec K τ := by
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 6) (Fin 6) K, N = (τ : Matrix (Fin 6) (Fin 6) K) - 1 :=
    ⟨_, rfl⟩
  have hNv : ∀ v : Fin 6 → K, N.mulVec v = (τ : Matrix (Fin 6) (Fin 6) K).mulVec v - v := by
    intro v
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hmem : ∀ v : Fin 6 → K, N.mulVec v ∈ S ⊓ S' := by
    intro v
    rw [hNv]
    exact inf_UnipGL_sub_mem hτ v
  have hfix : ∀ v : Fin 6 → K,
      (τ : Matrix (Fin 6) (Fin 6) K).mulVec (N.mulVec v) = N.mulVec v := by
    intro v
    exact inf_UnipGL_fix_sup hτ ((inf_le_left.trans le_sup_left : S ⊓ S' ≤ S ⊔ S') (hmem v))
  have hNN : N * N = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hNv (N.mulVec v), hfix v, sub_self]
  have hN0 : N ≠ 0 := by
    intro h0
    apply hne
    apply Units.ext
    rw [Units.val_one]
    rw [hN, sub_eq_zero] at h0
    exact h0
  have hex : ∃ v : Fin 6 → K, N.mulVec v ≠ 0 := by
    by_contra hcon
    apply hN0
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.zero_mulVec]
    by_contra hv
    exact hcon ⟨v, hv⟩
  have hrank_pos : 0 < Matrix.rank N := by
    obtain ⟨v, hv⟩ := hex
    unfold Matrix.rank
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨N.mulVec v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hrank_le : Matrix.rank N ≤ 1 := by
    have hle : LinearMap.range N.mulVecLin ≤ S ⊓ S' := by
      rintro _ ⟨v, rfl⟩
      exact hmem v
    have h := Submodule.finrank_mono hle
    rw [hL] at h
    exact h
  unfold IsTransvec
  rw [← hN]
  exact ⟨hNN, by omega⟩

theorem a5_inter_special_transvec {g : Cube K ≃ₗ[K] Cube K} (hg : g ∈ Gam K)
    (hs : Special K g) {u : Cube K ≃ₗ[K] Cube K} (hu : u ∈ U0 K ⊓ conjSub g (U0 K))
    (hu1 : u ≠ 1) :
    ∃ τ : GL (Fin 6) K, IsTransvec K τ ∧ u = rhoEquiv K τ := by
  obtain ⟨G, hG, rfl⟩ := Subgroup.mem_map.mp hg
  have hdet : (G : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp hG
  have hd : Module.finrank K ↥(imgS0 G ⊓ S0 K) = 1 := (special_rhoEquiv_iff hdet).mp hs
  have hconj : conjSub (rhoEquiv K G) (U0 K) = Urad K (imgS0 G) := by
    rw [U0_eq_Urad]
    exact conjSub_Urad G (S0 K)
  obtain ⟨hu0, hu0'⟩ := Subgroup.mem_inf.mp hu
  rw [hconj] at hu0'
  rw [U0_eq_Urad] at hu0
  obtain ⟨τ, hτ, rfl⟩ := mem_Urad_iff.mp hu0
  obtain ⟨τ', hτ', hτeq⟩ := mem_Urad_iff.mp hu0'
  have hrho : rho K τ = rho K τ' := by
    apply LinearMap.ext
    intro ξ
    show rhoEquiv K τ ξ = rhoEquiv K τ' ξ
    rw [hτeq]
  have hS0 : S0 K ≠ ⊥ := by
    intro h
    have h3 := finrank_S0 (K := K)
    rw [h, finrank_bot] at h3
    omega
  have hττ' : τ = τ' := rho_eq_of_unip hS0 hτ hτ' hrho
  have hτ2 : τ ∈ UnipGL K (imgS0 G) := by
    rw [hττ']
    exact hτ'
  have hL : Module.finrank K ↥(S0 K ⊓ imgS0 G) = 1 := by
    rw [inf_comm]
    exact hd
  have hne : τ ≠ 1 := by
    rintro rfl
    exact hu1 (map_one (rhoEquiv K))
  exact ⟨τ, a5_isTransvec_of_inter (Subgroup.mem_inf.mpr ⟨hτ, hτ2⟩) hL hne, rfl⟩

theorem a5_inter_special_transvec' {g₁ g₂ : Cube K ≃ₗ[K] Cube K} (hg₁ : g₁ ∈ Gam K)
    (hg₂ : g₂ ∈ Gam K) (hs : Special K (g₁⁻¹ * g₂)) {u : Cube K ≃ₗ[K] Cube K}
    (hu : u ∈ conjSub g₁ (U0 K) ⊓ conjSub g₂ (U0 K)) (hu1 : u ≠ 1) :
    ∃ τ : GL (Fin 6) K, IsTransvec K τ ∧ u = rhoEquiv K τ := by
  obtain ⟨G₁, -, hG₁eq⟩ := Subgroup.mem_map.mp hg₁
  obtain ⟨hu₁, hu₂⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨u₀, hu₀U, hu₀eq⟩ := mem_conjSub.mp hu₁
  obtain ⟨u₂, hu₂U, hu₂eq⟩ := mem_conjSub.mp hu₂
  have key : g₁⁻¹ * g₂ * u₂ * (g₁⁻¹ * g₂)⁻¹ = u₀ := by
    calc g₁⁻¹ * g₂ * u₂ * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * (g₂ * u₂ * g₂⁻¹) * g₁ := by group
      _ = g₁⁻¹ * u * g₁ := by rw [hu₂eq]
      _ = u₀ := by rw [← hu₀eq]; group
  have hu₀1 : u₀ ≠ 1 := by
    rintro rfl
    apply hu1
    rw [← hu₀eq, mul_one, mul_inv_cancel]
  have hgmem : g₁⁻¹ * g₂ ∈ Gam K := Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₁) hg₂
  obtain ⟨τ, hτ, hτeq⟩ := a5_inter_special_transvec hgmem hs
    (Subgroup.mem_inf.mpr ⟨hu₀U, mem_conjSub.mpr ⟨u₂, hu₂U, key⟩⟩) hu₀1
  refine ⟨G₁ * τ * G₁⁻¹, IsTransvec.conj' hτ G₁, ?_⟩
  rw [← hu₀eq, hτeq, ← hG₁eq, map_mul, map_mul, map_inv]

private theorem s81j_mem_W0_iff {s : Cube K ≃ₗ[K] Cube K} (hs : s ∈ Gam K) {c : K} (hc : c ≠ 0)
    (hsp : s (p0 K) = c • p0 K) (x : Cube K) :
    s x ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔ x ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  have hU : conjSub s (U0 K) = U0 K := U0_norm (K := K) s hs ⟨c, hc, hsp⟩
  have hL : (Submodule.span K {p0 K}).map (s : Cube K →ₗ[K] Cube K) =
      Submodule.span K {p0 K} := by
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hsp]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _
  have hW := Wsp_map s (Submodule.span K {p0 K}) (U0 K)
  rw [hL, hU] at hW
  have h2 : s x ∈ (Wsp (Submodule.span K {p0 K}) (U0 K)).map (s : Cube K →ₗ[K] Cube K) ↔
      x ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rw [← hW] at h2
  exact h2

private theorem s81j_beta_inv {s : Cube K ≃ₗ[K] Cube K} (hs : s ∈ Gam K) {c : K}
    (hsp : s (p0 K) = c • p0 K) (x : Cube K) :
    beta K (p0 K) (s⁻¹ x) = c * beta K (p0 K) x := by
  have hx : s (s⁻¹ x) = x := by
    rw [LinearEquiv.coe_inv]
    exact s.apply_symm_apply x
  have h := Gam_beta_inv (K := K) hs (p0 K) (s⁻¹ x)
  rw [hsp, hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact h.symm

private theorem s81j_special_iff {s₁ s₂ Q : Cube K ≃ₗ[K] Cube K} (h₁ : s₁ ∈ Gam K)
    (h₂ : s₂ ∈ Gam K) {c₁ c₂ : K} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (e₁ : s₁ (p0 K) = c₁ • p0 K) (e₂ : s₂ (p0 K) = c₂ • p0 K) :
    Special K (s₁⁻¹ * Q * s₂) ↔ Special K Q := by
  have hP : (s₁⁻¹ * Q * s₂) (p0 K) = c₂ • s₁⁻¹ (Q (p0 K)) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e₂, map_smul, map_smul]
  have hβP : beta K (p0 K) (c₂ • s₁⁻¹ (Q (p0 K))) =
      c₂ * (c₁ * beta K (p0 K) (Q (p0 K))) := by
    rw [map_smul, smul_eq_mul, s81j_beta_inv h₁ e₁]
  have hWP : c₂ • s₁⁻¹ (Q (p0 K)) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔
      Q (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
    refine (Submodule.smul_mem_iff _ hc₂).trans ?_
    have h := s81j_mem_W0_iff (K := K) h₁ hc₁ e₁ (s₁⁻¹ (Q (p0 K)))
    have hx : s₁ (s₁⁻¹ (Q (p0 K))) = Q (p0 K) := by
      rw [LinearEquiv.coe_inv]
      exact s₁.apply_symm_apply _
    rw [hx] at h
    exact h.symm
  have hz : c₂ * (c₁ * beta K (p0 K) (Q (p0 K))) = 0 ↔
      beta K (p0 K) (Q (p0 K)) = 0 := by
    rw [mul_eq_zero, mul_eq_zero]
    constructor
    · rintro (h | h | h)
      · exact absurd h hc₂
      · exact absurd h hc₁
      · exact h
    · intro h
      exact Or.inr (Or.inr h)
  unfold Special
  rw [hP, hβP, hWP, hz]

theorem special_rel_point [Finite K] {g₁ g₂ g₁' g₂' : Cube K ≃ₗ[K] Cube K} (h₁ : g₁ ∈ Gam K)
    (h₂ : g₂ ∈ Gam K) (h₁' : g₁' ∈ Gam K) (h₂' : g₂' ∈ Gam K) {c₁ c₂ : K} (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (e₁ : g₁' (p0 K) = c₁ • g₁ (p0 K)) (e₂ : g₂' (p0 K) = c₂ • g₂ (p0 K)) :
    Special K (g₁'⁻¹ * g₂') ↔ Special K (g₁⁻¹ * g₂) := by
  have hs₁ : g₁⁻¹ * g₁' ∈ Gam K := (Gam K).mul_mem ((Gam K).inv_mem h₁) h₁'
  have hs₂ : g₂⁻¹ * g₂' ∈ Gam K := (Gam K).mul_mem ((Gam K).inv_mem h₂) h₂'
  have hs₁p : (g₁⁻¹ * g₁') (p0 K) = c₁ • p0 K := by
    rw [LinearEquiv.mul_apply, e₁, map_smul, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have hs₂p : (g₂⁻¹ * g₂') (p0 K) = c₂ • p0 K := by
    rw [LinearEquiv.mul_apply, e₂, map_smul, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have hid : g₁'⁻¹ * g₂' = (g₁⁻¹ * g₁')⁻¹ * (g₁⁻¹ * g₂) * (g₂⁻¹ * g₂') := by group
  rw [hid]
  exact s81j_special_iff hs₁ hs₂ hc₁ hc₂ hs₁p hs₂p

end CFSG.RankThree.GF2n.Smith81.A5Cube
