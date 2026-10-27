module

public import CFSG.Quasithin.EmptyFaithful.R3c12Cfg
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction

public section

namespace CFSG.Quasithin.R3c12

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine

section U33

variable {F : Type} [Field F]

theorem eig_eq_one (hF : Nat.card F = 9) {E : Matrix (Fin 3) (Fin 3) F} (hE : E ^ 3 = 1)
    {v : Fin 3 → F} (hv : v ≠ 0) {c : F} (hc : E *ᵥ v = c • v) : c = 1 := by
  have hE3 : E * E * E = 1 := by
    rw [← sq, ← pow_succ]
    exact hE
  have h3 : c ^ 3 • v = v := by
    have h1 : E *ᵥ (E *ᵥ (E *ᵥ v)) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hE3, Matrix.one_mulVec]
    simp only [hc, Matrix.mulVec_smul, smul_smul] at h1
    have : c * c * c = c ^ 3 := by ring
    rwa [this] at h1
  have h0 : (c ^ 3 - 1) • v = 0 := by rw [sub_smul, h3, one_smul, sub_self]
  have hc3 : c ^ 3 = 1 := by
    have := (smul_eq_zero.mp h0).resolve_right hv
    exact sub_eq_zero.mp this
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hF]
  have h9 := FiniteField.pow_card c
  rw [hcard] at h9
  calc c = c ^ 9 := h9.symm
    _ = (c ^ 3) ^ 3 := by rw [← pow_mul]
    _ = 1 := by rw [hc3, one_pow]

theorem eq_one_of_fixes_three {E : Matrix (Fin 3) (Fin 3) F} {v w u : Fin 3 → F}
    (hind : LinearIndependent F ![v, w, u]) (hv : E *ᵥ v = v) (hw : E *ᵥ w = w)
    (hu : E *ᵥ u = u) : E = 1 := by
  have hspan : Submodule.span F (Set.range ![v, w, u]) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank (by simp)
  have hfun : Matrix.toLin' E = LinearMap.id := by
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa [Matrix.toLin'_apply] using hv
    · simpa [Matrix.toLin'_apply] using hw
    · simpa [Matrix.toLin'_apply] using hu
  have : Matrix.toLin' E = Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [hfun, Matrix.toLin'_one]
  exact Matrix.toLin'.injective this

theorem linearIndependent_of_orth (h : UnitaryFieldData 3 1 F) {v w u : Fin 3 → F}
    (hvv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0)
    (hww : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w w ≠ 0)
    (huu : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u u ≠ 0)
    (hvw : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v w = 0)
    (hvu : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v u = 0)
    (hwu : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w u = 0) :
    LinearIndependent F ![v, w, u] := by
  have hwv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w v = 0 := by
    rw [← bar_gramForm h v w, hvw, map_zero]
  have huv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u v = 0 := by
    rw [← bar_gramForm h v u, hvu, map_zero]
  have huw : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u w = 0 := by
    rw [← bar_gramForm h w u, hwu, map_zero]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • v + g 1 • w + g 2 • u = 0 := by
    simpa [Fin.sum_univ_three] using hg
  have e0 := congrArg (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v) hg'
  have e1 := congrArg (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) w) hg'
  have e2 := congrArg (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u) hg'
  simp only [map_add, map_smul, smul_eq_mul, map_zero] at e0 e1 e2
  rw [hvw, hvu, mul_zero, mul_zero, add_zero, add_zero] at e0
  rw [hwv, hwu, mul_zero, mul_zero, zero_add, add_zero] at e1
  rw [huv, huw, mul_zero, mul_zero, zero_add, zero_add] at e2
  intro i
  fin_cases i
  · exact (mul_eq_zero.mp e0).resolve_right hvv
  · exact (mul_eq_zero.mp e1).resolve_right hww
  · exact (mul_eq_zero.mp e2).resolve_right huu

theorem u33_no_three_cent (hF : Nat.card F = 9) {e a b : StatedSU 3 3 F} (he3 : e ^ 3 = 1)
    (he1 : e ≠ 1) (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b)
    (hcomm : a * b = b * a) (hea : e * a = a * e) (heb : e * b = b * e) : False := by
  have h := unitaryFieldData_of_card hF
  obtain ⟨L, hL⟩ := tauLine_surjective (h := h) (hF := hF) ⟨a, ha⟩
  obtain ⟨M, hM⟩ := tauLine_surjective (h := h) (hF := hF) ⟨b, hb⟩
  have hLa : (tauLine h hF L : StatedSU 3 3 F) = a := congrArg Subtype.val hL
  have hMb : (tauLine h hF M : StatedSU 3 3 F) = b := congrArg Subtype.val hM
  have hLM : L ≠ M := fun hh => hab (by rw [← hLa, ← hMb, hh])
  have horth := (tauLine_commute_iff (h := h) (hF := hF) hLM).mp (by rw [hLa, hMb]; exact hcomm)
  obtain ⟨T, hT, hmul⟩ := exists_tauLine_mul_eq (h := h) (hF := hF) hLM horth
  have hfixL : lineAct hF e L = L := by
    rw [lineAct_eq_self_iff (h := h) (hF := hF), Subgroup.mem_centralizer_singleton_iff, hLa]
    exact hea
  have hfixM : lineAct hF e M = M := by
    rw [lineAct_eq_self_iff (h := h) (hF := hF), Subgroup.mem_centralizer_singleton_iff, hMb]
    exact heb
  have hfixT : lineAct hF e T = T := by
    rw [lineAct_eq_self_iff (h := h) (hF := hF), Subgroup.mem_centralizer_singleton_iff, ← hmul,
      hLa, hMb]
    calc e * (a * b) = (e * a) * b := (mul_assoc e a b).symm
      _ = (a * e) * b := by rw [hea]
      _ = a * (e * b) := mul_assoc a e b
      _ = a * (b * e) := by rw [heb]
      _ = (a * b) * e := (mul_assoc a b e).symm
  set E : Matrix (Fin 3) (Fin 3) F := ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hE
  have hE3 : E ^ 3 = 1 := by
    have := congrArg (fun g : StatedSU 3 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) he3
    simpa using this
  have hfix : ∀ N : NonisoLine F, lineAct hF e N = N → E *ᵥ N.gen = N.gen := by
    intro N hN
    have hline : lineOf (h := h) N.gen (N.gramForm_gen (h := h)) = N :=
      Subtype.ext N.eq_span_gen.symm
    obtain ⟨c, hc⟩ := exists_mulVec_eq_smul (h := h) (hF := hF) e (N.gramForm_gen (h := h))
      (by rw [hline, hN])
    have := eig_eq_one hF hE3 N.gen_ne_zero hc
    rw [hc, this, one_smul]
  have hv := hfix L hfixL
  have hw := hfix M hfixM
  have hu := hfix T hfixT
  have hTmem : ∀ x ∈ L.1 ⊔ M.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x T.gen = 0 := by
    have : T.gen ∈ (T.1 : Set (Fin 3 → F)) := T.gen_mem
    rw [hT] at this
    exact this
  have hvw : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen M.gen = 0 :=
    horth _ L.gen_mem _ M.gen_mem
  have hvu : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen T.gen = 0 :=
    hTmem _ (Submodule.mem_sup_left L.gen_mem)
  have hwu : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) M.gen T.gen = 0 :=
    hTmem _ (Submodule.mem_sup_right M.gen_mem)
  have hind := linearIndependent_of_orth h (L.gramForm_gen (h := h)) (M.gramForm_gen (h := h))
    (T.gramForm_gen (h := h)) hvw hvu hwu
  have hE1 : E = 1 := eq_one_of_fixes_three hind hv hw hu
  exact he1 (Subtype.ext (Units.ext hE1))

theorem not_clConfig_statedSU (hF : Nat.card F = 9) : ¬ ClConfig (StatedSU 3 3 F) := by
  rintro ⟨T, V, e, -, -, hV4, hV2, -, he1, he3, hec⟩
  obtain ⟨a, ha⟩ : ∃ a : ↥V, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card V = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => (hcon x).trans (hcon y).symm⟩, ⟨1⟩⟩
    omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : ↥V, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set ↥V) ⊆ {1, a} := by
      intro x _
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr (hcon x hx)
    have hle : (Set.univ : Set ↥V).ncard ≤ ({1, a} : Set ↥V).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, a} : Set ↥V).ncard ≤ 2 :=
      (Set.ncard_insert_le 1 {a}).trans (by rw [Set.ncard_singleton])
    have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
    rw [Set.ncard_univ, hV4] at hle
    omega
  have hasq : (a : StatedSU 3 3 F) * a = 1 := hV2 a a.2
  have hbsq : (b : StatedSU 3 3 F) * b = 1 := hV2 b b.2
  have hainv : (a : StatedSU 3 3 F)⁻¹ = a := inv_eq_of_mul_eq_one_right hasq
  have hbinv : (b : StatedSU 3 3 F)⁻¹ = b := inv_eq_of_mul_eq_one_right hbsq
  have hab : (a : StatedSU 3 3 F) * b = b * a := by
    have hmem : (a : StatedSU 3 3 F) * b ∈ V := V.mul_mem a.2 b.2
    have habinv : ((a : StatedSU 3 3 F) * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (hV2 _ hmem)
    calc (a : StatedSU 3 3 F) * b = ((a : StatedSU 3 3 F) * b)⁻¹ := habinv.symm
      _ = (b : StatedSU 3 3 F)⁻¹ * (a : StatedSU 3 3 F)⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [hainv, hbinv]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haord : orderOf (a : StatedSU 3 3 F) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hasq) (fun h1 => ha (Subtype.ext h1))
  have hbord : orderOf (b : StatedSU 3 3 F) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hbsq) (fun h1 => hb1 (Subtype.ext h1))
  exact u33_no_three_cent hF he3 he1 haord hbord (fun h1 => hba (Subtype.ext h1.symm)) hab
    (hec a a.2) (hec b b.2)

end U33

theorem not_clConfig_of_u33 {X : Type} [Group X] (h : StatedClassicalModel X .PSU 3 3 1) :
    ¬ ClConfig X := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
  have hK9 : Nat.card K = 9 := by simpa using hK
  let ψ : X ≃* StatedSU 3 3 K :=
    φ.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_statedSU_eq_bot hK9)).trans QuotientGroup.quotientBot)
  exact fun hc => not_clConfig_statedSU hK9 (hc.map ψ)

end CFSG.Quasithin.R3c12
