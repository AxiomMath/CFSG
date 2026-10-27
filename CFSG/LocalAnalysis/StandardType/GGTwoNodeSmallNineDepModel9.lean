module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepModel9Aux
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallModel
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepChart

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ninedep_model_9 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (h : Fin 8 → V)
    (α : Fin 8 → Module.Dual (ZMod 3) V) (x : V) (u : Fin 8 → ZMod 3)
    (C : NineDepChart 9 h α x u) (ha : V) (αa : Module.Dual (ZMod 3) V) (hha : αa ha = 2)
    (hx : αa x ≠ 0) (hM : C.e ha 8 ≠ 0) (s : ℕ) (hs : s ≤ 2) (o : ℕ × ℕ × ℕ) (ho : o ∈ kopts ())
    (hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3))
    (hA : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod 3)) :
    ∃ (nF : ℕ) (gens : List Refl) (x' : Vec) (b : ℕ),
      (⟨3, 9, nF, gens, x', b⟩ : Pt) ∈ pts9 () ∧
      ∃ e : V ≃ₗ[ZMod 3] (Fin 9 → ZMod 3), (⟨3, 9, nF, gens, x', b⟩ : Pt).Models e h α x ha αa := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let c : Fin 9 → ZMod 3 := C.e ha
  let d : ZMod 3 := c 8
  have hd : d ≠ 0 := hM
  have hd_eq : C.e ha 8 = d := rfl
  let T : (Fin 9 → ZMod 3) ≃ₗ[ZMod 3] (Fin 9 → ZMod 3) :=
    { toFun := pk4_Tlm c d
      invFun := pk4_Slm c d
      left_inv := fun y => pk4_Tlm_Slm c d hd y
      right_inv := fun y => pk4_Slm_Tlm c d hd y
      map_add' := (pk4_Tlm c d).map_add'
      map_smul' := (pk4_Tlm c d).map_smul' }
  let e' : V ≃ₗ[ZMod 3] (Fin 9 → ZMod 3) := C.e.trans T
  have he' : ∀ w, e' w = pk4_Tlm c d (C.e w) := fun w => rfl
  let uH : Vec := (List.range 8).map (fun k => (pk4_alphaNat α ha k).val)
  let G : List Refl := (List.range 8).map
    (fun k => (⟨(alpha8 k).dropLast ++ [0, uH.getD k 0], hvec8 k ++ [0]⟩ : Refl))
  let e8v : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 1]
  let xv : Vec := [0, 0, 0, 0, 0, 0, 0, 1, 0]
  let fa : Vec := List.ofFn (fun j : Fin 9 => (αa (e'.symm (Pi.single j 1))).val)
  let P : Pt := ⟨3, 9, 8, G ++ [⟨fa, e8v⟩], xv, bound9⟩
  have ho1 : o.2.1 < 3 := by
    have ho' := ho
    simp only [kopts, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at ho'
    rcases ho' with ⟨k, -, rfl⟩ | rfl | rfl | rfl | rfl <;> norm_num
  have ho2 : o.2.2 < 3 := by
    have ho' := ho
    simp only [kopts, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at ho'
    rcases ho' with ⟨k, -, rfl⟩ | rfl | rfl | rfl | rfl <;> norm_num
  have hcx : C.e x 8 = 0 := by rw [C.x_eq]; norm_num
  have hch : ∀ i : Fin 8, C.e (h i) 8 = 0 := by
    intro i
    rw [C.h_eq i 8, List.getD_eq_getElem?_getD]
    have hnone : (hvec8 (i : ℕ))[((8 : Fin 9) : ℕ)]? = none :=
      List.getElem?_eq_none_iff.mpr (by rw [pk4_hvec8_length]; norm_num)
    rw [hnone]
    rfl
  have hlenG : G.length = 8 := by simp [G, List.length_map, List.length_range]
  have he'h : ∀ i : Fin 8, e' (h i) = P.vec (hvec8 i ++ [0]) := by
    intro i
    rw [he', pk4_Tlm_fix c d (C.e (h i)) (hch i)]
    ext j
    rw [C.h_eq i j, Pt.vec, pk4_getD_append_zero]
  have he'x : e' x = (Pi.single (7 : Fin 9) 1 : Fin 9 → ZMod 3) := by
    rw [he', pk4_Tlm_fix c d (C.e x) hcx]
    ext j
    rw [C.x_eq j]
    fin_cases j <;> simp [Pi.single_apply, Fin.ext_iff]
  have he'ha : e' ha = (Pi.single (8 : Fin 9) 1 : Fin 9 → ZMod 3) := by
    rw [he']
    ext j
    rw [pk4_Tlm_apply]
    by_cases h : j = 8
    · subst h
      rw [if_pos rfl]
      change d⁻¹ * c 8 = (Pi.single (8 : Fin 9) 1 : Fin 9 → ZMod 3) 8
      rw [show c 8 = d from rfl, inv_mul_cancel₀ hd, Pi.single_eq_same]
    · rw [if_neg h]
      have hz : c j * d⁻¹ * c 8 = c j := by
        rw [show c 8 = d from rfl, mul_assoc, inv_mul_cancel₀ hd, mul_one]
      change c j - c j * d⁻¹ * c 8 = (Pi.single (8 : Fin 9) 1 : Fin 9 → ZMod 3) j
      rw [hz]
      simp [Pi.single_apply, h]
  have hfa_getD : ∀ j : Fin 9, fa.getD j.val 0 = (αa (e'.symm (Pi.single j 1))).val := by
    intro j
    dsimp only [fa]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.isLt]
    rfl
  have hfa7 : fa.getD 7 0 ≠ 0 := by
    have h : fa.getD 7 0 = (αa (e'.symm (Pi.single (7 : Fin 9) 1))).val := by
      simpa using hfa_getD (7 : Fin 9)
    rw [h]
    rw [show e'.symm (Pi.single (7 : Fin 9) 1) = x from by
          rw [← he'x, e'.symm_apply_apply]]
    exact (ZMod.val_ne_zero _).mpr hx
  have hfa8 : fa.getD 8 0 = 2 := by
    have h : fa.getD 8 0 = (αa (e'.symm (Pi.single (8 : Fin 9) 1))).val := by
      simpa using hfa_getD (8 : Fin 9)
    rw [h]
    rw [show e'.symm (Pi.single (8 : Fin 9) 1) = ha from by
          rw [← he'ha, e'.symm_apply_apply]]
    rw [hha]
    decide
  have hfa_len : fa.length = 9 := by
    dsimp only [fa]
    simp [List.length_ofFn]
  have hfa_mem : fa ∈ allVecs 9 := by
    have hlt : ∀ x ∈ fa, x < 3 := by
      intro x hx
      dsimp only [fa] at hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact ZMod.val_lt _
    have h := pk4_allVecs_mem_of_lt fa hlt
    rwa [hfa_len] at h
  have hαa_dot : ∀ w : V, αa w = P.dot (P.vec fa) (e' w) := by
    intro w
    have hlin : e'.symm (e' w) = ∑ j : Fin 9, (e' w) j • e'.symm (Pi.single j 1) := by
      conv_lhs => rw [pk4_pi_single_expand (e' w)]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])
    calc αa w = αa (e'.symm (e' w)) := by rw [e'.symm_apply_apply]
      _ = αa (∑ j : Fin 9, (e' w) j • e'.symm (Pi.single j 1)) := by rw [hlin]
      _ = ∑ j : Fin 9, (e' w) j * αa (e'.symm (Pi.single j 1)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])
      _ = ∑ j : Fin 9, (fa.getD j.val 0 : ZMod 3) * (e' w) j := by
            exact Finset.sum_congr rfl (fun j _ => by
              rw [hfa_getD j, ZMod.natCast_zmod_val]; ring)
      _ = P.dot (P.vec fa) (e' w) := by
            rw [Pt.dot]; rfl
  have hPvecx : P.vec xv = (Pi.single (7 : Fin 9) 1 : Fin 9 → ZMod 3) := by
    dsimp only [P]
    ext j
    rw [Pt.vec]
    fin_cases j <;> simp [Pi.single_apply, Fin.ext_iff, xv]
  have hPvece8 : P.vec e8v = (Pi.single (8 : Fin 9) 1 : Fin 9 → ZMod 3) := by
    dsimp only [P]
    ext j
    rw [Pt.vec]
    fin_cases j <;> simp [Pi.single_apply, Fin.ext_iff, e8v]
  have hPgetD (i : Fin 8) : P.gens.getD i.val ⟨[], []⟩ = G.getD i.val ⟨[], []⟩ := by
    show (G ++ ([⟨fa, e8v⟩] : List Refl)).getD i.val ⟨[], []⟩ = G.getD i.val ⟨[], []⟩
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by rw [List.length_append, hlenG]; omega),
      List.getElem?_eq_getElem (by omega : i.val < G.length)]
    congr 1
    rw [List.getElem_append_left (by omega : i.val < G.length)]
  have hPgetD8 : P.gens.getD 8 ⟨[], []⟩ = ⟨fa, e8v⟩ := by
    show (G ++ ([⟨fa, e8v⟩] : List Refl)).getD 8 ⟨[], []⟩ = ⟨fa, e8v⟩
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [List.length_append, hlenG])]
    congr 1
  have hG_getD : ∀ i : Fin 8, G.getD i.val ⟨[], []⟩ =
      (⟨(alpha8 i).dropLast ++ [0, uH.getD i.val 0], hvec8 i ++ [0]⟩ : Refl) := by
    intro i
    dsimp only [G]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
    rfl
  have hdot_fa : ∀ j : Fin 8, dotv fa (hvec8 j ++ [0]) = (αa (h j)).val := by
    intro j
    have hb_len : (hvec8 j ++ [0]).length = 9 := by
      rw [List.length_append, pk4_hvec8_length]; rfl
    have hlt : dotv fa (hvec8 j ++ [0]) < 3 := by
      unfold dotv; exact Nat.mod_lt _ (by norm_num)
    have hcast : ((dotv fa (hvec8 j ++ [0]) : ℕ) : ZMod 3) = αa (h j) := by
      rw [pk4_dotv_cast fa (hvec8 j ++ [0]) hfa_len hb_len,
        hαa_dot (h j), he'h j]
      rfl
    calc dotv fa (hvec8 j ++ [0])
        = ((dotv fa (hvec8 j ++ [0]) : ℕ) : ZMod 3).val :=
          (ZMod.val_cast_of_lt hlt).symm
      _ = (αa (h j)).val := by rw [hcast]
  have uH_getD : ∀ i : Fin 8, uH.getD i.val 0 = (α i ha).val := by
    intro i
    dsimp only [uH]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
    simp only [Option.map_some, Option.getD_some]
    have hp : pk4_alphaNat α ha i.val = α i ha := by
      show (if h : i.val < 8 then α ⟨i.val, h⟩ ha else 0) = α i ha
      rw [dif_pos i.isLt]
    rw [hp]
  have hα_dot : ∀ (i : Fin 8) (w : V), α i w =
      P.dot (P.vec ((alpha8 i).dropLast ++ [0, uH.getD i.val 0])) (e' w) := by
    intro i w
    have hdrop : (alpha8 i).dropLast ++ [0] = alpha8 i := by
      unfold alpha8
      rw [List.dropLast_concat]
    have hA : (alpha8 i).dropLast ++ [0, uH.getD i.val 0] =
        (alpha8 i) ++ [uH.getD i.val 0] := by
      rw [show ([0, uH.getD i.val 0] : List ℕ) = [0] ++ [uH.getD i.val 0] from rfl]
      rw [← List.append_assoc, hdrop]
    have hA_lt : ∀ j : ℕ, j < 8 →
        ((alpha8 i).dropLast ++ [0, uH.getD i.val 0]).getD j 0 = (alpha8 i).getD j 0 := by
      intro j hj
      rw [hA]
      exact pk4_getD_append_left (alpha8 i) [uH.getD i.val 0] j (by simpa [alpha8] using hj)
    have hA_seven : ((alpha8 i).dropLast ++ [0, uH.getD i.val 0]).getD 7 0 = 0 := by
      rw [hA]
      rw [pk4_getD_append_left (alpha8 i) [uH.getD i.val 0] 7 (by simp [alpha8])]
      exact pk4_alpha8_getD_seven i
    have hA_eight : ((alpha8 i).dropLast ++ [0, uH.getD i.val 0]).getD 8 0 =
        uH.getD i.val 0 := by
      rw [hA]
      rw [pk4_getD_append_right (alpha8 i) [uH.getD i.val 0] 8
        (by simp [alpha8]) (by simp [alpha8])]
      simp [alpha8]
    have hα_h : ∀ j : Fin 8, j.val < 7 →
        α i (h j) = (((alpha8 i).getD j.val 0 : ℕ) : ZMod 3) := by
      intro j hj
      rw [C.α_eq i (h j)]
      simp only [C.h_eq]
      rw [Finset.sum_eq_single (⟨j.val, by omega⟩ : Fin 9)
        (fun t _ ht => by
          rw [pk4_hvec8_getD_lt j.val hj t.val]
          have hne : t.val ≠ j.val := by
            intro h
            exact ht (show t = (⟨j.val, by omega⟩ : Fin 9) from Fin.ext h)
          rw [if_neg hne, Nat.cast_zero, mul_zero])
        (fun hmem => absurd (Finset.mem_univ _) hmem)]
      rw [pk4_hvec8_getD_lt j.val hj (⟨j.val, by omega⟩ : Fin 9).val, if_pos rfl,
        Nat.cast_one, mul_one]
      have hne8 : ((⟨j.val, by omega⟩ : Fin 9)).val ≠ 8 := by
        show j.val ≠ 8
        omega
      rw [if_neg hne8, add_zero]
    have hCx : C.e x = (Pi.single (7 : Fin 9) 1 : Fin 9 → ZMod 3) := by
      ext t
      rw [C.x_eq t]
      fin_cases t <;> simp [Pi.single_apply, Fin.ext_iff]
    have hα_x : α i x = 0 := by
      rw [C.α_eq i x, hCx]
      rw [Finset.sum_eq_single (7 : Fin 9)
        (fun t _ ht => by
          rw [Pi.single_apply, if_neg ht, mul_zero])
        (fun hmem => absurd (Finset.mem_univ _) hmem)]
      rw [Pi.single_apply, if_pos rfl, mul_one]
      rw [if_neg (by decide : ¬ ((7 : Fin 9).val = 8)), add_zero]
      change (((alpha8 i).getD 7 0 : ℕ) : ZMod 3) = 0
      rw [pk4_alpha8_getD_seven i, Nat.cast_zero]
    have hα_ha : α i ha = ((uH.getD i.val 0 : ℕ) : ZMod 3) := by
      rw [uH_getD i, pk4_val_cast]
    have hbasis : ∀ j : Fin 9,
        α i (e'.symm (Pi.single j 1)) =
          (P.vec ((alpha8 i).dropLast ++ [0, uH.getD i.val 0])) j := by
      intro j
      rcases lt_trichotomy j.val 7 with hlt | heq | hgt
      · have hj8 : j.val < 8 := by omega
        have hvec : P.vec (hvec8 j.val ++ [0]) = (Pi.single j 1 : Fin 9 → ZMod 3) := by
          ext t
          rw [Pt.vec, pk4_getD_append_zero, pk4_hvec8_getD_lt j.val hlt t.val]
          by_cases ht : t = j
          · rw [if_pos (by rw [ht]), Pi.single_apply, if_pos ht]
            simp
          · rw [if_neg (fun h => ht (Fin.ext h)), Pi.single_apply, if_neg ht]
            simp
        have hsym : e'.symm (Pi.single j 1) = h ⟨j.val, hj8⟩ := by
          rw [← hvec, ← he'h ⟨j.val, hj8⟩, e'.symm_apply_apply]
        rw [hsym, hα_h ⟨j.val, hj8⟩ hlt, Pt.vec, hA_lt j.val hj8]
      · have hj7 : j = (7 : Fin 9) := by ext; exact heq
        have hsym : e'.symm (Pi.single j 1) = x := by
          rw [hj7, ← he'x, e'.symm_apply_apply]
        rw [hsym, hα_x, Pt.vec, heq, hA_seven, Nat.cast_zero]
      · have hj8 : j = (8 : Fin 9) := by ext; omega
        have hsym : e'.symm (Pi.single j 1) = ha := by
          rw [hj8, ← he'ha, e'.symm_apply_apply]
        rw [hsym, hα_ha, Pt.vec, show j.val = 8 from by omega, hA_eight]
    have hlin : e'.symm (e' w) = ∑ j : Fin 9, (e' w) j • e'.symm (Pi.single j 1) := by
      conv_lhs => rw [pk4_pi_single_expand (e' w)]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])
    calc α i w = α i (e'.symm (e' w)) := by rw [e'.symm_apply_apply]
      _ = α i (∑ j : Fin 9, (e' w) j • e'.symm (Pi.single j 1)) := by rw [hlin]
      _ = ∑ j : Fin 9, (e' w) j * α i (e'.symm (Pi.single j 1)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])
      _ = ∑ j : Fin 9, (e' w) j *
            (P.vec ((alpha8 i).dropLast ++ [0, uH.getD i.val 0])) j := by
            exact Finset.sum_congr rfl (fun j _ => by rw [hbasis j])
      _ = ∑ j : Fin 9,
            (P.vec ((alpha8 i).dropLast ++ [0, uH.getD i.val 0])) j * (e' w) j := by
            exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = P.dot (P.vec ((alpha8 i).dropLast ++ [0, uH.getD i.val 0])) (e' w) := by
            rw [Pt.dot]
  let sus : Vec := (pk4_nonJ s).map (fun k => (pk4_alphaNat α ha k).val)
  have hu : pk4_uc s o sus = uH := by
    dsimp only [sus, uH]
    exact pk4_u_eq α ha s hs o ho1 hH
  refine ⟨8, G ++ [⟨fa, e8v⟩], xv, bound9, ?_, e', ?_⟩
  · show P ∈ pts9 ()
    unfold pts9
    refine List.mem_flatMap.mpr ⟨s, ?_, ?_⟩
    · interval_cases s <;> simp
    · refine List.mem_flatMap.mpr ⟨o, ho, ?_⟩
      refine List.mem_flatMap.mpr ⟨sus, ?_, ?_⟩
      · have h := pk4_allVecs_mem_of_lt sus (by
          intro x hx
          dsimp only [sus] at hx
          obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
          exact ZMod.val_lt _)
        rwa [List.length_map] at h
      · refine List.mem_map.mpr ⟨fa, ?_, ?_⟩
        · rw [List.mem_filter]
          refine ⟨hfa_mem, ?_⟩
          simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, beq_iff_eq]
          refine ⟨⟨hfa7, hfa8⟩, ?_⟩
          intro jj hjj
          obtain ⟨h1, h2⟩ := pk4_hjj_mem s jj hjj
          have hjlt : jj.1 < 8 := by omega
          have hh1 : s ≤ jj.1 := by omega
          have hh2 : jj.1 < s + 6 := by omega
          rw [hdot_fa ⟨jj.1, hjlt⟩, hA ⟨jj.1, hjlt⟩ hh1 hh2]
          rw [show (jj.1 : ℕ) - s = jj.2 from by omega]
          rw [ZMod.val_cast_of_lt]
          split <;> omega
        · change (⟨3, 9, 8, (List.range 8).map (fun k =>
              (⟨(alpha8 k).dropLast ++ [0, (pk4_uc s o sus).getD k 0],
                hvec8 k ++ [0]⟩ : Refl)) ++ [({ f := fa, h := e8v } : Refl)],
              xv, bound9⟩ : Pt) = P
          rw [hu]
  · unfold Pt.Models
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · show (G ++ ([⟨fa, e8v⟩] : List Refl)).length = 9
      rw [List.length_append, hlenG]; simp
    · rw [he'x, hPvecx]
    · intro i
      refine ⟨?_, ?_⟩
      · rw [hPgetD i, hG_getD i]
        exact he'h i
      · intro w
        rw [hPgetD i, hG_getD i]
        exact hα_dot i w
    · rw [hPgetD8, he'ha, hPvece8]
    · intro w
      rw [hPgetD8]
      exact hαa_dot w

end CFSG.TwoNodeSmall


