module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Sylow
public import Certificates.Certificate9547

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Timmesfeld.RankTwo CFSG.Quasithin.B42G2Id

@[expose] def fixedSet {G : Type*} [Group G] (E : Subgroup G) : Set G :=
  {x | ∃ e ∈ E, e ≠ 1 ∧ x * e = e * x}

theorem conj_mem_fixedSet {G : Type*} [Group G] {E E' : Subgroup G} {h : G}
    (hsurj : ∀ e' ∈ E', ∃ e ∈ E, h * e * h⁻¹ = e') {x : G}
    (hx : x ∈ fixedSet E') : h⁻¹ * x * h ∈ fixedSet E := by
  obtain ⟨e', he', he1, hxe⟩ := hx
  obtain ⟨e, he, rfl⟩ := hsurj e' he'
  refine ⟨e, he, fun h1 => he1 (by rw [h1]; group), ?_⟩
  have : x * (h * e * h⁻¹) = h * e * h⁻¹ * x := hxe
  calc h⁻¹ * x * h * e = h⁻¹ * (x * (h * e * h⁻¹)) * h := by group
    _ = h⁻¹ * (h * e * h⁻¹ * x) * h := by rw [this]
    _ = e * (h⁻¹ * x * h) := by group

section Gen

variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

namespace G28Model

theorem letterElt_xor (r : ℕ) {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    M.letterElt (8 * r + (a ^^^ b)) = M.letterElt (8 * r + a) * M.letterElt (8 * r + b) := by
  have hab : a ^^^ b < 8 := xor_lt8' ha hb
  have e1 : (8 * r + (a ^^^ b)) / 8 = r := by omega
  have e2 : (8 * r + (a ^^^ b)) % 8 = a ^^^ b := by omega
  have e3 : (8 * r + a) / 8 = r := by omega
  have e4 : (8 * r + a) % 8 = a := by omega
  have e5 : (8 * r + b) / 8 = r := by omega
  have e6 : (8 * r + b) % 8 = b := by omega
  simp only [letterElt, e1, e2, e3, e4, e5, e6]
  rw [ofNat'_xor' ha hb, map_add]
  exact xPar_add (F := rootOperatorFamily .G2) (rootVec r) _ _

theorem wordElt_nil : M.wordElt [] = 1 := rfl

theorem wordElt_append (w₁ w₂ : List ℕ) : M.wordElt (w₁ ++ w₂) = M.wordElt w₁ * M.wordElt w₂ := by
  simp [wordElt, List.map_append, List.prod_append]

theorem wordElt_flatMap (f : ℕ → List ℕ) (ts : List ℕ) :
    M.wordElt (ts.flatMap f) = (ts.map fun i => M.wordElt (f i)).prod := by
  induction ts with
  | nil => simp [wordElt]
  | cons i ts ih => rw [List.flatMap_cons, M.wordElt_append, ih, List.map_cons, List.prod_cons]

theorem wordElt_single (n : ℕ) : M.wordElt [n] = M.letterElt n := by
  simp [wordElt]

theorem eq_top_of_simple {H : Subgroup ↥(adjointGroup .G2 K)}
    (hx : ∀ i : Fin Tag.G2.rank, ∀ c : K, xPar (rootOperatorFamily .G2) (Pi.single i 1) c ∈ H)
    (hy : ∀ i : Fin Tag.G2.rank, ∀ c : K, xPar (rootOperatorFamily .G2) (-Pi.single i 1) c ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  refine Subgroup.closure_induction (p := fun x hx => (⟨x, hx⟩ : ↥(adjointGroup .G2 K)) ∈ H)
    ?_ ?_ ?_ ?_ hg
  · rintro x ⟨i, c, h | h⟩
    · have h2 : endHom K (xPar (rootOperatorFamily .G2) (Pi.single i 1) c) = xOp .G2 K i c := by
        rw [xPar_simple, endHom_xElt]
      have : (⟨x, Subgroup.subset_closure ⟨i, c, Or.inl h⟩⟩ : ↥(adjointGroup .G2 K)) =
          xPar (rootOperatorFamily .G2) (Pi.single i 1) c :=
        Subtype.ext (Units.ext (h.trans h2.symm))
      rw [this]
      exact hx i c
    · have h2 : endHom K (xPar (rootOperatorFamily .G2) (-Pi.single i 1) c) = yOp .G2 K i c := by
        rw [xPar_neg_simple, endHom_yElt]
      have : (⟨x, Subgroup.subset_closure ⟨i, c, Or.inr h⟩⟩ : ↥(adjointGroup .G2 K)) =
          xPar (rootOperatorFamily .G2) (-Pi.single i 1) c :=
        Subtype.ext (Units.ext (h.trans h2.symm))
      rw [this]
      exact hy i c
  · exact H.one_mem
  · intro x y hx hy ihx ihy
    exact H.mul_mem ihx ihy
  · intro x hx ihx
    exact H.inv_mem ihx


section Certified


theorem gen_spec :
    uCode ≠ idCode ∧ zCode ≠ idCode ∧ genW.size = 30 ∧
    (∀ k < 14, mulCode (wordCode genW[k]!) zCode = mulCode zCode (wordCode genW[k]!)) ∧
    (∀ k < 16, mulCode (wordCode genW[14 + k]!) uCode = mulCode uCode (wordCode genW[14 + k]!)) ∧
    targetN.size = targetSteps.size ∧
    ∀ m < targetSteps.size, (∀ i ∈ targetSteps[m]!, i < 30) ∧
      wordCode ((targetSteps[m]!).flatMap fun i => genW[i]!) = letterCode targetN[m]! :=
  genOK_spec Certificates.certificate9547

theorem genElt_mem_fixedSet {k : ℕ} (hk : k < 30) : M.wordElt genW[k]! ∈ fixedSet M.E0 := by
  obtain ⟨-, -, -, ha, hb, -⟩ := gen_spec
  have hv : Valid (wordCode genW[k]!) := valid_wordCode _
  have hx := M.rho_wordElt genW[k]!
  by_cases hk14 : k < 14
  · refine ⟨M.zE, M.zE_mem_E0, M.zE_ne_one, ?_⟩
    exact (M.eq_iff_codes (valid_mulCode hv valid_zCode) (valid_mulCode valid_zCode hv)
      (M.rho_mul_code hv valid_zCode hx M.rho_zE) (M.rho_mul_code valid_zCode hv M.rho_zE hx)).2
      (ha k hk14)
  · have hk' : k - 14 < 16 := by omega
    have e : 14 + (k - 14) = k := by omega
    refine ⟨M.uE, M.uE_mem_E0, M.uE_ne_one, ?_⟩
    have := hb (k - 14) hk'
    rw [e] at this
    exact (M.eq_iff_codes (valid_mulCode hv valid_uCode) (valid_mulCode valid_uCode hv)
      (M.rho_mul_code hv valid_uCode hx M.rho_uE) (M.rho_mul_code valid_uCode hv M.rho_uE hx)).2
      this

theorem targetElt_mem {m : ℕ} (hm : m < 6) :
    M.letterElt targetN[m]! ∈ Subgroup.closure (fixedSet M.E0) := by
  obtain ⟨-, -, -, -, -, -, hm'⟩ := gen_spec
  have hsz : targetSteps.size = 6 := by rfl
  obtain ⟨hlt, hword⟩ := hm' m (by omega)
  have h1 : M.wordElt (targetSteps[m]!.flatMap fun i => genW[i]!) = M.letterElt targetN[m]! := by
    apply M.rho_injective
    rw [M.rho_wordElt, M.rho_letterElt, hword]
  rw [← h1, M.wordElt_flatMap]
  refine Subgroup.list_prod_mem _ (fun x hx => ?_)
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (M.genElt_mem_fixedSet (hlt i hi))

theorem letterElt_Aa_mem {t : ℕ} (ht1 : 1 ≤ t) (ht : t < 8) :
    M.letterElt t ∈ Subgroup.closure (fixedSet M.E0) ∧
      M.letterElt (48 + t) ∈ Subgroup.closure (fixedSet M.E0) := by
  have hg : ∀ k < 7, genW[k]! = [1 + k] ∧ genW[7 + k]! = [49 + k] := by decide
  obtain ⟨h1, h2⟩ := hg (t - 1) (by omega)
  have e1 : 1 + (t - 1) = t := by omega
  have e2 : 49 + (t - 1) = 48 + t := by omega
  rw [e1] at h1
  rw [e2] at h2
  refine ⟨?_, ?_⟩
  · have := Subgroup.subset_closure (M.genElt_mem_fixedSet (k := t - 1) (by omega))
    rwa [h1, wordElt_single] at this
  · have := Subgroup.subset_closure (M.genElt_mem_fixedSet (k := 7 + (t - 1)) (by omega))
    rwa [h2, wordElt_single] at this

theorem xPar_rootVec_eq (r : ℕ) (c : K) :
    xPar (rootOperatorFamily .G2) (rootVec r) c = M.letterElt (8 * r + (M.τ c).toNat) := by
  have ht := toNat_lt' (M.τ c)
  have e1 : (8 * r + (M.τ c).toNat) / 8 = r := by omega
  have e2 : (8 * r + (M.τ c).toNat) % 8 = (M.τ c).toNat := by omega
  simp only [letterElt, e1, e2, ofNat'_toNat', RingEquiv.symm_apply_apply]

theorem letter_mem (r : ℕ) (hr : r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 11) {t : ℕ} (ht : t < 8) :
    M.letterElt (8 * r + t) ∈ Subgroup.closure (fixedSet M.E0) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · have : M.letterElt (8 * r + 0) = 1 := by
      have e1 : (8 * r + 0) / 8 = r := by omega
      have e2 : (8 * r + 0) % 8 = 0 := by omega
      simp only [letterElt, e1, e2]
      have : CFSG.Quasithin.GF8.ofNat' 0 = 0 := rfl
      rw [this, map_zero]
      exact xPar_zero _
    rw [this]
    exact Subgroup.one_mem _
  have hA := M.letterElt_Aa_mem ht0 ht
  have h41 := M.targetElt_mem (m := 0) (by norm_num)
  have h42 := M.targetElt_mem (m := 1) (by norm_num)
  have h44 := M.targetElt_mem (m := 2) (by norm_num)
  have h89 := M.targetElt_mem (m := 3) (by norm_num)
  have h90 := M.targetElt_mem (m := 4) (by norm_num)
  have h92 := M.targetElt_mem (m := 5) (by norm_num)
  have tn0 : targetN[0]! = 41 := by decide
  have tn1 : targetN[1]! = 42 := by decide
  have tn2 : targetN[2]! = 44 := by decide
  have tn3 : targetN[3]! = 89 := by decide
  have tn4 : targetN[4]! = 90 := by decide
  have tn5 : targetN[5]! = 92 := by decide
  rw [tn0] at h41
  rw [tn1] at h42
  rw [tn2] at h44
  rw [tn3] at h89
  rw [tn4] at h90
  rw [tn5] at h92
  have x12 : M.letterElt (8 * 5 + 3) = M.letterElt (8 * 5 + 1) * M.letterElt (8 * 5 + 2) :=
    M.letterElt_xor 5 (a := 1) (b := 2) (by norm_num) (by norm_num)
  have x14 : M.letterElt (8 * 5 + 5) = M.letterElt (8 * 5 + 1) * M.letterElt (8 * 5 + 4) :=
    M.letterElt_xor 5 (a := 1) (b := 4) (by norm_num) (by norm_num)
  have x24 : M.letterElt (8 * 5 + 6) = M.letterElt (8 * 5 + 2) * M.letterElt (8 * 5 + 4) :=
    M.letterElt_xor 5 (a := 2) (b := 4) (by norm_num) (by norm_num)
  have x34 : M.letterElt (8 * 5 + 7) = M.letterElt (8 * 5 + 3) * M.letterElt (8 * 5 + 4) :=
    M.letterElt_xor 5 (a := 3) (b := 4) (by norm_num) (by norm_num)
  have y12 : M.letterElt (8 * 11 + 3) = M.letterElt (8 * 11 + 1) * M.letterElt (8 * 11 + 2) :=
    M.letterElt_xor 11 (a := 1) (b := 2) (by norm_num) (by norm_num)
  have y14 : M.letterElt (8 * 11 + 5) = M.letterElt (8 * 11 + 1) * M.letterElt (8 * 11 + 4) :=
    M.letterElt_xor 11 (a := 1) (b := 4) (by norm_num) (by norm_num)
  have y24 : M.letterElt (8 * 11 + 6) = M.letterElt (8 * 11 + 2) * M.letterElt (8 * 11 + 4) :=
    M.letterElt_xor 11 (a := 2) (b := 4) (by norm_num) (by norm_num)
  have y34 : M.letterElt (8 * 11 + 7) = M.letterElt (8 * 11 + 3) * M.letterElt (8 * 11 + 4) :=
    M.letterElt_xor 11 (a := 3) (b := 4) (by norm_num) (by norm_num)
  have m41 : M.letterElt (8 * 5 + 1) ∈ Subgroup.closure (fixedSet M.E0) := h41
  have m42 : M.letterElt (8 * 5 + 2) ∈ Subgroup.closure (fixedSet M.E0) := h42
  have m44 : M.letterElt (8 * 5 + 4) ∈ Subgroup.closure (fixedSet M.E0) := h44
  have m89 : M.letterElt (8 * 11 + 1) ∈ Subgroup.closure (fixedSet M.E0) := h89
  have m90 : M.letterElt (8 * 11 + 2) ∈ Subgroup.closure (fixedSet M.E0) := h90
  have m92 : M.letterElt (8 * 11 + 4) ∈ Subgroup.closure (fixedSet M.E0) := h92
  have m43 := x12 ▸ Subgroup.mul_mem _ m41 m42
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using hA.1
  · interval_cases t
    · exact m41
    · exact m42
    · exact m43
    · exact m44
    · exact x14 ▸ Subgroup.mul_mem _ m41 m44
    · exact x24 ▸ Subgroup.mul_mem _ m42 m44
    · exact x34 ▸ Subgroup.mul_mem _ m43 m44
  · exact hA.2
  · interval_cases t
    · exact m89
    · exact m90
    · exact y12 ▸ Subgroup.mul_mem _ m89 m90
    · exact m92
    · exact y14 ▸ Subgroup.mul_mem _ m89 m92
    · exact y24 ▸ Subgroup.mul_mem _ m90 m92
    · exact y34 ▸ Subgroup.mul_mem _ (y12 ▸ Subgroup.mul_mem _ m89 m90) m92

theorem closure_fixedSet_E0 : Subgroup.closure (fixedSet M.E0) = ⊤ := by
  have hc : ∀ (r : ℕ), (r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 11) → ∀ c : K,
      xPar (rootOperatorFamily .G2) (rootVec r) c ∈ Subgroup.closure (fixedSet M.E0) := by
    intro r hr c
    rw [M.xPar_rootVec_eq r c]
    exact M.letter_mem r hr (toNat_lt' (M.τ c))
  have r5 : rootVec 5 = hexRoot 5 := by decide
  have r0 : rootVec 0 = hexRoot 0 := by decide
  have r11 : rootVec 11 = -hexRoot 5 := by decide
  have r6 : rootVec 6 = -hexRoot 0 := by decide
  apply eq_top_of_simple
  · intro i c
    fin_cases i
    · have e : (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
          rootVec 5 := by
        rw [r5]
        exact single_zero_eq_hexRoot
      show xPar (rootOperatorFamily .G2) (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) c ∈ _
      rw [e]
      exact hc 5 (by norm_num) c
    · have e : (Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
          rootVec 0 := by
        rw [r0]
        exact single_one_eq_hexRoot
      show xPar (rootOperatorFamily .G2) (Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1) c ∈ _
      rw [e]
      exact hc 0 (by norm_num) c
  · intro i c
    fin_cases i
    · have e : (-Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
          rootVec 11 := by
        rw [r11]
        exact congrArg Neg.neg single_zero_eq_hexRoot
      show xPar (rootOperatorFamily .G2) (-Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) c ∈ _
      rw [e]
      exact hc 11 (by norm_num) c
    · have e : (-Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 : Fin Tag.G2.rank → ℤ) =
          rootVec 6 := by
        rw [r6]
        exact congrArg Neg.neg single_one_eq_hexRoot
      show xPar (rootOperatorFamily .G2) (-Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1) c ∈ _
      rw [e]
      exact hc 6 (by norm_num) c

include M in
theorem closure_fixedSet_eq_top (hK : Nat.card K = 8) {E : Subgroup ↥(adjointGroup .G2 K)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    Subgroup.closure (fixedSet E) = ⊤ := by
  have : Finite ↥(adjointGroup .G2 K) := Subtype.finite
  obtain ⟨h, hh⟩ := M.exists_conj_E0 hK hE hE9
  have hinj : Function.Injective (fun e : E => (⟨h * e * h⁻¹, hh e e.2⟩ : M.E0)) := by
    intro a b hab
    have h1 : h * (a : ↥(adjointGroup .G2 K)) * h⁻¹ = h * (b : ↥(adjointGroup .G2 K)) * h⁻¹ :=
      congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hcard : Nat.card M.E0 = Nat.card E := by rw [(M.isElemAbelian_E0_card).2, hE9]
  have hbij := Function.Injective.bijective_of_nat_card_le hinj hcard.le
  have hs : ∀ e' ∈ M.E0, ∃ e ∈ E, h * e * h⁻¹ = e' := fun e' he' => by
    obtain ⟨⟨e, he⟩, hfe⟩ := hbij.2 ⟨e', he'⟩
    exact ⟨e, he, congrArg Subtype.val hfe⟩
  let N : Subgroup ↥(adjointGroup .G2 K) :=
    (Subgroup.closure (fixedSet E)).comap (MulAut.conj h⁻¹).toMonoidHom
  have hN : fixedSet M.E0 ⊆ N := fun x hx => by
    have := conj_mem_fixedSet hs hx
    exact Subgroup.subset_closure (by simpa [MulAut.conj_apply] using this)
  have hN' : Subgroup.closure (fixedSet M.E0) ≤ N := (Subgroup.closure_le N).mpr hN
  rw [M.closure_fixedSet_E0] at hN'
  rw [eq_top_iff]
  intro g _
  have h2 : (MulAut.conj h⁻¹) (h * g * h⁻¹) ∈ Subgroup.closure (fixedSet E) :=
    hN' (Subgroup.mem_top (h * g * h⁻¹))
  rwa [MulAut.conj_apply, show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at h2

end Certified

end G28Model

end Gen

end CFSG.RankThree.PartTwo.Sec4.Item434G28
