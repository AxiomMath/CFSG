module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdj

public section

namespace CFSG.GroupTheory

private theorem two_le_of_three_le_two_pow {n k : ℕ} (hn : 3 ≤ n) (hnk : n = 2 ^ k) :
    2 ≤ k := by
  by_contra h
  have hk : k ≤ 1 := by omega
  have hle : 2 ^ k ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hk
  omega

private theorem eq_two_pow_pred_of_eq_two_mul {n m k : ℕ} (hnk : n = 2 ^ k)
    (hmn : n = 2 * m) (hk : 2 ≤ k) : m = 2 ^ (k - 1) := by
  have hkpos : 1 ≤ k := by omega
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc 2 ^ k = 2 ^ (k - 1 + 1) := by rw [Nat.sub_add_cancel hkpos]
      _ = 2 ^ (k - 1) * 2 := Nat.pow_succ 2 (k - 1)
      _ = 2 * 2 ^ (k - 1) := by rw [mul_comm]
  omega

private theorem even_of_eq_two_pow {n m k : ℕ} (hn : 3 ≤ n) (hnk : n = 2 ^ k)
    (hm : m = n ∨ m = 2 * n ∨ n = 2 * m) : Even m := by
  have hk2 : 2 ≤ k := two_le_of_three_le_two_pow hn hnk
  rcases hm with rfl | rfl | hmn
  · rw [hnk]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  · exact even_two_mul n
  · rw [eq_two_pow_pred_of_eq_two_mul hnk hmn hk2]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩

private theorem three_dvd_two_pow_sub_one_of_even {m : ℕ} (hm : Even m) :
    3 ∣ 2 ^ m - 1 := by
  obtain ⟨t, rfl⟩ := even_iff_exists_two_mul.mp hm
  have hmod : (2 : ℕ) ^ (2 * t) ≡ 1 [MOD 3] := by
    have h4 : (2 ^ 2 : ℕ) ≡ 1 [MOD 3] := by norm_num
    have hpow : (2 ^ 2 : ℕ) ^ t ≡ 1 ^ t [MOD 3] := h4.pow t
    simpa [pow_mul] using hpow
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmod.symm

private theorem odd_dvd_of_dvd {n m s : ℕ} (hm : m = n ∨ m = 2 * n ∨ n = 2 * m)
    (hsn : s ∣ n) (hso : Odd s) : s ∣ m := by
  rcases hm with hmn | hmn | hnm
  · exact hmn ▸ hsn
  · rw [hmn]
    exact hsn.trans (dvd_mul_left n 2)
  · rw [hnm] at hsn
    exact hso.coprime_two_right.dvd_of_dvd_mul_right (by simpa [mul_comm] using hsn)

private theorem dvd_two_pow_sub_one_of_odd_dvd {n m r s : ℕ}
    (hm : m = n ∨ m = 2 * n ∨ n = 2 * m) (hsn : s ∣ n) (hso : Odd s)
    (hsr : r ∣ 2 ^ s - 1) : r ∣ 2 ^ m - 1 :=
  hsr.trans (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (odd_dvd_of_dvd hm hsn hso))

private theorem four_le_and_even_of_eq_two_pow {n m k : ℕ} {P : ℕ → Prop}
    (hn : 3 ≤ n) (hnk : n = 2 ^ k)
    (hm : m = n ∨ m = 2 * n ∨ (n = 2 * m ∧ P m))
    (hnot : ¬ (P 2 ∧ n = 4)) : 4 ≤ m ∧ Even m := by
  have hm' : m = n ∨ m = 2 * n ∨ n = 2 * m := by
    rcases hm with h | h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hk2 : 2 ≤ k := two_le_of_three_le_two_pow hn hnk
  refine ⟨?_, even_of_eq_two_pow hn hnk hm'⟩
  rcases hm with rfl | rfl | ⟨hnm, hP⟩
  · rw [hnk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk2
  · omega
  · have hk3 : 3 ≤ k := by
      by_contra h
      have hk_eq : k = 2 := by omega
      rw [hk_eq] at hnk
      norm_num at hnk
      have hm2' : m = 2 := by omega
      exact hnot ⟨by rwa [hm2'] at hP, hnk⟩
    rw [eq_two_pow_pred_of_eq_two_mul hnk hnm (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)

theorem two_le_and_dvd_two_pow_sub_one_and_four_le_even {n m r : ℕ} {P : ℕ → Prop}
    (hn : 3 ≤ n)
    (hm : m = n ∨ m = 2 * n ∨ (n = 2 * m ∧ P m))
    (hcase : (∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
      (∃ k : ℕ, n = 2 ^ k ∧ r = 3)) :
    2 ≤ m ∧ r ∣ 2 ^ m - 1 ∧
      ((∃ k : ℕ, n = 2 ^ k) → ¬ (P 2 ∧ n = 4) → 4 ≤ m ∧ Even m) := by
  have hm' : m = n ∨ m = 2 * n ∨ n = 2 * m := by
    rcases hm with h | h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine ⟨by rcases hm with h | h | ⟨h, _⟩ <;> omega, ?_, ?_⟩
  · rcases hcase with ⟨s, hsn, hso, _, hsr⟩ | ⟨k, hnk, hr3⟩
    · exact dvd_two_pow_sub_one_of_odd_dvd hm' hsn hso hsr
    · rw [hr3]
      exact three_dvd_two_pow_sub_one_of_even (even_of_eq_two_pow hn hnk hm')
  · rintro ⟨k, hnk⟩ hnot
    exact four_le_and_even_of_eq_two_pow hn hnk hm hnot

end CFSG.GroupTheory

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private noncomputable def adjPi (c : Ctx23L D Ch)
    (hKM : Hinf (D.M ⊓ c.L) ≤ D.M) :
    ↥(Hinf (D.M ⊓ c.L)) →* Bar2 D.M :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).comp (Subgroup.inclusion hKM)

private noncomputable def adjN (c : Ctx23L D Ch) (d : S23_9_A0Data D Ch c)
    (hKM : Hinf (D.M ⊓ c.L) ≤ D.M) : Subgroup ↥(Hinf (D.M ⊓ c.L)) :=
  d.rep.ker.comap (adjPi c hKM)

private noncomputable def adjP (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (d : S23_9_A0Data D Ch c) (hKM : Hinf (D.M ⊓ c.L) ≤ D.M)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) : Subgroup ↥(c.H hV) :=
  ((adjN c d hKM).map
    ((c.phiL hV).comp (Subgroup.inclusion hKL)).rangeRestrict).map
      ((c.phiL hV).comp (Subgroup.inclusion hKL)).range.subtype

private noncomputable def adjR (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) : Subgroup ↥(Hinf (D.M ⊓ c.L)) :=
  ((c.phiL hV).comp (Subgroup.inclusion hKL)).ker

private theorem adjN_normal (c : Ctx23L D Ch) (d : S23_9_A0Data D Ch c)
    (hKM : Hinf (D.M ⊓ c.L) ≤ D.M) : (adjN c d hKM).Normal := by
  dsimp only [adjN]
  infer_instance

private theorem adjPi_range (c : Ctx23L D Ch)
    (hKM : Hinf (D.M ⊓ c.L) ≤ D.M) :
    (adjPi c hKM).range = barImage D.M (Hinf (D.M ⊓ c.L)) := by
  simp only [adjPi, MonoidHom.range_comp, Subgroup.inclusion_range, barImage]

private theorem range_comp_inclusion_eq_map (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) :
    ((c.phiL hV).comp (Subgroup.inclusion hKL)).range =
      ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

private theorem adj_le_N_of_barImage_le_ker (c : Ctx23L D Ch) (d : S23_9_A0Data D Ch c)
    (hKM : Hinf (D.M ⊓ c.L) ≤ D.M) {Y : Subgroup G}
    (hle : barImage D.M Y ≤ d.rep.ker) :
    Y.subgroupOf (Hinf (D.M ⊓ c.L)) ≤ adjN c d hKM := by
  intro k hk
  dsimp only [adjN]
  change (uc22p21cPi D.M) ⟨k.1, hKM k.2⟩ ∈ d.rep.ker
  exact hle (uc22p21c_mem_barImage.2
    ⟨⟨k.1, hKM k.2⟩, Subgroup.mem_subgroupOf.mp hk, rfl⟩)

private theorem adj_map_subgroupOf_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) {Y : Subgroup G}
    (hY : Y ≤ Hinf (D.M ⊓ c.L)) :
    (Y.subgroupOf c.L).map (c.phiL hV) =
      ((Y.subgroupOf (Hinf (D.M ⊓ c.L))).map
        ((c.phiL hV).comp (Subgroup.inclusion hKL)).rangeRestrict).map
          ((c.phiL hV).comp (Subgroup.inclusion hKL)).range.subtype := by
  have hcomp : (Y.subgroupOf (Hinf (D.M ⊓ c.L))).map
      (Subgroup.inclusion hKL) = Y.subgroupOf c.L := by
    have h1 : ((Y.subgroupOf (Hinf (D.M ⊓ c.L))).map
        (Subgroup.inclusion hKL)).map c.L.subtype = Y := by
      rw [Subgroup.map_map, Subgroup.subtype_comp_inclusion,
        Subgroup.map_subgroupOf_eq_of_le hY]
    have h2 : (Y.subgroupOf c.L).map c.L.subtype = Y :=
      Subgroup.map_subgroupOf_eq_of_le (hY.trans hKL)
    exact Subgroup.map_subtype_inj.mp (h1.trans h2.symm)
  calc (Y.subgroupOf c.L).map (c.phiL hV)
      = ((Y.subgroupOf (Hinf (D.M ⊓ c.L))).map
          (Subgroup.inclusion hKL)).map (c.phiL hV) := by rw [hcomp]
    _ = (Y.subgroupOf (Hinf (D.M ⊓ c.L))).map
          ((c.phiL hV).comp (Subgroup.inclusion hKL)) := by
        rw [Subgroup.map_map]
    _ = (Y.subgroupOf (Hinf (D.M ⊓ c.L))).map
          ((((c.phiL hV).comp (Subgroup.inclusion hKL)).range).subtype.comp
            ((c.phiL hV).comp (Subgroup.inclusion hKL)).rangeRestrict) := by
        rw [MonoidHom.subtype_comp_rangeRestrict]
    _ = ((Y.subgroupOf (Hinf (D.M ⊓ c.L))).map
          ((c.phiL hV).comp (Subgroup.inclusion hKL)).rangeRestrict).map
            (((c.phiL hV).comp (Subgroup.inclusion hKL)).range).subtype := by
        rw [Subgroup.map_map]

private theorem adjP_eq_map (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (d : S23_9_A0Data D Ch c) (hKM : Hinf (D.M ⊓ c.L) ≤ D.M)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) :
    adjP c hV d hKM hKL =
      (adjN c d hKM).map ((c.phiL hV).comp (Subgroup.inclusion hKL)) := by
  dsimp only [adjP]
  rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]

private theorem adjP_le_map (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (d : S23_9_A0Data D Ch c) (hKM : Hinf (D.M ⊓ c.L) ≤ D.M)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) :
    adjP c hV d hKM hKL ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) := by
  rw [adjP_eq_map c hV d hKM hKL, ← range_comp_inclusion_eq_map c hV hKL]
  exact Subgroup.map_le_range
    (f := (c.phiL hV).comp (Subgroup.inclusion hKL)) (adjN c d hKM)

private theorem adjP_normalizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (d : S23_9_A0Data D Ch c) (hKM : Hinf (D.M ⊓ c.L) ≤ D.M)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) :
    ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) ≤
      Subgroup.normalizer
        ((adjP c hV d hKM hKL : Subgroup ↥(c.H hV)) : Set ↥(c.H hV)) := by
  rw [← range_comp_inclusion_eq_map c hV hKL]
  haveI hNf : ((adjN c d hKM).map
      ((c.phiL hV).comp (Subgroup.inclusion hKL)).rangeRestrict).Normal :=
    (adjN_normal c d hKM).map _
      (MonoidHom.rangeRestrict_surjective _)
  have h := CFSG.GroupTheory.map_subtype_le_normalizer
    (K := ((c.phiL hV).comp (Subgroup.inclusion hKL)).range) (X := ⊤)
    (L := (adjN c d hKM).map
      ((c.phiL hV).comp (Subgroup.inclusion hKL)).rangeRestrict)
    (Subgroup.le_normalizer_of_normal
      (H := (adjN c d hKM).map
        ((c.phiL hV).comp (Subgroup.inclusion hKL)).rangeRestrict) (K := ⊤))
  simpa [adjP, Subgroup.map_top, Subgroup.range_subtype] using h

private theorem le_adjP_of_barImage_le_ker (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (d : S23_9_A0Data D Ch c) (hKM : Hinf (D.M ⊓ c.L) ≤ D.M)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) {X : Subgroup ↥(c.H hV)} {Y : Subgroup G}
    (hX : X ≤ (Y.subgroupOf c.L).map (c.phiL hV))
    (hY : Y ≤ Hinf (D.M ⊓ c.L)) (hle : barImage D.M Y ≤ d.rep.ker) :
    X ≤ adjP c hV d hKM hKL := by
  calc X ≤ (Y.subgroupOf c.L).map (c.phiL hV) := hX
    _ = ((Y.subgroupOf (Hinf (D.M ⊓ c.L))).map
          ((c.phiL hV).comp (Subgroup.inclusion hKL)).rangeRestrict).map
            ((c.phiL hV).comp (Subgroup.inclusion hKL)).range.subtype :=
      adj_map_subgroupOf_eq c hV hKL hY
    _ ≤ adjP c hV d hKM hKL := by
      dsimp only [adjP]
      exact Subgroup.map_mono (Subgroup.map_mono
        (adj_le_N_of_barImage_le_ker c d hKM hle))

private theorem adjR_isSolvable (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L) :
    Group.IsSolvable ↥(adjR c hV hKL) := by
  haveI : Group.IsSolvable ↥(c.phiL hV).ker := phiL_ker_isSolvable c hV hK hnat
  dsimp only [adjR]
  let g : ↥(((c.phiL hV).comp (Subgroup.inclusion hKL)).ker) →*
      ↥(c.phiL hV).ker :=
    { toFun := fun x => ⟨Subgroup.inclusion hKL x.1, x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := g) fun a b hab =>
    Subtype.ext (Subgroup.inclusion_injective hKL (congrArg Subtype.val hab))

private theorem adj_sup_ker_eq_top (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (d : S23_9_A0Data D Ch c) (hKM : Hinf (D.M ⊓ c.L) ≤ D.M)
    (hKL : Hinf (D.M ⊓ c.L) ≤ c.L)
    (h : adjP c hV d hKM hKL =
      ((c.phiL hV).comp (Subgroup.inclusion hKL)).range) :
    adjN c d hKM ⊔ adjR c hV hKL = ⊤ := by
  rw [adjP_eq_map c hV d hKM hKL] at h
  simpa only [adjR] using codisjoint_iff.mp
    (Subgroup.map_eq_range_iff.mp h)

theorem not_barImage_le_ker_or_of_generate (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (d : S23_9_A0Data D Ch c)
    (hnot : ¬ barImage D.M (Hinf (D.M ⊓ c.L)) ≤ d.rep.ker) (hK : KOrdNatural)
    {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n)
    {X₁ X₂ : Subgroup ↥(c.H hV)}
    (hX₁ : X₁ ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hX₂ : X₂ ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    (hgen : ∀ N ≤ ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV),
      ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) ≤
        Subgroup.normalizer (N : Set ↥(c.H hV)) → X₁ ≤ N → X₂ ≤ N →
        N = ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV))
    {Y₁ Y₂ : Subgroup G} (hY₁ : Y₁ ≤ Hinf (D.M ⊓ c.L))
    (hY₂ : Y₂ ≤ Hinf (D.M ⊓ c.L))
    (hXY₁ : X₁ ≤ (Y₁.subgroupOf c.L).map (c.phiL hV))
    (hXY₂ : X₂ ≤ (Y₂.subgroupOf c.L).map (c.phiL hV)) :
    ¬ barImage D.M Y₁ ≤ d.rep.ker ∨ ¬ barImage D.M Y₂ ≤ d.rep.ker := by
  classical
  have hKL : Hinf (D.M ⊓ c.L) ≤ c.L :=
    (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right
  have hKM : Hinf (D.M ⊓ c.L) ≤ D.M :=
    (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  by_contra hcon
  push Not at hcon
  obtain ⟨hle₁, hle₂⟩ := hcon
  have hX₁P : X₁ ≤ adjP c hV d hKM hKL :=
    le_adjP_of_barImage_le_ker c hV d hKM hKL hXY₁ hY₁ hle₁
  have hX₂P : X₂ ≤ adjP c hV d hKM hKL :=
    le_adjP_of_barImage_le_ker c hV d hKM hKL hXY₂ hY₂ hle₂
  have hP_eq_exp : adjP c hV d hKM hKL =
      ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) :=
    hgen (adjP c hV d hKM hKL) (adjP_le_map c hV d hKM hKL)
      (adjP_normalizer c hV d hKM hKL) hX₁P hX₂P
  have hP_eq : adjP c hV d hKM hKL =
      ((c.phiL hV).comp (Subgroup.inclusion hKL)).range := by
    rw [hP_eq_exp, ← range_comp_inclusion_eq_map c hV hKL]
  have htop := adj_sup_ker_eq_top c hV d hKM hKL hP_eq
  have hKperfect : Group.IsPerfect ↥(Hinf (D.M ⊓ c.L)) :=
    Subgroup.isPerfect_iff.mpr (by simpa using c.Hinf_inf_L_perfect)
  haveI : (adjN c d hKM).Normal := adjN_normal c d hKM
  have hNtop : adjN c d hKM = ⊤ :=
    CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top (B := adjR c hV hKL)
      (M := adjN c d hKM) hKperfect (adjR_isSolvable c hV hK hnat hKL) htop
  refine hnot ?_
  rw [← adjPi_range c hKM]
  intro x hx
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
  change k ∈ adjN c d hKM
  rw [hNtop]
  exact Subgroup.mem_top k

theorem adjData_exponent_fields (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {r m : ℕ}
    (hn : 3 ≤ CFSG.Open.pRank 2 D.Z) (hcn : c.n = CFSG.Open.pRank 2 D.Z)
    (hm : m = CFSG.Open.pRank 2 D.Z ∨ m = 2 * CFSG.Open.pRank 2 D.Z ∨
      (CFSG.Open.pRank 2 D.Z = 2 * m ∧ IsSUn ↥(c.H hV) 4 m ∧
        NatSUn (c.H hV) ⊤ ⊥ 4 m))
    (hcase : (∃ s : ℕ, s ∣ c.n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
      (∃ k : ℕ, c.n = 2 ^ k ∧ r = 3)) :
    2 ≤ m ∧ r ∣ 2 ^ m - 1 ∧
      ((∃ k : ℕ, c.n = 2 ^ k) → ¬ S23_9_SU44 D Ch c hV → 4 ≤ m ∧ Even m) := by
  have hcase' := c.a1_disj_of_cn_eq (n := CFSG.Open.pRank 2 D.Z) hcn hcase
  have h := CFSG.GroupTheory.two_le_and_dvd_two_pow_sub_one_and_four_le_even
    (n := CFSG.Open.pRank 2 D.Z) (m := m) (r := r)
    (P := fun m => IsSUn ↥(c.H hV) 4 m ∧ NatSUn (c.H hV) ⊤ ⊥ 4 m) hn hm hcase'
  refine ⟨h.1, h.2.1, ?_⟩
  rintro ⟨k, hk⟩ hnotSU
  refine h.2.2 ⟨k, by rw [← hcn]; exact hk⟩ ?_
  intro hP
  refine hnotSU ?_
  change IsSUn ↥(c.H hV) 4 2 ∧ NatSUn (c.H hV) ⊤ ⊥ 4 2 ∧ c.n = 4
  exact ⟨hP.1.1, hP.1.2, hcn.trans hP.2⟩

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
