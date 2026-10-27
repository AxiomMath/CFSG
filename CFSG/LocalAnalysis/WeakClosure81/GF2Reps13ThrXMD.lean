module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXJ

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

structure TetraFrame (A X Q : Subgroup (MulAut W)) (a : MulAut W)
    (lam : s13IsoComps X → Additive ↥X →+ ZMod 3) (q r : ↥X)
    (u₁ u₂ c d : s13IsoComps X) : Prop where
  ha : a ∈ A
  hl : IsCoord X 3 lam
  hQq : Q = Subgroup.zpowers (q : MulAut W)
  hQr : Q.map (MulAut.conj a).toMonoidHom = Subgroup.zpowers (r : MulAut W)
  h12 : u₁ ≠ u₂
  h1c : u₁ ≠ c
  h1d : u₁ ≠ d
  h2c : u₂ ≠ c
  h2d : u₂ ≠ d
  hcd : c ≠ d
  hq : ∀ U, lam U (Additive.ofMul q) ≠ 0 ↔ (U = u₁ ∨ U = u₂ ∨ U = c)
  hr : ∀ U, lam U (Additive.ofMul r) ≠ 0 ↔ (U = u₁ ∨ U = u₂ ∨ U = d)
  hsq : s13Supp X Q = {(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W)}
  hsr : s13Supp X (Q.map (MulAut.conj a).toMonoidHom) =
    {(u₁ : Subgroup W), (u₂ : Subgroup W), (d : Subgroup W)}
  hrk₁ : rk ↥(u₁ : Subgroup W) = 2
  hrk₂ : rk ↥(u₂ : Subgroup W) = 2
  hrkc : rk ↥(c : Subgroup W) = 2
  hrkd : rk ↥(d : Subgroup W) = 2

private theorem w16g_mem_supp_zpow_coord {lam : s13IsoComps X → Additive ↥X →+ ZMod 3}
    (hl : IsCoord X 3 lam) (q : ↥X) (U : s13IsoComps X) :
    (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers (q : MulAut W)) ↔
      lam U (Additive.ofMul q) ≠ 0 := by
  have h1 : (U : Subgroup W) ∈ s13Supp X (Subgroup.zpowers (q : MulAut W)) ↔
      commSub (U : Subgroup W) (Subgroup.zpowers (q : MulAut W)) ≠ ⊥ := by
    simp only [s13Supp, Set.mem_setOf_eq, U.2, true_and]
  rw [h1]
  exact (coord_ne_zero_iff hl q U).symm

private theorem w16g_exists_zpowers_of_card_three {L : Subgroup (MulAut W)}
    (hL : Nat.card ↥L = 3) : ∃ q : MulAut W, L = Subgroup.zpowers q := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : IsCyclic ↥L := isCyclic_of_prime_card hL
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := ↥L)
  have hqtop : Subgroup.zpowers q = ⊤ := (Subgroup.eq_top_iff' _).mpr hq
  refine ⟨(q : MulAut W), ?_⟩
  have hcard : Nat.card ↥L ≤ Nat.card ↥(Subgroup.zpowers (q : MulAut W)) := by
    have hord : orderOf q = Nat.card ↥L := by
      rw [← Nat.card_zpowers (q : ↥L), hqtop, Subgroup.card_top]
    simpa only [Nat.card_zpowers, Subgroup.orderOf_coe, hord] using le_rfl
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr q.2) hcard).symm

private theorem w16g_overlap_data {g : MulAut W}
    (he : (s13Supp X Q).ncard = 3)
    (he' : (s13Supp X (Q.map (MulAut.conj g).toMonoidHom)).ncard = 3)
    (hov : (s13Supp X (Q.map (MulAut.conj g).toMonoidHom) ∩ s13Supp X Q).ncard = 2) :
    ∃ u₁ u₂ c d : s13IsoComps X,
      u₁ ≠ u₂ ∧ u₁ ≠ c ∧ u₁ ≠ d ∧ u₂ ≠ c ∧ u₂ ≠ d ∧ c ≠ d ∧
      s13Supp X Q = {(u₁ : Subgroup W), (u₂ : Subgroup W), (c : Subgroup W)} ∧
      s13Supp X (Q.map (MulAut.conj g).toMonoidHom) =
        {(u₁ : Subgroup W), (u₂ : Subgroup W), (d : Subgroup W)} := by
  classical
  set e : Set (Subgroup W) := s13Supp X Q with he_def
  set e' : Set (Subgroup W) := s13Supp X (Q.map (MulAut.conj g).toMonoidHom) with he'_def
  have he_e : e.ncard = 3 := by rw [he_def]; exact he
  have he'_e : e'.ncard = 3 := by rw [he'_def]; exact he'
  have hov_e : (e' ∩ e).ncard = 2 := by rw [he_def, he'_def]; exact hov
  obtain ⟨U₁, U₂, hU₁₂, hinter⟩ := Set.ncard_eq_two.mp hov_e
  have hU₁_int : U₁ ∈ e' ∩ e := by rw [hinter]; simp
  have hU₂_int : U₂ ∈ e' ∩ e := by rw [hinter]; simp
  have hU₁e : U₁ ∈ e := hU₁_int.2
  have hU₂e : U₂ ∈ e := hU₂_int.2
  let u₁ : s13IsoComps X := ⟨U₁, hU₁e.1⟩
  let u₂ : s13IsoComps X := ⟨U₂, hU₂e.1⟩
  have hCcard : (e \ ({U₁, U₂} : Set (Subgroup W))).ncard = 1 := by
    rw [← hinter, Set.ncard_sdiff Set.inter_subset_right, he_e, hov_e]
  obtain ⟨C, hCeq⟩ := Set.ncard_eq_one.mp hCcard
  have hCmem : C ∈ e \ ({U₁, U₂} : Set (Subgroup W)) := by
    rw [hCeq]; exact Set.mem_singleton C
  have hC : C ∈ e := hCmem.1
  have hCnot : C ∉ ({U₁, U₂} : Set (Subgroup W)) := hCmem.2
  let c : s13IsoComps X := ⟨C, hC.1⟩
  have hDcard : (e' \ ({U₁, U₂} : Set (Subgroup W))).ncard = 1 := by
    rw [← hinter, Set.ncard_sdiff Set.inter_subset_left, he'_e, hov_e]
  obtain ⟨Dd, hDdeq⟩ := Set.ncard_eq_one.mp hDcard
  have hDdmem : Dd ∈ e' \ ({U₁, U₂} : Set (Subgroup W)) := by
    rw [hDdeq]; exact Set.mem_singleton Dd
  have hDd : Dd ∈ e' := hDdmem.1
  have hDdnot : Dd ∉ ({U₁, U₂} : Set (Subgroup W)) := hDdmem.2
  let d : s13IsoComps X := ⟨Dd, hDd.1⟩
  have hsq : e = ({U₁, U₂, C} : Set (Subgroup W)) := by
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hz2 : z ∈ ({U₁, U₂} : Set (Subgroup W))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz2 ⊢
        rcases hz2 with rfl | rfl <;> simp
      · have hzmem : z ∈ e \ ({U₁, U₂} : Set (Subgroup W)) := ⟨hz, hz2⟩
        rw [hCeq] at hzmem
        simp only [Set.mem_singleton_iff] at hzmem
        rw [hzmem]; simp
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · exact hU₁e
      · exact hU₂e
      · exact hC
  have hsr : e' = ({U₁, U₂, Dd} : Set (Subgroup W)) := by
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hz2 : z ∈ ({U₁, U₂} : Set (Subgroup W))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz2 ⊢
        rcases hz2 with rfl | rfl <;> simp
      · have hzmem : z ∈ e' \ ({U₁, U₂} : Set (Subgroup W)) := ⟨hz, hz2⟩
        rw [hDdeq] at hzmem
        simp only [Set.mem_singleton_iff] at hzmem
        rw [hzmem]; simp
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · exact hU₁_int.1
      · exact hU₂_int.1
      · exact hDd
  have h12 : u₁ ≠ u₂ := by
    intro hEq
    exact hU₁₂ (congrArg Subtype.val hEq)
  have h1c : u₁ ≠ c := by
    intro hEq
    have hCU₁ : C = U₁ := (congrArg Subtype.val hEq).symm
    apply hCnot
    rw [hCU₁]
    simp
  have h1d : u₁ ≠ d := by
    intro hEq
    have hDd₁ : Dd = U₁ := (congrArg Subtype.val hEq).symm
    apply hDdnot
    rw [hDd₁]
    simp
  have h2c : u₂ ≠ c := by
    intro hEq
    have hCU₂ : C = U₂ := (congrArg Subtype.val hEq).symm
    apply hCnot
    rw [hCU₂]
    simp
  have h2d : u₂ ≠ d := by
    intro hEq
    have hDd₂ : Dd = U₂ := (congrArg Subtype.val hEq).symm
    apply hDdnot
    rw [hDd₂]
    simp
  have hcd : c ≠ d := by
    intro hEq
    have hCD : C = Dd := congrArg Subtype.val hEq
    apply hCnot
    rw [← hinter]
    refine ⟨?_, hC⟩
    rw [hCD]; exact hDd
  refine ⟨u₁, u₂, c, d, h12, h1c, h1d, h2c, h2d, hcd, ?_, ?_⟩
  · exact hsq
  · exact hsr

theorem w16g_tetra_frame (h : HAb A X Q t 3) (hQ3 : Nat.card ↥Q = 3)
    (he : (s13Supp X Q).ncard = 3)
    (hov : ∃ a ∈ A,
      (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard = 2) :
    ∃ (a : MulAut W) (lam : s13IsoComps X → Additive ↥X →+ ZMod 3) (q r : ↥X)
      (u₁ u₂ c d : s13IsoComps X), TetraFrame A X Q a lam q r u₁ u₂ c d := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨a, ha, hov2⟩ := hov
  have hSP : s13Supp X (Q.map (MulAut.conj a).toMonoidHom) =
      (fun U : Subgroup W => U.map a.toMonoidHom) '' s13Supp X Q :=
    s13Supp_conj (X := X) (L := Q) (g := a) (h.hXA a ha)
      (fun x hx => by simpa using h.hXA a⁻¹ (A.inv_mem ha) x hx)
  have he' : (s13Supp X (Q.map (MulAut.conj a).toMonoidHom)).ncard = 3 := by
    rw [hSP, Set.ncard_image_of_injective _ (Subgroup.map_injective a.injective)]
    exact he
  have hQX' : Q.map (MulAut.conj a).toMonoidHom ≤ X := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    change (MulAut.conj a) q₀ ∈ X
    rw [MulAut.conj_apply]
    exact h.hXA a ha q₀ (h.hQX hq₀)
  obtain ⟨q₀, hQq₀⟩ := w16g_exists_zpowers_of_card_three hQ3
  have hq₀Q : q₀ ∈ Q := by rw [hQq₀]; exact Subgroup.mem_zpowers q₀
  let q : ↥X := ⟨q₀, h.hQX hq₀Q⟩
  have hQq : Q = Subgroup.zpowers (q : MulAut W) := hQq₀
  have hQ3' : Nat.card ↥(Q.map (MulAut.conj a).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, hQ3]
  obtain ⟨r₀, hQr₀⟩ := w16g_exists_zpowers_of_card_three hQ3'
  have hr₀Q' : r₀ ∈ Q.map (MulAut.conj a).toMonoidHom := by
    rw [hQr₀]; exact Subgroup.mem_zpowers r₀
  let r : ↥X := ⟨r₀, hQX' hr₀Q'⟩
  have hQr : Q.map (MulAut.conj a).toMonoidHom = Subgroup.zpowers (r : MulAut W) := hQr₀
  obtain ⟨lam, hl⟩ := exists_coord h.hW hp3 hp32 h.hXe
  obtain ⟨u₁, u₂, c, d, h12, h1c, h1d, h2c, h2d, hcd, hsq, hsr⟩ :=
    w16g_overlap_data (X := X) (Q := Q) (g := a) he he' hov2
  have h' : HAb A X (Q.map (MulAut.conj a).toMonoidHom) (a * t * a⁻¹) 3 := h.conj ha
  have hrank := (s13_three_ranks h).1 he
  have hrank' := (s13_three_ranks h').1 he'
  refine ⟨a, lam, q, r, u₁, u₂, c, d, ?_⟩
  refine ⟨ha, hl, hQq, hQr, h12, h1c, h1d, h2c, h2d, hcd, ?_, ?_, hsq, hsr,
    ?_, ?_, ?_, ?_⟩
  · intro U
    rw [← w16g_mem_supp_zpow_coord hl q U, ← hQq, hsq]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
  · intro U
    rw [← w16g_mem_supp_zpow_coord hl r U, ← hQr, hsr]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
  · exact hrank (u₁ : Subgroup W) (by rw [hsq]; simp)
  · exact hrank (u₂ : Subgroup W) (by rw [hsq]; simp)
  · exact hrank (c : Subgroup W) (by rw [hsq]; simp)
  · exact hrank' (d : Subgroup W) (by rw [hsr]; simp)

end CFSG.LocalAnalysis.WeakClosure81
