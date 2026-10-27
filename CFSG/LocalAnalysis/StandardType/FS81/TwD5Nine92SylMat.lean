module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Main
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5OE6
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5OddCore
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5ReflMat
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5ReflCheck
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Transfer
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem localOrthII_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {B : Basis3 G (5 + 1)} (hb0 : B.b 0 = b₀) (hrec : RecOutTwD5 B b₀) : LocalOrthII B b₀ := by
  refine ⟨?_, Or.inr (Or.inr hrec.2.1)⟩
  refine le_antisymm ?_ ?_
  ·
    intro A hA
    obtain ⟨g, hgC, hActs⟩ := hA
    have hgncomm : g * b₀ = b₀ * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      have hconj : MulAut.conj g b₀ = b₀ := by
        rw [MulAut.conj_apply, hgncomm, mul_assoc, mul_inv_cancel, mul_one]
      simpa using congrArg Subgroup.zpowers hconj
    have hAall : A ∈ evenAll0 5 := by
      rw [← hrec.2.1]
      exact ⟨g, hgN, hActs⟩
    obtain ⟨σ, s, hsign, ⟨hσ0, hprod⟩, hAeq⟩ := hAall
    have hcol : (fun i : Fin (5 + 1) => A i 0) =
        Pi.single (0 : Fin (5 + 1)) (s 0) := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [hAeq, spMat, hσ0]
      · simp [hAeq, spMat, hσ0, hi]
    have hvec : B.vec (fun i : Fin (5 + 1) => A i 0) = b₀ := by
      rw [← hActs 0, hb0, hgncomm]
      group
    have hsingle : (Pi.single (0 : Fin (5 + 1)) (s 0) : Coords (5 + 1)) =
        Pi.single (0 : Fin (5 + 1)) (1 : ZMod 3) := by
      apply B.vec_injective
      rw [← hcol, hvec, B.vec_single, hb0]
    have hs0 : s 0 = 1 := by
      simpa using congrFun hsingle 0
    have hsprod : ∏ i : Fin 5, s i.succ = 1 := by
      have h := Fin.prod_univ_succ (fun i : Fin (5 + 1) => s i)
      rw [hprod, hs0, one_mul] at h
      exact h.symm
    rw [evenFix0, spSet]
    exact ⟨σ, s, hsign, ⟨hσ0, hs0, hsprod⟩, hAeq⟩
  ·
    intro A hA
    have hAll : A ∈ evenAll0 5 := evenFix0_five_subset_evenAll0 hA
    rw [← hrec.2.1] at hAll
    obtain ⟨g, hgN, hActs⟩ := hAll
    obtain ⟨σ, s, _, ⟨hσ0, hs0, -⟩, hAeq⟩ := hA
    have hcol : (fun i : Fin (5 + 1) => A i 0) =
        Pi.single (0 : Fin (5 + 1)) (1 : ZMod 3) := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [hAeq, spMat, hσ0, hs0]
      · simp [hAeq, spMat, hσ0, hi]
    have hconj : g * b₀ * g⁻¹ = b₀ := by
      have h := hActs 0
      rw [hcol, B.vec_single, hb0] at h
      exact h
    refine ⟨g, ?_, hActs⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * b₀ = (g * b₀ * g⁻¹) * g := by group
      _ = b₀ * g := by rw [hconj]

theorem oddCoreTrivial_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀) : OddCoreTrivial E :=
  t5OddCore_holds G b₀ K E hstd B hB (Or.inr (localOrthII_of_recOutTwD5 hB.2.1 hrec)) hfus

theorem glHom_ggAutomizer_eq_oE6_one {G : Type} [Group G]
    [Finite G] {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀) :
    (ggAutomizer ⊤ B.span).map B.glHom = oE6 1 := by
  have hodd : OddCoreTrivial B.span := by
    rw [hB.1]
    exact oddCoreTrivial_of_recOutTwD5 hstd hB hrec hfus
  have hS : StabMatHyp 5 (evenAll0 5) ((ggAutomizer ⊤ B.span).map B.glHom) :=
    B.stabMatHyp_xg hB.2.1 hrec.2.1 hodd hfus
  have hcard : Nat.card ↥((ggAutomizer ⊤ B.span).map B.glHom) = 103680 := by
    rw [Subgroup.card_map_of_injective B.glHom_injective, hrec.1]
  have hgt : 2 ^ 6 * Nat.factorial 6 <
      Nat.card ↥((ggAutomizer ⊤ B.span).map B.glHom) := by
    rw [hcard]
    norm_num
  obtain ⟨ε, hε, hX⟩ :=
    t5MatMain_of_refl t5ReflAll_holds ((ggAutomizer ⊤ B.span).map B.glHom) hS hgt
  have hε1 : ε = 1 := by
    let v : Coords (5 + 1) := fun _ => 1
    have hv : v ≠ 0 := by
      intro h0
      have h1 : v 0 = (0 : Coords (5 + 1)) 0 := congrFun h0 0
      simp [v] at h1
    have hwt : wt v = 6 := by
      unfold wt
      have hf : (Finset.univ.filter fun i : Fin (5 + 1) => v i ≠ 0) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro i _
        simp [v]
      rw [hf, Finset.card_univ, Fintype.card_fin]
    have hprodv : ∏ i : Fin (5 + 1), v i = 1 := by simp [v]
    have hconj : IsConjLine b₀ (B.line v) := by
      rw [hrec.2.2.2 v hv]
      exact Or.inr ⟨hwt, hprodv⟩
    rw [B.isConjLine_iff_isConjLineIn hfus, ← hB.2.1, ← B.vec_single 0,
      B.isConjLineIn_iff_exists_mulVec (Pi.single 0 1) hv] at hconj
    rw [hX] at hconj
    have hshape := (oE6RecOut_holds ε hε).2.2 v hv
    rcases hshape.mp hconj with ⟨hle, -⟩ | ⟨-, hprod⟩
    · rw [hwt] at hle
      omega
    · rw [hprodv] at hprod
      exact hprod.symm
  rw [hε1] at hX
  exact hX

theorem mem_wE6_of_mem_oE6_of_pow_three {ε : ZMod 3} {A : GL (Fin 6) (ZMod 3)}
    (hA : A ∈ oE6 ε) (h3 : A ^ 3 = 1) : A ∈ wE6 ε := by
  have hnegone_center :
      (-1 : GL (Fin 6) (ZMod 3)) ∈ Subgroup.center (GL (Fin 6) (ZMod 3)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    rw [mul_neg_one, neg_one_mul]
  have hnormal : (Subgroup.zpowers (-1 : GL (Fin 6) (ZMod 3))).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hnegone_center)
  have hle : oE6 ε ≤ wE6 ε ⊔ Subgroup.zpowers (-1 : GL (Fin 6) (ZMod 3)) := by
    rw [oE6]
    refine (Subgroup.closure_le
      (wE6 ε ⊔ Subgroup.zpowers (-1 : GL (Fin 6) (ZMod 3)))).mpr ?_
    rintro x (hx | hx)
    · obtain ⟨σ, s, hs, ⟨hσ0, hprod⟩, hxval⟩ := hx
      rcases hs 0 with hs0 | hs0
      · have hxw : x ∈ wE6 ε := by
          refine Subgroup.subset_closure (Or.inl ?_)
          rw [hxval]
          refine ⟨σ, s, hs, ⟨hσ0, hs0, ?_⟩, rfl⟩
          have h := hprod
          rw [Fin.prod_univ_succ, hs0, one_mul] at h
          exact h
        exact Subgroup.mem_sup_left hxw
      ·
        have hxw : -x ∈ wE6 ε := by
          refine Subgroup.subset_closure (Or.inl ?_)
          have hnegval : ((-x : GL (Fin 6) (ZMod 3)) :
              Matrix (Fin 6) (Fin 6) (ZMod 3)) = spMat σ (fun i => -s i) := by
            rw [Units.val_neg, hxval]
            ext i j
            by_cases hij : i = σ j <;> simp [spMat, hij]
          rw [hnegval]
          have hPs : ∏ i : Fin 5, s i.succ = -1 := by
            have h' : -(∏ i : Fin 5, s i.succ) = 1 := by
              have h := hprod
              rw [Fin.prod_univ_succ, hs0] at h
              calc -(∏ i : Fin 5, s i.succ)
                  = (-1 : ZMod 3) * (∏ i : Fin 5, s i.succ) := by ring
                _ = 1 := h
            calc ∏ i : Fin 5, s i.succ
                = (-1 : ZMod 3) * (-(∏ i : Fin 5, s i.succ)) := by ring
              _ = (-1) * 1 := by rw [h']
              _ = -1 := by norm_num
          refine ⟨σ, fun i => -s i, ?_, ⟨hσ0, by change -s 0 = 1; rw [hs0]; decide, ?_⟩, rfl⟩
          · intro i
            rcases hs i with h | h
            · right
              change -s i = -1
              rw [h]
            · left
              change -s i = 1
              rw [h]
              decide
          · rw [show (fun i : Fin 5 => -s i.succ) =
                fun i : Fin 5 => (-1 : ZMod 3) * s i.succ by
              funext i; ring]
            rw [Finset.prod_mul_distrib, hPs]
            norm_num
        have hxeq : (-x) * (-1 : GL (Fin 6) (ZMod 3)) = x := by
          rw [neg_mul_neg, mul_one]
        rw [← hxeq]
        exact Subgroup.mul_mem_sup hxw (Subgroup.mem_zpowers (-1))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr hx))
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_right
      (s := wE6 ε) (t := Subgroup.zpowers (-1 : GL (Fin 6) (ZMod 3)))).mp (hle hA)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
  rcases Int.even_or_odd n with he | ho
  · have hz1 : z = 1 := by
      rw [← hn]
      exact Even.neg_one_zpow he
    rw [← hyz, hz1, mul_one]
    exact hy
  ·
    have hzn : z = -1 := by
      rw [← hn]
      exact Odd.neg_one_zpow ho
    have hA3 : (y * (-1 : GL (Fin 6) (ZMod 3))) ^ 3 = 1 := by
      rw [← hzn, hyz]
      exact h3
    have hy3 : y ^ 3 = -1 := by
      have h := hA3
      rw [mul_neg_one] at h
      rw [Odd.neg_pow (by decide : Odd 3) y] at h
      have h2 := congrArg (fun t => (-1 : GL (Fin 6) (ZMod 3)) * t) h
      simpa [neg_mul_neg, mul_one] using h2
    have hrow := wE6_mulVec_zero ε (pow_mem hy 3) (Pi.single 0 1)
    rw [hy3] at hrow
    rw [show ((-1 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = -1 by
      rw [Units.val_neg, Units.val_one]] at hrow
    rw [Matrix.neg_mulVec, Matrix.one_mulVec] at hrow
    simp at hrow
    exact absurd hrow (by decide)

end CFSG.StandardType.FrameRoute.FS81

end
