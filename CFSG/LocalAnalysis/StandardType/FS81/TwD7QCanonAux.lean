module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCent
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7M0Model
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaNormElements
public import CFSG.LocalAnalysis.StandardType.FS81.D6MarkOfModel
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Mathlib.GroupTheory.SubgroupSupCommute

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly Subgroup

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

theorem vec_cons_zero (B : Basis3 G (k + 1)) (e : Coords k) :
    B.vec (Fin.cons 0 e) =
      (List.ofFn fun i : Fin k => B.b i.succ ^ (e i).val).prod := by
  unfold vec
  rw [List.ofFn_succ]
  simp

@[expose] def dropFirst (B : Basis3 G (k + 1)) : Basis3 G k where
  b i := B.b i.succ
  comm i j := B.comm i.succ j.succ
  ord i := B.ord i.succ
  indep e he := by
    have h : Fin.cons (0 : ZMod 3) e = (0 : Coords (k + 1)) :=
      B.indep _ ((B.vec_cons_zero e).trans he)
    funext i
    have := congrFun h i.succ
    simpa using this

theorem dropFirst_span (B : Basis3 G (k + 1)) :
    B.dropFirst.span = Subgroup.closure (Set.range fun i : Fin k => B.b i.succ) :=
  rfl

theorem dropFirst_span_le (B : Basis3 G (k + 1)) : B.dropFirst.span ≤ B.span := by
  rw [B.dropFirst_span]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, rfl⟩
  exact B.b_mem_span _

theorem card_span (B : Basis3 G k) : Nat.card ↥B.span = 3 ^ k := by
  rw [← Nat.card_congr B.equiv.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem isElemAbelian_span (B : Basis3 G k) : IsElemAbelian 3 B.span := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    obtain ⟨e, he⟩ := B.exists_vec_eq a.2
    obtain ⟨e', he'⟩ := B.exists_vec_eq b.2
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    rw [← he, ← he', ← B.vec_add, ← B.vec_add, add_comm]
  · intro x hx
    obtain ⟨e, rfl⟩ := B.exists_vec_eq hx
    have h3 : B.vec e ^ 3 = 1 := by
      rw [← B.vec_nsmul 3 e,
        show (3 : ℕ) • e = 0 by
          funext i
          simp [nsmul_eq_mul, show (3 : ZMod 3) = 0 by decide]]
      exact B.vec_zero
    exact h3

theorem eq_zero_of_vec_mem_zpowers_of_coord_zero (B : Basis3 G (k + 1)) {e : Coords (k + 1)}
    (h0 : e 0 = 0) (he : B.vec e ∈ Subgroup.zpowers (B.b 0)) : e = 0 := by
  classical
  have hfin : IsOfFinOrder (B.b 0) := orderOf_pos_iff.mp (by rw [B.ord 0]; norm_num)
  obtain ⟨n, -, hn⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp he)
  have h : B.vec (n • (Pi.single 0 1 : Coords (k + 1))) = B.vec e := by
    rw [B.vec_nsmul, B.vec_single]
    exact hn
  have hcoe : n • (Pi.single 0 1 : Coords (k + 1)) = e := B.vec_injective h
  have hn0 : (n : ZMod 3) = 0 := by
    have h1 := congrFun hcoe 0
    simpa [h0] using h1
  rw [← hcoe]
  funext i
  simp [nsmul_eq_mul, hn0]

end Basis3

open TwD7Q in
theorem img_m0_le_centralizer_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    img (B.b 0 * B.b 1) ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤
      Subgroup.centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))) ∧
      ((img (B.b 0 * B.b 1) ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆).subgroupOf
        (Subgroup.centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))))).Normal := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({B.b 1} : Set G) ⊓ K
  let M : Subgroup G := ⁅C, C⁆
  have hMleC : M ≤ C := Subgroup.commutator_le_self C
  have hMleK : M ≤ K := hMleC.trans inf_le_right
  have hMleCen : M ≤ cen (B.b 0 * B.b 1) := by
    have h := (commutator_centralizer_le_beta_of_std_twD7 hstd B).2
    simpa only [hB.2.1] using h
  have hrec' : RecOutTwD7 B (B.b 0) := hB.2.1.symm ▸ hrec
  have hb₀ : B.b 0 = b₀ := hB.2.1
  have hKC' : K ≤ Subgroup.centralizer ({B.b 0} : Set G) := by
    simpa only [hb₀] using hstd.2.1.1.2.1
  have hKnorm : Subgroup.centralizer ({B.b 0} : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer hstd.2.1.1.2.1).mp
      hstd.2.1.1.2.2.1
    simpa only [hb₀] using h
  have hle : img (B.b 0 * B.b 1) M ≤
      Subgroup.centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))) := by
    rintro _ ⟨m, hmM, rfl⟩
    exact (B.pr_mem_centralizer_twD7Quot_b_zero_iff hrec' m).mpr
      (hKC' (hMleK (mem_subgroupOf.mp hmM)))
  have hconj : ∀ q ∈ Subgroup.centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))),
      ∀ x ∈ img (B.b 0 * B.b 1) M, q * x * q⁻¹ ∈ img (B.b 0 * B.b 1) M := by
    intro q hq x hx
    obtain ⟨g, hgq⟩ := pr_surjective (B.b 0 * B.b 1) q
    have hgC0 : (g : G) ∈ Subgroup.centralizer ({B.b 0} : Set G) :=
      (B.pr_mem_centralizer_twD7Quot_b_zero_iff hrec' g).mp (hgq ▸ hq)
    obtain ⟨m, hmM, rfl⟩ := mem_img_iff.mp hx
    have hgβ : Commute (g : G) (B.b 0 * B.b 1) := mem_cen_iff.mp g.2
    have hg0 : Commute (g : G) (B.b 0) :=
      Subgroup.mem_centralizer_singleton_iff.mp hgC0
    have hg1 : Commute (g : G) (B.b 1) := by
      have hc : Commute (g : G) ((B.b 0)⁻¹ * (B.b 0 * B.b 1)) :=
        hg0.inv_right.mul_right hgβ
      convert hc using 1
      group
    have hCmap : C.map (MulAut.conj (g : G)).toMonoidHom ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        calc B.b 1 * ((g : G) * y * (g : G)⁻¹)
            = (B.b 1 * (g : G)) * y * (g : G)⁻¹ := by group
          _ = ((g : G) * B.b 1) * y * (g : G)⁻¹ := by rw [hg1.eq]
          _ = (g : G) * (B.b 1 * y) * (g : G)⁻¹ := by group
          _ = (g : G) * (y * B.b 1) * (g : G)⁻¹ := by
                rw [← Subgroup.mem_centralizer_singleton_iff.mp hy.1]
          _ = ((g : G) * y) * (B.b 1 * (g : G)⁻¹) := by group
          _ = ((g : G) * y) * ((g : G)⁻¹ * B.b 1) := by
                rw [hg1.symm.inv_right.eq]
          _ = ((g : G) * y * (g : G)⁻¹) * B.b 1 := by group
      · have hgN : (g : G) ∈ Subgroup.normalizer (K : Set G) := hKnorm hgC0
        exact (Subgroup.mem_normalizer_iff.mp hgN y).mp hy.2
    have hMmap : M.map (MulAut.conj (g : G)).toMonoidHom ≤ M := by
      change (⁅C, C⁆ : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom ≤ ⁅C, C⁆
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hCmap hCmap
    have hmM' : (g : G) * (m : G) * (g : G)⁻¹ ∈ M :=
      hMmap (Subgroup.mem_map.mpr ⟨(m : G), hmM, rfl⟩)
    have hmCen : (g : G) * (m : G) * (g : G)⁻¹ ∈ cen (B.b 0 * B.b 1) :=
      (cen (B.b 0 * B.b 1)).mul_mem
        ((cen (B.b 0 * B.b 1)).mul_mem g.2 m.2) ((cen (B.b 0 * B.b 1)).inv_mem g.2)
    refine mem_img_iff.mpr ⟨⟨_, hmCen⟩, hmM', ?_⟩
    rw [← hgq]
    have hsub : (⟨(g : G) * (m : G) * (g : G)⁻¹, hmCen⟩ : ↥(cen (B.b 0 * B.b 1))) =
        (⟨(g : G), g.2⟩ : ↥(cen (B.b 0 * B.b 1))) * ⟨(m : G), m.2⟩ *
          (⟨(g : G), g.2⟩ : ↥(cen (B.b 0 * B.b 1)))⁻¹ := rfl
    rw [hsub, map_mul, map_mul, map_inv]
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_⟩
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hconj q hq x, fun hx => by
    have h := hconj q⁻¹ (inv_mem hq) _ hx
    simpa [mul_assoc] using h⟩

end CFSG.StandardType.FrameRoute.FS81
