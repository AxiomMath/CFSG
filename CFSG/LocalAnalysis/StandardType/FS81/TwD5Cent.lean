module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Defs
public import CFSG.LocalAnalysis.StandardType.FS81.RowOutTwD7
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

private theorem realized_centralizer_subset_evenFix0_of_recOutTwD5 {G : Type} [Group G] [Finite G]
    {b₀ : G} {B : Basis3 G (5 + 1)} (hb0 : B.b 0 = b₀) (hrec : RecOutTwD5 B b₀) :
    B.realized (Subgroup.centralizer ({b₀} : Set G)) ⊆ evenFix0 5 := by
  intro A hA
  obtain ⟨g, hgC, hActs⟩ := hA
  have hgcomm : g * b₀ = b₀ * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hconj : MulAut.conj g b₀ = b₀ := by
      rw [MulAut.conj_apply, hgcomm, mul_assoc, mul_inv_cancel, mul_one]
    simpa using congrArg Subgroup.zpowers hconj
  have hAall : A ∈ evenAll0 5 := by
    rw [← hrec.2.1]
    exact ⟨g, hgN, hActs⟩
  obtain ⟨σ, s, hsign, hσs, hAeq⟩ := hAall
  obtain ⟨hσ0, hprod⟩ := hσs
  have hcol : (fun i : Fin (5 + 1) => A i 0) =
      Pi.single (0 : Fin (5 + 1)) (s 0) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [hAeq, spMat, hσ0]
    · simp [hAeq, spMat, hσ0, hi]
  have hvec : B.vec (fun i : Fin (5 + 1) => A i 0) = b₀ := by
    rw [← hActs 0, hb0, hgcomm]
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

theorem centralizer_eq_sup_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    Subgroup.centralizer ({b₀} : Set G) =
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) := by
  obtain ⟨_, hHyp, hCanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hcenter, hmark, -⟩ := hHyp
  obtain ⟨-, hsup, hmax, hcard, -⟩ := hCanon
  obtain ⟨_hKs, ⟨φ⟩⟩ :=
    isSimpleGroup_and_mulEquiv_of_isRow_twD (r := 5) (by norm_num) hmark hcenter
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hcenter
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin]
    decide
  refine le_antisymm ?_ (sup_le hKC inf_le_left)
  by_contra hout
  obtain ⟨B', hB', heven, M, hM, hMnot⟩ :=
    exists_basis_not_mem_evenFix0_of_not_le
      (V := Fin 4 ⊕ Fin 4 ⊕ Fin 2 → ZMod 2)
      (Q := CFSG.LieType.Universal.Spin.quadMinus 5 (ZMod 2) 1 1)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 5 (ZMod 2)
        (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0))
      (exists_totallySingular_three_quadMinus (n := 4) (by norm_num))
      h6
      (omegaAutIsometric_quadMinus (n := 4) (by norm_num))
      (n := 5) (by norm_num)
      φ hb₀ hKC hKn hdisj hsup hmax hcard hout
  let C := Subgroup.centralizer ({b₀} : Set G)
  have hsub : B.realized C ⊆ evenFix0 5 :=
    realized_centralizer_subset_evenFix0_of_recOutTwD5 hB.2.1 hrec
  have hcardeq : Nat.card ↥(B.realized C) = Nat.card ↥(B'.realized C) :=
    Basis3.card_realized_eq_of_span_eq (hB.1.trans hB'.1.symm) C
  have hcardeq' : (B.realized C).ncard = (B'.realized C).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hcardeq
  have hle : (B'.realized C).ncard ≤ (evenFix0 5).ncard := by
    rw [← hcardeq']
    exact Set.ncard_le_ncard hsub
  have heq : evenFix0 5 = B'.realized C := Set.eq_of_subset_of_ncard_le heven hle
  rw [← heq] at hM
  exact hMnot hM

theorem centralizer_span_eq_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    Subgroup.centralizer (E : Set G) =
      (E ⊓ K) ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) := by
  have hstd0 : StdTwD5 b₀ K E := hstd
  obtain ⟨_, hHyp, hCanon⟩ := hstd0
  obtain ⟨_, hKC, hKn, _, _, _, _, _, hEmax, _, _, _⟩ := hHyp
  obtain ⟨-, hsup, -, -, hself⟩ := hCanon
  obtain ⟨-, hEelem, -⟩ := hEmax
  let C := Subgroup.centralizer ({b₀} : Set G)
  let D := C ⊓ Subgroup.centralizer (K : Set G)
  have hout : C = K ⊔ D := centralizer_eq_sup_of_recOutTwD5 hstd hB hrec
  have hE_cent : E ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hEelem.1
  have hEK_cent : (E ⊓ K : Subgroup G) ≤ Subgroup.centralizer (E : Set G) :=
    inf_le_left.trans hE_cent
  have hD_C : D ≤ C := inf_le_left
  have hD_CK : D ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  have hD_zp : D ≤ Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hdcomm : Commute d b₀ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hD_C hd)
    exact ((Commute.zpow_right hdcomm m).eq).symm
  have hD_EK : D ≤ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) :=
    hD_CK.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))
  have hD_le_E : D ≤ Subgroup.centralizer (E : Set G) := by
    have hzp : Subgroup.zpowers b₀ ≤ Subgroup.centralizer (D : Set G) :=
      Subgroup.le_centralizer_iff.mp hD_zp
    have hEK : (E ⊓ K : Subgroup G) ≤ Subgroup.centralizer (D : Set G) :=
      Subgroup.le_centralizer_iff.mp hD_EK
    have hsupD : (Subgroup.zpowers b₀ ⊔ (E ⊓ K) : Subgroup G) ≤
        Subgroup.centralizer (D : Set G) := sup_le hzp hEK
    rw [hsup] at hsupD
    exact Subgroup.le_centralizer_iff.mpr hsupD
  refine le_antisymm ?_ ?_
  · intro x hx
    have hb₀E : b₀ ∈ E :=
      hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
    have hxC : x ∈ C :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb₀E) hx
    have hxKD : x ∈ K ⊔ D := by rwa [hout] at hxC
    have hsub : K.subgroupOf C ⊔ D.subgroupOf C = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKC hD_C, ← hout, Subgroup.subgroupOf_self]
    have hx' : (⟨x, hxC⟩ : ↥C) ∈ K.subgroupOf C ⊔ D.subgroupOf C := by
      rw [hsub]
      exact Subgroup.mem_top _
    have hKnormal : (K.subgroupOf C).Normal := hKn
    obtain ⟨k, hk, d, hd, hkd⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
    have hkdG : (k : G) * (d : G) = x := by
      simpa using congrArg Subtype.val hkd
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hdE : (d : G) ∈ Subgroup.centralizer (E : Set G) := hD_le_E hdD
    have hkE : (k : G) ∈ Subgroup.centralizer (E : Set G) := by
      have hk_eq : (k : G) = x * (d : G)⁻¹ := by
        rw [← hkdG]
        group
      rw [hk_eq]
      exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hdE)
    have hk_inf : (k : G) ∈ E ⊓ K := by
      rw [← hself]
      exact ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left) hkE, hkK⟩
    rw [← hkdG]
    exact Subgroup.mul_mem_sup hk_inf hdD
  · intro x hx
    exact sup_le hEK_cent hD_le_E hx

theorem odd_card_centralizer_span_of_odd {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀)
    (hD : Odd (Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)))) :
    Odd (Nat.card ↥(Subgroup.centralizer (E : Set G))) := by
  have hstd0 : StdTwD5 b₀ K E := hstd
  obtain ⟨_, hHyp, hCanon⟩ := hstd0
  obtain ⟨_, _, _, hcenter, _⟩ := hHyp
  obtain ⟨-, -, -, hcard, -⟩ := hCanon
  let D := Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)
  have hcomm : ∀ a ∈ (E ⊓ K : Subgroup G), ∀ b ∈ D, Commute a b := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2 a ha.2
  have hdisj : ((E ⊓ K : Subgroup G) ⊓ D) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxEK, hxD⟩ := Subgroup.mem_inf.mp hx
    have hxK : x ∈ K := hxEK.2
    have hxCK : x ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.mem_inf.mp hxD).2
    have hxcenter : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxCK (y : G) y.2)
    rw [hcenter, Subgroup.mem_bot] at hxcenter
    exact Subtype.ext_iff.mp hxcenter
  rw [centralizer_span_eq_of_recOutTwD5 hstd hB hrec]
  rw [CFSG.card_sup_eq_mul_of_commute (E ⊓ K) D hcomm hdisj, hcard]
  exact (Odd.pow (n := 5) (by decide : Odd 3)).mul hD

end CFSG.StandardType.FrameRoute.FS81

end
