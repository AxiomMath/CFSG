module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModelAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
open QuadraticMap Module CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.RankThree.OrthogonalInvolutions
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthBlk
  CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open scoped Matrix commutatorElement

private theorem commute_zpowers_nineJ {G : Type} [Group G] {K : Subgroup G} {b : G} :
    ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ nineJ K b, Commute x y := by
  intro x hx y hy
  unfold nineJ at hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hyb : Commute y b := Subgroup.mem_centralizer_singleton_iff.mp
    ((Subgroup.commutator_le_self _).trans inf_le_right hy)
  exact (hyb.zpow_right k).symm

private theorem inf_centralizer_le_zpowers_sup_nineJ {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    K ⊓ Subgroup.centralizer ({B.b 2} : Set G) ≤
      Subgroup.zpowers (B.b 2) ⊔ nineJ K (B.b 2) := by
  classical
  obtain ⟨φ, B', F, j, hB', hjinj, hj, heven, hU, hφB'⟩ :=
    exists_frame_coordinates_of_recOutTwD5 hstd hB hrec
  let i₂ : Fin 5 := 1
  let a : G := B.b i₂.succ
  have haK : a ∈ K := hB.2.2 _ (Fin.succ_ne_zero i₂)
  let x : ↥(orthDerived Q5) := φ ⟨a, haK⟩
  have hxval := phi_eq_or_eq_inv_frameRot hB' hj hφB' i₂ haK
  obtain ⟨hx3, hxU, hxfix⟩ := frameRot_facts_of_eq_or_eq_inv F (j i₂) hxval
  have hQ5 : (polarBilin Q5).Nondegenerate := nondegenerate_Q5
  have hUnd : PolarNondegOn Q5 (F.U (j i₂)) := fun u hu huv =>
    F.nondeg (j i₂) u hu fun v hv => by
      rw [polar_comm]
      exact huv v hv
  have hU2 : finrank (ZMod 2) (F.U (j i₂)) = 2 := hU (j i₂)
  have hUc : IsCompl (F.U (j i₂)) (perpOf Q5 (F.U (j i₂))) := isCompl_perp hUnd
  have hdimV : finrank (ZMod 2) V5 = 10 := by
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  have hdimW : finrank (ZMod 2) (perpOf Q5 (F.U (j i₂))) = 8 := by
    have := Submodule.finrank_add_eq_of_isCompl hUc
    rw [hU2, hdimV] at this
    omega
  have hP : (polarBilin (Q5.restrict (perpOf Q5 (F.U (j i₂))))).Nondegenerate :=
    perp_polarBilin_nondegenerate hQ5 hUnd
  have hT : ∃ T : Submodule (ZMod 2) (perpOf Q5 (F.U (j i₂))), finrank (ZMod 2) T = 3 ∧
      ∀ u ∈ T, (Q5.restrict (perpOf Q5 (F.U (j i₂)))) u = 0 :=
    perp_exists_ts_three hQ5 hUnd (by simp [hdimW])
  have hW6 : 6 ≤ finrank (ZMod 2) (perpOf Q5 (F.U (j i₂))) := by simp [hdimW]
  have hdec := (centralizer_decomp_of_plane_commutator (Q := Q5) (U := F.U (j i₂))
    hQ5 hUc hU2 hP hW6 hT
    (x := ((x : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5))
    (show ((x : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) ∈ orthDerived Q5 from x.2)
    hx3 hxU hxfix).1
  let Ck : Subgroup ↥K := Subgroup.centralizer ({⟨a, haK⟩} : Set ↥K)
  let Cl : Subgroup ↥(orthDerived Q5) := Subgroup.centralizer ({x} : Set ↥(orthDerived Q5))
  have hK : K ⊓ Subgroup.centralizer ({a} : Set G) = Ck.map K.subtype :=
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.map_subtype_centralizer_singleton
      K ⟨a, haK⟩).symm
  have hφ : Ck.map φ.toMonoidHom = Cl :=
    CFSG.RankThree.PartTwo.map_centralizer_singleton φ ⟨a, haK⟩
  have hL : orthDerived Q5 ⊓ Subgroup.centralizer
      ({(x : V5 ≃ₗ[ZMod 2] V5)} : Set (V5 ≃ₗ[ZMod 2] V5)) =
      Cl.map (orthDerived Q5).subtype :=
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.map_subtype_centralizer_singleton
      (orthDerived Q5) x).symm
  have hJ : nineJ K a = (⁅Ck, Ck⁆).map K.subtype := by
    unfold nineJ
    rw [Subgroup.map_commutator, hK]
  have hφJ : (⁅Ck, Ck⁆).map φ.toMonoidHom = ⁅Cl, Cl⁆ := by
    rw [Subgroup.map_commutator, hφ]
  have hCl : Cl ≤ Subgroup.zpowers x ⊔ ⁅Cl, Cl⁆ := by
    have hdec' := hdec
    rw [hL, ← Subgroup.map_commutator] at hdec'
    have hdec'' : Subgroup.map (orthDerived Q5).subtype Cl ≤
        (Subgroup.zpowers x ⊔ ⁅Cl, Cl⁆).map (orthDerived Q5).subtype := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      exact hdec'
    exact (Subgroup.map_le_map_iff_of_injective (orthDerived Q5).subtype_injective).mp hdec''
  have hCk : Ck ≤ Subgroup.zpowers (⟨a, haK⟩ : ↥K) ⊔ ⁅Ck, Ck⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := φ.toMonoidHom) φ.injective]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hφJ, hφ]
    exact hCl
  intro y hy
  have hy' : y ∈ K ⊓ Subgroup.centralizer ({a} : Set G) := hy
  rw [hK] at hy'
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
  rw [← hzy]
  have hz' : (z : G) ∈ (Subgroup.zpowers (⟨a, haK⟩ : ↥K) ⊔ ⁅Ck, Ck⁆).map K.subtype :=
    Subgroup.mem_map.mpr ⟨z, hCk hz, rfl⟩
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← hJ] at hz'
  exact hz'

theorem inf_centralizer_eq_zpowers_sup_nineJ {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    K ⊓ Subgroup.centralizer ({B.b 2} : Set G) = Subgroup.zpowers (B.b 2) ⊔ nineJ K (B.b 2) := by
  refine le_antisymm (inf_centralizer_le_zpowers_sup_nineJ hstd hB hrec) ?_
  have haK : B.b 2 ∈ K := hB.2.2 2 (by decide)
  refine sup_le (fun y hy => ?_) (fun y hy => ?_)
  · exact Subgroup.mem_inf.mpr ⟨Subgroup.zpowers_le.mpr haK hy,
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hy⟩
  · unfold nineJ at hy
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.commutator_le_self _).trans inf_le_left hy,
      (Subgroup.commutator_le_self _).trans inf_le_right hy⟩

theorem commutator_nineJ_eq_self {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    ⁅nineJ K (B.b 2), nineJ K (B.b 2)⁆ = nineJ K (B.b 2) := by
  classical
  have hsimple := nineJ_simple_of_recOutTwD5 hstd hB hrec
  have hmap : (⁅(⊤ : Subgroup ↥(nineJ K (B.b 2))),
        (⊤ : Subgroup ↥(nineJ K (B.b 2)))⁆).map (nineJ K (B.b 2)).subtype =
      ⁅nineJ K (B.b 2), nineJ K (B.b 2)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rcases hsimple.eq_bot_or_eq_top_of_normal
    (⁅(⊤ : Subgroup ↥(nineJ K (B.b 2))), (⊤ : Subgroup ↥(nineJ K (B.b 2)))⁆) with hbot | htop'
  · have hJbot : ⁅nineJ K (B.b 2), nineJ K (B.b 2)⁆ = ⊥ := by
      rw [← hmap, hbot, Subgroup.map_bot]
    have hcommJ : IsMulCommutative ↥(nineJ K (B.b 2)) :=
      Subgroup.commutator_self_eq_bot_iff.mp hJbot
    have hdec := inf_centralizer_eq_zpowers_sup_nineJ hstd hB hrec
    have hcommAJ := commute_zpowers_nineJ (K := K) (b := B.b 2)
    have hCcomm : IsMulCommutative ↥(K ⊓ Subgroup.centralizer ({B.b 2} : Set G)) := by
      refine IsMulCommutative.of_comm (fun x y => Subtype.ext ?_)
      have hx' : (x : G) ∈ Subgroup.zpowers (B.b 2) ⊔ nineJ K (B.b 2) := by
        rw [← hdec]
        exact x.2
      have hy' : (y : G) ∈ Subgroup.zpowers (B.b 2) ⊔ nineJ K (B.b 2) := by
        rw [← hdec]
        exact y.2
      obtain ⟨xm, hxm, xj, hxj, hxy⟩ := (CFSG.mem_sup_of_commute hcommAJ).mp hx'
      obtain ⟨ym, hym, yj, hyj, hyy⟩ := (CFSG.mem_sup_of_commute hcommAJ).mp hy'
      change (x : G) * (y : G) = (y : G) * (x : G)
      rw [← hxy, ← hyy]
      have h1 : Commute xm ym := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxm
        obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hym
        exact (Commute.refl (B.b 2)).zpow_zpow k l
      have h2 : Commute xm yj := hcommAJ xm hxm yj hyj
      have h3 : Commute xj ym := (hcommAJ ym hym xj hxj).symm
      have h4 : Commute xj yj :=
        congrArg Subtype.val (hcommJ.is_comm.comm ⟨xj, hxj⟩ ⟨yj, hyj⟩)
      exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
    have hCbot : ⁅K ⊓ Subgroup.centralizer ({B.b 2} : Set G),
        K ⊓ Subgroup.centralizer ({B.b 2} : Set G)⁆ = ⊥ :=
      Subgroup.commutator_self_eq_bot_iff.mpr hCcomm
    have hJbot' : nineJ K (B.b 2) = ⊥ := by
      unfold nineJ
      exact hCbot
    exact absurd hJbot' ((Subgroup.nontrivial_iff_ne_bot _).mp hsimple.toNontrivial)
  · rw [← hmap, htop', Subgroup.map_top, Subgroup.range_subtype]

theorem three_dvd_card_nineJ {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    3 ∣ Nat.card ↥(nineJ K (B.b 2)) := by
  classical
  have ha3 : (B.b 2) ^ 3 = 1 := by
    rw [← B.ord 2]
    exact pow_orderOf_eq_one _
  have hb33 : (B.b 3) ^ 3 = 1 := by
    rw [← B.ord 3]
    exact pow_orderOf_eq_one _
  have hb3ne : B.b 3 ≠ 1 := by
    intro h
    have hord := B.ord 3
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hb3_not : B.b 3 ∉ Subgroup.zpowers (B.b 2) := by
    intro hmem
    rw [mem_zpowers_iff_mem_range_orderOf, show orderOf (B.b 2) = 3 from B.ord 2] at hmem
    obtain ⟨n, hn, hna⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_range] at hn
    interval_cases n
    · rw [pow_zero] at hna
      exact hb3ne hna.symm
    · rw [pow_one] at hna
      exact (Basis3.b_ne_b_ne_inv B (by decide : (2 : Fin 6) ≠ 3)).1 hna
    · have h2 : (B.b 2) ^ 2 = (B.b 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, show (2 + 1 : ℕ) = 3 by norm_num, ha3]
      have hinv : (B.b 3)⁻¹ = B.b 2 := by
        rw [← hna, h2, inv_inv]
      exact (Basis3.b_ne_b_ne_inv B (by decide : (2 : Fin 6) ≠ 3)).2 hinv.symm
  have hdec := inf_centralizer_eq_zpowers_sup_nineJ hstd hB hrec
  have hb3 : B.b 3 ∈ K ⊓ Subgroup.centralizer ({B.b 2} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hB.2.2 3 (by decide), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (B.comm 3 2).eq
  have hcomm := commute_zpowers_nineJ (K := K) (b := B.b 2)
  rw [hdec] at hb3
  obtain ⟨x, hx, j, hjJ, hxj⟩ := (CFSG.mem_sup_of_commute hcomm).mp hb3
  have hx3 : x ^ 3 = 1 := by
    have h := orderOf_dvd_of_mem_zpowers hx
    rw [B.ord 2] at h
    exact (orderOf_dvd_iff_pow_eq_one).mp h
  have hcommxb : Commute x (B.b 3) := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (B.comm 2 3).zpow_left k
  have hjeq : j = x⁻¹ * B.b 3 := by
    rw [← hxj]
    group
  have hj3 : j ^ 3 = 1 := by
    rw [hjeq, Commute.mul_pow hcommxb.inv_left, inv_pow, hx3, hb33, inv_one, one_mul]
  have hjne : j ≠ 1 := by
    intro h
    have hb3x : B.b 3 = x := by rw [← hxj, h, mul_one]
    exact hb3_not (hb3x.symm ▸ hx)
  have hordj : orderOf j = 3 := orderOf_eq_prime hj3 hjne
  have hdvd : orderOf j ∣ Nat.card ↥(nineJ K (B.b 2)) :=
    Subgroup.orderOf_dvd_natCard _ hjJ
  rwa [hordj] at hdvd

theorem center_nineJ_eq_bot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) :
    Subgroup.center ↥(nineJ K (B.b 2)) = ⊥ := by
  classical
  have hsimple := nineJ_simple_of_recOutTwD5 hstd hB hrec
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(nineJ K (B.b 2))) with h | h
  · exact h
  · have hcomm : IsMulCommutative ↥(nineJ K (B.b 2)) := Subgroup.center_eq_top_iff.mp h
    have hJbot : ⁅nineJ K (B.b 2), nineJ K (B.b 2)⁆ = ⊥ :=
      Subgroup.commutator_self_eq_bot_iff.mpr hcomm
    rw [commutator_nineJ_eq_self hstd hB hrec] at hJbot
    exact absurd hJbot ((Subgroup.nontrivial_iff_ne_bot _).mp hsimple.toNontrivial)

end CFSG.StandardType.FrameRoute.FS81

end
