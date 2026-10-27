module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Weak
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Offender
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Coxeter

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}

omit [Finite G] in
private theorem conjMatHom_acts {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) (x : ↥(Subgroup.normalizer (E : Set G))) :
    B.Acts (x : G) ((conjMatHom hB x : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  rw [conjMatHom_apply]
  exact B.acts_matOf (fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe B.span (normalizerToBspan hB x) y)

theorem conjMatHom_ker {G : Type} [Group G] [Finite G] {B : Basis3 G (5 + 1)} {b₀ : G}
    {K E : Subgroup G} (hB : Adapted B b₀ K E) :
    (conjMatHom hB).ker =
      (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hyS : y ∈ B.span := by rwa [hB.1]
    have hxS : (x : G) ∈ Subgroup.normalizer (B.span : Set G) := by
      rw [hB.1]
      exact x.2
    have hacts := conjMatHom_acts hB x
    have h1 : (x : G) * y * (x : G)⁻¹ =
        B.vec (((conjMatHom hB x : GL (Fin 6) (ZMod 3)) :
          Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ B.coords ⟨y, hyS⟩) := by
      have h := B.acts_vec' hxS hacts (B.coords ⟨y, hyS⟩)
      rwa [B.vec_coords] at h
    rw [hx] at h1
    have h1' : (x : G) * y * (x : G)⁻¹ = y := by
      simpa [B.vec_coords, Matrix.one_mulVec] using h1
    have h2 : (x : G) * y = y * (x : G) := by
      calc (x : G) * y = (x : G) * y * (x : G)⁻¹ * (x : G) := by group
        _ = y * (x : G) := by rw [h1']
    exact h2.symm
  · intro hx
    apply Units.ext
    change ((conjMatHom hB x : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) = 1
    rw [conjMatHom_apply]
    refine B.matOf_eq_of_acts (g := (x : G)) (fun y => ?_) ?_
    · exact Subgroup.normalizerMonoidHom_apply_apply_coe B.span (normalizerToBspan hB x) y
    · intro j
      rw [show (fun i => (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) i j) = Pi.single j 1 from by
        funext i
        simp [Matrix.one_apply, Pi.single_apply]]
      rw [B.vec_single]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx (B.b j) (by
        rw [← hB.1]; exact B.b_mem_span j)).symm
      calc (x : G) * B.b j * (x : G)⁻¹ = B.b j * (x : G) * (x : G)⁻¹ := by rw [hcomm]
        _ = B.b j := by group

omit [Finite G] in
private theorem coords_fixed_of_conjMatHom {B : Basis3 G (5 + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) {F : Subgroup G}
    (a : ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)))
    {M : GL (Fin 6) (ZMod 3)}
    (hM : M ∈ (F.subgroupOf (Subgroup.normalizer (E : Set G))).map (conjMatHom hB)) :
    M *ᵥ B.coords ⟨a.1, hB.1.symm ▸ a.2.1.1⟩ =
      B.coords ⟨a.1, hB.1.symm ▸ a.2.1.1⟩ := by
  set v : Coords 6 := B.coords ⟨a.1, hB.1.symm ▸ a.2.1.1⟩ with hvdef
  change M *ᵥ v = v
  have hv : B.vec v = a.1 := B.vec_coords _
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hM
  have hxF : (y : G) ∈ F := Subgroup.mem_subgroupOf.mp hy
  have hcomm := Subgroup.mem_centralizer_iff.mp a.2.2 (y : G) hxF
  have hconj : (y : G) * a.1 * (y : G)⁻¹ = a.1 := by
    calc (y : G) * a.1 * (y : G)⁻¹ = a.1 * (y : G) * (y : G)⁻¹ := by rw [hcomm.symm]
      _ = a.1 := by group
  have hyS : (y : G) ∈ Subgroup.normalizer (B.span : Set G) := by
    rw [hB.1]
    exact y.2
  have hacts := conjMatHom_acts hB y
  have h1 : (y : G) * B.vec v * (y : G)⁻¹ =
      B.vec (((conjMatHom hB y : GL (Fin 6) (ZMod 3)) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) :=
    B.acts_vec' hyS hacts v
  have h2 : B.vec (((conjMatHom hB y : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = a.1 := by
    calc B.vec (((conjMatHom hB y : GL (Fin 6) (ZMod 3)) :
          Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v)
        = (y : G) * B.vec v * (y : G)⁻¹ := h1.symm
      _ = (y : G) * a.1 * (y : G)⁻¹ := by rw [hv]
      _ = a.1 := hconj
  exact B.vec_injective (by
    have h3 : B.vec (((conjMatHom hB y : GL (Fin 6) (ZMod 3)) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = B.vec v := by rw [h2, hv]
    simpa using h3)

omit [Finite G] in
private theorem card_centralizer_le_card_fixed_of_conjMatHom {B : Basis3 G (5 + 1)} {b₀ : G}
    {K E : Subgroup G} (hB : Adapted B b₀ K E) {F : Subgroup G}
    (hord : orderOf b₀ = 3) (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K)) :
    Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) ≤
      Nat.card {v : Coords 6 // v 0 = 0 ∧
        ∀ a ∈ (F.subgroupOf (Subgroup.normalizer (E : Set G))).map (conjMatHom hB),
          ((a : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} := by
  have hdisj' : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := by rwa [hB.1]
  let vOf : ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) → Coords 6 := fun a =>
    B.coords ⟨a.1, hB.1.symm ▸ a.2.1.1⟩
  have hvOf : ∀ a, B.vec (vOf a) = a.1 := fun a => B.vec_coords _
  let Φ : ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) →
      {v : Coords 6 // v 0 = 0 ∧
        ∀ a ∈ (F.subgroupOf (Subgroup.normalizer (E : Set G))).map (conjMatHom hB),
          ((a : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} :=
    fun a => ⟨vOf a,
      B.coords_zero_of_mem hB.2.1 hord hB.2.2 hdisj'
        ⟨a.1, hB.1.symm ▸ a.2.1.1⟩ a.2.1.2,
      by
        intro M hM
        exact coords_fixed_of_conjMatHom hB a hM⟩
  refine Nat.card_le_card_of_injective Φ ?_
  intro a b hab
  apply Subtype.ext
  have hv : vOf a = vOf b := congrArg Subtype.val hab
  have h1 : a.1 = b.1 := by
    have := congrArg B.vec hv
    rwa [hvOf a, hvOf b] at this
  exact h1

theorem eq_E_of_le_normalizer_of_oE6
    {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hfus : Fus42 B b₀) (hX : (ggAutomizer ⊤ B.span).map B.glHom = oE6 1)
    (hw : ∀ A ∈ oE6 1, A ^ 3 = 1 → A ∈ wE6 1) {F : Subgroup G}
    (hFN : F ≤ Subgroup.normalizer (E : Set G)) (hF : IsElemAbelian 3 F)
    (hFc : Nat.card F = Nat.card E) : F = E := by
  classical
  have hstd' : StdTwD5 b₀ K E := hstd
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -, hEmax, -, -, -⟩ := hhyp
  obtain ⟨hdisj, hsup, -, hEKcard, hCK⟩ := hcanon
  have hOut : ¬ 3 ∣ Nat.card (Outer K) := not_three_dvd_card_outer_of_isTwD5 hKmark hKz
  have hnorm : ¬ (Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
    rw [← hB.1]
    exact hfus.1
  have hord : orderOf b₀ = 3 := hb₀
  have hEA : Nat.card E = 3 * Nat.card ↥(E ⊓ K) := card_E_eq_three_mul_card_inf_of_std hstd'
  let N := Subgroup.normalizer (E : Set G)
  let C := Subgroup.centralizer (E : Set G)
  let Fbar : Subgroup (GL (Fin 6) (ZMod 3)) := (F.subgroupOf N).map (conjMatHom hB)
  have hrange : (conjMatHom hB).range = (ggAutomizer ⊤ B.span).map B.glHom := by
    rw [conjMatHom, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (normalizerToBspan_surjective hB), Subgroup.map_top,
      normalizerMonoidHom_range_eq_ggAutomizer]
  have hFbar_le : Fbar ≤ oE6 1 := by
    refine (Subgroup.map_le_range (conjMatHom hB) (F.subgroupOf N)).trans ?_
    rw [hrange, hX]
  have hFbar_el : IsElemAbelian 3 Fbar := (hF.subgroupOf N).map (conjMatHom hB)
  have hFbar_w : Fbar ≤ wE6 1 := fun A hA =>
    hw A (hFbar_le hA) (hFbar_el.2 A hA)
  have hFCE : F ⊓ C ≤ E := by
    intro f hf
    have hf3 : f ^ 3 ^ 1 = 1 := by
      rw [pow_one]
      exact hF.2 f hf.1
    exact fs81_three_elem_mem_E hb₀ hKC hKn hOut hA2 hsup hCK hEmax.2.1 hnorm hf.2 hf3
  let fF : ↥F →* GL (Fin 6) (ZMod 3) := (conjMatHom hB).comp (Subgroup.inclusion hFN)
  have hfFker : fF.ker = (F ⊓ C).subgroupOf F := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, conjMatHom_ker hB]
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  have hindex : (F ⊓ C).relIndex F = Nat.card fF.range := by
    rw [← Subgroup.index_ker fF, hfFker]
    rfl
  have hrangeF : fF.range = Fbar := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hcardF : Nat.card F = Nat.card Fbar * Nat.card ↥(F ⊓ C) := by
    have h := Subgroup.relIndex_mul_card (F ⊓ C) F
    have hinf : (F ⊓ C) ⊓ F = F ⊓ C := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, hx.1⟩
    rw [hinf] at h
    rw [hindex, hrangeF] at h
    exact h.symm
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h2 : Nat.card ↥(F ⊓ C) ≤
      Nat.card ↥(E ⊓ Subgroup.centralizer (F : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hFCE hx, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => hFcomm y hy x hx.1
  have h3 : Nat.card ↥(E ⊓ Subgroup.centralizer (F : Set G)) ≤
      3 * Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) := by
    have h4 := Subgroup.relIndex_mul_card (E ⊓ K) (E ⊓ Subgroup.centralizer (F : Set G))
    have h5 : E ⊓ K ⊓ (E ⊓ Subgroup.centralizer (F : Set G)) =
        E ⊓ K ⊓ Subgroup.centralizer (F : Set G) := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · intro hx
        exact ⟨hx.1, hx.2.2⟩
      · intro hx
        exact ⟨hx.1, hx.1.1, hx.2⟩
    have h6 := Subgroup.relIndex_mul_card (E ⊓ K) E
    have hEKE : E ⊓ K ⊓ E = E ⊓ K := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, hx.1⟩
    rw [hEKE, hEA] at h6
    have h7 : (E ⊓ K).relIndex E = 3 :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (h6.trans (by ring))
    have h8 : (E ⊓ K).relIndex (E ⊓ Subgroup.centralizer (F : Set G)) ≤ 3 := by
      rw [← h7]
      exact Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h7]; norm_num)
    rw [h5] at h4
    rw [← h4]
    exact Nat.mul_le_mul_right _ h8
  have hcardfix := card_centralizer_le_card_fixed_of_conjMatHom hB hord hdisj (F := F)
  by_cases hbot : Fbar = ⊥
  · have hFC : F ≤ C := by
      intro y hy
      have hy1 : conjMatHom hB ⟨y, hFN hy⟩ = 1 := by
        have hmem : conjMatHom hB ⟨y, hFN hy⟩ ∈ Fbar :=
          Subgroup.mem_map.mpr ⟨⟨y, hFN hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hyker : ⟨y, hFN hy⟩ ∈ (conjMatHom hB).ker := hy1
      rw [conjMatHom_ker hB, Subgroup.mem_subgroupOf] at hyker
      exact hyker
    have hFE : F ≤ E := fun y hy => hFCE ⟨hy, hFC hy⟩
    exact Subgroup.eq_of_le_of_card_ge hFE hFc.ge
  · exfalso
    have hnoff := wE6_noOffender (Or.inl rfl) (card_wE6_dvd (Or.inl rfl)) hFbar_w hFbar_el hbot
    have hlt : Nat.card F < Nat.card E := by
      calc Nat.card F = Nat.card Fbar * Nat.card ↥(F ⊓ C) := hcardF
        _ ≤ Nat.card Fbar *
            (3 * Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G))) :=
            Nat.mul_le_mul_left _ (h2.trans h3)
        _ = 3 * (Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) *
            Nat.card Fbar) := by ring
        _ ≤ 3 * (Nat.card {v : Coords 6 // v 0 = 0 ∧
            ∀ a ∈ Fbar, ((a : GL (Fin 6) (ZMod 3)) :
              Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} * Nat.card Fbar) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcardfix)
        _ < 3 * 3 ^ 5 := Nat.mul_lt_mul_of_pos_left hnoff (by norm_num)
        _ = Nat.card E := by rw [hEA, hEKcard]
    omega

theorem le_normalizer_of_eq_E {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E)
    (huniq : ∀ F : Subgroup G, F ≤ Subgroup.normalizer (E : Set G) → IsElemAbelian 3 F →
      Nat.card F = Nat.card E → F = E)
    {R : Subgroup G} (hR : IsPGroup 3 R) (hER : E ≤ R) : R ≤ Subgroup.normalizer (E : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hRN
  let N := Subgroup.normalizer (E : Set G)
  have hEC : E ≤ Subgroup.centralizer (E : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hEN : E ≤ N := hEC.trans (Subgroup.centralizer_le_normalizer (E : Set G))
  have hR₀E : E ≤ R ⊓ N := le_inf hER hEN
  have hne : R ⊓ N ≠ R := by
    intro h
    exact hRN (h ▸ inf_le_right)
  have hlt : (R ⊓ N).subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hne (le_antisymm inf_le_left (Subgroup.subgroupOf_eq_top.mp htop))
  have hnil : Group.IsNilpotent ↥R := hR.isNilpotent
  obtain ⟨x, hxN, hxS⟩ :=
    SetLike.exists_of_lt
      ((Group.normalizerCondition_of_isNilpotent (G := ↥R)) ((R ⊓ N).subgroupOf R) hlt)
  have hxR : (x : G) ∈ R := x.2
  have hconjN : conjSubgroup (x : G) E ≤ N := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    have hs : x⁻¹ * y * x ∈ E := hy
    have hs₀ : x⁻¹ * y * x ∈ R ⊓ N := hR₀E hs
    have hsR : x⁻¹ * y * x ∈ R := hs₀.1
    have hmem := (Subgroup.mem_normalizer_iff.mp hxN ⟨x⁻¹ * y * x, hsR⟩).mp
      (Subgroup.mem_subgroupOf.mpr hs₀)
    have hval : (((x * ⟨x⁻¹ * y * x, hsR⟩ * x⁻¹ : ↥R) : R) : G) = y := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hyN : (((x * ⟨x⁻¹ * y * x, hsR⟩ * x⁻¹ : ↥R) : R) : G) ∈ N :=
      (Subgroup.mem_subgroupOf.mp hmem).2
    rwa [hval] at hyN
  have hEq : conjSubgroup (x : G) E = E :=
    huniq (conjSubgroup (x : G) E) hconjN
      (hE.map (MulAut.conj (x : G)).toMonoidHom)
      (Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective)
  have hxNE : (x : G) ∈ N := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hEq
  exact hxS (Subgroup.mem_subgroupOf.mpr ⟨hxR, hxNE⟩)

theorem le_normalizer_of_isPGroup_of_oE6
    {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hfus : Fus42 B b₀)
    (hX : (ggAutomizer ⊤ B.span).map B.glHom = oE6 1)
    (hw : ∀ A ∈ oE6 1, A ^ 3 = 1 → A ∈ wE6 1) {R : Subgroup G} (hR : IsPGroup 3 R)
    (hER : E ≤ R) : R ≤ Subgroup.normalizer (E : Set G) := by
  have hstd' : StdTwD5 b₀ K E := hstd
  obtain ⟨-, hhyp, -⟩ := hstd
  obtain ⟨-, -, -, -, -, -, -, -, hEmax, -, -, -⟩ := hhyp
  exact le_normalizer_of_eq_E hEmax.2.1
    (fun F hFN hF hFc => eq_E_of_le_normalizer_of_oE6 hstd' hB hfus hX hw hFN hF hFc)
    hR hER

end CFSG.StandardType.FrameRoute.FS81

end
