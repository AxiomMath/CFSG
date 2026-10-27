module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl4tf_map_conj_one {T : Type*} [Group T] (X : Subgroup T) :
    X.map (MulAut.conj (1 : T)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map, MulAut.conj_apply]

private theorem s16h_sl4tf_map_conj_mul {T : Type*} [Group T] (X : Subgroup T) (x y : T) :
    (X.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      X.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext t
  simp [MulAut.conj_apply, mul_assoc]

private theorem s16h_sl4tf_exists_conj_eq {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {φ : MulAut (Vtil V₀ V hV)}
    (hφ : φ ∈ Mbar D.M V₀ V hV) :
    ∃ m : G, m ∈ D.M ∧ barSub V₀ V hV (conjSubgroup L m) =
      (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom := by
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hgm : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil _ _).inv_mem g.2
  have hgt : actTil V₀ V hV ⟨(g : G)⁻¹, hgm⟩ = (actTil V₀ V hV g)⁻¹ := by
    rw [show (⟨(g : G)⁻¹, hgm⟩ : stabTil V₀ V) = ⟨g, g.2⟩⁻¹ from rfl, map_inv]
  refine ⟨(g : G)⁻¹, D.M.inv_mem hgM, ?_⟩
  rw [← hgφ, s15_Infra_barSub_conjSubgroup V₀ V hV hgm L]
  congr 1
  rw [hgt, inv_inv]

private theorem s16h_sl4tf_relIndex_stabilizer_eq_two {T : Type*} [Group T]
    {X K : Subgroup (MulAut T)} {x₁ : MulAut T} (hx₁ : x₁ ∈ X)
    (hx₁K : K.map (MulAut.conj x₁).toMonoidHom ≠ K)
    (huniq : ∀ a ∈ X, ∀ b ∈ X, K.map (MulAut.conj a).toMonoidHom ≠ K →
      K.map (MulAut.conj b).toMonoidHom ≠ K →
        K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj b).toMonoidHom) :
    ((X ⊓ Subgroup.normalizer (K : Set (MulAut T))).subgroupOf X).index = 2 := by
  set K' := K.map (MulAut.conj x₁).toMonoidHom with hK'
  have hmemA : ∀ b : X, b ∈ (X ⊓ Subgroup.normalizer (K : Set (MulAut T))).subgroupOf X ↔
      K.map (MulAut.conj (b : MulAut T)).toMonoidHom = K := fun b => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => (Subgroup.mem_normalizer_iff_map_conj_eq).1 h.2,
      fun h => ⟨b.2, (Subgroup.mem_normalizer_iff_map_conj_eq).2 h⟩⟩
  have hinj : ∀ (b : MulAut T) (A₁ A₂ : Subgroup (MulAut T)),
      A₁.map (MulAut.conj b).toMonoidHom = A₂.map (MulAut.conj b).toMonoidHom → A₁ = A₂ :=
    fun b _ _ h => Subgroup.map_injective (MulAut.conj b).injective h
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x₁, hx₁⟩, fun b => xor_iff_iff_not.mpr ⟨fun hbg hb => ?_, fun hb => ?_⟩⟩
  · rw [hmemA, Subgroup.coe_mul, ← s16h_sl4tf_map_conj_mul] at hbg
    rw [hmemA] at hb
    exact hx₁K (hinj b K' K (hbg.trans hb.symm))
  · rw [hmemA] at hb
    rw [hmemA, Subgroup.coe_mul, ← s16h_sl4tf_map_conj_mul]
    by_contra hne
    have h1 := huniq _ (X.mul_mem b.2 hx₁) _ b.2
      (by rw [← s16h_sl4tf_map_conj_mul]; exact hne) hb
    rw [← s16h_sl4tf_map_conj_mul] at h1
    exact hx₁K (hinj b K' K h1)

theorem s16h_sl4_two_frame_of_setting (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) :
    ∃ L' : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      L' ≠ lBar ⊥ V h.hyp151.isElemAbelian L ∧
      s16h_SL4TwoFrame (Mbar D.M ⊥ V h.hyp151.isElemAbelian)
        (lBar ⊥ V h.hyp151.isElemAbelian L) L'
        (barSub ⊥ V h.hyp151.isElemAbelian D.T) := by
  classical
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨x0, y0, hxy0, hSxy0⟩ := Set.ncard_eq_two.1 hs2
  have hAS : lBar ⊥ V hV L ∈ {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV,
        X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} :=
    ⟨1, (Mbar D.M ⊥ V hV).one_mem, (s16h_sl4tf_map_conj_one _).symm⟩
  have hSxy' : {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV,
        X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = {x0, y0} := hSxy0
  rw [hSxy'] at hAS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hAS
  obtain ⟨B, hBA, hSAB⟩ : ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)),
      B ≠ lBar ⊥ V hV L ∧
      {X : Subgroup (MulAut (Vtil ⊥ V hV)) | ∃ φ ∈ Mbar D.M ⊥ V hV,
        X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} =
        {lBar ⊥ V hV L, B} := by
    rcases hAS with h1 | h1
    · exact ⟨y0, fun hy => hxy0 (h1.symm.trans hy.symm), by rw [hSxy', h1]⟩
    · exact ⟨x0, fun hx => hxy0 (hx.trans h1), by rw [hSxy', h1, Set.pair_comm]⟩
  have hBS : B ∈ {X : Subgroup (MulAut (Vtil ⊥ V hV)) | ∃ φ ∈ Mbar D.M ⊥ V hV,
      X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} := by
    rw [hSAB]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨ψ, hψM, hBψ⟩ := hBS
  have hAB : (lBar ⊥ V hV L).map (MulAut.conj ψ).toMonoidHom = B := hBψ.symm
  have hpairH : ∀ φ ∈ Mbar D.M ⊥ V hV,
      (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom = lBar ⊥ V hV L ∨
        (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom = B := by
    intro φ hφ
    have hmem : (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom ∈
        {X : Subgroup (MulAut (Vtil ⊥ V hV)) | ∃ θ ∈ Mbar D.M ⊥ V hV,
          X = (lBar ⊥ V hV L).map (MulAut.conj θ).toMonoidHom} := ⟨φ, hφ, rfl⟩
    rw [hSAB] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  obtain ⟨m₀, hm₀M, hKm₀⟩ := s16h_sl4tf_exists_conj_eq (V₀ := ⊥) h.hyp151 hV hψM
  have hKB : barSub ⊥ V hV (conjSubgroup L m₀) = B := hKm₀.trans hAB
  have hne1 : m₀ * (1 : G)⁻¹ ∉ nBar D.M ⊥ V hV L := by
    intro hmem
    have := (s15_Infra_mul_inv_mem_nBar_iff (L := L) h.hyp151.hyp125 hV D.M.one_mem hm₀M).1 hmem
    rw [conjSubgroup_one, hKB] at this
    exact hBA this
  have hc1 : ⁅lBar ⊥ V hV L, B⁆ = ⊥ ∧
      commSub (commSub ⊤ (lBar ⊥ V hV L)) B = ⊥ := by
    have := s15_Kbar_commute_conj h.hyp151 (m := 1) (m' := m₀) D.M.one_mem hm₀M hne1
    rwa [conjSubgroup_one, hKB] at this
  have hcomm : ∀ a ∈ lBar ⊥ V hV L, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc1.1
    exact ((Subgroup.mem_centralizer_iff.1 (hcent ha)) b hb).symm
  have hTsylOf : CFSG.ABGLocalTools.IsSylowOf 2
      (barSub ⊥ V hV D.T) (Mbar D.M ⊥ V hV) :=
    s16c7_isSylowOf_barSub (p := 2) ⊥ V hV D.sylowM hMs
  have hTsyl := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 hTsylOf
  have hidx : ((Mbar D.M ⊥ V hV ⊓
      Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV)))).subgroupOf
        (Mbar D.M ⊥ V hV)).index = 2 := by
    refine s16h_sl4tf_relIndex_stabilizer_eq_two (X := Mbar D.M ⊥ V hV)
      (K := lBar ⊥ V hV L) (x₁ := ψ) hψM ?_ ?_
    · rw [hAB]
      exact hBA
    · intro a ha b hb hane hbne
      rcases hpairH a ha with h1 | h1
      · exact absurd h1 hane
      · rcases hpairH b hb with h2 | h2
        · exact absurd h2 hbne
        · rw [h1, h2]
  have ht_exists : ∃ t ∈ barSub ⊥ V hV D.T,
      t ∉ Mbar D.M ⊥ V hV ⊓
        Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
    by_contra hcon
    have hTN : barSub ⊥ V hV D.T ≤ Mbar D.M ⊥ V hV ⊓
        Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
      intro t ht
      by_contra hnt
      exact hcon ⟨t, ht, hnt⟩
    have hNA : Mbar D.M ⊥ V hV ⊓
        Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) ≤
        Mbar D.M ⊥ V hV := inf_le_left
    have hmul := Subgroup.relIndex_mul_relIndex (barSub ⊥ V hV D.T)
      (Mbar D.M ⊥ V hV ⊓
        Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))))
      (Mbar D.M ⊥ V hV) hTN hNA
    have hNrel : (Mbar D.M ⊥ V hV ⊓
        Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV)))).relIndex
          (Mbar D.M ⊥ V hV) = 2 := hidx
    have hdvd : 2 ∣ (barSub ⊥ V hV D.T).relIndex (Mbar D.M ⊥ V hV) := by
      refine ⟨(barSub ⊥ V hV D.T).relIndex (Mbar D.M ⊥ V hV ⊓
        Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV)))), ?_⟩
      rw [← hmul, hNrel]
      exact mul_comm _ 2
    exact hTsyl.2.2 hdvd
  obtain ⟨t, htT, htN⟩ := ht_exists
  have htA : t ∈ Mbar D.M ⊥ V hV := hTsyl.1 htT
  have htnorm : t ∉ Subgroup.normalizer
      (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
    intro htn
    exact htN (Subgroup.mem_inf.2 ⟨htA, htn⟩)
  have hHtne : (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom ≠ lBar ⊥ V hV L :=
    fun h => htnorm ((Subgroup.mem_normalizer_iff_map_conj_eq).2 h)
  have hHtB : (lBar ⊥ V hV L).map (MulAut.conj t).toMonoidHom = B := by
    rcases hpairH t htA with h | h
    · exact absurd h hHtne
    · exact h
  have hHle : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV h.hyp151.le
  have hBle : B ≤ Mbar D.M ⊥ V hV := by
    rw [← hAB]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact (Mbar D.M ⊥ V hV).mul_mem
      ((Mbar D.M ⊥ V hV).mul_mem hψM (hHle hy)) ((Mbar D.M ⊥ V hV).inv_mem hψM)
  have hBmap : ∀ φ ∈ Mbar D.M ⊥ V hV,
      B.map (MulAut.conj φ).toMonoidHom = B ∨
        B.map (MulAut.conj φ).toMonoidHom = lBar ⊥ V hV L := by
    intro φ hφ
    have hmem : B.map (MulAut.conj φ).toMonoidHom ∈
        {X : Subgroup (MulAut (Vtil ⊥ V hV)) | ∃ θ ∈ Mbar D.M ⊥ V hV,
          X = (lBar ⊥ V hV L).map (MulAut.conj θ).toMonoidHom} := by
      rw [← hAB, s16h_sl4tf_map_conj_mul]
      exact ⟨φ * ψ, (Mbar D.M ⊥ V hV).mul_mem hφ hψM, rfl⟩
    rw [hSAB] at hmem
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem) with h | h
    · exact Or.inr h
    · exact Or.inl h
  refine ⟨B, hBA, ?_⟩
  refine
    { le_x := hHle
      le_x' := hBle
      t_le := hTsyl.1
      t_two := hTsyl.2.1
      t_syl := hTsyl.2.2
      comm := hcomm
      perm := fun φ hφ => by
        have hinj : Function.Injective
            (Subgroup.map (MulAut.conj φ).toMonoidHom :
              Subgroup (MulAut (Vtil ⊥ V hV)) → Subgroup (MulAut (Vtil ⊥ V hV))) :=
          Subgroup.map_injective (MulAut.conj φ).injective
        rcases hpairH φ hφ with hH | hH
        · rcases hBmap φ hφ with hBm | hBm
          · exact Or.inl ⟨hH, hBm⟩
          · exfalso
            exact hBA (hinj (by rw [hBm, hH]))
        · rcases hBmap φ hφ with hBm | hBm
          · exfalso
            exact hBA (hinj (by rw [hBm, hH]))
          · exact Or.inr ⟨hH, hBm⟩
      swap := ⟨t, htT, hHtB⟩ }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
