module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4Defs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThree

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two9
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrame
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
import CFSG.RankThree.PartOne.K133H.F4Weyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

private theorem l04fHE1_isElemAbelian_top_f4 :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (Fin Tag.F4.rank → ZMod 3))) := by
  refine ⟨inferInstance, fun x _ => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem l04fHE1_card_range_of_injective {G : Type*} [Group G]
    {ι : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* G}
    (hinj : Function.Injective ι) : Nat.card ι.range = 3 ^ 4 := by
  rw [← Subgroup.map_top ι, Subgroup.card_map_of_injective (f := ι) hinj,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  change Fintype.card (Fin 4 → ZMod 3) = 3 ^ 4
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

private theorem l04fHE1_isElemAbelian_frame {K : Type} [Field K] [Finite K]
    (D : ExcFrames.E6QPlusThree.E6QPlusThreeFrame K) :
    IsElemAbelian 3 D.frame.range := by
  have h := CFSG.SectionRank.isElemAbelian_map (f := D.frame)
    (E := ⊤) l04fHE1_isElemAbelian_top_f4
  rwa [MonoidHom.range_eq_map]

private theorem l04fHE1_ref_automizer
    {K : Type} [Field K] [Finite K]
    (D : ExcFrames.E6QPlusThree.E6QPlusThreeFrame K)
    (hsurj : Function.Surjective D.weyl) :
    Nat.card (ggAutomizer ⊤ D.frame.range) = 1152 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero 3 := ⟨by norm_num⟩
  let V := Multiplicative (Fin Tag.F4.rank → ZMod 3)
  let A₀ := D.frame.range
  let e : V ≃* A₀ := MonoidHom.ofInjective D.frame_injective
  let Tor : WeylGroup .F4 →* MulAut V := ExcWeylOuter.torusMulAut .F4 3
  have hTor_inj : Function.Injective Tor :=
    ExcWeylOuter.torusMulAut_injective (τ := .F4) (p := 3) (by norm_num)
  have hTor_apply : ∀ (w : WeylGroup .F4) (v : V), Tor w v =
      Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w (Multiplicative.toAdd v)) :=
    fun w v => ExcWeylOuter.torusMulAut_apply w (Multiplicative.toAdd v)
  have he_apply : ∀ v : V, ((e v : A₀) : adjointGroup .E6 K) = D.frame v :=
    fun v => MonoidHom.ofInjective_apply D.frame_injective
  have hcongr_apply : ∀ (f : MulAut V) (b : A₀),
      ((MulAut.congr e f) b : A₀) = e (f (e.symm b)) := fun f b => rfl
  have hAut : ggAutomizer ⊤ A₀ = Tor.range.map (MulAut.congr e).toMonoidHom := by
    apply le_antisymm
    · intro φ hφ
      rw [mem_ggAutomizer_iff] at hφ
      obtain ⟨g, -, hgN, hφg⟩ := hφ
      let a : D.N := ⟨g, D.mem_N_of_conj g (fun s =>
        (Subgroup.mem_normalizer_iff.1 hgN (D.frame s)).1
          (MonoidHom.mem_range.mpr ⟨s, rfl⟩))⟩
      refine Subgroup.mem_map.mpr ⟨Tor (D.weyl a),
        MonoidHom.mem_range.mpr ⟨D.weyl a, rfl⟩, ?_⟩
      change MulAut.congr e (Tor (D.weyl a)) = φ
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [hcongr_apply (Tor (D.weyl a)) b]
      rw [show ((e ((Tor (D.weyl a)) (e.symm b)) : A₀) : adjointGroup .E6 K) =
          D.frame ((Tor (D.weyl a)) (e.symm b)) from he_apply _]
      rw [hTor_apply (D.weyl a) (e.symm b)]
      rw [hφg b]
      have h2 : (b : adjointGroup .E6 K) = D.frame (e.symm b) := by
        calc (b : adjointGroup .E6 K) = ↑(e (e.symm b)) :=
              congrArg Subtype.val (e.apply_symm_apply b).symm
          _ = D.frame (e.symm b) := he_apply (e.symm b)
      rw [h2]
      exact (D.conj_frame a (Multiplicative.toAdd (e.symm b))).symm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨σ, hσ, rfl⟩ := hy
      rw [MonoidHom.mem_range] at hσ
      obtain ⟨w, rfl⟩ := hσ
      obtain ⟨a, rfl⟩ := hsurj w
      have hnorm : (a : adjointGroup .E6 K) ∈
          Subgroup.normalizer (A₀ : Set (adjointGroup .E6 K)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hx
          refine MonoidHom.mem_range.mpr ⟨Tor (D.weyl a) v, ?_⟩
          rw [hTor_apply (D.weyl a) v]
          exact (D.conj_frame a (Multiplicative.toAdd v)).symm
        · intro hx
          obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hx
          have hu' : D.frame (Multiplicative.ofAdd (Multiplicative.toAdd u)) =
              (a : adjointGroup .E6 K) * x * (a : adjointGroup .E6 K)⁻¹ := hu
          refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd
            (TableBExc.torusAct .F4 3
              (D.weyl ⟨((a : adjointGroup .E6 K))⁻¹, D.N.inv_mem a.2⟩)
              (Multiplicative.toAdd u)), ?_⟩
          rw [← D.conj_frame (⟨((a : adjointGroup .E6 K))⁻¹, D.N.inv_mem a.2⟩ : D.N)
            (Multiplicative.toAdd u), hu']
          group
      have h1 : ggConjAut A₀ hnorm = MulAut.congr e (Tor (D.weyl a)) := by
        apply MulEquiv.ext
        intro b
        apply Subtype.ext
        rw [ggConjAut_apply, hcongr_apply (Tor (D.weyl a)) b]
        rw [show ((e ((Tor (D.weyl a)) (e.symm b)) : A₀) : adjointGroup .E6 K) =
            D.frame ((Tor (D.weyl a)) (e.symm b)) from he_apply _]
        rw [hTor_apply (D.weyl a) (e.symm b)]
        have h2 : (b : adjointGroup .E6 K) = D.frame (e.symm b) := by
          calc (b : adjointGroup .E6 K) = ↑(e (e.symm b)) :=
                congrArg Subtype.val (e.apply_symm_apply b).symm
            _ = D.frame (e.symm b) := he_apply (e.symm b)
        rw [h2]
        exact D.conj_frame a (Multiplicative.toAdd (e.symm b))
      change MulAut.congr e (Tor (D.weyl a)) ∈ ggAutomizer ⊤ A₀
      rw [← h1]
      exact ggConjAut_mem_ggAutomizer (Subgroup.mem_top _) hnorm
  have hcard_range : Nat.card Tor.range = 1152 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hTor_inj).toEquiv,
      CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
  change Nat.card (ggAutomizer ⊤ A₀) = 1152
  rw [hAut, Subgroup.card_map_of_injective (MulAut.congr e).injective, hcard_range]

private theorem l04fHE1_conj {K : Type} [Field K] [Finite K]
    (D : ExcFrames.E6QPlusThree.E6QPlusThreeFrame K)
    {E : Subgroup (adjointGroup .E6 K)} {g : adjointGroup .E6 K}
    (h : E.map (MulAut.conj g).toMonoidHom = D.frame.range) :
    Nat.card (ggAutomizer ⊤ E) = Nat.card (ggAutomizer ⊤ D.frame.range) := by
  have hmap := F4AutWeyl.ggAutomizer_map_eq (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective ⊤ E h
  rw [Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).surjective] at hmap
  rw [hmap, Subgroup.card_map_of_injective (MulAut.congr _).injective]

theorem ggPumpTwExc_autOrderAt_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K + 1) :
    KGA.GGF4AutOrderAt 3 (adjointGroup .E6 K) := by
  intro E hE hr
  obtain ⟨D, hsurj⟩ :=
    ExcFrames.E6QPlusThree.exists_e6QPlusThreeFrame_weyl_surjective (K := K) h3
  have hA₀ : IsElemAbelian 3 D.frame.range := l04fHE1_isElemAbelian_frame D
  have hA₀card : Nat.card D.frame.range = 3 ^ 4 :=
    l04fHE1_card_range_of_injective D.frame_injective
  have hEcard : Nat.card E = 3 ^ 4 :=
    le_antisymm
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two.card_le_of_isElemAbelian_E6_three h3 hE) hr
  refine ⟨hEcard, ?_⟩
  obtain ⟨g, hg⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two.exists_conj_eq_of_card_E6_three
      h3 hE hEcard hA₀ hA₀card
  rw [l04fHE1_conj D hg, l04fHE1_ref_automizer D hsurj]

end CFSG.StandardType

end
