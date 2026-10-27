module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.Milestones.ASVolI.I1Cohomology
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas
import CFSG.Adapters.LieModelSimple
import CFSG.Blueprint.LieModelAPI
import CFSG.Quasithin.EmptyFaithful.S153QPC1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped commutatorElement

theorem uc22p22d_charP_two {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hF])

theorem uc22p22d_isL2_of_statedSL {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ n) (e : X ≃* ↥(StatedSL 2 F)) : IsL2 X n := by
  haveI : CharP F 2 := uc22p22d_charP_two (by omega) hF
  have hZ := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := F)
  let g : StatedProj (StatedSL 2 F) ≃* StatedSL 2 F :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance,
    inferInstance, hF, ⟨e.trans g.symm⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem uc22p22d_isL2_of_omegaMinus4 {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ k) (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* ↥(StatedOmega (StatedQuadMinus 2 F b c))) : IsL2 X (2 * k) := by
  haveI : CharP F 2 := uc22p22d_charP_two hk hF
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨F', _, _, ω, hrank, hω⟩ := CFSG.ASVolI.burnsideI16h_exists_quad_ext hbc
  haveI : Module.Finite F F' := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  haveI : Finite F' := Module.finite_of_finite F
  letI : Fintype F' := Fintype.ofFinite F'
  haveI : CharP F' 2 := charP_of_injective_algebraMap (algebraMap F F').injective 2
  have hK : Fintype.card F = 2 ^ k := by rw [← Nat.card_eq_fintype_card, hF]
  let S : CFSG.ASVolI.burnsideI16h_Setup F F' := ⟨k, b, c, hk, hK, ω, hω, hbc, hrank⟩
  have hF' : Nat.card F' = 2 ^ (2 * k) := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := F'), hrank, hF]
    ring
  exact uc22p22d_isL2_of_statedSL (by omega) hF'
    ((e.trans (CFSG.ASVolI.burnsideI16h_θ S)).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F'))

theorem uc22p22d_comm_mem_of_index_two {Γ : Type} [Group Γ] {N : Subgroup Γ} [N.Normal]
    (h : N.index = 2) (x y : Γ) : ⁅x, y⁆ ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (Γ ⧸ N) = 2 := by rw [← Subgroup.index_eq_card]; exact h
  haveI : IsCyclic (Γ ⧸ N) := isCyclic_of_prime_card hcard
  have h1 : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (IsMulCommutative.is_comm.comm _ _)
  exact (QuotientGroup.eq_one_iff _).1 h1

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell in
theorem uc22p22d_omegaPlus4_equiv {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) :
    Nonempty ((Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) ≃*
      ↥(StatedOmega (StatedQuadPlus 2 F))) := by
  have hle1 : (jProd (F := F)).range ≤ StatedOmega (StatedQuadPlus 2 F) := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [jProd_apply]
    exact mul_mem (j1_mem_omega h4 a) (j2_mem_omega h4 b)
  have hle2 : StatedOmega (StatedQuadPlus 2 F) ≤ (jProd (F := F)).range := by
    have hidx : ((jProd (F := F)).range.subgroupOf
        (CFSG.LieType.BorelTits.orthGroup (StatedQuadPlus 2 F))).index = 2 := relIndex_jProd_range
    haveI hN : ((jProd (F := F)).range.subgroupOf
        (CFSG.LieType.BorelTits.orthGroup (StatedQuadPlus 2 F))).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have := uc22p22d_comm_mem_of_index_two hidx ⟨x, hx⟩ ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  exact ⟨(MonoidHom.ofInjective jProd_injective).trans
    (MulEquiv.subgroupCongr (le_antisymm hle1 hle2))⟩

theorem uc22p22d_equiv_of_proj {X Y : Type} [Group X] [Group Y] {C : Subgroup X} (f : X →* Y)
    (hinj : ∀ c ∈ C, ∀ c' ∈ C, f c = f c' → c = c') (hsurj : ∀ y, ∃ c ∈ C, f c = y) :
    Nonempty (↥C ≃* Y) :=
  ⟨MulEquiv.ofBijective (f.comp C.subtype)
    ⟨fun a b h => Subtype.ext (hinj a a.2 b b.2 h), fun y => by
      obtain ⟨c, hc, hcy⟩ := hsurj y
      exact ⟨⟨c, hc⟩, hcy⟩⟩⟩

theorem uc22p22d_prod {A B : Type} [Group A] [Group B] (hA : IsSimpleGroup A) (hB : IsSimpleGroup B)
    (hAn : ∃ a b : A, a * b ≠ b * a) (hBn : ∃ a b : B, a * b ≠ b * a)
    {C : Subgroup (A × B)} (hsub : C.IsSubnormal) (hq : CFSG.Open.IsQuasisimple ↥C) :
    Nonempty (↥C ≃* A) ∨ Nonempty (↥C ≃* B) := by
  haveI hCnt : Nontrivial ↥C := uc22p22a_qs_nontrivial hq
  have hsurj1 : Function.Surjective (MonoidHom.fst A B) := fun a => ⟨(a, 1), rfl⟩
  have hsurj2 : Function.Surjective (MonoidHom.snd A B) := fun b => ⟨(1, b), rfl⟩
  have h1 := Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hA (hsub.map hsurj1)
  have h2 := Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hB (hsub.map hsurj2)
  have hbot1 : C.map (MonoidHom.fst A B) = ⊥ → ∀ c ∈ C, c.1 = 1 := by
    intro h c hc
    have : c.1 ∈ C.map (MonoidHom.fst A B) := ⟨c, hc, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have hbot2 : C.map (MonoidHom.snd A B) = ⊥ → ∀ c ∈ C, c.2 = 1 := by
    intro h c hc
    have : c.2 ∈ C.map (MonoidHom.snd A B) := ⟨c, hc, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have htop1 : C.map (MonoidHom.fst A B) = ⊤ → ∀ a : A, ∃ c ∈ C, c.1 = a := by
    intro h a
    have : a ∈ C.map (MonoidHom.fst A B) := by rw [h]; trivial
    obtain ⟨c, hc, hca⟩ := this
    exact ⟨c, hc, hca⟩
  have htop2 : C.map (MonoidHom.snd A B) = ⊤ → ∀ b : B, ∃ c ∈ C, c.2 = b := by
    intro h b
    have : b ∈ C.map (MonoidHom.snd A B) := by rw [h]; trivial
    obtain ⟨c, hc, hcb⟩ := this
    exact ⟨c, hc, hcb⟩
  rcases h2 with h2 | h2
  · rcases h1 with h1 | h1
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥C)
      apply hx
      apply Subtype.ext
      exact Prod.ext (hbot1 h1 x x.2) (hbot2 h2 x x.2)
    · refine Or.inl (uc22p22d_equiv_of_proj (MonoidHom.fst A B) ?_ (htop1 h1))
      intro c hc c' hc' h
      exact Prod.ext h (by rw [hbot2 h2 c hc, hbot2 h2 c' hc'])
  · rcases h1 with h1 | h1
    · refine Or.inr (uc22p22d_equiv_of_proj (MonoidHom.snd A B) ?_ (htop2 h2))
      intro c hc c' hc' h
      exact Prod.ext (by rw [hbot1 h1 c hc, hbot1 h1 c' hc']) h
    · have hfst : ∀ a : A, ∃ b : B, (a, b) ∈ C := fun a => by
        obtain ⟨c, hc, hca⟩ := htop1 h1 a
        exact ⟨c.2, by rw [← hca]; exact hc⟩
      have hsnd : ∀ b : B, ∃ a : A, (a, b) ∈ C := fun b => by
        obtain ⟨c, hc, hcb⟩ := htop2 h2 b
        exact ⟨c.1, by rw [← hcb]; exact hc⟩
      let CA : Subgroup A := C.comap (MonoidHom.inl A B)
      let CB : Subgroup B := C.comap (MonoidHom.inr A B)
      have hCAn : CA.Normal := ⟨fun a ha a' => by
        obtain ⟨b', hb'⟩ := hfst a'
        have := C.mul_mem (C.mul_mem hb' ha) (C.inv_mem hb')
        simpa [CA] using this⟩
      have hCBn : CB.Normal := ⟨fun b hb b' => by
        obtain ⟨a', ha'⟩ := hsnd b'
        have := C.mul_mem (C.mul_mem ha' hb) (C.inv_mem ha')
        simpa [CB] using this⟩
      haveI := hCAn
      haveI := hCBn
      rcases hA.eq_bot_or_eq_top_of_normal CA with hCA | hCA
      · refine Or.inr (uc22p22d_equiv_of_proj (MonoidHom.snd A B) ?_ (htop2 h2))
        intro c hc c' hc' h
        have hmem : (c * c'⁻¹ : A × B) ∈ C := C.mul_mem hc (C.inv_mem hc')
        have hfst' : c.1 * c'.1⁻¹ ∈ CA := by
          have h2' : (c * c'⁻¹ : A × B) = (c.1 * c'.1⁻¹, 1) := by
            refine Prod.ext rfl ?_
            have : c.2 = c'.2 := h
            simp [this]
          rw [h2'] at hmem
          exact hmem
        rw [hCA, Subgroup.mem_bot, mul_inv_eq_one] at hfst'
        exact Prod.ext hfst' h
      · rcases hB.eq_bot_or_eq_top_of_normal CB with hCB | hCB
        · refine Or.inl (uc22p22d_equiv_of_proj (MonoidHom.fst A B) ?_ (htop1 h1))
          intro c hc c' hc' h
          have hmem : (c * c'⁻¹ : A × B) ∈ C := C.mul_mem hc (C.inv_mem hc')
          have hsnd' : c.2 * c'.2⁻¹ ∈ CB := by
            have h2' : (c * c'⁻¹ : A × B) = (1, c.2 * c'.2⁻¹) := by
              refine Prod.ext ?_ rfl
              have : c.1 = c'.1 := h
              simp [this]
            rw [h2'] at hmem
            exact hmem
          rw [hCB, Subgroup.mem_bot, mul_inv_eq_one] at hsnd'
          exact Prod.ext h hsnd'
        · exfalso
          have hAin : ∀ a : A, (a, (1 : B)) ∈ C := fun a => by
            have : a ∈ CA := by rw [hCA]; trivial
            exact this
          have hBin : ∀ b : B, ((1 : A), b) ∈ C := fun b => by
            have : b ∈ CB := by rw [hCB]; trivial
            exact this
          let W : Subgroup ↥C := ((MonoidHom.snd A B).comp C.subtype).ker
          haveI hWn : W.Normal := MonoidHom.normal_ker _
          rcases uc22p22a_qs_normal hq hWn with hW | hW
          · obtain ⟨a, a', haa⟩ := hAn
            have hm1 : (⟨(a, 1), hAin a⟩ : ↥C) ∈ W := by simp [W]
            have hc := Subgroup.mem_center_iff.1 (hW hm1) ⟨(a', 1), hAin a'⟩
            apply haa
            have := congrArg (fun x : ↥C => (x : A × B).1) hc
            simpa using this.symm
          · obtain ⟨b, b', hbb⟩ := hBn
            have hx : (⟨((1 : A), b), hBin b⟩ : ↥C) ∈ W ⊔ Subgroup.center ↥C := by
              rw [hW]; trivial
            obtain ⟨w, hw, z, hz, hwz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
            have hw2 : (w : A × B).2 = 1 := by simpa [W] using hw
            have hz2 : (z : A × B).2 = b := by
              have := congrArg (fun x : ↥C => (x : A × B).2) hwz
              simpa [hw2] using this
            have hc := Subgroup.mem_center_iff.1 hz ⟨(1, b'), hBin b'⟩
            apply hbb
            have := congrArg (fun x : ↥C => (x : A × B).2) hc
            simp only [Subgroup.coe_mul, Prod.snd_mul] at this
            rw [hz2] at this
            exact this.symm

theorem uc22p22d_noncomm_of_perfect {A : Type} [Group A] [Nontrivial A] (hp : commutator A = ⊤) :
    ∃ a b : A, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative A := ⟨⟨fun a b => hcon a b⟩⟩
  have h1 : commutator A = ⊥ := (commutator_eq_bot_iff A).2 inferInstance
  rw [hp] at h1
  exact top_ne_bot h1

theorem uc22p22d_isL2_of_natOmegaMinus4 {H : Type} [Group H] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W) {L : Subgroup H}
    {A B : Submodule (ZMod 2) W} {k : ℕ} (hk : 1 ≤ k) (h : NatOmegaMinus4 ρ L A B k) :
    IsL2 ↥L (2 * k) := by
  obtain ⟨F, _, _, hF, b, c, hbc, -, -, -, φ, -⟩ := h
  exact uc22p22d_isL2_of_omegaMinus4 hk hF b c hbc φ

theorem uc22p22d_isL2_of_concl {H : Type} [Group H] [Finite H] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) H W) {L : Subgroup H} {n : ℕ}
    (hn : 2 ≤ n) (hL : CFSG.Open.IsComponentOf L ⊤) (h : uc22br4_K147Concl ρ L n) :
    IsL2 ↥L n := by
  rcases h with ⟨-, h⟩ | h
  · rcases h with hnat | ⟨k, hk, hs⟩ | ⟨h3, hL2, -⟩
    · obtain ⟨F, _, _, hF, -, -, -, φ, -⟩ := hnat
      exact uc22p22d_isL2_of_statedSL hn hF φ
    · subst hk
      have hk1 : 1 ≤ k := by omega
      rcases hs with hs | hs
      · obtain ⟨Ai, hAi, -⟩ := hs
        exact uc22p22d_isL2_of_natOmegaMinus4 ρ hk1 (hAi 0).2.2
      · obtain ⟨Ai, hAi, -⟩ := hs
        exact uc22p22d_isL2_of_natOmegaMinus4 ρ hk1 (hAi 0).2.2
    · subst h3
      exact hL2
  · obtain ⟨F, _, _, hF, -, -, -, φ, -⟩ := h
    haveI : CharP F 2 := uc22p22d_charP_two (by omega) hF
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨ψ⟩ := uc22p22d_omegaPlus4_equiv h4
    have hsimp := CFSG.Quasithin.QP.sl2_isSimpleGroup h4
    have hqs : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4
    haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := hsimp.toNontrivial
    obtain ⟨a, b, hab⟩ := uc22p22d_noncomm_of_perfect (Group.isPerfect_def.1 hqs.1)
    set X : Subgroup H := lgConj L
    have hLX : L ≤ X := by
      refine le_trans (le_of_eq ?_) (le_iSup (fun g : H => L.map (MulAut.conj g).toMonoidHom) 1)
      ext x
      simp
    have hsubX : (L.subgroupOf X).IsSubnormal :=
      (CFSG.Open.IsSubnormal.top_iff.1 hL.2.1).subgroupOf
    let e : ↥X ≃* (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) :=
      φ.trans ψ.symm
    let C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) :=
      (L.subgroupOf X).map e.toMonoidHom
    have hCsub : C.IsSubnormal := hsubX.map e.surjective
    let eL : ↥L ≃* ↥C :=
      (Subgroup.subgroupOfEquivOfLe hLX).symm.trans
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)
    have hCq : CFSG.Open.IsQuasisimple ↥C := CFSG.Open.IsQuasisimple.of_mulEquiv eL.symm hL.2.2
    rcases uc22p22d_prod hsimp hsimp ⟨a, b, hab⟩ ⟨a, b, hab⟩ hCsub hCq with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact uc22p22d_isL2_of_statedSL hn hF
        ((eL.trans f).trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))
    · exact uc22p22d_isL2_of_statedSL hn hF
        ((eL.trans f).trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))

@[expose] def uc22p22d_J1Nontrivial : Prop :=
  ∀ (X : Type) [Group X], IsJ1 X → Nontrivial X

theorem uc22p22d_nontrivial {G : Type} [Group G] [Finite G] {D : Data G} {Ch : Choice2011 G}
    (hJ1 : uc22p22d_J1Nontrivial) {c : Ctx22b D Ch} {p : ℕ} {K : Subgroup G} {n : ℕ}
    (hK : K2213 D c p K n) : Nontrivial ↥(mbarImage D.M c.V K) := by
  rcases hK.2.2 with ⟨hsp, -⟩ | ⟨hsu, -⟩ | ⟨h3, -⟩ | ⟨-, h4, -⟩
  · exact (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp).toNontrivial
  · exact uc22p22a_qs_nontrivial hsu.1
  · rcases h3 with ⟨-, hL | hS⟩ | ⟨hJ, -⟩
    · exact (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL).toNontrivial
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 _
        (CFSG.Blueprint.LieModel.twistedB2_iff.1 hS).2).1
    · exact hJ1 _ hJ
  · rcases h4 with hU | hL
    · exact (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU).toNontrivial
    · exact (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL).toNontrivial

section Case147

variable {G : Type} [Group G] [Finite G]

theorem uc22p22d_lgConj_of_normal {M K : Subgroup G} (V : Subgroup G) (hKM : K ≤ M)
    (hnorm : (K.subgroupOf M).Normal) : lgConj (mbarImage M V K) = mbarImage M V K :=
  uc22br4_lgConj_mbarImage_of_normal M V K hKM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hnorm)

theorem uc22p22d_isSU3_of_isU3 {X : Type} [Group X] {n : ℕ} (hq : CFSG.Open.IsQuasisimple X)
    (hU : IsU3 X n) : IsSU3 X n := by
  have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
  haveI := hs
  haveI := uc22p22a_qs_nontrivial hq
  have hc : Subgroup.center X = ⊥ :=
    uc22p22a_center_eq_bot (uc22p22d_noncomm_of_perfect hq.1)
  exact ⟨hq, CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm hU⟩

theorem uc22p22d_isL2_of_case147 (hK147 : K147) (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch)
    (hred : TwoReduced D.M c.V) (hel : CFSG.Open.IsElemAbelian 2 c.V) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKV : ¬ K ≤ centralizer (c.V : Set G)) {n : ℕ} (hn2 : 2 ≤ n)
    (hcase : Case147 (mbarImage D.M c.V K) n) (h9 : ¬ MBarGT D.M ⊥ c.V (c.n + 1))
    (hn : c.n ≤ n) : IsL2 ↥(mbarImage D.M c.V K) n := by
  have hgt : ¬ MBarGT D.M ⊥ c.V (n + 1) := fun h =>
    h9 (uc22br4_mBarGT_mono D.M ⊥ c.V h (by omega))
  obtain ⟨Vmod, i1, i2, i3, e, ρ, hc', hconcl⟩ :=
    uc22br4_k147_exists hK147 D c.hVM hel c.hVne c.hVirr hred hK hKV hcase hgt
  have hpc : CFSG.pCore 2 (MBar D.M c.V) = ⊥ := (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 hred
  exact uc22p22d_isL2_of_concl ρ hn2
    (uc22br4_isComponentOf_mbarImage D.M c.V K c.hVM hpc hK hKV) hconcl

end Case147

section Pair

variable {G : Type} [Group G] [Finite G]

theorem uc22p22d_mbarImage_ne (M V : Subgroup G) {K K' : Subgroup G} (hK : K ∈ calC M)
    (hK' : K' ∈ CFSG.Quasithin.cComp M) (hne : K ≠ K') (hnt : mbarImage M V K ≠ ⊥) :
    mbarImage M V K ≠ mbarImage M V K' := by
  intro heq
  have hKM : K ≤ M := uc22p22a_le_of_isSubnormal hK.1
  have hK'M : K' ≤ M := CFSG.Quasithin.le_of_mem_cComp hK'
  have hcomm : ⁅K, K'⁆ ≤ CFSG.Quasithin.solvRad M :=
    uc22p20e_comm_le_solvRad (uc22p20e_cComp_of_calC hK) hK' hne
  set π : ↥M →* MBar M V := QuotientGroup.mk' (kerAct M V).normalCore
  have hperf : ⁅K.subgroupOf M, K.subgroupOf M⁆ = K.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKM, hK.2.1]
  have hcomm' : ⁅K.subgroupOf M, K'.subgroupOf M⁆ ≤ (CFSG.Quasithin.solvRad M).subgroupOf M := by
    show _ ≤ Subgroup.comap M.subtype _
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hKM, Subgroup.map_subgroupOf_eq_of_le hK'M]
    exact hcomm
  haveI := CFSG.Quasithin.solvRad_isSolvable M
  haveI hRs : Group.IsSolvable ↥((CFSG.Quasithin.solvRad M).subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (CFSG.Quasithin.solvRad_le M)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (CFSG.Quasithin.solvRad_le M)).injective
  haveI hRb : Group.IsSolvable ↥(((CFSG.Quasithin.solvRad M).subgroupOf M).map π) :=
    Group.isSolvable_of_surjective
      (MonoidHom.subgroupMap_surjective π ((CFSG.Quasithin.solvRad M).subgroupOf M))
  have hKbar : ⁅mbarImage M V K, mbarImage M V K⁆ = mbarImage M V K := by
    unfold mbarImage
    rw [← Subgroup.map_commutator, hperf]
  have hle : mbarImage M V K ≤ ((CFSG.Quasithin.solvRad M).subgroupOf M).map π := by
    calc mbarImage M V K = ⁅mbarImage M V K, mbarImage M V K⁆ := hKbar.symm
      _ = ⁅mbarImage M V K, mbarImage M V K'⁆ := by rw [← heq]
      _ ≤ _ := by
        unfold mbarImage
        rw [← Subgroup.map_commutator]
        exact Subgroup.map_mono hcomm'
  haveI : Group.IsSolvable ↥(mbarImage M V K) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥(mbarImage M V K) := Subgroup.isPerfect_iff.2 hKbar
  haveI : Nontrivial ↥(mbarImage M V K) := (Subgroup.nontrivial_iff_ne_bot _).2 hnt
  exact Group.IsPerfect.not_isSolvable ↥(mbarImage M V K) inferInstance

theorem uc22p22d_conjSet_pair {M K : Subgroup G} {t : G} (ht : t ∈ M)
    (hne : K.map (MulAut.conj t).toMonoidHom ≠ K) (hcard : (conjSetOf M K).ncard = 2) :
    conjSetOf M K = {K, K.map (MulAut.conj t).toMonoidHom} := by
  have hsub : ({K, K.map (MulAut.conj t).toMonoidHom} : Set (Subgroup G)) ⊆ conjSetOf M K := by
    rintro X (rfl | rfl)
    · exact ⟨1, M.one_mem, by ext x; simp⟩
    · exact ⟨t, ht, rfl⟩
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, Set.ncard_pair hne.symm])
    (Set.toFinite _)).symm

theorem uc22p22d_conjClosure_pair {M K : Subgroup G} {t : G} (ht : t ∈ M)
    (hne : K.map (MulAut.conj t).toMonoidHom ≠ K) (hcard : (conjSetOf M K).ncard = 2) :
    conjClosure M K = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
  unfold conjClosure
  rw [uc22p22d_conjSet_pair ht hne hcard, iSup_pair]

end Pair

section Split

variable {H : Type} [Group H] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem uc22p22d_apply_commOn_le (ρ : Representation (ZMod 2) H W) (L : Subgroup H) (h : H) {x : W}
    (hx : x ∈ commOn ρ L ⊤) : ρ h x ∈ commOn ρ (L.map (MulAut.conj h).toMonoidHom) ⊤ := by
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, ha, u, -, rfl⟩ := hw
    have : ρ h (ρ a u - u) = ρ (h * a * h⁻¹) (ρ h u) - ρ h u := by
      rw [rep_conj_apply, map_sub]
    rw [this]
    have hm : h * a * h⁻¹ ∈ L.map (MulAut.conj h).toMonoidHom :=
      ⟨a, ha, by simp [MulAut.conj_apply]⟩
    exact sub_mem_commOn hm Submodule.mem_top
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem uc22p22d_map_conj_map_conj (L : Subgroup H) (g h : H) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      L.map (MulAut.conj (h * g)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by group⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g * z * g⁻¹, ⟨z, hz, rfl⟩, by group⟩

theorem uc22p22d_inv_dichotomy {ρ : Representation (ZMod 2) H W} (hirr : ρ.IsIrreducible)
    (S : Submodule (ZMod 2) W) (hS : ∀ h : H, ∀ x ∈ S, ρ h x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, fun g v hv => hS g v hv⟩ : Subrepresentation ρ) with
    h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

theorem uc22p22d_split (ρ : Representation (ZMod 2) H W) (hirr : ρ.IsIrreducible)
    (hfaith : Function.Injective ρ) {L : Subgroup H} (hL : L ≠ ⊥) (g : H)
    (hne : L.map (MulAut.conj g).toMonoidHom ≠ L)
    (hconj : ∀ h : H, L.map (MulAut.conj h).toMonoidHom = L ∨
      L.map (MulAut.conj h).toMonoidHom = L.map (MulAut.conj g).toMonoidHom)
    (hfix : commOn ρ L ⊤ ≤ fixSub ρ (L.map (MulAut.conj g).toMonoidHom)) :
    commOn ρ L ⊤ ⊔ commOn ρ (L.map (MulAut.conj g).toMonoidHom) ⊤ = ⊤ ∧
      commOn ρ L ⊤ ⊓ commOn ρ (L.map (MulAut.conj g).toMonoidHom) ⊤ = ⊥ := by
  set L' := L.map (MulAut.conj g).toMonoidHom
  have hinj : ∀ h : H, Function.Injective (Subgroup.map (MulAut.conj h).toMonoidHom) := fun h =>
    Subgroup.map_injective (MulAut.conj h).injective
  have hact : ∀ h : H, (L.map (MulAut.conj h).toMonoidHom = L ∧
        L'.map (MulAut.conj h).toMonoidHom = L') ∨
      (L.map (MulAut.conj h).toMonoidHom = L' ∧ L'.map (MulAut.conj h).toMonoidHom = L) := by
    intro h
    have h2 : L'.map (MulAut.conj h).toMonoidHom = L.map (MulAut.conj (h * g)).toMonoidHom :=
      uc22p22d_map_conj_map_conj L g h
    rcases hconj h with h1 | h1
    · refine Or.inl ⟨h1, ?_⟩
      rcases hconj (h * g) with h3 | h3
      · exact absurd (hinj h (by rw [h2, h3, h1])) hne.symm
      · rw [h2, h3]
    · refine Or.inr ⟨h1, ?_⟩
      rcases hconj (h * g) with h3 | h3
      · rw [h2, h3]
      · exact absurd (hinj h (by rw [h2, h3, h1])) hne.symm
  have hW : ∀ h : H, ∀ x ∈ commOn ρ L ⊤, ρ h x ∈ commOn ρ (L.map (MulAut.conj h).toMonoidHom) ⊤ :=
    fun h x hx => uc22p22d_apply_commOn_le ρ L h hx
  have hW' : ∀ h : H, ∀ x ∈ commOn ρ L' ⊤,
      ρ h x ∈ commOn ρ (L'.map (MulAut.conj h).toMonoidHom) ⊤ :=
    fun h x hx => uc22p22d_apply_commOn_le ρ L' h hx
  have hWne : commOn ρ L ⊤ ≠ ⊥ := by
    intro hW0
    apply hL
    rw [eq_bot_iff]
    intro a ha
    have h1 : ρ a = 1 := by
      refine LinearMap.ext fun u => ?_
      have hmem : ρ a u - u ∈ commOn ρ L ⊤ := sub_mem_commOn ha Submodule.mem_top
      rw [hW0, Submodule.mem_bot, sub_eq_zero] at hmem
      simpa using hmem
    have h2 : a = 1 := hfaith (h1.trans (map_one ρ).symm)
    rw [h2]
    exact Subgroup.one_mem _
  refine ⟨?_, ?_⟩
  · have hS : ∀ h : H, ∀ x ∈ commOn ρ L ⊤ ⊔ commOn ρ L' ⊤,
        ρ h x ∈ commOn ρ L ⊤ ⊔ commOn ρ L' ⊤ := by
      intro h x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      rcases hact h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy' := hW h y hy
        have hz' := hW' h z hz
        rw [h1] at hy'
        rw [h2] at hz'
        exact Submodule.add_mem_sup hy' hz'
      · have hy' := hW h y hy
        have hz' := hW' h z hz
        rw [h1] at hy'
        rw [h2] at hz'
        rw [add_comm]
        exact Submodule.add_mem_sup hz' hy'
    rcases uc22p22d_inv_dichotomy hirr _ hS with h | h
    · exact absurd (eq_bot_iff.2 (le_sup_left.trans h.le)) hWne
    · exact h
  · have hS : ∀ h : H, ∀ x ∈ commOn ρ L ⊤ ⊓ commOn ρ L' ⊤,
        ρ h x ∈ commOn ρ L ⊤ ⊓ commOn ρ L' ⊤ := by
      intro h x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hy' := hW h x hx1
      have hz' := hW' h x hx2
      rcases hact h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hy'
        rw [h2] at hz'
        exact ⟨hy', hz'⟩
      · rw [h1] at hy'
        rw [h2] at hz'
        exact ⟨hz', hy'⟩
    rcases uc22p22d_inv_dichotomy hirr _ hS with h | h
    · exact h
    · exfalso
      have hWtop : commOn ρ L ⊤ = ⊤ := eq_top_iff.2 (h.ge.trans inf_le_left)
      have hall : ∀ a ∈ L', ρ a = 1 := by
        intro a ha
        refine LinearMap.ext fun u => ?_
        have hu : u ∈ commOn ρ L ⊤ := by
          rw [hWtop]
          exact Submodule.mem_top
        have := hfix hu a ha
        simpa using this
      apply hL
      have hL'bot : L' = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        have h2 : a = 1 := hfaith ((hall a ha).trans (map_one ρ).symm)
        rw [h2]
        exact Subgroup.one_mem _
      exact (Subgroup.map_eq_bot_iff_of_injective L
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).1 hL'bot

end Split

end CFSG.LocalAnalysis.UniquenessCase.UC22
