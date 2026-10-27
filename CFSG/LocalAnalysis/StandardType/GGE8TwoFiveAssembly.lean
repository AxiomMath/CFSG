module

public import CFSG.LocalAnalysis.StandardType.GGE8TwoFiveFinite
public import CFSG.LocalAnalysis.StandardType.GGE8TwoFiveKernel
public import CFSG.LocalAnalysis.StandardType.GGE8TwoFiveFiveB
public import CFSG.LocalAnalysis.StandardType.GGE8TwoFiveFiveA
public import CFSG.LocalAnalysis.StandardType.GGExcLangPairAt

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.OmNonsplit CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

private theorem e8f5e_map_centralizer_of_range_eq {G H : Type} [Group G] [Group H] {ι : H →* G}
    (hι : Function.Injective ι) {Γ : Subgroup G} (hr : ι.range = Γ) (a : H) :
    (Subgroup.centralizer {a}).map ι = Γ ⊓ Subgroup.centralizer {ι a} := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨hr ▸ ⟨c, rfl⟩, ?_⟩
    simpa using congrArg ι hc
  · rintro ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ : x ∈ ι.range := hr ▸ hx
    refine ⟨c, ?_, rfl⟩
    exact hι (by simpa using hx')

private theorem e8f5e_exists_setup
    {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E8 L 5) (hq : S.D.q = 2) {ι : E8Two →* ModGL Tag.E8 L}
    (hinj : Function.Injective ι) (hrange : ι.range = S.Γ) {x : E8Two} (hx5 : x ^ 5 = 1)
    (hx1 : x ≠ 1) (hxT : ι x ∈ S.D.torus) :
    ∃ a : Fin Tag.E8.rank → Lˣ, rootDiagUnit Tag.E8 a = ι x ∧ E8TwoFiveSetup S a := by
  obtain ⟨a', ha'⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup
      (mem_twistedTorusOf.1 hxT).1
  have ha'5 : ∀ i, a' i ^ 5 = 1 := by
    have h1 : rootDiagUnit Tag.E8 (a' ^ 5) = rootDiagUnit Tag.E8 (1 : Fin Tag.E8.rank → Lˣ) := by
      have e1 : rootDiagUnit Tag.E8 (a' ^ 5) = rootDiagUnit Tag.E8 a' ^ 5 :=
        (rootDiagUnitHom Tag.E8 L).map_pow a' 5
      have e2 : rootDiagUnit Tag.E8 (1 : Fin Tag.E8.rank → Lˣ) = 1 :=
        (rootDiagUnitHom Tag.E8 L).map_one
      rw [e1, e2, ha', ← map_pow, hx5, map_one]
    have h2 : a' ^ 5 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  refine ⟨a', ha', hq, ha' ▸ hxT, ha' ▸ (hrange ▸ ⟨x, rfl⟩), ha'5, ?_⟩
  rw [ha']
  exact fun h => hx1 (hinj (by rw [h, map_one]))

private theorem e8f5e_kernelA_of_quasisimple
    {L : Type} [Field L] [IsAlgClosed L]
    (S : LangSetup Tag.E8 L 5) {ι : E8Two →* ModGL Tag.E8 L} (hinj : Function.Injective ι)
    (hrange : ι.range = S.Γ) {a : Fin Tag.E8.rank → Lˣ} (hset : E8TwoFiveSetup S a) {y : E8Two}
    (hy : rootDiagUnit Tag.E8 a = ι y) (hy1 : y ≠ 1)
    (hq : IsQuasisimple ↥(Subgroup.centralizer {y})) :
    E8TwoFiveKernelA S.ρ (rootCharHom a) := by
  rcases e8TwoFive_kernelType S hset with hA | hB
  · exact hA
  · exfalso
    obtain ⟨K₀, hK₀⟩ := e8TwoFive_isFiveBIn S hset hB
    have hXc := e8f5e_map_centralizer_of_range_eq hinj hrange y
    rw [hy, ← hXc] at hK₀
    have h' := IsFiveBIn.comap hinj (Subgroup.map_le_range _ _) hK₀
    rw [Subgroup.comap_map_eq_self_of_injective hinj] at h'
    exact (IsFiveB.not_isQuasisimple_centralizer (show IsFiveB y (K₀.comap ι) from h') hy1) hq

theorem e8TwoFive_centralizer_models
    (a : E8Two) (ha5 : orderOf a = 5) :
    (∃ K₀ : Subgroup E8Two, IsFiveB a K₀ ∧ ∃ N : ℕ,
      LieModel (↥K₀ ⧸ Subgroup.center ↥K₀) .POmegaMinus N 2 1) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ 2) ^ 2 ∧
      Nonempty (↥(Subgroup.centralizer {a}) ≃* CFSG.Open.StatedSU 5 (2 ^ 2) F) := by
  classical
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]; norm_num
  have h5 : ¬ 5 ∣ Nat.card (GaloisField 2 1) := by rw [hF]; norm_num
  have ha : a ^ 5 = 1 := by rw [← ha5]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha5
    norm_num at ha5
  obtain ⟨L, hL, hLac, S, ι, hq, -, -, hinj, hrange, haT, -⟩ :=
    CFSG.StandardType.LangPair.langPairAt_E8_five h5 ha ha (Commute.refl a)
  obtain ⟨a', ha', hset⟩ := e8f5e_exists_setup S (by rw [hq, hF]) hinj hrange ha ha1 haT
  have hXc := e8f5e_map_centralizer_of_range_eq hinj hrange a
  have hXc' : (Subgroup.centralizer {a}).map ι =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a'} := by rw [ha']; exact hXc
  rcases e8TwoFive_kernelType S hset with hA | hB
  · right
    obtain ⟨F, _, _, hF, ⟨ε⟩⟩ := e8TwoFive_statedSU_equiv S hset hA
    let η := (Subgroup.equivMapOfInjective (Subgroup.centralizer {a}) ι hinj).trans
      (MulEquiv.subgroupCongr hXc')
    exact ⟨F, inferInstance, inferInstance, hF, ⟨η.trans ε.symm⟩⟩
  · left
    obtain ⟨K₀, hK₀, N, hM⟩ := e8TwoFive_isFiveBIn_with_minus_model S hset hB
    have hKrange : K₀ ≤ ι.range := hrange.symm ▸ (hK₀.1.1.trans inf_le_left : K₀ ≤ S.Γ)
    have hKmap : (K₀.comap ι).map ι = K₀ := Subgroup.map_comap_eq_self hKrange
    let η := (Subgroup.equivMapOfInjective (K₀.comap ι) ι hinj).trans
      (MulEquiv.subgroupCongr hKmap)
    let ηq := QuotientGroup.congr _ _ η (Subgroup.map_center_eq η)
    have hMn : LieModel (↥(K₀.comap ι) ⧸ Subgroup.center ↥(K₀.comap ι)) .POmegaMinus N 2 1 :=
      LieModel.of_mulEquiv ηq.symm hM
    rw [ha', ← hXc] at hK₀
    have hK₀' := IsFiveBIn.comap hinj (Subgroup.map_le_range _ _) hK₀
    rw [Subgroup.comap_map_eq_self_of_injective hinj] at hK₀'
    exact ⟨K₀.comap ι, hK₀', N, hMn⟩

theorem e8TwoFiveCentInput_holds :
    E8TwoFiveCentInput := by
  intro a ha5
  rcases e8TwoFive_centralizer_models a ha5 with hB | hA
  · obtain ⟨K₀, hK₀, _⟩ := hB
    exact Or.inl ⟨K₀, hK₀⟩
  · obtain ⟨F, _, _, hF, ⟨ε⟩⟩ := hA
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (n := 5) (p := 2) (f := 2) hF (by norm_num) (by norm_num)).1
    exact Or.inr (CFSG.LocalCores.isQuasisimple_of_mulEquiv ε.symm hqs)

theorem e8TwoFivePlaneCentInput_holds :
    E8TwoFivePlaneCentInput := by
  classical
  intro A hA hcard hq
  obtain ⟨a, haA, b, hbA, ha1, hb, hAeq⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.exists_gen_pair Nat.prime_five hA hcard
  have ha5 : a ^ 5 = 1 := hA.2 a haA
  have hb5 : b ^ 5 = 1 := hA.2 b hbA
  have hab : Commute a b := by
    have := hA.1.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩
    exact congrArg Subtype.val this
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]; norm_num
  have h5 : ¬ 5 ∣ Nat.card (GaloisField 2 1) := by rw [hF]; norm_num
  obtain ⟨L, hL, hLac, S, ι, hq2, -, -, hinj, hrange, haT, hbT⟩ :=
    CFSG.StandardType.LangPair.langPairAt_E8_five h5 ha5 hb5 hab
  have hq2' : S.D.q = 2 := by rw [hq2, hF]
  have hTorus : A ≤ S.D.torus.comap ι := by
    rw [← hAeq, Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [haT, hbT]
  obtain ⟨a', ha', hseta⟩ := e8f5e_exists_setup S hq2' hinj hrange ha5 ha1 haT
  obtain ⟨b', hb', hsetb⟩ := e8f5e_exists_setup S hq2' hinj hrange hb5 hb1 hbT
  have hKA : ∀ i j : ℕ, ¬ (5 ∣ i ∧ 5 ∣ j) →
      E8TwoFiveKernelA S.ρ (rootCharHom (a' ^ i * b' ^ j)) := by
    intro i j hij
    have hyA : a ^ i * b ^ j ∈ A := A.mul_mem (A.pow_mem haA i) (A.pow_mem hbA j)
    have hy1 := e8TwoFive_plane_pow_mul_ne_one ha5 hb5 hab ha1 hb hij
    have hy5 : (a ^ i * b ^ j) ^ 5 = 1 := hA.2 _ hyA
    obtain ⟨ay, hay, hsety⟩ := e8f5e_exists_setup S hq2' hinj hrange hy5 hy1 (hTorus hyA)
    have hay' : ay = a' ^ i * b' ^ j := by
      refine CFSG.LieType.Chevalley.rootDiagUnit_injective ?_
      rw [hay, map_mul, map_pow, map_pow]
      have e1 : rootDiagUnit Tag.E8 (a' ^ i * b' ^ j) =
          rootDiagUnit Tag.E8 a' ^ i * rootDiagUnit Tag.E8 b' ^ j := by
        have := (rootDiagUnitHom Tag.E8 L).map_mul (a' ^ i) (b' ^ j)
        rw [(rootDiagUnitHom Tag.E8 L).map_pow, (rootDiagUnitHom Tag.E8 L).map_pow] at this
        exact this
      rw [e1, ha', hb']
    rw [← hay']
    exact e8f5e_kernelA_of_quasisimple S hinj hrange hsety hay hy1 (hq _ hyA hy1)
  have h5L : (5 : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := by
      have := S.hqpow.2
      rwa [hq2'] at this
    have h2' : (2 : L) = 0 := by exact_mod_cast h2
    have e : (5 : L) = 2 * 2 + 1 := by norm_num
    rw [e, h2']
    simp
  have ha'5 : ∀ i, a' i ^ 5 = 1 := hseta.2.2.2.1
  have hb'5 : ∀ i, b' i ^ 5 = 1 := hsetb.2.2.2.1
  have hcount := e8TwoFive_plane_roots_nontrivial h5L ha'5 hb'5 (fun i j hij => (hKA i j hij).1)
  have hdisj : ∀ β ∈ kernelRoots (rootCharHom a'), rootChar b' β ≠ 1 := by
    rintro β ⟨hβ, hχ⟩
    refine (hcount β hβ).resolve_left ?_
    exact fun hne => hne hχ
  have hKA1 : E8TwoFiveKernelA S.ρ (rootCharHom a') := by
    simpa using hKA 1 0 (by omega)
  have hcomm := e8TwoFive_plane_centralizer_comm S hseta hKA1 hsetb.2.1 hsetb.2.2.1 hb'5 hdisj
  have hmem : ∀ z : ↥(Subgroup.centralizer (A : Set E8Two)),
      ι z.1 ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a'} ⊓
        Subgroup.centralizer {rootDiagUnit Tag.E8 b'} := by
    intro z
    rw [ha', hb']
    have hz := Subgroup.mem_centralizer_iff.1 z.2
    refine ⟨⟨hrange ▸ ⟨z.1, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    · rintro _ rfl
      simpa [map_mul] using congrArg ι (hz a haA)
    · rintro _ rfl
      simpa [map_mul] using congrArg ι (hz b hbA)
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have := congrArg Subtype.val (hcomm.is_comm.comm ⟨ι x.1, hmem x⟩ ⟨ι y.1, hmem y⟩)
  exact hinj (by simpa [map_mul] using this)

end FieldFiveE8

end CFSG.StandardType
