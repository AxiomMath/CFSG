module

public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagLie

public section

namespace CFSG.StandardType.Q1E7Model

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem exists_natCard_eq_two_pow {K : Type*} [Field K] [hF : Fintype K] [CharP K 2] :
    ∃ n : ℕ, Nat.card K = 2 ^ n := by
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨(n : ℕ), by rw [Nat.card_eq_fintype_card, hn]⟩

theorem q1E7Model_holds
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (adjointGroup .E7 K))} (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, a ∈ Set.range
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)))
    {u : MulAut (adjointGroup .E7 K)} (hu : u ∈ A) (hu1 : u ≠ 1)
    {J : Subgroup (adjointGroup .E7 K)}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ IJ _ θJ => GGAutsInduceOn A J θJ IJ) := by
  classical
  obtain ⟨g, rfl⟩ : ∃ g : adjointGroup .E7 K, MulAut.conj g = u :=
    Set.mem_range.mp (hAI u hu)
  have hinjC : Function.Injective
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hgne : g ≠ 1 := fun h => hu1 (by rw [h, map_one])
  have hgp : g ^ p = 1 := by
    have h : (MulAut.conj g) ^ p = 1 := hA.2 (MulAut.conj g) hu
    rw [← map_pow] at h
    exact hinjC (by rw [h, map_one])
  obtain ⟨n, hn⟩ := exists_natCard_eq_two_pow (K := K) (hF := Fintype.ofFinite K)
  have hqK : Nat.card K = 2 ^ (n : ℕ) := hn
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hqK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have h5K : ¬ 5 ∣ Nat.card K := by
    rw [hqK]
    intro h
    have h2 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
    norm_num at h2
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt .E7 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (τ := .E7)
      (by decide) hp hp2
  have hperf : commutator ↥(adjointGroup .E7 K) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup .E7 K
      (fun h => absurd h (by decide))).commutator_eq_top
  have hβ : ∀ c, (MulAut.conj g c : ModGL .E7 K) =
      (g : ModGL .E7 K) * c * (g : ModGL .E7 K)⁻¹ := by
    intro c
    rw [MulAut.conj_apply]
    rfl
  have hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) (g : ModGL .E7 K) ∈
      adjointGroup .E7 (AlgebraicClosure K) :=
    CFSG.LocalAnalysis.ComponentInitial.baseChangeGL_mem_adjointGroup _ g.2
  have hgp' : (g : ModGL .E7 K) ^ p = 1 := by
    simpa using congrArg (fun z : ↥(adjointGroup .E7 K) => (z : ModGL .E7 K)) hgp
  have hgne' : (g : ModGL .E7 K) ≠ 1 := fun h => hgne (Subtype.ext h)
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := .E7) (p := p)
      (by decide) hp hpK Nat.prime_five h5K (Or.inl le_rfl)
      hmon hperf (MulAut.conj g) (g : ModGL .E7 K) hhL hβ hgp' hgne'
  let L := AlgebraicClosure K
  let X : Subgroup (ModGL .E7 L) := J.map ι
  have hfixmap : (ggAutFixedSubgroup (MulAut.conj g)).map ι =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E7 a} := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hrange]
        exact ⟨c, rfl⟩
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have hm : rootDiagUnit .E7 a * ι c * (rootDiagUnit .E7 a)⁻¹ = ι c := by
          rw [← hconjι c, hc]
        have h3 := congrArg (fun z : ModGL .E7 L => z * rootDiagUnit .E7 a) hm
        simpa [mul_assoc] using h3.symm
    · rintro ⟨hyΓ, hyC⟩
      rw [← hrange] at hyΓ
      obtain ⟨c, hcι⟩ := MonoidHom.mem_range.mp hyΓ
      refine ⟨c, ?_, hcι⟩
      rw [← hcι] at hyC
      have hcomm : ι c * rootDiagUnit .E7 a = rootDiagUnit .E7 a * ι c :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      have hfix : rootDiagUnit .E7 a * ι c * (rootDiagUnit .E7 a)⁻¹ = ι c := by
        rw [← hcomm]
        simp
      apply hinj
      rw [hconjι c, hfix]
  have hX : CFSG.Assembly.IsComponentOf X
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E7 a}) := by
    have hJopen : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup (MulAut.conj g)) :=
      CFSG.Assembly.isComponentOf_iff_open.mp hJ
    have hmap := CFSG.LieType.SemisimpleCentralizers.Held.isComponentOf_map_of_injective
      ι hinj hJopen
    rw [hfixmap] at hmap
    exact CFSG.Assembly.isComponentOf_iff_open.mpr hmap
  let A' : Subgroup (adjointGroup .E7 K) :=
    A.comap (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))
  let E : Subgroup (ModGL .E7 L) := A'.map ι
  have hE : E ≤ S.D.model := by
    intro e he
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp he
    have hΓ : ι w ∈ S.Γ := by
      rw [← hrange]
      exact ⟨w, rfl⟩
    exact (Subgroup.commutator_le_self S.D.model) hΓ
  have hEp : ∀ e ∈ E, e ^ p = 1 := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp he
    have hwA : MulAut.conj w ∈ A := Subgroup.mem_comap.mp hw
    have hwp : w ^ p = 1 := by
      have h : (MulAut.conj w) ^ p = 1 := hA.2 (MulAut.conj w) hwA
      rw [← map_pow] at h
      exact hinjC (by rw [h, map_one])
    rw [← map_pow, hwp, map_one]
  have hker : familyKernel (fun _ : Unit => a) = rootCharKernel a := by
    ext α
    simp only [familyKernel, rootCharKernel, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1, h.2 ()⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  have hW :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd
      (K := L) hp hp2 (τ := .E7)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (by intro h; exact absurd h (by decide)) hap
  have htoral : toralCentralizer .E7 L a = toralRootGroup .E7 L a :=
    CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_of_stabilizer_le
      .E7 L a hW
  have hconn : E ≤ familyGroup (fun _ : Unit => a) := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp he
    have hwA : MulAut.conj w ∈ A := Subgroup.mem_comap.mp hw
    have huw : MulAut.conj w * MulAut.conj g = MulAut.conj g * MulAut.conj w := by
      have h := (isMulCommutative_iff.mp hA.1) ⟨MulAut.conj w, hwA⟩ ⟨MulAut.conj g, hu⟩
      exact congrArg Subtype.val h
    have hwg : w * g * w⁻¹ = g := by
      apply hinjC
      rw [map_mul, map_mul, map_inv]
      rw [huw]
      group
    have hcomm : w * g = g * w := by
      have h3 := congrArg (fun z : adjointGroup .E7 K => z * w) hwg
      simpa [mul_assoc] using h3
    have hgw : MulAut.conj g w = w := by
      rw [MulAut.conj_apply]
      rw [← hcomm]
      simp
    have hιwΓ : ι w ∈ S.Γ := by
      rw [← hrange]
      exact ⟨w, rfl⟩
    have hιwG : ι w ∈ adjointGroup .E7 L :=
      ((Subgroup.commutator_le_self S.D.model) hιwΓ).1
    have hfixd : rootDiagUnit .E7 a * ι w * (rootDiagUnit .E7 a)⁻¹ = ι w := by
      rw [← hconjι w, hgw]
    have hmemC : ι w ∈ toralCentralizer .E7 L a :=
      mem_toralCentralizer.mpr ⟨hιwG, hfixd⟩
    have hmem : ι w ∈ toralRootGroup .E7 L a := htoral ▸ hmemC
    simpa only [familyGroup, hker, toralRootGroup] using hmem
  have hGE : GGE0Concl E X :=
    langTorus_connectedModelAction (τ := .E7) (L := L) (p := p) (Or.inr (Or.inl rfl)) hp hp2
      S a hT hap h1 E X hE hEp hconn hX
  have hpL : (p : L) ≠ 0 := by
    refine natCast_ne_zero_of_ringChar_ne hp ?_
    rw [ringChar.eq L 2]
    exact fun h => hp2 h.symm
  have hτne : (Tag.E7) ≠ .G2 := by decide
  obtain ⟨i, hQS, hXeq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
      S hτne hp hpL hT hap h1 (CFSG.Assembly.isComponentOf_iff_open.mp hX)
  obtain ⟨t, n, f, hLM, -, -⟩ :=
    langComp_lieModel_alternative (Or.inr (Or.inl rfl)) S hp hp2 hT hap i hQS
      (y := 1) (Subgroup.one_mem _) (map_one _) (by simp)
  have hmarkX : LargeEvenMarking X (fun _ _ _ _ _ _ => True) := by
    rw [hXeq]
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_of_lieModel_centerQuot (Group.isPerfect_def.mp hQS.1) hLM)
  have hGE' := hGE.2 hmarkX
  let eJK : ↥J ≃* ↥X := J.equivMapOfInjective ι hinj
  have hcoeJK : ∀ j : ↥J, ((eJK j : ↥X) : ModGL .E7 L) = ι (j : adjointGroup .E7 K) :=
    fun _ => rfl
  have hmarkJ : LargeEvenMarking J (fun _ _ _ IJ _ θJ => GGAutsInduceOn A J θJ IJ) := by
    refine largeEvenMarking_congr eJK ?_ hGE'
    intro lab R instR I F θK hP a ha
    obtain ⟨w, rfl⟩ : ∃ w, MulAut.conj w = a := Set.mem_range.mp (hAI a ha)
    have hwA' : w ∈ A' := Subgroup.mem_comap.mpr ha
    have hmemE : (ι w)⁻¹ ∈ E :=
      Subgroup.inv_mem _ (Subgroup.mem_map.mpr ⟨w, hwA', rfl⟩)
    obtain ⟨φ, hφ, hind⟩ := hP.2 ((ι w)⁻¹) hmemE
    refine ⟨φ, hφ, ?_⟩
    have hrel : ∀ j j' : ↥J,
        (MulAut.conj w (j : adjointGroup .E7 K) = (j' : adjointGroup .E7 K)) ↔
          (((eJK j' : ↥X) : ModGL .E7 L) =
            ι w * ((eJK j : ↥X) : ModGL .E7 L) * (ι w)⁻¹) := by
      intro j j'
      rw [hcoeJK j', hcoeJK j]
      constructor
      · intro h
        rw [← h]
        simp only [MulAut.conj_apply, map_mul, map_inv]
      · intro h
        apply hinj
        simpa only [MulAut.conj_apply, map_mul, map_inv] using h.symm
    have hind' : LargeEvenInduces θK
        (fun l l' : ↥X => (l' : ModGL .E7 L) = ι w * (l : ModGL .E7 L) * (ι w)⁻¹) φ := by
      simpa only [inv_inv] using hind
    exact (largeEvenInduces_congr_equiv eJK θK
      (fun j j' : ↥J =>
        MulAut.conj w (j : adjointGroup .E7 K) = (j' : adjointGroup .E7 K))
      (fun l l' : ↥X => (l' : ModGL .E7 L) = ι w * (l : ModGL .E7 L) * (ι w)⁻¹)
      hrel φ).2 hind'
  have hnormJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := by
    intro a ha j hj
    obtain ⟨w, rfl⟩ : ∃ w, MulAut.conj w = a := Set.mem_range.mp (hAI a ha)
    have hwA' : w ∈ A' := Subgroup.mem_comap.mpr ha
    have hmemE : ι w ∈ E := Subgroup.mem_map.mpr ⟨w, hwA', rfl⟩
    have hN : ι w ∈ Subgroup.normalizer (X : Set (ModGL .E7 L)) := hGE.1 hmemE
    have hjX : ι (j : adjointGroup .E7 K) ∈ X := ⟨j, hj, rfl⟩
    have hmemX : ι w * ι (j : adjointGroup .E7 K) * (ι w)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hN (ι (j : adjointGroup .E7 K))).mp hjX
    have heq : ι (MulAut.conj w (j : adjointGroup .E7 K)) =
        ι w * ι (j : adjointGroup .E7 K) * (ι w)⁻¹ := by
      rw [MulAut.conj_apply]
      simp only [map_mul, map_inv]
    rw [← heq] at hmemX
    obtain ⟨x, hxJ, hxeq⟩ := Subgroup.mem_map.mp hmemX
    exact (hinj hxeq) ▸ hxJ
  exact ⟨hnormJ, hmarkJ⟩

end CFSG.StandardType.Q1E7Model
