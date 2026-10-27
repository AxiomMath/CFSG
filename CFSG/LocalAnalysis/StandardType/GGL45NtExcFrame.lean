module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcGeo
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtLattice
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrameLemmas
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrameStab
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcCentral
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcCoroot

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly CFSG.StandardType
  CFSG.StandardType.LieCore CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.C14Idx


@[expose] noncomputable def twFw
    (τ : Tag) (L : Type) [Field L]
    [CharP L 2] (e : ℕ)
    (Q : ModGL τ L) (w : WeylGroup τ) : ModGL τ L →* ModGL τ L :=
  (MulAut.conj (canonicalRep (coxeterSystem τ) L w)).toMonoidHom.comp (frobTwistGL τ L 2 e Q)

@[expose] noncomputable def famSub
                                      (τ : Tag) (L : Type) [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) : Subgroup (ModGL τ L) :=
  Subgroup.closure (Set.range fun i => rootDiagUnit τ (a i))


theorem card_elemAbelian_lt
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {N : ℕ} (hN : 1000 ≤ N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (ModGL τ L)}
    [Finite E] (hE : IsElemAbelian p E) : Nat.card E < p ^ N := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpL : (p : L) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff L 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  haveI : NeZero (p : L) := ⟨hpL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  let F : E →* Module.End L (RootModule τ L) :=
    (Units.coeHom (Module.End L (RootModule τ L))).comp (Subgroup.subtype E)
  have hcomm : ∀ i j : E, Commute (F i) (F j) := by
    intro i j
    haveI : IsMulCommutative ↥E := hE.1
    change F i * F j = F j * F i
    rw [← map_mul, ← map_mul, mul_comm' i j]
  have hpow : ∀ i : E, F i ^ p = 1 := by
    intro i
    have h := congrArg (fun u : ModGL τ L => (u : Module.End L (RootModule τ L))) (hE.2 i i.2)
    simpa [F] using h
  obtain ⟨b, μ, hμ⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one
      hζ F hcomm hpow
  have hroot : ∀ (x : E) (j : Fin (Module.finrank L (RootModule τ L))), (μ x j) ^ p = 1 := by
    intro x j
    have hv : Module.End.HasEigenvector (F x) (μ x j) (b j) :=
      ⟨by rw [Module.End.mem_genEigenspace_one]; exact hμ x j, Module.Basis.ne_zero b j⟩
    have h1 := hv.pow_apply p
    rw [hpow x] at h1
    have h1' : b j = (μ x j) ^ p • b j := by simpa using h1
    have h2 : ((μ x j) ^ p - 1) • b j = 0 := by
      rw [sub_smul, one_smul, ← h1', sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (Module.Basis.ne_zero b j)
  let χ : E → (Fin (Module.finrank L (RootModule τ L)) → rootsOfUnity p L) :=
    fun x j =>
      ⟨Units.mk0 (μ x j) (by
          intro h0
          have h1 := hroot x j
          rw [h0, zero_pow hp.ne_zero] at h1
          exact zero_ne_one h1),
        by
          rw [mem_rootsOfUnity]
          exact Units.ext (by
            rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, hroot x j])⟩
  have hχ : Function.Injective χ := by
    intro x y hxy
    have hμeq : ∀ j, μ x j = μ y j := by
      intro j
      have h := congrArg (fun z : rootsOfUnity p L => ((z : Lˣ) : L)) (congrFun hxy j)
      simpa [χ] using h
    apply Subtype.ext
    apply Units.ext
    change F x = F y
    apply b.ext
    intro j
    rw [hμ x j, hμ y j, hμeq j]
  have hcard_le : Nat.card E ≤ p ^ Module.finrank L (RootModule τ L) := by
    have h1 : Nat.card E ≤
        Nat.card (Fin (Module.finrank L (RootModule τ L)) → rootsOfUnity p L) :=
      Nat.card_le_card_of_injective χ hχ
    have h2 : Nat.card (Fin (Module.finrank L (RootModule τ L)) → rootsOfUnity p L) ≤
        p ^ Module.finrank L (RootModule τ L) := by
      rw [Nat.card_fun]
      have hfin : Nat.card (Fin (Module.finrank L (RootModule τ L))) =
          Module.finrank L (RootModule τ L) := by simp [Nat.card_eq_fintype_card]
      rw [hfin]
      exact Nat.pow_le_pow_left (card_rootsOfUnity L p) _
    exact h1.trans h2
  have hd_lt : Module.finrank L (RootModule τ L) < 1000 := by
    rw [Module.finrank_finsupp_self]
    rw [card_label τ, Nat.card_eq_fintype_card, card_isRoot τ]
    cases τ <;> decide
  calc Nat.card E ≤ p ^ Module.finrank L (RootModule τ L) := hcard_le
    _ < p ^ N := Nat.pow_lt_pow_right hp.one_lt (lt_of_lt_of_le hd_lt hN)

theorem nontoralMinRank_eq_of_nonTorsion
    {τ : Tag} {p : ℕ} (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) : nontoralMinRank τ p = 1000 := by
  cases τ <;> simp_all [nontoralMinRank]

theorem ratPts_le_endPow
                                      {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {Φ : ModGL τ L →* ModGL τ L} {n : ℕ} (hn : 1 ≤ n) :
    ratPts τ L Φ ≤ ratPts τ L (endPow Φ n) := by
  intro g hg
  rw [ratPts, Subgroup.mem_inf] at hg ⊢
  refine ⟨hg.1, ?_⟩
  show endPow Φ n g = g
  rw [endPow_apply]
  exact Function.iterate_fixed hg.2 n

theorem exists_rootDiagUnit_of_mem_torusGroup
                                   {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {x : ModGL τ L} (hx : x ∈ torusGroup τ L) :
    ∃ t : Fin τ.rank → Lˣ, x = rootDiagUnit τ t :=
  exists_rootDiagUnit_eq_of_mem_torusGroup hx

theorem lang_conj_identity
    {Γ : Type*} [Group Γ] (F₀ : Γ →* Γ) (g n : Γ) (hg : F₀ g = g * n)
    (y : Γ) : g⁻¹ * F₀ (g * y * g⁻¹) * g = n * F₀ y * n⁻¹ := by
  rw [map_mul, map_mul, map_inv, hg]
  group

theorem endPow_conj
                                      {Γ : Type*} [Group Γ] (F₀ F₁ : Γ →* Γ) (h : Γ)
    (hF : ∀ y, h * F₀ (h⁻¹ * y * h) * h⁻¹ = F₁ y) (n : ℕ) (y : Γ) :
    endPow F₁ n (h * y * h⁻¹) = h * endPow F₀ n y * h⁻¹ := by
  induction n generalizing y with
  | zero => simp [endPow_apply]
  | succ n ih =>
    have hL : endPow F₁ (n + 1) (h * y * h⁻¹) =
        F₁ (endPow F₁ n (h * y * h⁻¹)) := by
      rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
    have hR : endPow F₀ (n + 1) y = F₀ (endPow F₀ n y) := by
      rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
    rw [hL, ih, ← hF (h * endPow F₀ n y * h⁻¹),
      show h⁻¹ * (h * endPow F₀ n y * h⁻¹) * h = endPow F₀ n y from by group, hR]

theorem exc_lang_frame_of_toral
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hM2 : GGLieLangPosition) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q)
    (hfin : Finite ↥(ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p)))
    {E : Subgroup (ModGL τ L)} (hEab : IsElemAbelian p E)
    (hEF : E ≤ ratPts τ L (frobTwistGL τ L 2 e Q))
    (htoral : CFSG.StandardType.ExcFramesHalf.IsToralSubgroup τ L E) :
    ∃ (w : WeylGroup τ) (h : ModGL τ L) (a : E → Fin τ.rank → Lˣ), h ∈ adjointGroup τ L ∧
      (∀ x : E, h * x * h⁻¹ = rootDiagUnit τ (a x)) ∧
      ∀ g, h * frobTwistGL τ L 2 e Q (h⁻¹ * g * h) * h⁻¹ = twFw τ L e Q w g := by
  classical
  let F₀ : ModGL τ L →* ModGL τ L := frobTwistGL τ L 2 e Q
  have hSt : IsSteinbergEndZ τ L (2 ^ e) F₀ := isSteinbergEndZ_frobTwistGL 2 e hQ
  have hleF0 : ratPts τ L F₀ ≤ ratPts τ L (endPow F₀ p) := ratPts_le_endPow hp.one_le
  haveI hfinG : Finite ↥(ratPts τ L (endPow F₀ p)) := hfin
  haveI hfinF0 : Finite ↥(ratPoints F₀) :=
    Finite.of_injective (Subgroup.inclusion hleF0) (Subgroup.inclusion_injective hleF0)
  obtain ⟨w, g₀, hg₀, hlang, hmap⟩ :=
    hM2 τ (isExcTag τ) L e he F₀ hSt hfinF0 p hp hp2 E hEF hEab htoral
  have hg₀inv : g₀⁻¹ ∈ adjointGroup τ L := Subgroup.inv_mem _ hg₀
  have hF : ∀ y, g₀⁻¹ * F₀ (g₀ * y * g₀⁻¹) * g₀ = twFw τ L e Q w y := by
    intro y
    have h := lang_conj_identity F₀ g₀ (canonicalRep (coxeterSystem τ) L w) hlang y
    change g₀⁻¹ * F₀ (g₀ * y * g₀⁻¹) * g₀ =
      canonicalRep (coxeterSystem τ) L w * F₀ y * (canonicalRep (coxeterSystem τ) L w)⁻¹
    exact h
  have hxT : ∀ x : E, g₀⁻¹ * (x : ModGL τ L) * g₀ ∈ torusGroup τ L := by
    intro x
    have hxmap : (MulAut.conj g₀⁻¹).toMonoidHom (x : ModGL τ L) ∈
        E.map (MulAut.conj g₀⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ x.2
    have hmem : (MulAut.conj g₀⁻¹).toMonoidHom (x : ModGL τ L) ∈
        CFSG.RankThree.PartOne.KE.twistedTorusOf (canonicalRep (coxeterSystem τ) L w) F₀ :=
      hmap hxmap
    rw [CFSG.RankThree.PartOne.KE.twistedTorusOf] at hmem
    have h1 : (MulAut.conj g₀⁻¹).toMonoidHom (x : ModGL τ L) ∈ torusGroup τ L :=
      (Subgroup.mem_inf.mp hmem).1
    simpa [MulAut.conj_apply, inv_inv] using h1
  have hex : ∀ x : E, ∃ t : Fin τ.rank → Lˣ,
      g₀⁻¹ * (x : ModGL τ L) * g₀ = rootDiagUnit τ t :=
    fun x => exists_rootDiagUnit_of_mem_torusGroup (hxT x)
  let a : E → Fin τ.rank → Lˣ := fun x => Classical.choose (hex x)
  have ha_conj : ∀ x : E, g₀⁻¹ * (x : ModGL τ L) * g₀ = rootDiagUnit τ (a x) :=
    fun x => Classical.choose_spec (hex x)
  refine ⟨w, g₀⁻¹, a, hg₀inv, ?_, ?_⟩
  · intro x
    simpa only [inv_inv] using ha_conj x
  · intro y
    simpa only [inv_inv] using hF y

theorem exc_lang_frame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hM1 : GGLieToralPosition) (hM2 : GGLieLangPosition)
    (hL : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5)
    {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q)
    (hfin : Finite ↥(ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p)))
    {E : Subgroup (ModGL τ L)} (hEab : IsElemAbelian p E)
    (hEF : E ≤ ratPts τ L (frobTwistGL τ L 2 e Q)) :
    ∃ (w : WeylGroup τ) (h : ModGL τ L) (a : E → Fin τ.rank → Lˣ), h ∈ adjointGroup τ L ∧
      (∀ x : E, h * x * h⁻¹ = rootDiagUnit τ (a x)) ∧
      (∀ g, h * frobTwistGL τ L 2 e Q (h⁻¹ * g * h) * h⁻¹ = twFw τ L e Q w g) ∧
      ∀ g, (g ∈ ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p) ∧ ∀ x ∈ E, g * x = x * g) ↔
        h * g * h⁻¹ ∈ ratPts τ L (endPow (twFw τ L e Q w) p) ⊓ familyGroup a := by
  classical
  let F₀ : ModGL τ L →* ModGL τ L := frobTwistGL τ L 2 e Q
  have hSt : IsSteinbergEndZ τ L (2 ^ e) F₀ := isSteinbergEndZ_frobTwistGL 2 e hQ
  have hleF0 : ratPts τ L F₀ ≤ ratPts τ L (endPow F₀ p) := ratPts_le_endPow hp.one_le
  have hE_le : E ≤ ratPts τ L (endPow F₀ p) := hEF.trans hleF0
  haveI hfinG : Finite ↥(ratPts τ L (endPow F₀ p)) := hfin
  haveI hfinE : Finite E :=
    Finite.of_injective (Subgroup.inclusion hE_le) (Subgroup.inclusion_injective hE_le)
  haveI hfinF0 : Finite ↥(ratPoints F₀) :=
    Finite.of_injective (Subgroup.inclusion hleF0) (Subgroup.inclusion_injective hleF0)
  have hcard : Nat.card E < p ^ nontoralMinRank τ p :=
    card_elemAbelian_lt (N := nontoralMinRank τ p)
      (le_of_eq (nontoralMinRank_eq_of_nonTorsion h3 h5).symm) hp hp2 hEab
  have htoral := hM1 τ (isExcTag τ) L hL e he F₀ hSt hfinF0 p hp hp2 E hEF hEab hcard
  obtain ⟨w, h, a, hhG, hconj, hFw⟩ :=
    exc_lang_frame_of_toral hM2 hp hp2 he hQ hfin hEab hEF htoral
  have ha : ∀ i j, a i j ^ p = 1 := by
    intro x j
    have hxp : (x : ModGL τ L) ^ p = 1 := hEab.2 (x : ModGL τ L) x.2
    have h1 : (rootDiagUnit τ (a x)) ^ p = 1 := by
      rw [← hconj x]
      have hconj' : h * (x : ModGL τ L) * h⁻¹ = (MulAut.conj h) (x : ModGL τ L) := by
        rw [MulAut.conj_apply]
      rw [hconj', ← map_pow, hxp, map_one]
    have h2 : rootDiagUnit τ ((a x) ^ p) = 1 := by
      have hm := (rootDiagUnitHom τ L).map_pow (a x) p
      change (rootDiagUnitHom τ L) ((a x) ^ p) = 1
      rw [hm]
      exact h1
    have h3' : (a x) ^ p = 1 :=
      rootDiagUnit_injective (by rw [h2, rootDiagUnit_one])
    simpa using congrFun h3' j
  refine ⟨w, h, a, hhG, hconj, hFw, ?_⟩
  intro g'
  constructor
  · rintro ⟨hg'G, hg'cent⟩
    have hyG : h * g' * h⁻¹ ∈ adjointGroup τ L :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hhG hg'G.1) (Subgroup.inv_mem _ hhG)
    have hyfam : h * g' * h⁻¹ ∈ familyGroup a := by
      rw [mem_familyGroup_iff hp hp2 h3 h5 a ha hyG]
      intro x
      have hcx : g' * (x : ModGL τ L) = (x : ModGL τ L) * g' := hg'cent x x.2
      have hxinv : (x : ModGL τ L) * g' * (x : ModGL τ L)⁻¹ = g' := by
        rw [← hcx]; group
      rw [← hconj x]
      calc (h * (x : ModGL τ L) * h⁻¹) * (h * g' * h⁻¹) *
            (h * (x : ModGL τ L) * h⁻¹)⁻¹
            = h * ((x : ModGL τ L) * g' * (x : ModGL τ L)⁻¹) * h⁻¹ := by group
        _ = h * g' * h⁻¹ := by rw [hxinv]
    refine Subgroup.mem_inf.mpr ⟨?_, hyfam⟩
    rw [ratPts, Subgroup.mem_inf]
    refine ⟨hyG, ?_⟩
    show endPow (twFw τ L e Q w) p (h * g' * h⁻¹) = h * g' * h⁻¹
    have hconj2 := endPow_conj F₀ (twFw τ L e Q w) h hFw p g'
    rw [hg'G.2] at hconj2
    simpa using hconj2
  · rintro hmem
    rw [Subgroup.mem_inf] at hmem
    have hyG : h * g' * h⁻¹ ∈ adjointGroup τ L := by
      have h := hmem.1
      rw [ratPts, Subgroup.mem_inf] at h
      exact h.1
    have hyfix : endPow (twFw τ L e Q w) p (h * g' * h⁻¹) = h * g' * h⁻¹ := by
      have h := hmem.1
      rw [ratPts, Subgroup.mem_inf] at h
      exact h.2
    have hg'G : g' ∈ adjointGroup τ L := by
      have hmem' : h⁻¹ * (h * g' * h⁻¹) * h ∈ adjointGroup τ L :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhG) hyG) hhG
      have heq : h⁻¹ * (h * g' * h⁻¹) * h = g' := by group
      rwa [heq] at hmem'
    have hg'fix : endPow F₀ p g' = g' := by
      have hconj2 := endPow_conj F₀ (twFw τ L e Q w) h hFw p g'
      rw [hyfix] at hconj2
      have hX : h * endPow F₀ p g' * h⁻¹ = h * g' * h⁻¹ := hconj2.symm
      rw [mul_assoc, mul_assoc] at hX
      exact mul_right_cancel (mul_left_cancel hX)
    have hg'cent : ∀ x ∈ E, g' * x = x * g' := by
      intro x hxE
      let xE : E := ⟨x, hxE⟩
      have hxfam := (mem_familyGroup_iff hp hp2 h3 h5 a ha hyG).mp hmem.2 xE
      rw [← hconj xE] at hxfam
      have hconjEq : (x : ModGL τ L) * g' * (x : ModGL τ L)⁻¹ = g' := by
        have h1 : h⁻¹ * ((h * (x : ModGL τ L) * h⁻¹) * (h * g' * h⁻¹) *
              (h * (x : ModGL τ L) * h⁻¹)⁻¹) * h
            = (x : ModGL τ L) * g' * (x : ModGL τ L)⁻¹ := by group
        have h2 : h⁻¹ * (h * g' * h⁻¹) * h = g' := by group
        have hh := congrArg (fun t => h⁻¹ * t * h) hxfam
        rw [h1, h2] at hh
        exact hh
      have : (x : ModGL τ L) * g' = g' * (x : ModGL τ L) := by
        calc (x : ModGL τ L) * g'
            = ((x : ModGL τ L) * g' * (x : ModGL τ L)⁻¹) * (x : ModGL τ L) := by group
          _ = g' * (x : ModGL τ L) := by rw [hconjEq]
      exact this.symm
    exact ⟨⟨hg'G, hg'fix⟩, hg'cent⟩

theorem twFw_eq_frobTwistGL
                                   {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (e : ℕ) (Q : ModGL τ L) (w : WeylGroup τ) :
    twFw τ L e Q w = frobTwistGL τ L 2 e (canonicalRep (coxeterSystem τ) L w * Q) := by
  apply MonoidHom.ext
  intro g
  change canonicalRep (coxeterSystem τ) L w *
      (Q * entrywiseFrobGL τ L 2 e g * Q⁻¹) * (canonicalRep (coxeterSystem τ) L w)⁻¹ =
    (canonicalRep (coxeterSystem τ) L w * Q) * entrywiseFrobGL τ L 2 e g *
      (canonicalRep (coxeterSystem τ) L w * Q)⁻¹
  group

theorem frame_hQT
                                   {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ) :
    ∀ t : Fin τ.rank → Lˣ, ∃ t' : Fin τ.rank → Lˣ,
      (canonicalRep (coxeterSystem τ) L w * Q) * rootDiagUnit τ t *
        (canonicalRep (coxeterSystem τ) L w * Q)⁻¹ = rootDiagUnit τ t' := by
  intro t
  rcases hQ with rfl | ⟨s, j, h, rfl⟩
  · exact ⟨weylTuple w t, by simpa using canonicalRep_conj_rootDiagUnit (K := L) w t⟩
  · cases h
    refine ⟨weylTuple w (fun i => t ((s.perm ^ j).symm i)), ?_⟩
    have h1 : canonicalRep (coxeterSystem s.tag) L w * diagramMap s L ^ j * rootDiagUnit s.tag t *
        (canonicalRep (coxeterSystem s.tag) L w * diagramMap s L ^ j)⁻¹ =
        canonicalRep (coxeterSystem s.tag) L w *
          (diagramMap s L ^ j * rootDiagUnit s.tag t * (diagramMap s L ^ j)⁻¹) *
          (canonicalRep (coxeterSystem s.tag) L w)⁻¹ := by group
    rw [h1, CFSG.HardMathSupport.C14L44.diagramMap_zpow_conj_rootDiagUnit,
      canonicalRep_conj_rootDiagUnit]

theorem frame_hQτ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {Q : ModGL τ L} (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) L w * Q ∈ adjointGroup τ L ∨
      ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L), n ∈ adjointGroup τ L ∧
        canonicalRep (coxeterSystem τ) L w * Q = (h ▸ diagramMap t L ^ j) * n := by
  rcases hQ with rfl | ⟨s, j, h, rfl⟩
  · left
    simpa using canonicalRep_mem_adjointGroup (coxeterSystem τ) L w
  · cases h
    right
    refine ⟨s, j, rfl, diagramMap s L ^ (-j) * canonicalRep (coxeterSystem s.tag) L w *
      diagramMap s L ^ j, ?_, ?_⟩
    · have h := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow s L (-j)) _
        (canonicalRep_mem_adjointGroup (coxeterSystem s.tag) L w)
      simpa using h
    · group

theorem exc_frame_hsat
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {ι : Type} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5) [Finite ι]
    (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1)
    (hcard : p ^ 2 ≤ Nat.card (famSub τ L a)) :
    ∀ v : Fin τ.rank → ℤ, p • v ∈ AddSubgroup.closure (familyKernel a) →
      v ∈ AddSubgroup.closure (familyKernel a) := by
  intro v hv
  by_cases hG : τ = .G2 ∧ p = 3
  ·
    obtain ⟨rfl, rfl⟩ := hG
    have hcard' : 9 ≤ Nat.card (Subgroup.closure
        (Set.range fun i => rootDiagUnit Tag.G2 (a i))) := by
      have h := hcard
      norm_num at h
      simpa [famSub] using h
    have hempty : familyKernel a = ∅ := familyKernel_empty_G2_three a ha hcard'
    rw [hempty, AddSubgroup.closure_empty, AddSubgroup.mem_bot] at hv
    have hv0 : v = 0 := by
      funext i
      have hi : 3 • v i = 0 := by
        have h := congrFun hv i
        simpa [Pi.smul_apply] using h
      rw [nsmul_eq_mul] at hi
      exact (mul_eq_zero.mp hi).resolve_left (by norm_num)
    rw [hempty, AddSubgroup.closure_empty, AddSubgroup.mem_bot]
    exact hv0
  · exact familyKernel_pSaturated hp hp2 h3 h5 (fun h hp3 => hG ⟨h, hp3⟩) a v hv

private theorem eW2_diagKer_mul_comm
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {x y : ModGL τ L}
    (hx : x ∈ diagKer τ L (familyKernel a)) (hy : y ∈ diagKer τ L (familyKernel a)) :
    x * y = y * x := by
  obtain ⟨t, rfl, -⟩ := hx
  obtain ⟨s, rfl, -⟩ := hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm t s]

private theorem eW2_diagKer_le_adjointGroup
                                   {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    diagKer τ L (familyKernel a) ≤ adjointGroup τ L := by
  intro g hg
  obtain ⟨t, rfl, -⟩ := hg
  exact torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup t)

theorem exc_frame_power
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ι : Type} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h3D : τ = .D4 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) [Finite ι] {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ) (a : ι → Fin τ.rank → Lˣ)
    (ha : ∀ i j, a i j ^ p = 1)
    (hfix : ∀ i, twFw τ L e Q w (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i))
    (hfin : Finite ↥(ratPts τ L (endPow (twFw τ L e Q w) p))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ z ∈ diagKer τ L (familyKernel a), (∃ n : ℕ, z ^ p ^ n = 1) →
      endPow (twFw τ L e Q w) p z = z → twFw τ L e Q w z = z ^ N := by
  classical
  let Q' : ModGL τ L := canonicalRep (coxeterSystem τ) L w * Q
  let F : ModGL τ L →* ModGL τ L := frobTwistGL τ L 2 e Q'
  have hFw : twFw τ L e Q w = F := twFw_eq_frobTwistGL e Q w
  have hfix' : ∀ i, F (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i) := by
    intro i
    rw [← hFw]
    exact hfix i
  have hQT : ∀ t : Fin τ.rank → Lˣ, ∃ t' : Fin τ.rank → Lˣ,
      Q' * rootDiagUnit τ t * Q'⁻¹ = rootDiagUnit τ t' := frame_hQT hQ w
  have hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ)
      (n : ModGL τ L), n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n :=
    frame_hQτ hQ w
  obtain ⟨k, hk1, hkpow⟩ := lemma45_frame hp hp2 h3 h3D h5 a ha e Q' hQT hQτ hfix'
  obtain ⟨γ, -, -, -, -, hFγ⟩ := lemma44_frame hp hp2 h3 h3D h5 a ha e Q' hQT hQτ hfix'
  let q : ℕ := 2 ^ e
  let Kk : ℕ := p * k
  let G : Subgroup (ModGL τ L) := ratPts τ L (endPow F p)
  have hfinG : Finite G := by
    dsimp only [G]
    rw [← hFw]
    exact hfin
  let P : ℕ := p ^ (Nat.card G).factorization p
  have hPpos : 0 < P := by
    dsimp only [P]
    exact pow_pos hp.pos _
  let tt : ℕ := Nat.totient P
  have ht1 : 1 ≤ tt := by
    dsimp only [tt]
    have h := Nat.totient_pos.mpr hPpos
    omega
  let X : ℕ := Kk * (tt - 1) + 1
  let N : ℕ := q ^ X
  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hq2 : 2 ≤ q := by
    dsimp only [q]
    have h : 1 < 2 ^ e := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hN2 : 2 ≤ N := by
    dsimp only [N]
    have hX1 : 1 ≤ X := by dsimp only [X]; omega
    calc 2 ≤ q := hq2
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ X := Nat.pow_le_pow_right (by omega) hX1
  have hcopqP : Nat.Coprime q P := by
    dsimp only [q, P]
    exact Nat.Coprime.pow e _ h2p
  have hExp : X + Kk = Kk * tt + 1 := by
    dsimp only [X]
    rw [Nat.add_assoc, Nat.add_comm 1 Kk, ← Nat.add_assoc, ← Nat.mul_succ,
      Nat.succ_eq_add_one, Nat.sub_add_cancel ht1]
  have hswap : (q ^ Kk) ^ tt = (q ^ tt) ^ Kk := by
    rw [← pow_mul, mul_comm Kk tt, pow_mul]
  have hXKk : N * q ^ Kk = (q ^ tt) ^ Kk * q := by
    dsimp only [N]
    rw [← pow_add, hExp, pow_add, pow_one, pow_mul, hswap]
  have hqt : q ^ tt ≡ 1 [MOD P] := by
    dsimp only [tt]
    exact Nat.ModEq.pow_totient hcopqP
  have hmod : N * q ^ Kk ≡ q [MOD P] := by
    rw [hXKk]
    exact (Nat.ModEq.mul (Nat.ModEq.pow Kk hqt) (Nat.ModEq.refl q)).trans
      (by rw [one_pow, one_mul])
  refine ⟨N, hN2, ?_⟩
  intro z hzZ hzp hzF
  have hzF' : endPow F p z = z := by
    rw [hFw] at hzF
    exact hzF
  have hzG : z ∈ G := by
    dsimp only [G]
    rw [ratPts, Subgroup.mem_inf]
    exact ⟨eW2_diagKer_le_adjointGroup a hzZ, hzF'⟩
  let zG : G := ⟨z, hzG⟩
  have hzP : z ^ P = 1 := by
    have hdvd_card : orderOf z ∣ Nat.card G := by
      have h : zG ^ Nat.card G = 1 := pow_card_eq_one' (x := zG)
      have h' := map_pow (Subgroup.subtype G) zG (Nat.card G)
      rw [h, map_one] at h'
      have h2 : z ^ Nat.card G = 1 := by simpa using h'.symm
      exact orderOf_dvd_of_pow_eq_one h2
    obtain ⟨n, hn⟩ := hzp
    have hdvd_pn : orderOf z ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd_pn
    have hdvd_m : p ^ j ∣ Nat.card G := by rwa [hj] at hdvd_card
    have hcardG : Nat.card G ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨1, G.one_mem⟩, hfinG⟩
    have hfac : j ≤ (Nat.card G).factorization p := by
      have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero j hp.ne_zero) hcardG).mpr hdvd_m
      have := hle p
      simpa [Nat.Prime.factorization_pow hp] using this
    have hdvd_P : orderOf z ∣ P := by
      rw [hj]
      dsimp only [P]
      exact pow_dvd_pow p hfac
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd_P
  have hFzZ : F z ∈ diagKer τ L (familyKernel a) := by
    let zZ : diagKer τ L (familyKernel a) := ⟨z, hzZ⟩
    have hFz : F z = (γ (zZ ^ 2 ^ e) : ModGL τ L) := hFγ zZ
    rw [hFz]
    exact (γ (zZ ^ 2 ^ e)).2
  have hFz' : (F z) ^ (q ^ Kk) = z ^ q := by
    have h := hkpow z hzZ hzp hzF'
    have hexp : (2 : ℕ) ^ (e * (p * k)) = q ^ Kk := by
      dsimp only [q, Kk]
      rw [pow_mul]
    rwa [hexp] at h
  have hzNZ : z ^ N ∈ diagKer τ L (familyKernel a) :=
    Subgroup.pow_mem (diagKer τ L (familyKernel a)) hzZ N
  have hcomm : Commute (F z) (z ^ N) := eW2_diagKer_mul_comm a hFzZ hzNZ
  have hzNpow : (z ^ N) ^ (q ^ Kk) = z ^ q := by
    rw [← pow_mul]
    exact pow_eq_pow_iff_modEq.2
      (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hzP) hmod)
  have hxc : (F z * (z ^ N)⁻¹) ^ (q ^ Kk) = 1 := by
    rw [Commute.mul_pow hcomm.inv_right, inv_pow, hFz', hzNpow, mul_inv_cancel]
  obtain ⟨n, hn⟩ := hzp
  have hFpn : (F z) ^ (p ^ n) = 1 := by
    rw [← map_pow, hn, map_one]
  have hzNpn : (z ^ N) ^ (p ^ n) = 1 := by
    rw [← pow_mul, mul_comm N (p ^ n), pow_mul, hn, one_pow]
  have hxpn : (F z * (z ^ N)⁻¹) ^ (p ^ n) = 1 := by
    rw [Commute.mul_pow hcomm.inv_right, inv_pow, hFpn, hzNpn, inv_one, mul_one]
  have hcopc : Nat.Coprime (q ^ Kk) (p ^ n) := by
    have h : Nat.Coprime q p := by
      dsimp only [q]
      exact Nat.Coprime.pow_left e h2p
    exact Nat.Coprime.pow Kk n h
  have hx1 : F z * (z ^ N)⁻¹ = 1 := by
    have hdvd_gcd : orderOf (F z * (z ^ N)⁻¹) ∣ Nat.gcd (q ^ Kk) (p ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxc) (orderOf_dvd_of_pow_eq_one hxpn)
    have hgcd : Nat.gcd (q ^ Kk) (p ^ n) = 1 := hcopc.gcd_eq_one
    have hord1 : orderOf (F z * (z ^ N)⁻¹) = 1 := by
      rw [hgcd] at hdvd_gcd
      exact Nat.dvd_one.mp hdvd_gcd
    exact orderOf_eq_one_iff.mp hord1
  have hgoal : F z = z ^ N := mul_inv_eq_one.mp hx1
  rw [hFw]
  exact hgoal

theorem exc_frame_norm
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {ι : Type} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h3D : τ = .D4 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) [Finite ι] {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ) (a : ι → Fin τ.rank → Lˣ)
    (ha : ∀ i j, a i j ^ p = 1)
    (hfix : ∀ i, twFw τ L e Q w (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i))
    (hsat : ∀ v : Fin τ.rank → ℤ, p • v ∈ AddSubgroup.closure (familyKernel a) →
      v ∈ AddSubgroup.closure (familyKernel a))
    (y : ModGL τ L) (hy : y ∈ diagKer τ L (familyKernel a)) (hyp : ∃ n : ℕ, y ^ p ^ n = 1)
    (hyF : twFw τ L e Q w y = y) :
    ∃ z ∈ diagKer τ L (familyKernel a), (∃ n : ℕ, z ^ p ^ n = 1) ∧
      endPow (twFw τ L e Q w) p z = z ∧
      ((List.range p).map fun i => (endPow (twFw τ L e Q w) i) z).prod = y := by
  let Q' : ModGL τ L := canonicalRep (coxeterSystem τ) L w * Q
  have hFw : twFw τ L e Q w = frobTwistGL τ L 2 e Q' := twFw_eq_frobTwistGL e Q w
  have hQT : ∀ t : Fin τ.rank → Lˣ, ∃ t' : Fin τ.rank → Lˣ,
      Q' * rootDiagUnit τ t * Q'⁻¹ = rootDiagUnit τ t' := by
    intro t
    simpa [Q'] using frame_hQT hQ w t
  have hfix' : ∀ i, frobTwistGL τ L 2 e Q' (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i) := by
    intro i
    rw [← hFw]
    exact hfix i
  have hyF' : frobTwistGL τ L 2 e Q' y = y := by
    rw [← hFw]
    exact hyF
  obtain ⟨z, hz, hzpow, hzfix, hzprod⟩ :=
    lemma46_frame_gen hp hp2 a ha e he Q' hQT hfix' hsat y hy hyp hyF'
  refine ⟨z, hz, hzpow, ?_, ?_⟩
  · rw [hFw]
    exact hzfix
  · rw [hFw]
    exact hzprod

private theorem eC7_coe_endPow
                                      {Γ : Type*} [Group Γ] (G : Subgroup Γ)
    (c : Γ →* Γ) (F' : G →* G)
    (hF' : ∀ x : G, ((F' x : G) : Γ) = c x) (n : ℕ) (x : G) :
    ((endPow F' n x : G) : Γ) = endPow c n (x : Γ) := by
  rw [endPow_apply, endPow_apply]
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hF', ih]

theorem exc_frame_central
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ι : Type} (hIdx : ExcIdxFrobInput) (hBor : ExcBorelInput) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h3D : τ = .D4 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) [Finite ι] {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ) (a : ι → Fin τ.rank → Lˣ)
    (ha : ∀ i j, a i j ^ p = 1)
    (hfix : ∀ i, twFw τ L e Q w (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i))
    (hfin : Finite ↥(ratPts τ L (endPow (twFw τ L e Q w) p)))
    (hsat0 : ∀ y ∈ ratPts τ L (twFw τ L e Q w) ⊓ familyGroup a, y ^ p = 1 → y ∈ famSub τ L a) :
    ∀ y ∈ ratPts τ L (endPow (twFw τ L e Q w) p) ⊓ familyGroup a, (∃ n : ℕ, y ^ p ^ n = 1) →
      y ∈ diagKer τ L (familyKernel a) := by
  intro y hy hyPow
  let Q' : ModGL τ L := canonicalRep (coxeterSystem τ) L w * Q
  have hFw : twFw τ L e Q w = frobTwistGL τ L 2 e Q' := twFw_eq_frobTwistGL e Q w
  have hQT : ∀ t : Fin τ.rank → Lˣ, ∃ t' : Fin τ.rank → Lˣ,
      Q' * rootDiagUnit τ t * Q'⁻¹ = rootDiagUnit τ t' := by
    intro t
    simpa [Q'] using frame_hQT hQ w t
  have hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ)
      (n : ModGL τ L), n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n := by
    simpa [Q'] using frame_hQτ hQ w
  have hQfr : entrywiseFrobGL τ L 2 e Q' = Q' := by
    simpa [Q'] using entrywiseFrobGL_frameMatrix hQ w e
  have hfix' : ∀ i, frobTwistGL τ L 2 e Q' (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i) := by
    intro i
    rw [← hFw]
    exact hfix i
  let M : Subgroup (adjointGroup τ L) := famM a
  let Z : Subgroup (adjointGroup τ L) := (famZ a).subgroupOf (adjointGroup τ L)
  let S : Subgroup (adjointGroup τ L) := famS a
  let E : Subgroup (adjointGroup τ L) := (famSub τ L a).subgroupOf (adjointGroup τ L)
  let F₀ : adjointGroup τ L →* adjointGroup τ L := frameEndo e hQτ
  have hF0coe : ∀ g : adjointGroup τ L,
      ((F₀ g : adjointGroup τ L) : ModGL τ L) = frobTwistGL τ L 2 e Q' g :=
    fun g => frameEndo_apply e hQτ g
  have hstruct := central_structure hBor a
  have hstab := central_stability hp hp2 h3 h5 a ha hQT hQτ hfix'
  have hlang := central_lang hBor hp.one_le a he hQfr hQτ hstab.2.1 hstab.2.2
  haveI hfinW : Finite ↥(ratPts τ L (endPow (twFw τ L e Q w) p)) := hfin
  have hfix_le : F₀.eqLocus (MonoidHom.id (adjointGroup τ L)) ≤
      (endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup τ L)) := by
    intro g hg
    show endPow F₀ p g = g
    rw [endPow_apply]
    exact Function.iterate_fixed hg p
  haveI hfinFix : Finite ↥((endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup τ L))) := by
    let g : ↥((endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup τ L))) →
        ↥(ratPts τ L (endPow (twFw τ L e Q w) p)) := fun x =>
      ⟨(x : adjointGroup τ L), by
        rw [ratPts, Subgroup.mem_inf]
        refine ⟨(x : adjointGroup τ L).2, ?_⟩
        show endPow (twFw τ L e Q w) p (x : ModGL τ L) = (x : ModGL τ L)
        have hcoe := eC7_coe_endPow (Γ := ModGL τ L) (adjointGroup τ L)
          (frobTwistGL τ L 2 e Q') (frameEndo e hQτ)
          (fun z => frameEndo_apply e hQτ z) p (x : adjointGroup τ L)
        rw [hFw, ← hcoe]
        exact congrArg Subtype.val x.2⟩
    exact Finite.of_injective g (fun x y hxy => by
      have h : (x : ModGL τ L) = (y : ModGL τ L) :=
        congrArg (fun z : ↥(ratPts τ L (endPow (twFw τ L e Q w) p)) => (z : ModGL τ L)) hxy
      exact Subtype.ext (Subtype.ext h))
  have hEM : ∀ x ∈ E, ∀ m ∈ M, x * m = m * x := by
    intro x hx m hm
    apply Subtype.ext
    show (x : ModGL τ L) * (m : ModGL τ L) = (m : ModGL τ L) * (x : ModGL τ L)
    have hxsub : (x : ModGL τ L) ∈ famSub τ L a := Subgroup.mem_subgroupOf.mp hx
    have hmG : (m : ModGL τ L) ∈ familyGroup a := Subgroup.mem_subgroupOf.mp hm
    have hmAdj : (m : ModGL τ L) ∈ adjointGroup τ L := (m : adjointGroup τ L).2
    have hle : famSub τ L a ≤ Subgroup.centralizer ({(m : ModGL τ L)} : Set (ModGL τ L)) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨i, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h := (mem_familyGroup_iff hp hp2 h3 h5 a ha hmAdj).mp hmG i
      calc (m : ModGL τ L) * rootDiagUnit τ (a i)
          = (rootDiagUnit τ (a i) * (m : ModGL τ L) * (rootDiagUnit τ (a i))⁻¹) *
              rootDiagUnit τ (a i) := by rw [h]
        _ = rootDiagUnit τ (a i) * (m : ModGL τ L) := by group
    exact (Subgroup.mem_centralizer_iff.1 (hle hxsub) _ (Set.mem_singleton _)).symm
  have hsat0prop : ∀ y' ∈ M, F₀ y' = y' → y' ^ p = 1 → y' ∈ E := by
    intro y' hyM hyF hyP
    have hyFam : (y' : ModGL τ L) ∈ familyGroup a := Subgroup.mem_subgroupOf.mp hyM
    have hyadj : (y' : ModGL τ L) ∈ adjointGroup τ L := (y' : adjointGroup τ L).2
    have hyTw : twFw τ L e Q w (y' : ModGL τ L) = (y' : ModGL τ L) := by
      have h := congrArg Subtype.val hyF
      rw [hF0coe y'] at h
      rw [hFw]
      exact h
    have hyP' : (y' : ModGL τ L) ^ p = 1 := by
      simpa using congrArg Subtype.val hyP
    have hmem : (y' : ModGL τ L) ∈ famSub τ L a :=
      hsat0 (y' : ModGL τ L) (by
        rw [Subgroup.mem_inf]
        exact ⟨⟨hyadj, hyTw⟩, hyFam⟩) hyP'
    exact Subgroup.mem_subgroupOf.mpr hmem
  have hcoroot : CorootPSaturated p (familyKernel a) :=
    CFSG.HardMathSupport.C14Coroot.corootPSaturated_of_nonTorsion hp hp2 h3 h5 a
  have hfinF0 : Finite ↥(F₀.eqLocus (MonoidHom.id (adjointGroup τ L))) :=
    Finite.of_injective (Subgroup.inclusion hfix_le) (Subgroup.inclusion_injective hfix_le)
  have hidx : IdxConclusion p a F₀ :=
    hIdx τ L p hp hp2 a e he Q' hQT hQτ F₀ hF0coe hstab.1 hfinF0 hcoroot
  haveI hZS : Finite ↥(Z ⊓ S) := hstruct.2.2.2.2.2
  have hprop := prop43_abstract hp hp2 F₀ M Z S E hstruct.1 hstruct.2.1 hstruct.2.2.1
    hstruct.2.2.2.1 hstruct.2.2.2.2.1 hstab.1 hstab.2.1 hstab.2.2 hlang.1 hlang.2
    hEM hsat0prop hidx
  obtain ⟨hyRat, hyFam⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨hyAdj, hyFix⟩ := Subgroup.mem_inf.mp hyRat
  let y' : adjointGroup τ L := ⟨y, hyAdj⟩
  have hy'M : y' ∈ M := Subgroup.mem_subgroupOf.mpr hyFam
  have hy'F : endPow F₀ p y' = y' := by
    apply Subtype.ext
    have hcoe := eC7_coe_endPow (Γ := ModGL τ L) (adjointGroup τ L)
      (frobTwistGL τ L 2 e Q') (frameEndo e hQτ)
      (fun z => frameEndo_apply e hQτ z) p y'
    rw [hcoe, ← hFw]
    simpa [y'] using hyFix
  have hy'Pow : ∃ n : ℕ, y' ^ p ^ n = 1 := by
    obtain ⟨n, hn⟩ := hyPow
    exact ⟨n, Subtype.ext (by change (y : ModGL τ L) ^ p ^ n = 1; simpa [y'] using hn)⟩
  have hy'Z : y' ∈ Z := hprop y' hy'M hy'F hy'Pow
  exact famZ_le_diagKer a hy'Z

theorem diagKer_central
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {z m : ModGL τ L}
    (hz : z ∈ diagKer τ L (familyKernel a)) (hm : m ∈ familyGroup a) : z * m = m * z := by
  obtain ⟨t, rfl, ht⟩ := hz
  have htorus : torusGroup τ L ≤
      Subgroup.centralizer ({rootDiagUnit τ t} : Set (ModGL τ L)) := by
    intro h hh
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact rootDiagUnit_mul_comm_of_mem_torusGroup t hh
  have hroot : rootSpan τ L (familyKernel a) ≤
      Subgroup.centralizer ({rootDiagUnit τ t} : Set (ModGL τ L)) := by
    show (⨆ α ∈ familyKernel a, rootSubgroup τ L α) ≤ _
    refine iSup₂_le fun α hα => ?_
    show Subgroup.closure (Set.range (pinnedX τ L α)) ≤ _
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hconj := rootDiagUnit_conj_pinnedX t hα.1 c
    rw [ht α hα, Units.val_one, one_mul] at hconj
    calc rootDiagUnit τ t * pinnedX τ L α c
        = (rootDiagUnit τ t * pinnedX τ L α c * (rootDiagUnit τ t)⁻¹) *
            rootDiagUnit τ t := by group
      _ = pinnedX τ L α c * rootDiagUnit τ t := by rw [hconj]
  have hle : familyGroup a ≤
      Subgroup.centralizer ({rootDiagUnit τ t} : Set (ModGL τ L)) := by
    show torusGroup τ L ⊔ rootSpan τ L (familyKernel a) ≤ _
    exact sup_le htorus hroot
  exact Subgroup.mem_centralizer_iff.1 (hle hm) _ (Set.mem_singleton _)

private theorem eF1_diagKer_le_torusGroup
                                   {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (Ψ : Set (Fin τ.rank → ℤ)) :
    diagKer τ L Ψ ≤ torusGroup τ L := by
  intro g hg
  obtain ⟨t, rfl, -⟩ := hg
  exact rootDiagUnit_mem_torusGroup t

private theorem eF1_diagKer_le_adjointGroup
                                   {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (Ψ : Set (Fin τ.rank → ℤ)) :
    diagKer τ L Ψ ≤ adjointGroup τ L :=
  fun _ hg => torusGroup_le_adjointGroup (eF1_diagKer_le_torusGroup Ψ hg)

private theorem eF1_famSub_le_torusGroup
                                   {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    famSub τ L a ≤ torusGroup τ L :=
  (Subgroup.closure_le (torusGroup τ L)).2 fun _ ⟨i, hi⟩ =>
    hi ▸ rootDiagUnit_mem_torusGroup (a i)

private theorem eF1_diagKer_comm_famSub
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {ι : Type} (a : ι → Fin τ.rank → Lˣ) {z : ModGL τ L}
    (hz : z ∈ diagKer τ L (familyKernel a)) :
    ∀ e ∈ famSub τ L a, z * e = e * z := by
  intro e he
  obtain ⟨t, rfl, -⟩ := hz
  exact rootDiagUnit_mul_comm_of_mem_torusGroup t (eF1_famSub_le_torusGroup a he)

private theorem eF1_mem_familyGroup_of_comm
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ι : Type} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5)
    [Finite ι] (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1) {g : ModGL τ L}
    (hga : g ∈ adjointGroup τ L)
    (hg : ∀ i, rootDiagUnit τ (a i) * g * (rootDiagUnit τ (a i))⁻¹ = g) :
    g ∈ familyGroup a := by
  have hmem : g ∈ familyCentralizer τ L a :=
    (mem_familyCentralizer (a := a) (g := g)).2 ⟨hga, hg⟩
  rwa [CFSG.HardMathSupport.C14Lattice.familyCentralizer_eq_familyGroup_of_nonTorsion
    hp hp2 h3 h5 a ha] at hmem

private theorem eF1_mem_diagKer
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ι : Type} (hIdx : ExcIdxFrobInput) (hBor : ExcBorelInput) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h3D : τ = .D4 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) [Finite ι] {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ) (a : ι → Fin τ.rank → Lˣ)
    (ha : ∀ i j, a i j ^ p = 1)
    (hfix : ∀ i, twFw τ L e Q w (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i))
    (hfin : Finite ↥(ratPts τ L (endPow (twFw τ L e Q w) p)))
    (hsat0 : ∀ y ∈ ratPts τ L (twFw τ L e Q w) ⊓ familyGroup a, y ^ p = 1 →
      y ∈ famSub τ L a)
    {u : ModGL τ L}
    (hu : u ∈ pCent p (ratPts τ L (endPow (twFw τ L e Q w) p)) (famSub τ L a)) :
    u ∈ diagKer τ L (familyKernel a) := by
  obtain ⟨huG0, hucomm, hupow⟩ := hu
  have huG := huG0
  rw [ratPts, Subgroup.mem_inf] at huG
  have hfam : u ∈ familyGroup a := by
    apply eF1_mem_familyGroup_of_comm hp hp2 h3 h5 a ha huG.1
    intro i
    have hci := hucomm (rootDiagUnit τ (a i)) (Subgroup.subset_closure (Set.mem_range_self i))
    rw [← hci]; group
  exact exc_frame_central hIdx hBor hp hp2 h3 h3D h5 he hQ w a ha hfix hfin hsat0 u ⟨huG0, hfam⟩ hupow

private theorem eF1_list_prod_pow
                                      {Γ : Type*} [Monoid Γ] (z : Γ) (N n : ℕ) :
    ((List.range n).map fun i => z ^ N ^ i).prod = z ^ (∑ i ∈ Finset.range n, N ^ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.sum_range_succ, pow_add]
    simp

theorem exc_frame_absGeo
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ι : Type} (hIdx : ExcIdxFrobInput) (hBor : ExcBorelInput) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h3D : τ = .D4 → p ≠ 3)
    (h5 : τ = .E8 → p ≠ 5) [Finite ι] {e : ℕ} (he : 1 ≤ e) {Q : ModGL τ L}
    (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ) (a : ι → Fin τ.rank → Lˣ)
    (ha : ∀ i j, a i j ^ p = 1)
    (hfix : ∀ i, twFw τ L e Q w (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i))
    (hfin : Finite ↥(ratPts τ L (endPow (twFw τ L e Q w) p)))
    (hcard : p ^ 2 ≤ Nat.card (famSub τ L a))
    (hsat0 : ∀ y ∈ ratPts τ L (twFw τ L e Q w) ⊓ familyGroup a, y ^ p = 1 → y ∈ famSub τ L a) :
    AbsGeo p (ratPts τ L (endPow (twFw τ L e Q w) p)) (twFw τ L e Q w) (famSub τ L a) := by
  have hsat := exc_frame_hsat hp hp2 h3 h5 a ha hcard
  obtain ⟨N, hN2, hNpow⟩ := exc_frame_power hp hp2 h3 h3D h5 he hQ w a ha hfix hfin
  refine ⟨?_, ?_, N, hN2, ?_, ?_⟩
  · intro u hu v hv
    have huZ := eF1_mem_diagKer hIdx hBor hp hp2 h3 h3D h5 he hQ w a ha hfix hfin hsat0 hu
    have hvZ := eF1_mem_diagKer hIdx hBor hp hp2 h3 h3D h5 he hQ w a ha hfix hfin hsat0 hv
    obtain ⟨tu, rfl, -⟩ := huZ
    obtain ⟨tv, rfl, -⟩ := hvZ
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    exact mul_comm tu tv
  · intro u hu w' hw hwcomm
    rw [ratPts, Subgroup.mem_inf] at hw
    have huZ := eF1_mem_diagKer hIdx hBor hp hp2 h3 h3D h5 he hQ w a ha hfix hfin hsat0 hu
    have hwfam : w' ∈ familyGroup a := by
      apply eF1_mem_familyGroup_of_comm hp hp2 h3 h5 a ha hw.1
      intro i
      have hci := hwcomm (rootDiagUnit τ (a i)) (Subgroup.subset_closure (Set.mem_range_self i))
      rw [← hci]; group
    exact (diagKer_central a huZ hwfam).symm
  · intro u hu
    have huZ := eF1_mem_diagKer hIdx hBor hp hp2 h3 h3D h5 he hQ w a ha hfix hfin hsat0 hu
    obtain ⟨huG0, _, hupow⟩ := hu
    have huG := huG0
    rw [ratPts, Subgroup.mem_inf] at huG
    exact hNpow u huZ hupow huG.2
  · intro y hy hyF
    have hyZ := eF1_mem_diagKer hIdx hBor hp hp2 h3 h3D h5 he hQ w a ha hfix hfin hsat0 hy
    obtain ⟨hyG0, _, hypow⟩ := hy
    obtain ⟨z, hzZ, hzpow, hzfix, hzprod⟩ :=
      exc_frame_norm hp hp2 h3 h3D h5 he hQ w a ha hfix hsat y hyZ hypow hyF
    refine ⟨z, ⟨?_, ?_, hzpow⟩, ?_⟩
    · exact ⟨eF1_diagKer_le_adjointGroup (familyKernel a) hzZ, hzfix⟩
    · exact eF1_diagKer_comm_famSub a hzZ
    · have hNz : twFw τ L e Q w z = z ^ N := hNpow z hzZ hzpow hzfix
      have hmap : (List.range p).map (fun i => (endPow (twFw τ L e Q w) i) z) =
          (List.range p).map (fun i => z ^ N ^ i) := by
        apply List.map_congr_left
        intro i _
        exact endPow_pow hNz i
      have hprod : ((List.range p).map fun i => (endPow (twFw τ L e Q w) i) z).prod =
          z ^ (∑ i ∈ Finset.range p, N ^ i) := by
        rw [hmap, eF1_list_prod_pow]
      rw [← hzprod]
      exact hprod

private lemma eF4_pCent_mem_iff
                                      {p : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ']
    (c : Γ ≃* Γ') {G : Subgroup Γ} {E : Subgroup Γ} {G' : Subgroup Γ'} {E' : Subgroup Γ'}
    (hG : ∀ g, g ∈ G ↔ c g ∈ G') (hE : ∀ g, g ∈ E ↔ c g ∈ E') (u : Γ) :
    c u ∈ pCent p G' E' ↔ u ∈ pCent p G E := by
  simp only [pCent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨huG', hcent', hk⟩
    refine ⟨(hG u).mpr huG', ?_, ?_⟩
    · intro e he
      apply c.injective
      rw [map_mul, map_mul]
      exact hcent' (c e) ((hE e).mp he)
    · obtain ⟨k, hk⟩ := hk
      exact ⟨k, c.injective (by rw [map_pow, map_one]; exact hk)⟩
  · rintro ⟨huG, hcent, hk⟩
    refine ⟨(hG u).mp huG, ?_, ?_⟩
    · intro e' he'
      obtain ⟨e, rfl⟩ := c.surjective e'
      rw [← map_mul, ← map_mul, hcent e ((hE e).mpr he')]
    · obtain ⟨k, hk⟩ := hk
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem absGeo_of_mulEquiv
                                      {p : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ'] (c : Γ ≃* Γ')
    {G : Subgroup Γ} {F₀ : Γ →* Γ} {E : Subgroup Γ} {G' : Subgroup Γ'} {F₁ : Γ' →* Γ'}
    {E' : Subgroup Γ'} (hG : ∀ g, g ∈ G ↔ c g ∈ G') (hF : ∀ g, F₁ (c g) = c (F₀ g))
    (hE : ∀ g, g ∈ E ↔ c g ∈ E') (h : AbsGeo p G' F₁ E') : AbsGeo p G F₀ E := by
  obtain ⟨hcomm, hcent, N, hN2, hpow, hnorm⟩ := h
  refine ⟨?_, ?_, N, hN2, ?_, ?_⟩
  · intro u hu v hv
    apply c.injective
    rw [map_mul, map_mul]
    exact hcomm (c u) ((eF4_pCent_mem_iff c hG hE u).mpr hu) (c v)
      ((eF4_pCent_mem_iff c hG hE v).mpr hv)
  · intro u hu w hw hcw
    apply c.injective
    rw [map_mul, map_mul]
    exact hcent (c u) ((eF4_pCent_mem_iff c hG hE u).mpr hu) (c w) ((hG w).mp hw) fun e' he' => by
      obtain ⟨e, rfl⟩ := c.surjective e'
      rw [← map_mul, ← map_mul, hcw e ((hE e).mpr he')]
  · intro u hu
    apply c.injective
    rw [← hF u, hpow (c u) ((eF4_pCent_mem_iff c hG hE u).mpr hu), map_pow]
  · intro a ha haF
    have hca : c a ∈ pCent p G' E' := (eF4_pCent_mem_iff c hG hE a).mpr ha
    have hcaF : F₁ (c a) = c a := by rw [hF a, haF]
    obtain ⟨b', hb', hb'eq⟩ := hnorm (c a) hca hcaF
    refine ⟨c.symm b', ?_, ?_⟩
    · exact (eF4_pCent_mem_iff c hG hE (c.symm b')).mp (by rwa [c.apply_symm_apply])
    · apply c.injective
      rw [map_pow, c.apply_symm_apply]
      exact hb'eq

theorem excAlgGeoStd_of_frame
    (hM1 : GGLieToralPosition) (hM2 : GGLieLangPosition)
    (hIdx : ExcIdxFrobInput) (hBor : ExcBorelInput) :
    ExcAlgGeoStd := by
  intro L _ _ _ hL p hp hp2 τ h3 h3D h5 e Q he hQ _hSt hfin E hEG hEab hcard hEfix hSat0
  have hEF : E ≤ ratPts τ L (frobTwistGL τ L 2 e Q) := by
    intro x hx
    rw [ratPts, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · have hxG := hEG hx
      rw [ratPts, Subgroup.mem_inf] at hxG
      exact hxG.1
    · show frobTwistGL τ L 2 e Q x = x
      exact hEfix x hx
  obtain ⟨w, h, a, hh, hEa, hF, -⟩ :=
    exc_lang_frame hM1 hM2 hL hp hp2 h3 h5 he hQ hfin hEab hEF
  haveI hfinE : Finite E :=
    Finite.of_injective (Subgroup.inclusion hEG) (Subgroup.inclusion_injective hEG)
  have ha : ∀ i j, a i j ^ p = 1 := by
    intro x j
    have hxp : (x : ModGL τ L) ^ p = 1 := hEab.2 (x : ModGL τ L) x.2
    have h1 : (rootDiagUnit τ (a x)) ^ p = 1 := by
      rw [← hEa x]
      have hconj : h * (x : ModGL τ L) * h⁻¹ = (MulAut.conj h) (x : ModGL τ L) := by
        rw [MulAut.conj_apply]
      rw [hconj, ← map_pow, hxp, map_one]
    have h2 : rootDiagUnit τ ((a x) ^ p) = 1 := by
      have hm := (rootDiagUnitHom τ L).map_pow (a x) p
      change (rootDiagUnitHom τ L) ((a x) ^ p) = 1
      rw [hm]
      exact h1
    have h3 : (a x) ^ p = 1 :=
      rootDiagUnit_injective (by rw [h2, rootDiagUnit_one])
    simpa using congrFun h3 j
  have hfix : ∀ i, twFw τ L e Q w (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i) := by
    intro x
    rw [← hF (rootDiagUnit τ (a x))]
    rw [← hEa x]
    rw [show h⁻¹ * (h * (x : ModGL τ L) * h⁻¹) * h = (x : ModGL τ L) from by group]
    rw [hEfix x x.2]
  let c : ModGL τ L ≃* ModGL τ L := MulAut.conj h
  have hG : ∀ g, g ∈ ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p) ↔
      c g ∈ ratPts τ L (endPow (twFw τ L e Q w) p) := by
    intro g
    rw [ratPts, Subgroup.mem_inf, ratPts, Subgroup.mem_inf]
    constructor
    · rintro ⟨hgadj, hgfix⟩
      refine ⟨?_, ?_⟩
      · show h * g * h⁻¹ ∈ adjointGroup τ L
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hgadj) (Subgroup.inv_mem _ hh)
      · show endPow (twFw τ L e Q w) p (h * g * h⁻¹) = h * g * h⁻¹
        rw [endPow_conj (frobTwistGL τ L 2 e Q) (twFw τ L e Q w) h hF p g]
        have hgfix' : endPow (frobTwistGL τ L 2 e Q) p g = g := hgfix
        rw [hgfix']
    · rintro ⟨hcadj, hcfix⟩
      refine ⟨?_, ?_⟩
      · have hmem : h⁻¹ * (h * g * h⁻¹) * h ∈ adjointGroup τ L :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hcadj) hh
        have heq : h⁻¹ * (h * g * h⁻¹) * h = g := by group
        rwa [heq] at hmem
      · have hcfix' : endPow (twFw τ L e Q w) p (h * g * h⁻¹) = h * g * h⁻¹ := hcfix
        have hconj := endPow_conj (frobTwistGL τ L 2 e Q) (twFw τ L e Q w) h hF p g
        rw [hcfix'] at hconj
        exact (mul_left_cancel (mul_right_cancel hconj)).symm
  have hfinw : Finite ↥(ratPts τ L (endPow (twFw τ L e Q w) p)) := by
    let d : ↥(ratPts τ L (endPow (twFw τ L e Q w) p)) →
        ↥(ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p)) := fun y =>
      ⟨c.symm (y : ModGL τ L), (hG (c.symm (y : ModGL τ L))).mpr (by
        rw [c.apply_symm_apply]; exact y.2)⟩
    refine Finite.of_injective d ?_
    intro y1 y2 hy
    exact Subtype.ext (c.symm.injective (congrArg Subtype.val hy))
  have hgen : ∀ x : E, rootDiagUnit τ (a x) = c x := fun x => (hEa x).symm
  have hrange : Set.range (fun i : E => rootDiagUnit τ (a i)) =
      c.toMonoidHom '' (E : Set (ModGL τ L)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, (hgen i).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hgen ⟨x, hx⟩⟩
  have hmap : famSub τ L a = E.map c.toMonoidHom := by
    apply le_antisymm
    · rw [famSub]
      refine (Subgroup.closure_le _).2 ?_
      rw [hrange]
      exact fun y hy => hy
    · rw [famSub, hrange]
      exact fun y hy => Subgroup.subset_closure hy
  have hE : ∀ g, g ∈ E ↔ c g ∈ famSub τ L a := by
    intro g
    rw [hmap]
    exact (Subgroup.mem_map_iff_mem (f := c.toMonoidHom) c.injective).symm
  have hcard' : p ^ 2 ≤ Nat.card (famSub τ L a) := by
    rw [hmap, Subgroup.card_map_of_injective (f := c.toMonoidHom) c.injective]
    exact hcard
  have hF' : ∀ g, twFw τ L e Q w (c g) = c (frobTwistGL τ L 2 e Q g) := by
    intro g
    show twFw τ L e Q w (h * g * h⁻¹) = h * frobTwistGL τ L 2 e Q g * h⁻¹
    rw [← hF (h * g * h⁻¹)]
    rw [show h⁻¹ * (h * g * h⁻¹) * h = g from by group]
  have hsat0' : ∀ y ∈ ratPts τ L (twFw τ L e Q w) ⊓ familyGroup a, y ^ p = 1 →
      y ∈ famSub τ L a := by
    intro y hy hyP
    set y' : ModGL τ L := h⁻¹ * y * h with hy'def
    have hy_eq : y = c y' := by
      rw [hy'def]
      show y = h * (h⁻¹ * y * h) * h⁻¹
      group
    have hyFw : twFw τ L e Q w y = y := by
      have h := (Subgroup.mem_inf.mp hy).1
      rw [ratPts, Subgroup.mem_inf] at h
      exact h.2
    have hyadj : y ∈ adjointGroup τ L := by
      have h := (Subgroup.mem_inf.mp hy).1
      rw [ratPts, Subgroup.mem_inf] at h
      exact h.1
    have hyfam : y ∈ familyGroup a := (Subgroup.mem_inf.mp hy).2
    have hy'adj : y' ∈ adjointGroup τ L := by
      rw [hy'def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hyadj) hh
    have hy'fix : frobTwistGL τ L 2 e Q y' = y' := by
      have h := hF' y'
      rw [← hy_eq] at h
      rw [hyFw] at h
      rw [hy_eq] at h
      exact (c.injective h).symm
    have hy'pow : y' ^ p = 1 := by
      have hconj : y' = MulAut.conj h⁻¹ y := by rw [hy'def, MulAut.conj_apply, inv_inv]
      rw [hconj, ← map_pow, hyP, map_one]
    have hy'comm : ∀ x ∈ E, y' * x = x * y' := by
      intro x hxE
      let xE : E := ⟨x, hxE⟩
      have hcomm := (mem_familyGroup_iff hp hp2 h3 h5 a ha hyadj).mp hyfam xE
      rw [← hEa xE] at hcomm
      have hconjEq : x * y' * x⁻¹ = y' := by
        have h1 : h⁻¹ * ((h * x * h⁻¹) * y * (h * x * h⁻¹)⁻¹) * h = x * y' * x⁻¹ := by
          rw [hy'def]; group
        have h2 : h⁻¹ * y * h = y' := hy'def.symm
        have hh2 := congrArg (fun t => h⁻¹ * t * h) hcomm
        rw [h1, h2] at hh2
        exact hh2
      have : x * y' = y' * x := by
        calc x * y' = (x * y' * x⁻¹) * x := by group
          _ = y' * x := by rw [hconjEq]
      exact this.symm
    have hy'G : y' ∈ ratPts τ L (endPow (frobTwistGL τ L 2 e Q) p) :=
      ratPts_le_endPow (Φ := frobTwistGL τ L 2 e Q) hp.one_le (by
        rw [ratPts, Subgroup.mem_inf]
        exact ⟨hy'adj, hy'fix⟩)
    have hy'E : y' ∈ E := hSat0 y' hy'G hy'pow hy'comm hy'fix
    rw [hy_eq]
    exact (hE y').mp hy'E
  have hAbs : AbsGeo p (ratPts τ L (endPow (twFw τ L e Q w) p)) (twFw τ L e Q w)
      (famSub τ L a) :=
    exc_frame_absGeo hIdx hBor hp hp2 h3 h3D h5 he hQ w a ha hfix hfinw hcard' hsat0'
  exact absGeo_of_mulEquiv c hG hF' hE hAbs

end CFSG.HardMathSupport.C14Exc
