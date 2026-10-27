module

public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.StarRad
public import CFSG.RankThree.PartOne.TCF.Pow2
public import CFSG.RankThree.PartOne.TCF.Simple

public noncomputable section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.TCF
open scoped commutatorElement

section Basic

@[expose] def SimpleOrBotDvd {G : Type*} [Group G] (m : ℕ) (P : Subgroup G) : Prop :=
  SimpleOrBot P ∧ (P ≠ ⊥ → m ∣ Nat.card P)

theorem simpleOrBotDvd_bot {G : Type*} [Group G] {m : ℕ} : SimpleOrBotDvd m (⊥ : Subgroup G) :=
  ⟨simpleOrBot_bot, fun h => absurd rfl h⟩

theorem SimpleOrBotDvd.map {G H : Type*} [Group G] [Group H] {m : ℕ} {P : Subgroup G}
    (f : G →* H) (hf : Function.Injective f) (h : SimpleOrBotDvd m P) :
    SimpleOrBotDvd m (P.map f) :=
  ⟨h.1.map f hf, fun hne => by
    rw [Subgroup.card_map_of_injective hf]
    exact h.2 fun hP => hne (by rw [hP, Subgroup.map_bot])⟩

theorem SimpleOrBotDvd.of_map {G H : Type*} [Group G] [Group H] {m : ℕ} {P : Subgroup G}
    (f : G →* H) (hf : Function.Injective f) (h : SimpleOrBotDvd m (P.map f)) :
    SimpleOrBotDvd m P :=
  ⟨h.1.of_map f hf, fun hne => by
    have := h.2 fun h0 => hne ((Subgroup.map_eq_bot_iff_of_injective _ hf).1 h0)
    rwa [Subgroup.card_map_of_injective hf] at this⟩

theorem simpleOrBotDvd_of_mulEquiv_simple {G₀ G : Type*} [Group G₀] [Group G] [IsSimpleGroup G₀]
    (hns : ¬ Group.IsSolvable G₀) {P : Subgroup G} (e : G₀ ≃* ↥P) {m : ℕ}
    (hm : m ∣ Nat.card G₀) : SimpleOrBotDvd m P :=
  ⟨simpleOrBot_of_mulEquiv_simple hns e, fun _ => by
    rw [← Nat.card_congr e.toEquiv]
    exact hm⟩

theorem simpleOrBotDvd_range {G₀ G : Type*} [Group G₀] [Group G] [IsSimpleGroup G₀]
    (hns : ¬ Group.IsSolvable G₀) (f : G₀ →* G) (hf : Function.Injective f) {m : ℕ}
    (hm : m ∣ Nat.card G₀) : SimpleOrBotDvd m f.range :=
  simpleOrBotDvd_of_mulEquiv_simple hns (MonoidHom.ofInjective hf) hm

end Basic

section A1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLR

section Dyn

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)
  {i j : Fin ReeTag.F4.tag.rank}

open CFSG.RankThree.Classical (conjSL conjSL_one conjSL_mul)


theorem simpleOrBotDvd_A1Pair [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (h : A1Pair i j) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    SimpleOrBotDvd (Nat.card K - 1) (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n') := by
  classical
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  have hβ : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  have hAB := h.commute_rankOne (L := L)
  have hdisj := h.disjoint (L := L)
  have hspan := h.rootSpan_eq (L := L)
  set A := rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) with hA
  set B := rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) with hB
  have hABle : A ⊔ B ≤ adjointGroup ReeTag.F4.tag L := by
    rw [← hspan]
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _
  have hmul : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B,
      twistMap D.F n' (x * y) = twistMap D.F n' x * twistMap D.F n' y :=
    fun x hx y hy => twistMap_mul n' (hABle hx) (hABle hy)
  have hφA := twistMap_mem_rankOne D hperm hα hβ (fun γ hγ => h.tau_long hstab hγ)
  have hφB := twistMap_mem_rankOne D hperm hβ hα (fun γ hγ => h.tau_short hstab hγ)
  obtain ⟨P₀, hX⟩ := h.exists_twist D hK hn' hperm hstab
  let R : Subgroup (SL2 L) :=
    (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P₀)
  let X : Subgroup (ModGL ReeTag.F4.tag L) :=
    R.map (rootSL2 ReeTag.F4.tag L (Pi.single i 1))
  have hρinj := rootSL2_injective_of_field (K := L) (τ := ReeTag.F4.tag) (Pi.single i 1)
  have hρadj : ∀ B₀ : SL2 L,
      rootSL2 ReeTag.F4.tag L (Pi.single i 1) B₀ ∈ adjointGroup ReeTag.F4.tag L := fun B₀ =>
    (hABle (Subgroup.mem_sup_left ⟨B₀, rfl⟩))
  have hXmem : ∀ x, x ∈ X ↔ x ∈ A ∧ twistMap D.F n' (twistMap D.F n' x) = x := by
    intro x
    constructor
    · rintro ⟨B₀, hB₀, rfl⟩
      refine ⟨⟨B₀, rfl⟩, ?_⟩
      rw [twistMap_twistMap D hn' (hρadj B₀)]
      exact (a1_hS1_of_action D.Frq D.Frq_pow P₀ hX B₀).2 hB₀
    · rintro ⟨⟨B₀, rfl⟩, hfix⟩
      refine ⟨B₀, ?_, rfl⟩
      rw [twistMap_twistMap D hn' (hρadj B₀)] at hfix
      exact (a1_hS1_of_action D.Frq D.Frq_pow P₀ hX B₀).1 hfix
  have hPmem : ∀ g, g ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n' ↔ g ∈ A ⊔ B ∧ twistMap D.F n' g = g := by
    intro g
    rw [hspan]
    constructor
    · rintro ⟨hg, -, hfix⟩
      exact ⟨hg, hfix⟩
    · rintro ⟨hg, hfix⟩
      exact ⟨hg, hABle hg, hfix⟩
  obtain ⟨Θ, hΘinj, hΘr⟩ := fixed_swap hAB hdisj (twistMap D.F n') hmul hφA hφB X hXmem _ hPmem
  have hsimple : IsSimpleGroup (SL2 K) :=
    CFSG.LieType.Ree.LargeReeInvolution.isSimpleGroup_SL2 ha hK
  have hns : ¬ Group.IsSolvable (SL2 K) := by
    obtain ⟨x, y, hxy⟩ := CFSG.LieType.Ree.LargeReeInvolution.exists_SL2_mul_ne_mul (K := K)
    intro hs
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.2 hs) x y)
  have hSLinj :
      Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A₀ B₀ hAB₀
    ext i₀ j₀
    have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) L =>
      (X : Matrix (Fin 2) (Fin 2) L) i₀ j₀) hAB₀
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K L).injective h1
  have hconjinj : Function.Injective (conjSL P₀) := fun A₀ B₀ hAB₀ => by
    have h1 := congrArg (conjSL P₀⁻¹) hAB₀
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  let e1 : SL2 K ≃* R := (MonoidHom.ofInjective hSLinj).trans
    (Subgroup.equivMapOfInjective _ (conjSL P₀) hconjinj)
  let e2 : R ≃* X := Subgroup.equivMapOfInjective R (rootSL2 ReeTag.F4.tag L (Pi.single i 1)) hρinj
  let e3 : X ≃* Θ.range := MonoidHom.ofInjective hΘinj
  let e4 := MulEquiv.subgroupCongr hΘr
  refine simpleOrBotDvd_of_mulEquiv_simple hns (e1.trans (e2.trans (e3.trans e4))) ?_
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact Dvd.dvd.mul_left (by simpa using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2) _


end Dyn

end A1

section B2s

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KLR
open Matrix

section B2

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)

theorem simpleOrBotDvd_B2 [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    SimpleOrBotDvd (Nat.card K - 1) (B2Q L ⊓ twistedFixed D.F n') := by
  classical
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨ω, hω, hε1, hε2⟩ := b2_exists_eps hstab
  have hεW := wordProd_mem_parabolicWeylGroup_b2 (b2Words_letters ω hω)
  set ε := (coxeterSystem ReeTag.F4.tag).wordProd ω with hε
  set m := canonicalRep (coxeterSystem ReeTag.F4.tag) L ε with hm
  have hmQ : m ∈ B2Q L := canonicalRep_mem_subsystemGroup hεW
  have heq : ∀ g ∈ B2Q L, twistMap D.F n' g = twistMap D.F m g := fun g hg =>
    twist_eq_on_B2Q D hperm hε1 hε2 hg
  obtain ⟨S₀, hS₀, hLang⟩ := antiSp_lang_aut L a
  let mQ : B2Q L := ⟨m, hmQ⟩
  let M : antiSp L := B2eQ L mQ
  obtain ⟨h, hh⟩ := hLang M
  let Fm : B2Q L →* B2Q L := (MulAut.conj mQ).toMonoidHom.comp (B2Ftilde D)
  have hFm : ∀ x, B2eQ L (Fm x) = M * S₀ (B2eQ L x) * M⁻¹ := by
    intro x
    show B2eQ L (mQ * B2Ftilde D x * mQ⁻¹) = _
    rw [map_mul, map_mul, map_inv, B2eQ_Ftilde D hS₀]
  let P' : Subgroup (ModGL ReeTag.F4.tag L) := B2Q L ⊓ twistedFixed D.F n'
  let P'₀ : Subgroup (B2Q L) := P'.subgroupOf (B2Q L)
  have hP'₀ : ∀ x : B2Q L, x ∈ P'₀ ↔ Fm x = x := by
    intro x
    have hxad := B2Q_le_adjointGroup x.2
    show (x : ModGL ReeTag.F4.tag L) ∈ P' ↔ _
    constructor
    · rintro ⟨-, -, hfix⟩
      refine Subtype.ext ?_
      show m * Fext D.F x * m⁻¹ = x
      have : twistMap D.F n' x = x := hfix
      rw [heq x x.2] at this
      exact this
    · intro hFx
      refine ⟨x.2, hxad, ?_⟩
      have h1 : m * Fext D.F x * m⁻¹ = x := congrArg Subtype.val hFx
      show twistMap D.F n' x = x
      rw [heq x x.2]
      exact h1
  have hP'eq : P'₀.map (B2Q L).subtype = P' :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_left
  let Y₁ : Subgroup (antiSp L) := P'₀.map (B2eQ L).toMonoidHom
  have hY₁ : ∀ A : antiSp L, A ∈ Y₁ ↔ M * S₀ A * M⁻¹ = A := by
    intro A
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (hP'₀ x).1 hx
      have h2 := hFm x
      rw [h1] at h2
      exact h2.symm
    · intro hA
      refine ⟨(B2eQ L).symm A, (hP'₀ _).2 ?_, by simp⟩
      apply (B2eQ L).injective
      rw [hFm, MulEquiv.apply_symm_apply]
      exact hA
  have hY₂ : ∀ A : antiSp L, A ∈ Y₁.map (MulAut.conj h).toMonoidHom ↔ S₀ A = A := by
    intro A
    constructor
    · rintro ⟨B, hB, rfl⟩
      have hB' := (hY₁ B).1 hB
      rw [hh] at hB'
      show S₀ (h * B * h⁻¹) = h * B * h⁻¹
      rw [map_mul, map_mul, map_inv]
      calc S₀ h * S₀ B * (S₀ h)⁻¹ = h * (h⁻¹ * S₀ h * S₀ B * (h⁻¹ * S₀ h)⁻¹) * h⁻¹ := by group
        _ = h * B * h⁻¹ := by rw [hB']
    · intro hA
      refine ⟨h⁻¹ * A * h, (hY₁ _).2 ?_, ?_⟩
      · rw [hh, map_mul, map_mul, map_inv, hA]
        group
      · show h * (h⁻¹ * A * h) * h⁻¹ = A
        group
  have hrange : Y₁.map (MulAut.conj h).toMonoidHom = (szEmbed hK (algebraMap K L)).range := by
    ext A
    rw [hY₂, fixed_S0_iff_mem_range hK hS₀]
  obtain ⟨-, hnt, hsimp⟩ := suzuki_simple ha hK
  have hperf := (suzuki_perfect ha hK).2
  have hns : ¬ Group.IsSolvable (suzukiGroup a K) := Group.IsPerfect.not_isSolvable _
  have hdvdSz : Nat.card K - 1 ∣ Nat.card (suzukiGroup a K) := by
    rw [suzuki_order hK, hK]
    exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
  have h1 : SimpleOrBotDvd (Nat.card K - 1) (szEmbed hK (algebraMap K L)).range :=
    simpleOrBotDvd_range hns _ (szEmbed_injective hK _) hdvdSz
  rw [← hrange] at h1
  have h2 : SimpleOrBotDvd (Nat.card K - 1) Y₁ :=
    SimpleOrBotDvd.of_map (MulAut.conj h).toMonoidHom (MulAut.conj h).injective h1
  have h3 : SimpleOrBotDvd (Nat.card K - 1) P'₀ :=
    SimpleOrBotDvd.of_map (B2eQ L).toMonoidHom (B2eQ L).injective h2
  have h4 := SimpleOrBotDvd.map (B2Q L).subtype (B2Q L).subtype_injective h3
  rw [hP'eq] at h4
  exact h4


end B2

end B2s

section Star

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLR

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)

theorem simpleOrBotDvd_parabolic_fixed [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w') {J : Finset (Fin ReeTag.F4.tag.rank)} (hJ : BalancedSupport J)
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)),
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
        (J : Set (Fin ReeTag.F4.tag.rank))) :
    SimpleOrBotDvd (Nat.card K - 1) (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (J : Set (Fin ReeTag.F4.tag.rank))) ⊓ twistedFixed D.F n') := by
  rcases hJ with rfl | h02 | h03 | h13 | h12
  · rw [rootSpan_parabolicRoots_empty, bot_inf_eq]
    exact simpleOrBotDvd_bot
  · have hJ : J = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h02 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact simpleOrBotDvd_A1Pair D ha hK a1Pair_zero_two hn' hperm hstab
  · have hJ : J = ({⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h03 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact simpleOrBotDvd_A1Pair D ha hK a1Pair_zero_three hn' hperm hstab
  · have hJ : J = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h13 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    subst hJ
    exact simpleOrBotDvd_A1Pair D ha hK a1Pair_one_three hn' hperm hstab
  · have hJs : (J : Set (Fin ReeTag.F4.tag.rank)) = f4B2Support := by
      ext k
      constructor
      · intro hk
        have hk' := (h12 k).1 hk
        refine (mem_f4B2Support k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · intro hk
        have hk' := (mem_f4B2Support k).1 hk
        refine (h12 k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
    rw [hJs] at hstab ⊢
    rw [← B2Q_eq_rootSpan]
    exact simpleOrBotDvd_B2 D ha hK hperm hstab

theorem starSimpleDvd [IsAlgClosed L] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hord : orderOf (rootDiagUnit ReeTag.F4.tag b) = p)
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    SimpleOrBotDvd (Nat.card K - 1) (rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) := by
  have hbp := pow_eq_one_of_orderOf_rootDiagUnit hord
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hord
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D.isFrob w b).1 hb
  obtain ⟨u, J, hJ, hΦ⟩ := exists_balanced_conj (a := a) hp hp3 hbp hb1 hw
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hst : ∀ β, IsRoot ReeTag.F4.tag β →
      (w • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b) := fun β hβ =>
    mem_kernel_iff_smul_dualRoot hp (by omega) hbp hw hβ
  have hFN : Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u) =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm u) :=
    D.isFrob.fext_canonicalRep u
  have hNad : canonicalRep (coxeterSystem ReeTag.F4.tag) L u ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L u
  have hnad : canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L w
  have hn'ad : canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹ ∈
      adjointGroup ReeTag.F4.tag L :=
    mul_mem (mul_mem hNad hnad) (inv_mem (Fext_mem D.F hNad))
  have hperm : PermAct (canonicalRep (coxeterSystem ReeTag.F4.tag) L u *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
      (Fext D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹)
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) := by
    rw [hFN]
    exact ((permAct_canonicalRep u).mul (permAct_canonicalRep w)).mul
      (permAct_canonicalRep (ReeTag.F4.weylPerm u)).inv
  have key := simpleOrBotDvd_parabolic_fixed D ha hK hn'ad hperm hJ
    (fun γ hγ => smul_dualRoot_mem_parabolic hS w u hst hΦ hγ)
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := D.F) u hS
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
  rw [hΦ] at hmap
  refine SimpleOrBotDvd.of_map
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).injective ?_
  rw [hmap]
  exact key


end Star

section Master

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KLR
open scoped Pointwise commutatorElement

variable {L : Type} [Field L]

section MasterThm

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

@[expose] def StarSimpleDvd (n : ModGL ReeTag.F4.tag L) (S : Set (Fin ReeTag.F4.tag.rank → ℤ)) :
    Prop :=
  SimpleOrBotDvd (Nat.card K - 1) (rootSpan ReeTag.F4.tag L S ⊓ twistedFixed D.F n)

theorem component_data_of_frame_dvd
    {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hconj : ∀ x : ReeTag.F4.reeGamma K a, orderOf x = p →
      ∃ c : ReeTag.F4.reeGamma K a,
        g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ ∈ torusGroup ReeTag.F4.tag L)
    (hrad : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ,
      orderOf (rootDiagUnit ReeTag.F4.tag b) = p →
      rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n →
      StarSimpleDvd D n (rootCharKernel b))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    ∃ N : Subgroup (ReeTag.F4.reeGamma K a),
      N ≤ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) ∧
      (∀ D' : Subgroup (ReeTag.F4.reeGamma K a),
        IsComponentOf (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) D' →
          D' = N) ∧
      (N ≠ ⊥ →
        IsComponentOf (Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a))) N) ∧
      (N ≠ ⊥ → Nat.card K - 1 ∣ Nat.card N) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨c, hcH⟩ := hconj x hx
  let ψ : ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
    ((MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a)).comp (MulAut.conj c).toMonoidHom
  have hψ : ∀ d, ψ d = g₀⁻¹ * thetaGamma L a (c * d * c⁻¹) * g₀ := fun d => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro d₁ d₂ h
    rw [hψ, hψ] at h
    have h1 := mul_left_cancel (mul_right_cancel h)
    have h2 := mul_left_cancel (mul_right_cancel (thetaGamma_injective L h1))
    exact h2
  have hψmem : ∀ d, ψ d ∈ adjointGroup ReeTag.F4.tag L := fun d => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg₀) (thetaGamma_mem_adjointGroup L _)) hg₀
  have hψtw : ∀ d, ψ d ∈ twistedFixed D.F n := fun d => by
    rw [hψ]
    exact conj_mem_twistedFixed D.F hg₀ hFg₀ (thetaGamma_mem_adjointGroup L _) (D.fext_theta _)
  have hy : ψ x = g₀⁻¹ * thetaGamma L a (c * x * c⁻¹) * g₀ := hψ x
  have hyH : ψ x ∈ torusGroup ReeTag.F4.tag L := by rw [hy]; exact hcH
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
  have hordy : orderOf (rootDiagUnit ReeTag.F4.tag b) = p := by
    rw [← hb, orderOf_injective ψ hψinj x]
    exact hx
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hordy
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hordy
  have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨(isRoot_neg_iff).2 hα.1, by rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2]; simp⟩
  have hcommh : ∀ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * ψ d := by
    intro d hd
    rw [← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.1 hd
  have hHQ : ∀ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d ∈ (torusGroup ReeTag.F4.tag L : Set (ModGL ReeTag.F4.tag L)) *
        (rootSpan ReeTag.F4.tag L (rootCharKernel b) : Set (ModGL ReeTag.F4.tag L)) :=
    fun d hd => mem_torus_mul_rootSpan_of_commute hp hordW hap ha1 hS hSn (fun _ h => h)
      (hψmem d) (hcommh d hd)
  have hL2 : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : PerfectRing L 2 := PerfectField.toPerfectRing 2
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃+* L, ∀ c, σ c = c ^ 2 :=
    ⟨frobeniusEquiv L 2, fun c => by simp [frobeniusEquiv_apply, frobenius_def]⟩
  set P : Subgroup (ModGL ReeTag.F4.tag L) :=
    rootSpan ReeTag.F4.tag L (rootCharKernel b) ⊓ twistedFixed D.F n with hP
  have hPψ : ∀ u ∈ P, ∃ d ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)),
      ψ d = u := by
    rintro u ⟨huQ, huT⟩
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀ hFg₀ huT
    obtain ⟨γ, hγ⟩ := D.exists_theta_of_fixed hadj hfix
    have hθc : thetaGamma L a (c * x * c⁻¹) = g₀ * ψ x * g₀⁻¹ := by
      rw [hy]; group
    have huy : u * ψ x = ψ x * u := by
      rw [hb]
      exact Subgroup.mem_centralizer_singleton_iff.1
        (rootSpan_rootCharKernel_le_centralizer b huQ)
    have hcomm : γ * (c * x * c⁻¹) = (c * x * c⁻¹) * γ := by
      apply thetaGamma_injective L
      rw [map_mul (thetaGamma L a) γ (c * x * c⁻¹), map_mul (thetaGamma L a) (c * x * c⁻¹) γ, hγ,
        hθc]
      calc g₀ * u * g₀⁻¹ * (g₀ * ψ x * g₀⁻¹) = g₀ * (u * ψ x) * g₀⁻¹ := by group
        _ = g₀ * (ψ x * u) * g₀⁻¹ := by rw [huy]
        _ = g₀ * ψ x * g₀⁻¹ * (g₀ * u * g₀⁻¹) := by group
    have hd : c⁻¹ * γ * c ∈ Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * γ * c) * x = c⁻¹ * (γ * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * γ) * c := by rw [hcomm]
        _ = x * (c⁻¹ * γ * c) := by group
    refine ⟨c⁻¹ * γ * c, hd, ?_⟩
    rw [hψ, show c * (c⁻¹ * γ * c) * c⁻¹ = γ by group, hγ]
    group
  have hrad' : SimpleOrBotDvd (Nat.card K - 1) P := hrad b hordy (by rw [← hb]; exact hψtw x)
  set C : Subgroup (ReeTag.F4.reeGamma K a) :=
    Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) with hC
  let N : Subgroup (ReeTag.F4.reeGamma K a) := P.comap ψ ⊓ C
  have hNC : N ≤ C := inf_le_right
  have hCN : ⁅C, C⁆ ≤ N := by
    refine Subgroup.commutator_le.2 fun d₁ hd₁ d₂ hd₂ => ?_
    have hdC : ⁅d₁, d₂⁆ ∈ C := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)
    refine ⟨?_, hdC⟩
    show ψ ⁅d₁, d₂⁆ ∈ P
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hT : ψ d₁ * ψ d₂ * (ψ d₁)⁻¹ * (ψ d₂)⁻¹ ∈ twistedFixed D.F n :=
      (twistedFixed D.F n).mul_mem ((twistedFixed D.F n).mul_mem
        ((twistedFixed D.F n).mul_mem (hψtw d₁) (hψtw d₂))
        ((twistedFixed D.F n).inv_mem (hψtw d₁))) ((twistedFixed D.F n).inv_mem (hψtw d₂))
    exact ⟨commutator_mem_rootSpan hS (hHQ d₁ hd₁) (hHQ d₂ hd₂), hT⟩
  have h2 : ∀ g ∈ C, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N := by
    rintro g hg ⟨k, hk⟩
    have h1 : ψ g ^ (2 ^ k) = 1 := by
      rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    exact ⟨⟨mem_rootSpan_of_pow_two_pow_eq_one σ hσ hS (hHQ g hg) h1, hψtw g⟩, hg⟩
  have hNP : N.map ψ = P := by
    ext u
    constructor
    · rintro ⟨d, ⟨hdP, -⟩, rfl⟩
      exact hdP
    · intro hu
      obtain ⟨d, hdC, rfl⟩ := hPψ u hu
      exact ⟨d, ⟨hu, hdC⟩, rfl⟩
  have hNs : SimpleOrBotDvd (Nat.card K - 1) N :=
    SimpleOrBotDvd.of_map ψ hψinj (by rw [hNP]; exact hrad')
  exact ⟨N, hNC, h2, fun D' hD' => component_eq_of_simpleOrBot hNC hCN hNs.1 hD',
    fun hN1 => isComponentOf_of_simpleOrBot hNC hCN hNs.1 hN1, hNs.2⟩

end MasterThm

end Master

end CFSG.RankThree.PartOne.FOC
