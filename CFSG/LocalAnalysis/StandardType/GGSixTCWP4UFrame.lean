module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG3
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGroup
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Untw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.LieType.Chevalley.SingleEdgePerfect
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGLabelIsoField
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType.TableCRes

section Setup

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem charP_two_of_finite_field_card_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hdvd : ringChar K ∣ 2 ^ f := by
    rw [← hK, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ (by exact_mod_cast n.pos.ne')
  have h2 : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hdvd)
  rw [← h2]
  exact ringChar.charP K

theorem exists_langSetup_of_elem
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (y : ↥(adjointGroup τ K)) (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = 2 ^ f ∧ Function.Injective ι ∧ ι.range = S.Γ := by
  classical
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h | h | h | h <;> exact single_edge_perfect τ K (by simp [h])
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h <;> simp [h]) hp hp2
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have h5K : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  obtain ⟨S, a, ι, hq, -, -, -, -, hinj, hrange, -⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ' hp hpK Nat.prime_five h5K (Or.inl le_rfl) hmon
      hperf (MulAut.conj y) (y : ModGL τ K)
      (baseChangeGL_mem_adjointGroup _ y.2) (fun c => by simp) (by
        rw [← Subgroup.coe_pow, hyp]; rfl) (fun h => hy1 (Subtype.ext h))
  exact ⟨S, ι, hq.trans hK, hinj, hrange⟩

end Setup

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Conj

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem model_eq_map_of_step
    (S S₁ : LangSetup τ L p₀) {g : ModGL τ L}
    (hg : g ∈ adjointGroup τ L)
    (hstep : S₁.D.step = (MulAut.conj g⁻¹).toMonoidHom.comp
      (S.D.step.comp (MulAut.conj g).toMonoidHom)) :
    S₁.D.model = S.D.model.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hs : ∀ y, S₁.D.step y = g⁻¹ * S.D.step (g * y * g⁻¹) * g := by
    intro y
    rw [hstep]
    simp
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    obtain ⟨hya, hys⟩ := (LangDatum.mem_model (D := S₁.D)).1 hy
    refine ⟨g * y * g⁻¹, ?_, by simp [mul_assoc]⟩
    refine (LangDatum.mem_model (D := S.D)).2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hg hya) (inv_mem hg)
    · have h1 : S₁.D.step y = y := hys
      rw [hs] at h1
      have h2 : S.D.step (g * y * g⁻¹) = g * y * g⁻¹ := by
        have := congrArg (fun z => g * z * g⁻¹) h1
        simpa [mul_assoc] using this
      exact h2
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hza, hzs⟩ := (LangDatum.mem_model (D := S.D)).1 hz
    refine (LangDatum.mem_model (D := S₁.D)).2 ⟨?_, ?_⟩
    · simpa using mul_mem (mul_mem (inv_mem hg) hza) hg
    · have h3 : S₁.D.step ((MulAut.conj g⁻¹).toMonoidHom z) = (MulAut.conj g⁻¹).toMonoidHom z := by
        rw [hs]
        have : g * ((MulAut.conj g⁻¹).toMonoidHom z) * g⁻¹ = z := by simp [mul_assoc]
        rw [this]
        have h4 : S.D.step z = z := hzs
        rw [h4]
        simp [mul_assoc]
      exact h3

theorem gamma_eq_map_of_step
    (S S₁ : LangSetup τ L p₀) {g : ModGL τ L}
    (hg : g ∈ adjointGroup τ L)
    (hstep : S₁.D.step = (MulAut.conj g⁻¹).toMonoidHom.comp
      (S.D.step.comp (MulAut.conj g).toMonoidHom)) :
    S₁.Γ = S.Γ.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hm := model_eq_map_of_step S S₁ hg hstep
  change ⁅S₁.D.model, S₁.D.model⁆ = (⁅S.D.model, S.D.model⁆).map _
  rw [hm, Subgroup.map_commutator]

end Conj

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Frame

variable {τ : Tag} {L : Type} [Field L] {X : Type} [Group X]

structure GGTCUFrame (Γ : Subgroup (ModGL τ L)) (G₀ B : Subgroup X) where
  ν : ↥B →* ↥G₀ ⧸ Subgroup.center ↥G₀
  inj : Function.Injective ν
  act : ∀ b : ↥B, ∃ n : ↥G₀, (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) = ν b ∧
    ∀ y : ↥G₀, (b : X) * (y : X) * (b : X)⁻¹ = (n : X) * (y : X) * (n : X)⁻¹
  Θ : (↥G₀ ⧸ Subgroup.center ↥G₀) ≃* ↥Γ

namespace GGTCUFrame

variable {Γ : Subgroup (ModGL τ L)} {G₀ B : Subgroup X} (fr : GGTCUFrame Γ G₀ B)

@[expose] noncomputable def embLang : (↥G₀ ⧸ Subgroup.center ↥G₀) →* ModGL τ L :=
  Γ.subtype.comp fr.Θ.toMonoidHom

theorem embLang_injective : Function.Injective fr.embLang :=
  fun _ _ h => fr.Θ.injective (Subtype.ext h)

theorem range_embLang : fr.embLang.range = Γ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (fr.Θ y).2
  · intro hx
    obtain ⟨y, hy⟩ := fr.Θ.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

@[expose] noncomputable def toLang : ↥B →* ModGL τ L := fr.embLang.comp fr.ν

theorem toLang_injective : Function.Injective fr.toLang :=
  fun _ _ h => fr.inj (fr.embLang_injective h)

@[expose] noncomputable def BLang : Subgroup (ModGL τ L) := fr.toLang.range

@[expose] noncomputable def DLang (D : Subgroup X) : Subgroup (ModGL τ L) :=
  ((D.subgroupOf B).map fr.ν).map fr.embLang

@[expose] noncomputable def JLang (J : Subgroup X) : Subgroup (ModGL τ L) :=
  ((J.subgroupOf G₀).map (QuotientGroup.mk' (Subgroup.center ↥G₀))).map fr.embLang

theorem card_BLang : Nat.card fr.BLang = Nat.card B :=
  (Nat.card_congr (MonoidHom.ofInjective fr.toLang_injective).toEquiv).symm

theorem DLang_le_BLang {D : Subgroup X} : fr.DLang D ≤ fr.BLang := by
  rintro _ ⟨_, ⟨d, _, rfl⟩, rfl⟩
  exact ⟨d, rfl⟩

theorem card_DLang {D : Subgroup X} (hDB : D ≤ B) : Nat.card (fr.DLang D) = Nat.card D := by
  rw [DLang, Subgroup.card_map_of_injective fr.embLang_injective,
    Subgroup.card_map_of_injective fr.inj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv


theorem isComponentOf_JLang {D J : Subgroup X} (hDB : D ≤ B) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))) :
    IsComponentOf (fr.JLang J)
      (Γ ⊓ Subgroup.centralizer ((fr.DLang D : Subgroup (ModGL τ L)) : Set (ModGL τ L))) := by
  have h1 : IsComponentOf (J.subgroupOf G₀)
      ((G₀ ⊓ Subgroup.centralizer (D : Set X)).subgroupOf G₀) :=
    isComponentOf_subgroupOf_of_le hJ hJG
  rw [centralizer_eq_of_inner_action hDB fr.ν fr.act] at h1
  have h2 := isComponentOf_map_centralizer_central
    (Z := Subgroup.center ↥G₀) le_rfl _ h1
  rw [image_eq_of_inner_action fr.ν fr.act] at h2
  have h3 := isComponentOf_map_injective fr.embLang fr.embLang_injective h2
  rw [map_centralizer_of_injective_range fr.embLang fr.embLang_injective, fr.range_embLang] at h3
  exact h3

theorem le_DLang_of_commute {D J : Subgroup X} (hJG : J ≤ G₀)
    (hJ : commutator ↥J = ⊤) (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D) :
    fr.BLang ⊓ Subgroup.centralizer ((fr.JLang J : Subgroup (ModGL τ L)) : Set (ModGL τ L)) ≤
      fr.DLang D := by
  rintro _ ⟨hB, hC⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨n, hn1, hn2⟩ := fr.act b
  have hcomm : ∀ j : ↥G₀, (j : X) ∈ J →
      fr.ν b * QuotientGroup.mk j = QuotientGroup.mk j * fr.ν b := by
    intro j hj
    have hjm : fr.embLang (QuotientGroup.mk j) ∈ fr.JLang J :=
      ⟨_, ⟨j, (Subgroup.mem_subgroupOf.2 hj), rfl⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hC _ hjm
    apply fr.embLang_injective
    simpa [toLang, map_mul] using this.symm
  have hbJ : (b : X) ∈ Subgroup.centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have := commute_of_inner_action_on_perfect hJG hJ hn2 (hn1 ▸ hcomm) j hj
    exact this.symm
  have hbD : (b : X) ∈ D := by
    rw [← hcent]
    exact Subgroup.mem_inf.2 ⟨b.2, hbJ⟩
  exact ⟨fr.ν b, ⟨b, Subgroup.mem_subgroupOf.2 hbD, rfl⟩, rfl⟩

theorem isElemAbelian_BLang {p : ℕ} (hBel : IsElemAbelian p B) : IsElemAbelian p fr.BLang := by
  have h1 : IsElemAbelian p (B.subgroupOf B) := hBel.subgroupOf B
  rw [Subgroup.subgroupOf_self] at h1
  have h2 := h1.map fr.toLang
  rwa [Subgroup.map_top] at h2

@[expose] noncomputable def mapEquivΓ {Γ' : Subgroup (ModGL τ L)} (e : ↥Γ ≃* ↥Γ') :
    GGTCUFrame Γ' G₀ B where
  ν := fr.ν
  inj := fr.inj
  act := fr.act
  Θ := fr.Θ.trans e

theorem nonempty_equiv_JLang {J : Subgroup X} (hJG : J ≤ G₀) (hJq : CFSG.Open.IsQuasisimple ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥(fr.JLang J) ⧸ Subgroup.center ↥(fr.JLang J)) := by
  have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJq.1
  have hperf0 : Group.IsPerfect ↥(J.subgroupOf G₀) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJG).symm.surjective
  obtain ⟨q2⟩ := centerQuot_equiv_map_central (Z := Subgroup.center ↥G₀) le_rfl hperf0
  exact ⟨(centerQuotMulEquivOfEquiv (Subgroup.subgroupOfEquivOfLe hJG).symm).trans
    (q2.trans (centerQuotMulEquivOfEquiv
      (Subgroup.equivMapOfInjective _ fr.embLang fr.embLang_injective)))⟩

end GGTCUFrame

end Frame

section FieldExtOpen

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Blueprint
open scoped commutatorElement

section FieldExt

theorem center_quot_eq_bot_of_isQuasisimple {Y : Type*} [Group Y]
    (hY : CFSG.Open.IsQuasisimple Y) : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  obtain ⟨hperf, hsimple⟩ := hY
  by_contra hne
  have htop : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊤ :=
    (hsimple.eq_bot_or_eq_top_of_normal _).resolve_left hne
  have hcomm : commutator Y ≤ Subgroup.center Y := by
    rw [commutator]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    have h1 : (QuotientGroup.mk (⁅a, b⁆) : Y ⧸ Subgroup.center Y) = 1 := by
      have hc := Subgroup.mem_center_iff.1 (htop ▸ Subgroup.mem_top (QuotientGroup.mk a))
        (QuotientGroup.mk b)
      rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hc]
      group
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hZ : Subgroup.center Y = ⊤ := top_le_iff.1 (hperf ▸ hcomm)
  have := hsimple.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Y ⧸ Subgroup.center Y)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx ((QuotientGroup.eq_one_iff y).2 (hZ ▸ Subgroup.mem_top y))

theorem two_le_of_fieldExt
    {X Y : Type} [Group X] [Group Y] {J : Subgroup X} {J' : Subgroup Y}
    (hJ : CFSG.Open.IsQuasisimple ↥J)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* (↥J' ⧸ Subgroup.center ↥J'))
    {f k : ℕ} (hfield : GGCompFieldAt (2 ^ (f * k)) J')
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f') : 2 ≤ k := by
  obtain ⟨lab, hlab, -, hdeg, -, -, -, hhas, -⟩ := hfield
  obtain ⟨t', m, f', hlt, hmod⟩ := hF
  have hcen : Subgroup.center (↥J ⧸ Subgroup.center ↥J) = ⊥ :=
    center_quot_eq_bot_of_isQuasisimple hJ
  obtain ⟨lab', hlab', -, -, -, hdeg', hraw'⟩ := exists_label_rawDatum_of_lieModel hcen hmod
  have h1 : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := ggHasLabel_of_mulEquiv e.symm hhas
  have h2 : GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) := hraw'
  have hdeq := markDeg_eq_of_ggLabelIso (ggLabelRigidInput_holds lab lab' _ hlab hlab' h1 h2)
  have hpow : markDeg lab = f * k := Nat.pow_right_injective (le_refl 2) hdeg
  by_contra hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl <;> simp at hpow <;> omega

end FieldExt

end FieldExtOpen

section Conclusion

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def UFieldInput
    (τ : Tag) :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ p : ℕ) (S : LangSetup τ L p₀),
    p.Prime → p ≠ 2 → ∀ (ι : Type) (a : ι → Fin τ.rank → Lˣ),
      (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) → (∀ u j, a u j ^ p = 1) →
      ∀ K : Subgroup (ModGL τ L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) →
        ∃ i : KernelComponent (famCharHom a),
          K ≤ rootSpan τ L (famOrbit S.ρ a i) ∧
          GGCompFieldAt (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)) K

@[expose] def UToralAt
    (τ : Tag) (p n : ℕ)
     : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (A : Subgroup (ModGL τ (AlgebraicClosure K))),
    A ≤ adjointGroup τ (AlgebraicClosure K) → IsElemAbelian p A → Nat.card A = n →
    ∃ g ∈ adjointGroup τ (AlgebraicClosure K),
      ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ (AlgebraicClosure K)

section Main

theorem exists_uframe
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D : Subgroup X} {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) τ (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S : LangSetup τ (AlgebraicClosure K) 5), S.D.q = 2 ^ f ∧ Nonempty (GGTCUFrame S.Γ G₀ B) := by
  classical
  obtain ⟨K, instF, instFin, hKcard, ⟨eK⟩⟩ := hmod
  have : CharP K 2 := charP_two_of_finite_field_card_two_pow hKcard
  have hZadj : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let θ : (↥G₀ ⧸ Subgroup.center ↥G₀) ≃* ↥(adjointGroup τ K) :=
    eK.trans ((QuotientGroup.quotientMulEquivOfEq hZadj).trans QuotientGroup.quotientBot)
  have hcl : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥ := by
    have h1 := Subgroup.map_center_eq θ
    rw [hZadj] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h1
  obtain ⟨ν, hνinj, hνact⟩ := exists_inner_hom_of_faithful_inner hBN hin hfaith hcl
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    have h2 := hp.two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  let b₀ : ↥B := ⟨(x : X), hDB x.2⟩
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    apply hx1
    have h' : (x : X) = 1 := congrArg (fun z : ↥B => (z : X)) h
    exact Subtype.ext h'
  have hb₀p : b₀ ^ p = 1 := Subtype.ext (hBel.2 (x : X) (hDB x.2))
  have hy1 : θ (ν b₀) ≠ 1 := fun h => hb₀1 (hνinj (θ.injective (by rw [h, map_one, map_one])))
  have hyp : θ (ν b₀) ^ p = 1 := by rw [← map_pow, ← map_pow, hb₀p, map_one, map_one]
  obtain ⟨S, ι, hq, hinj, hrange⟩ := exists_langSetup_of_elem hτ hKcard hp hp2 (θ (ν b₀)) hy1 hyp
  exact ⟨K, instF, instFin, inferInstance, S, hq, ⟨⟨ν, hνinj, hνact,
    θ.trans ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩⟩⟩

theorem exists_torus_uframe
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B : Subgroup X} [Finite B] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] (S : LangSetup τ (AlgebraicClosure K) 5)
    (fr : GGTCUFrame S.Γ G₀ B) (hBel : IsElemAbelian p B) (htor : UToralAt τ p (Nat.card B)) :
    ∃ S₁ : LangSetup τ (AlgebraicClosure K) 5, S₁.D.q = S.D.q ∧
      ∃ fr₁ : GGTCUFrame S₁.Γ G₀ B, fr₁.BLang ≤ S₁.D.torus := by
  classical
  have : Finite fr.BLang := Finite.of_equiv _ (MonoidHom.ofInjective fr.toLang_injective).toEquiv
  have hBΓ : fr.BLang ≤ S.Γ := by
    rintro _ ⟨b, rfl⟩
    exact (fr.Θ (fr.ν b)).2
  have hΓmodel : S.Γ ≤ S.D.model := by
    change ⁅S.D.model, S.D.model⁆ ≤ S.D.model
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hBmodel : fr.BLang ≤ S.D.model := hBΓ.trans hΓmodel
  have hBadj : fr.BLang ≤ adjointGroup τ (AlgebraicClosure K) := hBmodel.trans inf_le_left
  have hBimgel : IsElemAbelian p fr.BLang := fr.isElemAbelian_BLang hBel
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨g, hg, hgx⟩ := htor K fr.BLang hBadj hBimgel fr.card_BLang
  obtain ⟨g₁, hg₁, S₁, -, hq₁, hstep, -, htorus, -, -⟩ :=
    ggTCInputG3Toral_holds τ (AlgebraicClosure K) 5 S hτ p hp hp2 fr.BLang hBmodel hBimgel
      ⟨g, hg, hgx⟩
  have hΓ := gamma_eq_map_of_step S S₁ hg₁ hstep
  let e : ↥S.Γ ≃* ↥S₁.Γ :=
    (MulEquiv.subgroupMap (MulAut.conj g₁⁻¹) S.Γ).trans (MulEquiv.subgroupCongr hΓ.symm)
  refine ⟨S₁, hq₁, fr.mapEquivΓ e, ?_⟩
  rintro _ ⟨b, rfl⟩
  have hlang : (fr.mapEquivΓ e).toLang b = g₁⁻¹ * fr.toLang b * g₁ := by
    change (MulAut.conj g₁⁻¹) ((fr.Θ (fr.ν b) : ↥S.Γ) : ModGL τ (AlgebraicClosure K)) = _
    rw [MulAut.conj_apply, inv_inv]
    rfl
  rw [hlang]
  exact htorus _ ⟨b, rfl⟩

theorem uframe_conclude
    {τ : Tag} (hField : UFieldInput τ)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] (S₁ : LangSetup τ (AlgebraicClosure K) 5)
    (hq : S₁.D.q = 2 ^ f) (fr₁ : GGTCUFrame S₁.Γ G₀ B) (hBT : fr₁.BLang ≤ S₁.D.torus)
    (hBel : IsElemAbelian p B) (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f') :
    ∃ (Ψ : Set (Fin τ.rank → ℤ)),
      IsRootComponent Ψ ∧
      (∀ γ ∈ Ψ, ∀ δ ∈ (S₁.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ,
        iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ)) ∧
      Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ Ψ)) ∧
      2 * Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ τ.rank := by
  classical
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hBel₁ : IsElemAbelian p fr₁.BLang := fr₁.isElemAbelian_BLang hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite fr₁.BLang := Finite.of_equiv _ (MonoidHom.ofInjective fr₁.toLang_injective).toEquiv
  have hD₁B : fr₁.DLang D ≤ fr₁.BLang := fr₁.DLang_le_BLang
  have hpar : ∀ u : fr₁.DLang D, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := fun u =>
    exists_param_of_torus (hBT (hD₁B u.2)).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit τ (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hBT (hD₁B u.2)
  have hrange : (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u)) =
      ((fr₁.DLang D : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit τ (a u) ∈ (fr₁.DLang D : Set (ModGL τ (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JLang J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u))) := by
    rw [hrange]
    exact fr₁.isComponentOf_JLang hDB hJG hJ
  obtain ⟨i, hspan, hfield⟩ :=
    hField (AlgebraicClosure K) 5 p S₁ hp hp2 (fr₁.DLang D) a haT hap (fr₁.JLang J) hcomp
  rw [hq, ← pow_mul] at hfield
  have h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) :=
    two_le_of_fieldExt hJ.2.2 (fr₁.nonempty_equiv_JLang hJG hJ.2.2).some hfield hF
  have hC := fr₁.le_DLang_of_commute hJG hJ.2.2.1 hcent
  have hcard := card_le_of_famChar S₁ fr₁.BLang (fr₁.DLang D) (fr₁.JLang J) hBT hBel₁.2 hD₁B a i
    hspan hC
  refine ⟨componentRoots (famCharHom a) i, isRootComponent_componentRoots i, ?_, ?_,
    two_mul_finrank_le_of_orbit S₁ a haT i h2⟩
  · obtain ⟨j, hj⟩ := exists_image_component_of_stable (famCharHom a)
      (fun γ hγ => rho_mem_kernelRoots_famChar S₁ a haT hγ) S₁.frob.iform_eq i
    have hij : i ≠ j := by
      rintro rfl
      exact image_ne_of_two_le_componentOrbitLength h2 hj
    intro γ hγ δ hδ
    rw [hj] at hδ
    refine ⟨iform_eq_zero_of_mem_componentRoots' hij hγ hδ, ?_⟩
    obtain ⟨hγk, hγi⟩ := hγ
    obtain ⟨hδk, hδi⟩ := hδ
    have := not_isRoot_of_mk_ne (χ := famCharHom a) (α := ⟨γ, hγk⟩) (β := ⟨δ, hδk⟩)
      (by rw [hγi, hδi]; exact hij) one_pos one_pos
    simpa using this
  · calc Nat.card B = Nat.card fr₁.BLang := fr₁.card_BLang.symm
      _ ≤ Nat.card (fr₁.DLang D) *
          p ^ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := hcard
      _ = p ^ (2 + Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i))) := by
        rw [fr₁.card_DLang hDB, hDcard, pow_add]

theorem uframe_main
    {τ : Tag} (hField : UFieldInput τ)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) τ (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (htor : UToralAt τ p (Nat.card B)) :
    ∃ (Ψ : Set (Fin τ.rank → ℤ)) (ρ : Equiv.Perm (Fin τ.rank → ℤ)),
      IsRootComponent Ψ ∧ (∀ γ, IsRoot τ (ρ γ) ↔ IsRoot τ γ) ∧
      (∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) ∧
      (∀ γ ∈ Ψ, ∀ δ ∈ (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ,
        iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ)) ∧
      Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ Ψ)) ∧
      2 * Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ τ.rank := by
  obtain ⟨K, instF, instFin, instChar, S, hq, ⟨fr⟩⟩ :=
    exists_uframe hτ hp hp2 hmod hBN hin hfaith hBel hDB hDcard
  obtain ⟨S₁, hq₁, fr₁, hBT⟩ := exists_torus_uframe hτ hp hp2 S fr hBel htor
  obtain ⟨Ψ, hΨ, horth, hcard, h2r⟩ :=
    uframe_conclude hField hp hp2 S₁ (hq₁.trans hq) fr₁ hBT hBel hDB hDcard hJG hJ hcent hF
  exact ⟨Ψ, S₁.ρ, hΨ, S₁.frob.isRoot_iff, S₁.frob.iform_eq, horth, hcard, h2r⟩

end Main

end Conclusion

end CFSG.StandardType.TableCRes
