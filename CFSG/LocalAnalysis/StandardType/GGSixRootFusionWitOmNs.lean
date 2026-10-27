module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmNsCore
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmRest
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaPM
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

namespace WitOmNs

open Module QuadraticMap CFSG.RankThree.Classical2

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem bstar_preimage {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    {Ω : Subgroup (V ≃ₗ[K] V)} {φ : ↥Ω →* G} (hφ : Function.Injective φ) (hBφ : Bs ≤ φ.range) :
    (∀ a ∈ (Bs.comap φ).map Ω.subtype, ∀ b ∈ (Bs.comap φ).map Ω.subtype, a * b = b * a) ∧
      (∀ a ∈ (Bs.comap φ).map Ω.subtype, a ^ p = 1) ∧
      Nat.card ((Bs.comap φ).map Ω.subtype) = Nat.card Bs := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨Y, hY, rfl⟩ _ ⟨Y', hY', rfl⟩
    have h1 : φ (Y * Y') = φ (Y' * Y) := by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hBs hY hY'
    exact congrArg Subtype.val (hφ h1)
  · rintro _ ⟨Y, hY, rfl⟩
    have h1 : φ (Y ^ p) = 1 := by rw [map_pow]; exact hBs.2 _ hY
    have h2 : Y ^ p = 1 := hφ (h1.trans (map_one φ).symm)
    show ((Y : V ≃ₗ[K] V)) ^ p = 1
    rw [← SubgroupClass.coe_pow, h2, OneMemClass.coe_one]
  · rw [Subgroup.card_map_of_injective Ω.subtype_injective]
    have e := (Bs.comap φ).equivMapOfInjective φ hφ
    rw [Nat.card_congr e.toEquiv, Subgroup.map_comap_eq_self hBφ]

theorem exists_witness_grp (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (h10 : 10 ≤ finrank K V)
    {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K + 1) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hcard : p ^ 2 ≤ Nat.card Bs)
    (φ : ↥(orthDerived Q) →* G) (hφ : Function.Injective φ) (hBφ : Bs ≤ φ.range) {s : G}
    (hs : s ∈ φ.range)
    (hs2 : orderOf s = 2) :
    ∃ y : G, y * s = s * y ∧ ∃ m ∈ φ.range, m * y * m⁻¹ ∈ Bs ∧ m * y * m⁻¹ ≠ 1 ∧
      ∃ L₁ : Subgroup G, IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer {m * y * m⁻¹}) ∧
        Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  have := LayerCores.finite_linearEquiv (K := K) (V := V)
  set A : Subgroup (V ≃ₗ[K] V) := (Bs.comap φ).map (orthDerived Q).subtype with hA
  have hmemA : ∀ a, a ∈ A ↔ ∃ Y : orthDerived Q, φ Y ∈ Bs ∧ (Y : V ≃ₗ[K] V) = a := fun a => Iff.rfl
  have hAΩ : A ≤ orthDerived Q := Subgroup.map_subtype_le _
  obtain ⟨hAc, hAp, hcardA⟩ := bstar_preimage hBs hφ hBφ
  have hAmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A := by
    intro g hg hgp hcomm
    refine ⟨⟨g, hg⟩, hSC _ ?_ ?_, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨Y, rfl⟩ := hBφ hb
      have h1 := hcomm (Y : V ≃ₗ[K] V) ⟨Y, hb, rfl⟩
      have h2 : (⟨g, hg⟩ : orthDerived Q) * Y = Y * ⟨g, hg⟩ := Subtype.ext h1
      rw [← map_mul, ← map_mul, h2]
    · have h1 : (⟨g, hg⟩ : orthDerived Q) ^ p = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow]
        exact hgp)
      rw [← map_pow, h1, map_one]
  obtain ⟨v, rfl⟩ := hs
  have hvv : v * v = 1 := by
    have h2 := pow_orderOf_eq_one (φ v)
    rw [hs2, pow_two, ← map_mul] at h2
    exact hφ (by rw [h2, map_one])
  have hv1 : (v : V ≃ₗ[K] V) ≠ 1 := by
    intro h
    have h1 : v = 1 := Subtype.ext h
    rw [h1, map_one, orderOf_one] at hs2
    norm_num at hs2
  obtain ⟨d, hdA, hd1, g, hg, hcommt, Lp, hLq, hLΩ, hLd, hLn, hcount⟩ :=
    exists_witness_lin hQ hT h10 hp hpK hAΩ hAc hAp hAmax (hcardA ▸ hcard)
      (Subgroup.commutator_le_self _ v.2) (congrArg Subtype.val hvv) hv1
  obtain ⟨d', hd'B, rfl⟩ := (hmemA d).mp hdA
  set g' : orthDerived Q := ⟨g, hg⟩ with hg'
  refine ⟨φ (g' * d' * g'⁻¹), ?_, φ g'⁻¹, ⟨_, rfl⟩, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcommt
  have hconj : φ g'⁻¹ * φ (g' * d' * g'⁻¹) * (φ g'⁻¹)⁻¹ = φ d' := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [hconj]
  refine ⟨hd'B, fun h => hd1 (by
    have h2 : d' = 1 := hφ (h.trans (map_one φ).symm)
    rw [h2]
    rfl), ?_⟩
  set L₁ : Subgroup G := (Lp.subgroupOf (orthDerived Q)).map φ with hL₁
  have hmemL : ∀ x : orthDerived Q,
      x ∈ Lp.subgroupOf (orthDerived Q) ↔ (x : V ≃ₗ[K] V) ∈ Lp := fun x =>
    Subgroup.mem_subgroupOf
  have hle : L₁ ≤ φ.range ⊓ Subgroup.centralizer {φ d'} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : x * d' = d' * x := Subtype.ext (hLd _ ((hmemL x).mp hx))
    rw [← map_mul, ← map_mul, h1]
  have hUq : CFSG.IsQuasisimple ↥(Lp.subgroupOf (orthDerived Q)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLΩ).symm hLq
  have hker : φ.ker ≤ Subgroup.center ↥(orthDerived Q) := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ]
    exact bot_le
  have hL₁q := SURepair.isQuasisimple_map_of_isQuasisimple hker hUq
  refine ⟨L₁, ⟨hle, ?_, hL₁q⟩, ?_⟩
  · refine IsSubnormal.step hle ?_ (IsSubnormal.refl _)
    rw [Subgroup.normal_subgroupOf_iff hle]
    rintro _ k ⟨x, hx, rfl⟩ ⟨⟨c, rfl⟩, hkc⟩
    have hcd : c * d' = d' * c := hφ (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hkc
      rw [map_mul, map_mul]
      exact this)
    refine ⟨c * x * c⁻¹, (hmemL _).mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact hLn c (Subgroup.commutator_le_self _ c.2) (congrArg Subtype.val hcd) x
      ((hmemL x).mp hx)
  ·
    have hpre : ∀ c : ↥(Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G),
        ∃ Y : orthDerived Q, φ Y = c := fun c => hBφ c.2.1
    choose Y hY using hpre
    have hYA : ∀ c, (Y c : V ≃ₗ[K] V) ∈ A := fun c =>
      ⟨Y c, by rw [SetLike.mem_coe, Subgroup.mem_comap, hY c]; exact c.2.1, rfl⟩
    have hYL : ∀ c, ∀ x ∈ Lp, (Y c : V ≃ₗ[K] V) * x = x * (Y c : V ≃ₗ[K] V) := by
      intro c x hx
      have hxΩ : x ∈ orthDerived Q := hLΩ hx
      have h1 : φ ⟨x, hxΩ⟩ ∈ L₁ := ⟨⟨x, hxΩ⟩, (hmemL _).mpr hx, rfl⟩
      have h2 := Subgroup.mem_centralizer_iff.mp c.2.2 _ h1
      rw [← hY c, ← map_mul, ← map_mul] at h2
      exact (congrArg Subtype.val (hφ h2)).symm
    have hinj : Function.Injective (fun c : ↥(Bs ⊓ Subgroup.centralizer (L₁ : Set G) :
        Subgroup G) => (⟨⟨(Y c : V ≃ₗ[K] V), hYA c⟩, hYL c⟩ :
          {z : A // ∀ x ∈ Lp, (z : V ≃ₗ[K] V) * x = x * z})) := by
      intro c c' h
      have h1 : Y c = Y c' := Subtype.ext (congrArg (fun z => ((z.1 : A) : V ≃ₗ[K] V)) h)
      exact Subtype.ext (by rw [← hY c, ← hY c', h1])
    exact (Nat.card_le_card_of_injective _ hinj).trans hcount

end Group

section Tags

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin.Twisted

theorem witnessAlt_POmegaPlus_nonsplit {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} (hn5 : 5 ≤ n) (hn : 3 ≤ n)
    {ψ : spinGroup (quadPlus n (GaloisField 2 f)) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (plusDatum n (GaloisField 2 f) hn) .POmegaPlus n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : p ∣ 2 ^ f + 1) {E : Subgroup G} {r : G}
    (hE : GGStepThreeChoice p Bs (ggM p B x L D J) (plusDatum n (GaloisField 2 f) hn)
      .POmegaPlus ψ E r) {s : G} (hs : s ∈ ggG0 p B x L D J) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .POmegaPlus f r s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ :=
      PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hC, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n (GaloisField 2 f) hn
  set πe := MulEquiv.ofBijective (AutOm.spinModelPlus (K := GaloisField 2 f) hn)
    ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ with hπe
  set e₁ := CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv
    (coordinateQuadPlus n (GaloisField 2 f)) with he₁
  set φ : ↥(orthDerived (coordinateQuadPlus n (GaloisField 2 f))) →* G :=
    ψ.comp (πe.symm.toMonoidHom.comp e₁.symm.toMonoidHom) with hφ
  have hφinj : Function.Injective φ := hψinj.comp (πe.symm.injective.comp e₁.symm.injective)
  have hφrange : φ.range = ggG0 p B x L D J := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨e₁ (πe u), ?_⟩
      simp [hφ]
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hdim : finrank (GaloisField 2 f) (Fin (2 * n) → GaloisField 2 f) = 2 * n :=
    Module.finrank_fin_fun _
  have hcard : p ^ 2 ≤ Nat.card Bs := by
    rw [← hE.2.2.1]
    exact Subgroup.card_le_of_le hE.1
  obtain ⟨y, hys, m, hm, hb, hb1, L₁, hL₁, hL₁c⟩ := exists_witness_grp hnd hT (by omega) hp
    (hK ▸ hpq) hctx.2.1.2.1 hctx.2.1.2.2.2 hcard φ hφinj (by rw [hφrange, ← hrange]; exact hBψ)
    (by rw [hφrange]; exact hs) hs2
  rw [hφrange] at hm hL₁
  exact Or.inr (Or.inl ⟨y, hys, m, Subgroup.le_normalizer hm, hb1,
    Or.inr (Or.inr ⟨hb, L₁, hL₁, Or.inl hL₁c⟩)⟩)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem witnessAlt_POmegaMinus_nonsplit {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} (hn5 : 5 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2 ^ f)
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (minusDatum n hirr) .POmegaMinus n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : p ∣ 2 ^ f + 1) {E : Subgroup G} {r : G}
    (hE : GGStepThreeChoice p Bs (ggM p B x L D J) (minusDatum n hirr) .POmegaMinus ψ E r)
    {s : G} (hs : s ∈ ggG0 p B x L D J) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .POmegaMinus f r s := by
  have hn : 4 ≤ n := by omega
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ :=
      PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hC, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  set πe := MulEquiv.ofBijective (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ with hπe
  set e₁ := CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv
    (coordinateQuadMinus n K (by omega) b c) with he₁
  set φ : ↥(orthDerived (coordinateQuadMinus n K (by omega) b c)) →* G :=
    ψ.comp (πe.symm.toMonoidHom.comp e₁.symm.toMonoidHom) with hφ
  have hφinj : Function.Injective φ := hψinj.comp (πe.symm.injective.comp e₁.symm.injective)
  have hφrange : φ.range = ggG0 p B x L D J := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨e₁ (πe u), ?_⟩
      simp [hφ]
  have hdim : finrank K (Fin (2 * n) → K) = 2 * n := Module.finrank_fin_fun _
  have hcard : p ^ 2 ≤ Nat.card Bs := by
    rw [← hE.2.2.1]
    exact Subgroup.card_le_of_le hE.1
  obtain ⟨y, hys, m, hm, hb, hb1, L₁, hL₁, hL₁c⟩ := exists_witness_grp hnd hT (by omega) hp
    (hK ▸ hpq) hctx.2.1.2.1 hctx.2.1.2.2.2 hcard φ hφinj (by rw [hφrange, ← hrange]; exact hBψ)
    (by rw [hφrange]; exact hs) hs2
  rw [hφrange] at hm hL₁
  exact Or.inr (Or.inl ⟨y, hys, m, Subgroup.le_normalizer hm, hb1,
    Or.inr (Or.inr ⟨hb, L₁, hL₁, Or.inl hL₁c⟩)⟩)

end Tags

end WitOmNs

section Inputs

theorem ggSixRootFusionWitnessOn_POmegaPlusQ1Five :
    GGSixRootFusionWitnessOn fun t n f p => t = .POmegaPlus ∧ p ∣ 2 ^ f + 1 ∧ 5 ≤ n := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, hpq, hn5⟩ := hP
  have hn : 3 ≤ n := by omega
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hctx s1 _ E r hE _ _ s hs hs2
  exact WitOmNs.witnessAlt_POmegaPlus_nonsplit hn5 hn hctx s1 hpq hE hs hs2

theorem ggSixRootFusionWitnessOn_POmegaMinusQ1Five :
    GGSixRootFusionWitnessOn fun t n f p => t = .POmegaMinus ∧ p ∣ 2 ^ f + 1 ∧ 5 ≤ n := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 _ E r hE _ _ s hs hs2
  obtain ⟨rfl, hpq, hn5⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact WitOmNs.witnessAlt_POmegaMinus_nonsplit (K := GaloisField 2 f) hn5 (minusCoeffs_irr 2 f)
    (GaloisField.card 2 f (by have := hctx.2.2.2.1.1.2.1; omega)) hctx s1 hpq hE hs hs2

end Inputs

end CFSG.StandardType
