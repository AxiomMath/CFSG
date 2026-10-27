module

public import CFSG.RankThree.PartOne.S11.FivePlusLocal
import CFSG.RankThree.PartOne.S10.NormalPCoreTwoCommutatorThetaComponent
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace S11d

theorem smul_mem_actionCommutator_of_comm {J B C : Type*} [Group J] [Group B] [Group C]
    [MulDistribMulAction B J] [MulDistribMulAction C J]
    (hBC : ∀ (b : B) (c : C) (x : J), b • (c • x) = c • (b • x))
    {K : Subgroup J} (hK : ∀ b : B, ∀ x ∈ K, b • x ∈ K) (b : B) {x : J}
    (hx : x ∈ actionCommutator C K) : b • x ∈ actionCommutator C K := by
  have hle : actionCommutator C K ≤
      (actionCommutator C K).comap (MulDistribMulAction.toMonoidHom J b) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨h, hh, c, rfl⟩
    change b • (h⁻¹ * (c • h)) ∈ actionCommutator C K
    have e : b • (h⁻¹ * (c • h)) = (b • h)⁻¹ * (c • (b • h)) := by
      rw [smul_mul', smul_inv', hBC]
    rw [e]
    exact gen_mem_actionCommutator (hK b h hh) c
  exact hle hx

theorem smul_mem_map_sylow_two {J D : Type*} [Group J] [Group D] [MulDistribMulAction D J]
    {F : Subgroup J} [Finite F] (P₂ : Sylow 2 F) [Subsingleton (Sylow 2 F)]
    (hFD : ∀ b : D, ∀ x ∈ F, b • x ∈ F) (b : D) {x : J}
    (hx : x ∈ (P₂ : Subgroup F).map F.subtype) : b • x ∈ (P₂ : Subgroup F).map F.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hyF : b • (y : J) ∈ F := hFD b y y.2
  set y' : F := ⟨b • (y : J), hyF⟩ with hy'
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P₂.isPGroup' ⟨y, hy⟩
  have hyk : y ^ (2 ^ k) = 1 := by
    have h1 : (⟨y, hy⟩ : (P₂ : Subgroup F)) ^ (2 ^ k) = 1 := by
      rw [← hk]; exact pow_orderOf_eq_one _
    exact congrArg Subtype.val h1
  have hy'k : y' ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have h2 : ((y ^ (2 ^ k) : F) : J) = 1 := by rw [hyk]; rfl
    show (b • (y : J)) ^ (2 ^ k) = 1
    rw [← smul_pow']
    have h3 : (y : J) ^ (2 ^ k) = 1 := by simpa using h2
    rw [h3, smul_one]
  have hord : orderOf y' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy'k
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hz2 : IsPGroup 2 (Subgroup.zpowers y') :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨S, hS⟩ := hz2.exists_le_sylow
  have hSP : S = P₂ := Subsingleton.elim S P₂
  have hy'mem : y' ∈ (P₂ : Subgroup F) := by
    have := hS (Subgroup.mem_zpowers y')
    rwa [hSP] at this
  exact ⟨y', hy'mem, rfl⟩

theorem exists_invariant_two_commutator_of_inner_action_c {J B C : Type*} [Group J] [Finite J]
    [Group B] [Finite B] [Group C] [Finite C] [MulDistribMulAction B J] [MulDistribMulAction C J]
    (h2C : ¬ 2 ∣ Nat.card C)
    (hBC : ∀ (b : B) (c : C) (x : J), b • (c • x) = c • (b • x))
    {Q : Subgroup (MulAut J)} (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hinn : Q ≤ (MulAut.conj : J →* MulAut J).range)
    (hBQ : (MulDistribMulAction.toMulAut B J).range ≤ normalizer (Q : Set (MulAut J)))
    (hCQ : (MulDistribMulAction.toMulAut C J).range ≤ normalizer (Q : Set (MulAut J)))
    (hQC : ⁅Q, (MulDistribMulAction.toMulAut C J).range⁆ = Q) :
    ∃ E : Subgroup J, E ≠ ⊥ ∧ IsPGroup 2 E ∧ (∀ b : B, ∀ x ∈ E, b • x ∈ E) ∧
      actionCommutator C E = E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := MulDistribMulAction.toMulAut B J with hρ
  set ρC := MulDistribMulAction.toMulAut C J with hρC
  set c : J →* MulAut J := MulAut.conj with hc
  set QJ : Subgroup J := Q.comap c with hQJ
  have hρQ : ∀ (b : B) (σ : MulAut J), σ ∈ Q → ρ b * σ * (ρ b)⁻¹ ∈ Q := fun b σ hσ =>
    (Subgroup.mem_normalizer_iff.mp (hBQ ⟨b, rfl⟩) σ).mp hσ
  have hρCQ : ∀ (b : C) (σ : MulAut J), σ ∈ Q → ρC b * σ * (ρC b)⁻¹ ∈ Q := fun b σ hσ =>
    (Subgroup.mem_normalizer_iff.mp (hCQ ⟨b, rfl⟩) σ).mp hσ
  have hQJinv : ∀ b : B, ∀ x ∈ QJ, b • x ∈ QJ := by
    intro b x hx
    have hx' : c x ∈ Q := hx
    show c (b • x) ∈ Q
    have e : c (b • x) = ρ b * c x * (ρ b)⁻¹ := mulAut_conj_apply_automorphism (ρ b) x
    rw [e]
    exact hρQ b _ hx'
  have hQJinvC : ∀ b : C, ∀ x ∈ QJ, b • x ∈ QJ := by
    intro b x hx
    have hx' : c x ∈ Q := hx
    show c (b • x) ∈ Q
    have e : c (b • x) = ρC b * c x * (ρC b)⁻¹ := mulAut_conj_apply_automorphism (ρC b) x
    rw [e]
    exact hρCQ b _ hx'
  set F := actionCommutator C QJ with hF
  have hFle : F ≤ QJ := SteinbergBM.actionCommutator_le_of_invariant hQJinvC
  have hFinvC : ∀ b : C, ∀ x ∈ F, b • x ∈ F := fun b x hx =>
    SteinbergBM.smul_mem_actionCommutator_of_invariant hQJinvC b hx
  have hFinv : ∀ b : B, ∀ x ∈ F, b • x ∈ F := fun b x hx =>
    smul_mem_actionCommutator_of_comm hBC hQJinv b hx
  let f : F →* Q := (c.comp F.subtype).codRestrict Q (fun x => hFle x.2)
  have hfker : f.ker ≤ Subgroup.center F := by
    intro x hx
    have hx1 : c (x : J) = 1 := by
      have h1 : f x = 1 := hx
      exact congrArg Subtype.val h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h2 := congrArg (fun σ : MulAut J => σ (y : J)) hx1
    simp only [hc, MulAut.conj_apply, MulAut.one_apply] at h2
    show (y : J) * (x : J) = (x : J) * (y : J)
    calc (y : J) * (x : J) = ((x : J) * (y : J) * (x : J)⁻¹) * (x : J) := by rw [h2]
      _ = (x : J) * (y : J) := by group
  have : Group.IsNilpotent Q := hQ2.isNilpotent
  have : Group.IsNilpotent F := Subgroup.isNilpotent_of_ker_le_center f hfker
  let P₂ : Sylow 2 F := default
  have hP₂n : (P₂ : Subgroup F).Normal := inferInstance
  have : Unique (Sylow 2 F) := Sylow.unique_of_normal P₂ hP₂n
  set Pj : Subgroup J := (P₂ : Subgroup F).map F.subtype with hPj
  have hPjinv : ∀ b : B, ∀ x ∈ Pj, b • x ∈ Pj := fun b x hx =>
    smul_mem_map_sylow_two P₂ hFinv b hx
  have hPjinvC : ∀ b : C, ∀ x ∈ Pj, b • x ∈ Pj := fun b x hx =>
    smul_mem_map_sylow_two P₂ hFinvC b hx
  have hPj2 : IsPGroup 2 Pj := P₂.isPGroup'.map F.subtype
  set E := actionCommutator C Pj with hE
  have hEle : E ≤ Pj := SteinbergBM.actionCommutator_le_of_invariant hPjinvC
  refine ⟨E, ?_, hPj2.to_le hEle, fun b x hx => smul_mem_actionCommutator_of_comm hBC hPjinv b hx,
    SteinbergBM.actionCommutator_actionCommutator_of_isPGroup Nat.prime_two hPj2 h2C hPjinvC⟩
  intro hE0
  have hfix : ∀ b : C, ∀ x ∈ Pj, b • x = x := by
    intro b x hx
    have h1 : x⁻¹ * (b • x) ∈ E := gen_mem_actionCommutator hx b
    rw [hE0, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  have hQF : Q ≤ F.map c := by
    refine hQC.symm.le.trans ?_
    rw [Subgroup.commutator_le]
    rintro σ hσ _ ⟨b, rfl⟩
    obtain ⟨x, rfl⟩ := hinn hσ
    have hx : x ∈ QJ := hσ
    refine ⟨x * (b • x⁻¹), ?_, ?_⟩
    · have h1 := gen_mem_actionCommutator (A := C) (QJ.inv_mem hx) b
      simpa using h1
    · have e : c (b • x⁻¹) = ρC b * c x⁻¹ * (ρC b)⁻¹ :=
        mulAut_conj_apply_automorphism (ρC b) x⁻¹
      rw [map_mul, e, map_inv, commutatorElement_def]
      group
  have hfs : Function.Surjective f := by
    rintro ⟨σ, hσ⟩
    obtain ⟨x, hx, hxσ⟩ := hQF hσ
    exact ⟨⟨x, hx⟩, Subtype.ext hxσ⟩
  have hmax := (P₂.mapSurjective hfs).is_maximal' (hQ2.to_subgroup ⊤) le_top
  rw [Sylow.coe_mapSurjective] at hmax
  have hQPj : ∀ σ ∈ Q, ∃ x ∈ Pj, c x = σ := by
    intro σ hσ
    have h1 : (⟨σ, hσ⟩ : Q) ∈ (P₂ : Subgroup F).map f := hmax ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyσ⟩ := h1
    exact ⟨y, ⟨y, hy, rfl⟩, congrArg Subtype.val hyσ⟩
  apply hQ1
  rw [← hQC, eq_bot_iff, Subgroup.commutator_le]
  rintro σ hσ _ ⟨b, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hQPj σ hσ
  have h1 : ρC b * c x * (ρC b)⁻¹ = c x := by
    have e : c (b • x) = ρC b * c x * (ρC b)⁻¹ := mulAut_conj_apply_automorphism (ρC b) x
    rw [← e, hfix b x hx]
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem not_two_dvd_card_zpowers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup H}
    (hA : IsPGroup p A) {a : H} (ha : a ∈ A) : ¬ 2 ∣ Nat.card (Subgroup.zpowers a) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨a, ha⟩
  have hk' : orderOf a = p ^ k := (Subgroup.orderOf_coe (⟨a, ha⟩ : A)).trans hk
  intro h2
  rw [Nat.card_zpowers, hk'] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem exists_two_commutator_in_thetaComponent_c {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hK : CatalogPrimeTwoAutomorphismsInner) {L A Q : Subgroup H} {a : H}
    (hAL : A ≤ normalizer (L : Set H)) (hQL : Q ≤ normalizer (L : Set H)) (hA : IsPGroup p A)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (ha : a ∈ A)
    (hQ2 : IsPGroup 2 Q) (hAQ : A ≤ normalizer (Q : Set H)) (hQa : ⁅Q, zpowers a⁆ = Q)
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hcat : Catalog ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)))
    (hmove : ∃ q : Q, thetaQuotientAction p hQL q ≠ 1) :
    ∃ T : Subgroup H, T ≤ L ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ normalizer (T : Set H) ∧
      ⁅T, zpowers a⁆ = T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, hNchar, hNp, -⟩ := solvable_prime_complement_core_characterization (H := ↥L) hp
  set N := aschbacherSolvableCore p L with hN
  have : N.Normal := inferInstance
  have hzA : zpowers a ≤ A := zpowers_le.mpr ha
  have hzL : zpowers a ≤ normalizer (L : Set H) := hzA.trans hAL
  let _ : MulDistribMulAction A L := conjActionOn hAL
  let _ : MulDistribMulAction (zpowers a) L := conjActionOn hzL
  have hinv : CFSG.IsInvariant A L N := CFSG.isInvariant_of_characteristic N
  have hinvC : CFSG.IsInvariant (zpowers a) L N :=
    CFSG.isInvariant_of_characteristic N
  have h2C : ¬ 2 ∣ Nat.card (zpowers a) := not_two_dvd_card_zpowers hp hp2 hA ha
  have hQA : ⁅Q, A⁆ = Q := le_antisymm (commutator_le_left_of_normalizes hAQ)
    (hQa.symm.le.trans (Subgroup.commutator_mono le_rfl hzA))
  set Γ := normalizer (L : Set H) with hΓ
  set Φ := thetaQuotientConj p L with hΦ
  have hact : ∀ (b : A) (x : L ⧸ N),
      MulDistribMulAction.toMulAut A (L ⧸ N) b x = Φ ⟨b, hAL b.2⟩ x := by
    intro b x
    induction x using QuotientGroup.induction_on with
    | H l =>
      change b • ((l : L) : L ⧸ N) = _
      rw [MulAction.Quotient.smul_mk, hΦ, thetaQuotientConj_mk]
      rfl
  have hactC : ∀ (b : zpowers a) (x : L ⧸ N),
      MulDistribMulAction.toMulAut (zpowers a) (L ⧸ N) b x = Φ ⟨b, hzL b.2⟩ x := by
    intro b x
    induction x using QuotientGroup.induction_on with
    | H l =>
      change b • ((l : L) : L ⧸ N) = _
      rw [MulAction.Quotient.smul_mk, hΦ, thetaQuotientConj_mk]
      rfl
  set Qa : Subgroup (MulAut (L ⧸ N)) := (Q.subgroupOf Γ).map Φ with hQa'
  set P : Subgroup (MulAut (L ⧸ N)) := (A.subgroupOf Γ).map Φ with hP
  set PC : Subgroup (MulAut (L ⧸ N)) := ((zpowers a).subgroupOf Γ).map Φ with hPC
  have hPrange : (MulDistribMulAction.toMulAut A (L ⧸ N)).range = P := by
    ext σ
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨⟨b, hAL b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, ?_⟩
      ext x
      exact (hact b x).symm
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, ?_⟩
      ext x
      exact hact ⟨g, Subgroup.mem_subgroupOf.mp hg⟩ x
  have hPCrange : (MulDistribMulAction.toMulAut (zpowers a) (L ⧸ N)).range = PC := by
    ext σ
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨⟨b, hzL b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, ?_⟩
      ext x
      exact (hactC b x).symm
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, ?_⟩
      ext x
      exact hactC ⟨g, Subgroup.mem_subgroupOf.mp hg⟩ x
  have hP' : IsPGroup p P := (hA.comap_subtype).map Φ
  have hQ2' : IsPGroup 2 Qa := (hQ2.comap_subtype).map Φ
  have hPQ : P ≤ normalizer (Qa : Set (MulAut (L ⧸ N))) := by
    have h1 : A.subgroupOf Γ ≤ normalizer (Q.subgroupOf Γ : Set Γ) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hAQ (Subgroup.mem_subgroupOf.mp hx)) (h : H)
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map Φ)
  have hPCQ : PC ≤ normalizer (Qa : Set (MulAut (L ⧸ N))) := by
    have h1 : (zpowers a).subgroupOf Γ ≤ normalizer (Q.subgroupOf Γ : Set Γ) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hAQ (hzA (Subgroup.mem_subgroupOf.mp hx))) (h : H)
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map Φ)
  have hQA' : ⁅Q.subgroupOf Γ, A.subgroupOf Γ⁆ = Q.subgroupOf Γ := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQL,
      Subgroup.map_subgroupOf_eq_of_le hAL]
    exact hQA
  have hQC' : ⁅Q.subgroupOf Γ, (zpowers a).subgroupOf Γ⁆ = Q.subgroupOf Γ := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQL,
      Subgroup.map_subgroupOf_eq_of_le hzL]
    exact hQa
  have hQP : ⁅Qa, P⁆ = Qa := by
    rw [hQa', hP, ← Subgroup.map_commutator, hQA']
  have hQPC : ⁅Qa, PC⁆ = Qa := by
    rw [hQa', hPC, ← Subgroup.map_commutator, hQC']
  have hinn : Qa ≤ (MulAut.conj : (L ⧸ N) →* MulAut (L ⧸ N)).range :=
    hK (L ⧸ N) hLq hcat p P Qa hp hp3 hP' hQ2' hPQ hQP
  have hQa1 : Qa ≠ ⊥ := by
    obtain ⟨q, hq⟩ := hmove
    intro h
    have h1 : Φ ⟨q, hQL q.2⟩ ∈ Qa := Subgroup.mem_map_of_mem Φ (Subgroup.mem_subgroupOf.mpr q.2)
    rw [h, Subgroup.mem_bot] at h1
    exact hq h1
  have hBC : ∀ (b : A) (c : zpowers a) (x : L ⧸ N), b • (c • x) = c • (b • x) := by
    intro b c x
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk,
        MulAction.Quotient.smul_mk]
      congr 1
      apply Subtype.ext
      have hbc : (b : H) * (c : H) = (c : H) * (b : H) := hAcomm b b.2 c (hzA c.2)
      change (b : H) * ((c : H) * l * (c : H)⁻¹) * (b : H)⁻¹ =
        (c : H) * ((b : H) * l * (b : H)⁻¹) * (c : H)⁻¹
      calc (b : H) * ((c : H) * l * (c : H)⁻¹) * (b : H)⁻¹
          = ((b : H) * (c : H)) * l * ((b : H) * (c : H))⁻¹ := by group
        _ = ((c : H) * (b : H)) * l * ((c : H) * (b : H))⁻¹ := by rw [hbc]
        _ = (c : H) * ((b : H) * l * (b : H)⁻¹) * (c : H)⁻¹ := by group
  obtain ⟨E, hE1, hE2, hEinv, hEE⟩ := exists_invariant_two_commutator_of_inner_action_c h2C hBC
    hQ2' hQa1 hinn (hPrange ▸ hPQ) (hPCrange ▸ hPCQ) (hPCrange ▸ hQPC)
  have hcA : ∀ (c : zpowers a) (x : L ⧸ N), c • x = (⟨(c : H), hzA c.2⟩ : A) • x := by
    intro c x
    induction x using QuotientGroup.induction_on with
    | H l => rfl
  have hEA : actionCommutator A E = E := by
    refine le_antisymm (SteinbergBM.actionCommutator_le_of_invariant hEinv) ?_
    refine hEE.symm.le.trans ((closure_le _).2 ?_)
    rintro _ ⟨h, hh, c, rfl⟩
    rw [hcA]
    exact gen_mem_actionCommutator (A := A) hh ⟨(c : H), hzA c.2⟩
  obtain ⟨T', -, hT'1, hT'2, hT'inv, hT'A, hT'π⟩ :=
    SteinbergBM.coprime_two_commutator_lifts_through_invariant_supplement hp hp2 hA N hNp ⊤
      (fun _ _ _ => Subgroup.mem_top _) (top_sup_eq N) E hE1 hE2 hEinv hEA
  have hT'invC : ∀ c : zpowers a, ∀ x ∈ T', c • x ∈ T' := fun c x hx =>
    hT'inv ⟨(c : H), hzA c.2⟩ x hx
  have hBCL : ∀ (b : A) (c : zpowers a) (x : L), b • (c • x) = c • (b • x) := by
    intro b c x
    apply Subtype.ext
    have hbc : (b : H) * (c : H) = (c : H) * (b : H) := hAcomm b b.2 c (hzA c.2)
    change (b : H) * ((c : H) * x * (c : H)⁻¹) * (b : H)⁻¹ =
      (c : H) * ((b : H) * x * (b : H)⁻¹) * (c : H)⁻¹
    calc (b : H) * ((c : H) * x * (c : H)⁻¹) * (b : H)⁻¹
        = ((b : H) * (c : H)) * x * ((b : H) * (c : H))⁻¹ := by group
      _ = ((c : H) * (b : H)) * x * ((c : H) * (b : H))⁻¹ := by rw [hbc]
      _ = (c : H) * ((b : H) * x * (b : H)⁻¹) * (c : H)⁻¹ := by group
  set T'c : Subgroup L := actionCommutator (zpowers a) T' with hT'c
  have hT'cle : T'c ≤ T' := SteinbergBM.actionCommutator_le_of_invariant hT'invC
  have hT'cinv : ∀ b : A, ∀ x ∈ T'c, b • x ∈ T'c := fun b x hx =>
    smul_mem_actionCommutator_of_comm hBCL hT'inv b hx
  have hπC : ∀ (c : zpowers a) (l : L), (QuotientGroup.mk' N) (c • l) =
      c • (QuotientGroup.mk' N) l := fun c l => (MulAction.Quotient.smul_mk (H := N) c l).symm
  have hmapT : T'c.map (QuotientGroup.mk' N) = E := by
    rw [hT'c, SteinbergBM.map_actionCommutator (QuotientGroup.mk' N) hπC T', hT'π, hEE]
  have hT'c1 : T'c ≠ ⊥ := by
    intro h
    rw [h, Subgroup.map_bot] at hmapT
    exact hE1 hmapT.symm
  have hT'c2 : IsPGroup 2 T'c := hT'2.to_le hT'cle
  have hT'cc : actionCommutator (zpowers a) T'c = T'c :=
    SteinbergBM.actionCommutator_actionCommutator_of_isPGroup Nat.prime_two hT'2 h2C hT'invC
  set T := T'c.map L.subtype with hT
  have hfwd : ∀ b ∈ A, ∀ g ∈ T, b * g * b⁻¹ ∈ T := by
    rintro b hb _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.mpr ⟨((⟨b, hb⟩ : A) • x), hT'cinv ⟨b, hb⟩ x hx, rfl⟩
  refine ⟨T, Subgroup.map_subtype_le _, ?_, hT'c2.map _, le_normalizer_of_conj_mem_forall hfwd,
    ?_⟩
  · intro h
    exact hT'c1 ((Subgroup.map_eq_bot_iff_of_injective T'c L.subtype_injective).mp h)
  · rw [← SteinbergBM.map_actionCommutator_conj hzL T'c, hT'cc]

theorem exists_zero_thetaComponent_of_inner_c (hB5 : SelectedPrimeElementsNormalizeThetaComponents)
    (hK : CatalogPrimeTwoAutomorphismsInner) (he : CFSG.Assembly.evenRank H ≤ 3) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hcat : ∀ L ∈ thetaComponents p H, Catalog ((L ⧸ aschbacherSolvableCore p L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore p L)))
    {A Q : Subgroup H} (hA : IsPGroup p A) (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) (hAQ : A ≤ normalizer (Q : Set H))
    (hQN : ⁅A, Q ⊓ aschbacherSolvableCore p H⁆ = ⊥)
    (hQO : ⁅Q.map (QuotientGroup.mk' (aschbacherSolvableCore p H)),
      pCore p (H ⧸ aschbacherSolvableCore p H)⁆ = ⊥)
    {a : H} (ha : a ∈ A) (hQa : ⁅Q, Subgroup.zpowers a⁆ = Q) :
    ∃ L ∈ thetaComponents p H, A ≤ normalizer (L : Set H) ∧ ⁅L, Subgroup.zpowers a⁆ = L ∧
      ∃ T : Subgroup H, T ≤ L ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ normalizer (T : Set H) ∧
        ⁅T, Subgroup.zpowers a⁆ = T := by
  classical
  have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hQA : ⁅Q, A⁆ = Q := le_antisymm (commutator_le_left_of_normalizes hAQ)
    (hQa.symm.le.trans (Subgroup.commutator_mono le_rfl hzA))
  have hQa0 : ⁅Q, Subgroup.zpowers a⁆ ≠ ⊥ := by rw [hQa]; exact hQ1
  obtain ⟨J, hJ, hQJ, hAJ, hnc⟩ :=
    select_moved_component hB5 he hp hp3 hA hQ2 hAQ hQA hQN hQO ha hQa0
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNchar, -, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set N := aschbacherSolvableCore p H with hN
  have := hNchar
  have : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨hLmem, hLJ⟩ := perfectResidual_comap_mem_thetaComponents hp hJ
  set L := inSubgroup perfectResidual (J.comap π) with hLdef
  have hAnorm : ∀ x ∈ A, x ∈ normalizer (L : Set H) := by
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨x, hx⟩
    exact hB5.1 H he p hp hp3 x ⟨k, (Subgroup.orderOf_coe (⟨x, hx⟩ : A)).trans hk⟩ L hLmem
  have hAL : A ≤ normalizer (L : Set H) := fun x hx => hAnorm x hx
  have hQL : Q ≤ normalizer (L : Set H) := by
    intro q hq
    apply SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual (J.comap π)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hQJ (Subgroup.mem_map_of_mem π hq)) (π h)
  have hzπ : Subgroup.zpowers (π a) ≤ normalizer (Q.map π : Set (H ⧸ N)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π (hAQ ha))
  have hQnc : ∃ q ∈ Q, ∃ j ∈ J, j * π q ≠ π q * j := by
    by_contra hcon
    push Not at hcon
    apply hnc
    refine (commutator_le_left_of_normalizes hzπ).trans ?_
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun j hj => hcon q hq j hj
  have hanc : ∃ j ∈ J, j * π a ≠ π a * j := by
    by_contra hcon
    push Not at hcon
    apply hnc
    exact commutator_le_centralizer_of_normalizes hQJ
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun j hj => hcon j hj))
  refine ⟨L, hLmem, hAL, ?_, ?_⟩
  ·
    obtain ⟨j, hjJ, hj⟩ := hanc
    rw [← hLJ] at hjJ
    obtain ⟨l, hlL, rfl⟩ := hjJ
    have hzL : Subgroup.zpowers a ≤ normalizer (L : Set H) :=
      Subgroup.zpowers_le.mpr (hAL ha)
    let _ : MulDistribMulAction (Subgroup.zpowers a) L := conjActionOn hzL
    have hnt := thetaQuotientConj_apply_ne_of_not_commute hp hLmem (hAL ha) (l := ⟨l, hlL⟩) hj
    have hA1 := actionCommutator_top_eq_top_of_moving_theta_quotient hp hLmem.1 hLmem.2.2
      (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) (⟨l, hlL⟩ : L) hnt
    have h := SteinbergBM.map_actionCommutator_conj hzL (⊤ : Subgroup L)
    have hTopL : (⊤ : Subgroup L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hA1, hTopL] at h
    exact h.symm
  ·
    obtain ⟨q, hq, j, hjJ, hj⟩ := hQnc
    rw [← hLJ] at hjJ
    obtain ⟨l, hlL, rfl⟩ := hjJ
    have hmoved := thetaQuotientConj_apply_ne_of_not_commute hp hLmem (hQL hq) (l := ⟨l, hlL⟩) hj
    refine exists_two_commutator_in_thetaComponent_c hp hp3 hK hAL hQL hA hAcomm ha hQ2 hAQ hQa
      hLmem.2.2 (hcat L hLmem) ⟨⟨q, hq⟩, fun h1 => hmoved ?_⟩
    have h2 : thetaQuotientAction p hQL ⟨q, hq⟩ ((⟨l, hlL⟩ : L) : L ⧸ aschbacherSolvableCore p L) =
        ((⟨l, hlL⟩ : L) : L ⧸ aschbacherSolvableCore p L) := by
      rw [h1]
      rfl
    exact h2

end S11d

end CFSG.RankThree.PartOne
