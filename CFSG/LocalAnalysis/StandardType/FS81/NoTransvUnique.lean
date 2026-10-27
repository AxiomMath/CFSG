module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvTheta
public import CFSG.RankThree.Transfer.WeaklyClosedPrime

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

variable {G : Type} [Group G] [Finite G] {b₀ : G} {K E P₁ : Subgroup G}

theorem fs81Nt_card_le_of_isPGroup {R H : Subgroup G} (hR : IsPGroup 3 R) (hRH : R ≤ H) :
    Nat.card R ≤ 3 ^ (Nat.card H).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  have hdvd : 3 ^ k ∣ Nat.card H := hk ▸ Subgroup.card_dvd_of_le hRH
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd)

theorem sylowN1_of_forall_pow_mem {b₀ : G} {K E P₁ : Subgroup G}
    (hle : P₁ ≤ transvN1 b₀ K E) (hp : IsPGroup 3 P₁) (hE : E ≤ P₁)
    (hsyl : ∀ y ∈ transvN1 b₀ K E, ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ P₁) :
    SylowN1 b₀ K E P₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp' : IsPGroup 3 (P₁.subgroupOf (transvN1 b₀ K E)) := fun x => by
    obtain ⟨k, hk⟩ := hp ⟨((x : ↥(transvN1 b₀ K E)) : G),
      Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨T, hPT⟩ := hp'.exists_le_sylow
  have hTP : (T : Subgroup ↥(transvN1 b₀ K E)) ≤ P₁.subgroupOf (transvN1 b₀ K E) := by
    intro t ht
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
    exact hsyl (t : G) t.2 k (by
      simpa using congrArg (fun z : ↥(transvN1 b₀ K E) => (z : G))
        (congrArg Subtype.val hk))
  have hEq : (T : Subgroup ↥(transvN1 b₀ K E)) = P₁.subgroupOf (transvN1 b₀ K E) :=
    le_antisymm hTP hPT
  refine ⟨hle, hp, ?_, hE⟩
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ← hEq,
    Sylow.card_eq_multiplicity T]

@[expose] def NoOffenderA (b₀ : G) (K E : Subgroup G) : Prop :=
  ∀ F : Subgroup G, F ≤ Subgroup.normalizer (E : Set G) → IsElemAbelian 3 F →
    (∀ f ∈ F, b₀⁻¹ * (f * b₀ * f⁻¹) ∈ E ⊓ K) →
    ¬ F ≤ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) →
    Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) *
      (F ⊓ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G)).relIndex F <
      Nat.card ↥(E ⊓ K)

namespace TransvP1

theorem inf_N1_le (hP : SylowN1 b₀ K E P₁) {R : Subgroup G} (hR : IsPGroup 3 R) (hPR : P₁ ≤ R) :
    R ⊓ transvN1 b₀ K E ≤ P₁ := by
  have hle : P₁ ≤ R ⊓ transvN1 b₀ K E := le_inf hPR hP.le
  have hcard : Nat.card ↥(R ⊓ transvN1 b₀ K E) ≤ Nat.card P₁ := by
    rw [hP.card]
    exact fs81Nt_card_le_of_isPGroup (hR.to_le inf_le_left) inf_le_right
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm.le

theorem eq_E_of_le (hP : SylowN1 b₀ K E P₁)
    (hfixN : ∀ g ∈ Subgroup.normalizer (E : Set G), b₀⁻¹ * (g * b₀ * g⁻¹) ∈ E ⊓ K)
    (hΩ : ∀ y ∈ P₁, y ^ 3 = 1 → y ∈ E) (hoff : NoOffenderA b₀ K E)
    (hEA : Nat.card E = 3 * Nat.card ↥(E ⊓ K)) {R : Subgroup G} (hR : IsPGroup 3 R)
    (hPR : P₁ ≤ R) (hRN : R ≤ Subgroup.normalizer (E : Set G)) {F : Subgroup G} (hFR : F ≤ R)
    (hF : IsElemAbelian 3 F) (hFc : Nat.card F = Nat.card E) : F = E := by
  set CA := Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) with hCA
  have hF₀E : F ⊓ CA ≤ E := by
    intro f hf
    have hfN : f ∈ transvN1 b₀ K E := by
      refine ⟨hRN (hFR hf.1), fun a ha => ?_, hfixN f (hRN (hFR hf.1))⟩
      rw [← Subgroup.mem_centralizer_iff.mp hf.2 a ha, mul_inv_cancel_right]
    exact hΩ f (inf_N1_le hP hR hPR ⟨hFR hf.1, hfN⟩) (hF.2 f hf.1)
  by_cases hFA : F ≤ CA
  · have hFE : F ≤ E := fun f hf => hF₀E ⟨hf, hFA hf⟩
    exact Subgroup.eq_of_le_of_card_ge hFE hFc.symm.le
  exfalso
  have hlt := hoff F (hFR.trans hRN) hF (fun f hf => hfixN f (hRN (hFR hf))) hFA
  have h1 : CA.relIndex F * Nat.card ↥(CA ⊓ F) = Nat.card F := Subgroup.relIndex_mul_card CA F
  rw [← Subgroup.inf_relIndex_left F CA] at h1
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h2 : Nat.card ↥(CA ⊓ F) ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (F : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hF₀E ⟨hx.2, hx.1⟩, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => hFcomm y hy x hx.2
  have h3 : Nat.card ↥(E ⊓ Subgroup.centralizer (F : Set G)) ≤
      3 * Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) := by
    have h4 := Subgroup.relIndex_mul_card (E ⊓ K) (E ⊓ Subgroup.centralizer (F : Set G))
    have h5 : E ⊓ K ⊓ (E ⊓ Subgroup.centralizer (F : Set G)) =
        E ⊓ K ⊓ Subgroup.centralizer (F : Set G) := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    have h6 := Subgroup.relIndex_mul_card (E ⊓ K) E
    have hEKE : E ⊓ K ⊓ E = E ⊓ K := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [hEKE, hEA] at h6
    have h7 : (E ⊓ K).relIndex E = 3 :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (h6.trans (by ring))
    have h8 : (E ⊓ K).relIndex (E ⊓ Subgroup.centralizer (F : Set G)) ≤ 3 := by
      rw [← h7]
      exact Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h7]; norm_num)
    rw [h5] at h4
    rw [← h4]
    exact Nat.mul_le_mul_right _ h8
  have : Nat.card F < Nat.card E := by
    calc Nat.card F = (F ⊓ CA).relIndex F * Nat.card ↥(CA ⊓ F) := h1.symm
      _ ≤ (F ⊓ CA).relIndex F * (3 * Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G))) :=
          Nat.mul_le_mul_left _ (h2.trans h3)
      _ = 3 * (Nat.card ↥(E ⊓ K ⊓ Subgroup.centralizer (F : Set G)) * (F ⊓ CA).relIndex F) := by
          ring
      _ < 3 * Nat.card ↥(E ⊓ K) := Nat.mul_lt_mul_of_pos_left hlt (by norm_num)
      _ = Nat.card E := hEA.symm
  omega

theorem exists_sylow_weaklyClosed (hE : IsElemAbelian 3 E) (hP : SylowN1 b₀ K E P₁)
    (hfixN : ∀ g ∈ Subgroup.normalizer (E : Set G), b₀⁻¹ * (g * b₀ * g⁻¹) ∈ E ⊓ K)
    (hΩ : ∀ y ∈ P₁, y ^ 3 = 1 → y ∈ E) (hoff : NoOffenderA b₀ K E)
    (hEA : Nat.card E = 3 * Nat.card ↥(E ⊓ K)) :
    ∃ S : Sylow 3 G, E ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Subgroup.normalizer (E : Set G) ∧
      ∀ g : G, conjSubgroup g E ≤ S → conjSubgroup g E = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set NE := Subgroup.normalizer (E : Set G) with hNE
  have hP₁N : P₁ ≤ NE := fun x hx => mem_normalizer hP hx
  have hP₁' : IsPGroup 3 (P₁.subgroupOf NE) := fun x => by
    obtain ⟨k, hk⟩ := hP.pgroup ⟨((x : NE) : G), Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨Q, hQ⟩ := hP₁'.exists_le_sylow
  set S₁ := (Q : Subgroup NE).map NE.subtype with hS₁
  have hS₁p : IsPGroup 3 S₁ := Q.isPGroup'.map _
  have hS₁N : S₁ ≤ NE := Subgroup.map_subtype_le _
  have hPS₁ : P₁ ≤ S₁ := fun x hx => ⟨⟨x, hP₁N hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hES₁ : E ≤ S₁ := hP.E_le.trans hPS₁
  have hS₁card : Nat.card S₁ = 3 ^ (Nat.card NE).factorization 3 := by
    rw [Subgroup.card_map_of_injective NE.subtype_injective, Sylow.card_eq_multiplicity]
  have hwc : ∀ g : G, conjSubgroup g E ≤ S₁ → conjSubgroup g E = E := fun g hg =>
    eq_E_of_le hP hfixN hΩ hoff hEA hS₁p hPS₁ hS₁N hg (hE.map _)
      (Subgroup.card_map_of_injective (MulAut.conj g).injective)
  have hmax : ∀ {Q' : Subgroup G}, IsPGroup 3 Q' → S₁ ≤ Q' → Q' = S₁ := by
    intro Q' hQ' hle
    by_contra hne
    have : Group.IsNilpotent ↥Q' := hQ'.isNilpotent
    have hlt : S₁.subgroupOf Q' < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hne ?_
      exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hle
    obtain ⟨x, hxN, hxS⟩ :=
      SetLike.exists_of_lt ((normalizerCondition_of_isNilpotent : NormalizerCondition ↥Q') _ hlt)
    have hxQ : (x : G) ∈ Q' := x.2
    have hxS₁ : ∀ s : G, s ∈ S₁ ↔ (x : G) * s * (x : G)⁻¹ ∈ S₁ := by
      intro s
      constructor
      · intro hs
        exact Subgroup.mem_subgroupOf.mp
          ((Subgroup.mem_normalizer_iff.mp hxN ⟨s, hle hs⟩).mp (Subgroup.mem_subgroupOf.mpr hs))
      · intro hs
        have hsQ : s ∈ Q' := by
          have := Q'.mul_mem (Q'.mul_mem (Q'.inv_mem hxQ) (hle hs)) hxQ
          rwa [show (x : G)⁻¹ * ((x : G) * s * (x : G)⁻¹) * (x : G) = s by group] at this
        exact Subgroup.mem_subgroupOf.mp
          ((Subgroup.mem_normalizer_iff.mp hxN ⟨s, hsQ⟩).mpr (Subgroup.mem_subgroupOf.mpr hs))
    have hxNS : (x : G) ∈ Subgroup.normalizer (S₁ : Set G) := Subgroup.mem_normalizer_iff.mpr hxS₁
    have hxE : conjSubgroup (x : G) E = E := hwc x (by
      rintro _ ⟨e, he, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hxS₁ e).mp (hES₁ he))
    have hxNE : (x : G) ∈ NE := by
      rw [hNE, Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hxE
    have hzx : IsPGroup 3 (Subgroup.zpowers (x : G)) := hQ'.to_le (Subgroup.zpowers_le.mpr hxQ)
    have hsup : IsPGroup 3 ↥(S₁ ⊔ Subgroup.zpowers (x : G)) :=
      IsPGroup.to_sup_of_normal_left' hS₁p hzx (Subgroup.zpowers_le.mpr hxNS)
    have hsupN : S₁ ⊔ Subgroup.zpowers (x : G) ≤ NE :=
      sup_le hS₁N (Subgroup.zpowers_le.mpr hxNE)
    have hcard := fs81Nt_card_le_of_isPGroup hsup hsupN
    rw [← hS₁card] at hcard
    have heq := Subgroup.eq_of_le_of_card_ge
      (le_sup_left : S₁ ≤ S₁ ⊔ Subgroup.zpowers (x : G)) hcard
    apply hxS
    rw [Subgroup.mem_subgroupOf, heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact ⟨⟨S₁, hS₁p, fun hQ' hle => hmax hQ' hle⟩, hES₁, hS₁N, hwc⟩

theorem false_of_noOffender (h : TransvSetup b₀ K E) (hP : TransvP1 b₀ K E P₁) {n : ℕ}
    (B : Basis3 G (n + 1)) (hB : Adapted B b₀ K E) (hsc : SignChanges B.b b₀ E)
    (hKl : KleinSigns B E) (hd3 : DiagSigns3 B E) {μ : ℕ}
    (hμ : ∀ y ∈ P₁, y ^ 3 = tb b₀ y ^ μ) (hne : ¬ ∀ x ∈ P₁, x ^ 3 = 1)
    (hA9 : 9 ≤ Nat.card ↥(E ⊓ K)) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer K)) (hoff : NoOffenderA b₀ K E)
    (hEA : Nat.card E = 3 * Nat.card ↥(E ⊓ K)) (hG : b₀ ∈ commutator G) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA1 : ∃ a ∈ E ⊓ K, a ≠ 1 := by
    rcases (E ⊓ K).bot_or_exists_ne_one with hbot | hex
    · rw [hbot, Subgroup.card_bot] at hA9
      omega
    · exact hex
  have hfixN := hP.conj_b0_mem h fun m hm a ha => hP.not_conj_b0_inv h hμ hne hA1 hm ha
  have hΩ : ∀ y ∈ P₁, y ^ 3 = 1 → y ∈ E := fun y hy hy3 =>
    hP.mem_E_of_cube_eq_one h hμ hne hy hy3
  obtain ⟨S, hES, hSN, hwc⟩ := exists_sylow_weaklyClosed h.elem hP.toSylowN1 hfixN hΩ hoff hEA
  have hb3 : b₀ ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one b₀
  exact hP.not_mem_commutator h B hB hsc hKl hd3 hμ hne hA9 hKC hKn hKz hOut
    (CFSG.RankThree.Transfer.WCP.mem_commutator_of_weaklyClosed S hES hSN hwc
      (fun a ha b hb => h.comm ha hb) h.b0_mem hb3 hG)

end TransvP1

end CFSG.StandardType.FrameRoute.FS81

end
