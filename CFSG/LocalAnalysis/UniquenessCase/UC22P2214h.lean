module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.Adapters.LieModelSimple
import CFSG.Blueprint.LieModelAPI
import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Model
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki
import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_card_sup_of_permutes {B T : Subgroup G} (hperm : Permutes B T) (hBT : B ⊓ T = ⊥) :
    Nat.card ↥(B ⊔ T) = Nat.card B * Nat.card T := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : ↥B × ↥T => (⟨x.1 * x.2, mul_mem_sup x.1.2 x.2.2⟩ : ↥(B ⊔ T))) ⟨?_, ?_⟩)
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h1 : (b : G) * t = b' * t' := congrArg Subtype.val h
    have h2 : (b' : G)⁻¹ * b = t' * (t : G)⁻¹ := by
      calc (b' : G)⁻¹ * b = (b' : G)⁻¹ * (b * t) * (t : G)⁻¹ := by group
        _ = (b' : G)⁻¹ * (b' * t') * (t : G)⁻¹ := by rw [h1]
        _ = t' * (t : G)⁻¹ := by group
    have h3 : (b' : G)⁻¹ * b ∈ B ⊓ T :=
      ⟨B.mul_mem (B.inv_mem b'.2) b.2, h2 ▸ T.mul_mem t'.2 (T.inv_mem t.2)⟩
    rw [hBT, Subgroup.mem_bot, inv_mul_eq_one] at h3
    have h4 : (t : G) = t' := by
      rw [← h3] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
  · rintro ⟨g, hg⟩
    obtain ⟨b, hb, t, ht, rfl⟩ := uc22p2214_mem_sup_of_permutes hperm hg
    exact ⟨(⟨b, hb⟩, ⟨t, ht⟩), rfl⟩

theorem uc22p2214_inf_eq_bot_of_odd {B T : Subgroup G} (hBodd : Odd (Nat.card B)) (hT : IsPGroup 2 T) :
    B ⊓ T = ⊥ := by
  obtain ⟨k, hk⟩ := (hT.to_le (inf_le_right : B ⊓ T ≤ T)).exists_card_eq
  have hdvd : Nat.card ↥(B ⊓ T) ∣ Nat.card B := Subgroup.card_dvd_of_le inf_le_left
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hBodd) (even_iff_two_dvd.2 ((dvd_pow_self 2 hne).trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem uc22p2214_frattini {r : ℕ} [Fact r.Prime] {X E A : Subgroup G} (hEX : E ≤ X)
    (hEn : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E) (hAE : A ≤ E)
    (hA : Nat.card A = r ^ (Nat.card E).factorization r) :
    ∀ x ∈ X, ∃ e ∈ E, ∃ n ∈ X, n ∈ normalizer (A : Set G) ∧ x = e * n := by
  intro x hx
  have hA1 : Nat.card (A.subgroupOf E) = r ^ (Nat.card E).factorization r := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv
  let P1 : Sylow r E := Sylow.ofCard (A.subgroupOf E) hA1
  let φ : E →* E :=
    { toFun := fun e => ⟨x * e * x⁻¹, hEn x hx e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h : x * (a : G) * x⁻¹ = x * (b : G) * x⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  have hQ : Nat.card ((A.subgroupOf E).map φ) = r ^ (Nat.card E).factorization r := by
    rw [← hA1]
    exact Subgroup.card_map_of_injective hφ
  let P2 : Sylow r E := Sylow.ofCard ((A.subgroupOf E).map φ) hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E P1 P2
  have hgP : MulAut.conj g • (A.subgroupOf E) = (A.subgroupOf E).map φ :=
    congrArg (fun S : Sylow r E => (S : Subgroup E)) hg
  have hn : ∀ a ∈ A, ((g : G)⁻¹ * x) * a * ((g : G)⁻¹ * x)⁻¹ ∈ A := by
    intro a ha
    have h1 : φ ⟨a, hAE ha⟩ ∈ MulAut.conj g • (A.subgroupOf E) := by
      rw [hgP]
      exact ⟨⟨a, hAE ha⟩, ha, rfl⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa [φ, mul_assoc] using h2
  refine ⟨g, g.2, (g : G)⁻¹ * x, X.mul_mem (X.inv_mem (hEX g.2)) hx, ?_, by simp⟩
  exact Subgroup.mem_normalizer_fintype fun a ha => hn a ha

theorem uc22p2214_normalizes_of_pair {M K K' : Subgroup G} (hc2 : (conjSetOf M K).ncard = 2) (hK' : K' ∈ conjSetOf M K)
    {g : G} (hg : g ∈ M) (hgK : g ∈ normalizer (K : Set G)) : g ∈ normalizer (K' : Set G) := by
  have hgK' : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.1 hgK
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_cases hKK : K' = K
  · rw [hKK]
    exact hgK'
  obtain ⟨h, hh, rfl⟩ := hK'
  have hpair := uc22p22d_conjSet_pair hh hKK hc2
  have hmem : (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom ∈ conjSetOf M K := by
    rw [uc22p22d_map_conj_map_conj]
    exact ⟨g * h, M.mul_mem hg hh, rfl⟩
  rw [hpair] at hmem
  rcases hmem with h1 | h1
  · exfalso
    apply hKK
    have h2 := congrArg (fun L : Subgroup G => L.map (MulAut.conj g⁻¹).toMonoidHom) h1
    simp only [uc22p22d_map_conj_map_conj, inv_mul_cancel_left] at h2
    rw [h2]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (inv_mem hgK)
  · exact h1

theorem uc22p2214_swap {M K B T A : Subgroup G} {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hc2 : (conjSetOf M K).ncard = 2) (hBM : B ≤ M) (hTM : T ≤ M) (hBN : B ≤ normalizer (K : Set G))
    (hBodd : Odd (Nat.card B)) (hperm : Permutes B T) (hT : IsPGroup 2 T) (hTK : ¬ T ≤ normalizer (K : Set G))
    (hA : CFSG.ABGLocalTools.IsSylowOf r A B) :
    ∃ x ∈ M, x ∉ normalizer (K : Set G) ∧ x ∈ normalizer (A : Set G) := by
  set S := B ⊔ T with hS
  set S₀ := S ⊓ normalizer (K : Set G) with hS₀
  have hSM : S ≤ M := sup_le hBM hTM
  have hBS₀ : B ≤ S₀ := le_inf le_sup_left hBN
  have hAB : A ≤ B := hA.le
  have hS₀n : ∀ x ∈ S, ∀ e ∈ S₀, x * e * x⁻¹ ∈ S₀ := by
    intro x hx e he
    refine ⟨S.mul_mem (S.mul_mem hx he.1) (S.inv_mem hx), ?_⟩
    have hK1 : K.map (MulAut.conj x⁻¹).toMonoidHom ∈ conjSetOf M K := ⟨x⁻¹, M.inv_mem (hSM hx), rfl⟩
    have he1 : (K.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj e).toMonoidHom =
        K.map (MulAut.conj x⁻¹).toMonoidHom := Subgroup.mem_normalizer_iff_map_conj_eq.1
      (uc22p2214_normalizes_of_pair hc2 hK1 (hSM he.1) he.2)
    show x * e * x⁻¹ ∈ normalizer (K : Set G)
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    show K.map (MulAut.conj (x * e * x⁻¹)).toMonoidHom = K
    have e1 : K.map (MulAut.conj (x * e * x⁻¹)).toMonoidHom =
        ((K.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj e).toMonoidHom).map
          (MulAut.conj x).toMonoidHom := by
      rw [uc22p22d_map_conj_map_conj, uc22p22d_map_conj_map_conj, mul_assoc]
    rw [e1, he1, uc22p22d_map_conj_map_conj, mul_inv_cancel]
    ext y
    simp
  have hBT : B ⊓ T = ⊥ := uc22p2214_inf_eq_bot_of_odd hBodd hT
  have hcardS : Nat.card ↥S = Nat.card B * Nat.card T := uc22p2214_card_sup_of_permutes hperm hBT
  have hAcard := hA.card_eq
  have hB0 : Nat.card B ≠ 0 := Nat.card_pos.ne'
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hS₀0 : Nat.card ↥S₀ ≠ 0 := Nat.card_pos.ne'
  have hTr : (Nat.card T).factorization r = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((Fact.out : r.Prime).dvd_of_dvd_pow h))
  have h1 : (Nat.card B).factorization r ≤ (Nat.card ↥S₀).factorization r :=
    (Nat.factorization_le_iff_dvd hB0 hS₀0).2 (Subgroup.card_dvd_of_le hBS₀) r
  have h2 : (Nat.card ↥S₀).factorization r ≤ (Nat.card ↥S).factorization r :=
    (Nat.factorization_le_iff_dvd hS₀0 Nat.card_pos.ne').2 (Subgroup.card_dvd_of_le inf_le_left) r
  have h3 : (Nat.card ↥S).factorization r = (Nat.card B).factorization r := by
    rw [hcardS, Nat.factorization_mul hB0 hT0, Finsupp.add_apply, hTr, add_zero]
  have hAS₀ : Nat.card A = r ^ (Nat.card ↥S₀).factorization r := by
    rw [hAcard]
    congr 1
    omega
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ normalizer (K : Set G) := by
    by_contra hall
    exact hTK fun t ht => by
      by_contra h
      exact hall ⟨t, ht, h⟩
  obtain ⟨e, he, x, hxS, hxA, hte⟩ := uc22p2214_frattini inf_le_left hS₀n (hAB.trans hBS₀) hAS₀ t
    (le_sup_right (a := B) htT)
  refine ⟨x, hSM hxS, fun hxK => htK ?_, hxA⟩
  rw [hte]
  exact (normalizer (K : Set G)).mul_mem he.2 hxK

theorem uc22p2214_not_mem_piSet (D : Data G) (Ch : Choice2011 G) (h8 : S22_8 D Ch) (hSg : UC6S846.SigmaStd D)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ} (hp : p ∈ D.sig) : p ∉ piSet c.B0 := by
  intro hpB
  obtain ⟨a, ha, hao⟩ := uc22p22i_exists_elt_of_mem_piSet hpB
  exact uc22p2214_false_of_sp D Ch h1930 c hpB.1 (hSg.sig1_sp p (h8 h1930 c ▸ hp)) ha hao

theorem uc22p2214_sz8_fix {X : Type} [Group X] [Finite X] (hX : IsSz X 3)
    {α : MulAut X} (hα : α ^ 3 = 1) {y : X} (hy : orderOf y = 7) (hfix : α y = y) : α = 1 := by
  by_contra hα1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hαo : orderOf α = 3 := orderOf_eq_prime hα hα1
  obtain ⟨-, -, a, ha, K, _, _, h3, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel hX
  have ha1 : a = 1 := by omega
  subst ha1
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  set f : MulAut (CFSG.Blueprint.suzukiGroup 1 K) := MulAut.congr e α with hf
  have hfo : orderOf f = 2 * 1 + 1 := by
    rw [hf, MulEquiv.orderOf_eq, hαo]
  have hcop : Nat.Coprime (2 * 1 + 1) (Nat.card (CFSG.Blueprint.suzukiGroup 1 K)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup hK)
  obtain ⟨φ⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_fixedSubgroup_suzukiGroup le_rfl hK
    (by norm_num) hcop f hfo
  have hey : e y ∈ CFSG.Open.signalizerFixedSubgroup f := by
    show e (α (e.symm (e y))) = e y
    rw [MulEquiv.symm_apply_apply, hfix]
  obtain ⟨ψ⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_suzukiGroup_zero_sz
  have h20 : Nat.card (CFSG.Open.signalizerFixedSubgroup f) = 20 := by
    rw [Nat.card_congr (φ.trans ψ).toEquiv]
    exact CFSG.SignalizerFunctorTheorem.McBride.SzModel.card_sz_zero
  have hdvd := orderOf_dvd_natCard (⟨e y, hey⟩ : CFSG.Open.signalizerFixedSubgroup f)
  rw [Subgroup.orderOf_mk, h20, MulEquiv.orderOf_eq, hy] at hdvd
  norm_num at hdvd

theorem uc22p2214_conj_injective {Q : Type} [Group Q] {L : Subgroup Q} (hq : CFSG.Open.IsQuasisimple ↥L) :
    Function.Injective (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)) := by
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := hq.2
  have hXq : CFSG.Open.IsQuasisimple (↥L ⧸ center ↥L) :=
    uc22br4_isQuasisimple_of_surjective hq (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hZX : center (↥L ⧸ center ↥L) = ⊥ := uc22p21k_center_eq_bot hXq
  intro x y h
  have hc : y⁻¹ * x ∈ center (↥L ⧸ center ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun σ : MulAut (↥L ⧸ center ↥L) => σ g) h
    simp only [MulAut.conj_apply] at h1
    calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
      _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [h1]
      _ = y⁻¹ * x * g := by group
  rw [hZX, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem uc22p2214_autQuot_ne_one {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} (hq : CFSG.Open.IsQuasisimple ↥L)
    {a : Q} (haN : a ∈ normalizer (L : Set Q)) (hnt : ∃ k ∈ L, a * k * a⁻¹ * k⁻¹ ≠ 1) :
    uc22p2214_autQuot L ⟨a, haN⟩ ≠ 1 := by
  intro h1
  obtain ⟨k, hk, hk1⟩ := hnt
  refine hk1 ?_
  have key := uc22p2214_comm_eq_one_of_central hq.1 haN (fun l hl => ?_) k hk
  · rw [key, mul_inv_cancel]
  · have h2 := congrArg (fun β : MulAut (↥L ⧸ center ↥L) => β (QuotientGroup.mk ⟨l, hl⟩)) h1
    simp only [MulAut.one_apply] at h2
    rw [uc22p2214_autQuot_mk] at h2
    have h3 := (QuotientGroup.eq_iff_div_mem (N := center ↥L)).1 h2
    exact ⟨_, h3, by simp [div_eq_mul_inv]⟩

theorem uc22p2214_quotCenter_conj (M V K : Subgroup G) {g : G} (hg : g ∈ M) :
    Nonempty ((↥(mbarImage M V K) ⧸ center ↥(mbarImage M V K)) ≃*
      (↥(mbarImage M V (K.map (MulAut.conj g).toMonoidHom)) ⧸
        center ↥(mbarImage M V (K.map (MulAut.conj g).toMonoidHom)))) := by
  have hKb' := uc22br4_mbarImage_map_conj M V K ⟨g, hg⟩
  exact uc22p2214_quotCenter_congr (((mbarImage M V K).equivMapOfInjective _ (MulAut.conj _).injective).trans
    (MulEquiv.subgroupCongr hKb'.symm))

theorem uc22p2214_case_data (D : Data G) (Ch : Choice2011 G) (h17 : S21_17 D Ch) (hn : SpU3NotList D)
    (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hcl : (IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨ (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      ((IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n) ∧ (conjSetOf D.M K).ncard = 2)) :
    ¬ K ≤ centralizer (c.V : Set G) ∧ CFSG.Open.IsQuasisimple ↥(mbarImage D.M c.V K) ∧
      Shape2214 (↥(mbarImage D.M c.V K) ⧸ center ↥(mbarImage D.M c.V K)) n ∧
      (∀ K' ∈ conjSetOf D.M K, c.B0 ≤ normalizer (K' : Set G)) ∧ ¬ F08.Thin8 (conjClosure D.M K) := by
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hO2 : CFSG.pCore 2 (MBar D.M c.V) = ⊥ := (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 hred
  have hnt : Nontrivial ↥(mbarImage D.M c.V K) := by
    rcases hcl with ⟨hsp, -⟩ | ⟨hsu, -⟩ | ⟨hL | hS, -⟩
    · exact (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp).toNontrivial
    · exact uc22p22a_qs_nontrivial hsu.1
    · exact (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL).toNontrivial
    · exact (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hS).toNontrivial
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun hle =>
    ((Subgroup.nontrivial_iff_ne_bot _).1 hnt) ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 hle)
  have hq := (uc22br4_isComponentOf_mbarImage D.M c.V K c.hVM hO2 hKC hKV).2.2
  refine ⟨hKV, hq, ?_⟩
  rcases hcl with ⟨hsp, hodd⟩ | ⟨hsu, hmod⟩ | ⟨hLS, hc2⟩
  · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp
    obtain ⟨e⟩ := uc22p2214_quotCenter_of_simple hq
    have hN : (K.subgroupOf D.M).Normal :=
      uc22p21j_normal_of_s21_17 D Ch h17 hn h1930 c.toCtx22.toCtx21 K hKC
        (Or.inl ⟨n, uc22p22a_shape_sp4 D c hKC hsp⟩)
    refine ⟨Or.inr (Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hsp))),
      uc22p2214_fix D c hKM (Or.inl hN), ?_⟩
    rw [uc22p2214_conjClosure_eq_of_normal hKM hN]
    exact uc22p2214_not_thin_single D.M c.V hKM (Or.inl hsp)
  · have hN : (K.subgroupOf D.M).Normal :=
      uc22p21j_normal_of_s21_17 D Ch h17 hn h1930 c.toCtx22.toCtx21 K hKC
        (Or.inr ⟨n, uc22p22a_shape_su3 D c hKC hsu⟩)
    have hodd : Odd n := by
      have h2 : n % 6 = 1 := hmod
      exact Nat.odd_iff.2 (by omega)
    refine ⟨Or.inr (Or.inr (Or.inr hsu.2)), uc22p2214_fix D c hKM (Or.inl hN), ?_⟩
    rw [uc22p2214_conjClosure_eq_of_normal hKM hN]
    exact uc22p2214_not_thin_single D.M c.V hKM (Or.inr ⟨hsu, hodd⟩)
  · refine ⟨?_, uc22p2214_fix D c hKM (Or.inr hc2), uc22p2214_not_thin_pair hKC hc2⟩
    rcases hLS with hL | hS
    · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
      obtain ⟨e⟩ := uc22p2214_quotCenter_of_simple hq
      exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL)
    · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hS
      obtain ⟨e⟩ := uc22p2214_quotCenter_of_simple hq
      exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hS))

theorem uc22p2214_three_dvd_card_sp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSp4 X n) : 3 ∣ Nat.card X := by
  obtain ⟨E, -, -, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three (⊤ : Subgroup X)
  have h2 := uc22p2214_two_le_pRank_sp4 hX
  have h3 : 3 ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self 3 (by omega)
  exact h3.trans (Subgroup.card_subgroup_dvd_card E)

end CFSG.LocalAnalysis.UniquenessCase.UC22
