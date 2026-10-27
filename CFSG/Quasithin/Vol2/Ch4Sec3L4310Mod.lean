module

public import CFSG.Quasithin.Vol2.Ch4Sec3L439Mod
public import CFSG.Quasithin.Vol2.Ch4Sec3Final
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

@[expose] def LemmaC136 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R₀ L S : Subgroup G) (n : ℕ) (F : Type) [Field F]
    [Fintype F] (α : ↥L →* ↥(StatedSL 3 F)),
    IsMSPair G₀ R₀ → L ∈ cComp G₀ → (G₀ : Set G) = (L : Set G) * (R₀ : Set G) →
    G₀ ≤ Subgroup.normalizer (L : Set G) → 2 ≤ n →
    Fintype.card F = 2 ^ n → IsModO2Surj L α → IsSylowTwoOf S G₀ →
    G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    IsSumOfNaturalModulesVia L (c134Q G₀ L) ⊥ α false 2 →
      G₀ ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) = pCoreOf 2 L ∧
      IsMaxElemAbelian S (pCoreOf 2 L) ∧
      ∃ A : Subgroup G, A ≤ L ∧ IsMaxElemAbelian S A ∧
        (∀ B : Subgroup G, IsMaxElemAbelian S B → B = pCoreOf 2 L ∨ B = A) ∧
        Nat.card ↥(A ⊓ pCoreOf 2 L) = 2 ^ (4 * n)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_pow_eq_mul_of_mem_normalizer {K : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) (m : ℕ) :
    ∃ k' ∈ K, (k * s) ^ m = k' * s ^ m := by
  induction m with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨k', hk', h⟩ := ih
    have hsm : s ^ m ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hs m
    refine ⟨k' * (s ^ m * k * (s ^ m)⁻¹), K.mul_mem hk'
      ((Subgroup.mem_normalizer_iff.mp hsm k).mp hk), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem charTwo_sup_of_isPGroup {K S : Subgroup G} (hK : CharTwo K) (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) : CharTwo (K ⊔ S) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hK hS hSK

omit [Finite G] in
theorem mem_cComp_sup {K S H : Subgroup G} (hK : K ∈ cComp H)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) : K ∈ cComp (K ⊔ S) := by
  obtain ⟨hne, hperf, hsub, hmin⟩ := hK
  refine ⟨hne, hperf, ?_, fun K' hK'K hK'ne hK'perf hK'sub => ?_⟩
  · exact IsSubnormal.step le_sup_left (Subgroup.normal_subgroupOf_of_le_normalizer
      (_root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hSK)) (IsSubnormal.refl _)
  · exact hmin K' hK'K hK'ne hK'perf
      (subnormal_trans (subnormal_of_le_of_le hK'sub hK'K.le le_sup_left) hsub)

omit [Finite G] in
theorem isRankTwoLie2Derived_of_equiv_statedSL {X : Type} [Group X] {F : Type} [Field F]
    [Fintype F] {m : ℕ} (hm : 1 ≤ m) (hF : Fintype.card F = 2 ^ m) (e : X ≃* ↥(StatedSL 3 F)) :
    IsRankTwoLie2Derived (X ⧸ Subgroup.center X) := by
  left
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (specialLinearGroupEquivStatedSL 3 F).symm
  have hc : (Subgroup.center X).map e'.toMonoidHom =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Subgroup.map_center_eq e'
  refine ⟨m, ⟨Nat.prime_two, hm, by norm_num, by simp, by simp⟩, F, inferInstance, inferInstance,
    by rw [Nat.card_eq_fintype_card, hF], ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e' hc).trans (projectiveSpecialLinearGroupEquivStatedProj 3 F)

omit [Finite G] in
theorem isMaxElemAbelian_map_conj {S A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hA : IsMaxElemAbelian S A) :
    IsMaxElemAbelian S (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hAS, ⟨hc, hp⟩, hmax⟩ := hA
  refine ⟨?_, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, fun B hB hBe => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp (hAS ha)
  · rcases x with ⟨_, a, ha, rfl⟩
    rcases y with ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    have hab : a * b = b * a := setLike_mul_comm ha hb
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hab]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    show (g * a * g⁻¹) ^ 2 = 1
    rw [conj_pow, hp a ha, mul_one, mul_inv_cancel]
  · have h1 := hmax B hB hBe
    rwa [← Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv]

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem isMSPair_sup (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hchar : CharTwo K) {V : Subgroup G}
    (hc3 : C41Case3 H (pCoreOf 2 I) (H ⊓ M) L V K) :
    IsMSPair (K ⊔ (T ⊓ H)) (T ⊓ H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := T ⊓ H with hS
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := sk.S_le_normalizer
  have hSsylH := sk.base.isSylowTwoOf_S_H hR hC h37 h38 h39
  have hKH : K ≤ H := le_of_mem_cComp sk.cComp
  have hKSH : K ⊔ S ≤ H := _root_.sup_le hKH inf_le_right
  have hHloc : pCoreOf 2 H ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal sk.base.inM.1.1
  have hsqtk : IsSQTKIn (K ⊔ S) :=
    IsSQTKIn.mono (sqtkGroup_of_pCoreOf_ne_bot sk.base.hyp.qtke sk.base.hyp.simple
      sk.base.hyp.nonabelian hHloc) hKSH
  obtain ⟨m, F, _, _, hm, hF, ⟨e⟩, -, -, -, -, -⟩ := hc3
  have hSsyl : IsSylowTwoOf S (K ⊔ S) := by
    refine ⟨le_sup_right, hSsylH.2.1, fun h2 => hSsylH.2.2 ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex S (K ⊔ S) H le_sup_right hKSH
    exact h2.trans (Dvd.intro _ h1)
  refine ⟨⟨hsqtk, charTwo_sup_of_isPGroup hchar hSsylH.2.1 hSK, K,
    mem_cComp_sup sk.cComp hSK, Subgroup.coe_mul_of_right_le_normalizer_left K S hSK,
    isRankTwoLie2Derived_of_equiv_statedSL (by omega) hF e⟩,
    Or.inl ⟨S, ?_, hSsyl.2.2, (le_antisymm (pCoreOf_le 2 S) (le_pCoreOf_of_le_normalizer 2 le_rfl
      (fun x hx => Subgroup.le_normalizer hx) hSsylH.2.1)).symm⟩, ?_⟩
  · refine lt_of_le_of_ne le_sup_right fun hT => ?_
    have hKS : K ≤ S := hT ▸ le_sup_left
    have hsol : Group.IsSolvable ↥S := by
      have := hSsylH.2.1.isNilpotent
      infer_instance
    exact not_isSolvable_of_mem_cComp sk.cComp
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKS)
        (Subgroup.inclusion_injective hKS))
  · intro C hCS hC hchC hKSC
    have htC : t ∈ Subgroup.normalizer (C : Set G) := by
      have h1 := normalizer_le_normalizer_map_of_characteristic (C.subgroupOf S) sk.t_normalizer
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCS] at h1
    have hLC : L ⊔ (S ⊔ Subgroup.zpowers t) ≤ Subgroup.normalizer (C : Set G) :=
      _root_.sup_le (sk.L_le_K.trans (le_sup_left.trans hKSC))
        (_root_.sup_le (le_sup_right.trans hKSC) (Subgroup.zpowers_le.mpr htC))
    have hN := isUniqueM_normalizer_le sk.lemma_4_3_5 hC (hSsylH.2.1.to_le hCS) hLC
    exact sk.not_le (le_inf hKH ((le_sup_left.trans hKSC).trans hN))

theorem not_isC134Case2 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hKG : SL3ParabolicAutFact) (h136 : LemmaC136)
    (hchar : CharTwo K) {V : Subgroup G} (h438 : Concl438 H (pCoreOf 2 I) (H ⊓ M) L V K)
    (hCS : T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    ¬ IsC134Case 2 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K := by
  classical
  intro h2
  obtain ⟨⟨n₂, F₂, _, _, α, hF₂, hαm, hN⟩, -⟩ := (h2 : IsC134Case2 _ _ _)
  set S := T ⊓ H with hS
  set R := pCoreOf 2 I with hRdef
  set U := pCoreOf 2 K with hU
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := sk.S_le_normalizer
  have hOS : U ≤ S := sk.pCoreOf_K_le_S hR hC h37 h38 h39
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp sk.cComp
  have hLK := sk.L_le_K
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := sk.base.pCoreOf_le_S.trans hSK
  have hSsylH := sk.base.isSylowTwoOf_S_H hR hC h37 h38 h39
  have hKH : K ≤ H := le_of_mem_cComp sk.cComp
  have hKSH : K ⊔ S ≤ H := _root_.sup_le hKH inf_le_right
  have hKSN : K ⊔ S ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hSK
  have hSsyl : IsSylowTwoOf S (K ⊔ S) := by
    refine ⟨le_sup_right, hSsylH.2.1, fun h2 => hSsylH.2.2 ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex S (K ⊔ S) H le_sup_right hKSH
    exact h2.trans (Dvd.intro _ h1)
  have hQX : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (K : Set G) →
      c134Q (K ⊔ X) K = ⁅U, K⁆ := by
    intro X hX
    have hKXN : K ⊔ X ≤ Subgroup.normalizer (K : Set G) :=
      _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hX
    have hUO : U ≤ pCoreOf 2 (K ⊔ X) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
        (hKXN.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
    refine le_antisymm ?_ (Subgroup.commutator_mono hUO le_rfl)
    have h1 := (commutator_le_pCoreOf_of_le hperf hX le_rfl).1
    have hON : pCoreOf 2 (K ⊔ X) ≤ Subgroup.normalizer (K : Set G) :=
      (pCoreOf_le 2 _).trans hKXN
    show ⁅pCoreOf 2 (K ⊔ X), K⁆ ≤ ⁅U, K⁆
    rw [commutator_eq_commutator_commutator_of_perfect' hperf hON]
    exact Subgroup.commutator_mono h1 le_rfl
  have hQeq : c134Q (K ⊔ S) K = c134Q (K ⊔ R) K := (hQX S hSK).trans (hQX R hRK).symm
  have hQU : c134Q (K ⊔ R) K ≤ U := (commutator_le_pCoreOf_of_le hperf hRK le_rfl).1
  have hchKS := charTwo_sup_of_isPGroup hchar hSsylH.2.1 hSK
  have hCKS : (K ⊔ S) ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
    set N := (K ⊔ S) ⊓ Subgroup.centralizer (K : Set G) with hNdef
    have hNN : K ⊔ S ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
      mem_normalizer_inf (Subgroup.le_normalizer hx) (mem_normalizer_centralizer_of_mem (hKSN hx))
    have hNS : N ⊓ S = ⊥ := by
      rw [eq_bot_iff, ← hCS]
      exact fun x hx => ⟨hx.2, hx.1.2⟩
    have hOKS : pCoreOf 2 (K ⊔ S) ≤ S := pCoreOf_two_le_of_isSylowTwoOf hSsyl
    have hNC : N ≤ (K ⊔ S) ⊓ Subgroup.centralizer (pCoreOf 2 (K ⊔ S) : Set G) := by
      intro x hx
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hyKS : y ∈ K ⊔ S := pCoreOf_le 2 _ hy
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (hNN hyKS) x⁻¹).mp (N.inv_mem hx)
        have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [e]
        exact N.mul_mem hx this
      have h2 : x * y * x⁻¹ * y⁻¹ ∈ S := by
        apply hOKS
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hx.1) y).mp hy
        exact (pCoreOf 2 (K ⊔ S)).mul_mem this ((pCoreOf 2 (K ⊔ S)).inv_mem hy)
      have h3 : x * y * x⁻¹ * y⁻¹ = 1 := by
        rw [← Subgroup.mem_bot, ← hNS]
        exact ⟨h1, h2⟩
      have h4 : x * y = y * x := by
        calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
          _ = y * x := by rw [h3, one_mul]
      exact h4.symm
    have hNS' : N ≤ S := hNC.trans (hchKS.trans hOKS)
    rw [eq_bot_iff]
    intro x hx
    rw [← hNS]
    exact ⟨hx, hNS' hx⟩
  obtain ⟨m, F, _, _, W, α', β', W', hm, hF, -, hnat, hW', hY₀ne, hY₀perf, hstab₀, hPnorm⟩ :=
    sk.exists_parabolicData h438.1
  have hα' := hnat.2.1
  have hkerα' := hnat.2.2.1
  have hcard : Fintype.card F = Fintype.card F₂ :=
    card_eq_of_card_statedSL_eq ((card_modO2_of_surjective α' hα' hkerα').symm.trans
      (card_modO2_of_surjective α hαm.1 hαm.2))
  have hn₂ : 2 ≤ n₂ := by
    have h1 : 2 ^ m = 2 ^ n₂ := hF.symm.trans (hcard.trans hF₂)
    rw [← Nat.pow_right_injective (le_refl 2) h1]
    exact hm
  obtain ⟨c, hc0, hc1, hcc⟩ := exists_good_scalar hm (hcard.symm.trans hF)
  obtain ⟨hUC, hUmax, A, hAK, hAmax, hAS, hAcard⟩ := h136 G (K ⊔ S) S K S n₂ F₂ α
    (sk.isMSPair_sup hR hC h37 h38 h39 hchar h438.1) (mem_cComp_sup sk.cComp hSK)
    (Subgroup.coe_mul_of_right_le_normalizer_left K S hSK) hKSN hn₂ hF₂ hαm hSsyl hCKS
    (hQeq ▸ hN)
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    intro x hx y hy
    have hxC : x ∈ (K ⊔ S) ⊓ Subgroup.centralizer (U : Set G) := by rw [hUC]; exact hx
    exact (Subgroup.mem_centralizer_iff.mp hxC.2 y hy).symm
  have hUQ : U ≤ c134Q (K ⊔ R) K := by
    intro x hx
    have hxker : ∀ a : ↥K, α a = 1 → (a : G) * x = x * a := by
      intro a ha
      have h1 : a ∈ α.ker := ha
      rw [hαm.2] at h1
      exact hUab _ ((mem_pCoreOf_iff' a).mpr h1) x hx
    have hxK : ∀ g ∈ K, x⁻¹ * (g * x * g⁻¹) ∈ c134Q (K ⊔ R) K := by
      intro g hg
      rw [hQX R hRK]
      have h1 : ⁅x⁻¹, g⁆ ∈ ⁅U, K⁆ := Subgroup.commutator_mem_commutator (U.inv_mem hx) hg
      have e : ⁅x⁻¹, g⁆ = x⁻¹ * (g * x * g⁻¹) := by
        simp only [commutatorElement_def, inv_inv]; group
      rwa [e] at h1
    obtain ⟨n₁, hn₁Q, hxn⟩ :=
      exists_mul_mem_centralizer_of_natural hc0 hc1 hcc hαm.1 hN hxker hxK
    have h1 : x * n₁ ∈ S ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨hOS (U.mul_mem hx (hQU hn₁Q)), hxn⟩
    rw [hCS] at h1
    have h3 : x = n₁⁻¹ := eq_inv_of_mul_eq_one_left (Subgroup.mem_bot.mp h1)
    rw [h3]
    exact (c134Q (K ⊔ R) K).inv_mem hn₁Q
  have hUeq : U = c134Q (K ⊔ R) K := le_antisymm hUQ hQU
  rw [← hUeq] at hN
  obtain ⟨hKU, -, β, hβ, hβker, hβeq⟩ := hN
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have htS : t ∈ Subgroup.normalizer (S : Set G) := sk.t_normalizer
  have htL : t ∈ Subgroup.normalizer (L : Set G) :=
    sk.base.hyp.normal (sk.base.hyp.T_le sk.t_mem)
  have hUt : IsMaxElemAbelian S (U.map (MulAut.conj t).toMonoidHom) :=
    isMaxElemAbelian_map_conj htS hUmax
  have hUtne : U.map (MulAut.conj t).toMonoidHom ≠ U := by
    intro heq
    apply sk.not_commutator_conj_blockU_le hR hC h37 h38 h39 hchar
    have hbU : blockU K ≤ U := commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 K)
    have h1 : (blockU K).map (MulAut.conj t).toMonoidHom ≤ U :=
      (map_conj_mono hbU t).trans heq.le
    exact (Subgroup.commutator_mono h1 le_rfl).trans
      (commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 K))
  have hUtA : U.map (MulAut.conj t).toMonoidHom = A := (hAS _ hUt).resolve_left hUtne
  have hAt : A.map (MulAut.conj t).toMonoidHom = U := by
    rcases hAS _ (isMaxElemAbelian_map_conj htS hAmax) with h | h
    · exact h
    · exfalso
      have ht2 : t * t ∈ Subgroup.normalizer (U : Set G) := by
        have h1 : t * t ∈ S := by rw [← pow_two]; exact sk.t_sq
        exact normalizer_le_normalizer_pCoreOf 2 K (hSK h1)
      have hU2 := map_conj_eq_of_mem_normalizer ht2
      rw [map_conj_mul, hUtA, h] at hU2
      exact hUtne (hUtA.trans hU2)
  have hLA : L ≤ Subgroup.normalizer (A : Set G) := by
    intro l hl
    rw [← hUtA]
    have hl' : t⁻¹ * l * t ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htL) l).mp hl
      simpa using h1
    have hlU : t⁻¹ * l * t ∈ Subgroup.normalizer (U : Set G) :=
      le_normalizer_pCoreOf 2 K (hLK hl')
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨(t⁻¹ * l * t) * u * (t⁻¹ * l * t)⁻¹, (Subgroup.mem_normalizer_iff.mp hlU u).mp hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  let cU : ↥K → ↥U → ↥U := fun g u =>
    ⟨g * u * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU g.2) u).mp u.2⟩
  have hcU : ∀ (g : ↥K) (u : ↥U) (i : Fin 2),
      Multiplicative.toAdd (β (cU g u)) i =
        ((α g : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec
          (Multiplicative.toAdd (β u) i) := by
    intro g u i
    have h := hβeq g u (cU g u) rfl i
    simpa [moduleAct] using h
  let C₀ : Submodule F₂ (Fin 3 → F₂) :=
    { carrier := {x | ∀ a : ↥K, (a : G) ∈ A →
        ((α a : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec x = x}
      add_mem' := fun {x y} hx hy a ha => by rw [Matrix.mulVec_add, hx a ha, hy a ha]
      zero_mem' := fun a _ => Matrix.mulVec_zero _
      smul_mem' := fun r x hx a ha => by rw [Matrix.mulVec_smul, hx a ha] }
  have hmemC₀ : ∀ x, x ∈ C₀ ↔ ∀ a : ↥K, (a : G) ∈ A →
      ((α a : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec x = x := fun _ => Iff.rfl
  have hcentA : ∀ u : ↥U, (∀ i, Multiplicative.toAdd (β u) i ∈ C₀) →
      (u : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro u hu
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have haK : a ∈ K := hAK ha
    have h1 : cU ⟨a, haK⟩ u = u := by
      apply hβinj
      apply Multiplicative.toAdd.injective
      funext i
      rw [hcU]
      exact (hmemC₀ _).mp (hu i) ⟨a, haK⟩ ha
    have h2 : a * u * a⁻¹ = u := congrArg Subtype.val h1
    calc a * (u : G) = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h2]
  have hAU : ¬ A ≤ U := by
    intro hle
    exact hUtne (hUtA.trans (Subgroup.eq_of_le_of_card_ge hle
      (hAmax.2.2 U hUmax.1 hUmax.2.1)))
  have hcardF₂ : 2 ≤ Fintype.card F₂ := Fintype.one_lt_card
  have hdim : Module.finrank F₂ C₀ = 2 := by
    have hcoord : ∀ (u : ↥U), (u : G) ∈ A → ∀ i, Multiplicative.toAdd (β u) i ∈ C₀ := by
      intro u huA i
      refine (hmemC₀ _).mpr fun a ha => ?_
      have h1 : cU a u = u := by
        apply Subtype.ext
        show (a : G) * u * (a : G)⁻¹ = u
        have := hAmax.2.1.1
        rw [setLike_mul_comm ha huA, mul_inv_cancel_right]
      rw [← hcU, h1]
    let φ : ↥(A ⊓ U) → (Fin 2 → ↥C₀) := fun x i =>
      ⟨Multiplicative.toAdd (β ⟨x, x.2.2⟩) i, hcoord ⟨x, x.2.2⟩ x.2.1 i⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : β ⟨x, x.2.2⟩ = β ⟨y, y.2.2⟩ := by
        apply Multiplicative.toAdd.injective
        funext i
        exact congrArg Subtype.val (congrFun hxy i)
      exact Subtype.ext (congrArg (fun z : ↥U => (z : G)) (hβinj h1))
    have h1 := Nat.card_le_card_of_injective φ hφ
    rw [hAcard, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := ↥C₀),
      Module.card_eq_pow_finrank (K := F₂) (V := ↥C₀), hF₂, ← pow_mul, ← pow_mul] at h1
    have hd3 : Module.finrank F₂ C₀ ≤ 3 := by
      have := Submodule.finrank_le C₀
      rwa [Module.finrank_fin_fun] at this
    have hn₂ : 1 ≤ n₂ := by
      by_contra h0
      have : n₂ = 0 := by omega
      rw [this, pow_zero] at hF₂
      omega
    have hd2 : 2 ≤ Module.finrank F₂ C₀ := by
      have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
      by_contra hlt
      have h3 : Module.finrank F₂ C₀ ≤ 1 := by omega
      have h4 : n₂ * (Module.finrank F₂ C₀ * 2) ≤ n₂ * 2 :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rcases Nat.lt_or_ge (Module.finrank F₂ C₀) 3 with h | h
    · omega
    · exfalso
      have htop : C₀ = ⊤ := Submodule.eq_top_of_finrank_eq (by
        rw [Module.finrank_fin_fun]; omega)
      apply hAU
      intro a ha
      have haC : a ∈ (K ⊔ S) ⊓ Subgroup.centralizer (U : Set G) := by
        refine ⟨Subgroup.mem_sup_left (hAK ha), Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
        have h2 := hcentA ⟨u, hu⟩ (fun i => by rw [htop]; trivial)
        exact (Subgroup.mem_centralizer_iff.mp h2 a ha).symm
      rw [hUC] at haC
      exact haC
  set Y₁ : Subgroup (GL (Fin 3) F₂) :=
    ((L.subgroupOf K).map α).map (StatedSL 3 F₂).subtype with hY₁
  have hY₁perf : ⁅Y₁, Y₁⁆ = Y₁ := by
    have hAmap : (L.subgroupOf K).map K.subtype = L := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hLK
    have hAperf : ⁅L.subgroupOf K, L.subgroupOf K⁆ = L.subgroupOf K := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, hAmap, sk.base.hyp.commutator_eq]
    rw [hY₁, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hAperf]
  have hY₁stab : ∀ y ∈ Y₁, ∀ x ∈ C₀, (y : Matrix (Fin 3) (Fin 3) F₂).mulVec x ∈ C₀ := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩ x hx
    refine (hmemC₀ _).mpr fun a ha => ?_
    have hl' : (l : G) ∈ L := hl
    have hla : ((l⁻¹ * a * l : ↥K) : G) ∈ A := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hLA hl')) a).mp ha
      simpa [mul_assoc] using h1
    have h2 : α a * α l = α l * α (l⁻¹ * a * l) := by
      rw [map_mul, map_mul, map_inv]; group
    have h3 := congrArg (fun g : ↥(StatedSL 3 F₂) =>
      ((g : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂)) h2
    simp only [Subgroup.coe_mul, Units.val_mul] at h3
    show ((α a : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec
        (((α l : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec x) =
      ((α l : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec x
    rw [Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec, (hmemC₀ x).mp hx _ hla]
  have hULC : ⁅U, L⁆ ≤ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hlK : l ∈ K := hLK hl
    let w : ↥U := ⟨u, hu⟩ * cU ⟨l, hlK⟩ ⟨u, hu⟩⁻¹
    have hw : (w : G) = ⁅u, l⁆ := by
      show u * (l * u⁻¹ * l⁻¹) = u * l * u⁻¹ * l⁻¹
      group
    rw [← hw]
    refine hcentA w fun i => ?_
    have hyY : ((α ⟨l, hlK⟩ : ↥(StatedSL 3 F₂)) : GL (Fin 3) F₂) ∈ Y₁ :=
      ⟨α ⟨l, hlK⟩, ⟨⟨l, hlK⟩, hl, rfl⟩, rfl⟩
    have h1 := mulVec_sub_mem_of_perfect C₀ hdim Y₁ hY₁perf hY₁stab hyY
      (Multiplicative.toAdd (β ⟨u, hu⟩) i)
    have h2 : Multiplicative.toAdd (β w) i = -(((α ⟨l, hlK⟩ : GL (Fin 3) F₂) :
        Matrix (Fin 3) (Fin 3) F₂).mulVec (Multiplicative.toAdd (β ⟨u, hu⟩) i) -
          Multiplicative.toAdd (β ⟨u, hu⟩) i) := by
      show Multiplicative.toAdd (β (⟨u, hu⟩ * cU ⟨l, hlK⟩ ⟨u, hu⟩⁻¹)) i = _
      rw [map_mul, toAdd_mul, Pi.add_apply, hcU, map_inv, toAdd_inv, Pi.neg_apply,
        Matrix.mulVec_neg]
      abel
    rw [h2]
    exact C₀.neg_mem h1
  have hALU : ⁅A, L⁆ ≤ U := by
    have h1 : ⁅A, L⁆ = (⁅U, L⁆).map (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.map_commutator, hUtA, map_conj_eq_of_mem_normalizer htL]
    rw [h1]
    rintro _ ⟨w, hw, rfl⟩
    have hwU : w ∈ U := commutator_le_left_of_le_normalizer
      (hLK.trans (le_normalizer_pCoreOf 2 K)) hw
    have hwC := hULC hw
    show t * w * t⁻¹ ∈ U
    have hmem : t * w * t⁻¹ ∈ (K ⊔ S) ⊓ Subgroup.centralizer (U : Set G) := by
      refine ⟨Subgroup.mem_sup_left (hAK (by rw [← hUtA]; exact ⟨w, hwU, rfl⟩)), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [← hAt] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      have hwb := Subgroup.mem_centralizer_iff.mp hwC b hb
      show t * b * t⁻¹ * (t * w * t⁻¹) = t * w * t⁻¹ * (t * b * t⁻¹)
      calc t * b * t⁻¹ * (t * w * t⁻¹) = t * (b * w) * t⁻¹ := by group
        _ = t * (w * b) * t⁻¹ := by rw [hwb]
        _ = t * w * t⁻¹ * (t * b * t⁻¹) := by group
    rw [hUC] at hmem
    exact hmem
  obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ U := by
    by_contra h
    push Not at h
    exact hAU h
  have haK : a ∈ K := hAK haA
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hAmax.2.1.2 a haA
  have haL : ∀ l ∈ L, ⁅a, l⁆ ∈ pCoreOf 2 K := fun l hl =>
    hALU (Subgroup.commutator_mem_commutator haA hl)
  have haKK := commutator_mem_pCoreOf_of_involution hKG hm hF hα' hkerα' hW' hY₀ne hY₀perf
    hstab₀ hPnorm (Subgroup.le_normalizer haK) ha2 haL
  have hcent : ∀ γ : ↥(StatedSL 3 F), α' ⟨a, haK⟩ * γ = γ * α' ⟨a, haK⟩ := by
    intro γ
    obtain ⟨k, rfl⟩ := hα' γ
    have h1 := haKK k k.2
    have h2 : α' (⟨a, haK⟩ * k * (⟨a, haK⟩ : ↥K)⁻¹ * k⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hkerα', ← mem_pCoreOf_iff']
      simpa [commutatorElement_def] using h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc α' ⟨a, haK⟩ * α' k =
          (α' ⟨a, haK⟩ * α' k * (α' ⟨a, haK⟩)⁻¹ * (α' k)⁻¹) * (α' k * α' ⟨a, haK⟩) := by
          group
      _ = α' k * α' ⟨a, haK⟩ := by rw [h2, one_mul]
  set Ma := ((α' ⟨a, haK⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hMa
  have hscal : Ma ∈ Set.range (Matrix.scalar (Fin 3)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun ts => ?_
    have h1 := hcent (specialLinearGroupEquivStatedSL 3 F ts.toSpecialLinearGroup)
    have h2 := congrArg (fun g : ↥(StatedSL 3 F) =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, specialLinearGroupEquivStatedSL_coe,
      Matrix.TransvectionStruct.toSpecialLinearGroup_coe] at h2
    exact h2.symm
  obtain ⟨r, hr⟩ := hscal
  have hMa2 : Ma * Ma = 1 := by
    have h1 : α' ⟨a, haK⟩ * α' ⟨a, haK⟩ = 1 := by
      rw [← map_mul]
      convert map_one α'
      exact Subtype.ext ha2
    have h2 := congrArg (fun g : ↥(StatedSL 3 F) =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
    simpa using h2
  have hdet : Ma.det = 1 := by
    obtain ⟨γ, hγ⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective (α' ⟨a, haK⟩)
    have h1 : Ma = (γ : Matrix (Fin 3) (Fin 3) F) := by
      rw [hMa, ← hγ]
      exact specialLinearGroupEquivStatedSL_coe 3 F γ
    rw [h1]
    exact γ.2
  rw [← hr] at hMa2 hdet
  have hr2 : r * r = 1 := by
    have h1 := congrFun (congrFun hMa2 0) 0
    simpa [Matrix.scalar_apply] using h1
  have hr3 : r ^ 3 = 1 := by
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdet
  have hr1 : r = 1 := by
    have h1 : r ^ 3 = r * (r * r) := by ring
    rw [h1, hr2, mul_one] at hr3
    exact hr3
  have hα'a : α' ⟨a, haK⟩ = 1 := by
    apply Subtype.ext
    apply Units.ext
    show Ma = 1
    rw [← hr, hr1, map_one]
  have h1 : (⟨a, haK⟩ : ↥K) ∈ α'.ker := hα'a
  rw [hkerα'] at h1
  exact haU ((mem_pCoreOf_iff' _).mpr h1)

end Setting432K

theorem lemma4310Two_holds (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hKG : SL3ParabolicAutFact) (h136 : LemmaC136) :
    Lemma4310Two :=
  fun _ _ _ _ _ _ _ _ _ _ _ sk hchar _ h438 hCS =>
    sk.not_isC134Case2 hR hC h37 h38 h39 hKG h136 hchar h438 hCS

theorem stmt4_3_2_of_steps' (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h436 : Lemma436Comp) (hSp4 : Lemma437Sp4) (hA7 : Lemma437A7) (hKG : SL3ParabolicAutFact)
    (h136 : LemmaC136) (hEnd : Lemma43End) : Stmt4_3_2 :=
  stmt4_3_2_of_steps hR hC hC48 h36 h37 h38 h39 h436 hSp4 hA7 hKG
    (lemma439Fix_holds hR hC h37 h38 h39 hKG) (lemma4310Two_holds hR hC h37 h38 h39 hKG h136) hEnd

end CFSG.Quasithin.H13.Ch4
