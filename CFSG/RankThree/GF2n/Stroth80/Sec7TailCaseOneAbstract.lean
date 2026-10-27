module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSimpleFactorsAut
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOneLie
public import CFSG.RankThree.GF2n.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem commute_of_proj_eq_one {Y : Type} [Group Y] {ι : Type} {Gs : Subgroup Y}
    {X : ι → Subgroup Y} {π : ι → ↥Gs →* Y} (hπ : IsProj Gs X π) (hle : ∀ i, X i ≤ Gs) (i : ι)
    {x : Y} (hx : x ∈ X i) (w : ↥Gs) (hw : π i w = 1) : x * (w : Y) = (w : Y) * x := by
  have hxG : x ∈ Gs := hle i hx
  have key : (⟨x, hxG⟩ : ↥Gs) * w = w * ⟨x, hxG⟩ := by
    apply hπ.inj
    intro j
    rw [map_mul, map_mul]
    by_cases hij : j = i
    · subst hij
      rw [hw, mul_one, one_mul, hπ.self j ⟨x, hxG⟩ hx]
    · rw [hπ.other j i hij ⟨x, hxG⟩ hx, one_mul, mul_one]
  exact congrArg Subtype.val key

theorem exists_hom_perfect_simple {Y : Type} [Group Y] [Finite Y] {E N R : Subgroup Y}
    (hER : E ≤ R) (hNR : N ≤ R) (hEN : E ⊔ N = R) (hN2 : IsPGroup 2 N)
    [(N.subgroupOf R).Normal] {S : Type} [Group S] (eRN : (↥R ⧸ N.subgroupOf R) ≃* S) :
    ∃ θ : ↥E →* S, Function.Surjective θ ∧ IsPGroup 2 θ.ker := by
  classical
  let θ : ↥E →* S :=
    eRN.toMonoidHom.comp ((QuotientGroup.mk' (N.subgroupOf R)).comp (Subgroup.inclusion hER))
  have hθ : ∀ e : ↥E, θ e = eRN (QuotientGroup.mk (⟨(e : Y), hER e.2⟩ : ↥R)) := fun e => rfl
  refine ⟨θ, ?_, ?_⟩
  · intro s
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (eRN.symm s)
    have hsup : E.subgroupOf R ⊔ N.subgroupOf R = ⊤ := by
      apply Subgroup.map_injective R.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hER,
        Subgroup.map_subgroupOf_eq_of_le hNR, hEN, Subgroup.map_top, Subgroup.range_subtype]
    have hcm : c ∈ E.subgroupOf R ⊔ N.subgroupOf R := by rw [hsup]; exact Subgroup.mem_top c
    obtain ⟨e₁, he₁, n₁, hn₁, hen⟩ := Subgroup.mem_sup_of_normal_right.mp hcm
    refine ⟨⟨(e₁ : Y), Subgroup.mem_subgroupOf.mp he₁⟩, ?_⟩
    rw [hθ]
    have h1 : (QuotientGroup.mk c : ↥R ⧸ N.subgroupOf R) = QuotientGroup.mk e₁ := by
      rw [← hen, QuotientGroup.mk_mul]
      have : (QuotientGroup.mk n₁ : ↥R ⧸ N.subgroupOf R) = 1 :=
        (QuotientGroup.eq_one_iff n₁).mpr hn₁
      rw [this, mul_one]
    have h2 : (⟨(e₁ : Y), hER (Subgroup.mem_subgroupOf.mp he₁)⟩ : ↥R) = e₁ := rfl
    show eRN (QuotientGroup.mk (⟨(e₁ : Y), _⟩ : ↥R)) = s
    rw [h2, ← h1, hc]
    exact eRN.apply_symm_apply s
  · have hmem : ∀ x : ↥θ.ker, ((x : ↥E) : Y) ∈ N := by
      intro x
      have h1 : θ (x : ↥E) = 1 := x.2
      rw [hθ, map_eq_one_iff _ eRN.injective, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at h1
      exact h1
    let f : ↥θ.ker →* ↥N := MonoidHom.codRestrict ((E.subtype).comp θ.ker.subtype) N hmem
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    exact hN2.of_injective f hf

theorem no_beta
    (hOut : OutSolvableListStatement) (hBorel : BorelRankOneSolvableStatement)
    {Y : Type} [Group Y] [Finite Y] (q : ℕ) (hq4 : 4 ≤ q)
    (V N R K Gs : Subgroup Y) [hGsn : Gs.Normal]
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥)
    (hCGs : ∀ c : Y, (∀ s ∈ Gs, c * s = s * c) → c = 1)
    (hVGs : V ≤ Gs) (hVab : IsElemAbelian 2 V) (hti : IsTI V)
    (hKV : ∀ g ∈ normalizer (V : Set Y), g ∈ K) (hKnV : ∀ k ∈ K, k ∈ normalizer (V : Set Y))
    (hNR : N ≤ R) (hRK : R ≤ K) (hN2 : IsPGroup 2 N)
    (hpc : ∀ P : Subgroup Y, P ≤ K → (∀ k ∈ K, k ∈ normalizer (P : Set Y)) → IsPGroup 2 P →
      P ≤ N)
    (hNn : ∀ k ∈ K, k ∈ normalizer (N : Set Y))
    (hCKN : ∀ k ∈ K, (∀ n ∈ N, k * n = n * k) → k ∈ N)
    (hVcard : Nat.card V = q) (hNcard : Nat.card N = q ^ 9)
    (K₀ : Type) [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = q)
    (hRN : ∃ _ : (N.subgroupOf R).Normal,
      Nonempty ((↥R ⧸ N.subgroupOf R) ≃* StatedProj (StatedSL 4 K₀)))
    (r : ℕ) (X : Fin r → Subgroup ↥Gs) (hXn : ∀ i, (X i).Normal)
    (hXc : ∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) (hXgen : ⨆ i, X i = ⊤)
    (hXcov : ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i)) :
    False := by
  classical
  obtain ⟨hnormNR, ⟨eRN⟩⟩ := hRN
  obtain ⟨ι, hι, Xs, hSF, hlist, hBor⟩ :=
    simpleFactors_of_beta hBorel Gs hO2 hO r X hXn hXc hXgen hXcov
  obtain ⟨π, hπ⟩ := exists_isProj hSF
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by simpa [sq] using hVab.2 v hv
  have hNn' : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := fun k hk n hn =>
    (Subgroup.mem_normalizer_iff.mp (hNn k hk) n).mp hn
  have hne : ∀ i, ∃ v : ↥Gs, (v : Y) ∈ V ∧ π i v ≠ 1 := by
    intro i
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ x ∈ Xs i, ∀ v ∈ V, x * v = v * x := fun x hx v hv =>
      commute_of_proj_eq_one hπ hSF.le i hx ⟨v, hVGs hv⟩ (hcon ⟨v, hVGs hv⟩ hv)
    have hXK : Xs i ≤ K := by
      intro x hx
      refine hKV x ?_
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have : x * h * x⁻¹ = h := by
          rw [hcomm x hx h hh]
          simp
        rw [this]
        exact hh
      · intro hh
        have h1 : x * (x * h * x⁻¹) = (x * h * x⁻¹) * x := hcomm x hx _ hh
        have h2 : x * h * x⁻¹ = h :=
          calc x * h * x⁻¹ = x⁻¹ * (x * (x * h * x⁻¹)) := by group
            _ = x⁻¹ * ((x * h * x⁻¹) * x) := by rw [h1]
            _ = h := by group
        rw [h2] at hh
        exact hh
    exact no_component Gs K N (Xs i) hSF.gnormal hN2 hNn' hCKN hXK (hSF.le i)
      (hSF.normal i) (hSF.simple i) (hSF.nonab i)
  have hinj := fun i => proj_injOn_of_ne hSF hπ V hVGs hV2 hti i (hne i)
  have hKnV' : ∀ k ∈ K, conjSubgroup k V = V := fun k hk =>
    conjSubgroup_eq_self_iff.mpr (hKnV k hk)
  have hpc' : ∀ P : Subgroup Y, P ≤ K → (∀ k ∈ K, conjSubgroup k P = P) → IsPGroup 2 P → P ≤ N :=
    fun P hPK hP hP2 => hpc P hPK (fun k hk => conjSubgroup_eq_self_iff.mp (hP k hk)) hP2
  have hcard9 : Fintype.card ι ≤ 9 :=
    card_le_nine hSF hπ V N K hVGs hV2 hinj hKnV' hKV hpc' q (by omega) hVcard hNcard
  obtain ⟨hsimp4, hnab4⟩ := statedProj_statedSL_four_simple_nonabelian K₀
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 K₀)) := hsimp4
  haveI : Finite (StatedProj (StatedSL 4 K₀)) := Finite.of_equiv _ eRN.toEquiv
  have hperf4 : Group.IsPerfect (StatedProj (StatedSL 4 K₀)) :=
    isPerfect_of_simple_nonabelian hnab4
  have hperfRN : commutator (↥R ⧸ N.subgroupOf R) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := eRN.symm.toMonoidHom) eRN.symm.surjective
      (G := StatedProj (StatedSL 4 K₀))).commutator_eq_top
  obtain ⟨E, hER, hEperf, hEN, hEn⟩ := exists_perfect_sup_eq hNR hperfRN
  have hEne : E ≠ ⊥ := by
    intro h
    have hRN' : R ≤ N := by
      rw [← hEN, h, bot_sup_eq]
    haveI : Subsingleton (↥R ⧸ N.subgroupOf R) := by
      have : N.subgroupOf R = ⊤ := Subgroup.subgroupOf_eq_top.mpr hRN'
      rw [this]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨a, b, hab⟩ := hnab4
    exact hab (by
      have := Subsingleton.elim (eRN.symm a) (eRN.symm b)
      have h2 := eRN.symm.injective this
      rw [h2])
  obtain ⟨θ, hθ, hker⟩ := exists_hom_perfect_simple hER hNR hEN hN2 eRN
  have hfix := fix_factors hSF E (S := StatedProj (StatedSL 4 K₀))
    (factorial_nine_lt_card_L4 (by rw [hK₀]; exact hq4)) hEperf θ hθ hker hcard9
  have hEGs : E ≤ Gs :=
    le_of_fix_inner hSF hπ (fun i => hOut ↥(Xs i) (hlist i)) hCGs E hEperf hfix
  have hsolv := solvable_normalizer_inf hSF hπ V hVGs hV2 hBor hne
  have hEle : E ≤ normalizer (V : Set Y) ⊓ Gs := fun x hx =>
    ⟨hKnV x (hRK (hER hx)), hEGs hx⟩
  exact hEne (eq_bot_of_perfect_le_solvable hEperf hEle hsolv)

theorem caseOne_abstract
    (hCor2 : Tim77Cor2Statement)
    (hOut : OutSolvableListStatement) (hOutA : OutSolvableAlphaStatement)
    (hRank : TwoRankSporadicAltStatement) (hBorel : BorelRankOneSolvableStatement)
    (hArtin : ArtinLinearOrdersStatement) (hRad : RadicalTwoSubgroupLinearStatement)
    (hRad2 : RadicalTwoSubgroupRankTwoStatement)
    {Y : Type} [Group Y] [Finite Y] (q : ℕ) (hq4 : 4 ≤ q) (hq2 : ∃ g : ℕ, q = 2 ^ g)
    (V L N R K : Subgroup Y)
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥)
    (hC : ∀ X : Subgroup Y, X.Normal → V ≤ X → ∀ c : Y, (∀ x ∈ X, c * x = x * c) → c = 1)
    (hKV : ∀ g ∈ normalizer (V : Set Y), g ∈ K) (hKnV : ∀ k ∈ K, k ∈ normalizer (V : Set Y))
    (hVL : V ≤ L) (hLN : L ≤ N) (hNR : N ≤ R) (hRK : R ≤ K) (hN2 : IsPGroup 2 N)
    (hpc : ∀ P : Subgroup Y, P ≤ K → (∀ k ∈ K, k ∈ normalizer (P : Set Y)) → IsPGroup 2 P →
      P ≤ N)
    (hNn : ∀ k ∈ K, k ∈ normalizer (N : Set Y)) (hRn : ∀ k ∈ K, k ∈ normalizer (R : Set Y))
    (hLn : ∀ k ∈ K, k ∈ normalizer (L : Set Y))
    (hCKN : ∀ k ∈ K, (∀ n ∈ N, k * n = n * k) → k ∈ N)
    (hZN : ∀ x ∈ N, (∀ n ∈ N, x * n = n * x) → x ∈ V)
    (hVc : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v)
    (hVcard : Nat.card V = q) (hNcard : Nat.card N = q ^ 9) (hL64 : 2 ^ 6 < Nat.card L)
    (hLab : IsElemAbelian 2 L) (hVab : IsElemAbelian 2 V) (hti : IsTI V)
    (hWAC : ⁅WAC V, WAC V⁆ ≤ V)
    (hSyl : ∃ S : Sylow 2 Y, (S : Subgroup Y) ≤ normalizer (V : Set Y))
    (K₀ : Type) [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = q)
    (hRN : ∃ _ : (N.subgroupOf R).Normal,
      Nonempty ((↥R ⧸ N.subgroupOf R) ≃* StatedProj (StatedSL 4 K₀)))
    (hy : ∃ y ∈ R, orderOf y = 3 ∧ ∀ x ∈ N, y * x = x * y → x ∈ V) :
    ∃ (K₁ : Type) (_ : Field K₁) (_ : Finite K₁), Nat.card K₁ = q ∧
      Nonempty (↥(generalizedFitting Y) ≃* StatedProj (StatedSL 6 K₁)) := by
  classical
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVcard
    omega
  have hV2 : IsPGroup 2 ↥V := corB_isPGroup_of_isElemAbelian V hVab
  have hcor := hCor2 Y V hVab hti hWAC hSyl
  set Gs : Subgroup Y := Subgroup.normalClosure (V : Set Y) with hGs
  haveI hGsn : Gs.Normal := inferInstance
  have hVGs : V ≤ Gs := Subgroup.le_normalClosure
  have hCGs : ∀ c : Y, (∀ s ∈ Gs, c * s = s * c) → c = 1 := hC Gs hGsn hVGs
  have hcentre : Subgroup.center ↥Gs = ⊥ := corB_center_eq_bot hO hO2 Gs
  have tail : (ListGroup ↥Gs ∨ (Tim77Cor2AlphaExtra ↥Gs ∧ ∃ a b : ↥Gs, a * b ≠ b * a)) →
      ∃ (K₁ : Type) (_ : Field K₁) (_ : Finite K₁), Nat.card K₁ = q ∧
        Nonempty (↥(generalizedFitting Y) ≃* StatedProj (StatedSL 6 K₁)) := fun hX =>
    caseOne_tail hOut hOutA hRank hBorel hArtin hRad hRad2 q hq4 hq2 V L N R K Gs hO2 hO hCGs
      hKV hVGs hVL hLN hNR hRK hN2 hpc hNn hRn hLn hZN hVc hVcard hNcard hL64 hLab hX K₀ hK₀ hRN
      hy
  rcases hcor with ⟨-, hThm⟩ | hα | ⟨-, r, X, hXn, hXc, hXgen, hXcov⟩ | ⟨N', hN'n, hN'ab, hcardV, -⟩
  · exact tail (Or.inl (corB_listGroup hVne hV2 hThm hO2 hO))
  · have hAlpha : Tim77Cor2AlphaList ↥Gs := alphaList_of_isCoveringOf hα hcentre
    rcases alphaList_cases hAlpha with hlist | hextra
    · exact tail (Or.inl hlist)
    · refine tail (Or.inr ⟨hextra, ?_⟩)
      haveI : Nontrivial ↥Gs := by
        obtain ⟨v, hv, hv1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hVne
        exact ⟨⟨⟨v, hVGs hv⟩, 1, fun h => hv1 (congrArg Subtype.val h)⟩⟩
      exact exists_noncomm_of_perfect (Group.isPerfect_def.mpr hα.1)
  · exfalso
    exact no_beta hOut hBorel q hq4 V N R K Gs hO2 hO hCGs hVGs hVab hti hKV hKnV hNR hRK hN2 hpc
      hNn hCKN hVcard hNcard K₀ hK₀ hRN r X hXn hXc hXgen hXcov
  · exfalso
    have hpcGs : CFSG.pCore 2 ↥Gs = ⊥ := corB_pCore_sub_eq_bot hO2 Gs
    have hmemN : N' ∈ {K : Subgroup ↥Gs | K.Normal ∧ IsPGroup 2 K} :=
      ⟨hN'n, corB_isPGroup_of_isElemAbelian N' hN'ab⟩
    have hNle : N' ≤ CFSG.pCore 2 ↥Gs := le_sSup hmemN
    have hN'bot : N' = ⊥ := le_bot_iff.1 (hNle.trans hpcGs.le)
    subst hN'bot
    rw [Subgroup.map_bot, inf_bot_eq, Subgroup.card_bot] at hcardV
    omega

end CFSG.RankThree.GF2n.Stroth80
