module

public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11G2Q8InvField
public import CFSG.Quasithin.Vol2.Ch11G2Q8InvLong
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11G2Q8Siegel
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open scoped IsMulCommutative commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem mem_fixQ_conj_tL (x : ↥(cayleyGroup K)) (w : Ix3 → K) :
    w ∈ fixQ (x * tL 1 * x⁻¹) ↔ InC (g2Act x⁻¹ w) := by
  rw [mem_fixQ, g2Act_mul_apply, g2Act_mul_apply]
  constructor
  · intro h
    apply inC_of_tL_fix one_ne_zero
    have h1 := congrArg (g2Act x⁻¹) h
    rwa [g2Act_inv_apply] at h1
  · intro h
    rw [g2Act_tL_of_inC 1 h, g2Act_apply_inv]

theorem mem_commQ_conj_tL (x : ↥(cayleyGroup K)) (w : Ix3 → K) :
    w ∈ commQ (x * tL 1 * x⁻¹) ↔ g2Act x⁻¹ w ∈ stdF K 2 := by
  rw [mem_commQ]
  constructor
  · rintro ⟨z, rfl⟩
    rw [g2Act_mul_apply, g2Act_mul_apply, map_sub, g2Act_inv_apply]
    exact g2Act_tL_sub_mem 1 _
  · intro h
    obtain ⟨y, hy⟩ := exists_tL_sub_eq one_ne_zero h
    refine ⟨g2Act x y, ?_⟩
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply, ← g2Act_apply_inv x w, ← hy,
      map_sub]

theorem mem_F2_iff_polarQ (x : ↥(cayleyGroup K)) (y : Ix3 → K) :
    g2Act x⁻¹ y ∈ stdF K 2 ↔ ∀ c, InC (g2Act x⁻¹ c) → polarQ c y = 0 := by
  constructor
  · intro hy c hc
    rw [← polarQ_g2Act x⁻¹]
    obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp hy
    obtain ⟨c1, c2⟩ := hc
    simp only [polarQ, b1, b2, b3, b4, c1, c2]
    ring
  · intro h
    have e : ∀ c, InC c → polarQ c (g2Act x⁻¹ y) = 0 := by
      intro c hc
      have h1 := h (g2Act x c) (by rwa [g2Act_inv_apply])
      rwa [← polarQ_g2Act x⁻¹, g2Act_inv_apply] at h1
    have e0 := e (q6 1 0 0 0 0 0) ⟨rfl, rfl⟩
    have e1 := e (q6 0 1 0 0 0 0) ⟨rfl, rfl⟩
    have e2 := e (q6 0 0 0 0 1 0) ⟨rfl, rfl⟩
    have e3 := e (q6 0 0 0 0 0 1) ⟨rfl, rfl⟩
    simp [polarQ, q6] at e0 e1 e2 e3
    exact mem_stdF_two.mpr ⟨e2, e3, e0, e1⟩

theorem card_inC_le [Finite K] (x : ↥(cayleyGroup K)) :
    Nat.card {w : Ix3 → K // InC (g2Act x⁻¹ w)} ≤ Nat.card K ^ 4 := by
  have hinj : Function.Injective (fun w : {w : Ix3 → K // InC (g2Act x⁻¹ w)} =>
      (![(g2Act x⁻¹ w.1) (.inl 0), (g2Act x⁻¹ w.1) (.inl 1), (g2Act x⁻¹ w.1) (.inr 1),
        (g2Act x⁻¹ w.1) (.inr 2)] : Fin 4 → K)) := by
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    have key : g2Act x⁻¹ w = g2Act x⁻¹ w' := by
      funext j
      rcases j with j | j <;> fin_cases j
      exacts [congrFun h 0, congrFun h 1, hw.1.trans hw'.1.symm, hw.2.trans hw'.2.symm,
        congrFun h 2, congrFun h 3]
    have h2 := congrArg (g2Act x) key
    rw [g2Act_apply_inv, g2Act_apply_inv] at h2
    exact Subtype.ext h2
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fun, Nat.card_fin] at h1

theorem factG2RootLine_holds : SecB.FactG2RootLine := by
  intro G _ _ L V X T V₁ V₂ V₃ n hfl hCV E hEX hEab hm
  obtain ⟨_, K, _, _, _, hK, π, f, hf, c₀, hc0, hc1, g, -, -, hV₂, -⟩ := exists_coord_flagG2 hfl
  have hn := hfl.two_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h₂ : V₂ ≤ V := hfl.le₂₃.trans hfl.le₃
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : ((a * b⁻¹ : ↥V) : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨(a * b⁻¹).2, (hf.eq_iff a b).mp hab⟩
    rw [hCV, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.mp (Subtype.ext h1)
  have hcardV : Nat.card ↥V = Nat.card K ^ 6 := by
    rw [← card_Q]
    exact Nat.card_eq_of_bijective f ⟨hfinj, hf.surj⟩
  obtain ⟨CE, hCE⟩ : ∃ CE : Subgroup ↥V,
      CE = (V ⊓ Subgroup.centralizer (E : Set G)).subgroupOf V := ⟨_, rfl⟩
  have hmem_CE : ∀ w : ↥V, w ∈ CE ↔ ∀ e ∈ E, e * (w : G) = w * e := by
    intro w
    rw [hCE, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩
  have hidx : CE.index = Nat.card K ^ 2 := by
    have hdvd : CE.index ∣ 2 ^ (n * 6) := by
      rw [pow_mul, ← hK, ← hcardV]
      exact Dvd.intro_left _ CE.card_mul_index
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hm' : padicValNat 2 CE.index = 2 * n := by
      rw [hCE]
      exact hm
    rw [hk, padicValNat.prime_pow] at hm'
    rw [hk, hm', hK, ← pow_mul, mul_comm]
  have hcardCE : Nat.card CE = Nat.card K ^ 4 := by
    have h1 := CE.card_mul_index
    rw [hidx, hcardV, show Nat.card K ^ 6 = Nat.card K ^ 4 * Nat.card K ^ 2 by
      rw [← pow_add]] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have key : ∀ e (he : e ∈ E), ∃ γ : ↥(cayleyGroup K), γ * γ = 1 ∧
      ∀ w, f (SecA.conjV V e (hEX he).2 w) = g2Act γ (f w) := by
    intro e he
    obtain ⟨c, γ, σ, hc, hcγ⟩ := exists_smul_frob_conjV hf hc0 hc1 hK hn hfl.normalizer_le
      (hEX he)
    have hfixE : ∀ w ∈ CE, SecA.conjV V e (hEX he).2 w = w := by
      intro w hw
      apply Subtype.ext
      rw [SecA.conjV_apply_coe, (hmem_CE w).mp hw e he, mul_inv_cancel_right]
    have hσ : ∀ θ, σ θ = θ := by
      by_contra hσ
      obtain ⟨θ, hθ⟩ := not_forall.mp hσ
      let Te : (Ix3 → K) →+ (Ix3 → K) :=
        { toFun := fun x => c • g2Act γ (frobQ σ x)
          map_zero' := by
            rw [show frobQ (σ : K →+* K) 0 = 0 from funext fun j => map_zero σ, map_zero,
              smul_zero]
          map_add' := fun x y => by
            rw [show frobQ (σ : K →+* K) (x + y) = frobQ σ x + frobQ σ y from
              funext fun j => map_add σ (x j) (y j), map_add, smul_add] }
      have hTe : ∀ (a : K) (x : Ix3 → K), Te (a • x) = (σ : K →+* K) a • Te x := by
        intro a x
        show c • g2Act γ (frobQ σ (a • x)) = (σ : K →+* K) a • (c • g2Act γ (frobQ σ x))
        rw [frobQ_smul, g2Act_smul, smul_comm]
      have h1 := card_fix_sq_le Te (σ : K →+* K) hθ hTe
      have h3 : Nat.card CE ≤ Nat.card {x : Ix3 → K // Te x = x} := by
        refine Nat.card_le_card_of_injective (fun w => ⟨f w.1, ?_⟩) ?_
        · show c • g2Act γ (frobQ σ (f w.1)) = f w.1
          rw [← hcγ, hfixE _ w.2]
        · intro w w' h
          exact Subtype.ext (hfinj (congrArg Subtype.val h))
      rw [hcardCE] at h3
      rw [card_Q] at h1
      have h4 : Nat.card K ^ 4 * Nat.card K ^ 4 ≤ Nat.card K ^ 6 :=
        le_trans (Nat.mul_le_mul h3 h3) (by rw [← sq]; exact h1)
      rw [← pow_add] at h4
      have h5 : Nat.card K ^ 6 < Nat.card K ^ (4 + 4) := Nat.pow_lt_pow_right hq (by norm_num)
      omega
    have hfrob : ∀ x, frobQ (σ : K →+* K) x = x := fun x => funext fun j => hσ (x j)
    have hcγ' : ∀ w, f (SecA.conjV V e (hEX he).2 w) = c • g2Act γ (f w) := fun w => by
      rw [hcγ, hfrob]
    have hee : ∀ w, SecA.conjV V e (hEX he).2 (SecA.conjV V e (hEX he).2 w) = w := by
      intro w
      have he2 : e * e = 1 := by
        have := hEab.2 e he
        rwa [sq] at this
      apply Subtype.ext
      rw [SecA.conjV_apply_coe, SecA.conjV_apply_coe,
        show e * (e * (w : G) * e⁻¹) * e⁻¹ = (e * e) * w * (e * e)⁻¹ by group, he2]
      group
    have hsq : ∀ x, g2Act (γ * γ) x = (c * c)⁻¹ • x := by
      intro x
      obtain ⟨w, rfl⟩ := hf.surj x
      have h1 := congrArg f (hee w)
      rw [hcγ', hcγ', g2Act_smul, smul_smul] at h1
      rw [g2Act_mul_apply]
      conv_rhs => rw [← h1]
      rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
    have hcc : (c * c)⁻¹ = 1 := scalar_eq_one hsq
    have hc1' : c = 1 := by
      have h3 : c * c = 1 := by rw [← inv_inv (c * c), hcc, inv_one]
      have h4 : (c - 1) ^ 2 = 0 := by linear_combination h3 + (1 - c) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
    refine ⟨γ, cayley_eq_one fun x => by rw [hsq, hcc, one_smul], fun w => ?_⟩
    rw [hcγ', hc1', one_smul]
  choose γe hγe1 hγe using key
  have hfixCE : ∀ e (he : e ∈ E), ∀ w ∈ CE, g2Act (γe e he) (f w) = f w := by
    intro e he w hw
    rw [← hγe e he]
    congr 1
    apply Subtype.ext
    rw [SecA.conjV_apply_coe, (hmem_CE w).mp hw e he, mul_inv_cancel_right]
  have hlong : ∀ e (he : e ∈ E), γe e he ≠ 1 → ∃ x : ↥(cayleyGroup K),
      γe e he = x * tL 1 * x⁻¹ ∧ ∀ y, InC (g2Act x⁻¹ y) ↔ ∃ w ∈ CE, f w = y := by
    intro e he hne
    have hfix : Nat.card K ^ 4 ≤ Nat.card (fixQ (γe e he)) := by
      rw [← hcardCE]
      refine Nat.card_le_card_of_injective
        (fun w => ⟨f w.1, mem_fixQ.mpr (hfixCE e he _ w.2)⟩) ?_
      intro w w' h
      exact Subtype.ext (hfinj (congrArg Subtype.val h))
    obtain ⟨x, hx⟩ := eq_conj_tL_of_fix (hγe1 e he) hne hfix
    have hmemC : ∀ w ∈ CE, InC (g2Act x⁻¹ (f w)) := by
      intro w hw
      rw [← mem_fixQ_conj_tL, ← hx]
      exact mem_fixQ.mpr (hfixCE e he w hw)
    refine ⟨x, hx, fun y => ⟨fun hy => ?_, ?_⟩⟩
    · let φ : CE → {y : Ix3 → K // InC (g2Act x⁻¹ y)} := fun w => ⟨f w.1, hmemC _ w.2⟩
      have hinj : Function.Injective φ := by
        intro w w' h
        exact Subtype.ext (hfinj (congrArg Subtype.val h))
      have hbij := (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj,
        le_antisymm (Nat.card_le_card_of_injective φ hinj)
          (by rw [hcardCE]; exact card_inC_le x)⟩
      obtain ⟨w, hw⟩ := hbij.2 ⟨y, hy⟩
      exact ⟨w.1, w.2, congrArg Subtype.val hw⟩
    · rintro ⟨w, hw, rfl⟩
      exact hmemC w hw
  have hcommP : ∀ e (he : e ∈ E), γe e he ≠ 1 → ∀ y, y ∈ commQ (γe e he) ↔
      ∀ w ∈ CE, polarQ (f w) y = 0 := by
    intro e he hne y
    obtain ⟨x, hx, hxC⟩ := hlong e he hne
    rw [hx, mem_commQ_conj_tL, mem_F2_iff_polarQ]
    constructor
    · intro h w hw
      exact h _ ((hxC _).mpr ⟨w, hw, rfl⟩)
    · intro h c hc
      obtain ⟨w, hw, rfl⟩ := (hxC c).mp hc
      exact h w hw
  obtain ⟨e₀, he₀, hne₀⟩ : ∃ e, ∃ he : e ∈ E, γe e he ≠ 1 := by
    by_contra hall
    have htop : CE = ⊤ := by
      rw [eq_top_iff]
      intro w _
      rw [hmem_CE]
      intro e he
      have h1 : γe e he = 1 := by
        by_contra h1
        exact hall ⟨e, he, h1⟩
      have h3 : SecA.conjV V e (hEX he).2 w = w := hfinj (by
        rw [hγe e he, h1, map_one]
        rfl)
      have h4 := congrArg Subtype.val h3
      rw [SecA.conjV_apply_coe] at h4
      calc e * (w : G) = e * w * e⁻¹ * e := by group
        _ = w * e := by rw [h4]
    have h1 : CE.index = 1 := by rw [htop, Subgroup.index_top]
    rw [hidx] at h1
    have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow two_ne_zero hq
    omega
  obtain ⟨x₀, hx₀, -⟩ := hlong e₀ he₀ hne₀
  have hle : ⁅V, E⁆ ≤ (hf.pre (commQ (γe e₀ he₀))).map V.subtype := by
    rw [Subgroup.commutator_le]
    intro v hv e he
    have hcV : ⁅v, e⁆ ∈ V := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine V.mul_mem hv ?_
      rw [← mul_assoc]
      exact (Subgroup.mem_normalizer_iff.mp (hEX he).2 _).mp (V.inv_mem hv)
    refine ⟨⟨⁅v, e⁆, hcV⟩, ?_, rfl⟩
    have hc : (⟨⁅v, e⁆, hcV⟩ : ↥V) = ⟨v, hv⟩ * (SecA.conjV V e (hEX he).2 ⟨v, hv⟩)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SecA.conjV_apply_coe,
        commutatorElement_def]
      group
    have h3 : g2Act (γe e he) (f ⟨v, hv⟩) - f ⟨v, hv⟩ ∈ commQ (γe e₀ he₀) := by
      by_cases h1 : γe e he = 1
      · rw [h1, map_one, AddMonoid.End.coe_one, id_eq, sub_self]
        exact (commQ _).zero_mem
      · exact (hcommP e₀ he₀ hne₀ _).mpr ((hcommP e he h1 _).mp (mem_commQ.mpr ⟨_, rfl⟩))
    show f ⟨⁅v, e⁆, hcV⟩ ∈ commQ (γe e₀ he₀)
    rw [hc, hf.map_mul_inv, hγe e he, ← neg_sub]
    exact (commQ _).neg_mem h3
  have hVE : ∀ w : ↥V, (w : G) ∈ ⁅V, E⁆ ↔ f w ∈ commQ (γe e₀ he₀) := by
    intro w
    constructor
    · intro hw
      obtain ⟨w', hw', hww'⟩ := hle hw
      have h1 : w' = w := Subtype.ext hww'
      rw [← h1]
      exact hw'
    · intro hw
      obtain ⟨z, hz⟩ := mem_commQ.mp hw
      obtain ⟨v, rfl⟩ := hf.surj z
      rw [← hγe e₀ he₀, ← hf.map_mul_inv] at hz
      have h1 := hfinj hz
      subst h1
      rw [Subgroup.commutator_comm]
      have h3 : ((SecA.conjV V e₀ (hEX he₀).2 v * v⁻¹ : ↥V) : G) = ⁅e₀, (v : G)⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SecA.conjV_apply_coe,
          commutatorElement_def]
      rw [h3]
      exact Subgroup.commutator_mem_commutator he₀ v.2
  obtain ⟨l, hlL, hlV, hl⟩ := SecA.mem_autOn_iff.mp (rhoG hc0 hc1 π (g * x₀⁻¹)).2
  have hconj := subgroupOf_conjSubgroup_eq hf hc0 hc1 hV₂ hlV hl
  rw [show (g * x₀⁻¹)⁻¹ * g = x₀ by group] at hconj
  refine ⟨l, hlL, ?_⟩
  ext z
  by_cases hz : z ∈ V
  · have h1 : (⟨z, hz⟩ : ↥V) ∈ (conjSubgroup V₂ l).subgroupOf V ↔ z ∈ conjSubgroup V₂ l :=
      Iff.rfl
    rw [← h1, hconj, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gmapG, ← mem_commQ_conj_tL,
      ← hx₀]
    exact hVE ⟨z, hz⟩
  · have h1 : z ∉ ⁅V, E⁆ := fun h => hz (Subgroup.map_subtype_le _ (hle h))
    have h3 : z ∉ conjSubgroup V₂ l := fun h => hz (conjSubgroup_le_of_le h₂ hlV h)
    exact ⟨fun h => absurd h h1, fun h => absurd h h3⟩

end CFSG.Quasithin.Vol2.Ch11.G2Q8
