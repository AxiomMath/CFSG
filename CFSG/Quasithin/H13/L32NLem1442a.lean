module

public import CFSG.Quasithin.H13.L32NLem144Ba
public import CFSG.Quasithin.Vol2.GoldschmidtL128Wire
public import CFSG.Quasithin.H13.L32NLem14324e
public import CFSG.Quasithin.H13.L32NLem14324m
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.Quasithin.Background.G10Three
public import CFSG.Quasithin.Background.P4InspOrthBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

theorem card_dvd_of_plus_six {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    {f : LinearMap.BilinForm (ZMod 2) U} (hf : G11.IsSymplectic f) {q : U → ZMod 2}
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) U = 6)
    {W : Submodule (ZMod 2) U} (hW : 2 * Module.finrank (ZMod 2) W = 6) (hWq : ∀ w ∈ W, q w = 0)
    {Γ : Subgroup (U ≃ₗ[ZMod 2] U)} (hΓ : ∀ γ ∈ Γ, ∀ v, q (γ v) = q v) :
    Nat.card Γ ∣ 40320 := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (G11.P4InspOrth.p4insporth_quad hq) :=
    ⟨W, by rw [hW, hdim], fun x hx => by
      rw [G11.P4InspOrth.p4insporth_quad_apply]
      exact hWq x hx⟩
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2)
    (G11.P4InspOrth.p4insporth_nondegenerate_quad hf hq) (m := 2) (by rw [hdim]) (ε := 1)
    (Or.inl ⟨rfl, hplus⟩)
  rw [G11.P4InspOrth.p4insporth_orthogonalGroup_quad hq, Nat.card_zmod] at h
  simp only [Nat.cast_ofNat] at h
  have h2 : (∏ i ∈ Finset.Icc 1 2, (((2 : ℤ) ^ 2) ^ i - 1)) = 45 := by decide
  rw [h2] at h
  norm_num at h
  have hO : Nat.card ↥(G11.orthSub q) = 40320 := by exact_mod_cast h
  rw [← hO]
  exact Subgroup.card_dvd_of_le fun γ hγ v => hΓ γ hγ v

variable {G : Type} [Group G] [Finite G]

structure Ctx (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g a : G)
    (D : HatModelU (fsuU T V)) : Prop where
  base : L144B.Base G T L V V₂ g
  aV₂ : a ∈ V₂
  a1 : a ∉ fsuV1 T V
  card_V1 : Nat.card ↥(fsuV1 T V) = 2
  g111 : G111Hyp D.B (D.img (l32nH T V)) (D.π a) (D.hat (l32nE T V V₂ g))
    (D.img (CFSG.conjugate (l32nW T V V₂) g)) (D.img (CFSG.conjugate (centerOf (fsuU T V)) g))
  fixS : G11.SzG11S.G112ConclusionFixS D.B (D.img (l32nH T V))
    (D.img (CFSG.conjugate (l32nW T V V₂) g))
  rank3 : CFSG.Open.pRank 3
    (centralizerMod (fsuV1 T V) (Subgroup.normalizer (fsuV1 T V : Set G)) V₂) ≤ 1
  dim : ∃ k : ℕ, Module.finrank (ZMod 2) D.V = 2 * k ∧ 3 ≤ k
  Todd : Odd ((D.img T).relIndex (D.img (l32nH T V)))
  dich : (Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) =
        2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) ∧
      2 * Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) = Module.finrank (ZMod 2) D.V ∧
      ∃ q : D.V → ZMod 2, (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
        (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
        (∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v) ∧
        ∀ e ∈ D.hat (l32nE T V V₂ g), q e = 0) ∨
    2 ^ (Module.finrank (ZMod 2) D.V / 2) ≤ Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g))

theorem exists_ctx (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12813 : Lemma12_8_13) (h14312 : Lemma14312One)
    (hFixS : G11.SzG11S.TheoremG112FixS) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hU32 : Nat.card ↥(fsuU T V) ≠ 2 ^ 5)
    {V₂ : Subgroup G} {g : G} (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgH : g ∉ l32nH T V) (D : HatModelU (fsuU T V)) : ∃ a : G, Ctx G T L V V₂ g a D := by
  have h12811 := lemma12_8_11_of h1222 h12213
  have h12812 := lemma12_8_12_two_of h1222 h12213
  have B := L144B.exists_base h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP
    hgH
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  obtain ⟨H, hconc⟩ := L14324.fixS_of h1222 h12213 hFixS B.s1282 hgP hgH haV₂ ha1 D
  have hdim : ∃ k : ℕ, Module.finrank (ZMod 2) D.V = 2 * k ∧ 3 ≤ k := by
    obtain ⟨k, hk⟩ := Q8Pow.card_eq_of_extraspecial hext
    have hU := D.card_U
    rw [B.zU, hV1] at hU
    have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
    have hDV : Nat.card D.V = 2 ^ Module.finrank (ZMod 2) D.V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rw [hDV, hk] at hU
    have hd : Module.finrank (ZMod 2) D.V = 2 * k := by
      have h2 : 2 ^ (2 * k + 1) = 2 ^ (Module.finrank (ZMod 2) D.V + 1) := by
        rw [hU, pow_succ, mul_comm]
      have := Nat.pow_right_injective (le_refl 2) h2
      omega
    have hge := lemma14323Ge_of_inputs h1332 h1334 h1222 h12213 h12811 h12813 G T L V h
    rw [B.zU, hV1, hk] at hge
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk' : 2 * k + 1 ≤ 3 := by omega
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk'
      omega
    have hk3 : k ≠ 2 := fun h2 => hU32 (by rw [hk, h2])
    exact ⟨k, hd, by omega⟩
  have hTH : T ≤ l32nH T V := h.le_l32nH hV
  have hTodd : Odd ((D.img T).relIndex (D.img (l32nH T V))) := by
    have hdvd := L14332.relIndex_img_dvd D hTH (L14332.l32nH_le_normalizer_fsuU T V)
    have hsyl := (h.isSylowTwoOf_l32nH hV).2.2
    have hodd : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (T.relIndex (l32nH T V)) with he | ho
      · exact absurd (even_iff_two_dvd.mp he) hsyl
      · exact Nat.odd_iff.mp ho)
    exact Odd.of_dvd_nat hodd hdvd
  have hdich : (Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) =
        2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) ∧
      2 * Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) = Module.finrank (ZMod 2) D.V ∧
      ∃ q : D.V → ZMod 2, (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
        (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
        (∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v) ∧
        ∀ e ∈ D.hat (l32nE T V V₂ g), q e = 0) ∨
      2 ^ (Module.finrank (ZMod 2) D.V / 2) ≤
        Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) := by
    obtain ⟨k, hk₀⟩ := H.toG101Hyp.exists_card_X
    have hk : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ k := hk₀
    by_cases hle : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤
        2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1)
    · obtain ⟨h1, h2, -, h4⟩ := h14312 G T L V h V₂ g hV₂ hgP hgH D hle
      exact Or.inl ⟨h1, h2, h4⟩
    · right
      push Not at hle
      rw [hk] at hle ⊢
      have hlt := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hle
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨a, B, haV₂, ha1, hV1, H, hconc, (h12813 G T L V 3 (fsuV1 T V) V₂ B.s1282 g hgP hgH).2.2.2,
    hdim, hTodd, hdich⟩

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

omit [Finite G] C in
theorem H_N : l32nH T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
  L14332.l32nH_le_normalizer_fsuU T V

theorem six_le : 6 ≤ Module.finrank (ZMod 2) D.V := by
  obtain ⟨k, hk, hk3⟩ := C.dim
  omega

theorem X_le : D.img (CFSG.conjugate (l32nW T V V₂) g) ≤ D.img (l32nH T V) := C.g111.X_le

theorem X_elem : IsElemAbelian 2 (D.img (CFSG.conjugate (l32nW T V V₂) g)) :=
  C.g111.toG101Hyp.X_isElemAbelian

theorem exists_card_X : ∃ k : ℕ, Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ k :=
  C.g111.toG101Hyp.exists_card_X

theorem pCoreOf_eq_bot : pCoreOf 2 (D.img (l32nH T V)) = ⊥ :=
  C.g111.toG101Hyp.g10_3_pCoreOf_eq_bot

theorem lower : 2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) ≤
    Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) := by
  rcases C.dich with ⟨h1, -⟩ | h2
  · exact h1.ge
  · exact (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ 1)).trans h2

theorem πa_ne : D.π a ≠ 0 := C.base.pi_a_ne D C.aV₂ C.a1

theorem fix_T : ∀ t ∈ D.img T, t (D.π a) = D.π a := by
  intro t ht
  obtain ⟨y, hy, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp ht
  exact C.base.rho_T_pi_a D C.aV₂ C.a1 hy hyN

theorem isSylow : IsSylowTwoOf (D.img T) (D.img (l32nH T V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun γ hγ => ?_, ?_, fun h => ?_⟩
  · obtain ⟨x, hx, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (C.base.TH hx) hxN
  · exact (C.base.hyp.fsu.sylow.1.comap_of_injective
      (Subgroup.normalizer (fsuU T V : Set G)).subtype
      (Subgroup.normalizer (fsuU T V : Set G)).subtype_injective).map D.ρ
  · exact (Nat.not_even_iff_odd.mpr C.Todd) (even_iff_two_dvd.mpr h)

theorem conj_V1 {h : G} (hh : h ∈ l32nH T V) {w : G} (hw : w ∈ fsuV1 T V) : h * w * h⁻¹ = w := by
  have hw' : h * w * h⁻¹ ∈ fsuV1 T V := (Subgroup.mem_normalizer_iff.mp hh w).mp hw
  obtain ⟨z, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp C.card_V1
  by_cases hw1 : w = 1
  · rw [hw1, mul_one, mul_inv_cancel]
  · have hc1 : h * w * h⁻¹ ≠ 1 := fun h1 => hw1 (by
      calc w = h⁻¹ * (h * w * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group)
    have e1 := huniq ⟨w, hw⟩ fun h0 => hw1 (congrArg Subtype.val h0)
    have e2 := huniq ⟨h * w * h⁻¹, hw'⟩ fun h0 => hc1 (congrArg Subtype.val h0)
    exact congrArg Subtype.val (e2.trans e1.symm)

theorem mem_cmod_of_fix {h : G} (hh : h ∈ l32nH T V)
    (hfix : D.ρ ⟨h, H_N hh⟩ (D.π a) = D.π a) :
    h ∈ centralizerMod (fsuV1 T V) (Subgroup.normalizer (fsuV1 T V : Set G)) V₂ := by
  obtain ⟨_, S⟩ := C.base.set14
  have haU := C.base.V2U C.aV₂
  have hc : (h * a * h⁻¹)⁻¹ * a ∈ fsuV1 T V := by
    rw [D.ρ_π _ a haU, D.π_eq_iff _ (L128A.HatU.conj_mem (H_N hh) haU) a haU, C.base.zU] at hfix
    exact hfix
  refine ⟨hh, hh, fun v hv => ?_⟩
  rcases S.mem_V2 C.aV₂ C.a1 hv with hv1 | hv1
  · rw [C.conj_V1 hh hv1, mul_inv_cancel]
    exact one_mem _
  · have e : h * v * h⁻¹ * v⁻¹ =
        (h * a * h⁻¹)⁻¹ * (h * (a * v) * h⁻¹) * (a * v)⁻¹ * a := by group
    rw [e, C.conj_V1 hh hv1, mul_inv_cancel_right]
    exact hc

theorem no_E9 {P : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hPΓ : P ≤ D.img (l32nH T V))
    (hP9 : Nat.card P = 9) (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hPfix : ∀ x ∈ P, x (D.π a) = D.π a) : False := by
  classical
  set N := Subgroup.normalizer (fsuU T V : Set G) with hN
  set R : Subgroup ↥N := (l32nH T V).subgroupOf N ⊓ P.comap D.ρ with hR
  have hRP : R.map D.ρ = P := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact hr.2
    · intro p hp
      obtain ⟨r, hr, rfl⟩ := hPΓ hp
      exact ⟨r, ⟨hr, hp⟩, rfl⟩
  have hker : ∀ r ∈ R, D.ρ r = 1 → ∃ k : ℕ, r ^ 2 ^ k = 1 := by
    intro r hr h1
    have hrH : (r : G) ∈ l32nH T V := hr.1
    have h1' : D.ρ ⟨(r : G), H_N hrH⟩ = 1 := h1
    rw [L14332.rho_eq_one_iff_mem hrH, C.base.cHat] at h1'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨_, h1'⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  obtain ⟨Y, hYR, hY9, hYc, hY3, hYP⟩ := S8Five.exists_lift_nine D.ρ hRP hP9 hPc hP3 hker
  set YG := Y.map N.subtype with hYG
  have hYGle : YG ≤ centralizerMod (fsuV1 T V) (Subgroup.normalizer (fsuV1 T V : Set G)) V₂ := by
    rintro _ ⟨y, hy, rfl⟩
    have hyH : (y : G) ∈ l32nH T V := (hYR hy).1
    refine C.mem_cmod_of_fix hyH ?_
    exact hPfix _ (hYP y hy)
  have hYGe : IsElemAbelian 3 YG := by
    refine ⟨⟨⟨fun x z => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨x', hx', hxe⟩ := x.2
      obtain ⟨z', hz', hze⟩ := z.2
      apply Subtype.ext
      change (x : G) * z = z * x
      rw [← hxe, ← hze]
      exact congrArg Subtype.val (hYc x' hx' z' hz')
    · obtain ⟨x', hx', rfl⟩ := hx
      exact congrArg Subtype.val (hY3 x' hx')
  have hYGc : Nat.card YG = 3 ^ 2 := by
    rw [hYG, Subgroup.card_map_of_injective N.subtype_injective, hY9]
    norm_num
  have h2 := CFSG.SectionRank.le_pRank (by norm_num) hYGle hYGe hYGc
  have := C.rank3
  omega

theorem pRank_H_le_two : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(l32nH T V)) ≤ 2 := by
  have hO2 : pCoreOf 2 (l32nH T V) ≠ ⊥ := by
    intro hb
    have hle := C.base.hyp.fsuV1_le_pCoreOf
    rw [hb, le_bot_iff] at hle
    have := C.card_V1
    rw [hle, Subgroup.card_bot] at this
    omega
  have := C.base.hyp.fsu.simple
  have hsq := (QuasithinUnique.qtkeCore_of_cat C.base.hyp.fsu.nonabelian C.base.hyp.fsu.qtke).1 _
    hO2
  exact CFSG.SectionRank.isStronglyQuasithin_iff.mp hsq.1 3 Nat.prime_three (by norm_num)

theorem pRank_img_le_two : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(D.img (l32nH T V))) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥(l32nH T V) →* ↥(D.img (l32nH T V)) :=
    (D.ρ.comp (Subgroup.inclusion H_N)).codRestrict (D.img (l32nH T V))
      fun x => L128A.HatU.rho_mem_img D x.2 _ with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact ⟨⟨h, hh⟩, rfl⟩
  have hker : IsPGroup 2 f.ker := by
    intro x
    have hx : D.ρ ⟨((x : ↥(l32nH T V)) : G), H_N (x : ↥(l32nH T V)).2⟩ = 1 := by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      exact h1
    rw [L14332.rho_eq_one_iff_mem (x : ↥(l32nH T V)).2, C.base.cHat] at hx
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨_, hx⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hN : ¬ 3 ∣ Nat.card f.ker := by
    obtain ⟨k, hk⟩ := hker.exists_card_eq
    rw [hk]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have e := QuotientGroup.quotientKerEquivOfSurjective f hsurj
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
    CFSG.SectionRank.pRank_quotient_eq f.ker hN]
  exact C.pRank_H_le_two

theorem card_dvd_of_six (hd : Module.finrank (ZMod 2) D.V = 6)
    (hX : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤ 4) :
    Nat.card ↥(D.img (l32nH T V)) ∣ 40320 := by
  rcases C.dich with ⟨-, hE, q, -, hq, hΓ, hEq⟩ | h2
  · exact card_dvd_of_plus_six ⟨C.g111.alt, C.g111.nondegenerate⟩ hq hd (by omega) hEq hΓ
  · rw [hd] at h2
    norm_num at h2
    omega

end Ctx

end L1442

end CFSG.Quasithin.H13
