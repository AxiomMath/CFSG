module

public import CFSG.Quasithin.Background.E6TwentyTwoA

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjugate_le_of_mem_normalizer {X V : Subgroup G} {g : G} (hXV : X ≤ V)
    (hg : g ∈ Subgroup.normalizer (V : Set G)) : CFSG.conjugate X g ≤ V :=
  (BenderBranch.conjugate_mono hXV g).trans
    (BenderBranch.conjugate_eq_iff_mem_normalizer.2 hg).le

omit [Finite G] in
theorem mQuot_conjugate {X V : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    E3.mQuot V (CFSG.conjugate X g) = E3.mQuot V X := by
  unfold E3.mQuot
  congr 1
  have hVg : CFSG.conjugate V g = V := BenderBranch.conjugate_eq_iff_mem_normalizer.2 hg
  conv_lhs => rw [← hVg]
  exact Subgroup.relIndex_map_map_of_injective X V (MulAut.conj g⁻¹).injective

omit [Finite G] in
theorem isComponentIn_conjugate' {L U : Subgroup G}
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) (g : G) :
    IsComponentIn (CFSG.conjugate L g)
      (Subgroup.centralizer ((CFSG.conjugate U g : Subgroup G) : Set G)) := by
  rw [← BenderBranch.conjugate_centralizer]
  exact BenderBranch.isComponentIn_map (MulAut.conj g⁻¹) hL

omit [Finite G] in
theorem inf_centralizer_conjugate {V L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    V ⊓ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) =
      CFSG.conjugate (V ⊓ Subgroup.centralizer (L : Set G)) g := by
  rw [BenderBranch.conjugate_inf, BenderBranch.conjugate_eq_iff_mem_normalizer.2 hg,
    BenderBranch.conjugate_centralizer]

omit [Finite G] in
theorem not_centralizer_conjugate_le {U M : Subgroup G} {g : G} (hgM : g ∈ M)
    (hUM : ¬ Subgroup.centralizer (U : Set G) ≤ M) :
    ¬ Subgroup.centralizer ((CFSG.conjugate U g : Subgroup G) : Set G) ≤ M := by
  intro hle
  apply hUM
  rw [← BenderBranch.conjugate_centralizer] at hle
  have h1 := BenderBranch.conjugate_mono hle g⁻¹
  rw [BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one,
    BenderBranch.conjugate_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (M.inv_mem hgM))] at h1
  exact h1

theorem mQuot_inf_le {V U U' : Subgroup G} (hV : IsPGroup 2 V) :
    E3.mQuot V (U ⊓ U') ≤ E3.mQuot V U + E3.mQuot V U' := by
  have h1 := Subgroup.relIndex_inf_le (H := U) (K := U') (L := V)
  rw [E3.relIndex_eq_two_pow hV, E3.relIndex_eq_two_pow hV, E3.relIndex_eq_two_pow hV,
    ← pow_add] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem mQuot_inf_left_le {V U U' : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V) :
    E3.mQuot U (U ⊓ U') ≤ E3.mQuot V U' := by
  have hU : IsPGroup 2 U := hV.to_le hUV
  have h1 : (U ⊓ U').relIndex U = U'.relIndex U := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right U' U
  have h2 : U'.relIndex U ≤ U'.relIndex V :=
    Subgroup.relIndex_le_of_le_right hUV (E3.relIndex_ne_zero' V U')
  rw [← h1, E3.relIndex_eq_two_pow hU, E3.relIndex_eq_two_pow hV] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

theorem eq_or_eq_of_mQuot_eq_one {V U W : Subgroup G} (hV : IsPGroup 2 V) (hUW : U ≤ W)
    (hWV : W ≤ V) (h1 : E3.mQuot V U = 1) : W = U ∨ W = V := by
  have hW : IsPGroup 2 W := hV.to_le hWV
  have h := E3.mQuot_add hUW hWV
  rw [h1] at h
  rcases Nat.eq_zero_or_pos (E3.mQuot W U) with h0 | h0
  · left
    exact ((E3.mQuot_eq_zero_iff hW hUW).1 h0).symm
  · right
    have h0' : E3.mQuot V W = 0 := by omega
    exact (E3.mQuot_eq_zero_iff hV hWV).1 h0'

theorem three_le_pRank_of_commuting {p : ℕ} [hp : Fact p.Prime] {X L₁ L₂ L₃ : Subgroup G}
    (c12 : L₁ ≤ Subgroup.centralizer (L₂ : Set G)) (c13 : L₁ ≤ Subgroup.centralizer (L₃ : Set G))
    (c23 : L₂ ≤ Subgroup.centralizer (L₃ : Set G)) (hX₁ : L₁ ≤ X) (hX₂ : L₂ ≤ X) (hX₃ : L₃ ≤ X)
    {x₁ x₂ x₃ : G} (hx₁ : x₁ ∈ L₁) (hx₂ : x₂ ∈ L₂) (hx₃ : x₃ ∈ L₃) (hp₁ : x₁ ^ p = 1)
    (hp₂ : x₂ ^ p = 1) (hp₃ : x₃ ^ p = 1) (hc₁ : x₁ ≠ 1)
    (hc₂ : x₂ ∉ Subgroup.centralizer (L₂ : Set G)) (hc₃ : x₃ ∉ Subgroup.centralizer (L₃ : Set G)) :
    3 ≤ CFSG.Open.pRank p X := by
  have hp1 : 1 < p := hp.out.one_lt
  let F₀ : PUnit.{1} →* G := 1
  have hF₀ : Function.Injective F₀ := fun a b _ => Subsingleton.elim a b
  have hcard₀ : Nat.card PUnit.{1} = p ^ 0 := by simp
  have hx₁r : x₁ ∉ F₀.range := by
    rintro ⟨a, ha⟩
    exact hc₁ ha.symm
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrep₁⟩ := CFSG.SectionRank.exists_extend
    (fun _ _ => rfl) (fun _ => rfl) hcard₀ F₀ hF₀ hp₁ hx₁r (fun _ => Commute.one_left x₁)
  have hr₁ : ∀ a, F₁ a ∈ Subgroup.zpowers x₁ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₁ a
    rw [hb]
    exact Subgroup.mul_mem _ (by simp [F₀]) (Subgroup.pow_mem _ (Subgroup.mem_zpowers x₁) n)
  have hZ₁ : Subgroup.zpowers x₁ ≤ Subgroup.centralizer (L₂ : Set G) ⊓
      Subgroup.centralizer (L₃ : Set G) :=
    Subgroup.zpowers_le.2 ⟨c12 hx₁, c13 hx₁⟩
  have hx₂r : x₂ ∉ F₁.range := by
    rintro ⟨a, ha⟩
    exact hc₂ (ha ▸ (hZ₁ (hr₁ a)).1)
  have hc12 : ∀ a, Commute (F₁ a) x₂ := fun a =>
    (Subgroup.mem_centralizer_iff.1 (hZ₁ (hr₁ a)).1 x₂ hx₂).symm
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, hrep₂⟩ :=
    CFSG.SectionRank.exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁ hp₂ hx₂r hc12
  have hr₂ : ∀ a, F₂ a ∈ Subgroup.centralizer (L₃ : Set G) ⊓ X := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₂ a
    rw [hb]
    have hF₁X : F₁ b ∈ X := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr₁ b)
      rw [← hk]
      exact X.zpow_mem (hX₁ hx₁) k
    exact (Subgroup.centralizer (L₃ : Set G) ⊓ X).mul_mem
      (Subgroup.mem_inf.2 ⟨(hZ₁ (hr₁ b)).2, hF₁X⟩)
      ((Subgroup.centralizer (L₃ : Set G) ⊓ X).pow_mem (Subgroup.mem_inf.2 ⟨c23 hx₂, hX₂ hx₂⟩) n)
  have hx₃r : x₃ ∉ F₂.range := by
    rintro ⟨a, ha⟩
    exact hc₃ (ha ▸ (hr₂ a).1)
  have hc3 : ∀ a, Commute (F₂ a) x₃ := fun a =>
    (Subgroup.mem_centralizer_iff.1 (hr₂ a).1 x₃ hx₃).symm
  obtain ⟨F₃, hF₃, hcomm₃, hpow₃, hcard₃, hrep₃⟩ :=
    CFSG.SectionRank.exists_extend hcomm₂ hpow₂ hcard₂ F₂ hF₂ hp₃ hx₃r hc3
  have hrange : F₃.range ≤ X := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hb⟩ := hrep₃ a
    rw [hb]
    exact X.mul_mem (hr₂ b).2 (X.pow_mem (hX₃ hx₃) n)
  have := CFSG.SectionRank.le_pRank_of_injective hp1 hcomm₃ hpow₃ hcard₃ F₃ hF₃ hrange
  omega

end Tools

theorem e622_of (h311 : Theorem311Stmt) (hlist : Lemma115_3_List) (h618 : E618Stmt)
    (h621 : E621Stmt) (hCent : E68CentComp) : E622Stmt := by
  intro G _ _ T M V U hV h h15 hUV hU1
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  by_contra hnot
  have hUM := e6_16_two h hUV hnot
  obtain ⟨hr, hm, hUΓ⟩ := e6_16_one hV h h15 hUV hU1 hUM
  have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h h15 hr).2
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hO : oddCoreIn H = ⊥ := h621 G T M V U hV h h15 hUV hUΓ.2.1
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, IsComponentIn L H := by
    by_contra hno
    push Not at hno
    exact hnot (DoubleA3.charTwo_of_no_component hno hO)
  obtain ⟨hLM, -, -, -⟩ := e68_setting hlist h hUΓ hO hL
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hUCL : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun l hl => (Subgroup.mem_centralizer_iff.1 (hL.1 hl) u hu).symm
  have hCVL : V ⊓ Subgroup.centralizer (L : Set G) = U := by
    rcases eq_or_eq_of_mQuot_eq_one hV2 hUCL inf_le_left hU1 with heq | heq
    · exact heq
    · exfalso
      apply hLM
      have hVL : V ≤ Subgroup.centralizer (L : Set G) := by
        rw [← heq]
        exact inf_le_right
      exact (Subgroup.le_centralizer_iff.1 hVL).trans h.centralizer_le
  set MV := M ⊓ Subgroup.normalizer (V : Set G) with hMVdef
  have hU'facts : ∀ g ∈ MV, CFSG.conjugate U g ≤ V ∧ E3.mQuot V (CFSG.conjugate U g) = 1 ∧
      ¬ Subgroup.centralizer ((CFSG.conjugate U g : Subgroup G) : Set G) ≤ M := fun g hg =>
    ⟨conjugate_le_of_mem_normalizer hUV hg.2, (mQuot_conjugate hg.2).trans hU1,
      not_centralizer_conjugate_le hg.1 hUM⟩
  have hU₀ne : ∀ g ∈ MV, U ⊓ CFSG.conjugate U g ≠ ⊥ := by
    intro g hg h0
    have h1 := mQuot_inf_le (U := U) (U' := CFSG.conjugate U g) hV2
    rw [h0, hU1, (hU'facts g hg).2.1] at h1
    omega
  have hcomp : ∀ g ∈ MV,
      IsComponentIn L (Subgroup.centralizer ((U ⊓ CFSG.conjugate U g : Subgroup G) : Set G)) ∧
      IsComponentIn (CFSG.conjugate L g)
        (Subgroup.centralizer ((U ⊓ CFSG.conjugate U g : Subgroup G) : Set G)) := by
    intro g hg
    obtain ⟨hU'V, hU'1, hU'M⟩ := hU'facts g hg
    refine ⟨isComponentIn_of_le_hyperplane hlist h618 h621 hCent hV h h15 hm hUV hU1 hUM hL
      inf_le_left (hU₀ne g hg) ((mQuot_inf_left_le hV2 hUV).trans hU'1.le), ?_⟩
    rw [inf_comm]
    exact isComponentIn_of_le_hyperplane hlist h618 h621 hCent hV h h15 hm hU'V hU'1 hU'M
      (isComponentIn_conjugate' hL g) inf_le_left (by rw [inf_comm]; exact hU₀ne g hg)
      ((mQuot_inf_left_le hV2 hU'V).trans hU1.le)
  have hdich : ∀ g ∈ MV, CFSG.conjugate L g = L ∨ ⁅L, CFSG.conjugate L g⁆ = ⊥ := by
    intro g hg
    rcases BenderBranch.eq_or_commute_of_isComponentIn (hcomp g hg).1 (hcomp g hg).2 with
      heq | hc
    · exact Or.inl heq.symm
    · exact Or.inr hc
  have hLnot2 : ¬ ∃ k, Nat.card L = 2 ^ k := by
    rintro ⟨k, hk⟩
    have hL2 : IsPGroup 2 ↥L := IsPGroup.of_card hk
    have : Group.IsNilpotent ↥L := hL2.isNilpotent
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hLq
    have : Group.IsPerfect ↥L := hLq.1
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance
  obtain ⟨p, hp, hpL, hpodd⟩ :=
    (Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card L)).resolve_left hLnot2
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h2 => by
    rw [h2] at hpodd
    exact (Nat.not_even_iff_odd.2 hpodd) even_two
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) p hpL
  set x₁ : G := (y : G) with hx₁def
  have hx₁L : x₁ ∈ L := y.2
  have ho₁ : orderOf x₁ = p := by rw [hx₁def, Subgroup.orderOf_coe]; exact hy
  have hp₁ : x₁ ^ p = 1 := ho₁ ▸ pow_orderOf_eq_one x₁
  have hx₁1 : x₁ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ho₁
    exact hp.one_lt.ne ho₁
  have hOL : oddCoreIn L = ⊥ := le_bot_iff.1 (hO ▸ oddCoreIn_le_of_subnormal'' hL.1 hL.2.2)
  have hx₁C : x₁ ∉ Subgroup.centralizer (L : Set G) := by
    intro hx
    have hodd : Odd (Nat.card (Subgroup.zpowers x₁)) := by
      rw [Nat.card_zpowers, ho₁]
      exact hpodd
    have hle : Subgroup.zpowers x₁ ≤ oddCoreIn L :=
      le_oddCoreIn_of_odd (Subgroup.zpowers_le.2 hx₁L)
        ((Subgroup.le_centralizer_iff.1 (Subgroup.zpowers_le.2 hx)).trans
          (Subgroup.centralizer_le_normalizer _)) hodd
    rw [hOL] at hle
    exact hx₁1 (Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers x₁)))
  have hconj : ∀ g : G, g⁻¹ * x₁ * g ∈ CFSG.conjugate L g ∧ (g⁻¹ * x₁ * g) ^ p = 1 ∧
      g⁻¹ * x₁ * g ∉ Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    intro g
    refine ⟨BenderBranch.mem_conjugate_iff.2 (by group; exact hx₁L), ?_, ?_⟩
    · rw [show g⁻¹ * x₁ * g = g⁻¹ * x₁ * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hp₁]
      group
    · rw [← BenderBranch.conjugate_centralizer, BenderBranch.mem_conjugate_iff]
      intro hx
      apply hx₁C
      have : g * (g⁻¹ * x₁ * g) * g⁻¹ = x₁ := by group
      rwa [this] at hx
  have horbit : ∃ g₀ ∈ MV, ∀ g ∈ MV, CFSG.conjugate L g = L ∨
      CFSG.conjugate L g = CFSG.conjugate L g₀ := by
    by_cases hall : ∀ g ∈ MV, CFSG.conjugate L g = L
    · exact ⟨1, MV.one_mem, fun g hg => Or.inl (hall g hg)⟩
    push Not at hall
    obtain ⟨g₀, hg₀, hne₀⟩ := hall
    refine ⟨g₀, hg₀, fun g hg => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hne₁, hne₂⟩ := hcon
    have hc0 : ⁅L, CFSG.conjugate L g₀⁆ = ⊥ := (hdich g₀ hg₀).resolve_left hne₀
    have hc1 : ⁅L, CFSG.conjugate L g⁆ = ⊥ := (hdich g hg).resolve_left hne₁
    have hxg : g * g₀⁻¹ ∈ MV := MV.mul_mem hg (MV.inv_mem hg₀)
    have heqg : CFSG.conjugate (CFSG.conjugate L (g * g₀⁻¹)) g₀ = CFSG.conjugate L g := by
      rw [BenderBranch.conjugate_conjugate, inv_mul_cancel_right]
    have hc2 : ⁅CFSG.conjugate L g₀, CFSG.conjugate L g⁆ = ⊥ := by
      rcases hdich _ hxg with he | he
      · exfalso
        apply hne₂
        rw [← heqg, he]
      · rw [← heqg]
        unfold CFSG.conjugate
        rw [← Subgroup.map_commutator]
        change ⁅L, CFSG.conjugate L (g * g₀⁻¹)⁆.map _ = ⊥
        rw [he, Subgroup.map_bot]
    set D := U ⊓ CFSG.conjugate U g₀ ⊓ CFSG.conjugate U g with hDdef
    have hDV : D ≤ V := inf_le_left.trans (inf_le_left.trans hUV)
    have hD1 : D ≠ ⊥ := by
      intro h0
      have h1 := mQuot_inf_le (U := U ⊓ CFSG.conjugate U g₀) (U' := CFSG.conjugate U g) hV2
      have h2 := mQuot_inf_le (U := U) (U' := CFSG.conjugate U g₀) hV2
      rw [← hDdef, h0, (hU'facts g hg).2.1] at h1
      rw [hU1, (hU'facts g₀ hg₀).2.1] at h2
      omega
    have hLD : L ≤ Subgroup.centralizer (D : Set G) :=
      hL.1.trans (Subgroup.centralizer_le (inf_le_left.trans inf_le_left))
    have hL0D : CFSG.conjugate L g₀ ≤ Subgroup.centralizer (D : Set G) :=
      (isComponentIn_conjugate' hL g₀).1.trans
        (Subgroup.centralizer_le (inf_le_left.trans inf_le_right))
    have hLgD : CFSG.conjugate L g ≤ Subgroup.centralizer (D : Set G) :=
      (isComponentIn_conjugate' hL g).1.trans (Subgroup.centralizer_le inf_le_right)
    have h3 := three_le_pRank_of_commuting (p := p)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc0)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc2) hLD hL0D hLgD hx₁L
      (hconj g₀).1 (hconj g).1 hp₁ (hconj g₀).2.1 (hconj g).2.1 hx₁1 (hconj g₀).2.2
      (hconj g).2.2
    have h4 : CFSG.Open.pRank p (Subgroup.centralizer (D : Set G)) ≤ 2 :=
      (CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.centralizer_le_normalizer _)).trans
        ((A1b.pRank_le_evenRank hp hp2 ⟨D, hD1, hV2.to_le hDV, rfl⟩).trans h.qtke.2.2)
    omega
  obtain ⟨g₀, hg₀, hg₀orb⟩ := horbit
  set Y := L ⊔ CFSG.conjugate L g₀ with hYdef
  have hTMV : T ≤ MV := le_inf h.inM.2 h.normal
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := by
    intro t ht
    have htMV := hTMV ht
    have hmem : ∀ g ∈ MV, CFSG.conjugate L g ≤ Y := fun g hg => by
      rcases hg₀orb g hg with he | he
      · rw [he]
        exact le_sup_left
      · rw [he]
        exact le_sup_right
    have hle : CFSG.conjugate Y t ≤ Y := by
      unfold CFSG.conjugate
      rw [Subgroup.map_sup]
      refine sup_le (hmem t htMV) ?_
      have := hmem (g₀ * t) (MV.mul_mem hg₀ htMV)
      rwa [← BenderBranch.conjugate_conjugate] at this
    have heq : CFSG.conjugate Y t = Y :=
      Subgroup.eq_of_le_of_card_ge hle (BenderBranch.card_conjugate Y t).ge
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 heq
  set W := V ⊓ Subgroup.centralizer (Y : Set G) with hWdef
  have hWV : W ≤ V := inf_le_left
  have hUU : U ⊓ CFSG.conjugate U g₀ ≤ W := by
    intro x hx
    refine ⟨hUV hx.1, ?_⟩
    have hxL : x ∈ Subgroup.centralizer (L : Set G) := (hCVL ▸ hx.1 : x ∈ V ⊓ _).2
    have hxL0 : x ∈ Subgroup.centralizer ((CFSG.conjugate L g₀ : Subgroup G) : Set G) := by
      have h1 : x ∈ V ⊓ Subgroup.centralizer ((CFSG.conjugate L g₀ : Subgroup G) : Set G) := by
        rw [inf_centralizer_conjugate hg₀.2, hCVL]
        exact hx.2
      exact h1.2
    have hYx : Y ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hxL l hl)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hxL0 l hl)
    exact Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.1 (hYx hl)
  have hWq : E3.mQuot V W ≤ 2 := by
    have h1 := E3.mQuot_mono (V := V) hUU
    have h2 := mQuot_inf_le (U := U) (U' := CFSG.conjugate U g₀) hV2
    rw [hU1, (hU'facts g₀ hg₀).2.1] at h2
    omega
  have hW1 : W ≠ ⊥ := by
    intro h0
    rw [h0] at hWq
    omega
  have hLW : L ≤ Subgroup.centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.1 (inf_le_right.trans
      (Subgroup.centralizer_le (show (L : Set G) ⊆ Y from fun _ hx => Subgroup.mem_sup_left hx)))
  have hWM : ¬ Subgroup.centralizer (W : Set G) ≤ M := fun hle => hLM (hLW.trans hle)
  have hWΓ : W ∈ gammaE64 V M := mem_gammaE64_of_mQuot_lt hV h hWV hW1 hWM (by omega)
  have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
    B2F.le_normalizer_inf h.normal (B2F.le_normalizer_centralizer hTY)
  exact hWM (e6_13 h311 h hWV hW1 hWΓ.2.2.2 hTW)

end E6

end CFSG.Quasithin
