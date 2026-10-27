module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Defs
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup CFSG.Open
open scoped IsMulCommutative

open scoped IsMulCommutative commutatorElement

theorem sz5e1_fixbound_abelian {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (K E : Subgroup G)
    (hrank : ∀ T : Subgroup G, T ≤ K → T ≠ ⊥ → IsPGroup 2 T →
      CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE5 : ∀ x ∈ E, x ^ p = 1)
    (hKE : K ≤ normalizer (E : Set G)) (hKbot : K ≤ normalizer ((⊥ : Subgroup G) : Set G))
    [((⊥ : Subgroup G).subgroupOf E).Normal]
    [IsElementaryAbelian p (↥E ⧸ (⊥ : Subgroup G).subgroupOf E)] :
    FixBound (chiefRepE (p := p) hKE hKbot) 3 := by
  classical
  intro t ht ht2
  let g : G := (t : G)
  let T : Subgroup G := Subgroup.zpowers g
  let Y' : Subgroup ↥E := (⊥ : Subgroup G).subgroupOf E
  let A : Subgroup G := E ⊓ Subgroup.centralizer (T : Set G)
  have hY'bot : Y' = ⊥ := Subgroup.bot_subgroupOf E
  have hTK : T ≤ K := Subgroup.zpowers_le.mpr t.2
  have hgne : g ≠ 1 := fun h => ht (Subtype.ext (by simpa [g] using h))
  have hTne : T ≠ ⊥ := by
    intro h
    have hmem : g ∈ (⊥ : Subgroup G) := by rw [← h]; exact Subgroup.mem_zpowers g
    exact hgne (Subgroup.mem_bot.mp hmem)
  have hmap : (Subgroup.zpowers t).map K.subtype = T := by
    rw [MonoidHom.map_zpowers]; rfl
  have hT2 : IsPGroup 2 T := hmap ▸ IsPGroup.map ht2 K.subtype
  have hrankT : CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3 := hrank T hTK hTne hT2
  have hAelem : IsElementaryAbelian p ↥A :=
    { toIsMulCommutative := IsMulCommutative.of_comm (fun a b =>
        Subtype.ext (hEc _ (Subgroup.mem_inf.mp a.2).1 _ (Subgroup.mem_inf.mp b.2).1))
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun x =>
        Subtype.ext (hE5 _ (Subgroup.mem_inf.mp x.2).1)) }
  have hAelemOpen : IsElemAbelian p A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).mp hAelem
  have hAN : A ≤ normalizer (T : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup p ↥A).exists_card_eq
  have hk3 : k ≤ 3 :=
    (CFSG.SectionRank.le_pRank (p := p) (H := normalizer (T : Set G)) (E := A)
      hp.out.one_lt hAN hAelemOpen hk).trans hrankT
  have hAcard : Nat.card A ≤ p ^ 3 := by
    rw [hk]
    exact Nat.pow_le_pow_right hp.out.pos hk3
  have key : ∀ v : Additive (↥E ⧸ Y'), v ∈ fixSpace (chiefRepE (p := p) hKE hKbot) t →
      ∃ c : ↥E, (c : G) ∈ A ∧ Additive.ofMul (c : ↥E ⧸ Y') = v := by
    intro v hv
    obtain ⟨c, hc⟩ := CFSG.ABGLocalTools.exists_ofMul_mk (W₁ := E)
      (W₂ := (⊥ : Subgroup G)) v
    have hv_eq : chiefRepE (p := p) hKE hKbot t v = v := (mem_fixSpace _ _ v).mp hv
    have hv_eq' : ((CFSG.ABGLocalTools.chiefRep (p := p) hKE hKbot t :
        LinearMap.GeneralLinearGroup (ZMod p) (Additive (↥E ⧸ Y'))) :
        Additive (↥E ⧸ Y') →ₗ[ZMod p] Additive (↥E ⧸ Y')) v = v := by
      simpa [chiefRepE] using hv_eq
    have h1 : Additive.ofMul ((CFSG.ABGLocalTools.chiefConj hKE t c : ↥E) :
        ↥E ⧸ Y') = Additive.ofMul (c : ↥E ⧸ Y') := by
      have h2 := hv_eq'
      rw [hc] at h2
      rw [CFSG.ABGLocalTools.chiefRep_apply_mk (p := p) hKE hKbot t c] at h2
      exact h2
    have hconj : (CFSG.ABGLocalTools.chiefConj hKE t c : ↥E) = c := by
      have h3 : ((CFSG.ABGLocalTools.chiefConj hKE t c : ↥E) : ↥E ⧸ Y') =
          (c : ↥E ⧸ Y') := Additive.ofMul.injective h1
      have h4 : (CFSG.ABGLocalTools.chiefConj hKE t c)⁻¹ * c ∈ Y' :=
        (QuotientGroup.eq).mp h3
      rw [hY'bot, Subgroup.mem_bot] at h4
      exact inv_mul_eq_one.mp h4
    have hcomm : g * (c : G) = (c : G) * g := by
      have h5 := CFSG.ABGLocalTools.chiefConj_apply_coe hKE t c
      rw [hconj] at h5
      have h5' : (t : G) * (c : G) = (c : G) * (t : G) := by
        have h := congrArg (fun x => x * (t : G)) h5
        simpa [mul_assoc] using h.symm
      exact h5'
    have hcent : (c : G) ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hgcent : g ∈ Subgroup.centralizer ({(c : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm.symm
      have hzle : T ≤ Subgroup.centralizer ({(c : G)} : Set G) :=
        Subgroup.zpowers_le.mpr hgcent
      have h1 := hzle hh
      rw [Subgroup.mem_centralizer_iff] at h1
      exact (h1 (c : G) (Set.mem_singleton _)).symm
    exact ⟨c, Subgroup.mem_inf.mpr ⟨c.2, hcent⟩, hc.symm⟩
  let key' : ∀ v : fixSpace (chiefRepE (p := p) hKE hKbot) t,
      ∃ c : ↥E, (c : G) ∈ A ∧
        Additive.ofMul (c : ↥E ⧸ Y') = (v : Additive (↥E ⧸ Y')) :=
    fun v => key v v.2
  let f : fixSpace (chiefRepE (p := p) hKE hKbot) t → ↥A := fun v =>
    let c := Classical.choose (key' v)
    ⟨(c : G), (Classical.choose_spec (key' v)).1⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have hcv : ((Classical.choose (key' v) : ↥E) : G) =
        ((Classical.choose (key' w) : ↥E) : G) :=
      congrArg (fun x : ↥A => ((x : G))) hvw
    have hce : (Classical.choose (key' v) : ↥E) = Classical.choose (key' w) :=
      Subtype.ext hcv
    have hv := (Classical.choose_spec (key' v)).2
    have hw := (Classical.choose_spec (key' w)).2
    apply Subtype.ext
    rw [← hv, ← hw, hce]
  have hcardfix : Nat.card (fixSpace (chiefRepE (p := p) hKE hKbot) t) ≤ Nat.card A :=
    Nat.card_le_card_of_injective f hf
  have hcarddim : Nat.card (fixSpace (chiefRepE (p := p) hKE hKbot) t) =
      p ^ Module.finrank (ZMod p) (fixSpace (chiefRepE (p := p) hKE hKbot) t) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hfin : p ^ Module.finrank (ZMod p) (fixSpace (chiefRepE (p := p) hKE hKbot) t) ≤ p ^ 3 := by
    rw [← hcarddim]
    exact hcardfix.trans hAcard
  exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hfin

open scoped commutatorElement in
private theorem sz5e1_fc2_abel_card {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {X C : Subgroup G} (hCX : C ≤ X) (hXp : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) (hrk : CFSG.pRank p ↥C ≤ 3) :
    Nat.card (↥C ⧸ commutator ↥C) ≤ p ^ 4 := by
  have hCp : IsPGroup p ↥C := hXp.to_le hCX
  have hexp : ∀ x : ↥C, x ^ p = 1 := fun x => Subtype.ext (hXexp x (hCX x.2))
  have hcl : commutator ↥C ≤ Subgroup.center ↥C := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have h1 : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ = 1 := by
      have : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ ∈ ⁅⁅X, X⁆, X⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator (hCX a.2) (hCX b.2))
          (hCX z.2)
      rw [hXcl] at this
      exact Subgroup.mem_bot.mp this
    have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    simpa [commutatorElement_def, mul_assoc] using h2.symm
  have h4 := (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hCp hexp hcl).2.2 hrk
  obtain ⟨k, hk⟩ := (hCp.to_quotient (commutator ↥C)).exists_card_eq
  have := (CFSG.RankThree.PartTwo.quotient_commutator_rank hp.out hexp hk).2
  rw [hk]
  exact Nat.pow_le_pow_right hp.out.pos (this ▸ h4)

private theorem sz5e1_fc2_not_two_dvd {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup G} (hXp : IsPGroup p X) (Y' : Subgroup ↥X) :
    ¬ 2 ∣ Nat.card Y' := by
  intro hdvd
  obtain ⟨m, hm⟩ := hXp.exists_card_eq
  have h1 : Nat.card Y' ∣ p ^ m := hm ▸ Subgroup.card_subgroup_dvd_card Y'
  have h2' : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (hdvd.trans h1)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h2').symm

private theorem sz5e1_fc2_zpowers_fix {G M : Type} [Group G] [Group M] (t : G)
    (ψ : ↥(Subgroup.zpowers t) →* MulAut M) {q : M}
    (h : ψ ⟨t, Subgroup.mem_zpowers t⟩ q = q) (a : ↥(Subgroup.zpowers t)) : ψ a q = q := by
  let S : Subgroup ↥(Subgroup.zpowers t) := (MulAction.stabilizer (MulAut M) q).comap ψ
  have htS : (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) ∈ S := by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have hzS : Subgroup.zpowers (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) ≤ S :=
    Subgroup.zpowers_le.mpr htS
  have haz : a ∈ Subgroup.zpowers (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  have := hzS haz
  rwa [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

private theorem sz5e1_fc2_fix_lift {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {X Y K : Subgroup G} (hXp : IsPGroup p X) (hKX : K ≤ normalizer (X : Set G))
    (hKY : K ≤ normalizer (Y : Set G)) [(Y.subgroupOf X).Normal]
    [CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X)] {t : G} (htK : t ∈ K)
    (hT2 : IsPGroup 2 ↥(Subgroup.zpowers t)) :
    ∀ v ∈ LinearMap.ker ((CFSG.ABGLocalTools.chiefRep (p := p) hKX hKY ⟨t, htK⟩ :
      LinearMap.GeneralLinearGroup (ZMod p) _).val - 1),
    ∃ c : ↥X, (c : G) ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) ∧
      Additive.ofMul (c : ↥X ⧸ Y.subgroupOf X) = v := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y' : Subgroup ↥X := Y.subgroupOf X with hY'
  set T : Subgroup G := Subgroup.zpowers t with hT
  have hTK : T ≤ K := Subgroup.zpowers_le.mpr htK
  have hTX : T ≤ normalizer (X : Set G) := hTK.trans hKX
  have hTY : T ≤ normalizer (Y : Set G) := hTK.trans hKY
  have hT2' : IsPGroup 2 ↥T := hT.symm ▸ hT2
  let α : ↥T →* MulAut ↥X := CFSG.ABGLocalTools.chiefConj hTX
  have hα : ∀ (a : ↥T) (x : ↥X), ((α a x : ↥X) : G) = (a : G) * x * (a : G)⁻¹ :=
    fun a x => CFSG.ABGLocalTools.chiefConj_apply_coe hTX a x
  have hαY : ∀ a : ↥T, ∀ n ∈ Y', α a n ∈ Y' := by
    intro a n hn
    rw [hY', Subgroup.mem_subgroupOf] at hn ⊢
    rw [hα]
    exact (Subgroup.mem_normalizer_iff.mp (hTY a.2) n).mp hn
  have hcop : ¬ 2 ∣ Nat.card Y' := sz5e1_fc2_not_two_dvd hp2 hXp Y'
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hT2' α Y' hαY hcop
  intro v hv
  obtain ⟨w, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
  have hfixw : ((CFSG.ABGLocalTools.chiefConj hKX ⟨t, htK⟩ w : ↥X) : ↥X ⧸ Y') =
      (w : ↥X ⧸ Y') := by
    have h1 := LinearMap.mem_ker.mp hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      CFSG.ABGLocalTools.chiefRep_apply_mk] at h1
    exact congrArg Additive.toMul h1
  set q : ↥X ⧸ Y' := (w : ↥X ⧸ Y') with hq
  have ht0 : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α Y' hαY
      ⟨t, Subgroup.mem_zpowers t⟩ q = q := by
    rw [hq, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    have : (α ⟨t, Subgroup.mem_zpowers t⟩ w : ↥X) =
        CFSG.ABGLocalTools.chiefConj hKX ⟨t, htK⟩ w :=
      Subtype.ext (by rw [hα, CFSG.ABGLocalTools.chiefConj_apply_coe])
    rw [this]
    exact hfixw
  have hall : ∀ a : ↥T, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α Y' hαY
      a q = q := sz5e1_fc2_zpowers_fix t _ ht0
  have hmem : q ∈ {q : ↥X ⧸ Y' | ∀ a : ↥T,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α Y' hαY a q = q} := hall
  rw [hlift] at hmem
  obtain ⟨c, hc, hcq⟩ := hmem
  refine ⟨c, ?_, congrArg Additive.ofMul hcq⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h3 : (s : G) * c * (s : G)⁻¹ = c := by
    have := congrArg Subtype.val (hc ⟨s, hs⟩)
    rwa [hα] at this
  calc s * (c : G) = (s * c * s⁻¹) * s := by group
    _ = c * s := by rw [h3]

private theorem sz5e1_fc2_fix_count {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {X Y T : Subgroup G} (hXp : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) [(Y.subgroupOf X).Normal]
    [CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X)]
    (hrank : CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3)
    (F : Submodule (ZMod p) (Additive (↥X ⧸ Y.subgroupOf X)))
    (key : ∀ v ∈ F, ∃ c : ↥X, (c : G) ∈ Subgroup.centralizer (T : Set G) ∧
      Additive.ofMul (c : ↥X ⧸ Y.subgroupOf X) = v) :
    Module.finrank (ZMod p) F ≤ 4 := by
  classical
  set Y' : Subgroup ↥X := Y.subgroupOf X with hY'
  set C : Subgroup G := X ⊓ Subgroup.centralizer (T : Set G) with hC
  have hCX : C ≤ X := inf_le_left
  have hCN : C ≤ normalizer (T : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  have hrk : CFSG.pRank p ↥C ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    calc CFSG.Open.pRank p (⊤ : Subgroup ↥C)
        ≤ CFSG.Open.pRank p ((⊤ : Subgroup ↥C).map C.subtype) :=
          CFSG.SectionRank.pRank_le_map hp.out.one_lt C.subtype C.subtype_injective ⊤
      _ ≤ CFSG.Open.pRank p (normalizer (T : Set G)) := by
          refine CFSG.SectionRank.pRank_mono hp.out.one_lt ?_
          rw [Subgroup.map_top, Subgroup.range_subtype]
          exact hCN
      _ ≤ 3 := hrank
  have hbound := sz5e1_fc2_abel_card hCX hXp hXexp hXcl hrk
  let h : ↥C →* ↥X ⧸ Y' := (QuotientGroup.mk' Y').comp (Subgroup.inclusion hCX)
  have hker : commutator ↥C ≤ h.ker := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  let q : ↥C ⧸ commutator ↥C →* ↥X ⧸ Y' := QuotientGroup.lift (commutator ↥C) h hker
  have hmemq : ∀ v : F, Additive.toMul (v : Additive (↥X ⧸ Y')) ∈ Set.range q := by
    intro v
    obtain ⟨c, hcC, hcv⟩ := key v v.2
    have hcC' : (c : G) ∈ C := Subgroup.mem_inf.mpr ⟨c.2, hcC⟩
    refine ⟨((⟨c, hcC'⟩ : ↥C) : ↥C ⧸ commutator ↥C), ?_⟩
    have h1 : q ((⟨c, hcC'⟩ : ↥C) : ↥C ⧸ commutator ↥C) = (c : ↥X ⧸ Y') := rfl
    rw [h1, ← hcv]
    rfl
  have hinj : Function.Injective (Set.codRestrict (fun v : F => Additive.toMul (v : Additive (↥X ⧸ Y')))
      (Set.range q) hmemq) := by
    rw [Set.injective_codRestrict]
    intro v w hvw
    exact Subtype.ext (Additive.toMul.injective hvw)
  have hF4 : Nat.card F ≤ p ^ 4 :=
    (Nat.card_le_card_of_injective _ hinj).trans ((Finite.card_range_le q).trans hbound)
  have hfin : Module.Finite (ZMod p) F := inferInstance
  have hcard : Nat.card F = p ^ Module.finrank (ZMod p) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rw [hcard] at hF4
  exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hF4

private theorem sz5e1_fc2_fix {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {X Y K : Subgroup G} (hXp : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) (hKX : K ≤ normalizer (X : Set G))
    (hKY : K ≤ normalizer (Y : Set G)) [(Y.subgroupOf X).Normal]
    [CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X)] {t : G} (htK : t ∈ K)
    (hT2 : IsPGroup 2 ↥(Subgroup.zpowers t))
    (hrank : CFSG.Open.pRank p (normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) ≤ 3) :
    Module.finrank (ZMod p)
      (LinearMap.ker ((CFSG.ABGLocalTools.chiefRep (p := p) hKX hKY ⟨t, htK⟩ :
        LinearMap.GeneralLinearGroup (ZMod p) _).val - 1)) ≤ 4 :=
  sz5e1_fc2_fix_count hXp hXexp hXcl hrank _ (sz5e1_fc2_fix_lift hp2 hXp hKX hKY htK hT2)

theorem sz5e1_fixbound_class_two {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (K X Y : Subgroup G)
    (hrank : ∀ T : Subgroup G, T ≤ K → T ≠ ⊥ → IsPGroup 2 T →
      CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3)
    (hX5 : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1) (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥)
    (hKX : K ≤ normalizer (X : Set G)) (hKY : K ≤ normalizer (Y : Set G))
    [(Y.subgroupOf X).Normal] [IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X)] :
    FixBound (chiefRepE (p := p) hKX hKY) 4 := by
  intro t htne ht2
  let g : G := (t : G)
  have hgK : g ∈ K := t.2
  have hTle : Subgroup.zpowers g ≤ K := Subgroup.zpowers_le.mpr hgK
  have hTne : Subgroup.zpowers g ≠ ⊥ := by
    intro hbot
    rw [Subgroup.zpowers_eq_bot] at hbot
    exact htne (Subtype.ext hbot)
  have hz2 : IsPGroup 2 (Subgroup.zpowers g) := by
    have h1 := ht2.map K.subtype
    rwa [MonoidHom.map_zpowers] at h1
  have hfix := sz5e1_fc2_fix (p := p) hp2 hX5 hXexp hXcl hKX hKY hgK hz2
    (hrank (Subgroup.zpowers g) hTle hTne hz2)
  have hsub : (⟨g, hgK⟩ : ↥K) = t := Subtype.ext rfl
  rw [← hsub]
  have hV : fixSpace (chiefRepE (p := p) hKX hKY) (⟨g, hgK⟩ : ↥K) =
      LinearMap.ker ((CFSG.ABGLocalTools.chiefRep (p := p) hKX hKY (⟨g, hgK⟩ : ↥K) :
        LinearMap.GeneralLinearGroup (ZMod p)
          (Additive (↥X ⧸ Y.subgroupOf X))).val - 1) := by
    ext v
    simp [fixSpace, fixSpaceOf, chiefRepE]
  rw [hV]
  exact hfix

private theorem sz5e1_end_chiefRepE_mk {p : ℕ} [hp : Fact p.Prime] {H : Type} [Group H]
    {N W₁ W₂ : Subgroup H}
    (hN₁ : N ≤ normalizer (W₁ : Set H)) (hN₂ : N ≤ normalizer (W₂ : Set H))
    [(W₂.subgroupOf W₁).Normal] [IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁)]
    (n : N) (w : W₁) :
    chiefRepE (p := p) hN₁ hN₂ n (Additive.ofMul ((w : W₁) : W₁ ⧸ W₂.subgroupOf W₁)) =
      Additive.ofMul (((CFSG.ABGLocalTools.chiefConj hN₁ n w : W₁)) :
        W₁ ⧸ W₂.subgroupOf W₁) := by
  show (CFSG.ABGLocalTools.chiefRep (p := p) hN₁ hN₂ n :
      Additive (↥W₁ ⧸ W₂.subgroupOf W₁) →ₗ[ZMod p] Additive (↥W₁ ⧸ W₂.subgroupOf W₁))
      (Additive.ofMul ((w : W₁) : W₁ ⧸ W₂.subgroupOf W₁)) = _
  rw [CFSG.ABGLocalTools.chiefRep_apply_mk]

private theorem sz5e1_end_form {G : Type} [Group G] {p : ℕ} [hp : Fact p.Prime]
    (K X Z : Subgroup G)
    (hZX : Z ≤ X) (hZc : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z)
    (hXXZ : ⁅X, X⁆ ≤ Z)
    (hKX : K ≤ normalizer (X : Set G)) (hKZ : K ≤ normalizer (Z : Set G))
    [(Z.subgroupOf X).Normal] [IsElementaryAbelian p (↥X ⧸ Z.subgroupOf X)]
    [IsElementaryAbelian p ↥Z] (hZK : ⁅Z, K⁆ = ⊥)
    (ℓ : Additive ↥Z →ₗ[ZMod p] ZMod p) :
    ∃ f : Additive (↥X ⧸ Z.subgroupOf X) →ₗ[ZMod p]
        Additive (↥X ⧸ Z.subgroupOf X) →ₗ[ZMod p] ZMod p,
      (∀ v, f v v = 0) ∧
      (∀ (k : ↥K) (v w : Additive (↥X ⧸ Z.subgroupOf X)),
        f (chiefRepE (p := p) hKX hKZ k v) (chiefRepE (p := p) hKX hKZ k w) = f v w) ∧
      (∀ x y : ↥X,
        f (Additive.ofMul ((x : ↥X) : ↥X ⧸ Z.subgroupOf X))
          (Additive.ofMul ((y : ↥X) : ↥X ⧸ Z.subgroupOf X)) =
        ℓ (Additive.ofMul ⟨⁅(x : G), (y : G)⁆,
          hXXZ (Subgroup.commutator_mem_commutator x.2 y.2)⟩)) := by
  classical
  have hmem : ∀ x y : ↥X, ⁅(x : G), (y : G)⁆ ∈ Z :=
    fun x y => hXXZ (Subgroup.commutator_mem_commutator x.2 y.2)
  let cRight : ↥X → ↥X →* ↥Z := fun x =>
    { toFun := fun y => ⟨⁅(x : G), (y : G)⁆, hmem x y⟩
      map_one' := by
        apply Subtype.ext
        show ⁅(x : G), (((1 : ↥X) : G))⁆ = (1 : G)
        simp
      map_mul' := fun y y' => by
        apply Subtype.ext
        show ⁅(x : G), ((y : G) * (y' : G))⁆ =
          ⁅(x : G), (y : G)⁆ * ⁅(x : G), (y' : G)⁆
        have hz : ⁅(x : G), (y' : G)⁆ ∈ Z := hmem x y'
        have hc : (y : G) * ⁅(x : G), (y' : G)⁆ = ⁅(x : G), (y' : G)⁆ * (y : G) :=
          (hZc _ hz (y : G) y.2).symm
        rw [commutatorElement_mul_right_eq_mul_conj,
          mul_assoc ⁅(x : G), (y : G)⁆ (y : G) ⁅(x : G), (y' : G)⁆, hc, ← mul_assoc,
          mul_inv_cancel_right] }
  have hkerRight : ∀ x : ↥X, Z.subgroupOf X ≤ (cRight x).ker := by
    intro x z hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hzZ : (z : G) ∈ Z := by simpa [Subgroup.mem_subgroupOf] using hz
    show ⁅(x : G), (z : G)⁆ = (1 : G)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (hZc (z : G) hzZ (x : G) x.2).symm
  let cRightQ : ↥X → (↥X ⧸ Z.subgroupOf X →* ↥Z) := fun x =>
    QuotientGroup.lift (Z.subgroupOf X) (cRight x) (hkerRight x)
  have hRightQmul : ∀ x x' : ↥X, cRightQ (x * x') = cRightQ x * cRightQ x' := by
    intro x x'
    apply MonoidHom.ext
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    show (cRightQ (x * x')) (y : ↥X ⧸ Z.subgroupOf X) =
      (cRightQ x * cRightQ x') (y : ↥X ⧸ Z.subgroupOf X)
    rw [MonoidHom.mul_apply]
    show (⟨⁅((x * x' : ↥X) : G), (y : G)⁆, hmem (x * x') y⟩ : ↥Z) =
      (⟨⁅(x : G), (y : G)⁆, hmem x y⟩ : ↥Z) * ⟨⁅(x' : G), (y : G)⁆, hmem x' y⟩
    apply Subtype.ext
    show ⁅((x : G) * (x' : G)), (y : G)⁆ = ⁅(x : G), (y : G)⁆ * ⁅(x' : G), (y : G)⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hz : ⁅(x' : G), (y : G)⁆ ∈ Z := hmem x' y
    have hc : (x : G) * ⁅(x' : G), (y : G)⁆ = ⁅(x' : G), (y : G)⁆ * (x : G) :=
      (hZc _ hz (x : G) x.2).symm
    rw [hc, mul_inv_cancel_right]
    exact (hZc _ (hmem x y) _ (hZX (hmem x' y))).symm
  let cLeft : ↥X →* (↥X ⧸ Z.subgroupOf X →* ↥Z) :=
    { toFun := cRightQ
      map_one' := by
        apply MonoidHom.ext
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        show (cRightQ 1) (y : ↥X ⧸ Z.subgroupOf X) = 1
        show (⟨⁅(((1 : ↥X) : G)), (y : G)⁆, hmem 1 y⟩ : ↥Z) = 1
        apply Subtype.ext
        show ⁅(((1 : ↥X) : G)), (y : G)⁆ = (1 : G)
        simp
      map_mul' := hRightQmul }
  have hkerLeft : Z.subgroupOf X ≤ cLeft.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply MonoidHom.ext
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hzZ : (z : G) ∈ Z := by simpa [Subgroup.mem_subgroupOf] using hz
    show (cRightQ z) (y : ↥X ⧸ Z.subgroupOf X) = 1
    show (⟨⁅(z : G), (y : G)⁆, hmem z y⟩ : ↥Z) = 1
    apply Subtype.ext
    show ⁅(z : G), (y : G)⁆ = (1 : G)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hZc (z : G) hzZ (y : G) y.2
  let cBoth : ↥X ⧸ Z.subgroupOf X →* (↥X ⧸ Z.subgroupOf X →* ↥Z) :=
    QuotientGroup.lift (Z.subgroupOf X) cLeft hkerLeft
  have hcBoth_mk : ∀ x y : ↥X,
      cBoth ((x : ↥X) : ↥X ⧸ Z.subgroupOf X) ((y : ↥X) : ↥X ⧸ Z.subgroupOf X) =
        (⟨⁅(x : G), (y : G)⁆, hmem x y⟩ : ↥Z) := by
    intro x y
    rfl
  let β : Additive (↥X ⧸ Z.subgroupOf X) →+ Additive (↥X ⧸ Z.subgroupOf X) →+ Additive ↥Z :=
    { toFun := fun u =>
        { toFun := fun v => Additive.ofMul (cBoth (Additive.toMul u) (Additive.toMul v))
          map_zero' := by
            change Additive.ofMul (cBoth (Additive.toMul u) 1) = 0
            rw [map_one, ofMul_one]
          map_add' := fun v v' => by
            change Additive.ofMul (cBoth (Additive.toMul u)
                (Additive.toMul v * Additive.toMul v')) =
              Additive.ofMul (cBoth (Additive.toMul u) (Additive.toMul v)) +
                Additive.ofMul (cBoth (Additive.toMul u) (Additive.toMul v'))
            rw [map_mul, ofMul_mul] }
      map_zero' := by
        apply AddMonoidHom.ext
        intro v
        change Additive.ofMul (cBoth 1 (Additive.toMul v)) = 0
        rw [map_one, MonoidHom.one_apply, ofMul_one]
      map_add' := fun u u' => by
        apply AddMonoidHom.ext
        intro v
        change Additive.ofMul (cBoth (Additive.toMul u * Additive.toMul u')
            (Additive.toMul v)) =
          Additive.ofMul (cBoth (Additive.toMul u) (Additive.toMul v)) +
            Additive.ofMul (cBoth (Additive.toMul u') (Additive.toMul v))
        rw [map_mul, MonoidHom.mul_apply, ofMul_mul] }
  let f : Additive (↥X ⧸ Z.subgroupOf X) →ₗ[ZMod p]
      Additive (↥X ⧸ Z.subgroupOf X) →ₗ[ZMod p] ZMod p :=
    LinearMap.mk₂ (ZMod p) (fun u v => ℓ (β u v))
      (fun u u' v => by simp)
      (fun c u v => by simp [ZMod.map_smul, map_smul])
      (fun u v v' => by simp)
      (fun c u v => by simp [ZMod.map_smul, map_smul])
  have hf_apply : ∀ u v, f u v = ℓ (β u v) := fun u v => rfl
  have hclass : ∀ x y : ↥X,
      f (Additive.ofMul ((x : ↥X) : ↥X ⧸ Z.subgroupOf X))
        (Additive.ofMul ((y : ↥X) : ↥X ⧸ Z.subgroupOf X)) =
      ℓ (Additive.ofMul ⟨⁅(x : G), (y : G)⁆,
        hXXZ (Subgroup.commutator_mem_commutator x.2 y.2)⟩) := by
    intro x y
    rw [hf_apply]
    rfl
  have halt : ∀ v, f v v = 0 := by
    intro v
    obtain ⟨x, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
    rw [hclass]
    have h1 : (⟨⁅(x : G), (x : G)⁆, hmem x x⟩ : ↥Z) = 1 := by
      apply Subtype.ext
      show ⁅(x : G), (x : G)⁆ = (1 : G)
      rw [commutatorElement_self]
    rw [h1, ofMul_one, map_zero]
  have hinv : ∀ (k : ↥K) (v w : Additive (↥X ⧸ Z.subgroupOf X)),
      f (chiefRepE (p := p) hKX hKZ k v) (chiefRepE (p := p) hKX hKZ k w) = f v w := by
    intro k v w
    obtain ⟨x, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
    obtain ⟨y, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk w
    rw [sz5e1_end_chiefRepE_mk hKX hKZ k x, sz5e1_end_chiefRepE_mk hKX hKZ k y]
    rw [hclass, hclass]
    congr 1
    change Additive.ofMul (cBoth
        ((CFSG.ABGLocalTools.chiefConj hKX k x : ↥X) : ↥X ⧸ Z.subgroupOf X)
        ((CFSG.ABGLocalTools.chiefConj hKX k y : ↥X) : ↥X ⧸ Z.subgroupOf X)) =
      Additive.ofMul (cBoth ((x : ↥X) : ↥X ⧸ Z.subgroupOf X)
        ((y : ↥X) : ↥X ⧸ Z.subgroupOf X))
    rw [hcBoth_mk, hcBoth_mk]
    congr 1
    apply Subtype.ext
    show ⁅(↑(CFSG.ABGLocalTools.chiefConj hKX k x) : G),
        (↑(CFSG.ABGLocalTools.chiefConj hKX k y) : G)⁆ = ⁅(x : G), (y : G)⁆
    rw [CFSG.ABGLocalTools.chiefConj_apply_coe, CFSG.ABGLocalTools.chiefConj_apply_coe]
    have hconj : ⁅(k : G) * (x : G) * (k : G)⁻¹,
        (k : G) * (y : G) * (k : G)⁻¹⁆ = ⁅(x : G), (y : G)⁆ := by
      rw [← conjugate_commutatorElement]
      have hz : ⁅(x : G), (y : G)⁆ ∈ Z := hmem x y
      have hkz : (k : G) * ⁅(x : G), (y : G)⁆ = ⁅(x : G), (y : G)⁆ * (k : G) :=
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZK) hz) (k : G) k.2
      rw [hkz, mul_inv_cancel_right]
    exact hconj
  exact ⟨f, halt, hinv, hclass⟩

theorem sz5e1_class_two_endgame {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (K X Z : Subgroup G)
    (hX5 : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1) (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥)
    (hZX : Z ≤ X) (hZc : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (hXXZ : ⁅X, X⁆ ≤ Z)
    (hKX : K ≤ normalizer (X : Set G)) (hKZ : K ≤ normalizer (Z : Set G))
    [(Z.subgroupOf X).Normal] [IsElementaryAbelian p (↥X ⧸ Z.subgroupOf X)]
    (hZK : ⁅Z, K⁆ = ⊥)
    (hL51 : ∀ E : Subgroup G, IsPGroup p E → (∀ x ∈ E, x ^ p = 1) →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → K ≤ normalizer (E : Set G) → ⁅E, K⁆ = ⊥)
    (B : Submodule (ZMod p) (Additive (↥X ⧸ Z.subgroupOf X)))
    (hB : ∀ k : ↥K, ∀ b ∈ B, chiefRepE (p := p) hKX hKZ k b ∈ B)
    (hBnt : ∃ k : ↥K, ∃ b ∈ B, chiefRepE (p := p) hKX hKZ k b ≠ b)
    (hC : ∀ f : Additive (↥X ⧸ Z.subgroupOf X) →ₗ[ZMod p]
        Additive (↥X ⧸ Z.subgroupOf X) →ₗ[ZMod p] ZMod p,
      (∀ v, f v v = 0) →
      (∀ (k : ↥K) (v w : Additive (↥X ⧸ Z.subgroupOf X)),
        f (chiefRepE (p := p) hKX hKZ k v) (chiefRepE (p := p) hKX hKZ k w) = f v w) →
      ∀ v ∈ B, ∀ w ∈ B, f v w = 0) :
    False := by
  classical
  have _ := hXcl
  have hexpZ : ∀ z : ↥Z, z ^ p = 1 :=
    fun z => Subtype.ext (by simpa using hXexp (z : G) (hZX z.2))
  have hEAZ : IsElementaryAbelian p ↥Z :=
    { toIsMulCommutative :=
        IsMulCommutative.of_comm (fun a b => Subtype.ext (hZc (a : G) a.2 (b : G) (hZX b.2)))
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hexpZ }
  let Q := ↥X ⧸ Z.subgroupOf X
  let Bsub : Subgroup Q := B.toAddSubgroup.toSubgroup'
  let Psub : Subgroup ↥X := Bsub.comap (QuotientGroup.mk' (Z.subgroupOf X))
  let P : Subgroup G := Psub.map X.subtype
  have hmemP : ∀ x : ↥X, Additive.ofMul ((x : ↥X) : Q) ∈ B ↔ x ∈ Psub := by
    intro x
    rw [Subgroup.mem_comap, AddSubgroup.mem_toSubgroup']
    exact Iff.rfl
  have hPleX : P ≤ X := Subgroup.map_subtype_le (H := X) Psub
  have hZleP : Z ≤ P := by
    intro z hz
    refine ⟨⟨z, hZX hz⟩, ?_, rfl⟩
    apply (hmemP ⟨z, hZX hz⟩).mp
    have h1 : (((⟨z, hZX hz⟩ : ↥X) : Q)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hz)
    rw [h1]
    exact B.zero_mem
  have hKPconj : ∀ k ∈ K, ∀ g ∈ P, k * g * k⁻¹ ∈ P := by
    intro k hk g hg
    rcases hg with ⟨x, hx, rfl⟩
    refine ⟨CFSG.ABGLocalTools.chiefConj hKX ⟨k, hk⟩ x, ?_, ?_⟩
    · refine (hmemP (CFSG.ABGLocalTools.chiefConj hKX ⟨k, hk⟩ x)).mp ?_
      have h := hB ⟨k, hk⟩ (Additive.ofMul ((x : ↥X) : Q)) ((hmemP x).mpr hx)
      rwa [sz5e1_end_chiefRepE_mk hKX hKZ ⟨k, hk⟩ x] at h
    · exact CFSG.ABGLocalTools.chiefConj_apply_coe hKX ⟨k, hk⟩ x
  have hKP : K ≤ normalizer (P : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact hKPconj k hk g hg
    · intro hg
      have h1 := hKPconj k⁻¹ (K.inv_mem hk) (k * g * k⁻¹) hg
      have h2 : k⁻¹ * (k * g * k⁻¹) * (k⁻¹)⁻¹ = g := by group
      rwa [h2] at h1
  have hPabel : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rcases ha with ⟨x, hx, rfl⟩
    rcases hb with ⟨y, hy, rfl⟩
    have hxB : Additive.ofMul ((x : ↥X) : Q) ∈ B := (hmemP x).mpr hx
    have hyB : Additive.ofMul ((y : ↥X) : Q) ∈ B := (hmemP y).mpr hy
    let z : ↥Z := ⟨⁅(x : G), (y : G)⁆,
      hXXZ (Subgroup.commutator_mem_commutator x.2 y.2)⟩
    have hz0 : Additive.ofMul z = 0 :=
      (Module.forall_dual_apply_eq_zero_iff (ZMod p) (Additive.ofMul z)).mp (by
        intro ℓ
        obtain ⟨f, hfalt, hfinv, hfclass⟩ :=
          sz5e1_end_form K X Z hZX hZc hXXZ hKX hKZ hZK ℓ
        have h0 := hC f hfalt hfinv _ hxB _ hyB
        rw [hfclass x y] at h0
        exact h0)
    have hz1 : z = 1 := Additive.ofMul.injective (by rw [hz0, ofMul_one])
    have hzcoe : (z : G) = ⁅X.subtype x, X.subtype y⁆ := rfl
    rw [← hzcoe]
    exact congrArg (fun w : ↥Z => (w : G)) hz1
  have hP5 : IsPGroup p P := hX5.to_le hPleX
  have hPexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => hXexp x (hPleX hx)
  have hcommP : ⁅P, K⁆ = ⊥ := hL51 P hP5 hPexp hPabel hKP
  obtain ⟨k, b, hbB, hbne⟩ := hBnt
  obtain ⟨x, hbx⟩ := CFSG.ABGLocalTools.exists_ofMul_mk b
  have hxP : x ∈ Psub := by
    rw [← hmemP x, ← hbx]
    exact hbB
  have hxP' : (x : G) ∈ P := ⟨x, hxP, rfl⟩
  have hcent := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommP) hxP'
  have hkx : (k : G) * (x : G) = (x : G) * (k : G) :=
    Subgroup.mem_centralizer_iff.mp hcent (k : G) k.2
  have hconjfix : CFSG.ABGLocalTools.chiefConj hKX k x = x := by
    apply Subtype.ext
    rw [CFSG.ABGLocalTools.chiefConj_apply_coe]
    rw [hkx, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : chiefRepE (p := p) hKX hKZ k b = b := by
    rw [hbx, sz5e1_end_chiefRepE_mk hKX hKZ k x, hconjfix]
  exact hbne hfix

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
