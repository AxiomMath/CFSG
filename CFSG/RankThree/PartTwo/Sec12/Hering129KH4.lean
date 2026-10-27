module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KH3
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH1
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH2

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)


namespace Hering129KH4

variable {P : Type} [Group P] [Finite P] {Yh Bh : Subgroup P} {xh bh ch : P}
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] noncomputable def liftSub (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    (F : Subgroup (ProjGenLinGroup (Fin 3) K)) : Subgroup P :=
  ((F.subgroupOf (projImage (Sec4.slPi π 3 (p ^ f) K))).map e.symm.toMonoidHom).map Yh.subtype

theorem mem_liftSub (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    (F : Subgroup (ProjGenLinGroup (Fin 3) K)) {g : P} :
    g ∈ liftSub e F ↔ ∃ hg : g ∈ Yh,
      ((e ⟨g, hg⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ∈ F := by
  constructor
  · intro hg
    obtain ⟨a, haM, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨b, hbF, hba⟩ := Subgroup.mem_map.mp haM
    have hea : e a = b := by
      rw [← hba]
      exact e.apply_symm_apply b
    refine ⟨a.2, ?_⟩
    show ((e a : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ∈ F
    rw [hea]
    exact Subgroup.mem_subgroupOf.mp hbF
  · rintro ⟨hgY, hgF⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hgY⟩, Subgroup.mem_map.mpr
      ⟨e ⟨g, hgY⟩, Subgroup.mem_subgroupOf.mpr hgF, e.symm_apply_apply _⟩, rfl⟩

theorem mem_normalizer_of_forall_mem {G : Type*} [Group G] (S : Subgroup G) [Finite S] {c : G}
    (h : ∀ s ∈ S, c * s * c⁻¹ ∈ S) : c ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  let φ : S → S := fun s => ⟨c * s * c⁻¹, h s s.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : c * (a : G) * c⁻¹ = c * (b : G) * c⁻¹ := congrArg (fun t : S => (t : G)) hab
    exact Subtype.ext (by simpa using h1)
  obtain ⟨s, hs⟩ := Finite.surjective_of_injective hinj ⟨c * n * c⁻¹, hn⟩
  have h2 : c * (s : G) * c⁻¹ = c * n * c⁻¹ := congrArg (fun t : S => (t : G)) hs
  have h3 : (s : G) = n := by simpa using h2
  rw [← h3]
  exact s.2

theorem two_lt_pow_of_not_isSolvable {K : Type} [Field K] {π : Bool} {p f : ℕ}
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    (hns : ¬ Group.IsSolvable (projImage (Sec4.slPi π 3 (p ^ f) K))) : 2 < p ^ f := by
  by_contra hle
  have hp : p.Prime := hK.prime
  have hf : 1 ≤ f := hK.one_le
  have h2 : p ^ f = 2 := by
    have h1 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have hp2 : p = 2 := by
    have hd : p ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
  subst hp2
  have hf1 : f = 1 := Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 1 by rw [h2, pow_one])
  subst hf1
  cases π with
  | true => norm_num [Sec4.ModThree] at hq
  | false =>
    apply hns
    have hcard := CFSG.RankThree.CentralLiftU.card_statedSU_three_two hK.unitary rfl
    have hcard' : Nat.card (Sec4.slPi false 3 (2 ^ 1) K) = 216 := hcard
    haveI : Finite (Sec4.slPi false 3 (2 ^ 1) K) :=
      Nat.finite_of_card_ne_zero (by rw [hcard']; norm_num)
    haveI : Fintype (Sec4.slPi false 3 (2 ^ 1) K) := Fintype.ofFinite _
    have hsolv : Group.IsSolvable (Sec4.slPi false 3 (2 ^ 1) K) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcard']; norm_num)
    exact Group.isSolvable_of_surjective (Sec4.projOf_surjective _)

theorem liftSub_props [Yh.Normal] (hD : HessData Yh Bh xh bh ch) (hK : Sec4.PiField π p f K)
    (hq : Sec4.ModThree π (p ^ f)) (e : ↥Yh ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
    (hact : ∀ g ∈ Yh ⊔ Bh, ∃ y, Sec4.IsPGLAtP e g y) {y : GL (Fin 3) K}
    (hy : Sec4.IsPGLAtP e bh y) {F : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hF : PglHess π p f K y
      ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) F) :
    liftSub e F ≤ Yh ∧ CFSG.Assembly.IsElemAbelian 3 (liftSub e F) ∧
      Nat.card (liftSub e F) = 9 ∧ ch ∈ liftSub e F ∧
      Bh ≤ Subgroup.normalizer (liftSub e F : Set P) ∧ liftSub e F ⊓ Bh = Subgroup.zpowers ch ∧
      (∀ g ∈ liftSub e F, bh * g * bh⁻¹ * g⁻¹ ∈ Subgroup.zpowers ch) ∧
      (∃ g ∈ liftSub e F, bh * g * bh⁻¹ * g⁻¹ ≠ 1) := by
  obtain ⟨hFL, hFab, hFcard, hm0F, hFnorm, hFint, hFcomm, hFnt, -, -⟩ := hF
  set m₀ : ProjGenLinGroup (Fin 3) K :=
    ((e ⟨ch, hD.cY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) with hm₀
  have hconj : ∀ x : P, ∀ g ∈ Yh, x * g * x⁻¹ ∈ Yh := fun x g hg =>
    Subgroup.Normal.conj_mem inferInstance g hg x
  have hxBh : xh ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers xh))
  have hbBh : bh ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers bh))
  have hchBh : ch ∈ Bh := by
    rw [hD.gen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ch)
  have hxC : xh ∈ Subgroup.centralizer (Yh : Set P) := by
    have h := Subgroup.mem_zpowers xh
    rw [← hD.cent] at h
    exact (Subgroup.mem_inf.mp h).2
  have hns : ¬ Group.IsSolvable (projImage (Sec4.slPi π 3 (p ^ f) K)) := by
    intro hs
    apply Hering129KH2.not_isSolvable_of_hessData hD
    haveI := hs
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) (MulEquiv.surjective e.symm)
  haveI hperf : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hK
      (two_lt_pow_of_not_isSolvable hK hq hns)
  haveI hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; norm_num)
  haveI hFcm : IsMulCommutative F := hFab.1
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : F) ⟨b, hb⟩)
  have hmkN : ProjGenLinGroup.mk y ∈ Subgroup.normalizer (F : Set (ProjGenLinGroup (Fin 3) K)) :=
    mem_normalizer_of_forall_mem F hFnorm
  have hm0N : m₀ ∈ Subgroup.normalizer (F : Set (ProjGenLinGroup (Fin 3) K)) := by
    apply mem_normalizer_of_forall_mem F
    intro s hs
    have hc : m₀ * s * m₀⁻¹ = s := by
      rw [hcomm m₀ hm0F s hs, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc]
    exact hs
  obtain ⟨T, hT⟩ : ∃ T : Subgroup (ProjGenLinGroup (Fin 3) K),
      T = Subgroup.zpowers (ProjGenLinGroup.mk y) ⊔ Subgroup.zpowers m₀ := ⟨_, rfl⟩
  rw [← hT] at hFint
  have hTN : T ≤ Subgroup.normalizer (F : Set (ProjGenLinGroup (Fin 3) K)) := by
    rw [hT]
    exact sup_le (Subgroup.zpowers_le.mpr hmkN) (Subgroup.zpowers_le.mpr hm0N)
  have hTy : ProjGenLinGroup.mk y ∈ T := by
    rw [hT]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hTm : m₀ ∈ T := by
    rw [hT]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hN0 : StatedScalars (Fin 3) K ≤
      (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).ker :=
    fun g hg => MonoidHom.mem_ker.mpr (Sec4.mk_eq_one_iff_mem_statedScalars.mpr hg)
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : (Yh ⊔ Bh : Subgroup P) →* ProjGenLinGroup (Fin 3) K,
      ∀ a, ψ a = QuotientGroup.lift (StatedScalars (Fin 3) K) ProjGenLinGroup.mk hN0
        (Sec4.pglHomP hK hq (Yh ⊔ Bh) hact a) :=
    ⟨(QuotientGroup.lift (StatedScalars (Fin 3) K) ProjGenLinGroup.mk hN0).comp
      (Sec4.pglHomP hK hq (Yh ⊔ Bh) hact), fun a => rfl⟩
  have hψ : ∀ (a : (Yh ⊔ Bh : Subgroup P)) {z : GL (Fin 3) K},
      Sec4.IsPGLAtP e (a : P) z → ψ a = ProjGenLinGroup.mk z := by
    intro a z hz
    rw [hψdef, Sec4.pglHomP_apply a hz]
    rfl
  obtain ⟨Good, hGood⟩ : ∃ G : Subgroup P, ∀ β : P,
      β ∈ G ↔ ∃ hβ : β ∈ Yh ⊔ Bh, ψ ⟨β, hβ⟩ ∈ T :=
    ⟨{ carrier := {β | ∃ hβ : β ∈ Yh ⊔ Bh, ψ ⟨β, hβ⟩ ∈ T}
       mul_mem' := fun {a b} ha hb => by
         obtain ⟨ha1, ha2⟩ := ha
         obtain ⟨hb1, hb2⟩ := hb
         show ∃ hβ : a * b ∈ Yh ⊔ Bh, ψ ⟨a * b, hβ⟩ ∈ T
         refine ⟨mul_mem ha1 hb1, ?_⟩
         have h : (⟨a * b, mul_mem ha1 hb1⟩ : (Yh ⊔ Bh : Subgroup P)) =
             ⟨a, ha1⟩ * ⟨b, hb1⟩ := rfl
         rw [h, map_mul]
         exact T.mul_mem ha2 hb2
       one_mem' := by
         show ∃ hβ : (1 : P) ∈ Yh ⊔ Bh, ψ ⟨1, hβ⟩ ∈ T
         refine ⟨one_mem _, ?_⟩
         have h : (⟨1, one_mem _⟩ : (Yh ⊔ Bh : Subgroup P)) = 1 := rfl
         rw [h, map_one]
         exact T.one_mem
       inv_mem' := fun {a} ha => by
         obtain ⟨ha1, ha2⟩ := ha
         show ∃ hβ : a⁻¹ ∈ Yh ⊔ Bh, ψ ⟨a⁻¹, hβ⟩ ∈ T
         refine ⟨inv_mem ha1, ?_⟩
         have h : (⟨a⁻¹, inv_mem ha1⟩ : (Yh ⊔ Bh : Subgroup P)) =
             (⟨a, ha1⟩ : (Yh ⊔ Bh : Subgroup P))⁻¹ := rfl
         rw [h, map_inv]
         exact T.inv_mem ha2 }, fun β => Iff.rfl⟩
  have hGmem : ∀ (β : P) (hβ : β ∈ Yh ⊔ Bh), ψ ⟨β, hβ⟩ ∈ T → β ∈ Good :=
    fun β hβ h => (hGood β).mpr ⟨hβ, h⟩
  have hXG : xh ∈ Good := hGmem xh (Subgroup.mem_sup_right hxBh) (by
    rw [hψ ⟨xh, Subgroup.mem_sup_right hxBh⟩ (Sec4.isPGLAtP_of_mem_centralizer e hxC),
      ProjGenLinGroup.mk_one]
    exact T.one_mem)
  have hBG : bh ∈ Good := hGmem bh (Subgroup.mem_sup_right hbBh) (by
    rw [hψ ⟨bh, Subgroup.mem_sup_right hbBh⟩ hy]
    exact hTy)
  have hCG : ch ∈ Good := by
    obtain ⟨yc, hyc⟩ := hact ch (Subgroup.mem_sup_right hchBh)
    refine hGmem ch (Subgroup.mem_sup_right hchBh) ?_
    rw [hψ ⟨ch, Subgroup.mem_sup_right hchBh⟩ hyc,
      ← Sec4.coe_e_eq_mk_of_isPGLAtP hK hq hD.cY hyc]
    exact hTm
  have hBGood : Bh ≤ Good := by
    rw [hD.gen]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hXG) (Subgroup.zpowers_le.mpr hBG))
      (Subgroup.zpowers_le.mpr hCG)
  have hpull : ∀ (x : P) (hx : x ∈ Yh),
      ((e ⟨x, hx⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ∈
        Subgroup.zpowers m₀ → x ∈ Subgroup.zpowers ch := by
    intro x hx hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : e ((⟨ch, hD.cY⟩ : ↥Yh) ^ k) = e ⟨x, hx⟩ := by
      apply Subtype.ext
      rw [map_zpow, Subgroup.coe_zpow]
      exact hk
    have h2 : (⟨ch, hD.cY⟩ : ↥Yh) ^ k = ⟨x, hx⟩ := e.injective h1
    have h3 : ch ^ k = x := by
      have h4 := congrArg Subtype.val h2
      simpa using h4
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, h3⟩
  have hcomm' : ∀ x ∈ liftSub e F, ∀ z ∈ liftSub e F, x * z = z * x := by
    intro x hx z hz
    obtain ⟨hxY, hxF⟩ := (mem_liftSub e F).mp hx
    obtain ⟨hzY, hzF⟩ := (mem_liftSub e F).mp hz
    have h1 : e (⟨x, hxY⟩ * ⟨z, hzY⟩) = e (⟨z, hzY⟩ * ⟨x, hxY⟩) := by
      rw [map_mul, map_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm _ hxF _ hzF
    exact congrArg Subtype.val (e.injective h1)
  have hexp : ∀ x ∈ liftSub e F, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨hxY, hxF⟩ := (mem_liftSub e F).mp hx
    have h1 : e ((⟨x, hxY⟩ : ↥Yh) ^ 3) = e 1 := by
      rw [map_pow, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hFab.2 _ hxF
    have h2 : (⟨x, hxY⟩ : ↥Yh) ^ 3 = 1 := e.injective h1
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hab : CFSG.Assembly.IsElemAbelian 3 (liftSub e F) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm' a a.2 b b.2)⟩⟩, fun x hx => hexp x hx⟩
  have hcard : Nat.card (liftSub e F) = 9 := by
    unfold liftSub
    rw [Subgroup.card_map_of_injective Yh.subtype_injective,
      Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFL).toEquiv, hFcard]
  refine ⟨?_, hab, hcard, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact ((mem_liftSub e F).mp hg).1
  · exact (mem_liftSub e F).mpr ⟨hD.cY, hm0F⟩
  ·
    intro β hβ
    obtain ⟨yβ, hyβ⟩ := hact β (Subgroup.mem_sup_right hβ)
    have hmkβ : ProjGenLinGroup.mk yβ ∈ T := by
      obtain ⟨hβS, hψβ⟩ := (hGood β).mp (hBGood hβ)
      rw [hψ ⟨β, hβS⟩ hyβ] at hψβ
      exact hψβ
    have hmkN' := hTN hmkβ
    apply mem_normalizer_of_forall_mem (liftSub e F)
    intro n hn
    obtain ⟨hnY, hnF⟩ := (mem_liftSub e F).mp hn
    rw [mem_liftSub]
    refine ⟨hconj β n hnY, ?_⟩
    rw [Hering129KH3.conj_compat e hyβ hnY]
    exact (Subgroup.mem_normalizer_iff.mp hmkN' _).mp hnF
  ·
    apply le_antisymm
    · intro β hβ
      obtain ⟨hβF, hβB⟩ := Subgroup.mem_inf.mp hβ
      obtain ⟨hβY, hβm⟩ := (mem_liftSub e F).mp hβF
      obtain ⟨yβ, hyβ⟩ := hact β (Subgroup.mem_sup_right hβB)
      obtain ⟨_, hψβ⟩ := (hGood β).mp (hBGood hβB)
      have hmkβ : ψ ⟨β, Subgroup.mem_sup_right hβB⟩ = ProjGenLinGroup.mk yβ := hψ _ hyβ
      have heβ : ((e ⟨β, hβY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
          ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk yβ :=
        Sec4.coe_e_eq_mk_of_isPGLAtP hK hq hβY hyβ
      have hmem : ((e ⟨β, hβY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
          ProjGenLinGroup (Fin 3) K) ∈ F ⊓ T := by
        refine Subgroup.mem_inf.mpr ⟨hβm, ?_⟩
        rw [heβ, ← hmkβ]
        exact hψβ
      rw [hFint] at hmem
      exact hpull β hβY hmem
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨(mem_liftSub e F).mpr ⟨hD.cY, hm0F⟩, hchBh⟩
  ·
    intro g hg
    obtain ⟨hgY, hgF⟩ := (mem_liftSub e F).mp hg
    have hA : bh * g * bh⁻¹ ∈ Yh := hconj bh g hgY
    have hxY : bh * g * bh⁻¹ * g⁻¹ ∈ Yh := mul_mem hA (inv_mem hgY)
    refine hpull _ hxY ?_
    have h1 : (⟨bh * g * bh⁻¹ * g⁻¹, hxY⟩ : ↥Yh) =
        (⟨bh * g * bh⁻¹, hA⟩ : ↥Yh) * (⟨g, hgY⟩ : ↥Yh)⁻¹ := rfl
    have hx_eq : ((e ⟨bh * g * bh⁻¹ * g⁻¹, hxY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * ((e ⟨g, hgY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) :
          ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹ *
          ((e ⟨g, hgY⟩ : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)⁻¹ := by
      rw [h1, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        Hering129KH3.conj_compat e hy hgY]
    rw [hx_eq]
    exact hFcomm _ hgF
  ·
    obtain ⟨f₀, hf₀F, hf₀⟩ := hFnt
    have hfL : f₀ ∈ projImage (Sec4.slPi π 3 (p ^ f) K) := hFL hf₀F
    obtain ⟨a, ha⟩ : ∃ a : ↥Yh, e a = ⟨f₀, hfL⟩ :=
      ⟨e.symm ⟨f₀, hfL⟩, e.apply_symm_apply _⟩
    have hae : ((e a : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) = f₀ := by
      rw [ha]
    have haF : (a : P) ∈ liftSub e F := (mem_liftSub e F).mpr ⟨a.2, by
      show ((e a : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) ∈ F
      rw [hae]
      exact hf₀F⟩
    refine ⟨(a : P), haF, fun h => hf₀ ?_⟩
    have h2 : bh * (a : P) * bh⁻¹ = (a : P) := mul_inv_eq_one.mp h
    have h3 : (⟨bh * (a : P) * bh⁻¹, hconj bh a a.2⟩ : ↥Yh) = a := Subtype.ext h2
    have hc : ((e a : projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * ((e a : projImage (Sec4.slPi π 3 (p ^ f) K)) :
          ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹ := by
      have hc0 := Hering129KH3.conj_compat e hy a.2
      rw [h3] at hc0
      exact hc0
    rw [hae] at hc
    rw [← hc, mul_inv_cancel]

end Hering129KH4

end CFSG.RankThree.PartTwo.Sec12
