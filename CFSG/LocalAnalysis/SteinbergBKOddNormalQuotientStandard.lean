module

public import CFSG.LocalAnalysis.SteinbergBKOrderTwoCentralizerStandard
public import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.LocalAnalysis.SteinbergBK

open Subgroup

section OddNormalQuotient

variable {F : Type*} [Group F]

theorem simple_involution_centralizer_odd_normal_quotient_standardness [Finite F]
    {J : Subgroup F} [IsSimpleGroup J] (hJnab : ∃ x y : J, x * y ≠ y * x)
    (hE : ∃ E : Subgroup F, E ≤ J ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4)
    {a : F} (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set F))
    (hJn : (J.subgroupOf (centralizer ({a} : Set F))).Normal)
    (hsyl : ∃ S : Sylow 2 ↥(centralizer (J : Set F) ⊓ centralizer ({a} : Set F)),
      (S : Subgroup _).map (centralizer (J : Set F) ⊓ centralizer ({a} : Set F)).subtype =
        zpowers a)
    (R : Subgroup F) [R.Normal] (hR : Odd (Nat.card R)) :
    let θ : F →* F ⧸ R := QuotientGroup.mk' R
    Set.InjOn θ (J : Set F) ∧ (∀ Q : Subgroup F, IsPGroup 2 Q → Set.InjOn θ (Q : Set F)) ∧
      orderOf (θ a) = 2 ∧ IsSimpleGroup (J.map θ) ∧ (∃ x y : J.map θ, x * y ≠ y * x) ∧
      J.map θ ≤ centralizer ({θ a} : Set (F ⧸ R)) ∧
      ((J.map θ).subgroupOf (centralizer ({θ a} : Set (F ⧸ R)))).Normal ∧
      centralizer ({θ a} : Set (F ⧸ R)) = (centralizer ({a} : Set F)).map θ ∧
      centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) ⊓
          centralizer ({θ a} : Set (F ⧸ R)) =
        (centralizer (J : Set F) ⊓ centralizer ({a} : Set F)).map θ ∧
      CFSG.Assembly.ComponentType.IsStandardSubgroup (J.map θ) ∧
      (∃ S : Sylow 2 (centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))),
        (S : Subgroup _).map
          (centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))).subtype = zpowers (θ a)) ∧
      ∀ b ∈ centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)), orderOf b = 2 →
        ∃ h ∈ centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)), h⁻¹ * θ a * h = b := by
  intro θ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := centralizer (J : Set F) ⊓ centralizer ({a} : Set F) with hB
  obtain ⟨S, hS⟩ := hsyl
  have hθeq : ∀ x y : F, θ x = θ y → x⁻¹ * y ∈ R := fun x y h => QuotientGroup.eq.mp h
  have hinj2 : ∀ Q : Subgroup F, IsPGroup 2 Q → Set.InjOn θ (Q : Set F) := by
    intro Q hQ x hx y hy hxy
    have h1 : x⁻¹ * y ∈ R := hθeq x y hxy
    have h2 : x⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem hx) hy
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ ⟨_, h2⟩
    rw [Subgroup.orderOf_mk] at hk
    have h3 : orderOf (x⁻¹ * y) ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨_, h1⟩ : R)
      rwa [Subgroup.orderOf_mk] at this
    rw [hk] at h3
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans h3))
    rw [hk0, pow_zero] at hk
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp hk)
  have hJR : ∀ x ∈ J, x ∈ R → x = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf J) with h | h
    · intro x hxJ hxR
      have : (⟨x, hxJ⟩ : J) ∈ R.subgroupOf J := hxR
      rw [h] at this
      exact congrArg Subtype.val ((Subgroup.mem_bot).mp this)
    · exfalso
      obtain ⟨E, hEJ, -, hE4⟩ := hE
      have hER : E ≤ R := fun x hx => by
        have : (⟨x, hEJ hx⟩ : J) ∈ R.subgroupOf J := h ▸ mem_top _
        exact this
      have h4 := Subgroup.card_dvd_of_le hER
      rw [hE4] at h4
      exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4))
  have hinjJ : Set.InjOn θ (J : Set F) := by
    intro x hx y hy hxy
    exact inv_mul_eq_one.mp (hJR _ (J.mul_mem (J.inv_mem hx) hy) (hθeq x y hxy))
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hza : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hθa : orderOf (θ a) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ha2, map_one]
    · intro h
      apply ha1
      exact hinj2 (zpowers a) hza (mem_zpowers a) (one_mem _) (by rw [h, map_one])
  let fJ : J →* J.map θ := θ.subgroupMap J
  have hfJsurj : Function.Surjective fJ := θ.subgroupMap_surjective J
  have hfJinj : Function.Injective fJ := fun x y h =>
    Subtype.ext (hinjJ x.2 y.2 (congrArg Subtype.val h))
  have : Nontrivial (J.map θ) := hfJinj.nontrivial
  have hJbsimple : IsSimpleGroup (J.map θ) := IsSimpleGroup.isSimpleGroup_of_surjective fJ hfJsurj
  have hJbnab : ∃ x y : J.map θ, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hJnab
    exact ⟨fJ x, fJ y, fun h => hxy (hfJinj (by rw [map_mul, map_mul, h]))⟩
  have hσ : Function.Involutive (MulAut.conj a) := fun x => by
    simp only [MulAut.conj_apply]
    calc a * (a * x * a⁻¹) * a⁻¹ = a ^ 2 * x * (a ^ 2)⁻¹ := by rw [pow_two]; group
      _ = x := by rw [ha2, one_mul, inv_one, mul_one]
  have hCa : centralizer ({θ a} : Set (F ⧸ R)) = (centralizer ({a} : Set F)).map θ := by
    apply le_antisymm
    · intro q hq
      have hfix : MulAut.conj (θ a) q = q := by
        rw [MulAut.conj_apply]
        rw [mem_centralizer_singleton_iff] at hq
        rw [← hq, mul_inv_cancel_right]
      obtain ⟨c, hc, hcfix⟩ :=
        CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel (MulAut.conj a)
          (MulAut.conj (θ a)) hσ θ (QuotientGroup.mk'_surjective R)
          (by rw [QuotientGroup.ker_mk']; exact hR)
          (fun x => by simp only [MulAut.conj_apply, map_mul, map_inv]) q hfix
      refine ⟨c, ?_, hc⟩
      show c ∈ centralizer ({a} : Set F)
      rw [mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply] at hcfix
      exact (mul_inv_eq_iff_eq_mul.mp hcfix).symm
    · rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hc
      rw [mem_centralizer_singleton_iff, ← map_mul, hc, map_mul]
  have hJbC : J.map θ ≤ centralizer ({θ a} : Set (F ⧸ R)) := by
    rw [hCa]
    exact map_mono hJa
  have hconjJ : ∀ c ∈ centralizer ({a} : Set F), ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
    intro c hc j hj
    have := hJn.conj_mem ⟨j, hJa hj⟩ (mem_subgroupOf.mpr hj) ⟨c, hc⟩
    exact mem_subgroupOf.mp this
  have hJbn : ((J.map θ).subgroupOf (centralizer ({θ a} : Set (F ⧸ R)))).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨j, hj, hjn⟩ := hn
    have hg : (g : F ⧸ R) ∈ (centralizer ({a} : Set F)).map θ := hCa ▸ g.2
    obtain ⟨c, hc, hcg⟩ := hg
    refine ⟨c * j * c⁻¹, hconjJ c hc j hj, ?_⟩
    change θ (c * j * c⁻¹) = (g : F ⧸ R) * (n : F ⧸ R) * (g : F ⧸ R)⁻¹
    rw [map_mul, map_mul, map_inv, hcg, hjn]
  have hBb : centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) ⊓
      centralizer ({θ a} : Set (F ⧸ R)) = B.map θ := by
    apply le_antisymm
    · rintro q ⟨hqJ, hqa⟩
      have hq : q ∈ (centralizer ({a} : Set F)).map θ := hCa ▸ hqa
      obtain ⟨c, hc, rfl⟩ := hq
      refine ⟨c, ⟨?_, hc⟩, rfl⟩
      show c ∈ centralizer (J : Set F)
      rw [mem_centralizer_iff]
      intro j hj
      have hcj := hconjJ c hc j hj
      have h1 : θ (c * j * c⁻¹) = θ j := by
        have h2 := mem_centralizer_iff.mp hqJ (θ j) ⟨j, hj, rfl⟩
        rw [map_mul, map_mul, map_inv, ← h2, mul_inv_cancel_right]
      have h3 : c * j * c⁻¹ = j := hinjJ hcj hj h1
      calc j * c = c * j * c⁻¹ * c := by rw [h3]
        _ = c * j := by group
    · rintro _ ⟨c, ⟨hcJ, hca⟩, rfl⟩
      have hcJ' : c ∈ centralizer (J : Set F) := hcJ
      have hca' : c ∈ centralizer ({a} : Set F) := hca
      refine ⟨?_, ?_⟩
      · show θ c ∈ centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R))
        rw [mem_centralizer_iff]
        rintro _ ⟨j, hj, rfl⟩
        rw [← map_mul, mem_centralizer_iff.mp hcJ' j hj, map_mul]
      · show θ c ∈ centralizer ({θ a} : Set (F ⧸ R))
        rw [mem_centralizer_singleton_iff] at hca' ⊢
        rw [← map_mul, hca', map_mul]
  have hsylb : ∃ Sb : Sylow 2 ↥(centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) ⊓
      centralizer ({θ a} : Set (F ⧸ R))),
      (Sb : Subgroup _).map (centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) ⊓
        centralizer ({θ a} : Set (F ⧸ R))).subtype = zpowers (θ a) := by
    rw [hBb]
    let f : B →* B.map θ := θ.subgroupMap B
    have hf : Function.Surjective f := θ.subgroupMap_surjective B
    refine ⟨S.mapSurjective hf, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : (B.map θ).subtype.comp f = θ.comp B.subtype := MonoidHom.ext fun _ => rfl
    rw [hcomp, ← Subgroup.map_map, hS, MonoidHom.map_zpowers]
  have hJbq : CFSG.Assembly.IsQuasisimple (J.map θ) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hJbnab)
  have hEb : ∃ Eb : Subgroup (F ⧸ R), Eb ≤ J.map θ ∧ CFSG.Assembly.IsElemAbelian 2 Eb ∧
      Nat.card Eb = 4 := by
    obtain ⟨E, hEJ, hEab, hE4⟩ := hE
    refine ⟨E.map θ, map_mono hEJ, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
    · rintro ⟨_, e₁, he₁, rfl⟩ ⟨_, e₂, he₂, rfl⟩
      apply Subtype.ext
      change θ e₁ * θ e₂ = θ e₂ * θ e₁
      have h := congrArg Subtype.val (hEab.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
      change e₁ * e₂ = e₂ * e₁ at h
      rw [← map_mul, h, map_mul]
    · rintro _ ⟨e, he, rfl⟩
      rw [← map_pow, hEab.2 e he, map_one]
    · rw [← hE4]
      have hinj : Function.Injective (θ.subgroupMap E) := fun x y h =>
        Subtype.ext (hinjJ (hEJ x.2) (hEJ y.2) (congrArg Subtype.val h))
      exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, θ.subgroupMap_surjective E⟩)).symm
  have haB : a ∈ B := by
    have : a ∈ (S : Subgroup B).map B.subtype := hS ▸ mem_zpowers a
    exact map_subtype_le _ this
  have haJb : θ a ∈ centralizer ((J.map θ : Subgroup (F ⧸ R)) : Set (F ⧸ R)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, mem_centralizer_iff.mp haB.1 j hj, map_mul]
  have hcompb : CFSG.Assembly.IsComponentOf (J.map θ) (centralizer ({θ a} : Set (F ⧸ R))) :=
    ⟨hJbC, CFSG.Assembly.IsSubnormal.step hJbC hJbn (CFSG.Assembly.IsSubnormal.refl _), hJbq⟩
  obtain ⟨hSylb, hconjb, hstd⟩ :=
    quasisimple_involution_centralizer_order_two_standard hJbq hEb haJb hθa hcompb hsylb
  exact ⟨hinjJ, hinj2, hθa, hJbsimple, hJbnab, hJbC, hJbn, hCa, hBb, hstd, hSylb, hconjb⟩

end OddNormalQuotient

end CFSG.LocalAnalysis.SteinbergBK
