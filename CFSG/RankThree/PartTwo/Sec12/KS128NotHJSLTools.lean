module

import CFSG.RankThree.PartTwo.Sec12.Item127
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

theorem map_conj_mem_thetaComponentsAt {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {a : G} {K : Subgroup G} (hK : K ∈ thetaComponentsAt p a) (g : G) :
    K.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt p (g * a * g⁻¹) := by
  have hmem : ∀ x : G, x ∈ Subgroup.centralizer ({a} : Set G) →
      g * x * g⁻¹ ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hx]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  have hmem' : ∀ x : G, x ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set G) →
      g⁻¹ * x * g ∈ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * x) * g := by rw [hx]
      _ = a * (g⁻¹ * x * g) := by group
  let σ : Subgroup.centralizer ({a} : Set G) ≃*
      Subgroup.centralizer ({g * a * g⁻¹} : Set G) :=
    { toFun := fun x => ⟨g * x * g⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨K₀, hK₀, rfl⟩ := hK
  refine ⟨K₀.map σ.toMonoidHom, map_mulEquiv_mem_thetaComponents hp σ hK₀, ?_⟩
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨σ w, ⟨w, hw, rfl⟩, rfl⟩

theorem zpow_eq_one_or_eq_or_eq_inv {G : Type*} [Group G] {a : G} (ha3 : a ^ 3 = 1) (i : ℤ) :
    a ^ i = 1 ∨ a ^ i = a ∨ a ^ i = a⁻¹ := by
  have h3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
  obtain ⟨q, r, hr0, hr3, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 3 ∧ i = 3 * q + r :=
    ⟨i / 3, i % 3, by omega, by omega, by omega⟩
  rw [zpow_add, zpow_mul, h3, one_zpow, one_mul]
  interval_cases r
  · left
    exact zpow_zero a
  · right; left
    exact zpow_one a
  · right; right
    rw [show (2 : ℤ) = 3 + -1 by norm_num, zpow_add, h3, one_mul, zpow_neg_one]

theorem exists_conj_eq_of_moves {G : Type} [Group G] {E F : Subgroup G} {a c y : G}
    (hEc : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x) (haE : a ∈ E) (ha3 : a ^ 3 = 1) (hFE : F ≤ E)
    (hcF : c ∈ F) (hc1 : c ≠ 1)
    (hT : ∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      ∃ m ∈ Subgroup.normalizer (E : Set G), m * a = a * m ∧ m * u * m⁻¹ = v)
    (hyE : y ∈ Subgroup.normalizer (E : Set G)) (hyc : y * c = c * y)
    (hya : y * a * y⁻¹ * a⁻¹ ∈ Subgroup.zpowers c) (hya1 : y * a * y⁻¹ ≠ a)
    (hyF : ∀ f ∈ F, f ∉ Subgroup.zpowers c →
      y * f * y⁻¹ * f⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c ∧
        y * f * y⁻¹ * f⁻¹ ∉ Subgroup.zpowers c)
    {f₀ : G} (hf₀F : f₀ ∈ F) (hf₀c : f₀ ∉ Subgroup.zpowers c) :
    ∃ h ∈ Subgroup.normalizer (E : Set G), h * c * h⁻¹ = a := by
  have hcE : c ∈ E := hFE hcF
  have hac : a * c = c * a := hEc a haE c hcE
  have hyck : ∀ k : ℤ, y * c ^ k * y⁻¹ = c ^ k := fun k => by
    rw [← conj_zpow, show y * c * y⁻¹ = c by rw [hyc]; group]
  obtain ⟨f₁, hf₁F, hf₁c, k, hf₁⟩ : ∃ f₁ ∈ F, f₁ ∉ Subgroup.zpowers c ∧ ∃ k : ℤ,
      y * f₁ * y⁻¹ = a * c ^ k * f₁ := by
    obtain ⟨hg1, hg2⟩ := hyF f₀ hf₀F hf₀c
    obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup hac hg1
    have hyf : y * f₀ * y⁻¹ = a ^ i * c ^ j * f₀ := by
      rw [← hij]
      group
    rcases zpow_eq_one_or_eq_or_eq_inv ha3 i with h0 | h1 | h2
    · exfalso
      apply hg2
      rw [hij, h0, one_mul]
      exact Subgroup.zpow_mem_zpowers c j
    · exact ⟨f₀, hf₀F, hf₀c, j, by rw [hyf, h1]⟩
    · refine ⟨f₀⁻¹, F.inv_mem hf₀F, fun hm => hf₀c ?_, -j, ?_⟩
      · simpa using (Subgroup.zpowers c).inv_mem hm
      · have hf₀E : f₀ ∈ E := hFE hf₀F
        have hcjE : c ^ (-j) ∈ E := E.zpow_mem hcE _
        calc y * f₀⁻¹ * y⁻¹ = (y * f₀ * y⁻¹)⁻¹ := by group
          _ = f₀⁻¹ * c ^ (-j) * a := by rw [hyf, h2]; group
          _ = a * (f₀⁻¹ * c ^ (-j)) := by
              rw [hEc _ (E.mul_mem (E.inv_mem hf₀E) hcjE) a haE]
          _ = a * c ^ (-j) * f₀⁻¹ := by
              rw [hEc _ (E.inv_mem hf₀E) _ hcjE, mul_assoc]
  have hf₁1 : f₁ ≠ 1 := fun h1 => hf₁c (h1 ▸ Subgroup.one_mem _)
  have hf₂F : c ^ k * f₁ ∈ F := F.mul_mem (F.zpow_mem hcF k) hf₁F
  have hf₂1 : c ^ k * f₁ ≠ 1 := by
    intro h1
    apply hf₁c
    rw [eq_inv_of_mul_eq_one_right h1, ← zpow_neg]
    exact Subgroup.zpow_mem_zpowers c _
  obtain ⟨ε, hε⟩ := Subgroup.mem_zpowers_iff.mp hya
  have hyae : y * a * y⁻¹ = c ^ ε * a := by rw [hε]; group
  have ht₀F : c ^ (-ε) ∈ F := F.zpow_mem hcF _
  have ht₀1 : c ^ (-ε) ≠ 1 := by
    intro h1
    apply hya1
    rw [zpow_neg, inv_eq_one] at h1
    rw [hyae, h1, one_mul]
  obtain ⟨m₁, hm₁E, -, hm₁⟩ := hT c hcF hc1 f₁ hf₁F hf₁1
  obtain ⟨m₂, hm₂E, hm₂a, hm₂⟩ := hT _ hf₂F hf₂1 _ ht₀F ht₀1
  refine ⟨y * m₂ * y * m₁, mul_mem (mul_mem (mul_mem hyE hm₂E) hyE) hm₁E, ?_⟩
  have hm₂a' : m₂ * a * m₂⁻¹ = a := by rw [hm₂a]; group
  calc y * m₂ * y * m₁ * c * (y * m₂ * y * m₁)⁻¹
      = y * (m₂ * (y * (m₁ * c * m₁⁻¹) * y⁻¹) * m₂⁻¹) * y⁻¹ := by group
    _ = y * (m₂ * (a * c ^ k * f₁) * m₂⁻¹) * y⁻¹ := by rw [hm₁, hf₁]
    _ = y * ((m₂ * a * m₂⁻¹) * (m₂ * (c ^ k * f₁) * m₂⁻¹)) * y⁻¹ := by group
    _ = y * (a * c ^ (-ε)) * y⁻¹ := by rw [hm₂a', hm₂]
    _ = (y * a * y⁻¹) * (y * c ^ (-ε) * y⁻¹) := by group
    _ = c ^ ε * a * c ^ (-ε) := by rw [hyae, hyck]
    _ = a := by
        rw [mul_assoc, (Commute.zpow_right hac (-ε)).eq, ← mul_assoc, ← zpow_add,
          add_neg_cancel, zpow_zero, one_mul]

theorem le_thetaQuotCentralizer_of_conj_eq {G : Type} [Group G] [Finite G]
    {E F K L : Subgroup G} {a c h : G} (hK : K ∈ thetaComponentsAt 3 a) (haK : a ∉ K)
    (hFK : F ≤ K) (hFE : F ≤ E) (hE : ∀ e ∈ E, ∃ k : ℤ, ∃ f ∈ F, e = a ^ k * f)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hL : L ∈ thetaComponentsAt 3 c) (hcL : c ∈ L)
    (hcC : c ∈ Sec4.thetaQuotCentralizer L)
    (hhE : h ∈ Subgroup.normalizer (E : Set G)) (hhc : h * c * h⁻¹ = a) :
    E ≤ Sec4.thetaQuotCentralizer L := by
  set K' := K.map (MulAut.conj h⁻¹).toMonoidHom with hK'def
  have hac : h⁻¹ * a * h⁻¹⁻¹ = c := by rw [← hhc]; group
  have hK' : K' ∈ thetaComponentsAt 3 c := by
    have := map_conj_mem_thetaComponentsAt Nat.prime_three hK h⁻¹
    rwa [hac] at this
  have hcK' : c ∉ K' := by
    rintro ⟨k, hk, hkc⟩
    apply haK
    have : k = a := by
      rw [← hhc, ← hkc]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact this ▸ hk
  have hne : K' ≠ L := fun h1 => hcK' (h1 ▸ hcL)
  intro e he
  have hhe : h * e * h⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hhE e).mp he
  obtain ⟨k, f, hf, hkf⟩ := hE _ hhe
  have hpow : (h⁻¹ * a * h) ^ k = h⁻¹ * a ^ k * h := by
    simpa only [inv_inv] using (conj_zpow (i := k) (a := h⁻¹) (b := a))
  have he' : e = (h⁻¹ * a * h) ^ k * (h⁻¹ * f * h) := by
    rw [hpow, show h⁻¹ * a ^ k * h * (h⁻¹ * f * h) = h⁻¹ * (a ^ k * f) * h by group,
      ← hkf]
    group
  have hf' : h⁻¹ * f * h ∈ Sec4.thetaQuotCentralizer L := by
    have hfK' : h⁻¹ * f * h ∈ K' := ⟨f, hFK hf, by simp⟩
    have hfE : h⁻¹ * f * h ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hhE) f).mp (hFE hf)
      simpa using this
    exact mem_thetaQuotCentralizer_of_ne hK' hL hne hfK' (hEN hfE)
  have hca : h⁻¹ * a * h = c := by rw [← hac]; group
  rw [he', hca]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hcC k) hf'

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_normalizer_of {L E W : Subgroup G} (hE : Late.IsE27 E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hWE : W ≤ E) (x : L)
    (hx : ∀ e (he : e ∈ E), thetaBarAct L ⟨e, hEN he⟩
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x) *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x)⁻¹ ∈
      (W.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) :
    ∃ y : L, QuotientGroup.mk' (aschbacherSolvableCore 3 L) y =
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) x ∧
      (y : G) ∈ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun u => ⟨1, Subtype.ext (by simpa using hE.1.2 u u.2)⟩
  set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hT
  have hET : E ≤ Subgroup.normalizer (T : Set G) := fun e he =>
    Subgroup.mem_normalizer_fintype fun n hn =>
      conj_mem_inSubgroup_theta (hEN he) hn
  have hdisj : T ⊓ E = ⊥ := by
    rw [inf_comm]
    exact inf_inSubgroup_theta_eq_bot hE3
  have hT3 : ¬ 3 ∣ Nat.card T := by
    rw [hT, show Nat.card (inSubgroup (aschbacherSolvableCore 3) L) =
      Nat.card (aschbacherSolvableCore 3 L) from
        Subgroup.card_map_of_injective L.subtype_injective]
    exact three_not_dvd_card_aschbacherSolvableCore
  have hfac : (Nat.card (T ⊔ E : Subgroup G)).factorization 3 = 3 := by
    rw [CentralCover.card_sup_eq_mul_of_le_normalizer hET hdisj, hE.2,
      show Nat.card T * 27 = 3 * (9 * Nat.card T) by ring]
    exact KFacts.factorization_three_mul_nine_mul hT3
  have hSylE : IsSylowOf 3 E (T ⊔ E) :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_sup_right (by rw [hE.2, hfac]; norm_num)
  have hxE : ∀ e ∈ E, (x : G) * e * (x : G)⁻¹ ∈ T ⊔ E := by
    intro e he
    have heN := hEN he
    have hw : (x : G) * e * (x : G)⁻¹ * e⁻¹ ∈ L := by
      have h1 : e * (x : G)⁻¹ * e⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp heN _).mp (L.inv_mem x.2)
      have e1 : (x : G) * e * (x : G)⁻¹ * e⁻¹ = x * (e * (x : G)⁻¹ * e⁻¹) := by group
      rw [e1]
      exact L.mul_mem x.2 h1
    have hwW : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (⟨_, hw⟩ : L) ∈
        (W.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
      have h3 : thetaBarAct L ⟨e, heN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x) =
          QuotientGroup.mk' (aschbacherSolvableCore 3 L) (L.normalizerMonoidHom ⟨e, heN⟩ x) :=
        thetaBarAct_mk _ _
      have h4 : (⟨_, hw⟩ : L) = x * (L.normalizerMonoidHom ⟨e, heN⟩ x)⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
        group
      rw [h4, map_mul, map_inv, ← h3]
      have h5 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) x *
          (thetaBarAct L ⟨e, heN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x))⁻¹ =
          (thetaBarAct L ⟨e, heN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x) *
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x)⁻¹)⁻¹ := by group
      rw [h5]
      exact Subgroup.inv_mem _ (hx e he)
    obtain ⟨w, hwL, hwe⟩ := hwW
    have hwθ : (w : G)⁻¹ * ((x : G) * e * (x : G)⁻¹ * e⁻¹) ∈ T := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hwe
      exact ⟨_, hwe, by simp⟩
    have e2 : (x : G) * e * (x : G)⁻¹ =
        (w : G) * ((w : G)⁻¹ * ((x : G) * e * (x : G)⁻¹ * e⁻¹)) * e := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_right (hWE (Subgroup.mem_subgroupOf.mp hwL)))
      (Subgroup.mem_sup_left hwθ)) (Subgroup.mem_sup_right he)
  set E' := E.map (MulAut.conj (x : G)).toMonoidHom with hE'
  have hE'X : E' ≤ T ⊔ E := by
    rintro _ ⟨e, he, rfl⟩
    exact hxE e he
  have hE'card : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective, hE.2]
  have hSylE' : IsSylowOf 3 E' (T ⊔ E) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hE'X (by rw [hE'card, hfac]; norm_num)
  obtain ⟨k, hk, hkE⟩ := hSylE.exists_mem_conj hSylE'
  have hk' : k ∈ ((T ⊔ E : Subgroup G) : Set G) := hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left T E hET] at hk'
  obtain ⟨n, hn, e', he', rfl⟩ := hk'
  obtain ⟨n₀, hn₀, rfl⟩ := hn
  refine ⟨n₀⁻¹ * x, ?_, ?_⟩
  · have h0 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) n₀ = 1 :=
      (QuotientGroup.eq_one_iff n₀).mpr hn₀
    rw [map_mul, map_inv, h0, inv_one, one_mul]
  · refine Subgroup.mem_normalizer_fintype fun e he => ?_
    have h1 := (hkE _).mp ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 : ((n₀⁻¹ * x : L) : G) * e * ((n₀⁻¹ * x : L) : G)⁻¹ =
        e' * ((L.subtype n₀ * e')⁻¹ * ((x : G) * e * (x : G)⁻¹) * (L.subtype n₀ * e')) *
          e'⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
      group
    rw [h2]
    exact E.mul_mem (E.mul_mem he' h1) (E.inv_mem he')

end CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL
