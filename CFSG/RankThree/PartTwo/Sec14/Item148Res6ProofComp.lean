module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofComp
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofDefs
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofE9
import CFSG.RankThree.PartTwo.Sec13.Item131bProofF

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Item148Res6

open CFSG CFSG.RankThree.PartTwo.Sec14.Res2LBal CFSG.RankThree.PartTwo.Sec14.Item148Res5
open CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof (mem_zpowers_of_mem_zpowers isPGroup_of_pow_three)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_conj_inf_centralizer_eq_bot {J : Subgroup X}
    (hZJ : J ⊓ Subgroup.centralizer (J : Set X) = ⊥) (x : X) :
    J.map (MulAut.conj x).toMonoidHom ⊓
      Subgroup.centralizer ((J.map (MulAut.conj x).toMonoidHom : Subgroup X) : Set X) = ⊥ := by
  rw [← map_conj_centralizer, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective, hZJ,
    Subgroup.map_bot]

@[expose] noncomputable def diagHom {J₁ : Subgroup X} {a : X} (hc₁ : IsComponent J₁)
    (h01 : J₁ ≠ J₁.map (MulAut.conj (a ^ 1)).toMonoidHom)
    (h02 : J₁ ≠ J₁.map (MulAut.conj (a ^ 2)).toMonoidHom)
    (h12 : J₁.map (MulAut.conj (a ^ 1)).toMonoidHom ≠ J₁.map (MulAut.conj (a ^ 2)).toMonoidHom) :
    ↥J₁ →* X where
  toFun u := (u : X) * (a ^ 1 * (u : X) * (a ^ 1)⁻¹) * (a ^ 2 * (u : X) * (a ^ 2)⁻¹)
  map_one' := by simp
  map_mul' u u' := by
    have hc₂ := isComponent_conj hc₁ (a ^ 1)
    have hc₃ := isComponent_conj hc₁ (a ^ 2)
    exact diag_mul (commute_of_ne hc₁ hc₂ h01 u'.2 (conj_mem_map u.2 _))
      (commute_of_ne hc₁ hc₃ h02 u'.2 (conj_mem_map u.2 _))
      (commute_of_ne hc₂ hc₃ h12 (conj_mem_map u'.2 _) (conj_mem_map u.2 _))

theorem diagHom_apply {J₁ : Subgroup X} {a : X} (hc₁ : IsComponent J₁)
    (h01 : J₁ ≠ J₁.map (MulAut.conj (a ^ 1)).toMonoidHom)
    (h02 : J₁ ≠ J₁.map (MulAut.conj (a ^ 2)).toMonoidHom)
    (h12 : J₁.map (MulAut.conj (a ^ 1)).toMonoidHom ≠ J₁.map (MulAut.conj (a ^ 2)).toMonoidHom)
    (u : ↥J₁) :
    diagHom hc₁ h01 h02 h12 u =
      (u : X) * (a ^ 1 * (u : X) * (a ^ 1)⁻¹) * (a ^ 2 * (u : X) * (a ^ 2)⁻¹) :=
  rfl

theorem diagHom_injective {J₁ : Subgroup X} {a : X} (hc₁ : IsComponent J₁)
    (h01 : J₁ ≠ J₁.map (MulAut.conj (a ^ 1)).toMonoidHom)
    (h02 : J₁ ≠ J₁.map (MulAut.conj (a ^ 2)).toMonoidHom)
    (h12 : J₁.map (MulAut.conj (a ^ 1)).toMonoidHom ≠ J₁.map (MulAut.conj (a ^ 2)).toMonoidHom)
    (hZ : J₁ ⊓ Subgroup.centralizer (J₁ : Set X) = ⊥) :
    Function.Injective (diagHom hc₁ h01 h02 h12) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  rw [diagHom_apply] at hu
  have hc₂ := isComponent_conj hc₁ (a ^ 1)
  have hc₃ := isComponent_conj hc₁ (a ^ 2)
  have h1 : a ^ 1 * (u : X) * (a ^ 1)⁻¹ ∈ Subgroup.centralizer (J₁ : Set X) :=
    mem_centralizer_of_mem_of_ne hc₁ hc₂ h01 (conj_mem_map u.2 _)
  have h2 : a ^ 2 * (u : X) * (a ^ 2)⁻¹ ∈ Subgroup.centralizer (J₁ : Set X) :=
    mem_centralizer_of_mem_of_ne hc₁ hc₃ h02 (conj_mem_map u.2 _)
  have hu' : (u : X) = ((a ^ 1 * (u : X) * (a ^ 1)⁻¹) * (a ^ 2 * (u : X) * (a ^ 2)⁻¹))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
    exact hu
  have hmem : (u : X) ∈ J₁ ⊓ Subgroup.centralizer (J₁ : Set X) := by
    refine ⟨u.2, ?_⟩
    rw [hu']
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ h1 h2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

section Normalize

variable {J A : Subgroup X} {e b : X}

theorem conj_mem_normalizer_of_component_inf (hJ : IsComponent J)
    (hZJ : J ⊓ Subgroup.centralizer (J : Set X) = ⊥) (hE9 : Sec8.E9Closed ↥J)
    (h3 : 3 ∣ Nat.card J) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (h27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (J : Set X))
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (A : Set X) → w ^ 3 = 1 → w ∈ A)
    (he : e ∈ A) (hAJ : A ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.zpowers e)
    (hbA : b ∈ A) (hbJ : b ∈ J) (hb1 : b ≠ 1) (x : X) {a : X} (ha : a ∈ A) :
    x⁻¹ * a * x ∈ Subgroup.normalizer (J : Set X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hn
  set J₁ := J.map (MulAut.conj x).toMonoidHom with hJ₁def
  have hmove : a ∉ Subgroup.normalizer (J₁ : Set X) := fun h =>
    hn (mem_normalizer_map_conj_iff.mp h)
  have hc₁ : IsComponent J₁ := isComponent_conj hJ x
  have hZ₁ : J₁ ⊓ Subgroup.centralizer (J₁ : Set X) = ⊥ := map_conj_inf_centralizer_eq_bot hZJ x
  have h3₁ : 3 ∣ Nat.card J₁ := by rw [hJ₁def, card_map_conj]; exact h3
  have hne : ∀ g ∈ A, J₁.map (MulAut.conj g).toMonoidHom ≠ J := by
    intro g hg h
    apply hmove
    have h1 := congrArg (fun L : Subgroup X => L.map (MulAut.conj g⁻¹).toMonoidHom) h
    simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h1
    have h2 : J.map (MulAut.conj g⁻¹).toMonoidHom = J :=
      map_conj_eq_iff.mpr (hAN (A.inv_mem hg))
    rw [h1, h2]
    exact hAN ha
  have hJ₁J : J₁ ≠ J := by
    have := hne 1 A.one_mem
    rwa [map_conj_one] at this
  set D : Subgroup X := ⨆ (g : X) (_ : g ∈ A), J₁.map (MulAut.conj g).toMonoidHom with hD
  have hJ₁D : J₁ ≤ D := by
    have h := le_iSup₂_of_le (f := fun (g : X) (_ : g ∈ A) =>
      J₁.map (MulAut.conj g).toMonoidHom) 1 A.one_mem le_rfl
    rwa [map_conj_one] at h
  have hDC : D ≤ Subgroup.centralizer (J : Set X) :=
    iSup₂_le fun g hg _ hy => mem_centralizer_of_mem_of_ne hJ (isComponent_conj hc₁ g)
      (hne g hg).symm hy
  have hDJ₁ : D ≤ J₁ ⊔ Subgroup.centralizer (J₁ : Set X) := by
    refine iSup₂_le fun g _ => ?_
    by_cases hg : J₁.map (MulAut.conj g).toMonoidHom = J₁
    · rw [hg]
      exact le_sup_left
    · exact le_sup_of_le_right fun y hy =>
        mem_centralizer_of_mem_of_ne hc₁ (isComponent_conj hc₁ g) (Ne.symm hg) hy
  have hAD : A ≤ Subgroup.normalizer (D : Set X) := by
    have hle : ∀ a' ∈ A, D.map (MulAut.conj a').toMonoidHom ≤ D := by
      intro a' ha'
      rw [Subgroup.map_le_iff_le_comap]
      refine iSup₂_le fun g hg => ?_
      rw [← Subgroup.map_le_iff_le_comap, map_conj_map_conj]
      exact le_iSup₂_of_le (f := fun (g : X) (_ : g ∈ A) =>
        J₁.map (MulAut.conj g).toMonoidHom) (a' * g) (A.mul_mem ha' hg) le_rfl
    intro a' ha'
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hle a' ha') ?_
    have h1 := Subgroup.map_mono (f := (MulAut.conj a').toMonoidHom) (hle a'⁻¹ (A.inv_mem ha'))
    rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h1
  have hAp : IsPGroup 3 A := isPGroup_of_pow_three hA3
  have hmod := Sec6.card_inf_centralizer_modEq hAp hAD
  have h3D : 3 ∣ Nat.card D := h3₁.trans (Subgroup.card_dvd_of_le hJ₁D)
  have h3C : 3 ∣ Nat.card ↥(D ⊓ Subgroup.centralizer (A : Set X)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr h3D))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3C
  have hw' : orderOf (w : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hw
  have hw3 : (w : X) ^ 3 = 1 := by rw [← hw']; exact pow_orderOf_eq_one _
  have hw1 : (w : X) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw'
    omega
  have hwA : (w : X) ∈ A := hF3 _ w.2.2 hw3
  have hwe : (w : X) ∈ Subgroup.zpowers e := hAJ ⟨hwA, hDC w.2.1⟩
  have he3 : e ^ 3 = 1 := hA3 e he
  have heW : e ∈ Subgroup.zpowers (w : X) := mem_zpowers_of_mem_zpowers he3 hwe hw1
  have heD : e ∈ D := (Subgroup.zpowers_le.mpr w.2.1) heW
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hwe
    exact hw1 hwe
  obtain ⟨y, hyJ, z, hzC, hyz⟩ := mem_sup_centralizer_iff.mp (hDJ₁ heD)
  have hyzc : y * z = z * y := Subgroup.mem_centralizer_iff.mp hzC y hyJ
  have hy3 : y ^ 3 = 1 := by
    have h1 : y ^ 3 * z ^ 3 = 1 := by rw [← (Commute.mul_pow hyzc 3), hyz, he3]
    have h2 : y ^ 3 ∈ J₁ ⊓ Subgroup.centralizer (J₁ : Set X) := by
      refine ⟨J₁.pow_mem hyJ 3, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hzC 3)
    rw [hZ₁, Subgroup.mem_bot] at h2
    exact h2
  have hact : ∀ u ∈ J₁, u * y = y * u → e * u * e⁻¹ = u := by
    intro u hu huy
    have hzu : z * u = u * z := (Subgroup.mem_centralizer_iff.mp hzC u hu).symm
    rw [← hyz]
    calc y * z * u * (y * z)⁻¹ = y * (z * u) * z⁻¹ * y⁻¹ := by group
      _ = y * (u * z) * z⁻¹ * y⁻¹ := by rw [hzu]
      _ = (u * y) * y⁻¹ := by rw [huy]; group
      _ = u := by group
  have heN : e ∈ Subgroup.normalizer (J₁ : Set X) :=
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)) (hDJ₁ heD)
  have hbC : b ∈ Subgroup.centralizer (J₁ : Set X) :=
    mem_centralizer_of_mem_of_ne hc₁ hJ hJ₁J hbJ
  have hbN : b ∈ Subgroup.normalizer (J₁ : Set X) := Subgroup.centralizer_le_normalizer _ hbC
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hmove (one_mem _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoe : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hob : orderOf b = 3 := orderOf_eq_prime (hA3 b hbA) hb1
  have hoa : orderOf a = 3 := orderOf_eq_prime (hA3 a ha) ha1
  have hbe : b ∉ Subgroup.zpowers e := by
    intro hb
    have h1 : b ∈ J ⊓ Subgroup.centralizer (J : Set X) :=
      ⟨hbJ, hDC ((Subgroup.zpowers_le.mpr heD) hb)⟩
    rw [hZJ, Subgroup.mem_bot] at h1
    exact hb1 h1
  have hae : a ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers b := fun h =>
    hmove ((sup_le (Subgroup.zpowers_le.mpr heN) (Subgroup.zpowers_le.mpr hbN)) h)
  obtain ⟨h27', -⟩ := Sec13.Item131bProof.card_sup_sup_eq_27 hoe hob hoa (hAc e he b hbA)
    (hAc e he a ha) (hAc b hbA a ha) hbe hae
  have hAeq : Subgroup.zpowers e ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers a = A :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (sup_le (Subgroup.zpowers_le.mpr he) (Subgroup.zpowers_le.mpr hbA))
        (Subgroup.zpowers_le.mpr ha)) (by rw [h27, h27'])
  obtain ⟨h01, h02, h12⟩ := orbit_ne (hA3 a ha) hmove
  have hc₂ := isComponent_conj hc₁ (a ^ 1)
  have hc₃ := isComponent_conj hc₁ (a ^ 2)
  set δ := diagHom hc₁ h01 h02 h12 with hδ
  have hδinj : Function.Injective δ := diagHom_injective hc₁ h01 h02 h12 hZ₁
  have hne1 : J.map (MulAut.conj x).toMonoidHom ≠ J := hJ₁J
  have hδC : ∀ u : ↥J₁, (u : X) * y = y * u →
      δ u ∈ Subgroup.centralizer (A : Set X) ∧ δ u ∈ Subgroup.centralizer (J : Set X) := by
    intro u huy
    have hu1 : (u : X) ∈ Subgroup.centralizer (J : Set X) :=
      mem_centralizer_of_mem_of_ne hJ hc₁ hJ₁J.symm u.2
    have hu2 : a ^ 1 * (u : X) * (a ^ 1)⁻¹ ∈ Subgroup.centralizer (J : Set X) :=
      mem_centralizer_of_mem_of_ne hJ (isComponent_conj hc₁ (a ^ 1))
        (hne _ (A.pow_mem ha 1)).symm (conj_mem_map u.2 _)
    have hu3 : a ^ 2 * (u : X) * (a ^ 2)⁻¹ ∈ Subgroup.centralizer (J : Set X) :=
      mem_centralizer_of_mem_of_ne hJ (isComponent_conj hc₁ (a ^ 2))
        (hne _ (A.pow_mem ha 2)).symm (conj_mem_map u.2 _)
    have hJc : δ u ∈ Subgroup.centralizer (J : Set X) := by
      rw [hδ, diagHom_apply]
      exact mul_mem (mul_mem hu1 hu2) hu3
    refine ⟨?_, hJc⟩
    have hδa : δ u ∈ Subgroup.centralizer ({a} : Set X) := by
      rw [hδ, diagHom_apply]
      exact diag_mem_centralizer (hA3 a ha)
        (commute_of_ne hc₁ hc₂ h01 u.2 (conj_mem_map u.2 _))
        (commute_of_ne hc₁ hc₃ h02 u.2 (conj_mem_map u.2 _))
    have hδb : δ u ∈ Subgroup.centralizer ({b} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hJc b hbJ).symm
    have hδe : δ u ∈ Subgroup.centralizer ({e} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := diag_conj (b := a) (g := e) (hAc e he a ha) (u : X)
      rw [hact u u.2 huy] at h1
      rw [hδ, diagHom_apply]
      calc (u : X) * (a ^ 1 * (u : X) * (a ^ 1)⁻¹) * (a ^ 2 * (u : X) * (a ^ 2)⁻¹) * e =
          e * ((u : X) * (a ^ 1 * (u : X) * (a ^ 1)⁻¹) * (a ^ 2 * (u : X) * (a ^ 2)⁻¹)) *
            e⁻¹ * e := by rw [← h1]
        _ = e * ((u : X) * (a ^ 1 * (u : X) * (a ^ 1)⁻¹) * (a ^ 2 * (u : X) * (a ^ 2)⁻¹)) := by
          group
    have hle : A ≤ Subgroup.centralizer ({δ u} : Set X) := by
      rw [← hAeq]
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le,
        Subgroup.mem_centralizer_singleton_iff]
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hδe).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hδb).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hδa).symm
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hE9₁ : Sec8.E9Closed ↥J₁ :=
    hE9.of_mulEquiv (J.equivMapOfInjective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).symm
  obtain ⟨u₀, hu₀3, hu₀1, hu₀y⟩ :
      ∃ u₀ : ↥J₁, u₀ ^ 3 = 1 ∧ u₀ ≠ 1 ∧ ((u₀ : X) = y ∨ y = 1) := by
    by_cases hy1 : y = 1
    · obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3₁
      refine ⟨u, by rw [← hu]; exact pow_orderOf_eq_one u, ?_, Or.inr hy1⟩
      intro h
      rw [h, orderOf_one] at hu
      omega
    · refine ⟨⟨y, hyJ⟩, Subtype.ext (by simpa using hy3), fun h => hy1 ?_, Or.inl rfl⟩
      exact congrArg Subtype.val h
  obtain ⟨v₀, hv₀3, hu₀v₀, hv₀u₀⟩ := hE9₁ u₀ hu₀3 hu₀1
  have hcomm_y : ∀ w : ↥J₁, u₀ * w = w * u₀ → (w : X) * y = y * w := by
    intro w hw
    rcases hu₀y with h | h
    · rw [← h]
      exact (congrArg Subtype.val hw).symm
    · rw [h, mul_one, one_mul]
  have hu₀y' : (u₀ : X) * y = y * u₀ := hcomm_y u₀ rfl
  have hv₀y : (v₀ : X) * y = y * v₀ := hcomm_y v₀ hu₀v₀
  have hδ3 : ∀ u : ↥J₁, u ^ 3 = 1 → δ u ^ 3 = 1 := fun u hu => by
    rw [← map_pow, hu, map_one]
  obtain ⟨hu₀A, hu₀J⟩ := hδC u₀ hu₀y'
  obtain ⟨hv₀A, hv₀J⟩ := hδC v₀ hv₀y
  have hδu₀e : δ u₀ ∈ Subgroup.zpowers e := hAJ ⟨hF3 _ hu₀A (hδ3 u₀ hu₀3), hu₀J⟩
  have hδv₀e : δ v₀ ∈ Subgroup.zpowers e := hAJ ⟨hF3 _ hv₀A (hδ3 v₀ hv₀3), hv₀J⟩
  have hδu₀1 : δ u₀ ≠ 1 := fun h => hu₀1 (hδinj (h.trans (map_one δ).symm))
  have heu : e ∈ Subgroup.zpowers (δ u₀) := mem_zpowers_of_mem_zpowers he3 hδu₀e hδu₀1
  have hvu : δ v₀ ∈ Subgroup.zpowers (δ u₀) := (Subgroup.zpowers_le.mpr heu) hδv₀e
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvu
  apply hv₀u₀
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, hδinj ?_⟩
  rw [map_zpow, hk]

theorem commutator_le_normalizer_of_component_inf (hJ : IsComponent J)
    (hZJ : J ⊓ Subgroup.centralizer (J : Set X) = ⊥) (hE9 : Sec8.E9Closed ↥J)
    (h3 : 3 ∣ Nat.card J) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (h27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (J : Set X))
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (A : Set X) → w ^ 3 = 1 → w ∈ A)
    (he : e ∈ A) (hAJ : A ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.zpowers e)
    (hbA : b ∈ A) (hbJ : b ∈ J) (hb1 : b ≠ 1) (H : Subgroup X) :
    ⁅H, A⁆ ≤ Subgroup.normalizer (J : Set X) := by
  rw [Subgroup.commutator_le]
  intro x _ a ha
  have h1 := conj_mem_normalizer_of_component_inf hJ hZJ hE9 h3 hA3 hAc h27 hAN hF3 he hAJ hbA
    hbJ hb1 x⁻¹ ha
  rw [inv_inv] at h1
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem (hAN ha))

theorem le_normalizer_of_component_inf (hJ : IsComponent J)
    (hZJ : J ⊓ Subgroup.centralizer (J : Set X) = ⊥) (hE9 : Sec8.E9Closed ↥J)
    (h3 : 3 ∣ Nat.card J) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (h27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (J : Set X))
    (hF3 : ∀ w : X, w ∈ Subgroup.centralizer (A : Set X) → w ^ 3 = 1 → w ∈ A)
    (he : e ∈ A) (hAJ : A ⊓ Subgroup.centralizer (J : Set X) ≤ Subgroup.zpowers e)
    (hbA : b ∈ A) (hbJ : b ∈ J) (hb1 : b ≠ 1) {H : Subgroup X} (hH : H ≤ ⁅H, A⁆) :
    H ≤ Subgroup.normalizer (J : Set X) :=
  hH.trans (commutator_le_normalizer_of_component_inf hJ hZJ hE9 h3 hA3 hAc h27 hAN hF3 he hAJ
    hbA hbJ hb1 H)

end Normalize

end Item148Res6

end CFSG.RankThree.PartTwo.Sec14
