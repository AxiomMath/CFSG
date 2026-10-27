module

public import CFSG.Quasithin.Vol2.Ch6Sec1Prop15
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem12

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

section Field

variable {F : Type} [Field F] [Finite F]

theorem card_le_fix_mul_self_of_involutive (hF : 2 ∣ Nat.card F)
    (g : (Fin 2 → F) ≃+ (Fin 2 → F)) (hg : ∀ w, g (g w) = w) :
    Nat.card (Fin 2 → F) ≤
      Nat.card {w : Fin 2 → F // g w = w} * Nat.card {w : Fin 2 → F // g w = w} := by
  have : CharP F 2 := charP_two_of_two_dvd hF
  let φ : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun w => w + g w
      map_zero' := by simp
      map_add' := fun a b => by rw [map_add]; abel }
  have hcard : Nat.card (Fin 2 → F) = Nat.card φ.ker * Nat.card φ.range := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  have hker : Nat.card φ.ker ≤ Nat.card {w : Fin 2 → F // g w = w} := by
    refine Nat.card_le_card_of_injective (fun w => ⟨w.1, ?_⟩) ?_
    · have h1 : w.1 + g w.1 = 0 := AddMonoidHom.mem_ker.mp w.2
      funext i
      have h2 := congrFun h1 i
      simp only [Pi.add_apply, Pi.zero_apply] at h2
      linear_combination h2 - (w.1 i) * (CharTwo.two_eq_zero : (2 : F) = 0)
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext h1
  have hrange : Nat.card φ.range ≤ Nat.card {w : Fin 2 → F // g w = w} := by
    refine Nat.card_le_card_of_injective (fun w => ⟨w.1, ?_⟩) ?_
    · obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp w.2
      rw [← hv]
      change g (v + g v) = v + g v
      rw [map_add, hg, add_comm]
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext h1
  rw [hcard]
  exact Nat.mul_le_mul hker hrange

theorem exists_mul_self_eq (hF : 2 ∣ Nat.card F) (x : F) : ∃ y : F, y * y = x := by
  have : CharP F 2 := charP_two_of_two_dvd hF
  have hinj : Function.Injective (fun y : F => y * y) := by
    intro a b hab
    simp only at hab
    have h1 : (a - b) * (a - b) = 0 := by
      linear_combination hab + (b * b - a * b) * (CharTwo.two_eq_zero : (2 : F) = 0)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h1)
  exact Finite.injective_iff_surjective.mp hinj x

end Field

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem not_mem_S_of_fieldAut (h : Hyp611Nat G T M L V n) {t : G}
    (ht : IsInvolutoryFieldAut L t) : t ∉ ch6S T L V := by
  intro htS
  obtain ⟨y, hy, hty⟩ := h.exists_mem_TL_of_mem_S htS
  apply ht.2.2
  refine ⟨y, hy.2, fun x hx => ?_⟩
  have hcN : t * y⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ ht.1 (Subgroup.inv_mem _ (Subgroup.le_normalizer hy.2))
  have hz : y * x * y⁻¹ ∈ L := L.mul_mem (L.mul_mem hy.2 hx) (L.inv_mem hy.2)
  have h1 := h.commutator_mem_pCoreOf hcN hty hz
  have e : t * x * t⁻¹ * (y * x * y⁻¹)⁻¹ =
      t * y⁻¹ * (y * x * y⁻¹) * (t * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem not_mem_centralizer_of_fieldAut (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) : t ∉ Subgroup.centralizer (V : Set G) := fun hc =>
  h.not_mem_S_of_fieldAut ht ⟨htT, Subgroup.centralizer_le h.ZS_le hc⟩

theorem sq_mem_centralizer_of_fieldAut (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) : t * t ∈ Subgroup.centralizer (V : Set G) := by
  have htN : t ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer htT
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, htT⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine h.natural.mem_centralizer_of_pow ⟨t * t, Subgroup.mul_mem _ htN htN⟩ (fun g hg => ?_)
    k ?_
  · have h1 := ht.2.1 g hg
    rw [pow_two] at h1
    exact h.toHyp611.pCoreOf_le_centralizer h1
  · change (t * t) ^ 2 ^ k ∈ _
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, htk, one_pow]
    exact Subgroup.one_mem _

theorem card_fix_of_fieldAut (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) = 2 ^ n := by
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  have htL : (tt : G) ∈ Subgroup.normalizer (L : Set G) := h.T_le_normalizer_L htT
  apply le_antisymm
  · exact h.data.card_fixed_le_two_pow tt htL (h.not_mem_centralizer_of_fieldAut htT ht)
  · have hinv : ∀ w, h.data.conj tt (h.data.conj tt w) = w := by
      intro w
      rw [← h.data.conj_mul]
      exact h.data.conj_eq_of_mem_centralizer (tt * tt)
        (h.sq_mem_centralizer_of_fieldAut htT ht) w
    have h2 := card_le_fix_mul_self_of_involutive h.two_dvd_card_K (h.data.conj tt) hinv
    rw [← Nat.card_congr (h.data.fixedEquiv tt)] at h2
    have hK2 : Nat.card (Fin 2 → h.data.K) = 2 ^ n * 2 ^ n := by
      rw [Nat.card_fun, Nat.card_fin, h.data.card]
      ring
    rw [hK2] at h2
    exact Nat.mul_self_le_mul_self_iff.mp h2

theorem fix_ne_ZS_of_fieldAut (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) : V ⊓ Subgroup.centralizer ({t} : Set G) ≠ ch6ZS T L V := by
  intro heq
  apply h.not_mem_S_of_fieldAut ht
  refine ⟨htT, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  rw [← heq] at hz
  exact (Subgroup.mem_centralizer_iff.mp hz.2 t rfl).symm

theorem not_fix_le_ZS (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) : ¬ V ⊓ Subgroup.centralizer ({t} : Set G) ≤ ch6ZS T L V :=
  fun hle => h.fix_ne_ZS_of_fieldAut htT ht (Subgroup.eq_of_le_of_card_ge hle
    (by rw [h.card_ZS, h.card_fix_of_fieldAut htT ht]))

theorem not_ZS_le_fix (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) : ¬ ch6ZS T L V ≤ V ⊓ Subgroup.centralizer ({t} : Set G) :=
  fun hle => h.fix_ne_ZS_of_fieldAut htT ht (Subgroup.eq_of_le_of_card_ge hle
    (by rw [h.card_ZS, h.card_fix_of_fieldAut htT ht])).symm

theorem mem_centralizer_of_mem_S_of_fix (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) {r : G} (hrS : r ∈ ch6S T L V)
    (hrU : r ∈ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) : r ∈ Subgroup.centralizer (V : Set G) := by
  by_contra hrV
  have heq := h.centralizer_singleton_eq_ZS hrS hrV
  apply h.not_fix_le_ZS htT ht
  intro u hu
  rw [← heq]
  refine ⟨hu.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  rw [Set.mem_singleton_iff.mp hy]
  exact (Subgroup.mem_centralizer_iff.mp hrU u hu).symm

theorem conj_eq_of_fix (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T) {y : G}
    (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hyU : y ∈ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) {w : Fin 2 → h.data.K}
    (hw : h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ w = w) :
    h.data.conj ⟨y, hyN⟩ w = w := by
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  set u := (h.data.fixedEquiv tt).symm ⟨w, hw⟩ with hu
  have hEu : Multiplicative.toAdd (h.data.E ⟨(u : G), u.2.1⟩) = w :=
    congrArg Subtype.val ((h.data.fixedEquiv tt).apply_symm_apply ⟨w, hw⟩)
  rw [← hEu]
  exact h.data.conj_E_eq_of_commute ⟨y, hyN⟩ ⟨u, u.2.1⟩
    (Subgroup.mem_centralizer_iff.mp hyU u u.2).symm

theorem exists_ne_of_fieldAut (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) {σ : h.data.K ≃+* h.data.K}
    (hσ : ∀ (c : h.data.K) (w : Fin 2 → h.data.K),
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ (c • w) =
        σ c • h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ w) : ∃ θ, σ θ ≠ θ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hle⟩ := h.exists_line
  exact h.not_mem_S_of_fieldAut ht ⟨htT, h.mem_centralizer_ZS_of_linear hv hle htT
    fun c w => by rw [hσ, hcon]⟩

theorem exists_basis_fix (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) :
    ∃ u₁ u₂ : Fin 2 → h.data.K,
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ u₁ = u₁ ∧
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer htT⟩ u₂ = u₂ ∧ det2 u₁ u₂ ≠ 0 := by
  classical
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer htT⟩ with htt
  obtain ⟨σ, hσ⟩ := h.data.exists_semilinear tt (h.T_le_normalizer_L htT)
  obtain ⟨θ, hθ⟩ := h.exists_ne_of_fieldAut htT ht hσ
  have hF0 := card_fixed_mul_self_le σ hθ
  rw [h.data.card] at hF0
  have hfix : Nat.card {w : Fin 2 → h.data.K // h.data.conj tt w = w} = 2 ^ n := by
    rw [← Nat.card_congr (h.data.fixedEquiv tt)]
    exact h.card_fix_of_fieldAut htT ht
  have h2 : 2 ≤ Nat.card {c : h.data.K // σ c = c} := by
    have : Nontrivial {c : h.data.K // σ c = c} :=
      ⟨⟨⟨0, map_zero σ⟩, ⟨1, map_one σ⟩, fun h0 => zero_ne_one (congrArg Subtype.val h0)⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw0, hw⟩ : ∃ w : Fin 2 → h.data.K, w ≠ 0 ∧ h.data.conj tt w = w := by
    by_contra hcon'
    push Not at hcon'
    have hsub : Subsingleton {v : Fin 2 → h.data.K // h.data.conj tt v = v} :=
      ⟨fun a b => Subtype.ext (by
        have ha : a.1 = 0 := by by_contra hne; exact hcon' a.1 hne a.2
        have hb : b.1 = 0 := by by_contra hne; exact hcon' b.1 hne b.2
        rw [ha, hb])⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    rw [hfix] at this
    have : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
    omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
  simp only [Pi.zero_apply] at hi
  have hc : ∀ v : {v : Fin 2 → h.data.K // h.data.conj tt v = v}, v.1 = (v.1 i / w i) • w := by
    intro v
    obtain ⟨c, hc⟩ := exists_eq_smul_of_det2_eq_zero hw0 (hcon w v.1 hw v.2)
    rw [hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_assoc, div_self hi, mul_one]
  have hcf : ∀ v : {v : Fin 2 → h.data.K // h.data.conj tt v = v},
      σ (v.1 i / w i) = v.1 i / w i := by
    intro v
    have h1 := v.2
    rw [hc v, hσ, hw] at h1
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi this
  have hle : Nat.card {v : Fin 2 → h.data.K // h.data.conj tt v = v} ≤
      Nat.card {c : h.data.K // σ c = c} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨_, hcf v⟩) ?_
    intro v v' hvv'
    apply Subtype.ext
    rw [hc v, hc v']
    exact congrArg (· • w) (congrArg Subtype.val hvv')
  rw [hfix] at hle
  nlinarith

theorem mem_centralizer_of_linear_of_fix (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) {y : G} (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hyU : y ∈ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G))
    (hlin : ∀ (c : h.data.K) (w : Fin 2 → h.data.K),
      h.data.conj ⟨y, hyN⟩ (c • w) = c • h.data.conj ⟨y, hyN⟩ w) :
    y ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hdet⟩ := h.exists_basis_fix htT ht
  have h₁ := h.conj_eq_of_fix htT hyN hyU hu₁
  have h₂ := h.conj_eq_of_fix htT hyN hyU hu₂
  apply h.data.mem_centralizer_of_conj_eq ⟨y, hyN⟩
  intro w
  rw [eq_add_of_det2_ne_zero hdet w, map_add, hlin, hlin, h₁, h₂]

theorem centralizer_fix_le (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) :
    T ⊓ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
      ch6Q T V ⊔ Subgroup.zpowers t := by
  classical
  rintro y ⟨hyT, hyU⟩
  have hTN : ∀ {x : G}, x ∈ T → x ∈ Subgroup.normalizer (V : Set G) :=
    fun hx => h.toHyp611.T_le_normalizer hx
  set tt : Subgroup.normalizer (V : Set G) := ⟨t, hTN htT⟩ with htt
  set my : Subgroup.normalizer (V : Set G) := ⟨y, hTN hyT⟩ with hmy
  have htU : t ∈ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp hu.2 t rfl).symm
  obtain ⟨σ, hσ⟩ := h.data.exists_semilinear tt (h.T_le_normalizer_L htT)
  obtain ⟨τ, hτ⟩ := h.data.exists_semilinear my (h.T_le_normalizer_L hyT)
  by_cases hτ1 : ∀ c, τ c = c
  ·
    have hyV := h.mem_centralizer_of_linear_of_fix htT ht (hTN hyT) hyU
      (fun c w => by rw [hτ, hτ1])
    exact Subgroup.mem_sup_left ⟨hyT, hyV⟩
  push Not at hτ1
  obtain ⟨θ', hθ'⟩ := hτ1
  obtain ⟨θ, hθ⟩ := h.exists_ne_of_fieldAut htT ht hσ
  have hfix : Nat.card {w : Fin 2 → h.data.K // h.data.conj tt w = w} = 2 ^ n := by
    rw [← Nat.card_congr (h.data.fixedEquiv tt)]
    exact h.card_fix_of_fieldAut htT ht
  have hσ2 : σ * σ = 1 := by
    have h1 := card_fixed_le_fix_mul_self (h.data.conj tt) σ hσ
    have h2 := card_fixed_mul_self_le σ hθ
    rw [hfix] at h1
    rw [h.data.card] at h2
    exact mul_self_eq_one_of_card σ hθ (by rw [h.data.card]; exact le_antisymm h2 h1)
  have hτ2 : τ * τ = 1 := by
    have h0 : Nat.card {w : Fin 2 → h.data.K // h.data.conj tt w = w} ≤
        Nat.card {w : Fin 2 → h.data.K // h.data.conj my w = w} := by
      refine Nat.card_le_card_of_injective
        (fun w => ⟨w.1, h.conj_eq_of_fix htT (hTN hyT) hyU w.2⟩) ?_
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext h1
    have h1 := card_fixed_le_fix_mul_self (h.data.conj my) τ hτ
    have h2 := card_fixed_mul_self_le τ hθ'
    rw [hfix] at h0
    rw [h.data.card] at h2
    exact mul_self_eq_one_of_card τ hθ' (by rw [h.data.card]; exact le_antisymm h2 (h0.trans h1))
  have hστ : σ = τ := ringEquiv_eq_of_mul_self_eq_one h.two_dvd_card_K hσ2 hτ2
    (fun h1 => hθ (by rw [h1]; rfl)) (fun h1 => hθ' (by rw [h1]; rfl))
  have htyN : t * y ∈ Subgroup.normalizer (V : Set G) := hTN (T.mul_mem htT hyT)
  have htyU : t * y ∈ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) := Subgroup.mul_mem _ htU hyU
  have htyV := h.mem_centralizer_of_linear_of_fix htT ht htyN htyU (fun c w => by
    have e : (⟨t * y, htyN⟩ : Subgroup.normalizer (V : Set G)) = tt * my := rfl
    rw [e, h.data.conj_mul, h.data.conj_mul, hτ, hσ, ← hστ]
    change (σ * σ) c • _ = _
    rw [hσ2]
    rfl)
  have hq : t * y ∈ ch6Q T V := ⟨T.mul_mem htT hyT, htyV⟩
  have e : y = t⁻¹ * (t * y) := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)) hq

end Hyp611Nat

end CFSG.Quasithin.H13
