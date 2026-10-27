module

public import CFSG.Quasithin.EmptyFaithful.SzF53B2Glue
public import CFSG.Quasithin.EmptyFaithful.SzF53B2Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace SzF53B2

section Amalg

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace B2Setup

theorem V_le_Qb (h : B2Setup H M S) : VZ S M ≤ pCoreOf 2 H :=
  F112W.le_pCoreOf_G₂_of_critDist_eq_two h.amalgamHypV h.V_ne_bot h.crit

theorem relIndex_inf_centralizer_S (h : B2Setup H M S) :
    (VZ S M ⊓ Subgroup.centralizer (S : Set G)).relIndex (VZ S M) = 2 := by
  have hyp := h.amalgamHypV
  have hSM := h.sylow_M.1
  have hSH := h.sylow_H.1
  obtain ⟨x', hx'H, hx'Qb, hx'M, hnt, hle, hquad⟩ :=
    F112W.exists_conj_of_critDist_eq_two hyp h.V_ne_bot h.crit
  have hQaS : pCoreOf 2 M ≤ S := isSylowTwoOf_pCoreOf_le h.sylow_M
  have hQbS : pCoreOf 2 H ≤ S := isSylowTwoOf_pCoreOf_le h.sylow_H
  obtain ⟨-, hQS2, -⟩ := h.relIndex_facts
  have hVc : VZ S M ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    (h.V_le_center).trans inf_le_right
  have h1 : ¬ conjSub x' (VZ S M) ≤ pCoreOf 2 M := by
    intro hle'
    apply hnt
    rw [eq_bot_iff]
    refine (Subgroup.commutator_mono le_rfl hle').trans ?_
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVc).le
  have hV'S : conjSub x' (VZ S M) ≤ S := hx'Qb.trans hQbS
  have h2 : pCoreOf 2 M ⊔ conjSub x' (VZ S M) = S := by
    have hle2 : pCoreOf 2 M ⊔ conjSub x' (VZ S M) ≤ S := sup_le hQaS hV'S
    have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 M) (pCoreOf 2 M ⊔ conjSub x' (VZ S M)) S
      le_sup_left hle2
    rw [hQS2] at hmul
    have hne : (pCoreOf 2 M).relIndex (pCoreOf 2 M ⊔ conjSub x' (VZ S M)) ≠ 1 := by
      intro h1'
      exact h1 (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1'))
    have hdvd : (pCoreOf 2 M).relIndex (pCoreOf 2 M ⊔ conjSub x' (VZ S M)) ∣ 2 := ⟨_, hmul.symm⟩
    have h2' : (pCoreOf 2 M).relIndex (pCoreOf 2 M ⊔ conjSub x' (VZ S M)) = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne
    rw [h2'] at hmul
    have : (pCoreOf 2 M ⊔ conjSub x' (VZ S M)).relIndex S = 1 := by omega
    exact le_antisymm hle2 (Subgroup.relIndex_eq_one.mp this)
  have hxQb : conjSub x' (pCoreOf 2 H) = pCoreOf 2 H :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hx'H)
  have hVS' : VZ S M ≤ conjSub x' S := by
    have : VZ S M ≤ conjSub x' (pCoreOf 2 H) := by rw [hxQb]; exact h.V_le_Qb
    exact this.trans (conjSub_mono x' hQbS)
  have hVM' : VZ S M ≤ conjSub x' M := hVS'.trans (conjSub_mono x' hSM)
  have hCM : conjSub x' M ⊓ Subgroup.centralizer (conjSub x' (VZ S M) : Set G) =
      conjSub x' (pCoreOf 2 M) := by
    rw [← h.inf_centralizer_V, conjSub_inf, conjSub_centralizer]
  have h4 : VZ S M ⊓ Subgroup.centralizer (conjSub x' (VZ S M) : Set G) =
      VZ S M ⊓ conjSub x' (pCoreOf 2 M) := by
    apply le_antisymm
    · rintro v ⟨hvV, hvC⟩
      exact ⟨hvV, hCM ▸ ⟨hVM' hvV, hvC⟩⟩
    · rintro v ⟨hvV, hvQ⟩
      exact ⟨hvV, (hCM.symm ▸ hvQ : v ∈ conjSub x' M ⊓ _).2⟩
  have h5 : ¬ VZ S M ≤ conjSub x' (pCoreOf 2 M) := by
    intro hle'
    apply hnt
    have hV'c : conjSub x' (VZ S M) ≤ Subgroup.centralizer (conjSub x' (pCoreOf 2 M) : Set G) := by
      rw [conjSub_centralizer]
      exact conjSub_mono x' hVc
    have hV'V : conjSub x' (VZ S M) ≤ Subgroup.centralizer (VZ S M : Set G) :=
      hV'c.trans (Subgroup.centralizer_le hle')
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hV'V
  have h6 : (conjSub x' (pCoreOf 2 M)).relIndex (conjSub x' S) = 2 := by
    have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x').toMonoidHom)
      (pCoreOf 2 M) S (MulEquiv.injective (MulAut.conj x'))
    exact this.trans hQS2
  have h7 : (conjSub x' (pCoreOf 2 M)).relIndex (VZ S M) = 2 := by
    have hle1 : (conjSub x' (pCoreOf 2 M)).relIndex (VZ S M) ≤
        (conjSub x' (pCoreOf 2 M)).relIndex (conjSub x' S) :=
      Subgroup.relIndex_le_of_le_right hVS' (by rw [h6]; norm_num)
    have hne1 : (conjSub x' (pCoreOf 2 M)).relIndex (VZ S M) ≠ 1 := fun h1' =>
      h5 (Subgroup.relIndex_eq_one.mp h1')
    have hne0 : (conjSub x' (pCoreOf 2 M)).relIndex (VZ S M) ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have h8 : VZ S M ⊓ Subgroup.centralizer (S : Set G) =
      VZ S M ⊓ Subgroup.centralizer (conjSub x' (VZ S M) : Set G) := by
    apply le_antisymm
    · rintro v ⟨hvV, hvC⟩
      exact ⟨hvV, Subgroup.centralizer_le hV'S hvC⟩
    · rintro v ⟨hvV, hvC⟩
      refine ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have hS : S ≤ Subgroup.centralizer ({v} : Set G) := by
        rw [← h2]
        refine sup_le (fun q hq => ?_) (fun w hw => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp (hVc hvV) q hq).symm ▸ rfl
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp hvC w hw)
      have := Subgroup.mem_centralizer_singleton_iff.mp (hS hu)
      exact this
  rw [h8, h4]
  rw [Subgroup.inf_relIndex_left]
  exact h7

theorem card_V (h : B2Setup H M S) : Nat.card (VZ S M) = 4 := by
  have hSM := h.sylow_M.1
  have hQS2 := h.relIndex_facts.2.1
  have hVQ : VZ S M ≤ pCoreOf 2 M := (h.V_le_center).trans inf_le_left
  have hQ : pCoreOf 2 M ≤ Subgroup.centralizer (VZ S M : Set G) :=
    h.inf_centralizer_V.symm.le.trans inf_le_right
  have hmod := card_eq_sq_centralizer (M := M) (S := S) (Y := VZ S M) h.isElemAbelian_V hVQ
    h.amalgamHypV.normalizes hQ h.amalgam.quot_right hSM hQS2 h.inf_centralizer_M
  have hidx := h.relIndex_inf_centralizer_S
  have hmul := Subgroup.relIndex_mul_card (VZ S M ⊓ Subgroup.centralizer (S : Set G)) (VZ S M)
  rw [inf_eq_left.mpr (inf_le_left : VZ S M ⊓ Subgroup.centralizer (S : Set G) ≤ VZ S M)] at hmul
  rw [hidx] at hmul
  set c := Nat.card ↥(VZ S M ⊓ Subgroup.centralizer (S : Set G)) with hc
  have hcpos : 0 < c := Nat.card_pos
  have : c = 2 := by
    have h1 : c * c = 2 * c := by
      calc c * c = Nat.card (VZ S M) := by rw [hmod, pow_two]
        _ = 2 * c := hmul.symm
    exact (Nat.eq_of_mul_eq_mul_right hcpos h1)
  rw [hmod, this]
  norm_num

theorem card_Zb (h : B2Setup H M S) : Nat.card (quasithinOmegaOneCenter S) = 2 := by
  have hSM := h.sylow_M.1
  have hQS2 := h.relIndex_facts.2.1
  have hVQ : VZ S M ≤ pCoreOf 2 M := (h.V_le_center).trans inf_le_left
  have hQ : pCoreOf 2 M ≤ Subgroup.centralizer (VZ S M : Set G) :=
    h.inf_centralizer_V.symm.le.trans inf_le_right
  have hmod := card_eq_sq_centralizer (M := M) (S := S) (Y := VZ S M) h.isElemAbelian_V hVQ
    h.amalgamHypV.normalizes hQ h.amalgam.quot_right hSM hQS2 h.inf_centralizer_M
  rw [← h.inf_centralizer_S]
  have h4 := h.card_V
  rw [hmod] at h4
  have : Nat.card ↥(VZ S M ⊓ Subgroup.centralizer (S : Set G)) ^ 2 = 2 ^ 2 := by
    rw [h4]; norm_num
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this

theorem isNaturalS3 (h : B2Setup H M S) : F112W.IsNaturalS3 M (VZ S M) where
  card_eq := h.card_V
  index_eq := by rw [h.inf_centralizer_V]; exact h.relIndex_facts.1

omit [Finite G] in
theorem le_centralizer_of_card_two {W X : Subgroup G} (hW : Nat.card W = 2)
    (hX : X ≤ Subgroup.normalizer (W : Set G)) : W ≤ Subgroup.centralizer (X : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hw1 : w = 1
  · subst hw1; simp
  have hxw : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hX hx) w).mp hw
  by_cases hxw1 : x * w * x⁻¹ = 1
  · exfalso
    apply hw1
    have : w = x⁻¹ * (x * w * x⁻¹) * x := by group
    rw [this, hxw1]; group
  obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.mp hW
  have hall : ∀ z : ↥W, z = a ∨ z = b := fun z => by
    have : z ∈ ({a, b} : Set ↥W) := by rw [huniv]; exact Set.mem_univ z
    simpa using this
  have h1 := hall 1
  have h2 := hall ⟨w, hw⟩
  have h3 := hall ⟨x * w * x⁻¹, hxw⟩
  have hw1' : (⟨w, hw⟩ : ↥W) ≠ 1 := fun h' => hw1 (congrArg Subtype.val h')
  have hxw1' : (⟨x * w * x⁻¹, hxw⟩ : ↥W) ≠ 1 := fun h' => hxw1 (congrArg Subtype.val h')
  have heq : (⟨w, hw⟩ : ↥W) = ⟨x * w * x⁻¹, hxw⟩ := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      first | exact absurd (h2.trans h1.symm) hw1' | exact absurd (h3.trans h1.symm) hxw1' |
        exact h2.trans h3.symm
  have := congrArg Subtype.val heq
  simp only at this
  calc x * w = (x * w * x⁻¹) * x := by group
    _ = w * x := by rw [← this]

theorem eq_bot_or_eq_V (h : B2Setup H M S) {W : Subgroup G} (hWV : W ≤ VZ S M)
    (hW : M ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = VZ S M := by
  have hd : Nat.card W ∣ 4 := h.card_V ▸ Subgroup.card_dvd_of_le hWV
  have hcases : Nat.card W = 1 ∨ Nat.card W = 2 ∨ Nat.card W = 4 := by
    have : Nat.card W ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [h4] at this
    simpa using this
  rcases hcases with h1 | h2 | h4
  · left; exact (Subgroup.card_eq_one.mp h1)
  · exfalso
    have hc := le_centralizer_of_card_two h2 hW
    have : W ≤ ⊥ := by
      rw [← h.inf_centralizer_M]
      exact le_inf hWV hc
    have h1 : Nat.card W = 1 := Subgroup.card_eq_one.mpr (le_bot_iff.mp this)
    omega
  · right
    exact Subgroup.eq_of_le_of_card_ge hWV (by rw [h4, h.card_V])

theorem le_zb_of_normalizes_S (h : B2Setup H M S) {W : Subgroup G} (hWV : W ≤ VZ S M)
    (hWS : S ≤ Subgroup.normalizer (W : Set G)) (hne : W ≠ VZ S M) :
    W ≤ quasithinOmegaOneCenter S := by
  have hd : Nat.card W ∣ 4 := h.card_V ▸ Subgroup.card_dvd_of_le hWV
  have hcases : Nat.card W = 1 ∨ Nat.card W = 2 ∨ Nat.card W = 4 := by
    have : Nat.card W ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have h4 : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [h4] at this
    simpa using this
  rcases hcases with h1 | h2 | h4
  · rw [Subgroup.card_eq_one.mp h1]; exact bot_le
  · have hc := le_centralizer_of_card_two h2 hWS
    rw [← h.inf_centralizer_S]
    exact le_inf hWV hc
  · exact absurd (Subgroup.eq_of_le_of_card_ge hWV (by rw [h4, h.card_V])) hne

theorem omegaOneCenter_Qa (h : B2Setup H M S) :
    quasithinOmegaOneCenter (pCoreOf 2 M) = VZ S M := by
  have hSM := h.sylow_M.1
  have hQS2 := h.relIndex_facts.2.1
  set Qa := pCoreOf 2 M with hQa
  set Y0 := quasithinOmegaOneCenter Qa with hY0
  have hY0def : Y0 =
      Subgroup.closure {z | z ∈ Qa ⊓ Subgroup.centralizer (Qa : Set G) ∧ z ^ 2 = 1} := rfl
  have hVY0 : VZ S M ≤ Y0 := by
    intro v hv
    rw [hY0def]
    exact Subgroup.subset_closure
      ⟨h.V_le_center hv, F7.isElemAbelian_pow_eq_one h.isElemAbelian_V hv⟩
  have hY0ab : IsElemAbelian 2 Y0 := by
    rw [hY0def]
    refine F7.isElemAbelian_closure _ ?_ ?_
    · intro z hz w hw
      exact (Subgroup.mem_centralizer_iff.mp hz.1.2 w hw.1.1).symm
    · intro z hz; exact hz.2
  have hY0Q : Y0 ≤ Qa := by
    rw [hY0def, Subgroup.closure_le]
    exact fun z hz => hz.1.1
  have hY0C : Y0 ≤ Subgroup.centralizer (Qa : Set G) := by
    rw [hY0def, Subgroup.closure_le]
    exact fun z hz => hz.1.2
  have hQY0 : Qa ≤ Subgroup.centralizer (Y0 : Set G) := Subgroup.le_centralizer_iff.mpr hY0C
  have hMY0 : M ≤ Subgroup.normalizer (Y0 : Set G) := by
    rw [hY0def]
    refine F7.le_normalizer_closure _ (fun g hg z hz => ?_)
    obtain ⟨⟨hzQ, hzC⟩, hz2⟩ := hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hg) z).mp hzQ
      exact this
    · refine Subgroup.mem_centralizer_iff.mpr (fun q hq => ?_)
      have hq' : g⁻¹ * q * g ∈ Qa := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M (M.inv_mem hg)) q).mp hq
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hzC _ hq'
      calc q * (g * z * g⁻¹) = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by rw [← hc]
        _ = g * z * g⁻¹ * q := by group
    · rw [conj_pow, hz2]; group
  have hfix : Y0 ⊓ Subgroup.centralizer (M : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzY, hzC⟩
    have hz2 : z ^ 2 = 1 := F7.isElemAbelian_pow_eq_one hY0ab hzY
    have hzM : z ∈ M := pCoreOf_le 2 M (hY0Q hzY)
    have : z ∈ quasithinOmegaOneCenter M := Subgroup.subset_closure ⟨⟨hzM, hzC⟩, hz2⟩
    rw [h.omegaOneCenter_M] at this
    exact this
  have hmod := card_eq_sq_centralizer (M := M) (S := S) (Y := Y0) hY0ab hY0Q hMY0 hQY0
    h.amalgam.quot_right hSM hQS2 hfix
  have hcap : Y0 ⊓ Subgroup.centralizer (S : Set G) = quasithinOmegaOneCenter S := by
    apply le_antisymm
    · rintro z ⟨hzY, hzC⟩
      have hz2 : z ^ 2 = 1 := F7.isElemAbelian_pow_eq_one hY0ab hzY
      have hzS : z ∈ S := isSylowTwoOf_pCoreOf_le h.sylow_M (hY0Q hzY)
      exact Subgroup.subset_closure ⟨⟨hzS, hzC⟩, hz2⟩
    · intro z hz
      exact ⟨hVY0 (le_conjClosure _ _ hz), ((B2Base.zb_le_S S) hz).2⟩
  rw [hcap, h.card_Zb] at hmod
  apply le_antisymm
  · exact (Subgroup.eq_of_le_of_card_ge hVY0 (by rw [hmod, h.card_V]; norm_num)).symm.le
  · exact hVY0

theorem V_le_of_normal (h : B2Setup H M S) {K : Subgroup G}
    (hK : M ≤ Subgroup.normalizer (K : Set G)) (hKQ : K ≤ pCoreOf 2 M) (hK1 : K ≠ ⊥) :
    VZ S M ≤ K := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hQM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  obtain ⟨x, hxK, hx1, hxc⟩ := D14.exists_fixed_of_lt hQ2 hKQ (bot_lt_iff_ne_bot.mpr hK1)
    (hQM.trans hK) (fun t _ => by
      rw [Subgroup.mem_normalizer_iff]; intro y; simp [Subgroup.mem_bot])
  have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1]; exact Subgroup.one_mem _)
  have hxQ : x ∈ pCoreOf 2 M := hKQ hxK
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr (fun t ht => ?_)
    have h1 := hxc t ht
    rw [Subgroup.mem_bot] at h1
    have : t * x = x * t := by
      calc t * x = (t * x * t⁻¹ * x⁻¹) * (x * t) := by group
        _ = x * t := by rw [h1, one_mul]
    exact this
  obtain ⟨n, hn⟩ := hQ2 ⟨x, hxQ⟩
  have hxn : x ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hord : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hxn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hk
    exact hx1' (orderOf_eq_one_iff.mp hk)
  have hdvd2 : 2 ∣ Nat.card ↥(Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, hk]; exact dvd_pow_self 2 hk0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) 2 hdvd2
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hz2 : ((y : ↥(Subgroup.zpowers x)) : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hy2
    simpa using this
  have hz1 : ((y : ↥(Subgroup.zpowers x)) : G) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext (by simpa using h1)
    rw [this, orderOf_one] at hy
    omega
  have hzK : ((y : ↥(Subgroup.zpowers x)) : G) ∈ K := (Subgroup.zpowers_le.mpr hxK) y.2
  have hzC : ((y : ↥(Subgroup.zpowers x)) : G) ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    (Subgroup.zpowers_le.mpr hxC) y.2
  have hzV : ((y : ↥(Subgroup.zpowers x)) : G) ∈ VZ S M := by
    rw [← h.omegaOneCenter_Qa]
    exact Subgroup.subset_closure ⟨⟨hKQ hzK, hzC⟩, hz2⟩
  have hWn : M ≤ Subgroup.normalizer ((VZ S M ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_inf h.amalgamHypV.normalizes hK
  rcases h.eq_bot_or_eq_V (inf_le_left : VZ S M ⊓ K ≤ VZ S M) hWn with hW | hW
  · exfalso
    have : ((y : ↥(Subgroup.zpowers x)) : G) ∈ VZ S M ⊓ K := ⟨hzV, hzK⟩
    rw [hW, Subgroup.mem_bot] at this
    exact hz1 this
  · exact inf_eq_left.mp hW

end B2Setup

end Amalg

end SzF53B2

end CFSG.Quasithin
