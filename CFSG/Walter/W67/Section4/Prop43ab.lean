module

public import CFSG.Walter.W67.Statements
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.W2Cor32A
import CFSG.Walter.W67.W1Prop24A
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hmap : ∀ X : Subgroup G, g ∈ Subgroup.normalizer (X : Set G) →
      X.map (MulAut.conj g).toMonoidHom = X := by
    intro X hX
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hX y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.mp hX _).mpr ?_, ?_⟩
      · simpa [mul_assoc] using hx
      · simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := hmap (A ⊔ B) ?_
  · constructor
    · intro hx
      rw [← h1]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h1] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
        exact mul_left_cancel (mul_right_cancel hyx)
      rw [← this]
      exact hy
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hAB := Subgroup.map_sup A B (MulAut.conj g).toMonoidHom
    rw [hmap A hA, hmap B hB] at hAB
    constructor
    · intro hx
      rw [← hAB]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hAB] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
        exact mul_left_cancel (mul_right_cancel hyx)
      rw [← this]
      exact hy

theorem Frame.exists_decomp_H
    {h : Hyp G} (fr : Frame h) {x : G} (hx : x ∈ h.H) :
    ∃ j ∈ Subgroup.zpowers h.J, ∃ k ∈ h.K, ∃ e ∈ fr.E, x = j * k * e := by
  have hHdec := fr.isInternalDirectProduct_H.1
  have hKEH : h.K ⊔ fr.E ≤ h.H := hHdec ▸ le_sup_right
  have hN : h.K ⊔ fr.E ≤ Subgroup.normalizer (Subgroup.zpowers h.J : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hKEH
  rw [← hHdec] at hx
  obtain ⟨j, hj, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hx
  have hEN : fr.E ≤ Subgroup.normalizer (h.K : Set G) := fr.E_le_H.trans h.H_le_normalizer
  obtain ⟨k, hk, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hw
  exact ⟨j, hj, k, hk, e, he, by group⟩

theorem prop_4_3_ab : S_prop_4_3_ab := by
  intro G _ _ h fr hp hidx T₂ hT₂ h2
  have hT₂1 := ne_one_of_orderOf_eq_two h2
  obtain ⟨z, hzK, hz3, hzN, hzE, hzC⟩ := fr.exists_three_E
  obtain ⟨n, hn, hnT⟩ := fr.exists_conj_T_V hidx hT₂ h2
  set u := n * z * n⁻¹ with hu
  set U := Subgroup.zpowers u
  have hu3 : orderOf u = 3 := by rw [hu, orderOf_conj_mul]; exact hz3
  have hUcard : Nat.card U = 3 := by rw [Nat.card_zpowers, hu3]
  have hVK := fr.isKleinFour_V hT₂ h2
  have hnV : ∀ v ∈ fr.V T₂, n⁻¹ * v * n ∈ fr.T := by
    have hle : fr.T.map (MulAut.conj n).toMonoidHom ≤ fr.V T₂ := by
      rintro _ ⟨t, ht, rfl⟩
      exact hnT t ht
    have heq : fr.T.map (MulAut.conj n).toMonoidHom = fr.V T₂ :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom)
          (MulAut.conj n).injective, fr.card_T, fr.card_V hT₂ h2])
    intro v hv
    rw [← heq] at hv
    obtain ⟨t, ht, rfl⟩ := hv
    show n⁻¹ * (n * t * n⁻¹) * n ∈ fr.T
    rw [show n⁻¹ * (n * t * n⁻¹) * n = t by group]
    exact ht
  have huN : u ∈ Subgroup.normalizer (fr.V T₂ : Set G) :=
    JT.mem_normalizer_of_conj_mem fun v hv => by
      have h1 := hnV v hv
      have h3 : z * (n⁻¹ * v * n) * z⁻¹ ∈ fr.T := (Subgroup.mem_normalizer_iff.mp hzN _).mp h1
      have h4 := hnT _ h3
      have e : n * (z * (n⁻¹ * v * n) * z⁻¹) * n⁻¹ = u * v * u⁻¹ := by rw [hu]; group
      rwa [e] at h4
  have huC : u ∉ Subgroup.centralizer (fr.V T₂ : Set G) := by
    intro huC
    apply hzC
    rw [Subgroup.mem_centralizer_iff] at huC ⊢
    intro t ht
    have h1 := huC _ (hnT t ht)
    have h3 := congrArg (fun x => n⁻¹ * x * n) h1
    have e1 : n⁻¹ * (n * t * n⁻¹ * u) * n = t * z := by rw [hu]; group
    have e2 : n⁻¹ * (u * (n * t * n⁻¹)) * n = z * t := by rw [hu]; group
    rw [e1, e2] at h3
    exact h3
  have hNV : Subgroup.normalizer (fr.V T₂ : Set G) =
      U ⊔ Subgroup.centralizer (fr.V T₂ : Set G) := by
    refine le_antisymm (fun x hx => ?_)
      (sup_le (Subgroup.zpowers_le.mpr huN) (Subgroup.centralizer_le_normalizer _))
    have hxJ : x * h.J * x⁻¹ ∈ fr.V T₂ := (Subgroup.mem_normalizer_iff.mp hx h.J).mp fr.J_mem_V
    have hxJ1 : x * h.J * x⁻¹ ≠ 1 := fun h1 => h.J_ne_one (by
      have := congrArg (fun y => x⁻¹ * y * x) h1
      simpa [mul_assoc] using this)
    obtain ⟨i, hi⟩ :=
      exists_zpow_conj_eq_of_three hVK hu3 huN huC fr.J_mem_V h.J_ne_one hxJ hxJ1
    have hyN : u ^ i * x ∈ Subgroup.normalizer (fr.V T₂ : Set G) :=
      Subgroup.mul_mem _ (Subgroup.pow_mem _ huN i) hx
    have hyJ' : u ^ i * x * h.J * (u ^ i * x)⁻¹ = h.J :=
      calc u ^ i * x * h.J * (u ^ i * x)⁻¹ = u ^ i * (x * h.J * x⁻¹) * (u ^ i)⁻¹ := by group
        _ = h.J := hi
    have hyJ : (u ^ i * x) * h.J = h.J * (u ^ i * x) := by
      calc (u ^ i * x) * h.J = (u ^ i * x * h.J * (u ^ i * x)⁻¹) * (u ^ i * x) := by group
        _ = h.J * (u ^ i * x) := by rw [hyJ']
    have hyT₂ : u ^ i * x * T₂ * (u ^ i * x)⁻¹ = T₂ := by
      have h1 : u ^ i * x * T₂ * (u ^ i * x)⁻¹ ∈ fr.V T₂ :=
        (Subgroup.mem_normalizer_iff.mp hyN T₂).mp fr.T₂_mem_V
      have h3 : u ^ i * x * T₂ * (u ^ i * x)⁻¹ ∈ h.K :=
        h.conj_mem_K (h.mem_H_iff.mpr hyJ) hT₂.2
      rcases eq_one_or_eq_of_mem_zpowers h2 (fr.V_inf_K hT₂ h1 h3) with h4 | h4
      · exfalso
        apply hT₂1
        have := congrArg (fun y => (u ^ i * x)⁻¹ * y * (u ^ i * x)) h4
        simpa [mul_assoc] using this
      · exact h4
    have hyC : u ^ i * x ∈ Subgroup.centralizer (fr.V T₂ : Set G) := by
      rw [fr.centralizer_V]
      refine ⟨h.mem_H_iff.mpr hyJ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc u ^ i * x * T₂ = (u ^ i * x * T₂ * (u ^ i * x)⁻¹) * (u ^ i * x) := by group
        _ = T₂ * (u ^ i * x) := by rw [hyT₂]
    have : x = (u ^ i)⁻¹ * (u ^ i * x) := by group
    rw [this]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) i)))
      (Subgroup.mem_sup_right hyC)
  set τ := n * h.J * n⁻¹ with hτ
  have hτS : τ ∈ (fr.S : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hn.1 h.J).mp fr.J_mem
  have hτV : τ ∉ fr.V T₂ := fun hτV => by
    have := hnV τ hτV
    rw [hτ, show n⁻¹ * (n * h.J * n⁻¹) * n = h.J by group] at this
    exact fr.J_not_mem_T this
  have hτ2 : orderOf τ = 2 := by rw [hτ, orderOf_conj_mul, h.orderOf_J]
  have hfixz : ∀ t ∈ fr.T, z * t = t * z → t = 1 := fun t ht hzt =>
    JT.eq_one_of_conj_eq_of_orderOf_eq_three fr.isKleinFour_T hz3 hzN hzC ht
      (by rw [hzt, mul_inv_cancel_right])
  have hCU : Subgroup.centralizer (U : Set G) = Subgroup.centralizer ({u} : Set G) := by
    show Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) = _
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hT₁ : (fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = Subgroup.zpowers τ := by
    rw [hCU]
    apply le_antisymm
    · intro s hs
      obtain ⟨hs, hsu⟩ := Subgroup.mem_inf.mp hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hsu
      have hs' : n⁻¹ * s * n ∈ (fr.S : Subgroup G) := by
        have := (Subgroup.mem_normalizer_iff.mp hn.1 (n⁻¹ * s * n)).mpr
        apply this
        simpa [mul_assoc] using hs
      have hzs : z * (n⁻¹ * s * n) = (n⁻¹ * s * n) * z := by
        have := congrArg (fun x => n⁻¹ * x * n) hsu
        simp only [hu] at this
        calc z * (n⁻¹ * s * n) = n⁻¹ * (n * z * n⁻¹ * s) * n := by group
          _ = n⁻¹ * (s * (n * z * n⁻¹)) * n := by rw [hsu]
          _ = (n⁻¹ * s * n) * z := by group
      rcases fr.eq_one_or_eq_J_of_commute hzK hfixz hs' hzs with h1 | h1
      · have : s = 1 := by
          have := congrArg (fun x => n * x * n⁻¹) h1
          simpa [mul_assoc] using this
        rw [this]
        exact Subgroup.one_mem _
      · have : s = τ := by
          have := congrArg (fun x => n * x * n⁻¹) h1
          simp only [hτ]
          simpa [mul_assoc] using this
        rw [this]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      refine ⟨hτS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hzJ : z * h.J = h.J * z := h.commute_J (h.K_le_H hzK)
      rw [hτ, hu]
      calc n * h.J * n⁻¹ * (n * z * n⁻¹) = n * (h.J * z) * n⁻¹ := by group
        _ = n * (z * h.J) * n⁻¹ := by rw [hzJ]
        _ = n * z * n⁻¹ * (n * h.J * n⁻¹) := by group
  have hT₁card : Nat.card ((fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) :
      Subgroup G) = 2 := by
    rw [hT₁, Nat.card_zpowers, hτ2]
  have hVτ : fr.V T₂ ⊓ Subgroup.zpowers τ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxτ⟩
    rcases eq_one_or_eq_of_mem_zpowers hτ2 hxτ with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxV) hτV
  have hVS := fr.V_le_S hT₂
  have hτS' : Subgroup.zpowers τ ≤ (fr.S : Subgroup G) := Subgroup.zpowers_le.mpr hτS
  have hSdec : fr.V T₂ ⊔ Subgroup.zpowers τ = (fr.S : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hVS hτS')
    have hc : ∀ x ∈ fr.V T₂, ∀ y ∈ Subgroup.zpowers τ, x * y = y * x := fun x hx y hy =>
      fr.comm_of_mem_S (hVS hx) (hτS' hy)
    obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
    rw [hVτ, Subgroup.card_bot, mul_one, fr.card_V hT₂ h2, Nat.card_zpowers, hτ2] at hcard
    rw [hcard, fr.card_S]
  have hτA : ∀ x ∈ fr.A T₂, τ * x * τ⁻¹ = x⁻¹ := fun x hx => fr.S_inv_A hT₂ h2 hτS hτV hx
  have hτE : ∀ e ∈ fr.E, τ * e = e * τ := fun e he =>
    (Subgroup.mem_centralizer_iff.mp (fr.E_le_CS he) τ hτS)
  have hEN : fr.E ≤ Subgroup.normalizer (fr.A T₂ : Set G) := fun e he =>
    JT.mem_normalizer_of_conj_mem fun x hx => fr.E_conj_mem_A he hx hT₂
  have hAEodd : Odd (Nat.card (fr.A T₂ ⊔ fr.E : Subgroup G)) := by
    have hc := card_sup_mul_card_inf_of_le_normalizer hEN
    exact Odd.of_dvd_nat ((fr.odd_card_A T₂).mul fr.odd_card_E) (Dvd.intro _ hc)
  have hτN : τ ∈ Subgroup.normalizer ((fr.A T₂ ⊔ fr.E : Subgroup G) : Set G) :=
    mem_normalizer_sup (JT.mem_normalizer_of_conj_mem fun x hx => fr.S_conj_mem_A hτS hx hT₂)
      (JT.mem_normalizer_of_conj_mem fun e he => by
        rw [hτE e he, mul_inv_cancel_right]
        exact he)
  have hτN' : Subgroup.zpowers τ ≤ Subgroup.normalizer ((fr.A T₂ ⊔ fr.E : Subgroup G) :
      Set G) := Subgroup.zpowers_le.mpr hτN
  refine ⟨U, hUcard, hNV, Subgroup.zpowers_le.mpr
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn.2 hzE) (Subgroup.inv_mem _ hn.2)),
    ?_, hT₁card, ?_⟩
  ·
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hg₁N := (Subgroup.zpowers_le.mpr huN) hg₁
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hg₁N g₂).mp hg₂)
        (Subgroup.inv_mem _ hg₂)
    · exact le_commutator_of_orderOf_three' hVK le_rfl (Subgroup.mem_zpowers u) hu3 huN huC
  intro T₁g
  have hT₁g : T₁g = Subgroup.zpowers τ := hT₁
  rw [hT₁g]
  set X := Subgroup.zpowers τ ⊔ fr.A T₂ ⊔ fr.E
  have hXC : X ≤ Subgroup.centralizer (fr.V T₂ : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun w hw =>
        fr.comm_of_mem_S (hVS hw) (hτS' hx)
    · intro x hx
      rw [fr.centralizer_V]
      exact ⟨h.K_le_H (fr.A_le T₂ hx).1, (fr.A_le T₂ hx).2⟩
    · intro e he
      exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
        Subgroup.mem_centralizer_iff.mp (fr.E_le_CS he) w (hVS hw)
  have hVC : fr.V T₂ ≤ Subgroup.centralizer (fr.V T₂ : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => fr.comm_of_mem_S (hVS hw) (hVS hv)
  refine ⟨⟨?_, ?_, Subgroup.le_centralizer_iff.mpr hXC⟩, ?_,
    ⟨hSdec, disjoint_iff.mpr hVτ, fun x hx => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      fr.comm_of_mem_S (hτS' hw) (hVS hx)⟩⟩
  ·
    refine le_antisymm (sup_le hVC hXC) (fun x hx => ?_)
    rw [fr.centralizer_V] at hx
    obtain ⟨hxH, hxT₂⟩ := hx
    obtain ⟨j, hj, k, hk, e, he, rfl⟩ := fr.exists_decomp_H hxH
    have hjS : j ∈ (fr.S : Subgroup G) := (Subgroup.zpowers_le.mpr fr.J_mem) hj
    have hkT₂ : k ∈ h.K ⊓ Subgroup.centralizer ({T₂} : Set G) := by
      refine ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hxT₂
      have hjc : j * T₂ = T₂ * j := fr.comm_of_mem_S hjS (fr.T₂_mem_S hT₂)
      have hec : e * T₂ = T₂ * e :=
        (Subgroup.mem_centralizer_iff.mp (fr.E_le_CS he) T₂ (fr.T₂_mem_S hT₂)).symm
      calc k * T₂ = j⁻¹ * ((j * k * e) * T₂) * e⁻¹ := by
            rw [mul_assoc (j * k), hec]; group
        _ = j⁻¹ * (T₂ * (j * k * e)) * e⁻¹ := by rw [h1]
        _ = T₂ * k := by
            rw [show T₂ * (j * k * e) = (T₂ * j) * k * e by group, ← hjc]; group
    rw [fr.K_inf_centralizer_eq hT₂ h2] at hkT₂
    have hτX : Subgroup.zpowers τ ≤ X := le_sup_left.trans le_sup_left
    have hTle : fr.T ≤ fr.V T₂ ⊔ X :=
      calc fr.T ≤ (fr.S : Subgroup G) := fr.T_le_S
        _ = fr.V T₂ ⊔ Subgroup.zpowers τ := hSdec.symm
        _ ≤ fr.V T₂ ⊔ X := sup_le_sup_left hτX _
    have hAle : fr.A T₂ ≤ fr.V T₂ ⊔ X := (le_sup_right.trans le_sup_left).trans le_sup_right
    have hkle : k ∈ fr.V T₂ ⊔ X := (sup_le hTle hAle) hkT₂
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left ((Subgroup.zpowers_le.mpr fr.J_mem_V) hj)) hkle)
      (Subgroup.mem_sup_right (Subgroup.mem_sup_right he))
  ·
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxV, hxX⟩
    have hxX' : x ∈ (fr.A T₂ ⊔ fr.E) ⊔ Subgroup.zpowers τ := by
      rw [sup_comm, ← sup_assoc]
      exact hxX
    obtain ⟨w, hw, t', ht', rfl⟩ := (mem_sup_iff_of_le_normalizer hτN').mp hxX'
    have hwS : w ∈ (fr.S : Subgroup G) := by
      have : w = w * t' * t'⁻¹ := by group
      rw [this]
      exact (fr.S : Subgroup G).mul_mem (hVS hxV) ((fr.S : Subgroup G).inv_mem (hτS' ht'))
    have hw1 : w = 1 := eq_one_of_odd_of_isPGroup fr.S.isPGroup' hwS
      (Odd.of_dvd_nat hAEodd (Subgroup.orderOf_dvd_natCard _ hw))
    rw [hw1, one_mul] at hxV ⊢
    have : t' ∈ fr.V T₂ ⊓ Subgroup.zpowers τ := ⟨hxV, ht'⟩
    rwa [hVτ] at this
  ·
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨a, ha, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hg₂
      rcases eq_one_or_eq_of_mem_zpowers hτ2 hg₁ with rfl | rfl
      · rw [commutatorElement_def]
        simp only [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [commutatorElement_def]
        have h1 : τ * (a * e) * τ⁻¹ = a⁻¹ * e := by
          calc τ * (a * e) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * e * τ⁻¹) := by group
            _ = a⁻¹ * e := by rw [hτA a ha, hτE e he, mul_inv_cancel_right]
        rw [h1, show a⁻¹ * e * (a * e)⁻¹ = a⁻¹ * a⁻¹ by group]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) (Subgroup.inv_mem _ ha)
    · intro a ha
      have hodd : Odd (orderOf a) := odd_orderOf_of_mem_oddPart ha
      obtain ⟨m, hm⟩ := hodd
      set b := a ^ (m + 1)
      have hb2 : b * b = a := by
        rw [← pow_two, ← pow_mul, show (m + 1) * 2 = 2 * m + 1 + 1 by ring, pow_succ, ← hm,
          pow_orderOf_eq_one, one_mul]
      have hbA : b ∈ fr.A T₂ := Subgroup.pow_mem _ ha _
      have hc : ⁅τ, b⁻¹⁆ = a := by
        rw [commutatorElement_def, inv_inv]
        have : τ * b⁻¹ * τ⁻¹ = b := by
          rw [show τ * b⁻¹ * τ⁻¹ = (τ * b * τ⁻¹)⁻¹ by group, hτA b hbA, inv_inv]
        rw [this, hb2]
      rw [← hc]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers τ)
        (Subgroup.mem_sup_left (Subgroup.inv_mem _ hbA))

end CFSG.Walter.W67
