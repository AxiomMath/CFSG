module

public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Basic

public section

namespace CFSG.Quasithin.F134

open CFSG.Walter.J1 CFSG.Walter.J1Props

section Janko

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_commute (g a b : G) (hab : a * b = b * a) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) := by
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [hab]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem janko_not_commute_t (h : JankoHyp₀ G) {y s : G} (hy : orderOf y = 3) (hs : s * s = 1)
    (hs1 : s ≠ 1) (hst : s ≠ h.t) (hsc : s * h.t = h.t * s) (hyt : y * h.t = h.t * y)
    (hys : y * s = s * y) : False := by
  have hyF : y ∈ h.F :=
    h.mem_F_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hyt) (by rw [hy]; decide)
  have key : ∃ f ∈ h.F, f * f = 1 ∧ f ≠ 1 ∧ y * f = f * y := by
    rcases h.mem_centralizer_t.mp (Subgroup.mem_centralizer_singleton_iff.mpr hsc) with
      hF | hF
    · exact ⟨s, hF, hs, hs1, hys⟩
    · refine ⟨h.t * s, hF, ?_, ?_, ?_⟩
      · calc h.t * s * (h.t * s) = h.t * (s * h.t) * s := by group
          _ = (h.t * h.t) * (s * s) := by rw [hsc]; group
          _ = 1 := by rw [h.t_mul_t, hs, one_mul]
      · intro he
        apply hst
        calc s = h.t⁻¹ * (h.t * s) := by group
          _ = h.t⁻¹ := by rw [he, mul_one]
          _ = h.t := inv_eq_of_mul_eq_one_left h.t_mul_t
      · calc y * (h.t * s) = (y * h.t) * s := by group
          _ = h.t * (y * s) := by rw [hyt]; group
          _ = h.t * s * y := by rw [hys]; group
  obtain ⟨f, hfF, hf2, hf1, hyf⟩ := key
  have hy1 : y ≠ 1 := fun he => by rw [he, orderOf_one] at hy; omega
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hmem := A5Sub.mem_zpowers_of_commute_three h.iso hyF hfF hy3 hy1 hyf
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hf3 : (y ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hf2' : (y ^ k) ^ 2 = 1 := by rw [sq]; exact hf2
  have hord : orderOf (y ^ k) ∣ Nat.gcd 3 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf3) (orderOf_dvd_of_pow_eq_one hf2')
  rw [show Nat.gcd 3 2 = 1 from rfl, Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact hf1 hord

theorem janko_not_commute_four (h : JankoHyp₀ G) {y s₁ s₂ : G} (hy : orderOf y = 3)
    (h1 : s₁ * s₁ = 1) (h1' : s₁ ≠ 1) (h2 : s₂ * s₂ = 1) (h2' : s₂ ≠ 1) (h12 : s₁ ≠ s₂)
    (hc : s₁ * s₂ = s₂ * s₁) (hy1 : y * s₁ = s₁ * y) (hy2 : y * s₂ = s₂ * y) : False := by
  have hs₁ : orderOf s₁ = 2 := orderOf_eq_prime (by rw [sq]; exact h1) h1'
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hs₁
  have hy3 : orderOf (g * y * g⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  refine janko_not_commute_t h hy3 (s := g * s₂ * g⁻¹) ?_ ?_ ?_ ?_ ?_ ?_
  · calc g * s₂ * g⁻¹ * (g * s₂ * g⁻¹) = g * (s₂ * s₂) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · intro he
    apply h2'
    calc s₂ = g⁻¹ * (g * s₂ * g⁻¹) * g := by group
      _ = 1 := by rw [he]; group
  · intro he
    apply h12
    calc s₁ = g⁻¹ * (g * s₁ * g⁻¹) * g := by group
      _ = g⁻¹ * (g * s₂ * g⁻¹) * g := by rw [hg, he]
      _ = s₂ := by group
  · rw [← hg]
    exact conj_commute g s₂ s₁ hc.symm
  · rw [← hg]
    exact conj_commute g y s₁ hy1
  · exact conj_commute g y s₂ hy2

theorem janko_mul_self_of_sylow (h : JankoHyp₀ G) (S : Sylow 2 G) {x : G}
    (hx : x ∈ (S : Subgroup G)) : x * x = 1 := by
  obtain ⟨T, hT⟩ := h.exists_sylow_mem_t
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hx' : x ∈ ((g • T : Sylow 2 G) : Subgroup G) := by rw [hg]; exact hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
  have h1 := h.mul_self_of_mem_sylow T hT hx'
  rw [MulAut.smul_def, MulAut.conj_inv_apply] at h1
  calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

omit [Finite G] in
theorem card_eq_24 {B U : Subgroup G} {y : G} (hG : Nat.card G = 175560) (hUc : Nat.card U = 8)
    (hUB : U ≤ B) (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3) (hyB : y ∈ B)
    (hy : orderOf y = 3) : Nat.card B = 24 := by
  have hdvd : Nat.card B ∣ 24 * 7315 := by
    rw [show 24 * 7315 = 175560 by norm_num, ← hG]
    exact Subgroup.card_subgroup_dvd_card B
  have hcop : Nat.Coprime (Nat.card B) 7315 := Nat.coprime_of_dvd fun k hk hkB hk7 => by
    rcases hB k hk hkB with rfl | rfl <;> norm_num at hk7
  have h24 : Nat.card B ∣ 24 := hcop.dvd_of_dvd_mul_right hdvd
  have h8 : 8 ∣ Nat.card B := hUc ▸ Subgroup.card_dvd_of_le hUB
  have h3 : 3 ∣ Nat.card B := hy ▸ Subgroup.orderOf_dvd_natCard B hyB
  have : 24 ∣ Nat.card B := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3
  exact Nat.dvd_antisymm h24 this

theorem card_inf_eq_four {B U U' : Subgroup G} (hB : Nat.card B = 24) (hUB : U ≤ B) (hU'B : U' ≤ B)
    (hUc : Nat.card U = 8) (hU'c : Nat.card U' = 8) (hne : U ≠ U') :
    Nat.card (U ⊓ U' : Subgroup G) = 4 ∧ U ⊔ U' = B := by
  have hrel : ∀ W : Subgroup G, W ≤ B → Nat.card W = 8 → W.relIndex B = 3 := by
    intro W hW hWc
    have := Subgroup.relIndex_mul_card W B
    rw [inf_eq_left.mpr hW, hWc, hB] at this
    omega
  have hle := Subgroup.relIndex_inf_le (H := U) (K := U') (L := B)
  rw [hrel U hUB hUc, hrel U' hU'B hU'c] at hle
  have hmul := Subgroup.relIndex_mul_card (U ⊓ U') B
  rw [inf_eq_left.mpr (inf_le_left.trans hUB), hB] at hmul
  have hdvd : Nat.card (U ⊓ U' : Subgroup G) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hUc]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hjV⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hne8 : Nat.card (U ⊓ U' : Subgroup G) ≠ 8 := by
    intro h8
    have e1 := Subgroup.eq_of_le_of_card_ge (inf_le_left : U ⊓ U' ≤ U) (by rw [hUc, h8])
    have e2 := Subgroup.eq_of_le_of_card_ge (inf_le_right : U ⊓ U' ≤ U') (by rw [hU'c, h8])
    exact hne (e1.symm.trans e2)
  refine ⟨?_, ?_⟩
  · rw [hjV] at hmul hne8 ⊢
    interval_cases j
    · omega
    · omega
    · rfl
    · exact absurd rfl hne8
  · have hle' : U ⊔ U' ≤ B := sup_le hUB hU'B
    have hdvd' : Nat.card (U ⊔ U' : Subgroup G) ∣ 24 := hB ▸ Subgroup.card_dvd_of_le hle'
    have h8 : 8 ∣ Nat.card (U ⊔ U' : Subgroup G) := hUc ▸ Subgroup.card_dvd_of_le le_sup_left
    have hne' : Nat.card (U ⊔ U' : Subgroup G) ≠ 8 := by
      intro h8'
      have e1 := Subgroup.eq_of_le_of_card_ge (le_sup_left : U ≤ U ⊔ U') (by rw [hUc, h8'])
      have e2 := Subgroup.eq_of_le_of_card_ge (le_sup_right : U' ≤ U ⊔ U') (by rw [hU'c, h8'])
      exact hne (e1.trans e2.symm)
    obtain ⟨c, hc⟩ := h8
    have hc24 : 8 * c ≤ 24 := hc ▸ Nat.le_of_dvd (by norm_num) hdvd'
    have hcle : c ≤ 3 := by omega
    have hc3 : c = 3 := by
      rw [hc] at hdvd' hne'
      rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with h' | h' | h' | h' <;> subst h'
      · norm_num at hdvd'
      · exact absurd (by norm_num) hne'
      · norm_num at hdvd'
      · rfl
    exact Subgroup.eq_of_le_of_card_ge hle' (by rw [hB, hc, hc3])

theorem janko_mem_normalizer (h : JankoHyp₀ G) (hG : Nat.card G = 175560) {U B : Subgroup G}
    {y : G} (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hUB : U ≤ B)
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3) (hyB : y ∈ B)
    (hy : orderOf y = 3) : y ∈ Subgroup.normalizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUc : Nat.card U = 8 := h.card_sylow (hU.toSylow hUi)
  have hB24 := card_eq_24 hG hUc hUB hB hyB hy
  by_contra hyN
  have hU'c : Nat.card (U.map (MulAut.conj y).toMonoidHom) = 8 := by
    rw [← hUc]
    exact (Nat.card_congr (U.equivMapOfInjective _ (MulAut.conj y).injective).toEquiv).symm
  have hU'B : U.map (MulAut.conj y).toMonoidHom ≤ B := by
    rintro _ ⟨u, hu, rfl⟩
    exact B.mul_mem (B.mul_mem hyB (hUB hu)) (B.inv_mem hyB)
  have hUU' : U ≠ U.map (MulAut.conj y).toMonoidHom := by
    intro he
    apply hyN
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [he]
      exact ⟨u, hu, rfl⟩
    · intro hu
      have hu' : y * u * y⁻¹ ∈ U.map (MulAut.conj y).toMonoidHom := he ▸ hu
      obtain ⟨v, hv, hvu⟩ := hu'
      have hvu' : y * v * y⁻¹ = y * u * y⁻¹ := hvu
      have : v = u := by simpa using hvu'
      rwa [← this]
  have hU'p : IsPGroup 2 (U.map (MulAut.conj y).toMonoidHom) := hU.map _
  have hU'i : ¬ 2 ∣ (U.map (MulAut.conj y).toMonoidHom).index := by
    have h1 := (U.map (MulAut.conj y).toMonoidHom).card_mul_index
    have h2 := U.card_mul_index
    rw [hU'c] at h1
    rw [hUc] at h2
    have : (U.map (MulAut.conj y).toMonoidHom).index = U.index := by omega
    rw [this]
    exact hUi
  obtain ⟨hV4, hsup⟩ := card_inf_eq_four hB24 hUB hU'B hUc hU'c hUU'
  have hab : ∀ (W : Subgroup G) (hW : IsPGroup 2 W) (hWi : ¬ 2 ∣ W.index),
      ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro W hW hWi a ha b hb
    have := h.abelian_sylow (hW.toSylow hWi)
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set V := U ⊓ U.map (MulAut.conj y).toMonoidHom
  have hcent : B ≤ Subgroup.centralizer (V : Set G) := by
    rw [← hsup]
    refine sup_le (fun u hu => ?_) (fun u hu => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro v hv
    · exact (hab U hU hUi u hu v hv.1).symm
    · exact (hab _ hU'p hU'i u hu v hv.2).symm
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => janko_mul_self_of_sylow h (hU.toSylow hUi) hv.1
  obtain ⟨s₁, hs₁V, hs₁⟩ : ∃ s₁ ∈ V, s₁ ≠ 1 := by
    by_contra hall
    push Not at hall
    have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hall
    rw [this, Subgroup.card_bot] at hV4
    omega
  have hz : Subgroup.zpowers s₁ < V := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hs₁V) fun he => ?_
    have hc := Nat.card_zpowers s₁
    rw [he, hV4] at hc
    have : orderOf s₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq s₁ hs₁V)
    rw [← hc] at this
    norm_num at this
  obtain ⟨s₂, hs₂V, hs₂⟩ := IsConcreteLE.exists_of_lt hz
  have hs₂1 : s₂ ≠ 1 := fun he => hs₂ (he ▸ Subgroup.one_mem _)
  have hs₁₂ : s₁ ≠ s₂ := fun he => hs₂ (he ▸ Subgroup.mem_zpowers _)
  have hyc := Subgroup.mem_centralizer_iff.mp (hcent hyB)
  exact janko_not_commute_four h hy (hsq s₁ hs₁V) hs₁ (hsq s₂ hs₂V) hs₂1 hs₁₂
    (hab U hU hUi s₁ hs₁V.1 s₂ hs₂V.1) (hyc s₁ hs₁V).symm (hyc s₂ hs₂V).symm

end Janko

theorem card_walterJ1' : Nat.card CFSG.Open.walterJ1 = 175560 := by
  rw [CFSG.Walter.J1Props.J1_card]
  norm_num

theorem mem_map_subgroupOf_iff' {A G : Type*} [Group A] [Group G] {L K : Subgroup A}
    (ψ : ↥L ≃* G) (m : ↥L) : ψ m ∈ (K.subgroupOf L).map ψ.toMonoidHom ↔ (m : A) ∈ K := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]

theorem conj_pow_odd_inv {A : Type*} [Group A] {x y : A} (hxy : x * y * x⁻¹ = y⁻¹) (k : ℕ) :
    x ^ (2 * k + 1) * y * (x ^ (2 * k + 1))⁻¹ = y⁻¹ := by
  have h2 : x ^ 2 * y * (x ^ 2)⁻¹ = y := by
    have hinv : x * y⁻¹ * x⁻¹ = y := by
      rw [show x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ by group, hxy, inv_inv]
    calc x ^ 2 * y * (x ^ 2)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by rw [sq]; group
      _ = y := by rw [hxy, hinv]
  have hk : ∀ k : ℕ, x ^ (2 * k) * y * (x ^ (2 * k))⁻¹ = y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (2 * (k + 1)) * y * (x ^ (2 * (k + 1)))⁻¹ =
            x ^ 2 * (x ^ (2 * k) * y * (x ^ (2 * k))⁻¹) * (x ^ 2)⁻¹ := by
              rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add]
              group
        _ = y := by rw [ih, h2]
  calc x ^ (2 * k + 1) * y * (x ^ (2 * k + 1))⁻¹ =
        x * (x ^ (2 * k) * y * (x ^ (2 * k))⁻¹) * x⁻¹ := by
          rw [pow_succ']
          group
    _ = y⁻¹ := by rw [hk k, hxy]

theorem j1_local
    (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (y g : A)
    (e : ↥L ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) (hUB : U ≤ B) (hBL : B ≤ L)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3) (hyB : y ∈ B) (hy : orderOf y = 3)
    (hgL : g ∈ Subgroup.normalizer (L : Set A)) (hgU : g ∈ Subgroup.normalizer (U : Set A))
    (hgy : g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A)) :
    g * y * g⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ε : ↥L ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have hyL : y ∈ L := hBL hyB
  have hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    have hUw : IsPGroup 2 ((U.subgroupOf L).map ε.toMonoidHom) :=
      (hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm).map _
    have hUwi : ¬ 2 ∣ ((U.subgroupOf L).map ε.toMonoidHom).index := by
      have := Subgroup.index_map_equiv (U.subgroupOf L) ε
      erw [this]
      exact hU.2.2
    have hBw : ∀ q : ℕ, q.Prime → q ∣ Nat.card ((B.subgroupOf L).map ε.toMonoidHom) →
        q = 2 ∨ q = 3 := by
      intro q hq hqB
      refine hB q hq ?_
      rwa [← Nat.card_congr ((B.subgroupOf L).equivMapOfInjective _ ε.injective).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv] at hqB
    have hyw : orderOf (ε ⟨y, hyL⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
    have hN := janko_mem_normalizer jankoHyp₀ card_walterJ1' hUw hUwi
      (Subgroup.map_mono (Subgroup.subgroupOf_mono L hUB)) hBw
      ((mem_map_subgroupOf_iff' ε ⟨y, hyL⟩).2 hyB) hyw
    intro u hu
    have huw : ε ⟨u, hU.1 hu⟩ ∈ (U.subgroupOf L).map ε.toMonoidHom :=
      (mem_map_subgroupOf_iff' ε _).2 hu
    have h1 := (Subgroup.mem_normalizer_iff.mp hN _).1 huw
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact (mem_map_subgroupOf_iff' ε _).1 h1
  let φ : MulAut ↥L := L.normalizerMonoidHom ⟨g, hgL⟩
  obtain ⟨s, hs⟩ := J3_aut (MulAut.congr ε φ)
  set X : A := ((ε.symm s : ↥L) : A) with hXdef
  have hXL : X ∈ L := (ε.symm s).2
  have hgX : ∀ l ∈ L, g * l * g⁻¹ = X * l * X⁻¹ := by
    intro l hl
    have h1 := congrArg (fun ψ : MulAut CFSG.Open.walterJ1 => ψ (ε ⟨l, hl⟩)) hs
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.conj_apply] at h1
    have h2 : φ ⟨l, hl⟩ = ε.symm s * ⟨l, hl⟩ * (ε.symm s)⁻¹ := by
      rw [← ε.symm_apply_apply (φ ⟨l, hl⟩), h1, map_mul, map_mul, map_inv,
        MulEquiv.symm_apply_apply]
    have h3 := congrArg (fun m : ↥L => (m : A)) h2
    exact h3
  have hgX' : ∀ l ∈ L, g⁻¹ * l * g = X⁻¹ * l * X := by
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) l).1 hl
      rwa [inv_inv] at this
    have := hgX _ hl'
    calc g⁻¹ * l * g = X⁻¹ * (X * (g⁻¹ * l * g) * X⁻¹) * X := by group
      _ = X⁻¹ * (g * (g⁻¹ * l * g) * g⁻¹) * X := by rw [this]
      _ = X⁻¹ * l * X := by group
  have hginvU : ∀ u ∈ U, g⁻¹ * u * g ∈ U := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgU) u).1 hu
    rwa [inv_inv] at this
  have hXU : X ∈ Subgroup.normalizer (U : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [← hgX u (hU.1 hu)]
      exact (Subgroup.mem_normalizer_iff.mp hgU u).1 hu
    · intro hu
      have h1 := hginvU _ hu
      rw [hgX' _ (hU.1 hu)] at h1
      rwa [show X⁻¹ * (X * u * X⁻¹) * X = u by group] at h1
  have hXy : g * y * g⁻¹ = X * y * X⁻¹ := hgX y hyL
  have hgyy : g * y * g⁻¹ ∈ Subgroup.zpowers y :=
    (Subgroup.mem_normalizer_iff.mp hgy y).1 (Subgroup.mem_zpowers y)
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgyy
  have hk' : y ^ k = y ^ (k % 3) := by
    rw [← zpow_mod_orderOf, hy]
    rfl
  have hkr : 0 ≤ k % 3 ∧ k % 3 < 3 := ⟨Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num)⟩
  have hcases : g * y * g⁻¹ = 1 ∨ g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹ := by
    rw [← hk, hk']
    rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
    · left
      rw [h0, zpow_zero]
    · right; left
      rw [h1, zpow_one]
    · right; right
      rw [h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, eq_inv_iff_mul_eq_one, ← pow_succ,
        hy3]
  rcases hcases with h1 | h1 | h1
  · exfalso
    have : y = 1 := by
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, h1]
      group
    rw [this, orderOf_one] at hy
    omega
  · exact h1
  · exfalso
    rw [hXy] at h1
    have hX0 : orderOf X ≠ 0 := (orderOf_pos X).ne'
    obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd hX0
    obtain ⟨j, rfl⟩ := hm
    set z := X ^ (2 * j + 1)
    have hz : z * y * z⁻¹ = y⁻¹ := conj_pow_odd_inv h1 j
    have hz2 : IsPGroup 2 (Subgroup.zpowers z) := by
      refine IsPGroup.of_card (n := a) ?_
      rw [Nat.card_zpowers, orderOf_pow' X (by omega), ham,
        Nat.gcd_mul_left_left]
      exact Nat.mul_div_cancel _ (by omega)
    have hzL : Subgroup.zpowers z ≤ L := Subgroup.zpowers_le.mpr (L.pow_mem hXL _)
    have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (U : Set A) :=
      Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hXU _)
    have hsup2 : IsPGroup 2 (Subgroup.zpowers z ⊔ U : Subgroup A) :=
      hz2.to_sup_of_normal_right' hU.2.1 hzN
    have hle := CFSG.Quasithin.P134.le_of_isSylowTwoOf hU le_sup_right (sup_le hzL hU.1) hsup2
    have hzU : z ∈ U := hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
    have hyU' : y ∈ U := by
      have hmem : z * (y * z⁻¹ * y⁻¹) ∈ U := U.mul_mem hzU (hyU _ (U.inv_mem hzU))
      rwa [show z * (y * z⁻¹ * y⁻¹) = z * y * z⁻¹ * y⁻¹ by group, hz,
        show y⁻¹ * y⁻¹ = y by
          rw [← mul_inv_rev, inv_eq_iff_eq_inv, ← pow_two, eq_inv_iff_mul_eq_one, ← pow_succ, hy3]]
        at hmem
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hU.2.1
    have h3 : 3 ∣ 2 ^ b := hb ▸ hy ▸ Subgroup.orderOf_dvd_natCard U hyU'
    exact absurd h3 (not_three_dvd_two_pow b)

end CFSG.Quasithin.F134
