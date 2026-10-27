module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ShultStronglyClosedTI.LinearChain.CharacterSetup

variable {G : Type*} [Group G]

theorem eq_one_of_odd_orderOf_mul {Q J : Subgroup G}
    (hJQ : J ≤ Subgroup.centralizer (Q : Set G)) (hQJ : Q ⊓ J = ⊥) (hQ2 : IsPGroup 2 Q)
    {c w : G} (hc : c ∈ Q) (hw : w ∈ J) (hodd : Odd (orderOf (c * w))) : c = 1 := by
  set n := orderOf (c * w)
  have hcomm : Commute c w := Subgroup.mem_centralizer_iff.mp (hJQ hw) c hc
  have hpow : c ^ n * w ^ n = 1 := by
    rw [← hcomm.mul_pow, pow_orderOf_eq_one]
  have hcn : c ^ n ∈ Q ⊓ J := by
    refine ⟨Q.pow_mem hc n, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hpow]
    exact J.inv_mem (J.pow_mem hw n)
  rw [hQJ, Subgroup.mem_bot] at hcn
  have hdvd : orderOf c ∣ n := orderOf_dvd_of_pow_eq_one hcn
  obtain ⟨m, hm⟩ := hQ2 ⟨c, hc⟩
  have hdvd2 : orderOf c ∣ 2 ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (orderOf c) n :=
    (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)).coprime_dvd_left hdvd2
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem mk'_eq_one_iff {C Q : Subgroup G} [(Q.subgroupOf C).Normal] (x : C) :
    QuotientGroup.mk' (Q.subgroupOf C) x = 1 ↔ (x : G) ∈ Q := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mk'_injOn {C Q J : Subgroup G} [(Q.subgroupOf C).Normal] (hQJ : Q ⊓ J = ⊥)
    {a b : C} (ha : (a : G) ∈ J) (hb : (b : G) ∈ J)
    (hab : QuotientGroup.mk' (Q.subgroupOf C) a = QuotientGroup.mk' (Q.subgroupOf C) b) :
    a = b := by
  have h : QuotientGroup.mk' (Q.subgroupOf C) (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  have hmem : ((a⁻¹ * b : C) : G) ∈ Q ⊓ J := by
    refine ⟨(mk'_eq_one_iff _).mp h, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact J.mul_mem (J.inv_mem ha) hb
  rw [hQJ, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp (Subtype.ext hmem)

theorem orderOf_mk'_of_mem {C Q J : Subgroup G} [(Q.subgroupOf C).Normal] (hQJ : Q ⊓ J = ⊥)
    {b : C} (hb : (b : G) ∈ J) :
    orderOf (QuotientGroup.mk' (Q.subgroupOf C) b) = orderOf (b : G) := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow, mk'_eq_one_iff, Subgroup.coe_pow]
  constructor
  · intro h
    have hmem : (b : G) ^ n ∈ Q ⊓ J := ⟨h, J.pow_mem hb n⟩
    rwa [hQJ, Subgroup.mem_bot] at hmem
  · intro h
    rw [h]
    exact Q.one_mem

theorem card_map_mk'_of_le {C Q J X : Subgroup G} [(Q.subgroupOf C).Normal] (hJC : J ≤ C)
    (hQJ : Q ⊓ J = ⊥) (hXJ : X ≤ J) :
    Nat.card ((X.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C))) = Nat.card X := by
  have hXC : X ≤ C := hXJ.trans hJC
  let ψ : X →* ↥C ⧸ Q.subgroupOf C :=
    (QuotientGroup.mk' (Q.subgroupOf C)).comp (Subgroup.inclusion hXC)
  have hψ : Function.Injective ψ := fun a b hab =>
    Subgroup.inclusion_injective hXC (mk'_injOn (C := C) (a := Subgroup.inclusion hXC a)
      (b := Subgroup.inclusion hXC b) hQJ (hXJ a.2) (hXJ b.2) hab)
  have hrange : (X.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)) = ψ.range := by
    ext x
    constructor
    · rintro ⟨⟨w, hwC⟩, hwX, rfl⟩
      exact ⟨⟨w, hwX⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨Subgroup.inclusion hXC w, w.2, rfl⟩
  rw [hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm

theorem quotient_torus_basic {C Q J W : Subgroup G} [(Q.subgroupOf C).Normal] (hJC : J ≤ C)
    (hQJ : Q ⊓ J = ⊥) (hWJ : W ≤ J) [IsCyclic W] (u : C) (huJ : (u : G) ∈ J)
    (hu2 : orderOf (u : G) = 2) (huW : (u : G) ∉ W)
    (hinv : ∀ w ∈ W, (u : G) * w * (u : G)⁻¹ = w⁻¹) :
    IsCyclic ((W.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C))) ∧
      Nat.card ((W.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C))) = Nat.card W ∧
      orderOf (QuotientGroup.mk' (Q.subgroupOf C) u) = 2 ∧
      QuotientGroup.mk' (Q.subgroupOf C) u ∉
        (W.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)) ∧
      ∀ w ∈ (W.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)),
        (QuotientGroup.mk' (Q.subgroupOf C) u)⁻¹ * w * QuotientGroup.mk' (Q.subgroupOf C) u =
          w⁻¹ := by
  set π := QuotientGroup.mk' (Q.subgroupOf C)
  have hWC : W ≤ C := hWJ.trans hJC
  have hu1 : (u : G) ^ 2 = 1 := by rw [← hu2, pow_orderOf_eq_one]
  have huinv : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hu1])
  refine ⟨?_, card_map_mk'_of_le hJC hQJ hWJ, (orderOf_mk'_of_mem hQJ huJ).trans hu2, ?_, ?_⟩
  · have : IsCyclic (W.subgroupOf C) :=
      isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hWC).symm.surjective
    exact isCyclic_of_surjective _ (π.subgroupMap_surjective (W.subgroupOf C))
  · rintro ⟨⟨w, hwC⟩, hwW, hw⟩
    have hwW' : w ∈ W := hwW
    apply huW
    have h := mk'_injOn (C := C) (a := u) (b := ⟨w, hwC⟩) hQJ huJ (hWJ hwW') hw.symm
    rw [h]
    exact hwW'
  · rintro _ ⟨⟨w, hwC⟩, hwW, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [huinv]
    nth_rw 2 [← huinv]
    exact hinv w hwW

theorem quotient_torus_centralizer_normalizer {C Q J W : Subgroup G} [(Q.subgroupOf C).Normal]
    (hJC : J ≤ C) (hJQ : J ≤ Subgroup.centralizer (Q : Set G)) (hQJ : Q ⊓ J = ⊥)
    (hQ2 : IsPGroup 2 Q) (hWJ : W ≤ J) (hWodd : Odd (Nat.card W))
    (hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (u : C) (hu2 : orderOf (u : G) = 2)
    (hinv : ∀ w ∈ W, (u : G) * w * (u : G)⁻¹ = w⁻¹)
    (hW : ∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ →
      J ⊓ Subgroup.centralizer (W₀ : Set G) = W ∧
      J ⊓ Subgroup.normalizer (W₀ : Set G) = W ⊔ Subgroup.zpowers (u : G) ∧
      C ⊓ Subgroup.normalizer (W₀ : Set G) ≤ Q ⊔ J)
    (W₀ : Subgroup (↥C ⧸ Q.subgroupOf C))
    (hW₀ : W₀ ≤ (W.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C))) (hW₀ne : W₀ ≠ ⊥) :
    Subgroup.centralizer (W₀ : Set (↥C ⧸ Q.subgroupOf C)) =
        (W.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)) ∧
      Subgroup.normalizer (W₀ : Set (↥C ⧸ Q.subgroupOf C)) =
        (W.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)) ⊔
          Subgroup.zpowers (QuotientGroup.mk' (Q.subgroupOf C) u) := by
  set π := QuotientGroup.mk' (Q.subgroupOf C)
  set Wbar := (W.subgroupOf C).map π
  have hWC : W ≤ C := hWJ.trans hJC
  have hu1 : (u : G) ^ 2 = 1 := by rw [← hu2, pow_orderOf_eq_one]
  have huinv : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hu1])
  have hWorder : ∀ w ∈ W, Odd (orderOf w) := fun w hw => by
    have h := orderOf_dvd_natCard (⟨w, hw⟩ : W)
    rw [Subgroup.orderOf_mk] at h
    exact hWodd.of_dvd_nat h
  let W₀G : Subgroup G := (W₀.comap (π.comp (Subgroup.inclusion hWC))).map W.subtype
  have hmem : ∀ w : G, w ∈ W₀G ↔ ∃ hw : w ∈ W, π ⟨w, hWC hw⟩ ∈ W₀ := by
    intro w
    constructor
    · rintro ⟨⟨w, hw⟩, hw₀, rfl⟩
      exact ⟨hw, hw₀⟩
    · rintro ⟨hw, hw₀⟩
      exact ⟨⟨w, hw⟩, hw₀, rfl⟩
  have hW₀GW : W₀G ≤ W := fun w hw => ((hmem w).mp hw).1
  have hW₀GJ : W₀G ≤ J := hW₀GW.trans hWJ
  have hsurj : ∀ x ∈ W₀, ∃ w ∈ W₀G, ∃ hw : w ∈ C, π ⟨w, hw⟩ = x := by
    intro x hx
    obtain ⟨⟨w, hwC⟩, hwW, rfl⟩ := hW₀ hx
    exact ⟨w, (hmem w).mpr ⟨hwW, hx⟩, hwC, rfl⟩
  have hW₀Gne : W₀G ≠ ⊥ := by
    intro hbot
    apply hW₀ne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨w, hw, hwC, rfl⟩ := hsurj x hx
    rw [hbot, Subgroup.mem_bot] at hw
    subst hw
    exact (mk'_eq_one_iff _).mpr Q.one_mem
  obtain ⟨hWC₀, hWN₀, hCN₀⟩ := hW W₀G hW₀GW hW₀Gne
  have hcore : ∀ (y : C) (w w' : G) (hw : w ∈ W) (hw' : w' ∈ J),
      π (y * ⟨w, hWC hw⟩ * y⁻¹) = π ⟨w', hJC hw'⟩ → (y : G) * w * (y : G)⁻¹ = w' := by
    intro y w w' hw hw' heq
    have hc : (y : G) * w * (y : G)⁻¹ * w'⁻¹ ∈ Q := by
      have h1 : π (y * ⟨w, hWC hw⟩ * y⁻¹ * (⟨w', hJC hw'⟩ : C)⁻¹) = 1 := by
        rw [map_mul π _ _⁻¹, heq, map_inv, mul_inv_cancel]
      exact (mk'_eq_one_iff _).mp h1
    have hodd : Odd (orderOf ((y : G) * w * (y : G)⁻¹ * w'⁻¹ * w')) := by
      rw [inv_mul_cancel_right, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hWorder w hw
    have h1 := eq_one_of_odd_orderOf_mul hJQ hQJ hQ2 hc hw' hodd
    rw [mul_inv_eq_one] at h1
    exact h1
  have hconj : ∀ y : C, π y ∈ Subgroup.normalizer (W₀ : Set (↥C ⧸ Q.subgroupOf C)) →
      ∀ w ∈ W₀G, (y : G) * w * (y : G)⁻¹ ∈ W₀G := by
    intro y hy w hw
    obtain ⟨hwW, hwW₀⟩ := (hmem w).mp hw
    have h1 : π (y * ⟨w, hWC hwW⟩ * y⁻¹) ∈ W₀ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy _).mp hwW₀
    obtain ⟨w', hw', hw'C, hw'eq⟩ := hsurj _ h1
    rw [hcore y w w' hwW (hW₀GJ hw') hw'eq.symm]
    exact hw'
  have hnorm : ∀ x : C, π x ∈ Subgroup.normalizer (W₀ : Set (↥C ⧸ Q.subgroupOf C)) →
      (x : G) ∈ Subgroup.normalizer (W₀G : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj x hx h, fun hh => ?_⟩
    have h1 := hconj x⁻¹ (by rw [map_inv]; exact inv_mem hx) _ hh
    rwa [Subgroup.coe_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
      mul_assoc, inv_mul_cancel, mul_one] at h1
  have hQcent : ∀ a ∈ Q, a ∈ Subgroup.centralizer (W₀G : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hJQ (hW₀GJ hw)) a ha).symm
  have hJnorm : J ≤ Subgroup.normalizer (Q : Set G) :=
    hJQ.trans (Subgroup.centralizer_le_normalizer _)
  have hdecomp : ∀ x : C, (x : G) ∈ Subgroup.normalizer (W₀G : Set G) →
      ∃ a ∈ Q, ∃ b ∈ J, ∃ hb : b ∈ C, π x = π ⟨b, hb⟩ ∧ (x : G) = a * b := by
    intro x hx
    have hxQJ : (x : G) ∈ Q ⊔ J := hCN₀ ⟨x.2, hx⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Q J hJnorm] at hxQJ
    obtain ⟨a, ha, b, hb, hab⟩ := hxQJ
    have hbC : b ∈ C := hJC hb
    have haC : a ∈ C := by
      have : a = (x : G) * b⁻¹ := by rw [← hab, mul_inv_cancel_right]
      rw [this]
      exact C.mul_mem x.2 (C.inv_mem hbC)
    refine ⟨a, ha, b, hb, hbC, ?_, hab.symm⟩
    have hx' : x = ⟨a, haC⟩ * ⟨b, hbC⟩ := Subtype.ext hab.symm
    rw [hx', map_mul, (mk'_eq_one_iff _).mpr ha, one_mul]
  have hWbarcomm : ∀ a ∈ Wbar, ∀ b ∈ Wbar, a * b = b * a := by
    rintro _ ⟨⟨a, haC⟩, haW, rfl⟩ _ ⟨⟨b, hbC⟩, hbW, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hWcomm a haW b hbW)
  have hubar : ∀ h ∈ Wbar, π u * h * (π u)⁻¹ = h⁻¹ := by
    rintro _ ⟨⟨w, hwC⟩, hwW, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hinv w hwW
  have hubar2 : π u * π u = 1 := by
    rw [← map_mul]
    apply (mk'_eq_one_iff _).mpr
    rw [Subgroup.coe_mul, ← pow_two, hu1]
    exact Q.one_mem
  have hWbarC : Wbar ≤ Subgroup.centralizer (W₀ : Set (↥C ⧸ Q.subgroupOf C)) :=
    fun y hy => Subgroup.mem_centralizer_iff.mpr fun h hh => hWbarcomm h (hW₀ hh) y hy
  have huN : π u ∈ Subgroup.normalizer (W₀ : Set (↥C ⧸ Q.subgroupOf C)) := by
    have hfwd : ∀ h ∈ W₀, π u * h * (π u)⁻¹ ∈ W₀ := fun h hh => by
      rw [hubar h (hW₀ hh)]
      exact inv_mem hh
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have h1 := hfwd _ hh
    have hinvu : (π u)⁻¹ = π u := inv_eq_of_mul_eq_one_right hubar2
    rwa [hinvu, ← mul_assoc, ← mul_assoc, hubar2, one_mul, mul_assoc, hubar2, mul_one] at h1
  constructor
  ·
    refine le_antisymm (fun xbar hxbar => ?_) hWbarC
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf C) xbar
    have hxcent : (x : G) ∈ Subgroup.centralizer (W₀G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨hwW, hwW₀⟩ := (hmem w).mp hw
      have heq : π (x * ⟨w, hWC hwW⟩ * x⁻¹) = π ⟨w, hJC (hWJ hwW)⟩ := by
        rw [map_mul, map_mul, map_inv,
          (Subgroup.mem_centralizer_iff.mp hxbar _ hwW₀).symm, mul_inv_cancel_right]
      exact (mul_inv_eq_iff_eq_mul.mp (hcore x w w hwW (hWJ hwW) heq)).symm
    obtain ⟨a, ha, b, hb, hbC, hxb, hab⟩ :=
      hdecomp x (Subgroup.centralizer_le_normalizer _ hxcent)
    have hbcent : b ∈ Subgroup.centralizer (W₀G : Set G) := by
      have : b = a⁻¹ * (x : G) := by rw [hab, inv_mul_cancel_left]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQcent a ha)) hxcent
    have hbW : b ∈ W := by
      rw [← hWC₀]
      exact ⟨hb, hbcent⟩
    rw [hxb]
    exact ⟨⟨b, hbC⟩, hbW, rfl⟩
  ·
    refine le_antisymm (fun xbar hxbar => ?_)
      (sup_le (hWbarC.trans (Subgroup.centralizer_le_normalizer _))
        (Subgroup.zpowers_le.mpr huN))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf C) xbar
    have hxnorm := hnorm x hxbar
    obtain ⟨a, ha, b, hb, hbC, hxb, hab⟩ := hdecomp x hxnorm
    have hbnorm : b ∈ Subgroup.normalizer (W₀G : Set G) := by
      have : b = a⁻¹ * (x : G) := by rw [hab, inv_mul_cancel_left]
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ (hQcent a ha))) hxnorm
    have hbWu : b ∈ W ⊔ Subgroup.zpowers (u : G) := by
      rw [← hWN₀]
      exact ⟨hb, hbnorm⟩
    have huWnorm : Subgroup.zpowers (u : G) ≤ Subgroup.normalizer (W : Set G) := by
      apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => by rw [hinv h hh]; exact W.inv_mem hh, fun hh => ?_⟩
      have h1 := hinv _ hh
      have hh' : (u : G) * h * (u : G) ∈ W := by rwa [huinv] at hh
      rw [huinv, show (u : G) * ((u : G) * h * (u : G)) * (u : G) =
        ((u : G) * (u : G)) * h * ((u : G) * (u : G)) by group, ← pow_two, hu1, one_mul,
        mul_one] at h1
      rw [h1]
      exact W.inv_mem hh'
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left W _ huWnorm] at hbWu
    obtain ⟨w, hwW, v, hv, hwv⟩ := hbWu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hb' : (⟨b, hbC⟩ : C) = ⟨w, hWC hwW⟩ * u ^ n := by
      subst hwv
      rfl
    rw [hxb, hb', map_mul, map_zpow]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨w, hWC hwW⟩, hwW, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ n))

end CFSG.ShultStronglyClosedTI.LinearChain.CharacterSetup
