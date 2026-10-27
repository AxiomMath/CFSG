module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Fit
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Gap6R2.L3

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Setup (T N V P : Subgroup G) : Prop where
  PN : P ≤ N
  Pnorm : N ≤ Subgroup.normalizer (P : Set G)
  P2 : IsPGroup 2 P
  Pmax : ∀ W : Subgroup G, W ≤ N → N ≤ Subgroup.normalizer (W : Set G) → IsPGroup 2 W → W ≤ P
  TN : T ≤ N
  T2 : IsPGroup 2 T
  PT : P ≤ T
  gen : N = oTwoUpper N ⊔ T
  VT : V ≤ T
  TV : T ≤ Subgroup.normalizer (V : Set G)
  ab : ∀ a ∈ N, Odd (orderOf a) → ∀ b ∈ N, Odd (orderOf b) → a * b * a⁻¹ * b⁻¹ ∈ P
  dich : ∀ H : Subgroup G, T ≤ H → H ≤ N →
    (∀ A : Subgroup G, T ≤ A → A ≤ H → A = T ∨ A = H) →
    H ≤ Subgroup.normalizer (V : Set G) ∨
      ∃ W : Subgroup G, V ≤ W ∧ W ≤ H ∧ IsPGroup 2 W ∧ H ≤ Subgroup.normalizer (W : Set G)

omit [Finite G] in
theorem eq_one_of_odd_orderOf_of_pow {H : Type} [Group H] {x : H} (hodd : Odd (orderOf x))
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hm0 : m = 0 := by
    by_contra h
    rw [hm] at hodd
    exact (Nat.not_odd_iff_even.mpr ((Nat.even_pow).mpr ⟨even_two, h⟩)) hodd
  rw [hm0, pow_zero] at hm
  exact orderOf_eq_one_iff.mp hm

omit [Finite G] in
theorem mem_normalizer_sup {P V : Subgroup G} {g : G}
    (hP : g ∈ Subgroup.normalizer (P : Set G)) (hV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer ((P ⊔ V : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hP hV ⊢
  rw [Subgroup.map_sup, hP, hV]

omit [Finite G] in
theorem orderOf_conj_eq {H : Type} [Group H] (n a : H) : orderOf (n * a * n⁻¹) = orderOf a := by
  have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective a
  simpa [MulAut.conj_apply] using this


theorem Setup.le {T N V P : Subgroup G} (S : Setup T N V P) : V ≤ P := by
  classical
  have hQn : (P.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer S.PN).mpr S.Pnorm
  set Q : Subgroup ↥N := P.subgroupOf N with hQ
  let π : ↥N →* ↥N ⧸ Q := QuotientGroup.mk' Q
  have hπker : ∀ y : ↥N, π y = 1 ↔ (y : G) ∈ P := fun y =>
    (QuotientGroup.eq_one_iff y).trans Subgroup.mem_subgroupOf
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hcomm : ∀ a b : ↥N, Odd (orderOf a) → Odd (orderOf b) → π a * π b = π b * π a := by
    intro a b ha hb
    have h : ((a * b * a⁻¹ * b⁻¹ : ↥N) : G) ∈ P := by
      have := S.ab a a.2 (by rw [Subgroup.orderOf_coe]; exact ha) b b.2
        (by rw [Subgroup.orderOf_coe]; exact hb)
      simpa using this
    have h1 : π (a * b * a⁻¹ * b⁻¹) = 1 := (hπker _).mpr h
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h1)
  set O : Set (↥N ⧸ Q) := π '' {a : ↥N | Odd (orderOf a)} with hO
  set Y : Subgroup (↥N ⧸ Q) := Subgroup.closure O with hY
  have hOcomm : ∀ x ∈ O, ∀ y ∈ O, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hcomm a b ha hb
  have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    intro x hx y hy
    have : IsMulCommutative ↥Y :=
      Subgroup.isMulCommutative_closure fun x hx y hy _ => hOcomm x hx y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp this (⟨x, hx⟩ : ↥Y) ⟨y, hy⟩)
  have hOodd : ∀ x ∈ O, Odd (orderOf x) := by
    rintro _ ⟨a, ha, rfl⟩
    exact Odd.of_dvd_nat ha (orderOf_map_dvd π a)
  have hYodd : ∀ x ∈ Y, Odd (orderOf x) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hOodd y hy
    | one => simp
    | mul y z hy hz ihy ihz =>
      exact Odd.of_dvd_nat (ihy.mul ihz)
        ((Commute.orderOf_mul_dvd_lcm (hYc y hy z hz)).trans (Nat.lcm_dvd_mul _ _))
    | inv y hy ih => rwa [orderOf_inv]
  have hYnorm : ∀ g : ↥N ⧸ Q, ∀ x ∈ Y, g * x * g⁻¹ ∈ Y := by
    intro g x hx
    obtain ⟨n, rfl⟩ := hπsurj g
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨n * a * n⁻¹, ?_, ?_⟩
      · show Odd (orderOf (n * a * n⁻¹))
        rwa [orderOf_conj_eq]
      · simp [map_mul, map_inv]
    | one => simp
    | mul y z hy hz ihy ihz =>
      have := Y.mul_mem ihy ihz
      simpa [mul_assoc] using this
    | inv y hy ih =>
      have := Y.inv_mem ih
      simpa [mul_assoc] using this
  set Tb : Subgroup (↥N ⧸ Q) := (T.subgroupOf N).map π with hTb
  set Vb : Subgroup (↥N ⧸ Q) := (V.subgroupOf N).map π with hVb
  have hTb2 : IsPGroup 2 Tb :=
    (S.T2.of_equiv (Subgroup.subgroupOfEquivOfLe S.TN).symm).map π
  have hVTb : Vb ≤ Tb := Subgroup.map_mono fun x hx => S.VT hx
  have hTbY : Tb ≤ Subgroup.normalizer (Y : Set (↥N ⧸ Q)) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hYnorm g x hx, fun hx => ?_⟩
    have := hYnorm g⁻¹ _ hx
    simpa [mul_assoc] using this
  have hTbV : Tb ≤ Subgroup.normalizer (Vb : Set (↥N ⧸ Q)) := by
    have key : ∀ t : ↥N, (t : G) ∈ T → ∀ x ∈ Vb, π t * x * (π t)⁻¹ ∈ Vb := by
      rintro t ht _ ⟨v, hv, rfl⟩
      refine ⟨t * v * t⁻¹, ?_, by simp [map_mul, map_inv]⟩
      have := (Subgroup.mem_normalizer_iff.mp (S.TV ht) (v : G)).mp hv
      show ((t * v * t⁻¹ : ↥N) : G) ∈ V
      simpa using this
    rintro _ ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T := ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t ht' x, fun hx => ?_⟩
    have := key t⁻¹ (by simpa using T.inv_mem ht') _ hx
    simpa [mul_assoc] using this
  have hmin : ∀ B : Subgroup (↥N ⧸ Q), B ≤ Y → B ≠ ⊥ →
      Tb ≤ Subgroup.normalizer (B : Set (↥N ⧸ Q)) →
      (∀ B' : Subgroup (↥N ⧸ Q), B' ≤ B → Tb ≤ Subgroup.normalizer (B' : Set (↥N ⧸ Q)) →
        B' ≠ ⊥ → B' = B) → ⁅B, Vb⁆ = ⊥ := by
    intro B hBY hBne hBn hBmin
    set BG : Subgroup G := (B.comap π).map N.subtype with hBG
    have hmemBG : ∀ x : G, x ∈ BG ↔ ∃ y : ↥N, π y ∈ B ∧ (y : G) = x := by
      intro x
      simp [hBG, Subgroup.mem_map, Subgroup.mem_comap]
    have hBGN : BG ≤ N := Subgroup.map_subtype_le _
    have hPBG : P ≤ BG := fun p hp =>
      (hmemBG p).mpr ⟨⟨p, S.PN hp⟩, by rw [(hπker _).mpr hp]; exact B.one_mem, rfl⟩
    have hconjBG : ∀ t ∈ T, ∀ x ∈ BG, t * x * t⁻¹ ∈ BG := by
      intro t ht x hx
      obtain ⟨y, hy, rfl⟩ := (hmemBG x).mp hx
      refine (hmemBG _).mpr ⟨⟨t, S.TN ht⟩ * y * ⟨t, S.TN ht⟩⁻¹, ?_, by simp⟩
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hBn ⟨⟨t, S.TN ht⟩, ht, rfl⟩) _).mp hy
    have hTBG : T ≤ Subgroup.normalizer (BG : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hconjBG t ht x hx, fun hx => ?_⟩
      have := hconjBG t⁻¹ (T.inv_mem ht) _ hx
      simpa [mul_assoc] using this
    have hHeq : ∀ a ∈ T ⊔ BG, ∃ t ∈ T, ∃ b ∈ BG, a = t * b := by
      intro a ha
      have : a ∈ ((T ⊔ BG : Subgroup G) : Set G) := ha
      rw [Subgroup.coe_mul_of_left_le_normalizer_right T BG hTBG] at this
      obtain ⟨t, ht, b, hb, hab⟩ := Set.mem_mul.mp this
      exact ⟨t, ht, b, hb, hab.symm⟩
    have hminH : ∀ A : Subgroup G, T ≤ A → A ≤ T ⊔ BG → A = T ∨ A = T ⊔ BG := by
      intro A hTA hAH
      set C : Subgroup G := A ⊓ BG with hC
      set B' : Subgroup (↥N ⧸ Q) := (C.subgroupOf N).map π with hB'
      have hCN : C ≤ N := inf_le_right.trans hBGN
      have hB'B : B' ≤ B := by
        rintro _ ⟨c, hc, rfl⟩
        have hc' : (c : G) ∈ C := hc
        obtain ⟨y, hy, hyc⟩ := (hmemBG _).mp hc'.2
        have : y = c := Subtype.ext hyc
        rwa [← this]
      have hB'n : Tb ≤ Subgroup.normalizer (B' : Set (↥N ⧸ Q)) := by
        have key : ∀ t : ↥N, (t : G) ∈ T → ∀ x ∈ B', π t * x * (π t)⁻¹ ∈ B' := by
          rintro t ht _ ⟨c, hc, rfl⟩
          have hc' : (c : G) ∈ C := hc
          refine ⟨t * c * t⁻¹, ?_, by simp [map_mul, map_inv]⟩
          show ((t * c * t⁻¹ : ↥N) : G) ∈ C
          refine ⟨?_, ?_⟩
          · simpa using A.mul_mem (A.mul_mem (hTA ht) hc'.1) (A.inv_mem (hTA ht))
          · simpa using hconjBG t ht _ hc'.2
        rintro _ ⟨t, ht, rfl⟩
        have ht' : (t : G) ∈ T := ht
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨key t ht' x, fun hx => ?_⟩
        have := key t⁻¹ (by simpa using T.inv_mem ht') _ hx
        simpa [mul_assoc] using this
      by_cases hB'bot : B' = ⊥
      · left
        have hCT : C ≤ T := by
          intro c hc
          have hcN : c ∈ N := hCN hc
          have : π ⟨c, hcN⟩ ∈ B' := ⟨⟨c, hcN⟩, hc, rfl⟩
          rw [hB'bot, Subgroup.mem_bot, hπker] at this
          exact S.PT this
        refine le_antisymm (fun a ha => ?_) hTA
        obtain ⟨t, ht, b, hb, rfl⟩ := hHeq a (hAH ha)
        have hbA : b ∈ A := by simpa using A.mul_mem (A.inv_mem (hTA ht)) ha
        exact T.mul_mem ht (hCT ⟨hbA, hb⟩)
      · right
        have hB'eq : B' = B := hBmin B' hB'B hB'n hB'bot
        have hBGA : BG ≤ A := by
          intro b hb
          obtain ⟨y, hy, rfl⟩ := (hmemBG b).mp hb
          have hy' : π y ∈ B' := hB'eq ▸ hy
          obtain ⟨c, hc, hcy⟩ := hy'
          have hcy' : c⁻¹ * y ∈ Q := QuotientGroup.eq.mp hcy
          have hP : (c : G)⁻¹ * (y : G) ∈ P := by
            simpa using Subgroup.mem_subgroupOf.mp hcy'
          have hcA : (c : G) ∈ A := (show (c : G) ∈ C from hc).1
          have : (y : G) = c * ((c : G)⁻¹ * y) := by group
          rw [this]
          exact A.mul_mem hcA (hTA (S.PT hP))
        exact le_antisymm hAH (sup_le hTA hBGA)
    have hdichH := S.dich (T ⊔ BG) le_sup_left (sup_le S.TN hBGN) hminH
    have hcomm' : ∀ x ∈ BG, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ P := by
      intro x hx v hv
      have hxH : x ∈ T ⊔ BG := Subgroup.mem_sup_right hx
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (x * v * x⁻¹ * v⁻¹) ^ 2 ^ k = 1 := by
        rcases hdichH with hnorm | ⟨W, hVW, hWH, hW2, hHW⟩
        · have hxv : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hnorm hxH) v).mp hv
          have hc : x * v * x⁻¹ * v⁻¹ ∈ T := T.mul_mem (S.VT hxv) (T.inv_mem (S.VT hv))
          obtain ⟨k, hk⟩ := S.T2 ⟨_, hc⟩
          exact ⟨k, congrArg Subtype.val hk⟩
        · have hxv : x * v * x⁻¹ ∈ W :=
            (Subgroup.mem_normalizer_iff.mp (hHW hxH) v).mp (hVW hv)
          have hc : x * v * x⁻¹ * v⁻¹ ∈ W := W.mul_mem hxv (W.inv_mem (hVW hv))
          obtain ⟨k, hk⟩ := hW2 ⟨_, hc⟩
          exact ⟨k, congrArg Subtype.val hk⟩
      have hvN : v ∈ N := S.TN (S.VT hv)
      obtain ⟨y, hy, rfl⟩ := (hmemBG x).mp hx
      have hcY : π (y * ⟨v, hvN⟩ * y⁻¹ * ⟨v, hvN⟩⁻¹) ∈ Y := by
        have h1 : π y ∈ Y := hBY hy
        have h2 := hYnorm (π ⟨v, hvN⟩) (π y)⁻¹ (Y.inv_mem h1)
        have := Y.mul_mem h1 h2
        simpa [map_mul, map_inv, mul_assoc] using this
      have hpow : (π (y * ⟨v, hvN⟩ * y⁻¹ * ⟨v, hvN⟩⁻¹)) ^ 2 ^ k = 1 := by
        rw [← map_pow]
        have : (y * ⟨v, hvN⟩ * y⁻¹ * ⟨v, hvN⟩⁻¹ : ↥N) ^ 2 ^ k = 1 :=
          Subtype.ext (by simpa using hk)
        rw [this, map_one]
      have h1 := eq_one_of_odd_orderOf_of_pow (hYodd _ hcY) hpow
      have := (hπker _).mp h1
      simpa using this
    rw [eq_bot_iff, Subgroup.commutator_le]
    rintro b hb _ ⟨u, hu, rfl⟩
    obtain ⟨y, rfl⟩ := hπsurj b
    have hyBG : (y : G) ∈ BG := (hmemBG _).mpr ⟨y, hb, rfl⟩
    have hu' : (u : G) ∈ V := hu
    have hcm := hcomm' (y : G) hyBG (u : G) hu'
    show ⁅π y, π u⁆ ∈ (⊥ : Subgroup _)
    rw [Subgroup.mem_bot, commutatorElement_def]
    have h1 : π (y * u * y⁻¹ * u⁻¹) = 1 := (hπker _).mpr (by simpa using hcm)
    simpa [map_mul, map_inv] using h1
  have hYV : ⁅Y, Vb⁆ = ⊥ := commutator_eq_bot_of_minimal hYc hYodd hTb2 hVTb hTbY hTbV hmin
  have hoddcomm : ∀ a ∈ N, Odd (orderOf a) → ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ P := by
    intro a ha hoa v hv
    have hvN : v ∈ N := S.TN (S.VT hv)
    have hπa : π ⟨a, ha⟩ ∈ Y :=
      Subgroup.subset_closure ⟨⟨a, ha⟩, by
        show Odd (orderOf (⟨a, ha⟩ : ↥N))
        rwa [← Subgroup.orderOf_coe], rfl⟩
    have hπv : π ⟨v, hvN⟩ ∈ Vb := ⟨⟨v, hvN⟩, hv, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYV) hπa) _ hπv
    have h1 : π (⟨a, ha⟩ * ⟨v, hvN⟩ * ⟨a, ha⟩⁻¹ * ⟨v, hvN⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have : π ⟨a, ha⟩ * π ⟨v, hvN⟩ = π ⟨v, hvN⟩ * π ⟨a, ha⟩ := hc.symm
      rw [this]
      group
    have := (hπker _).mp h1
    simpa using this
  have hfwd : ∀ a ∈ N, Odd (orderOf a) → ∀ w ∈ P ⊔ V, a * w * a⁻¹ ∈ P ⊔ V := by
    intro a ha hoa
    have hle : P ⊔ V ≤ (P ⊔ V).comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (fun p hp => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_sup_left (by
          have := (Subgroup.mem_normalizer_iff.mp (S.Pnorm ha) p).mp hp
          simpa using this)
      · have h1 : a * v * a⁻¹ * v⁻¹ ∈ P ⊔ V := Subgroup.mem_sup_left (hoddcomm a ha hoa v hv)
        have h2 := (P ⊔ V).mul_mem h1 (Subgroup.mem_sup_right hv : v ∈ P ⊔ V)
        show a * v * a⁻¹ ∈ P ⊔ V
        simpa using h2
    intro w hw
    exact hle hw
  have hodd_norm : ∀ a ∈ N, Odd (orderOf a) →
      a ∈ Subgroup.normalizer ((P ⊔ V : Subgroup G) : Set G) := by
    intro a ha hoa
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hfwd a ha hoa w hw, fun hw => ?_⟩
    have hoa' : Odd (orderOf a⁻¹) := by rwa [orderOf_inv]
    have := hfwd a⁻¹ (N.inv_mem ha) hoa' _ hw
    simpa [mul_assoc] using this
  have hWN : P ⊔ V ≤ N := sup_le S.PN (S.VT.trans S.TN)
  have hNW : N ≤ Subgroup.normalizer ((P ⊔ V : Subgroup G) : Set G) := by
    calc N = oTwoUpper N ⊔ T := S.gen
      _ ≤ _ := by
        refine sup_le ((Subgroup.closure_le _).mpr fun a ha => hodd_norm a ha.1 ha.2) ?_
        intro t ht
        exact mem_normalizer_sup (S.Pnorm (S.TN ht)) (S.TV ht)
  have hVNP : V ≤ Subgroup.normalizer (P : Set G) := (S.VT.trans S.TN).trans S.Pnorm
  have hW2 : IsPGroup 2 (P ⊔ V : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' S.P2 (S.T2.to_le S.VT) hVNP
  exact le_sup_right.trans (S.Pmax _ hWN hNW hW2)

end CFSG.Quasithin.Gap6R2.L3
