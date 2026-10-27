module

public import CFSG.Quasithin.Recognition.RuTypeJ27e
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.Quasithin.Recognition.RuTypeJ27b
public import CFSG.Quasithin.Recognition.RuTypeJ27d

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

noncomputable abbrev P5 (b : G) : Subgroup G := (O5 b).map (G5 b).subtype

theorem card_P5 [Finite G] (b : G) : Nat.card (P5 b) = Nat.card (O5 b) :=
  Subgroup.card_map_of_injective Subtype.val_injective

theorem P5_odd [Finite G] (b : G) : Odd (Nat.card (P5 b)) := by
  rw [card_P5]; exact O5_odd b

theorem P5_le_G5 (b : G) : P5 b ≤ G5 b := Subgroup.map_subtype_le _

theorem conj_mem_P5 {b g x : G} (hg : g ∈ G5 b) (hx : x ∈ P5 b) : g * x * g⁻¹ ∈ P5 b := by
  obtain ⟨y, hy, rfl⟩ := hx
  have := (CFSG.oddCore_normal (G := G5 b)).conj_mem y hy ⟨g, hg⟩
  exact ⟨_, this, rfl⟩

theorem conj_mem_P5_of_inv [Finite G] {b c x : G} (hc : c * b * c⁻¹ = b⁻¹) (hx : x ∈ P5 b) :
    c * x * c⁻¹ ∈ P5 b := by
  have hc' : c⁻¹ * b * c = b⁻¹ := by
    have h1 : c * b⁻¹ * c⁻¹ = b := by
      rw [show c * b⁻¹ * c⁻¹ = (c * b * c⁻¹)⁻¹ by group, hc, inv_inv]
    calc c⁻¹ * b * c = c⁻¹ * (c * b⁻¹ * c⁻¹) * c := by rw [h1]
      _ = b⁻¹ := by group
  have hmem : ∀ g ∈ G5 b, c * g * c⁻¹ ∈ G5 b := by
    intro g hg
    rw [mem_G5] at hg ⊢
    have hgi : g * b⁻¹ = b⁻¹ * g := (Commute.inv_right hg).eq
    calc c * g * c⁻¹ * b = c * (g * (c⁻¹ * b * c)) * c⁻¹ := by group
      _ = c * (g * b⁻¹) * c⁻¹ := by rw [hc']
      _ = c * (b⁻¹ * g) * c⁻¹ := by rw [hgi]
      _ = (c * b⁻¹ * c⁻¹) * (c * g * c⁻¹) := by group
      _ = b * (c * g * c⁻¹) := by
          rw [show c * b⁻¹ * c⁻¹ = (c * b * c⁻¹)⁻¹ by group, hc, inv_inv]
  have hmem' : ∀ g ∈ G5 b, c⁻¹ * g * c ∈ G5 b := by
    intro g hg
    rw [mem_G5] at hg ⊢
    have hgi : g * b⁻¹ = b⁻¹ * g := (Commute.inv_right hg).eq
    have hcb : c * b * c⁻¹ = b⁻¹ := hc
    calc c⁻¹ * g * c * b = c⁻¹ * (g * (c * b * c⁻¹)) * c := by group
      _ = c⁻¹ * (g * b⁻¹) * c := by rw [hcb]
      _ = c⁻¹ * (b⁻¹ * g) * c := by rw [hgi]
      _ = (c⁻¹ * b⁻¹ * c) * (c⁻¹ * g * c) := by group
      _ = b * (c⁻¹ * g * c) := by
          rw [show c⁻¹ * b⁻¹ * c = (c⁻¹ * b * c)⁻¹ by group, hc', inv_inv]
  let α : G5 b ≃* G5 b :=
    { toFun := fun g => ⟨c * g * c⁻¹, hmem g g.2⟩
      invFun := fun g => ⟨c⁻¹ * g * c, hmem' g g.2⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun g => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun g h => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨_, oddCore_map α hy, rfl⟩

theorem eq_zpowers_of_centralizer {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    {x : X} (hx : orderOf x = p) (hC : ¬ p ^ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)))
    {S : Subgroup X} (hS : IsPGroup p S) (hxS : Subgroup.zpowers x ≤ S) :
    S = Subgroup.zpowers x := by
  classical
  by_contra hne
  have hlt : (Subgroup.zpowers x).subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun y hy => ?_) hxS
    have : (⟨y, hy⟩ : S) ∈ (Subgroup.zpowers x).subgroupOf S := htop ▸ Subgroup.mem_top _
    exact this
  have hnil : Group.IsNilpotent S := hS.isNilpotent
  obtain ⟨y, hyN, hyT⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyx : (y : X) * x * (y : X)⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.mp hyN ⟨x, hxS (Subgroup.mem_zpowers x)⟩).mp
      (Subgroup.mem_zpowers x)
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).mpr hyx
  obtain ⟨m, hm⟩ := hS y
  have hm' : (y : X) ^ p ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hiter : ∀ n : ℕ, (y : X) ^ n * x * ((y : X) ^ n)⁻¹ = x ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (y : X) ^ (n + 1) * x * ((y : X) ^ (n + 1))⁻¹ =
          (y : X) * ((y : X) ^ n * x * ((y : X) ^ n)⁻¹) * (y : X)⁻¹ := by
            rw [pow_succ']; group
        _ = (y : X) * x ^ (k ^ n) * (y : X)⁻¹ := by rw [ih]
        _ = ((y : X) * x * (y : X)⁻¹) ^ (k ^ n) := by rw [conj_pow]
        _ = x ^ (k ^ (n + 1)) := by rw [← hk, ← pow_mul, pow_succ, mul_comm]
  have hferm : k ^ p ^ m % p = k % p := by
    have h := ZMod.pow_card (p := p) (k : ZMod p)
    have hpow : ∀ n : ℕ, ((k : ZMod p)) ^ p ^ n = (k : ZMod p) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_mul, ih, h]
    have := hpow m
    rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff'] at this
    exact this
  have hyxx : (y : X) * x * (y : X)⁻¹ = x := by
    have h1 := hiter (p ^ m)
    rw [hm', one_mul, inv_one, mul_one] at h1
    rw [← hk]
    calc x ^ k = x ^ (k % orderOf x) := (pow_mod_orderOf x k).symm
      _ = x ^ (k ^ p ^ m % orderOf x) := by rw [hx, hferm]
      _ = x ^ (k ^ p ^ m) := pow_mod_orderOf x _
      _ = x := h1.symm
  have hyC : (y : X) ∈ Subgroup.centralizer ({x} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : X) * x = (y : X) * x * (y : X)⁻¹ * y := by group
      _ = x * y := by rw [hyxx]
  set K := S ⊓ Subgroup.centralizer ({x} : Set X)
  have hxK : Subgroup.zpowers x ≤ K := le_inf hxS (by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff])
  have hKlt : Subgroup.zpowers x < K := lt_of_le_of_ne hxK (fun h => hyT (by
    have : (y : X) ∈ K := ⟨y.2, hyC⟩
    rw [← h] at this
    exact this))
  have hKp : IsPGroup p K := hS.to_le inf_le_left
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hKp
  have hlt' : p < Nat.card K := by
    rw [← hx, ← Nat.card_zpowers]
    exact Subgroup.card_lt_of_lt hKlt
  have hj2 : 2 ≤ j := by
    rw [hj] at hlt'
    by_contra h
    push Not at h
    interval_cases j
    · simp at hlt'; exact absurd hlt' (by have := hp.out.one_lt; omega)
    · simp at hlt'
  apply hC
  have hdvd : Nat.card K ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hj] at hdvd
  exact (pow_dvd_pow p hj2).trans hdvd

theorem eq_one_of_zpowers_comm_inv {b i x : G} (hb5 : orderOf b = 5) (hib : i * b * i⁻¹ = b⁻¹)
    (hx : x ∈ Subgroup.zpowers b) (hxi : i * x = x * i) : x = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : i * b ^ k * i⁻¹ = (b ^ k)⁻¹ := by rw [← conj_zpow, hib, inv_zpow]
  have h2 : i * b ^ k * i⁻¹ = b ^ k := by rw [hxi, mul_inv_cancel_right]
  have h3 : (b ^ k) ^ 2 = 1 := by
    rw [pow_two]
    calc b ^ k * b ^ k = b ^ k * (i * b ^ k * i⁻¹) := by rw [h2]
      _ = b ^ k * (b ^ k)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  have h5 : (b ^ k) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_five_of_orderOf hb5,
      one_zpow]
  have := (pow_gcd_eq_one (a := b ^ k)).mpr ⟨h5, h3⟩
  rwa [show Nat.gcd 5 2 = 1 by norm_num, pow_one] at this

namespace RuDataM

variable (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

omit [Finite G] hbH in
theorem b_mem_P5 : b ∈ P5 b := by
  have hn : (Subgroup.zpowers (⟨b, mem_G5.mpr rfl⟩ : G5 b)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hc : (g : G) * b = b * g := mem_G5.mp g.2
    have hbg : g * ⟨b, mem_G5.mpr rfl⟩ * g⁻¹ = ⟨b, mem_G5.mpr rfl⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [hc, mul_inv_cancel_right])
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hbg]
    exact Subgroup.zpow_mem_zpowers _ _
  have ho : Odd (Nat.card (Subgroup.zpowers (⟨b, mem_G5.mpr rfl⟩ : G5 b))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hb5]
    decide
  have hle : Subgroup.zpowers (⟨b, mem_G5.mpr rfl⟩ : G5 b) ≤ O5 b := le_sSup ⟨hn, ho⟩
  exact ⟨_, hle (Subgroup.mem_zpowers _), rfl⟩

omit [Finite G] hbH in
theorem zpowers_le_P5 : Subgroup.zpowers b ≤ P5 b := by
  rw [Subgroup.zpowers_le]
  exact b_mem_P5 hb5

theorem eq_one_of_P5_T5
    {x : G} (hxP : x ∈ P5 b) (hxT : x ∈ M.T5 b) : x = 1 := by
  have hc : Nat.Coprime (Nat.card (P5 b)) (Nat.card (M.T5 b)) := by
    rw [card_T5 hbH hb5, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_right 3 (P5_odd b).coprime_two_right
  exact eq_one_of_mem_coprime hc hxP hxT

theorem mem_zpowers_of_P5_comm_z
    {x : G} (hxP : x ∈ P5 b) (hxz : x * M.z = M.z * x) :
    x ∈ Subgroup.zpowers b := by
  have hxH : x ∈ ruH M.T := M.mem_H_iff_comm.mpr hxz.symm
  obtain ⟨t, ht, c, hc, rfl⟩ := CH5_eq_mul hbH hb5 ⟨hxH, P5_le_G5 b hxP⟩
  have htP : t ∈ P5 b := by
    have e : t = c⁻¹ * (c * t) := by group
    rw [e]
    exact mul_mem (inv_mem (zpowers_le_P5 hb5 hc)) hxP
  rw [eq_one_of_P5_T5 hbH hb5 htP ht, mul_one]
  exact hc

theorem card_P5_eq
    {i t : G} (hiH : i ∈ ruH M.T) (hi2 : i * i = 1) (hib : i * b * i⁻¹ = b⁻¹)
    (ht : t ∈ M.T5 b) (hti : t * i * t⁻¹ = i * M.z) :
    Nat.card (P5 b) =
      5 * Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) ^ 2 := by
  classical
  have hz2 := M.z_mul_self
  have hiz : i * M.z = M.z * i := (M.Z_comm_H M.z_mem_Z hiH).symm
  have hzb : M.z * b = b * M.z := M.Z_comm_H M.z_mem_Z hbH
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb5; norm_num at hb5
  have hi1 : i ≠ 1 := fun h => hb1 (eq_one_of_zpowers_comm_inv hb5 hib
    (Subgroup.mem_zpowers b) (by rw [h, one_mul, mul_one]))
  have hiz1 : i ≠ M.z := fun h => hb1 (eq_one_of_zpowers_comm_inv hb5 hib
    (Subgroup.mem_zpowers b) (by rw [h]; exact hzb))
  set E := fourSub i M.z hi2 hz2 hiz
  have : IsKleinFour E := isKleinFour_fourSub hi2 hz2 hiz hi1 M.z_ne_one hiz1
  have hzG : M.z ∈ G5 b := mem_G5.mpr hzb
  have hiinv : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hzinv : M.z⁻¹ = M.z := inv_eq_of_mul_eq_one_right hz2
  have hiN : i ∈ Subgroup.normalizer (P5 b : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨conj_mem_P5_of_inv hib, fun h => ?_⟩
    have := conj_mem_P5_of_inv hib h
    rwa [show i * (i * x * i⁻¹) * i⁻¹ = x by
      calc i * (i * x * i⁻¹) * i⁻¹ = (i * i) * x * (i * i)⁻¹ := by group
        _ = x := by rw [hi2]; group] at this
  have hzN : M.z ∈ Subgroup.normalizer (P5 b : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨conj_mem_P5 hzG, fun h => ?_⟩
    have := conj_mem_P5 hzG h
    rwa [show M.z * (M.z * x * M.z⁻¹) * M.z⁻¹ = x by
      rw [hzinv]
      calc M.z * (M.z * x * M.z) * M.z = (M.z * M.z) * x * (M.z * M.z) := by group
        _ = x := by rw [hz2]; group] at this
  have hnorm : E ≤ Subgroup.normalizer (P5 b : Set G) := by
    intro x hx
    rcases mem_fourSub.mp hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hiN
    · exact hzN
    · exact mul_mem hiN hzN
  have hiE : i ∈ E := mem_fourSub.mpr (Or.inr (Or.inl rfl))
  have hzE : M.z ∈ E := mem_fourSub.mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (P5_odd b) hnorm hiE hzE
    hi1 M.z_ne_one hiz1
  have hCE : Nat.card (P5 b ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    rintro x ⟨hxP, hxE⟩
    rw [Subgroup.mem_bot]
    have hxz : x * M.z = M.z * x :=
      ((Subgroup.mem_centralizer_iff.mp hxE) M.z hzE).symm
    have hxi : i * x = x * i := (Subgroup.mem_centralizer_iff.mp hxE) i hiE
    exact eq_one_of_zpowers_comm_inv hb5 hib
      (mem_zpowers_of_P5_comm_z hbH hb5 hxP hxz) hxi
  have hCz : Nat.card (P5 b ⊓ Subgroup.centralizer ({M.z} : Set G) : Subgroup G) = 5 := by
    have heq : P5 b ⊓ Subgroup.centralizer ({M.z} : Set G) = Subgroup.zpowers b := by
      refine le_antisymm (fun x hx => ?_) (le_inf (zpowers_le_P5 hb5) ?_)
      · exact mem_zpowers_of_P5_comm_z hbH hb5 hx.1
          (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hzb.symm
    rw [heq, Nat.card_zpowers, hb5]
  have htG : t ∈ G5 b := ht.2
  have hCiz : Nat.card (P5 b ⊓ Subgroup.centralizer ({i * M.z} : Set G) : Subgroup G) =
      Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) := by
    have heq : P5 b ⊓ Subgroup.centralizer ({i * M.z} : Set G) =
        (P5 b ⊓ Subgroup.centralizer ({i} : Set G)).map (MulAut.conj t).toMonoidHom := by
      ext x
      constructor
      · rintro ⟨hxP, hxc⟩
        replace hxc := Subgroup.mem_centralizer_singleton_iff.mp hxc
        refine ⟨t⁻¹ * x * t, ⟨?_, ?_⟩, ?_⟩
        · have := conj_mem_P5 (inv_mem htG) hxP
          rwa [inv_inv] at this
        · apply Subgroup.mem_centralizer_singleton_iff.mpr
          have hti' : i = t⁻¹ * (i * M.z) * t := by rw [← hti]; group
          rw [hti']
          calc t⁻¹ * x * t * (t⁻¹ * (i * M.z) * t) = t⁻¹ * (x * (i * M.z)) * t := by group
            _ = t⁻¹ * ((i * M.z) * x) * t := by rw [hxc]
            _ = t⁻¹ * (i * M.z) * t * (t⁻¹ * x * t) := by group
        · show t * (t⁻¹ * x * t) * t⁻¹ = x
          group
      · rintro ⟨y, ⟨hyP, hyc⟩, rfl⟩
        replace hyc := Subgroup.mem_centralizer_singleton_iff.mp hyc
        refine ⟨conj_mem_P5 htG hyP, ?_⟩
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        show t * y * t⁻¹ * (i * M.z) = i * M.z * (t * y * t⁻¹)
        rw [← hti]
        calc t * y * t⁻¹ * (t * i * t⁻¹) = t * (y * i) * t⁻¹ := by group
          _ = t * (i * y) * t⁻¹ := by rw [hyc]
          _ = t * i * t⁻¹ * (t * y * t⁻¹) := by group
    rw [heq, Subgroup.card_map_of_injective (MulAut.conj t).injective]
  rw [hCE, hCz, hCiz, one_pow, mul_one] at hBW
  rw [hBW]
  ring

omit hbH hb5 in
theorem no_order_fifteen_H
    {w : G} (hw : w ∈ ruH M.T) (h15 : orderOf w = 15) : False := by
  have hφ : M.φ ⟨w, hw⟩ ^ 15 = 1 := by
    rw [← map_pow]
    have : (⟨w, hw⟩ : ruH M.T) ^ 15 = 1 := Subtype.ext (by
      simpa using (h15 ▸ pow_orderOf_eq_one w : w ^ 15 = 1))
    rw [this, map_one]
  have hQ : ∀ n : ℕ, M.φ ⟨w, hw⟩ ^ n = 1 → n ∣ 15 → n ≠ 0 → 15 / n ∣ 2 ^ 11 := by
    intro n hn hdvd hn0
    have hk : (⟨w, hw⟩ : ruH M.T) ^ n ∈ M.φ.ker := by rw [MonoidHom.mem_ker, map_pow, hn]
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    have h1 := Subgroup.orderOf_dvd_natCard _ hk
    rw [M.toRuData.card_Q] at h1
    have h2 : orderOf (w ^ n) = 15 / n := by
      rw [orderOf_pow_of_dvd hn0 (h15 ▸ hdvd), h15]
    simpa [h2] using h1
  rcases Sigma.no_order_fifteen _ hφ with h | h
  · have := hQ 3 h (by norm_num) (by norm_num)
    norm_num at this
  · have := hQ 5 h (by norm_num) (by norm_num)
    norm_num at this

omit hbH hb5 in
theorem card_dvd_fifteen {C : Subgroup G} {c : G}
    (hC : C ≤ Subgroup.centralizer ({c * M.z * c⁻¹} : Set G)) (hodd : Odd (Nat.card C)) :
    Nat.card C ∣ 15 := by
  have hmap : C.map (MulAut.conj c⁻¹).toMonoidHom ≤ ruH M.T := by
    rintro _ ⟨x, hx, rfl⟩
    have hxc := Subgroup.mem_centralizer_singleton_iff.mp (hC hx)
    show c⁻¹ * x * c⁻¹⁻¹ ∈ ruH M.T
    rw [inv_inv, M.mem_H_iff_comm]
    calc M.z * (c⁻¹ * x * c) = c⁻¹ * (c * M.z * c⁻¹ * x) * c := by group
      _ = c⁻¹ * (x * (c * M.z * c⁻¹)) * c := by rw [hxc]
      _ = c⁻¹ * x * c * M.z := by group
  have hdvd : Nat.card C ∣ 15 * 2 ^ 14 := by
    have h := Subgroup.card_dvd_of_le hmap
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, M.toRuData.card_H] at h
    have e : 2 ^ 11 * 120 = 15 * 2 ^ 14 := by norm_num
    rwa [e] at h
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 14 hodd.coprime_two_right) hdvd

omit hbH hb5 in
theorem false_of_card_fifteen {C : Subgroup G} {c : G}
    (hC : C ≤ Subgroup.centralizer ({c * M.z * c⁻¹} : Set G)) (h15 : Nat.card C = 15) : False := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcomm := comm_of_card_fifteen (X := C) h15
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 (by rw [h15]; norm_num)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [h15]; norm_num)
  have hw : orderOf (x * y) = 15 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (hcomm x y) (by rw [hx, hy]; norm_num),
      hx, hy]
  set w : G := ((x * y : C) : G)
  have hwo : orderOf w = 15 := by rw [Subgroup.orderOf_coe]; exact hw
  have hwc := Subgroup.mem_centralizer_singleton_iff.mp (hC (x * y).2)
  have hwH : c⁻¹ * w * c ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    calc M.z * (c⁻¹ * w * c) = c⁻¹ * (c * M.z * c⁻¹ * w) * c := by group
      _ = c⁻¹ * (w * (c * M.z * c⁻¹)) * c := by rw [hwc]
      _ = c⁻¹ * w * c * M.z := by group
  refine M.no_order_fifteen_H hwH ?_
  have := orderOf_conj_eq c⁻¹ w
  rwa [inv_inv, hwo] at this

theorem false_of_card_three
    {i t c : G} (ht : t ∈ M.T5 b)
    (hti : t * i * t⁻¹ = i * M.z) (hc : c * M.z * c⁻¹ = i)
    (h3 : Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 3)
    (h45 : Nat.card (P5 b) = 45) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have htG : t ∈ G5 b := ht.2
  have hzb : M.z * b = b * M.z := M.Z_comm_H M.z_mem_Z hbH
  have hcommP : ∀ x ∈ P5 b, ∀ y ∈ P5 b, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (comm_of_card_fortyfive (X := P5 b) h45 ⟨x, hx⟩ ⟨y, hy⟩)
  set C := P5 b ⊓ Subgroup.centralizer ({i} : Set G)
  obtain ⟨y0, hy0⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [h3])
  set y : G := (y0 : G)
  have hy3 : orderOf y = 3 := by rw [Subgroup.orderOf_coe]; exact hy0
  have hyP : y ∈ P5 b := y0.2.1
  have hyi : y * i = i * y := Subgroup.mem_centralizer_singleton_iff.mp y0.2.2
  set y4 := t * y * t⁻¹
  have hy4P : y4 ∈ P5 b := conj_mem_P5 htG hyP
  have hy43 : orderOf y4 = 3 := by rw [orderOf_conj_eq, hy3]
  have hy4iz : y4 * (i * M.z) = (i * M.z) * y4 := by
    rw [← hti]
    simp only [y4]
    calc t * y * t⁻¹ * (t * i * t⁻¹) = t * (y * i) * t⁻¹ := by group
      _ = t * (i * y) * t⁻¹ := by rw [hyi]
      _ = t * i * t⁻¹ * (t * y * t⁻¹) := by group
  have hy4not : y4 ∉ Subgroup.zpowers y := by
    intro hmem
    have hy4i : y4 * i = i * y4 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hk]
      exact (Commute.zpow_left hyi k).eq
    have hy4z : y4 * M.z = M.z * y4 := by
      have h1 : y4 * M.z = i⁻¹ * (i * y4) * M.z := by group
      calc y4 * M.z = i⁻¹ * (y4 * i) * M.z := by rw [hy4i]; group
        _ = i⁻¹ * (y4 * (i * M.z)) := by group
        _ = i⁻¹ * ((i * M.z) * y4) := by rw [hy4iz]
        _ = M.z * y4 := by group
    have hb := mem_zpowers_of_P5_comm_z hbH hb5 hy4P hy4z
    have h5 := Subgroup.orderOf_dvd_natCard _ hb
    rw [Nat.card_zpowers, hb5, hy43] at h5
    norm_num at h5
  have hyH : c⁻¹ * y * c ∈ ruH M.T := by
    rw [M.mem_H_iff_comm, ← hc] at *
    have hyi' : y * (c * M.z * c⁻¹) = (c * M.z * c⁻¹) * y := by rw [hc]; exact hyi
    calc M.z * (c⁻¹ * y * c) = c⁻¹ * ((c * M.z * c⁻¹) * y) * c := by group
      _ = c⁻¹ * (y * (c * M.z * c⁻¹)) * c := by rw [hyi']
      _ = c⁻¹ * y * c * M.z := by group
  have hyH3 : orderOf (c⁻¹ * y * c) = 3 := by
    have := orderOf_conj_eq c⁻¹ y
    rwa [inv_inv, hy3] at this
  obtain ⟨h, hhH, hh⟩ := M.exists_conj_bel hyH hyH3
  set g := h * c⁻¹
  have hgy : g * y * g⁻¹ = M.bel ∨ g * y * g⁻¹ = (M.bel : G)⁻¹ := by
    simp only [g]
    rcases hh with hh | hh
    · left; rw [← hh]; group
    · right; rw [← hh]; group
  have hgPB : ∀ x ∈ P5 b, g * x * g⁻¹ ∈ M.GB := by
    intro x hx
    rw [M.mem_GB]
    have hxy : x * y = y * x := hcommP x hx y hyP
    have h1 : (g * y * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * y * g⁻¹) := by
      calc (g * y * g⁻¹) * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hxy]
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rcases hgy with hgy | hgy
    · rw [hgy] at h1; exact h1
    · rw [hgy] at h1
      exact ((Commute.inv_left (show Commute (M.bel : G)⁻¹ (g * x * g⁻¹) from h1)).eq).trans
        (by rw [inv_inv]) |>.trans rfl |> fun h => by simpa using h
  have hBy : ∀ x ∈ M.B, g⁻¹ * x * g ∈ Subgroup.zpowers y := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases hgy with hgy | hgy
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← hgy, conj_zpow]
      group
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      have hb' : (M.bel : G) = (g * y * g⁻¹)⁻¹ := by rw [hgy, inv_inv]
      rw [hb', inv_zpow', conj_zpow]
      group
  obtain ⟨e⟩ := M.lemma_J27_2
  have hbG := hgPB b (b_mem_P5 hb5)
  have hy4G := hgPB y4 hy4P
  set β : M.XQ := ((⟨g * b * g⁻¹, hbG⟩ : M.GB) : M.XQ)
  set γ : M.XQ := ((⟨g * y4 * g⁻¹, hy4G⟩ : M.GB) : M.XQ)
  have hβγ : β * γ = γ * β := by
    simp only [β, γ, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show g * b * g⁻¹ * (g * y4 * g⁻¹) = g * y4 * g⁻¹ * (g * b * g⁻¹)
    have := hcommP b (b_mem_P5 hb5) y4 hy4P
    calc g * b * g⁻¹ * (g * y4 * g⁻¹) = g * (b * y4) * g⁻¹ := by group
      _ = g * (y4 * b) * g⁻¹ := by rw [this]
      _ = g * y4 * g⁻¹ * (g * b * g⁻¹) := by group
  have hmk : ∀ x : M.GB, (x : M.XQ) = 1 ↔ (x : G) ∈ M.B := by
    intro x
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hβ5 : β ^ 5 = 1 := by
    simp only [β, ← QuotientGroup.mk_pow]
    rw [hmk]
    have : ((⟨g * b * g⁻¹, hbG⟩ ^ 5 : M.GB) : G) = 1 := by
      simp only [SubgroupClass.coe_pow]
      rw [conj_pow, pow_five_of_orderOf hb5]
      group
    rw [this]
    exact one_mem _
  have hβ3 : β ^ 3 ≠ 1 := by
    simp only [β, ← QuotientGroup.mk_pow]
    rw [Ne, hmk]
    intro hB
    have h9 := M.pow_three_of_mem_B hB
    have hb9 : ((⟨g * b * g⁻¹, hbG⟩ ^ 3 : M.GB) : G) ^ 3 = (g * b * g⁻¹) ^ 9 := by
      simp only [SubgroupClass.coe_pow]
      rw [← pow_mul]
    rw [hb9, conj_pow] at h9
    have h9' : b ^ 9 = 1 := by
      calc b ^ 9 = g⁻¹ * (g * b ^ 9 * g⁻¹) * g := by group
        _ = 1 := by rw [h9]; group
    have := orderOf_dvd_of_pow_eq_one h9'
    rw [hb5] at this
    norm_num at this
  have hγ3 : γ ^ 3 = 1 := by
    simp only [γ, ← QuotientGroup.mk_pow]
    rw [hmk]
    have : ((⟨g * y4 * g⁻¹, hy4G⟩ ^ 3 : M.GB) : G) = 1 := by
      simp only [SubgroupClass.coe_pow]
      rw [conj_pow, ← hy43, pow_orderOf_eq_one]
      group
    rw [this]
    exact one_mem _
  have hγ2 : γ ^ 2 ≠ 1 := by
    intro h2
    have hγ1 : γ = 1 := by
      calc γ = γ ^ 3 * (γ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hγ3, h2]; group
    simp only [γ] at hγ1
    rw [hmk] at hγ1
    apply hy4not
    have := hBy _ hγ1
    rwa [show g⁻¹ * (g * y4 * g⁻¹) * g = y4 by group] at this
  set w := β * γ
  have hcβγ : Commute β γ := hβγ
  have hw15 : w ^ 15 = 1 := by
    rw [hcβγ.mul_pow, show 15 = 5 * 3 by rfl, pow_mul, hβ5, one_pow, one_mul, pow_mul', hγ3,
      one_pow]
  have hw3 : w ^ 3 ≠ 1 := by
    rw [hcβγ.mul_pow, hγ3, mul_one]
    exact hβ3
  have hw5 : w ^ 5 ≠ 1 := by
    rw [hcβγ.mul_pow, hβ5, one_mul, show 5 = 3 + 2 by rfl, pow_add, hγ3, one_mul]
    exact hγ2
  rcases m10_pow_fifteen (e w).2 (by rw [← SubgroupClass.coe_pow, ← map_pow, hw15, map_one]; rfl)
    with h | h
  · apply hw3
    apply e.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using h)
  · apply hw5
    apply e.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using h)

theorem G5_eq_mul
    {g : G} (hg : g ∈ G5 b) : ∃ p ∈ P5 b, ∃ t ∈ M.T5 b, g = p * t := by
  obtain ⟨o, ho, hoH⟩ := exists_O5_mul hbH hb5 ⟨g, hg⟩
  have hoG : (o : G) ∈ P5 b := ⟨o, ho, rfl⟩
  have hx : ((o⁻¹ * ⟨g, hg⟩ : G5 b) : G) ∈ M.CH5 b := ⟨hoH, (o⁻¹ * ⟨g, hg⟩).2⟩
  obtain ⟨t, ht, c, hc, hct⟩ := CH5_eq_mul hbH hb5 hx
  refine ⟨(o : G) * c, mul_mem hoG (zpowers_le_P5 hb5 hc), t, ht, ?_⟩
  have e : ((o⁻¹ * ⟨g, hg⟩ : G5 b) : G) = (o : G)⁻¹ * g := rfl
  rw [e] at hct
  calc g = (o : G) * ((o : G)⁻¹ * g) := by group
    _ = (o : G) * (c * t) := by rw [hct]
    _ = (o : G) * c * t := by group

theorem card_G5 : Nat.card (G5 b) = Nat.card (P5 b) * 8 := by
  classical
  let F : P5 b × M.T5 b → G5 b := fun q =>
    ⟨(q.1 : G) * q.2, mul_mem (P5_le_G5 b q.1.2) (M.T5_le_G5 q.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨p, t⟩ ⟨p', t'⟩ h
    have h1 : (p : G) * t = p' * t' := congrArg Subtype.val h
    have h2 : (p' : G)⁻¹ * p = t' * (t : G)⁻¹ := by
      calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * t) * (t : G)⁻¹ := by group
        _ = (p' : G)⁻¹ * (p' * t') * (t : G)⁻¹ := by rw [h1]
        _ = t' * (t : G)⁻¹ := by group
    have h3 := eq_one_of_P5_T5 hbH hb5 (mul_mem (inv_mem p'.2) p.2)
      (h2 ▸ mul_mem t'.2 (inv_mem t.2))
    have hpp : (p : G) = p' := by
      calc (p : G) = p' * ((p' : G)⁻¹ * p) := by group
        _ = p' := by rw [h3, mul_one]
    have htt : (t : G) = t' := by
      rw [hpp] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext hpp) (Subtype.ext htt)
  have hS : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨p, hp, t, ht, rfl⟩ := G5_eq_mul hbH hb5 hg
    exact ⟨⟨⟨p, hp⟩, ⟨t, ht⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hS⟩), Nat.card_prod, card_T5 hbH hb5]

theorem false_of_card_P5_five
    (h5 : Nat.card (P5 b) = 5) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (G5 b) = 40 := by rw [card_G5 hbH hb5, h5]
  have hmax : ∀ S : Subgroup G, IsPGroup 5 S → Subgroup.zpowers b ≤ S →
      S = Subgroup.zpowers b := fun S hS hbS =>
    eq_zpowers_of_centralizer hb5 (by rw [hcard]; norm_num) hS hbS
  have hBp : IsPGroup 5 (Subgroup.zpowers b) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hb5]
    exact ⟨1, by norm_num⟩
  let S0 : Sylow 5 G :=
    { toSubgroup := Subgroup.zpowers b
      isPGroup' := hBp
      is_maximal' := fun {Q} hQ hle => hmax Q hQ hle }
  obtain ⟨e⟩ := M.lemma_J27_2
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm ⟨x5, x5_mem_m10⟩)
  have hg5 : g ^ 5 ∈ M.B.subgroupOf M.GB := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hg, ← map_pow]
    have : (⟨x5, x5_mem_m10⟩ : A6Models.m10) ^ 5 = 1 := Subtype.ext x5_pow_five
    rw [this, map_one]
  set g' : M.GB := g ^ 3
  have hg'5 : g' ^ 5 = 1 := by
    have := M.pow_three_of_mem_B (Subgroup.mem_subgroupOf.mp hg5)
    apply Subtype.ext
    simp only [g', SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [← pow_mul, show 3 * 5 = 5 * 3 by rfl, pow_mul]
    exact this
  have hg'1 : (g' : G) ≠ 1 := by
    intro h1
    have h1' : g' = 1 := Subtype.ext h1
    have hmk : ((g' : M.GB) : M.XQ) = 1 := by rw [h1']; rfl
    simp only [g', QuotientGroup.mk_pow, hg] at hmk
    rw [← map_pow, map_eq_one_iff _ e.symm.injective] at hmk
    have := congrArg Subtype.val hmk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    have hx3 : x5 ^ 3 ≠ 1 := by decide +kernel
    exact hx3 this
  have hg'o : orderOf (g' : G) = 5 := by
    refine orderOf_eq_prime ?_ hg'1
    have := congrArg Subtype.val hg'5
    simpa using this
  have hgp : IsPGroup 5 (Subgroup.zpowers (g' : G)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hg'o]
    exact ⟨1, by norm_num⟩
  obtain ⟨S', hS'⟩ := hgp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S' S0
  have hmem : h * (g' : G) * h⁻¹ ∈ Subgroup.zpowers b := by
    have : h * (g' : G) * h⁻¹ ∈ ((h • S' : Sylow 5 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, hS' (Subgroup.mem_zpowers _), by simp [MulAut.conj_apply]⟩
    rw [hh] at this
    simpa [S0] using this
  have hgen : Subgroup.zpowers (h * (g' : G) * h⁻¹) = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hmem) (le_of_eq ?_)
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_conj_eq, hg'o, hb5]
  have hbmem : b ∈ Subgroup.zpowers (h * (g' : G) * h⁻¹) := by
    rw [hgen]; exact Subgroup.mem_zpowers b
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbmem
  have hg'b : (g' : G) * M.bel = M.bel * g' := (M.mem_GB.mp g'.2).symm
  have hcomm : (h * M.bel * h⁻¹) * b = b * (h * M.bel * h⁻¹) := by
    rw [← hk]
    have hc : Commute (h * (M.bel : G) * h⁻¹) (h * (g' : G) * h⁻¹) := by
      show h * M.bel * h⁻¹ * (h * g' * h⁻¹) = h * g' * h⁻¹ * (h * M.bel * h⁻¹)
      calc h * M.bel * h⁻¹ * (h * g' * h⁻¹) = h * ((M.bel : G) * g') * h⁻¹ := by group
        _ = h * ((g' : G) * M.bel) * h⁻¹ := by rw [hg'b]
        _ = h * g' * h⁻¹ * (h * M.bel * h⁻¹) := by group
    exact (hc.zpow_right k).eq
  have hmemG : h * M.bel * h⁻¹ ∈ G5 b := mem_G5.mpr hcomm
  have h3 := Subgroup.orderOf_dvd_natCard (G5 b) hmemG
  rw [orderOf_conj_eq, M.orderOf_bel, hcard] at h3
  norm_num at h3

theorem lemma_J27_5 :
    Nat.card (P5 b) = 5 ^ 3 ∧ (∀ g ∈ G5 b, ∀ x ∈ P5 b, g * x * g⁻¹ ∈ P5 b) ∧
      (∀ g ∈ G5 b, ∃ p ∈ P5 b, ∃ t ∈ M.T5 b, g = p * t) ∧
      Nat.card (G5 b) = 5 ^ 3 * 8 ∧ Nonempty (M.T5 b ≃* QuaternionGroup 2) := by
  obtain ⟨i, hiH, hi2, hiz, hib, t, ht, hti⟩ := M.exists_inv_T5_conj hbH hb5
  have hP := card_P5_eq hbH hb5 hiH hi2 hib ht hti
  obtain ⟨c, hc⟩ := isConj_iff.mp hiz
  set C := P5 b ⊓ Subgroup.centralizer ({i} : Set G)
  have hCi : C ≤ Subgroup.centralizer ({c * M.z * c⁻¹} : Set G) := by
    rw [hc]; exact inf_le_right
  have hodd : Odd (Nat.card C) := (P5_odd b).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hdvd := M.card_dvd_fifteen hCi hodd
  have hcases : Nat.card C = 1 ∨ Nat.card C = 3 ∨ Nat.card C = 5 ∨ Nat.card C = 15 := by
    have hle : Nat.card C ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card C <;> simp_all
  have h125 : Nat.card (P5 b) = 5 ^ 3 := by
    rcases hcases with h | h | h | h
    · exact (false_of_card_P5_five hbH hb5 (by rw [hP, h]; norm_num)).elim
    · exact (false_of_card_three hbH hb5 ht hti hc h (by rw [hP, h]; norm_num)).elim
    · rw [hP, h]; norm_num
    · exact (M.false_of_card_fifteen hCi h).elim
  refine ⟨h125, fun g hg x hx => conj_mem_P5 hg hx, fun g hg => G5_eq_mul hbH hb5 hg,
    by rw [card_G5 hbH hb5, h125], T5_quaternion hbH hb5⟩

theorem lemma_J27_6
    (g : G) : g * b * g⁻¹ ∉ M.GB := by
  intro hg
  rw [M.mem_GB] at hg
  have hmem : g⁻¹ * M.bel * g ∈ G5 b := by
    rw [mem_G5]
    calc g⁻¹ * M.bel * g * b = g⁻¹ * ((M.bel : G) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * M.bel) * g := by rw [hg]
      _ = b * (g⁻¹ * M.bel * g) := by group
  have h3 := Subgroup.orderOf_dvd_natCard (G5 b) hmem
  rw [show g⁻¹ * (M.bel : G) * g = g⁻¹ * M.bel * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq,
    M.orderOf_bel, (lemma_J27_5 hbH hb5).2.2.2.1] at h3
  norm_num at h3

end Five

end RuDataM

end CFSG.Quasithin.RuType
