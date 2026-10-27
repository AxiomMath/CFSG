module

public import CFSG.Quasithin.Background.D2Y9
public import CFSG.Quasithin.Background.D2Y8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem refl_mod_z_core {t l z r : MulAut V} (hlz : l * z = z * l) (htl : t * l * t⁻¹ = l⁻¹)
    (htz : t * z * t⁻¹ = z) {i j : ℤ} (hr : r = l ^ i * z ^ j) :
    t * r * t⁻¹ * r ∈ Subgroup.zpowers z := by
  have hconj : t * (l ^ i * z ^ j) * t⁻¹ = (l⁻¹) ^ i * z ^ j := by
    calc t * (l ^ i * z ^ j) * t⁻¹ = (t * l ^ i * t⁻¹) * (t * z ^ j * t⁻¹) := by group
      _ = (t * l * t⁻¹) ^ i * (t * z * t⁻¹) ^ j := by rw [← conj_zpow, ← conj_zpow]
      _ = (l⁻¹) ^ i * z ^ j := by rw [htl, htz]
  have hcomm : Commute (l ^ i) (z ^ j) := (show Commute l z from hlz).zpow_zpow i j
  rw [hr, hconj]
  have e : (l⁻¹) ^ i * z ^ j * (l ^ i * z ^ j) = z ^ j * z ^ j := by
    calc (l⁻¹) ^ i * z ^ j * (l ^ i * z ^ j) = (l ^ i)⁻¹ * (z ^ j * l ^ i) * z ^ j := by
          rw [inv_zpow]; group
      _ = (l ^ i)⁻¹ * (l ^ i * z ^ j) * z ^ j := by rw [hcomm.symm.eq]
      _ = z ^ j * z ^ j := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j)
    (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j)

section Q

variable {X : Subgroup (MulAut V)} {t x z : MulAut V}

omit [Finite V] in
theorem tinv_inv_eq {t : MulAut V} (ht2 : t ^ 2 = 1) : t⁻¹ = t := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_two]
  exact ht2

theorem refl_mod_z_P (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) {p : MulAut V} (hp : p ∈ centR X x) :
    t * p * t⁻¹ * p ∈ Subgroup.zpowers z := by
  obtain ⟨hxo, hzo, hxz, hne, hsup⟩ := Good.E9 hV c hX1 h hg
  obtain ⟨-, -, hform⟩ := E9_data hxo hzo hxz hne
  have hpE : p ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by rw [hsup]; exact hp
  obtain ⟨i, j, hij⟩ := hform p hpE
  have htz : t * z * t⁻¹ = z := by
    rw [hg.tz]
    group
  exact refl_mod_z_core hxz h.hinv htz hij

omit [Finite V] in
theorem conj_mem_normR (h : InvPair X t x) {q : MulAut V}
    (hq : q ∈ normR X x) : t * q * t⁻¹ ∈ normR X x := by
  have ht2 : t ^ 2 = 1 := h.ht.2.2.1
  have htinv : t⁻¹ = t := tinv_inv_eq ht2
  have hqR : t * q * t⁻¹ ∈ pCoreOf 3 X :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X h.ht.1) q).mp hq.1
  have hq' : q⁻¹ ∈ normR X x := (normR X x).inv_mem hq
  refine mem_normR_of hqR (fun p hp => ?_) (fun p hp => ?_)
  · have h1 : t⁻¹ * p * t⁻¹⁻¹ ∈ centR X x := by
      rw [htinv]
      simpa [htinv] using conj_mem_centR h.ht h.hinv hp
    have h2 := normR_conj hq h1
    have h3 := conj_mem_centR h.ht h.hinv h2
    have e : t * q * t⁻¹ * p * (t * q * t⁻¹)⁻¹ = t * (q * (t⁻¹ * p * t⁻¹⁻¹) * q⁻¹) * t⁻¹ := by group
    rw [e]
    exact h3
  · have h1 : t⁻¹ * p * t⁻¹⁻¹ ∈ centR X x := by
      rw [htinv]
      simpa [htinv] using conj_mem_centR h.ht h.hinv hp
    have h2 := normR_conj hq' h1
    have h3 := conj_mem_centR h.ht h.hinv h2
    have e : (t * q * t⁻¹)⁻¹ * p * (t * q * t⁻¹) = t * (q⁻¹ * (t⁻¹ * p * t⁻¹⁻¹) * q⁻¹⁻¹) * t⁻¹ := by
      group
    rw [e]
    exact h3

theorem normR_comm_P_mod_z (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) (h : InvPair X t x) (hg : Good X t x z) {q p : MulAut V}
    (hq : q ∈ normR X x) (hp : p ∈ centR X x) : q * p * q⁻¹ * p⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨hxo, hzo, hxz, hne, hsup⟩ := Good.E9 hV c hX1 h hg
  obtain ⟨-, -, hform⟩ := E9_data hxo hzo hxz hne
  have hpE : p ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by rw [hsup]; exact hp
  obtain ⟨a, b, hab⟩ := hform p hpE
  rw [hab, normR_conj_zpow hV c hX1 h hg hq a b]
  exact Subgroup.zpow_mem _ (normR_x_mod_z hV c hX1 h hg hq) a

theorem normR_refl (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) {g : MulAut V} (hq : g ∈ normR X x) :
    t * g * t⁻¹ * g ∈ Subgroup.zpowers z := by
  have ht2 : t ^ 2 = 1 := h.ht.2.2.1
  have htinv : t⁻¹ = t := tinv_inv_eq ht2
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hg' : t * g * t⁻¹ ∈ normR X x := conj_mem_normR h hq
  obtain ⟨hxo, hzo, hxz, hne, hsup⟩ := Good.E9 hV c hX1 h hg
  have hz3 : z ^ 3 = 1 := hg.cube z hg.hz
  have htz : t * z * t⁻¹ = z := by rw [hg.tz]; group
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (normR_x_mod_z hV c hX1 h hg hq)
  have hζz : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.zpowers z := ⟨m, hm⟩
  have htζ : t * (g * x * g⁻¹ * x⁻¹) * t⁻¹ = g * x * g⁻¹ * x⁻¹ := by
    rw [← hm, ← conj_zpow, htz]
  have hζx : (g * x * g⁻¹ * x⁻¹) * x = x * (g * x * g⁻¹ * x⁻¹) := by
    rw [← hm]
    exact ((show Commute z x from hxz.symm).zpow_left m).eq
  have e0 : t⁻¹ * x * t = x⁻¹ := by
    rw [htinv]
    have := h.hinv
    rwa [htinv] at this
  have hxinv : t * x⁻¹ * t⁻¹ = x := by
    calc t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      _ = x := by rw [h.hinv, inv_inv]
  have htζ' : t * (g * x * g⁻¹ * x⁻¹)⁻¹ * t⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by
    rw [show t * (g * x * g⁻¹ * x⁻¹)⁻¹ * t⁻¹ = (t * (g * x * g⁻¹ * x⁻¹) * t⁻¹)⁻¹ by group, htζ]
  have hθg' : (t * g * t⁻¹) * x * (t * g * t⁻¹)⁻¹ * x⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by
    have hgx : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    calc (t * g * t⁻¹) * x * (t * g * t⁻¹)⁻¹ * x⁻¹
        = t * g * (t⁻¹ * x * t) * g⁻¹ * t⁻¹ * x⁻¹ := by group
      _ = t * g * x⁻¹ * g⁻¹ * t⁻¹ * x⁻¹ := by rw [e0]
      _ = t * (g * x * g⁻¹)⁻¹ * t⁻¹ * x⁻¹ := by group
      _ = t * ((g * x * g⁻¹ * x⁻¹) * x)⁻¹ * t⁻¹ * x⁻¹ := by rw [← hgx]
      _ = (t * x⁻¹ * t⁻¹) * (t * (g * x * g⁻¹ * x⁻¹)⁻¹ * t⁻¹) * x⁻¹ := by group
      _ = x * (g * x * g⁻¹ * x⁻¹)⁻¹ * x⁻¹ := by rw [hxinv, htζ']
      _ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by
        have : x * (g * x * g⁻¹ * x⁻¹)⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ * x :=
          (Commute.inv_right (show Commute x (g * x * g⁻¹ * x⁻¹) from hζx.symm)).eq
        rw [this]
        group
  have hmul := theta_mul (x := x) (z := z) (a := t * g * t⁻¹) (b := g)
    (normR_comm_z hV c hX1 h hg hg') (normR_x_mod_z hV c hX1 h hg hq)
    (normR_x_mod_z hV c hX1 h hg hg')
  rw [hθg'] at hmul
  have hp1 : (t * g * t⁻¹ * g) * x * ((t * g * t⁻¹ * g))⁻¹ * x⁻¹ = 1 := by
    rw [hmul]
    group
  have hpP : t * g * t⁻¹ * g ∈ centR X x := by
    refine mem_centR.mpr ⟨(pCoreOf 3 X).mul_mem hg'.1 hq.1, ?_⟩
    have h2 : (t * g * t⁻¹ * g) * x * ((t * g * t⁻¹ * g))⁻¹ = x := mul_inv_eq_one.mp hp1
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hkey : t * (t * g * t⁻¹ * g) * t⁻¹ = g * (t * g * t⁻¹ * g) * g⁻¹ := by
    calc t * (t * g * t⁻¹ * g) * t⁻¹ = (t * t) * g * t⁻¹ * g * t⁻¹ := by group
      _ = g * t⁻¹ * g * t⁻¹ := by rw [htt, one_mul]
      _ = g * t * g * t⁻¹ := by rw [htinv]
      _ = g * (t * g * t⁻¹ * g) * g⁻¹ := by group
  have hw1 := normR_comm_P_mod_z hV c hX1 h hg hq hpP
  have hw2 := refl_mod_z_P hV c hX1 h hg hpP
  set p := t * g * t⁻¹ * g with hp
  have hsq : p * p = (t * p * t⁻¹ * p⁻¹)⁻¹ * (t * p * t⁻¹ * p) := by group
  have hsq' : p * p ∈ Subgroup.zpowers z := by
    rw [hsq, hkey]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hw1) (by rw [← hkey]; exact hw2)
  have hp3 : p ^ 3 = 1 := hg.cube p hpP
  have : p = (p * p)⁻¹ := by
    calc p = p ^ 3 * (p * p)⁻¹ := by group
      _ = (p * p)⁻¹ := by rw [hp3, one_mul]
  rw [this]
  exact Subgroup.inv_mem _ hsq'

theorem normR_cube (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (h : InvPair X t x) (hg : Good X t x z) {g : MulAut V} (hq : g ∈ normR X x) :
    g ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ht2 : t ^ 2 = 1 := h.ht.2.2.1
  obtain ⟨hxo, hzo, hxz, hne, hsup⟩ := Good.E9 hV c hX1 h hg
  have hz3 : z ^ 3 = 1 := hg.cube z hg.hz
  have hgz := normR_comm_z hV c hX1 h hg hq
  have hζz0 := normR_x_mod_z hV c hX1 h hg hq
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = g * x * g⁻¹ * x⁻¹ := ⟨_, rfl⟩
  rw [← hζ] at hζz0
  have hgx : g * x * g⁻¹ = ζ * x := by rw [hζ]; group
  have hgζ : g * ζ = ζ * g := commute_zpowers_of_commute hgz hζz0
  have hζ3 : ζ ^ 3 = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hζz0
    rw [← hm]
    exact zpow_cube_eq_one hz3 m
  have key : ∀ n : ℕ, g ^ n * x * (g ^ n)⁻¹ = ζ ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih]
      have hc : g * ζ ^ n * g⁻¹ = ζ ^ n := by
        rw [((show Commute g ζ from hgζ).pow_right n).eq]
        group
      calc g * (ζ ^ n * x) * g⁻¹ = (g * ζ ^ n * g⁻¹) * (g * x * g⁻¹) := by group
        _ = ζ ^ n * (ζ * x) := by rw [hc, hgx]
        _ = ζ ^ (n + 1) * x := by rw [pow_succ, mul_assoc]
  have hu : g ^ 3 ∈ centR X x := by
    refine mem_centR.mpr ⟨(pCoreOf 3 X).pow_mem hq.1 3, ?_⟩
    have := key 3
    rw [hζ3, one_mul] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have hr6 := normR_refl hV c hX1 h hg hq
  have hinvu : t * g ^ 3 * t⁻¹ = (g ^ 3)⁻¹ := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hr6
    have hgζ' : g * (t * g * t⁻¹ * g) = (t * g * t⁻¹ * g) * g :=
      commute_zpowers_of_commute hgz hr6
    have hζ'3 : (t * g * t⁻¹ * g) ^ 3 = 1 := by
      rw [← hm]
      exact zpow_cube_eq_one hz3 m
    have e1 : t * g * t⁻¹ = (t * g * t⁻¹ * g) * g⁻¹ := by group
    calc t * g ^ 3 * t⁻¹ = (t * g * t⁻¹) ^ 3 := (conj_pow).symm
      _ = ((t * g * t⁻¹ * g) * g⁻¹) ^ 3 := by rw [← e1]
      _ = (t * g * t⁻¹ * g) ^ 3 * (g⁻¹) ^ 3 := by
        refine Commute.mul_pow ?_ 3
        exact (show Commute (t * g * t⁻¹ * g) g from hgζ'.symm).inv_right
      _ = (g ^ 3)⁻¹ := by rw [hζ'3, one_mul, inv_pow]
  by_contra hne1
  have hu1 : g ^ 3 ≠ 1 := hne1
  have hux := inverted_mem_zpowers hV c hX1 h hu hu1 hinvu
  have hxo3 : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
  have heq : Subgroup.zpowers (g ^ 3) = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact Subgroup.zpowers_le.mpr hux
    · have : orderOf (g ^ 3) = 3 := by
        have h3 : (g ^ 3) ^ 3 = 1 := by
          have := hg.cube _ hu
          exact this
        exact orderOf_eq_prime h3 hu1
      rw [hxo3, Nat.card_zpowers, this]
  have hxu : x ∈ Subgroup.zpowers (g ^ 3) := by rw [heq]; exact Subgroup.mem_zpowers x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxu
  have hgcomm : g * x = x * g := by
    rw [← hk]
    exact ((show Commute g (g ^ 3) from (Commute.refl g).pow_right 3).zpow_right k).eq
  have hgP : g ∈ centR X x := mem_centR.mpr ⟨hq.1, hgcomm⟩
  exact hu1 (hg.cube g hgP)

end Q

end CFSG.Quasithin
