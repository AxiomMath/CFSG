module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111P1Dat
public import CFSG.Quasithin.EmptyFaithful.S152UAut

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T V M : Subgroup G}

namespace P1Hyp

variable (h : P1Hyp T V M)

include h

theorem zpow_eq_one {c : G} (hcA : c ∈ h.A) (hcodd : Odd (orderOf c)) {i : ℤ}
    (hi : c ^ i ∈ Subgroup.centralizer (V : Set G)) : c ^ i = 1 := by
  have hmem : c ^ i ∈ Subgroup.zpowers c := Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i
  have hodd : Odd (orderOf (c ^ i)) :=
    Odd.of_dvd_nat hcodd (orderOf_dvd_of_mem_zpowers hmem)
  exact eq_one_of_odd_of_cenMod h.pN h.ch h.R2 h.sq (h.A.zpow_mem hcA i) hi hodd

theorem exists_P1 {a : G} (haT : a ∈ T) (ha2 : a * a = 1)
    (haC : a ∉ Subgroup.centralizer (V : Set G)) (haR : ∀ r ∈ Rg T V, a * r * a⁻¹ * r⁻¹ ∈ V) :
    ∃ (P1 : Subgroup G) (c : G), T ≤ P1 ∧ P1 ≤ M ∧ c ∈ P1 ∧ c ^ 3 = 1 ∧
      (∀ v ∈ V, c * v * c⁻¹ = v → v = 1) ∧ T.relIndex P1 = 3 ∧
      ¬ P1 ≤ Subgroup.normalizer (T : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, c, hcN, hcA, hcodd, hcρ, hα3, hα1, hαfree, hnorm, haN, hinv⟩ :=
    h.exists_c haT ha2 haC haR
  have hAk2 : IsPGroup 2 ↥h.Ak := isPGroup_cenMod_inf h.pN h.ch h.R2 h.sq
  have hAkT : h.Ak ≤ T := (cenMod_inf_le h.pN h.ch h.R2 h.sq).trans inf_le_left
  have hAkN : h.Ak ≤ Ng T V M := inf_le_left.trans cenMod_le
  have hNAk : Ng T V M ≤ Subgroup.normalizer (h.Ak : Set G) := le_normalizer_cenMod_inf
  have hcNg : c ∈ Ng T V M := cenMod_le hcA
  have hc3N : c ^ 3 ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hcN 3
  have hc3 : c ^ 3 = 1 := by
    have hcen : c ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
      have e : (⟨c ^ 3, hc3N⟩ : Subgroup.normalizer (V : Set G)) = ⟨c, hcN⟩ ^ 3 :=
        Subtype.ext (by simp)
      have h1 : conjAct V ⟨c ^ 3, hc3N⟩ = 1 := by rw [e, map_pow, hcρ, hα3]
      exact A4.conjAct_eq_one_iff.mp h1
    exact eq_one_of_odd_of_cenMod h.pN h.ch h.R2 h.sq (h.A.pow_mem hcA 3) hcen
      (Odd.of_dvd_nat hcodd (orderOf_pow_dvd 3))
  have hfree : ∀ v ∈ V, c * v * c⁻¹ = v → v = 1 := by
    intro v hv hcv
    by_contra hv1
    have hne : (⟨v, hv⟩ : ↥V) ≠ 1 := fun h1 => hv1 (congrArg Subtype.val h1)
    refine hαfree _ hne ?_
    rw [← hcρ]
    exact Subtype.ext (by rw [conj_coe_apply]; exact hcv)
  have hc1 : c ≠ 1 := by
    intro h1
    apply hα1
    rw [← hcρ]
    have : (⟨c, hcN⟩ : Subgroup.normalizer (V : Set G)) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcAk : Subgroup.zpowers c ≤ Subgroup.normalizer (h.Ak : Set G) :=
    Subgroup.zpowers_le.mpr (hNAk hcNg)
  have hconj : ∀ t ∈ T, t * c * t⁻¹ ∈ h.Ak ⊔ Subgroup.zpowers c := by
    intro t ht
    have htN : t ∈ Subgroup.normalizer (V : Set G) := h.NV ▸ h.TM ht
    have htM : conjAct V ⟨t, htN⟩ ∈ autOn M V := mem_autOn_iff_exists.mpr ⟨t, htN, h.TM ht, rfl⟩
    have hcA' : t * c * t⁻¹ ∈ h.A := conj_mem_cenMod (h.TN ht) hcA
    have hN' : t * c * t⁻¹ ∈ Subgroup.normalizer (V : Set G) := h.NVn (cenMod_le hcA')
    have hρ : conjAct V ⟨t * c * t⁻¹, hN'⟩ =
        conjAct V ⟨t, htN⟩ * α * (conjAct V ⟨t, htN⟩)⁻¹ := by
      have e : (⟨t * c * t⁻¹, hN'⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨t, htN⟩ * ⟨c, hcN⟩ * ⟨t, htN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hcρ]
    rcases hnorm _ htM with h1 | h1
    · have h2 : conjAct V ⟨c, hcN⟩ = conjAct V ⟨t * c * t⁻¹, hN'⟩ := by rw [hcρ, hρ, h1]
      have h3 := (conjAct_eq_iff hcN hN').mp h2
      have hk : c⁻¹ * (t * c * t⁻¹) ∈ h.Ak := ⟨h.A.mul_mem (h.A.inv_mem hcA) hcA', h3⟩
      have e : t * c * t⁻¹ = c * (c⁻¹ * (t * c * t⁻¹)) := by group
      rw [e]
      exact (h.Ak ⊔ Subgroup.zpowers c).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
        (Subgroup.mem_sup_left hk)
    · have hc'N : c⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hcN
      have h2 : conjAct V ⟨c⁻¹, hc'N⟩ = conjAct V ⟨t * c * t⁻¹, hN'⟩ := by
        have e : (⟨c⁻¹, hc'N⟩ : Subgroup.normalizer (V : Set G)) = ⟨c, hcN⟩⁻¹ := rfl
        rw [e, map_inv, hcρ, hρ, h1]
      have h3 := (conjAct_eq_iff hc'N hN').mp h2
      have hk : c⁻¹⁻¹ * (t * c * t⁻¹) ∈ h.Ak :=
        ⟨h.A.mul_mem (h.A.inv_mem (h.A.inv_mem hcA)) hcA', h3⟩
      have e : t * c * t⁻¹ = c⁻¹ * (c⁻¹⁻¹ * (t * c * t⁻¹)) := by group
      rw [e]
      exact (h.Ak ⊔ Subgroup.zpowers c).mul_mem
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)))
        (Subgroup.mem_sup_left hk)
  have hTAk : T ≤ Subgroup.normalizer (h.Ak : Set G) := h.TN.trans hNAk
  have hTW : T ≤ Subgroup.normalizer ((h.Ak ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro t ht
    have key : ∀ s ∈ T, ∀ x ∈ h.Ak ⊔ Subgroup.zpowers c,
        s * x * s⁻¹ ∈ h.Ak ⊔ Subgroup.zpowers c := by
      intro s hs x hx
      have hle : h.Ak ⊔ Subgroup.zpowers c ≤
          (h.Ak ⊔ Subgroup.zpowers c).comap (MulAut.conj s).toMonoidHom := by
        refine sup_le (fun y hy => ?_) ?_
        · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTAk hs) y).mp hy)
        · rw [Subgroup.zpowers_le]
          exact hconj s hs
      exact hle hx
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t ht x, fun hx => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hTW' : T ⊓ (h.Ak ⊔ Subgroup.zpowers c) ≤ h.Ak := by
    rintro x ⟨hxT, hxW⟩
    have hx' : x ∈ ((h.Ak ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := hxW
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hcAk] at hx'
    obtain ⟨k, hk, ci, hci, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hci
    obtain ⟨m, hm⟩ := h.T2 ⟨k * c ^ i, hxT⟩
    have hm' : (k * c ^ i) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := h.NVn (hAkN hk)
    have hciN : c ^ i ∈ Subgroup.normalizer (V : Set G) := Subgroup.zpow_mem _ hcN i
    have hkcN : k * c ^ i ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hkN hciN
    have hρk : conjAct V ⟨k, hkN⟩ = 1 := A4.conjAct_eq_one_iff.mpr hk.2
    have hρc : conjAct V ⟨c ^ i, hciN⟩ = α ^ i := by
      have e : (⟨c ^ i, hciN⟩ : Subgroup.normalizer (V : Set G)) = ⟨c, hcN⟩ ^ i :=
        Subtype.ext (by simp)
      rw [e, map_zpow, hcρ]
    have hρ : conjAct V ⟨k * c ^ i, hkcN⟩ = α ^ i := by
      have e : (⟨k * c ^ i, hkcN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨k, hkN⟩ * ⟨c ^ i, hciN⟩ := rfl
      rw [e, map_mul, hρk, hρc, one_mul]
    have hpow : (α ^ i) ^ 2 ^ m = 1 := by
      rw [← hρ, ← map_pow]
      have : (⟨k * c ^ i, hkcN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ m = 1 :=
        Subtype.ext (by simpa using hm')
      rw [this, map_one]
    have hα3i : (α ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα3, one_zpow]
    have hαi : α ^ i = 1 := by
      have hodd : Odd (orderOf (α ^ i)) :=
        Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hα3i)
      exact E2.eq_one_of_odd_orderOf_of_pow_two_pow hodd hpow
    have hci1 : c ^ i ∈ Subgroup.centralizer (V : Set G) :=
      A4.conjAct_eq_one_iff.mp (by rw [hρc, hαi])
    have hci : c ^ i = 1 := h.zpow_eq_one hcA hcodd hci1
    show k * c ^ i ∈ h.Ak
    rw [hci, mul_one]
    exact hk
  have hAkc : h.Ak ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxc⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxc
    rw [Subgroup.mem_bot]
    exact h.zpow_eq_one hcA hcodd hxA.2
  have hAkW : h.Ak.relIndex (h.Ak ⊔ Subgroup.zpowers c) = 3 := by
    have e := relIndex_sup_eq (D := h.Ak) (T := Subgroup.zpowers c) hcAk
    rw [sup_comm] at e
    rw [e]
    have h1 := Subgroup.relIndex_mul_card h.Ak (Subgroup.zpowers c)
    rw [hAkc, Subgroup.card_bot, mul_one, Nat.card_zpowers, hcord] at h1
    exact h1
  have hWT : (h.Ak ⊔ Subgroup.zpowers c) ⊓ T = h.Ak := by
    apply le_antisymm
    · rw [inf_comm]
      exact hTW'
    · exact le_inf le_sup_left hAkT
  have hWP : h.Ak ⊔ Subgroup.zpowers c ≤ T ⊔ (h.Ak ⊔ Subgroup.zpowers c) := le_sup_right
  have e1 : (h.Ak ⊔ Subgroup.zpowers c).relIndex (T ⊔ (h.Ak ⊔ Subgroup.zpowers c)) =
      h.Ak.relIndex T := by
    rw [relIndex_sup_eq hTW, ← Subgroup.inf_relIndex_right, hWT]
  have f1 := Subgroup.relIndex_mul_card (h.Ak ⊔ Subgroup.zpowers c)
    (T ⊔ (h.Ak ⊔ Subgroup.zpowers c))
  have f2 := Subgroup.relIndex_mul_card h.Ak (h.Ak ⊔ Subgroup.zpowers c)
  have f3 := Subgroup.relIndex_mul_card h.Ak T
  have f4 := Subgroup.relIndex_mul_card T (T ⊔ (h.Ak ⊔ Subgroup.zpowers c))
  rw [inf_eq_left.mpr hWP, e1] at f1
  rw [inf_eq_left.mpr le_sup_left, hAkW] at f2
  rw [inf_eq_left.mpr hAkT] at f3
  rw [inf_eq_left.mpr le_sup_left] at f4
  have hApos : 0 < Nat.card h.Ak := Nat.card_pos
  have hrpos : 0 < h.Ak.relIndex T := by
    rcases Nat.eq_zero_or_pos (h.Ak.relIndex T) with h0 | h0
    · rw [h0, zero_mul] at f3
      have := Nat.card_pos (α := T)
      omega
    · exact h0
  have hidx : T.relIndex (T ⊔ (h.Ak ⊔ Subgroup.zpowers c)) = 3 := by
    have h5 : h.Ak.relIndex T * (T.relIndex (T ⊔ (h.Ak ⊔ Subgroup.zpowers c)) * Nat.card h.Ak) =
        h.Ak.relIndex T * (3 * Nat.card h.Ak) := by
      calc h.Ak.relIndex T * (T.relIndex (T ⊔ (h.Ak ⊔ Subgroup.zpowers c)) * Nat.card h.Ak)
          = T.relIndex (T ⊔ (h.Ak ⊔ Subgroup.zpowers c)) * (h.Ak.relIndex T * Nat.card h.Ak) := by
            ring
        _ = T.relIndex (T ⊔ (h.Ak ⊔ Subgroup.zpowers c)) * Nat.card T := by rw [f3]
        _ = Nat.card ↥(T ⊔ (h.Ak ⊔ Subgroup.zpowers c)) := f4
        _ = h.Ak.relIndex T * Nat.card ↥(h.Ak ⊔ Subgroup.zpowers c) := f1.symm
        _ = h.Ak.relIndex T * (3 * Nat.card h.Ak) := by rw [f2]
    exact Nat.eq_of_mul_eq_mul_right hApos (Nat.eq_of_mul_eq_mul_left hrpos h5)
  have hcP1 : c ∈ T ⊔ (h.Ak ⊔ Subgroup.zpowers c) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hnn : ¬ T ⊔ (h.Ak ⊔ Subgroup.zpowers c) ≤ Subgroup.normalizer (T : Set G) := by
    intro hP
    have hcT : c ∈ Subgroup.normalizer (T : Set G) := hP hcP1
    have hcaT : c * a * c⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hcT a).mp haT
    have hyT : c * a * c⁻¹ * a⁻¹ ∈ T := T.mul_mem hcaT (T.inv_mem haT)
    have hyN : c * a * c⁻¹ * a⁻¹ ∈ Subgroup.normalizer (V : Set G) := h.NV ▸ h.TM hyT
    have hρ : conjAct V ⟨c * a * c⁻¹ * a⁻¹, hyN⟩ = α ^ 2 := by
      have e : (⟨c * a * c⁻¹ * a⁻¹, hyN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨c, hcN⟩ * ⟨a, haN⟩ * ⟨c, hcN⟩⁻¹ * ⟨a, haN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcρ]
      have h6 : conjAct V ⟨a, haN⟩ * α⁻¹ * (conjAct V ⟨a, haN⟩)⁻¹ = α := by
        have := congrArg (·⁻¹) hinv
        simpa [mul_assoc] using this
      calc α * conjAct V ⟨a, haN⟩ * α⁻¹ * (conjAct V ⟨a, haN⟩)⁻¹
          = α * (conjAct V ⟨a, haN⟩ * α⁻¹ * (conjAct V ⟨a, haN⟩)⁻¹) := by group
        _ = α ^ 2 := by rw [h6, pow_two]
    obtain ⟨m, hm⟩ := h.T2 ⟨c * a * c⁻¹ * a⁻¹, hyT⟩
    have hm' : (c * a * c⁻¹ * a⁻¹) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hpow : (α ^ 2) ^ 2 ^ m = 1 := by
      rw [← hρ, ← map_pow]
      have : (⟨c * a * c⁻¹ * a⁻¹, hyN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ m = 1 :=
        Subtype.ext (by simpa using hm')
      rw [this, map_one]
    have hodd : Odd (orderOf (α ^ 2)) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (by
        rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]))
    have h22 : α ^ 2 = 1 := E2.eq_one_of_odd_orderOf_of_pow_two_pow hodd hpow
    apply hα1
    calc α = α ^ 3 * (α ^ 2)⁻¹ := by group
      _ = 1 := by rw [hα3, h22]; simp
  refine ⟨T ⊔ (h.Ak ⊔ Subgroup.zpowers c), c, le_sup_left, sup_le h.TM (sup_le
    (hAkN.trans inf_le_left) (Subgroup.zpowers_le.mpr hcNg.1)), hcP1, hc3, hfree, hidx, hnn⟩

end P1Hyp

end Y15111

end CFSG.Quasithin
