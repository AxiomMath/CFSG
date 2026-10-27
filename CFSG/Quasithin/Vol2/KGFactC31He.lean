module

public import CFSG.Quasithin.Vol2.KGFactC31HeSx
public import Certificates.Certificate7222
public import CFSG.Quasithin.Vol2.KGFactC31HeScan
public import CFSG.Sporadic.HeldB.InnerClass

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native
  _root_.Certificates

theorem exists_ref_of_conj {τ c t y : Equiv.Perm (Fin 8330)} (hc : c ∈ heP)
    (htc : t = c * τ * c⁻¹) (hy : y ∈ heP) (hmove : y * t * y⁻¹ ≠ t)
    (he : ∃ e ∈ [25, 343, 17], y ^ e = 1)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * (y ^ j)⁻¹) = y ^ j * t * (y ^ j)⁻¹ * t)
    (hcls : ∀ y' ∈ heP, y' * τ * y'⁻¹ ≠ τ → (∃ e ∈ [25, 343, 17], y' ^ e = 1) →
      (∀ j : ℕ, τ * (y' ^ j * τ * (y' ^ j)⁻¹) = y' ^ j * τ * (y' ^ j)⁻¹ * τ) →
      ∃ d ∈ heAutGroup, ∃ m, ∀ bw ∈ refW m, d * elt bw * d⁻¹ ∈ orbSub y' τ) :
    ∃ d ∈ heAutGroup, ∃ m, ∀ bw ∈ refW m, d * elt bw * d⁻¹ ∈ orbSub y t := by
  subst htc
  have hpow : ∀ j : ℕ, (c⁻¹ * y * c) ^ j = c⁻¹ * y ^ j * c := fun j => by
    rw [show c⁻¹ * y * c = c⁻¹ * y * c⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
  have hy' : c⁻¹ * y * c ∈ heP := heP.mul_mem (heP.mul_mem (heP.inv_mem hc) hy) hc
  have hmove' : c⁻¹ * y * c * τ * (c⁻¹ * y * c)⁻¹ ≠ τ := by
    intro h1
    apply hmove
    calc y * (c * τ * c⁻¹) * y⁻¹ = c * (c⁻¹ * y * c * τ * (c⁻¹ * y * c)⁻¹) * c⁻¹ := by group
      _ = c * τ * c⁻¹ := by rw [h1]
  have he' : ∃ e ∈ [25, 343, 17], (c⁻¹ * y * c) ^ e = 1 := by
    obtain ⟨e, hes, hye⟩ := he
    exact ⟨e, hes, by rw [hpow, hye, mul_one, inv_mul_cancel]⟩
  have hcomm' : ∀ j : ℕ, τ * ((c⁻¹ * y * c) ^ j * τ * ((c⁻¹ * y * c) ^ j)⁻¹) =
      (c⁻¹ * y * c) ^ j * τ * ((c⁻¹ * y * c) ^ j)⁻¹ * τ := by
    intro j
    have h1 := hcomm j
    rw [hpow]
    have e1 : τ * (c⁻¹ * y ^ j * c * τ * (c⁻¹ * y ^ j * c)⁻¹) = c⁻¹ * ((c * τ * c⁻¹) *
        (y ^ j * (c * τ * c⁻¹) * (y ^ j)⁻¹)) * c := by group
    have e2 : c⁻¹ * y ^ j * c * τ * (c⁻¹ * y ^ j * c)⁻¹ * τ = c⁻¹ * (y ^ j * (c * τ * c⁻¹) *
        (y ^ j)⁻¹ * (c * τ * c⁻¹)) * c := by group
    rw [e1, e2, h1]
  obtain ⟨d, hd, m, hm⟩ := hcls _ hy' hmove' he' hcomm'
  refine ⟨c * d, heAutGroup.mul_mem (heP_le_heAutGroup hc) hd, m, fun bw hbw => ?_⟩
  have hU : (orbSub (c⁻¹ * y * c) τ).map (MulAut.conj c).toMonoidHom =
      orbSub y (c * τ * c⁻¹) := by
    rw [orbSub_map]
    congr 1
    show c * (c⁻¹ * y * c) * c⁻¹ = y
    group
  rw [← hU]
  refine ⟨d * elt bw * d⁻¹, hm bw hbw, ?_⟩
  show c * (d * elt bw * d⁻¹) * c⁻¹ = c * d * elt bw * (c * d)⁻¹
  group

theorem exists_ref_le_orbSub
    {t y : Equiv.Perm (Fin 8330)} (ht : t ∈ heP) (ht2 : orderOf t = 2) (hy : y ∈ heP)
    (hmove : y * t * y⁻¹ ≠ t) (he : ∃ e ∈ [25, 343, 17], y ^ e = 1)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * (y ^ j)⁻¹) = y ^ j * t * (y ^ j)⁻¹ * t) :
    ∃ d ∈ heAutGroup, ∃ m, ∀ bw ∈ refW m, d * elt bw * d⁻¹ ∈ orbSub y t := by
  have hcls : ∀ τ ∈ [heGenPerm 0, heT1P], ∀ y' ∈ heP, y' * τ * y'⁻¹ ≠ τ →
      (∃ e ∈ [25, 343, 17], y' ^ e = 1) →
      (∀ j : ℕ, τ * (y' ^ j * τ * (y' ^ j)⁻¹) = y' ^ j * τ * (y' ^ j)⁻¹ * τ) →
      ∃ d ∈ heAutGroup, ∃ m, ∀ bw ∈ refW m, d * elt bw * d⁻¹ ∈ orbSub y' τ := by
    intro τ hτ y' hy' hmv he' hcm
    obtain ⟨d, hd, h5 | h7⟩ := Certificates.certificate7222 τ hτ y' hy' hmv he' hcm
    · exact ⟨d, hd, 0, by rw [refW, if_pos rfl]; exact h5⟩
    · exact ⟨d, hd, 1, by rw [refW, if_neg one_ne_zero]; exact h7⟩
  rcases involution_conj_cases ht ht2 with ⟨c, hc, htc⟩ | ⟨c, hc, htc⟩
  · exact exists_ref_of_conj hc htc hy hmove he hcomm (hcls _ List.mem_cons_self)
  · exact exists_ref_of_conj hc htc hy hmove he hcomm
      (hcls _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem prime_dvd_he {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 4030387200) :
    p = 5 ∨ p = 7 ∨ p = 17 := by
  have h' : p ∣ 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h3))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1))

theorem exists_pow_eq_one {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 4030387200)
    {y : G} {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hyk : y ^ p ^ k = 1) (hy1 : y ≠ 1) :
    ∃ e ∈ [25, 343, 17], y ^ e = 1 := by
  obtain ⟨j, hj, hoy⟩ := exists_orderOf_eq_pow hp hyk hy1
  have hdvd : p ^ j ∣ 4030387200 := hoy ▸ hG ▸ orderOf_dvd_natCard y
  have hp1 : p ∣ 4030387200 := (dvd_pow_self p hj.ne').trans hdvd
  have hle : ∀ q, p ^ j ∣ q → (∀ i, p ^ i ∣ q → i ≤ j) → y ^ q = 1 := fun q hq _ =>
    orderOf_dvd_iff_pow_eq_one.mp (hoy ▸ hq)
  rcases prime_dvd_he hp hp5 hp1 with rfl | rfl | rfl
  · refine ⟨25, by simp, orderOf_dvd_iff_pow_eq_one.mp ?_⟩
    rw [hoy]
    have hj2 : j ≤ 2 := by
      by_contra h3
      have : 5 ^ 3 ∣ 4030387200 := (pow_dvd_pow 5 (by omega)).trans hdvd
      norm_num at this
    exact (pow_dvd_pow 5 hj2).trans (by norm_num)
  · refine ⟨343, by simp, orderOf_dvd_iff_pow_eq_one.mp ?_⟩
    rw [hoy]
    have hj3 : j ≤ 3 := by
      by_contra h4
      have : 7 ^ 4 ∣ 4030387200 := (pow_dvd_pow 7 (by omega)).trans hdvd
      norm_num at this
    exact (pow_dvd_pow 7 hj3).trans (by norm_num)
  · refine ⟨17, by simp, orderOf_dvd_iff_pow_eq_one.mp ?_⟩
    rw [hoy]
    have hj1 : j ≤ 1 := by
      by_contra h2
      have : 17 ^ 2 ∣ 4030387200 := (pow_dvd_pow 17 (by omega)).trans hdvd
      norm_num at this
    exact (pow_dvd_pow 17 hj1).trans (by norm_num)

theorem inspC31SporadicAt_he :
    CFSG.Quasithin.InspC31SporadicAt .He := by
  intro A _ _ S M₀ R M V hSn hSs hCS hM₀S hper _ _ hR2 hRM hMN hM₀R hsyl hVM₀ hVne hV hcomm hVc
    _ hNR _
  have h : Setup S M₀ R M V :=
    ⟨hSn, hSs, hper, hR2, hRM, hMN, hM₀R, hsyl, hVM₀, hVne, hV, hcomm, hVc, hNR⟩
  obtain ⟨ι, hι⟩ := exists_emb hSn hSs hCS
  have hne : ⁅V, M₀⁆ ≠ ⊥ := by rw [hcomm]; exact hVne
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm hper h.hM₀V hne
  have hy1 : y ≠ 1 := fun h1 => hyt (by rw [h1, one_mul, inv_one, mul_one])
  have hcommA : ∀ j : ℕ, t * (y ^ j * t * (y ^ j)⁻¹) = y ^ j * t * (y ^ j)⁻¹ * t := fun j => by
    have hm : y ^ j * t * (y ^ j)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.hM₀V hy) j) t).mp ht
    exact h.V_comm t ht _ hm
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      have := hV.2 t ht
      rwa [sq] at this
    · intro h1
      apply hyt
      rw [h1, mul_one, mul_inv_cancel]
  have hyS : y ∈ S := hM₀S hy
  have htS : t ∈ S := hM₀S (hVM₀ ht)
  have hyP := hι.mem_heP hyS
  have htP := hι.mem_heP htS
  have hy1' : ι y ≠ 1 := fun h1 => hy1 (hι.inj (by rw [h1, map_one]))
  have he : ∃ e ∈ [25, 343, 17], (ι y) ^ e = 1 := by
    have hyk' : (⟨ι y, hyP⟩ : ↥heP) ^ p ^ k = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, hyk, map_one, Subgroup.coe_one])
    obtain ⟨e, hes, hye⟩ := exists_pow_eq_one card_heP hp hp5 hyk'
      (fun h1 => hy1' (congrArg Subtype.val h1))
    exact ⟨e, hes, by simpa using congrArg Subtype.val hye⟩
  have hmove : ι y * ι t * (ι y)⁻¹ ≠ ι t := fun h1 => hyt (hι.inj (by
    rw [map_mul, map_mul, map_inv, h1]))
  have hcommP : ∀ j : ℕ, ι t * ((ι y) ^ j * ι t * ((ι y) ^ j)⁻¹) =
      (ι y) ^ j * ι t * ((ι y) ^ j)⁻¹ * ι t := fun j => by
    simp only [← map_pow, ← map_inv, ← map_mul, hcommA j]
  obtain ⟨d, hd, m, hm⟩ := exists_ref_le_orbSub htP
    (by rw [orderOf_injective ι hι.inj]; exact ht2) hyP hmove he hcommP
  have hι' := hι.conj (heAutGroup.inv_mem hd)
  have hU : ∀ bw ∈ refW m, elt bw ∈ V.map ((MulAut.conj d⁻¹).toMonoidHom.comp ι) := by
    intro bw hbw
    have hx := hm bw hbw
    rw [← orbSub_map] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨z, orbSub_le (h.hM₀V hy) ht hz, ?_⟩
    rw [MonoidHom.comp_apply, hzx]
    show d⁻¹ * (d * elt bw * d⁻¹) * d⁻¹⁻¹ = elt bw
    group
  by_cases hm0 : m = 0
  · subst hm0
    exact concl_w5 h hM₀S hι' (fun i => hU (w5W.getD i []) (by
      rw [refW, ite_eq_left rfl, List.getD_eq_getElem _ _ (by rw [len_w5W]; exact i.2)]
      exact List.getElem_mem _)) hy hp hp5 hyk hy1
  · exact (false_w7 h hι' (fun i => hU (w7W.getD i []) (by
      rw [refW, ite_eq_right hm0, List.getD_eq_getElem _ _ (by rw [len_w7W]; exact i.2)]
      exact List.getElem_mem _))).elim

end CFSG.Quasithin.KGC31.He

end
