module

public import CFSG.LocalAnalysis.UniquenessCase.UC6M591Dc
import CFSG.GH74.GLS.IVK.L2.SylowAux
import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAbel
public import CFSG.LocalAnalysis.UniquenessCase.UC6K591Defs
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open
open scoped IsMulCommutative commutatorElement

namespace UCK.M591D

theorem exists_odd_prime_dvd {S : Type*} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hab : ¬ IsMulCommutative S) : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card S := by
  by_contra h
  push Not at h
  have h2 : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card S → d = 2 := fun hd hdvd =>
    by_contra fun hne => h _ hd hne hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 S := IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' h2)
  haveI : Nontrivial S := hS.toNontrivial
  have hZ := hP.center_nontrivial
  have hZtop : center S = ⊤ := by
    rcases hS.eq_bot_or_eq_top_of_normal (center S) with h0 | h0
    · exact absurd h0 ((Subgroup.nontrivial_iff_ne_bot _).1 hZ)
    · exact h0
  exact hab ⟨⟨fun a b => mem_center_iff.1 (hZtop ▸ mem_top b) a⟩⟩

theorem isMulCommutative_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {H : Subgroup X}
    (hH : IsMulCommutative H) : IsMulCommutative (H.map f) :=
  ⟨⟨fun ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩ => Subtype.ext (by
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hH.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)))⟩⟩

theorem conj_mem_of_normal_subgroupOf {X : Type*} [Group X] {S W : Subgroup X} (hSW : S ≤ W)
    (hSn : (S.subgroupOf W).Normal) {w z : X} (hw : w ∈ W) (hz : z ∈ S) : w * z * w⁻¹ ∈ S := by
  have h := hSn.conj_mem ⟨z, hSW hz⟩ (mem_subgroupOf.2 hz) ⟨w, hw⟩
  rw [mem_subgroupOf] at h
  simpa using h

theorem moved_factor_false {X : Type*} [Group X] [Finite X] {N D W S : Subgroup X} (hD3 : Nat.card D = 3)
    (hcop : Nat.Coprime 3 (Nat.card N)) (hb : OddInvCent N D) [hWn : W.Normal] (hWN : W ≤ N) (hSW : S ≤ W)
    (hSs : IsSimpleGroup S) (hSn : (S.subgroupOf W).Normal) (hSab : ¬ IsMulCommutative S) {d : X}
    (hd : d ∈ D) (hdS : d ∉ normalizer (S : Set X)) : False := by
  obtain ⟨p, hp, hp2, hpS⟩ := exists_odd_prime_dvd hSs hSab
  haveI : Fact p.Prime := ⟨hp⟩
  have hDW : D ≤ normalizer (W : Set X) := by
    rw [normalizer_eq_top_iff.2 hWn]
    exact le_top
  have hcopW : Nat.Coprime 3 (Nat.card W) := Nat.Coprime.coprime_dvd_right (card_dvd_of_le hWN) hcop
  obtain ⟨Q, hQ, hDQ⟩ := exists_inv_sylow hp hD3 hcopW hDW
  have hQC : Q ≤ centralizer (D : Set X) := hb p hp hp2 Q (hQ.1.trans hWN) hQ.2.1 hDQ
  have hQS : Q ⊓ S ≠ ⊥ := by
    intro hbot
    obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hQ
    haveI : (S.subgroupOf W).Normal := hSn
    have hc := CFSG.GH74.GLS.IVK.card_sylow_inf_normal p P (S.subgroupOf W)
    have h1 : (P : Subgroup W) ⊓ S.subgroupOf W = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyQ : (y : X) ∈ Q := by
        rw [← hP]
        exact mem_map_of_mem _ hy.1
      have hy' : (y : X) ∈ Q ⊓ S := ⟨hyQ, hy.2⟩
      rw [hbot, mem_bot] at hy'
      exact mem_bot.2 (Subtype.ext hy')
    rw [h1, card_bot, Nat.card_congr (subgroupOfEquivOfLe hSW).toEquiv] at hc
    have hv : (Nat.card S).factorization p = 0 :=
      ((Nat.pow_eq_one.1 hc.symm).resolve_left hp.one_lt.ne')
    have := (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').1 hpS
    omega
  set Sd : Subgroup X := S.map (MulAut.conj d).toMonoidHom with hSd
  have hSdW : ∀ w ∈ W, ∀ y ∈ Sd, w * y * w⁻¹ ∈ Sd := by
    intro w hw y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hw' : d⁻¹ * w * d ∈ W := by simpa using hWn.conj_mem w hw d⁻¹
    refine ⟨_, conj_mem_of_normal_subgroupOf hSW hSn hw' hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hTn : ((S ⊓ Sd).subgroupOf S).Normal := by
    refine ⟨fun t ht s => ?_⟩
    rw [mem_subgroupOf] at ht ⊢
    exact ⟨(s * t * s⁻¹).2, by simpa using hSdW s (hSW s.2) t ht.2⟩
  haveI := hTn
  rcases hSs.eq_bot_or_eq_top_of_normal ((S ⊓ Sd).subgroupOf S) with hT | hT
  · have hdisj : S ⊓ Sd = ⊥ := by
      have h := subgroupOf_eq_bot.1 hT
      rw [eq_bot_iff]
      intro x hx
      exact h.le_bot ⟨hx, hx.1⟩
    apply hQS
    rw [eq_bot_iff, ← hdisj]
    intro x hx
    have hxd : d * x = x * d := mem_centralizer_iff.1 (hQC hx.1) d hd
    refine ⟨hx.2, x, hx.2, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxd, mul_inv_cancel_right]
  · apply hdS
    have hle : S ≤ Sd := by
      intro s hs
      have : (⟨s, hs⟩ : S) ∈ (S ⊓ Sd).subgroupOf S := by
        rw [hT]
        exact mem_top _
      exact (mem_subgroupOf.1 this).2
    have heq : S = Sd :=
      eq_of_le_of_card_ge hle (by rw [hSd, card_map_of_injective (MulAut.conj d).injective])
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [heq]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [heq] at hh
      obtain ⟨y, hy, hyh⟩ := hh
      have hyh' : d * y * d⁻¹ = d * h * d⁻¹ := by simpa [MulAut.conj_apply] using hyh
      have : y = h := by simpa using hyh'
      exact this ▸ hy

theorem fixed_factor_false (hKSz : KSz) {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    {N D S : Subgroup X} (hD3 : Nat.card D = 3) (hcop : Nat.Coprime 3 (Nat.card N)) (hb : OddInvCent N D)
    (hSN : S ≤ N) (hSs : IsSimpleGroup S) (hSab : ¬ IsMulCommutative S) {d : X} (hd : d ∈ D)
    (hdS : d ∈ normalizer (S : Set X)) {s : X} (hs : s ∈ S) (hds : d * s ≠ s * d) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hds (by simp)
  have hord : orderOf d = 3 := by
    have hdvd : orderOf d ∣ 3 := by
      have := orderOf_dvd_natCard (⟨d, hd⟩ : D)
      rwa [Subgroup.orderOf_mk, hD3] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hd1
    · exact h
  have hDz : zpowers d = D :=
    eq_of_le_of_card_ge (zpowers_le.2 hd) (by rw [hD3, Nat.card_zpowers, hord])
  have hDS : D ≤ normalizer (S : Set X) := by
    rw [← hDz]
    exact zpowers_le.2 hdS
  set α : MulAut S := S.normalizerMonoidHom ⟨d, hdS⟩ with hα
  have hαapp : ∀ x : S, ((α x : S) : X) = d * x * d⁻¹ := fun x =>
    S.normalizerMonoidHom_apply_apply_coe _ x
  have hα3 : α ^ 3 = 1 := by
    have h3 : (⟨d, hdS⟩ : normalizer (S : Set X)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hord, pow_orderOf_eq_one]
    rw [hα, ← map_pow, h3, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    apply hds
    have h2 : ((α ⟨s, hs⟩ : S) : X) = s := by rw [h1]; rfl
    rw [hαapp] at h2
    rw [← mul_inv_eq_iff_eq_mul]
    exact h2
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hS3 : Nat.Coprime 3 (Nat.card S) := Nat.Coprime.coprime_dvd_right (card_dvd_of_le hSN) hcop
  obtain ⟨p, hp, hp2, hndvd⟩ := hKSz S (hX.subgroup S) hSs hSab hS3 α hαord
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ, hDQ⟩ := exists_inv_sylow hp hD3 hS3 hDS
  have hQC : Q ≤ centralizer (D : Set X) := hb p hp hp2 Q (hQ.1.trans hSN) hQ.2.1 hDQ
  apply hndvd
  rw [← card_of_fusionIsSylowIn hQ]
  set C : Subgroup S := (centralizer ({d} : Set X)).subgroupOf S with hC
  have hQC' : Q.subgroupOf S ≤ C := by
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact centralizer_le (Set.singleton_subset_iff.2 hd) (hQC hx)
  have h1 : Nat.card Q ∣ Nat.card C := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hQ.1).toEquiv]
    exact card_dvd_of_le hQC'
  have h2 : Nat.card C = Nat.card {x : S // α x = x} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun x => ?_)
    rw [hC, mem_subgroupOf, mem_centralizer_singleton_iff, Subtype.ext_iff, hαapp, mul_inv_eq_iff_eq_mul]
    exact ⟨Eq.symm, Eq.symm⟩
  rwa [← h2]

theorem nonabelian_case_false (hKSz : KSz) {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    {N D W : Subgroup X} (hD3 : Nat.card D = 3) (hcop : Nat.Coprime 3 (Nat.card N)) (hb : OddInvCent N D)
    (hcomm : ⁅N, D⁆ = N) [hWn : W.Normal] (hWN : W ≤ N) {r : ℕ} (S : Fin r → Subgroup X)
    (hSW : ∀ i, S i ≤ W) (hSs : ∀ i, IsSimpleGroup (S i)) (hSn : ∀ i, ((S i).subgroupOf W).Normal)
    (hSab : ∀ i, ¬ IsMulCommutative (S i)) (i₀ : Fin r) (e : ((i : Fin r) → S i) ≃* W)
    (he : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : X) = x i) : False := by
  classical
  by_cases hall : ∀ i, S i ≤ centralizer (D : Set X)
  ·
    have hWD : W ≤ centralizer (D : Set X) := by
      intro w hw
      set x := e.symm ⟨w, hw⟩ with hx
      have hxP : x ∈ ((centralizer (D : Set X)).subgroupOf W).comap e.toMonoidHom := by
        apply Subgroup.pi_mem_of_mulSingle_mem
        intro i
        rw [mem_comap, mem_subgroupOf, MulEquiv.coe_toMonoidHom,
          he i (Pi.mulSingle i (x i)) (fun j hj => Pi.mulSingle_eq_of_ne hj _), Pi.mulSingle_eq_same]
        exact hall i (x i).2
      rw [mem_comap, mem_subgroupOf, MulEquiv.coe_toMonoidHom, hx, MulEquiv.apply_symm_apply] at hxP
      exact hxP
    have hkey : ⁅N, D⁆ ≤ centralizer (W : Set X) := by
      rw [commutator_le]
      intro n _ d hd
      rw [mem_centralizer_iff]
      intro w hw
      have hdw : ∀ y ∈ W, d * y = y * d := fun y hy => mem_centralizer_iff.1 (hWD hy) d hd
      have hw₁ : n⁻¹ * w * n ∈ W := by simpa using hWn.conj_mem w hw n⁻¹
      have e1 := hdw w hw
      have e2 := hdw _ hw₁
      rw [commutatorElement_def]
      calc w * (n * d * n⁻¹ * d⁻¹) = n * ((n⁻¹ * w * n) * d) * n⁻¹ * d⁻¹ := by group
        _ = n * (d * (n⁻¹ * w * n)) * n⁻¹ * d⁻¹ := by rw [← e2]
        _ = n * d * n⁻¹ * d⁻¹ * (d * w) * d⁻¹ := by group
        _ = n * d * n⁻¹ * d⁻¹ * (w * d) * d⁻¹ := by rw [e1]
        _ = n * d * n⁻¹ * d⁻¹ * w := by group
    apply hSab i₀
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hbN : (b : X) ∈ ⁅N, D⁆ := by
      rw [hcomm]
      exact hWN (hSW i₀ b.2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact mem_centralizer_iff.1 (hkey hbN) a (hSW i₀ a.2)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨s, hs, hsD⟩ := SetLike.not_le_iff_exists.1 hi
    rw [mem_centralizer_iff] at hsD
    push Not at hsD
    obtain ⟨d, hd, hds⟩ := hsD
    by_cases hdS : d ∈ normalizer (S i : Set X)
    · exact fixed_factor_false hKSz hX hD3 hcop hb ((hSW i).trans hWN) (hSs i) (hSab i) hd hdS hs hds
    · exact moved_factor_false hD3 hcop hb hWN (hSW i) (hSs i) (hSn i) (hSab i) hd hdS

theorem lemmaC_step (hKSz : KSz) {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X) {N D : Subgroup X}
    (hND : N ⊔ D = ⊤) (hDN : D ≤ normalizer (N : Set X)) (hD3 : Nat.card D = 3)
    (hcop : Nat.Coprime 3 (Nat.card N)) (hb : OddInvCent N D) (IH : LemmaCBelow (Nat.card N)) :
    ∃ k : ℕ, Nat.card ↥⁅N, D⁆ = 2 ^ k := by
  have hNn : N.Normal := normalizer_eq_top_iff.1 (top_le_iff.1 (hND ▸ sup_le le_normalizer hDN))
  have hNDN : ⁅N, D⁆ ≤ N := le_normalizer_iff_commutator_le_left.1 hDN
  by_cases hcomm : ⁅N, D⁆ = N
  · by_cases hN1 : N = ⊥
    · exact ⟨0, by rw [hcomm, hN1, card_bot, pow_zero]⟩
    obtain ⟨W, ⟨hWn, hW1, hWN⟩, hWmin⟩ :=
      (Set.toFinite {W : Subgroup X | W.Normal ∧ W ≠ ⊥ ∧ W ≤ N}).exists_minimal ⟨N, hNn, hN1, le_rfl⟩
    haveI := hWn
    have hmin : ∀ M : Subgroup X, M.Normal → M ≤ W → M = ⊥ ∨ M = W := fun M hM hle =>
      (em (M = ⊥)).imp id fun hM1 => le_antisymm hle (hWmin ⟨hM, hM1, hle.trans hWN⟩ hle)
    obtain ⟨k, hk⟩ := card_eq_two_pow_mul hX hNn hD3 hcop hb hcomm hWN hW1 IH
    obtain ⟨r, S, hr, hSW, hSs, hconj, hSn, e, he⟩ :=
      CFSG.LocalCores.minimal_normal_simple_factors hWn hW1 hmin
    set i₀ : Fin r := ⟨0, hr⟩
    have hcardS : ∀ i, Nat.card (S i) = Nat.card (S i₀) := by
      intro i
      obtain ⟨g, hg⟩ := hconj i₀ i
      rw [hg, CFSG.conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
    by_cases hab : IsMulCommutative (S i₀)
    ·
      haveI := hab
      haveI := hSs i₀
      have hq : (Nat.card (S i₀)).Prime := IsSimpleGroup.prime_card
      have hW : Nat.card W = Nat.card (S i₀) ^ r := by
        rw [← Nat.card_congr e.toEquiv, Nat.card_pi]
        simp only [hcardS, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact abelian_case hDN hD3 hcop hb hWN hq hW hk
    · exfalso
      have hSab : ∀ i, ¬ IsMulCommutative (S i) := by
        intro i hi
        obtain ⟨g, hg⟩ := hconj i i₀
        apply hab
        rw [hg]
        exact isMulCommutative_map _ hi
      exact nonabelian_case_false hKSz hX hD3 hcop hb hcomm hWN S hSW hSs hSn hSab i₀ e he
  ·
    have hlt : Nat.card ↥⁅N, D⁆ < Nat.card N := card_lt_of_lt (lt_of_le_of_ne hNDN hcomm)
    have hcop' := Nat.Coprime.coprime_dvd_right (card_dvd_of_le hNDN) hcop
    obtain ⟨k, hk⟩ := IH X hX ⁅N, D⁆ D hlt (normalizer_commutator_ge_right N D) hD3 hcop' (hb.mono hNDN)
    refine ⟨k, ?_⟩
    rwa [CFSG.Quasithin.H13.coprime_commutator_commutator_eq hDN (by rw [hD3]; exact hcop)] at hk

end UCK.M591D

open UCK.M591D in
theorem UCK.lemmaC_of_KSz (h : UCK.KSz) : UCK.LemmaC := by
  suffices H : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ N D : Subgroup X,
      Nat.card N = n → D ≤ normalizer (N : Set X) → Nat.card D = 3 → Nat.Coprime 3 (Nat.card N) →
        OddInvCent N D → ∃ k : ℕ, Nat.card ↥⁅N, D⁆ = 2 ^ k by
    intro X _ _ hX N D hDN hD3 hcop hb
    exact H _ X hX N D rfl hDN hD3 hcop hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ hX N D hn hDN hD3 hcop hb
    refine lemmaC_of_restrict hX hDN hD3 hcop hb ?_
    intro Y _ _ hY N' D' hsup hcard hD'N' hD'3 hcop' hb'
    refine lemmaC_step h hY hsup hD'N' hD'3 hcop' hb' ?_
    intro Z _ _ hZ N'' D'' hlt hD''N'' hD''3 hcop'' hb''
    exact ih _ (by omega) Z hZ N'' D'' rfl hD''N'' hD''3 hcop'' hb''

end CFSG.LocalAnalysis.UniquenessCase
