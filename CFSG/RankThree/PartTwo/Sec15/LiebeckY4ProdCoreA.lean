module

public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdDefs
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiag
import CFSG.RankThree.PartTwo.Sec17.Item1722ProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag

section Elementary

variable {Γ : Type} [Group Γ]

private theorem mem_of_pow_mem {S : Subgroup Γ} {x : Γ} {m k : ℕ} (hm : ¬ 3 ∣ m)
    (h1 : x ^ m ∈ S) (h2 : x ^ 3 ^ k = 1) : x ∈ S := by
  have hcop : Nat.Coprime m (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h2)
      (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact S.pow_mem h1 j

private theorem not_three_dvd_orderOf [Finite Γ] {Q : Subgroup Γ} (hQ : ¬ 3 ∣ Nat.card Q) {q : Γ}
    (hq : q ∈ Q) : ¬ 3 ∣ orderOf q :=
  fun h => hQ (h.trans (Subgroup.orderOf_dvd_natCard Q hq))

private theorem mem_of_mul_pow {S : Subgroup Γ} {a b q : Γ} (hq : q = a * b)
    (hab : a * b = b * a) (hb : b ∈ S) (ha : ∃ k : ℕ, a ^ 3 ^ k = 1)
    (hord : ¬ 3 ∣ orderOf q) : q ∈ S := by
  subst hq
  obtain ⟨k, hk⟩ := ha
  have h1 : (a * b) ^ orderOf (a * b) = 1 := pow_orderOf_eq_one _
  rw [(show Commute a b from hab).mul_pow] at h1
  have h2 : a ^ orderOf (a * b) ∈ S := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact S.inv_mem (S.pow_mem hb _)
  exact S.mul_mem (mem_of_pow_mem hord h2 hk) hb

end Elementary

section TypeA

variable {Γ : Type} [Group Γ] [Finite Γ]

private theorem center_pow_three {W : Subgroup Γ} (hW : FacA5 ↥W ∨ FacA6 ↥W) {z : Γ} (hz : z ∈ W)
    (hzc : ∀ w ∈ W, w * z = z * w) : z ^ 3 = 1 := by
  have hmem : (⟨z, hz⟩ : ↥W) ∈ Subgroup.center ↥W :=
    Subgroup.mem_center_iff.mpr fun w => Subtype.ext (hzc w w.2)
  rcases hW with h5 | ⟨-, hcard, -⟩
  · obtain ⟨e⟩ := h5
    rw [center_eq_bot_five e, Subgroup.mem_bot] at hmem
    have h1 : z = 1 := congrArg Subtype.val hmem
    rw [h1, one_pow]
  · have h := pow_card_eq_one' (G := Subgroup.center ↥W) (x := ⟨⟨z, hz⟩, hmem⟩)
    rw [hcard] at h
    exact congrArg (fun x : ↥W => (x : Γ)) (congrArg Subtype.val h)

private theorem fix_of_typeA (hF5 : FixA5) (hF6 : FixA6Cover) {W : Subgroup Γ}
    (hW : FacA5 ↥W ∨ FacA6 ↥W) {b : Γ} (hbN : b ∈ Subgroup.normalizer (W : Set Γ))
    (hb3 : b ^ 3 = 1) (hbC : b ∉ Subgroup.centralizer (W : Set Γ)) {w : Γ} (hw : w ∈ W)
    (hcen : ∀ x ∈ W, x * (w⁻¹ * (b * w * b⁻¹)) = (w⁻¹ * (b * w * b⁻¹)) * x) :
    ∃ k : ℕ, w ^ 3 ^ k = 1 := by
  set σ : MulAut ↥W := W.normalizerMonoidHom ⟨b, hbN⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have h1 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (W : Set Γ))) ^ 3 = 1 := Subtype.ext hb3
    rw [h1, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hbC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun τ : MulAut ↥W => ((τ ⟨x, hx⟩ : ↥W) : Γ)) h
    simp only [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h1
    calc x * b = b * x * b⁻¹ * b := by rw [h1]
      _ = b * x := by group
  have hσw : ((σ ⟨w, hw⟩ : ↥W) : Γ) = b * w * b⁻¹ := by
    rw [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hy : (⟨w, hw⟩ : ↥W)⁻¹ * σ ⟨w, hw⟩ ∈ Subgroup.center ↥W := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := hcen g g.2
    simpa [hσw] using this
  rcases hW with h5 | ⟨hp, hcard, hφ⟩
  · obtain ⟨e⟩ := h5
    rw [center_eq_bot_five e, Subgroup.mem_bot, inv_mul_eq_one] at hy
    obtain ⟨k, hk⟩ := hF5 ↥W ⟨e⟩ σ hσ3 hσ1 ⟨w, hw⟩ hy.symm
    exact ⟨k, congrArg Subtype.val hk⟩
  · obtain ⟨k, hk⟩ := hF6 ↥W ⟨hp, hcard, hφ⟩ σ hσ3 hσ1 ⟨w, hw⟩ hy
    refine ⟨k + 1, ?_⟩
    have h := pow_card_eq_one' (G := Subgroup.center ↥W) (x := ⟨_, hk⟩)
    rw [hcard] at h
    have h2 := congrArg (fun x : ↥W => (x : Γ)) (congrArg Subtype.val h)
    simpa [pow_succ, pow_mul] using h2

private theorem eq_bot_of_normal_typeA {W : Subgroup Γ} (hW : FacA5 ↥W ∨ FacA6 ↥W)
    {N : Subgroup Γ} (hNW : N ≤ W) (hn : ∀ x ∈ W, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (h3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  have hnorm : (N.subgroupOf W).Normal := by
    refine ⟨fun x hx w => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn w w.2 x hx
  have hcard : Nat.card (N.subgroupOf W) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
  have hbot : N.subgroupOf W = ⊥ → N = ⊥ := fun h => by
    rwa [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hNW] at h
  rcases hW with h5 | ⟨hp, hcard3, hφ⟩
  · obtain ⟨e⟩ := h5
    haveI := isSimpleGroup_five e
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf W) with h | h
    · exact hbot h
    · exfalso
      rw [h, Subgroup.card_top, card_five e] at hcard
      exact h3 (by rw [← hcard]; norm_num)
  · have hq := isQuasisimple_tripleCover hp ⟨hcard3, hφ⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hnorm with h | h
    · exfalso
      rw [h, Subgroup.card_top, card_tripleCover ⟨hcard3, hφ⟩] at hcard
      exact h3 (by rw [← hcard]; norm_num)
    · apply hbot
      have h1 : Nat.card (N.subgroupOf W) ∣ 3 := hcard3 ▸ Subgroup.card_dvd_of_le h
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
      · exact Subgroup.eq_bot_of_card_eq _ h2
      · exact absurd (by rw [← hcard, h2]) h3

end TypeA

section Core

variable {Γ : Type} [Group Γ] [Finite Γ] {U V E : Subgroup Γ}

private theorem core_left (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hfixV : ∀ v ∈ V, (∀ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), b * v * b⁻¹ = v) →
      ∃ k : ℕ, v ^ 3 ^ k = 1)
    {Q : Subgroup Γ} (hQD : Q ≤ U ⊔ V) (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hBQ : E ⊓ Subgroup.centralizer (U : Set Γ) ≤ Subgroup.centralizer (Q : Set Γ)) : Q ≤ U := by
  intro q hq
  obtain ⟨u, hu, v, hv, hqe⟩ := exists_mul_eq_of_mem_sup hc (hQD hq)
  have hvfix : ∀ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), b * v * b⁻¹ = v := by
    intro b hb
    have h1 : q * b = b * q := Subgroup.mem_centralizer_iff.mp (hBQ hb) q hq
    have h2 : u * b = b * u := Subgroup.mem_centralizer_iff.mp hb.2 u hu
    have h3 : v * b = b * v := by
      refine mul_left_cancel (a := u) ?_
      calc u * (v * b) = u * v * b := (mul_assoc _ _ _).symm
        _ = b * (u * v) := by rw [← hqe]; exact h1
        _ = b * u * v := (mul_assoc _ _ _).symm
        _ = u * b * v := by rw [h2]
        _ = u * (b * v) := mul_assoc _ _ _
    calc b * v * b⁻¹ = v * b * b⁻¹ := by rw [← h3]
      _ = v := by group
  obtain ⟨k, hk⟩ := hfixV v hv hvfix
  exact mem_of_mul_pow (hqe.trans (hc u hu v hv)) (hc u hu v hv).symm hu ⟨k, hk⟩
    (not_three_dvd_orderOf hQ3 hq)

private theorem core_right (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hEU : E ≤ Subgroup.normalizer (U : Set Γ)) (hEV : E ≤ Subgroup.normalizer (V : Set Γ))
    (hfixU : ∀ b ∈ E, b ∉ Subgroup.centralizer (U : Set Γ) → ∀ u ∈ U,
      u⁻¹ * (b * u * b⁻¹) ∈ U ⊓ V → ∃ k : ℕ, u ^ 3 ^ k = 1)
    {b : Γ} (hbE : b ∈ E) (hbU : b ∉ Subgroup.centralizer (U : Set Γ))
    {Q : Subgroup Γ} (hQD : Q ≤ U ⊔ V) (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hbQ : ∀ q ∈ Q, q * b = b * q) : Q ≤ V := by
  intro q hq
  obtain ⟨u, hu, v, hv, hqe⟩ := exists_mul_eq_of_mem_sup hc (hQD hq)
  have hbu : b * u * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hEU hbE) u).mp hu
  have hbv : b * v * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hEV hbE) v).mp hv
  have hz : u⁻¹ * (b * u * b⁻¹) ∈ U ⊓ V := by
    have h1 : b * q * b⁻¹ = q := by rw [← hbQ q hq]; group
    have h2 : (b * u * b⁻¹) * (b * v * b⁻¹) = u * v := by
      have h3 : b * (u * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹) := by group
      rw [← h3, ← hqe]
      exact h1
    have h3 : u⁻¹ * (b * u * b⁻¹) = v * (b * v * b⁻¹)⁻¹ := by
      have h4 : b * u * b⁻¹ = u * v * (b * v * b⁻¹)⁻¹ := by rw [← h2]; group
      rw [h4]
      group
    exact ⟨U.mul_mem (U.inv_mem hu) hbu, h3 ▸ V.mul_mem hv (V.inv_mem hbv)⟩
  obtain ⟨k, hk⟩ := hfixU b hbE hbU u hu hz
  exact mem_of_mul_pow hqe (hc u hu v hv) hv ⟨k, hk⟩ (not_three_dvd_orderOf hQ3 hq)

private theorem core_pcore (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hZ : ∀ z ∈ U, (∀ w ∈ U, w * z = z * w) → z ^ 3 = 1)
    (hN : ∀ N : Subgroup Γ, N ≤ U → (∀ x ∈ U, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
      ¬ 3 ∣ Nat.card N → N = ⊥)
    (hfixV : ∀ v ∈ V, (∀ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), b * v * b⁻¹ = v) →
      ∃ k : ℕ, v ^ 3 ^ k = 1) :
    pPrimeCoreOf 3 ((U ⊔ V) ⊓ Subgroup.centralizer
      ((E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) : Set Γ)) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := (U ⊔ V) ⊓ Subgroup.centralizer
    ((E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) : Set Γ)
  set N := pPrimeCoreOf 3 T
  have hNT : N ≤ T := pPrimeCoreOf_le 3 T
  have hTN : T ≤ Subgroup.normalizer (N : Set Γ) := le_normalizer_pPrimeCoreOf 3 T
  have hNcop : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 T
  have hUT : U ≤ T := by
    refine fun u hu => ⟨Subgroup.mem_sup_left hu, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hb.2 u hu).symm
  have hNU : N ⊓ U = ⊥ := by
    refine hN (N ⊓ U) inf_le_right (fun x hx n hn => ⟨?_, U.mul_mem (U.mul_mem hx hn.2)
      (U.inv_mem hx)⟩) fun h3 => ?_
    · exact (Subgroup.mem_normalizer_iff.mp (hTN (hUT hx)) n).mp hn.1
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hNcop) h3
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨u, hu, v, hv, hne⟩ := exists_mul_eq_of_mem_sup hc (hNT hn).1
  have hnU : ∀ x ∈ U, x * n = n * x := by
    intro x hx
    have h1 : x * n * x⁻¹ * n⁻¹ ∈ N ⊓ U := by
      refine ⟨N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTN (hUT hx)) n).mp hn) (N.inv_mem hn),
        ?_⟩
      have h2 : v * x⁻¹ = x⁻¹ * v := by
        have := hc x⁻¹ (U.inv_mem hx) v hv
        exact this.symm
      have h3 : x * n * x⁻¹ * n⁻¹ = x * u * x⁻¹ * u⁻¹ := by
        rw [hne]
        calc x * (u * v) * x⁻¹ * (u * v)⁻¹ = x * u * (v * x⁻¹) * v⁻¹ * u⁻¹ := by group
          _ = x * u * (x⁻¹ * v) * v⁻¹ * u⁻¹ := by rw [h2]
          _ = x * u * x⁻¹ * u⁻¹ := by group
      rw [h3]
      exact U.mul_mem (U.mul_mem (U.mul_mem hx hu) (U.inv_mem hx)) (U.inv_mem hu)
    rw [hNU, Subgroup.mem_bot] at h1
    calc x * n = x * n * x⁻¹ * n⁻¹ * (n * x) := by group
      _ = n * x := by rw [h1, one_mul]
  have hucen : ∀ x ∈ U, x * u = u * x := fun x hx =>
    comm_left_of_comm_mul hc hx hv (by rw [← hne]; exact hnU x hx)
  have hu3 : u ^ 3 = 1 := hZ u hu hucen
  have hvfix : ∀ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), b * v * b⁻¹ = v := by
    intro b hb
    have h1 : b * n = n * b := Subgroup.mem_centralizer_iff.mp (hNT hn).2 b hb
    have h2 : u * b = b * u := Subgroup.mem_centralizer_iff.mp hb.2 u hu
    have h3 : v * b = b * v := by
      refine mul_left_cancel (a := u) ?_
      calc u * (v * b) = u * v * b := (mul_assoc _ _ _).symm
        _ = b * (u * v) := by rw [← hne]; exact h1.symm
        _ = b * u * v := (mul_assoc _ _ _).symm
        _ = u * b * v := by rw [h2]
        _ = u * (b * v) := mul_assoc _ _ _
    calc b * v * b⁻¹ = v * b * b⁻¹ := by rw [← h3]
      _ = v := by group
  obtain ⟨k, hk⟩ := hfixV v hv hvfix
  have hn3 : n ^ 3 ^ (k + 1) = 1 := by
    have e : 3 ^ (k + 1) = 3 * 3 ^ k := pow_succ' 3 k
    rw [hne, (show Commute u v from hc u hu v hv).mul_pow, e, pow_mul, pow_mul', hu3, hk, one_pow,
      one_pow, one_mul]
  have hord : ¬ 3 ∣ orderOf n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hn) hNcop)
  have hn1 : n ∈ (⊥ : Subgroup Γ) := mem_of_pow_mem hord
    (by rw [pow_orderOf_eq_one]; exact one_mem _) hn3
  exact hn1

end Core

section Counting

variable {Γ : Type} [Group Γ] [Finite Γ] {U V E : Subgroup Γ}

private theorem prodSetting_symm (h : ProdSetting U V E) : ProdSetting V U E where
  comm v hv u hu := (h.comm u hu v hv).symm
  elem := h.elem
  card := h.card
  norm := by rw [sup_comm]; exact h.norm
  perfect := by rw [sup_comm]; exact h.perfect
  rank := h.rank
  gen := by rw [sup_comm]; exact h.gen

private theorem nine_le_card_inf_centralizer (hs : ProdSetting U V E)
    (hEU : E ≤ Subgroup.normalizer (U : Set Γ)) (hEV : E ≤ Subgroup.normalizer (V : Set Γ))
    (hU : FacA5 ↥U ∨ FacA6 ↥U) :
    9 ≤ Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) := by
  have hc := hs.comm
  rcases hU with h5 | ⟨hUp, hcard3, hφ⟩
  · obtain ⟨eU⟩ := h5
    have h := card_le_mul_card_inf_centralizer hEU hs.elem (card_le_three_of_mulAut_five' eU)
    rw [hs.card] at h
    omega
  · by_contra hlt
    push Not at hlt
    have hge := card_le_mul_card_inf_centralizer hEU hs.elem
      (card_le_nine_of_mulAut_tripleCover' hUp ⟨hcard3, hφ⟩)
    rw [hs.card] at hge
    have hdvd : Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) ∣ 27 :=
      hs.card ▸ Subgroup.card_dvd_of_le inf_le_left
    have hKU : Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) = 3 := by
      generalize Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) = k at *
      interval_cases k <;> omega
    obtain ⟨eXU⟩ := hφ
    set ρ := (actQ U).comp (Subgroup.inclusion hEU)
    have hker : Nat.card ρ.ker = 3 := by
      have hk : ρ.ker.map E.subtype = E ⊓ Subgroup.centralizer (U : Set Γ) := by
        ext g
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.2, mem_centralizer_of_actQ_eq_one hUp hx⟩
        · rintro ⟨hgE, hgC⟩
          exact ⟨⟨g, hgE⟩, actQ_eq_one_of_mem_centralizer hgC, rfl⟩
      rw [← Subgroup.card_map_of_injective E.subtype_injective, hk, hKU]
    have hrange : Nat.card ρ.range = 9 := by
      have h1 : Nat.card E = Nat.card ρ.range * Nat.card ρ.ker := by
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
        exact Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
      rw [hs.card, hker] at h1
      omega
    have hrange3 : IsPGroup 3 ρ.range :=
      (isPGroup_of_isElemAbelian hs.elem).of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    have hQV : ∀ Q : Subgroup Γ, Q ≤ U ⊔ V → E ≤ Subgroup.normalizer (Q : Set Γ) →
        ¬ 3 ∣ Nat.card Q → Q ≤ V := by
      intro Q hQD hEQ hQ3
      set Qb := (Q.subgroupOf (U ⊔ V)).map (projQ hc)
      have hQb3 : ¬ 3 ∣ Nat.card Qb := fun h3' => hQ3 (h3'.trans (by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQD).toEquiv]
        exact Subgroup.card_map_dvd _ _))
      have hinv : ∀ σ ∈ ρ.range, ∀ q ∈ Qb, σ q ∈ Qb := by
        rintro _ ⟨e, rfl⟩ _ ⟨q, hq, rfl⟩
        have hq' : (q : Γ) ∈ Q := Subgroup.mem_subgroupOf.mp hq
        have heq : (e : Γ) * q * (e : Γ)⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hEQ e.2) q).mp hq'
        have heqD : (e : Γ) * q * (e : Γ)⁻¹ ∈ U ⊔ V := hQD heq
        have h1 := projQ_conj hc (hEU e.2) (hEV e.2) q heqD
        have hρe : ρ e = actQ U ⟨e, hEU e.2⟩ := rfl
        rw [hρe, ← h1]
        exact ⟨⟨_, heqD⟩, Subgroup.mem_subgroupOf.mpr heq, rfl⟩
      have hQbb := eq_bot_of_le_mulAut_six eXU hrange3 hrange hQb3 hinv
      intro q hq
      have h1 : projQ hc ⟨q, hQD hq⟩ = 1 := by
        have h2 : projQ hc ⟨q, hQD hq⟩ ∈ Qb :=
          ⟨⟨q, hQD hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
        rwa [hQbb, Subgroup.mem_bot] at h2
      obtain ⟨z, hz, hzc, v, hv, hqz⟩ := exists_of_projQ_eq_one hc h1
      have hz3 : z ^ 3 = 1 := center_pow_three (Or.inr ⟨hUp, hcard3, ⟨eXU⟩⟩) hz hzc
      exact mem_of_mul_pow hqz (hc z hz v hv) hv ⟨1, by simpa using hz3⟩
        (not_three_dvd_orderOf hQ3 hq)
    have hDV : U ⊔ V ≤ V :=
      hs.gen.trans (sSup_le fun Q hQ => hQV Q hQ.1.1 hQ.1.2.1 hQ.1.2.2)
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_fac (Or.inr ⟨hUp, hcard3, ⟨eXU⟩⟩)
    exact hab (Subtype.ext (hc a a.2 b (hDV (Subgroup.mem_sup_left b.2))))

private theorem card_eq_nine_of_counting {K L : Subgroup Γ} (hE : Nat.card E = 27) (hK : K ≤ E)
    (hL : L ≤ E) (h9 : 9 ≤ Nat.card K) (hz : Nat.card (K ⊓ L : Subgroup Γ) ≤ 3)
    (hzL : Nat.card (K ⊓ L : Subgroup Γ) < Nat.card L) : Nat.card K = 9 ∧ ¬ K ≤ L := by
  have hdvd : Nat.card K ∣ 27 := hE ▸ Subgroup.card_dvd_of_le hK
  have hle : Nat.card K ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
  have hne : ¬ K ≤ L := by
    intro h
    rw [inf_eq_left.mpr h] at hz
    omega
  refine ⟨?_, hne⟩
  by_contra h9'
  have h27 : Nat.card K = 27 := by
    generalize Nat.card K = k at *
    interval_cases k <;> omega
  have hKE : K = E := Subgroup.eq_of_le_of_card_ge hK (by omega)
  rw [hKE, inf_eq_right.mpr hL] at hzL
  exact lt_irrefl _ hzL

end Counting

section Rank

variable {Γ : Type} [Group Γ] [Finite Γ] {U V E : Subgroup Γ}

private theorem card_center_le {F₁ F₂ S : Subgroup Γ} (hs : ProdSetting U V E)
    (hF₁ : CFSG.Assembly.IsElemAbelian 3 F₁) (hF₂ : CFSG.Assembly.IsElemAbelian 3 F₂)
    (h₁ : F₁ ≤ U) (h₂ : F₂ ≤ V)
    (hS : ∀ z ∈ U, (∀ w ∈ U, w * z = z * w) → ∀ z' ∈ V, (∀ w ∈ V, w * z' = z' * w) →
      z * z' ∈ S) :
    Nat.card ((E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ)) :
        Subgroup Γ) * (Nat.card F₁ * Nat.card F₂) ≤
      27 * Nat.card S * Nat.card (U ⊓ V : Subgroup Γ) := by
  obtain ⟨hFab, hFcard⟩ := elemAbelian_sup hs.comm hF₁ hF₂ h₁ h₂
  have hFD : F₁ ⊔ F₂ ≤ U ⊔ V := sup_le_sup h₁ h₂
  set Z := (E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ))
  have hZE : CFSG.Assembly.IsElemAbelian 3 Z :=
    isElemAbelian_of_le hs.elem (inf_le_left.trans inf_le_left)
  have hZU : Z ≤ Subgroup.centralizer (U : Set Γ) := inf_le_left.trans inf_le_right
  have hZV : Z ≤ Subgroup.centralizer (V : Set Γ) := inf_le_right.trans inf_le_right
  have hG := card_mul_le_of_comm hs.rank hZE hFab (comm_of_centralizes hs.comm hZU hZV hFD)
  have hZF : Z ⊓ (F₁ ⊔ F₂) ≤ S := by
    intro x hx
    obtain ⟨z, hz, hzc, z', hz', hz'c, rfl⟩ := exists_center_mul_of_comm hs.comm (hFD hx.2)
      (fun u hu => Subgroup.mem_centralizer_iff.mp (hZU hx.1) u hu)
      (fun v hv => Subgroup.mem_centralizer_iff.mp (hZV hx.1) v hv)
    exact hS z hz hzc z' hz' hz'c
  have h1 : Nat.card (Z ⊓ (F₁ ⊔ F₂) : Subgroup Γ) ≤ Nat.card S := Subgroup.card_le_of_le hZF
  have h2 : Nat.card (F₁ ⊓ F₂ : Subgroup Γ) ≤ Nat.card (U ⊓ V : Subgroup Γ) :=
    Subgroup.card_le_of_le (inf_le_inf h₁ h₂)
  calc Nat.card Z * (Nat.card F₁ * Nat.card F₂)
      = Nat.card Z * (Nat.card (F₁ ⊔ F₂ : Subgroup Γ) * Nat.card (F₁ ⊓ F₂ : Subgroup Γ)) := by
        rw [hFcard]
    _ = (Nat.card Z * Nat.card (F₁ ⊔ F₂ : Subgroup Γ)) * Nat.card (F₁ ⊓ F₂ : Subgroup Γ) := by
        ring
    _ ≤ (27 * Nat.card (Z ⊓ (F₁ ⊔ F₂) : Subgroup Γ)) * Nat.card (U ⊓ V : Subgroup Γ) :=
        Nat.mul_le_mul hG h2
    _ ≤ 27 * Nat.card S * Nat.card (U ⊓ V : Subgroup Γ) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 27 h1)

private theorem rank_five_five (hs : ProdSetting U V E) (hinf : U ⊓ V = ⊥) (hU : FacA5 ↥U)
    (hV : FacA5 ↥V) :
    Nat.card ((E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ)) :
      Subgroup Γ) ≤ 3 := by
  obtain ⟨eU⟩ := hU
  obtain ⟨eV⟩ := hV
  obtain ⟨xU, hxU⟩ := exists_orderOf_three_five eU
  obtain ⟨xV, hxV⟩ := exists_orderOf_three_five eV
  obtain ⟨hFU, hFU3, hFUU⟩ := exists_zpowers_three hxU
  obtain ⟨hFV, hFV3, hFVV⟩ := exists_zpowers_three hxV
  have h := card_center_le hs hFU hFV hFUU hFVV (S := ⊥) fun z hz hzc z' hz' hz'c => by
    rw [eq_one_of_center_eq_bot (center_eq_bot_five eU) hz hzc,
      eq_one_of_center_eq_bot (center_eq_bot_five eV) hz' hz'c, mul_one]
    exact one_mem _
  rw [hFU3, hFV3, hinf, Subgroup.card_bot] at h
  omega

private theorem rank_six_five (hs : ProdSetting U V E) (hinf : U ⊓ V = ⊥) (hU : FacA6 ↥U)
    (hV : FacA5 ↥V) :
    Nat.card ((E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ)) :
      Subgroup Γ) ≤ 3 := by
  obtain ⟨hUp, hZU3, hφ⟩ := hU
  obtain ⟨eV⟩ := hV
  obtain ⟨F₀, hF₀, hF₀9⟩ := exists_elemAbelian_nine_tripleCover hUp ⟨hZU3, hφ⟩
  obtain ⟨hFU, hFU9, hFUU⟩ := exists_elemAbelian_map hF₀
  obtain ⟨xV, hxV⟩ := exists_orderOf_three_five eV
  obtain ⟨hFV, hFV3, hFVV⟩ := exists_zpowers_three hxV
  have h := card_center_le hs hFU hFV hFUU hFVV (S := Item148PtRes.centerIn U)
    fun z hz hzc z' hz' hz'c => by
      rw [eq_one_of_center_eq_bot (center_eq_bot_five eV) hz' hz'c, mul_one]
      exact mem_centerIn_of_comm hz hzc
  have hc3 : Nat.card (Item148PtRes.centerIn U) = 3 := by
    rw [Item148PtRes.centerIn, Subgroup.card_map_of_injective U.subtype_injective, hZU3]
  rw [hFU9, hF₀9, hFV3, hinf, Subgroup.card_bot, hc3] at h
  omega

private theorem rank_five_six (hs : ProdSetting U V E) (hinf : U ⊓ V = ⊥) (hU : FacA5 ↥U)
    (hV : FacA6 ↥V) :
    Nat.card ((E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ)) :
      Subgroup Γ) ≤ 3 := by
  have h := rank_six_five (prodSetting_symm hs) (by rwa [inf_comm]) hV hU
  rwa [inf_comm] at h

private theorem rank_six_six (hs : ProdSetting U V E) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hU : FacA6 ↥U) (hV : FacA6 ↥V) :
    Nat.card ((E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ)) :
      Subgroup Γ) ≤ 3 := by
  obtain ⟨hUp, hZU3, hφU⟩ := hU
  obtain ⟨hVp, hZV3, hφV⟩ := hV
  have hcV : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := fun v hv u hu => (hs.comm u hu v hv).symm
  have hUV : ⁅U, V⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_of_comm hcV)
  have hZU := Item148PtRes.inf_eq_centerIn_left hUV h3 hZU3
  have hZV := Item148PtRes.inf_eq_centerIn_right hUV h3 hZV3
  obtain ⟨F₁, hF₁, hF₁9⟩ := exists_elemAbelian_nine_tripleCover hUp ⟨hZU3, hφU⟩
  obtain ⟨F₂, hF₂, hF₂9⟩ := exists_elemAbelian_nine_tripleCover hVp ⟨hZV3, hφV⟩
  obtain ⟨hFU, hFU9, hFUU⟩ := exists_elemAbelian_map hF₁
  obtain ⟨hFV, hFV9, hFVV⟩ := exists_elemAbelian_map hF₂
  have h := card_center_le hs hFU hFV hFUU hFVV (S := U ⊓ V)
    fun z hz hzc z' hz' hz'c => by
      have h1 : z ∈ U ⊓ V := by rw [hZU]; exact mem_centerIn_of_comm hz hzc
      have h2 : z' ∈ U ⊓ V := by rw [hZV]; exact mem_centerIn_of_comm hz' hz'c
      exact (U ⊓ V).mul_mem h1 h2
  rw [hFU9, hF₁9, hFV9, hF₂9, h3] at h
  omega

end Rank

section J2

variable {Γ : Type} [Group Γ] [Finite Γ] {U V E : Subgroup Γ}

private theorem rank_five_j2 (hs : ProdSetting U V E) (hinf : U ⊓ V = ⊥) (hU : FacA5 ↥U)
    (hV : FacHJ ↥V) :
    Nat.card ((E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ)) :
      Subgroup Γ) ≤ 1 := by
  obtain ⟨eU⟩ := hU
  obtain ⟨eV⟩ := hV
  obtain ⟨xU, hxU⟩ := exists_orderOf_three_five eU
  obtain ⟨hFU, hFU3, hFUU⟩ := exists_zpowers_three hxU
  obtain ⟨F₀, hF₀, hF₀9⟩ := exists_elemAbelian_nine_j2 eV
  obtain ⟨hFV, hFV9, hFVV⟩ := exists_elemAbelian_map hF₀
  have h := card_center_le hs hFU hFV hFUU hFVV (S := ⊥) fun z hz hzc z' hz' hz'c => by
    rw [eq_one_of_center_eq_bot (center_eq_bot_five eU) hz hzc,
      eq_one_of_center_eq_bot (center_eq_bot_j2 eV) hz' hz'c, mul_one]
    exact one_mem _
  rw [hFU3, hFV9, hF₀9, hinf, Subgroup.card_bot] at h
  omega

private theorem fixV_of_j2 (hFJ : CentJ2E9) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) (eV : ↥V ≃* CFSG.Blueprint.NativeSporadic.J2)
    (hB9 : Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) = 9)
    (hB1 : ∀ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), (∀ x ∈ V, x * b = b * x) → b = 1) :
    ∀ v ∈ V, (∀ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), b * v * b⁻¹ = v) →
      ∃ k : ℕ, v ^ 3 ^ k = 1 := by
  set B := E ⊓ Subgroup.centralizer (U : Set Γ)
  have hBE : B ≤ E := inf_le_left
  have hBV : B ≤ Subgroup.normalizer (V : Set Γ) := hBE.trans hEV
  set ρ : ↥B →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hBV) with hρ
  have hρapp : ∀ (b : ↥B) (x : ↥V), ((ρ b x : ↥V) : Γ) = b * x * (b : Γ)⁻¹ := fun b x => by
    simp only [hρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine Subtype.ext (hB1 b b.2 fun x hx => ?_)
    have h1 := congrArg (fun τ : MulAut ↥V => ((τ ⟨x, hx⟩ : ↥V) : Γ)) (MonoidHom.mem_ker.mp hb)
    simp only [hρapp, MulAut.one_apply] at h1
    calc x * b = b * x * (b : Γ)⁻¹ * b := by rw [h1]
      _ = b * x := by group
  have hρ3 : ∀ b : ↥B, ρ b ^ 3 = 1 := fun b => by
    rw [← map_pow]
    have : b ^ 3 = 1 := Subtype.ext (hE.2 b (hBE b.2))
    rw [this, map_one]
  have hρcomm : ∀ b b' : ↥B, ρ b * ρ b' = ρ b' * ρ b := fun b b' => by
    rw [← map_mul, ← map_mul]
    congr 1
    have h : (b : Γ) * b' = b' * b :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨b, hBE b.2⟩ : ↥E) ⟨b', hBE b'.2⟩)
    exact Subtype.ext h
  have hinj : Function.Injective (MulAut.conj : ↥V →* MulAut ↥V) :=
    conj_injective (center_eq_bot_j2 eV)
  have hRle : ρ.range ≤ (MulAut.conj : ↥V →* MulAut ↥V).range := by
    rintro _ ⟨b, rfl⟩
    exact Sec17.j2_mem_range_conj_of_pow_eq_one ⟨eV⟩ (k := 1) (by rw [pow_one]; exact hρ3 b)
  set F := ρ.range.comap (MulAut.conj : ↥V →* MulAut ↥V)
  have hmap : F.map (MulAut.conj : ↥V →* MulAut ↥V) = ρ.range :=
    Subgroup.map_comap_eq_self hRle
  have hR9 : Nat.card ρ.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact hB9
  have hF9 : Nat.card F = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hR9]
  have hFab : CFSG.Assembly.IsElemAbelian 3 F := by
    refine ⟨⟨⟨fun a a' => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · obtain ⟨b, hb⟩ : MulAut.conj (a : ↥V) ∈ ρ.range := a.2
      obtain ⟨b', hb'⟩ : MulAut.conj (a' : ↥V) ∈ ρ.range := a'.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← hb, ← hb']
      exact hρcomm b b'
    · obtain ⟨b, hb⟩ : MulAut.conj x ∈ ρ.range := hx
      rw [map_pow, map_one, ← hb]
      exact hρ3 b
  intro v hv hfix
  obtain ⟨k, hk⟩ := hFJ ↥V ⟨eV⟩ F hFab hF9 ⟨v, hv⟩ (by
    intro f hf
    obtain ⟨b, hb⟩ : MulAut.conj f ∈ ρ.range := hf
    have h1 := congrArg (fun τ : MulAut ↥V => ((τ ⟨v, hv⟩ : ↥V) : Γ)) hb
    simp only [hρapp, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hfix b b.2] at h1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (v : Γ) * f = f * v * (f : Γ)⁻¹ * f := by rw [← h1]
      _ = f * v := by group)
  exact ⟨k, congrArg Subtype.val hk⟩

end J2

section Assembly

variable {Γ : Type} [Group Γ] [Finite Γ] {U V E : Subgroup Γ}

private structure CentFacts (U V E : Subgroup Γ) : Prop where
  normU : E ≤ Subgroup.normalizer (U : Set Γ)
  normV : E ≤ Subgroup.normalizer (V : Set Γ)
  card : Nat.card (E ⊓ Subgroup.centralizer (U : Set Γ) : Subgroup Γ) = 9
  fixV : ∀ v ∈ V, (∀ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), b * v * b⁻¹ = v) →
    ∃ k : ℕ, v ^ 3 ^ k = 1

private theorem normalizers_of_prodTypeA (hs : ProdSetting U V E)
    (ht : ProdTypeA U V) :
    E ≤ Subgroup.normalizer (U : Set Γ) ∧ E ≤ Subgroup.normalizer (V : Set Γ) := by
  have key : ∀ e ∈ E, e ∈ Subgroup.normalizer (U : Set Γ) ∧
      e ∈ Subgroup.normalizer (V : Set Γ) := by
    intro e he
    have heD := hs.norm he
    rcases ht with ⟨h3, hU, hV⟩ | ⟨hinf, ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hV⟩⟩
    · exact mem_normalizer_of_six_six hs.comm h3 hU.2 hV.2 hs.perfect heD (hs.elem.2 e he)
    · obtain ⟨eV⟩ := hV
      exact mem_normalizer_of_six_five hs.comm hU.2 hU.1 eV heD
    · obtain ⟨eU⟩ := hU
      have h := mem_normalizer_of_six_five (fun v hv u hu => (hs.comm u hu v hv).symm) hV.2 hV.1
        eU (by rw [sup_comm]; exact heD)
      exact ⟨h.2, h.1⟩
    · obtain ⟨eU⟩ := hU
      obtain ⟨eV⟩ := hV
      exact mem_normalizer_of_five_five hs.comm hinf eU eV heD (hs.elem.2 e he)
    · obtain ⟨eU⟩ := hU
      obtain ⟨eV⟩ := hV
      exact mem_normalizer_of_five_j2 hs.comm eU eV heD
  exact ⟨fun e he => (key e he).1, fun e he => (key e he).2⟩

private theorem fixV_of_typeA (hF5 : FixA5) (hF6 : FixA6Cover)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hEV : E ≤ Subgroup.normalizer (V : Set Γ))
    (hV : FacA5 ↥V ∨ FacA6 ↥V)
    (hb : ∃ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), b ∉ Subgroup.centralizer (V : Set Γ)) :
    ∀ v ∈ V, (∀ b ∈ E ⊓ Subgroup.centralizer (U : Set Γ), b * v * b⁻¹ = v) →
      ∃ k : ℕ, v ^ 3 ^ k = 1 := by
  obtain ⟨b, hbK, hbV⟩ := hb
  intro v hv hfix
  refine fix_of_typeA hF5 hF6 hV (hEV hbK.1) (hE.2 b hbK.1) hbV hv fun x hx => ?_
  rw [hfix b hbK, inv_mul_cancel, mul_one, one_mul]

private theorem centFacts_of_rank (hF5 : FixA5) (hF6 : FixA6Cover) (hs : ProdSetting U V E)
    (hNU : E ≤ Subgroup.normalizer (U : Set Γ)) (hNV : E ≤ Subgroup.normalizer (V : Set Γ))
    (hU : FacA5 ↥U ∨ FacA6 ↥U) (hV : FacA5 ↥V ∨ FacA6 ↥V)
    (hz : Nat.card ((E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓
      (E ⊓ Subgroup.centralizer (V : Set Γ)) : Subgroup Γ) ≤ 3) : CentFacts U V E := by
  have h9U := nine_le_card_inf_centralizer hs hNU hNV hU
  have h9V := nine_le_card_inf_centralizer (prodSetting_symm hs) hNV hNU hV
  obtain ⟨hcard, hne⟩ := card_eq_nine_of_counting hs.card inf_le_left inf_le_left h9U hz
    (by omega)
  refine ⟨hNU, hNV, hcard, fixV_of_typeA hF5 hF6 hs.elem hNV hV ?_⟩
  by_contra h
  push Not at h
  exact hne fun b hb => ⟨hb.1, h b hb⟩

private theorem centFacts_of_five_j2
    (hFJ : CentJ2E9)
    (hs : ProdSetting U V E) (hNU : E ≤ Subgroup.normalizer (U : Set Γ))
    (hNV : E ≤ Subgroup.normalizer (V : Set Γ)) (hinf : U ⊓ V = ⊥) (hU : FacA5 ↥U)
    (hV : FacHJ ↥V) : CentFacts U V E := by
  have hz := rank_five_j2 hs hinf hU hV
  have h9U := nine_le_card_inf_centralizer hs hNU hNV (Or.inl hU)
  obtain ⟨eV⟩ := hV
  have h3V : 3 ≤ Nat.card (E ⊓ Subgroup.centralizer (V : Set Γ) : Subgroup Γ) := by
    have h := card_le_mul_card_inf_centralizer hNV hs.elem (card_le_nine_of_mulAut_j2 eV)
    rw [hs.card] at h
    omega
  obtain ⟨hcard, -⟩ := card_eq_nine_of_counting (K := E ⊓ Subgroup.centralizer (U : Set Γ))
    (L := E ⊓ Subgroup.centralizer (V : Set Γ)) hs.card inf_le_left inf_le_left h9U
    (by omega) (by omega)
  refine ⟨hNU, hNV, hcard, fixV_of_j2 hFJ hs.elem hNV eV hcard fun b hb hbV => ?_⟩
  have hZ : ((E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ)) :
      Subgroup Γ) = ⊥ := Subgroup.eq_bot_of_card_le _ hz
  have hb' : b ∈ (E ⊓ Subgroup.centralizer (U : Set Γ)) ⊓ (E ⊓ Subgroup.centralizer (V : Set Γ)) :=
    ⟨hb, hb.1, Subgroup.mem_centralizer_iff.mpr hbV⟩
  rw [hZ] at hb'
  exact Subgroup.mem_bot.mp hb'

private theorem centFacts_of_prodTypeA
    (hF5 : FixA5)
    (hF6 : FixA6Cover) (hFJ : CentJ2E9) (hs : ProdSetting U V E) (ht : ProdTypeA U V) :
    CentFacts U V E := by
  obtain ⟨hNU, hNV⟩ := normalizers_of_prodTypeA hs ht
  rcases ht with ⟨h3, hU, hV⟩ | ⟨hinf, ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hV⟩⟩
  · exact centFacts_of_rank hF5 hF6 hs hNU hNV (Or.inr hU) (Or.inr hV)
      (rank_six_six hs h3 hU hV)
  · exact centFacts_of_rank hF5 hF6 hs hNU hNV (Or.inr hU) (Or.inl hV)
      (rank_six_five hs hinf hU hV)
  · exact centFacts_of_rank hF5 hF6 hs hNU hNV (Or.inl hU) (Or.inr hV)
      (rank_five_six hs hinf hU hV)
  · exact centFacts_of_rank hF5 hF6 hs hNU hNV (Or.inl hU) (Or.inl hV)
      (rank_five_five hs hinf hU hV)
  · exact centFacts_of_five_j2 hFJ hs hNU hNV hinf hU hV

end Assembly

theorem prodCoreA_holds :
    ProdCoreA := by
  intro hF5 hF6 hFJ Γ _ _ U V E hs ht
  have hf := centFacts_of_prodTypeA hF5 hF6 hFJ hs ht
  have hUA : FacA5 ↥U ∨ FacA6 ↥U := ht.fac_left
  have hfixU : ∀ b ∈ E, b ∉ Subgroup.centralizer (U : Set Γ) → ∀ u ∈ U,
      u⁻¹ * (b * u * b⁻¹) ∈ U ⊓ V → ∃ k : ℕ, u ^ 3 ^ k = 1 := by
    intro b hbE hbU u hu hz
    exact fix_of_typeA hF5 hF6 hUA (hf.normU hbE) (hs.elem.2 b hbE) hbU hu fun x hx =>
      hs.comm x hx _ hz.2
  refine ⟨E ⊓ Subgroup.centralizer (U : Set Γ), ⟨inf_le_left, by rw [hs.card, hf.card]⟩,
    fun Q hQ hBQ => core_left hs.comm hf.fixV hQ.1 hQ.2.2 hBQ, ?_,
    core_pcore hs.comm (fun z hz hzc => center_pow_three hUA hz hzc)
      (fun N hNU hn h3 => eq_bot_of_normal_typeA hUA hNU hn h3) hf.fixV⟩
  intro B' hB' hne Q hQ hB'Q
  obtain ⟨b, hbB', hbB⟩ : ∃ b ∈ B', b ∉ E ⊓ Subgroup.centralizer (U : Set Γ) := by
    by_contra h
    push Not at h
    refine hne (Subgroup.eq_of_le_of_card_ge h ?_)
    have h1 := hB'.2
    rw [hs.card] at h1
    rw [hf.card]
    omega
  exact core_right hs.comm hf.normU hf.normV hfixU (hB'.1 hbB') (fun hC => hbB ⟨hB'.1 hbB', hC⟩)
    hQ.1 hQ.2.2 fun q hq => Subgroup.mem_centralizer_iff.mp (hB'Q hbB') q hq

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
