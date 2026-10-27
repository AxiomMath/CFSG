module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2PGL
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

private theorem map_conj_quadY_le {P : Type*} [Group P] {G B : Subgroup P} {a y : P}
    (hyG : y ∈ G) (hya : y * a = a * y) :
    (quadY G B a).map (MulAut.conj y).toMonoidHom ≤ quadY G B a := by
  simp only [quadY, Subgroup.map_iSup]
  refine iSup_le fun x => iSup_le fun hxG => iSup_le fun hxa => ?_
  rw [Subgroup.map_map]
  have e : (MulAut.conj y).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (y * x)).toMonoidHom := by
    rw [show MulAut.conj (y * x) = MulAut.conj y * MulAut.conj x from map_mul _ y x]
    rfl
  rw [e]
  refine le_iSup_of_le (y * x) (le_iSup_of_le (G.mul_mem hyG hxG) (le_iSup_of_le ?_ le_rfl))
  calc (y * x) * a = y * (x * a) := by group
    _ = y * (a * x) := by rw [hxa]
    _ = (y * a) * x := by group
    _ = (a * y) * x := by rw [hya]
    _ = a * (y * x) := by group

private theorem conj_mem_quadY {P : Type*} [Group P] {G B : Subgroup P} {a y z : P}
    (hyG : y ∈ G) (hya : y * a = a * y) (hz : z ∈ quadY G B a) :
    y * z * y⁻¹ ∈ quadY G B a := by
  have h := map_conj_quadY_le (G := G) (B := B) (a := a) hyG hya
    (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
  simpa [MulAut.conj_apply] using h

private theorem le_quadY_self {P : Type*} [Group P] (G B : Subgroup P) (a : P) :
    B ≤ quadY G B a := by
  intro b hb
  refine Subgroup.mem_iSup_of_mem (1 : P) ?_
  refine Subgroup.mem_iSup_of_mem G.one_mem ?_
  refine Subgroup.mem_iSup_of_mem (by simp) ?_
  simpa using Subgroup.mem_map_of_mem (MulAut.conj (1 : P)).toMonoidHom hb

private theorem eight_le_two_mul_sub_outerTorusOrder {q : ℕ} (hq : Odd q) (h7 : 7 ≤ q) :
    8 ≤ 2 * q - outerTorusOrder q := by
  obtain ⟨k, rfl⟩ := hq
  unfold outerTorusOrder
  split_ifs with h <;> omega

private theorem odd_mem_quadY_of_centralizer {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {t β : PGL2 K}
    (ht : t * t = 1) (ht1 : t ≠ 1) (htJ : t ∈ pslRange K) (hβ : β * β = 1)
    (hβJ : β ∉ pslRange K) (hcomm : t * β = β * t) {G B : Subgroup (PGL2 K)}
    (htYβ : t ∈ quadY G B β) (hmemG : ∀ x : PGL2 K, x ∈ G) :
    ∀ x ∈ pslRange K, x * β = β * x → Odd (orderOf x) → x ∈ quadY G B β := by
  obtain ⟨U, w, hUc, hUcard, hβU, -, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard (by rw [pow_two]; exact hβ) hβJ
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  intro x hxJ hxβ hxodd
  by_cases hx1 : x = 1
  · subst hx1
    exact (quadY G B β).one_mem
  have hxC : x ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxβ
  have hxU : x ∈ U := by
    by_contra hxU
    obtain ⟨hxx, -⟩ := inverts_of_mem_sup_not_mem hUcomm hww hwinv hxC hxU
    exact hx1 (eq_one_of_mul_self_of_odd hxx hxodd)
  obtain ⟨k, hk⟩ :=
    exists_pow_eq_self_of_coprime (n := 2) (Nat.coprime_two_left.mpr hxodd)
  have hyU : x ^ k ∈ U := U.pow_mem hxU k
  have hy_sq : (x ^ k) * (x ^ k) = x := by
    calc (x ^ k) * (x ^ k) = x ^ (k * 2) := by rw [← pow_two, ← pow_mul]
      _ = x ^ (2 * k) := by rw [Nat.mul_comm]
      _ = (x ^ 2) ^ k := by rw [pow_mul]
      _ = x := hk
  have hyβ : (x ^ k) * β = β * (x ^ k) := hUcomm _ hyU β hβU
  have htC : t ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have htU : t ∉ U := by
    intro htU
    have hodd := odd_orderOf_of_mem_outer_torus hK hcard hβJ hUcard hβU htU htJ
    rw [orderOf_eq_prime (by rw [pow_two]; exact ht) ht1] at hodd
    exact absurd hodd (by decide)
  obtain ⟨-, htinv⟩ := inverts_of_mem_sup_not_mem hUcomm hww hwinv htC htU
  have hyt' : ∀ u ∈ U, u * t = t * u⁻¹ := by
    intro u hu
    have htu : t * u = u⁻¹ * t := by
      calc t * u = (t * u * t⁻¹) * t := by group
        _ = u⁻¹ * t := by rw [htinv u hu]
    have hu' : u = t * (u⁻¹ * t) := by
      calc u = (t * t) * u := by rw [ht, one_mul]
        _ = t * (t * u) := by group
        _ = t * (u⁻¹ * t) := by rw [htu]
    calc u * t = (t * (u⁻¹ * t)) * t := by
          conv_lhs => rw [hu']
      _ = t * u⁻¹ * (t * t) := by group
      _ = t * u⁻¹ := by rw [ht, mul_one]
  have hconj : (x ^ k) * t * (x ^ k)⁻¹ = ((x ^ k) * (x ^ k)) * t := by
    calc (x ^ k) * t * (x ^ k)⁻¹ = t * ((x ^ k) * (x ^ k))⁻¹ := by
          rw [hyt' (x ^ k) hyU]
          group
      _ = ((x ^ k) * (x ^ k)) * t :=
          (hyt' ((x ^ k) * (x ^ k)) (U.mul_mem hyU hyU)).symm
  have hxYβ : x ∈ quadY G B β := by
    have h1 : (x ^ k) * t * (x ^ k)⁻¹ ∈ quadY G B β :=
      conj_mem_quadY (G := G) (B := B) (a := β) (hmemG _) hyβ htYβ
    have hxeq : x = ((x ^ k) * t * (x ^ k)⁻¹) * t := by
      rw [hconj, hy_sq, mul_assoc, ht, mul_one]
    rw [hxeq]
    exact (quadY G B β).mul_mem h1 htYβ
  exact hxYβ

private theorem exists_mem_quadY_commuting {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {t β : PGL2 K}
    (ht : t * t = 1) (ht1 : t ≠ 1) (htJ : t ∈ pslRange K) (hβ : β * β = 1)
    (hβJ : β ∉ pslRange K) (hcomm : t * β = β * t) {G B : Subgroup (PGL2 K)}
    (hβB : β ∈ B) (hB_le_Yt : B ≤ quadY G B t) (hmemG : ∀ x : PGL2 K, x ∈ G)
    (hJ2 : (pslRange K).index = 2) (hqodd : Odd (Nat.card K)) (hq7 : 7 ≤ Nat.card K) :
    ∃ x : PGL2 K, x ∈ quadY G B t ∧ x ∈ pslRange K ∧ x * t = t * x ∧ x * x ≠ 1 := by
  obtain ⟨z, hzt, hβz, hzord⟩ :=
    exists_inverted_of_inner_outer hK hcard ht ht1 htJ hβ hβJ hcomm
  have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ
  have hβz' : β * z * β = z⁻¹ := by simpa [hβinv] using hβz
  have htinv' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hztinv : z⁻¹ * t = t * z⁻¹ := by
    have h := congrArg Inv.inv hzt
    rw [mul_inv_rev, mul_inv_rev, htinv'] at h
    exact h.symm
  let x : PGL2 K := z⁻¹ * z⁻¹
  have hxJ : x ∈ pslRange K := by
    simpa [x, pow_two] using Subgroup.sq_mem_of_index_two hJ2 z⁻¹
  have hxYt : x ∈ quadY G B t := by
    have hβYt : β ∈ quadY G B t := hB_le_Yt hβB
    have hconjβ : z * β * z⁻¹ ∈ quadY G B t :=
      conj_mem_quadY (G := G) (B := B) (a := t) (hmemG z) hzt hβYt
    have hxeq : x = β * (z * β * z⁻¹) := by
      dsimp only [x]
      calc z⁻¹ * z⁻¹ = (β * z * β) * z⁻¹ := by rw [hβz']
        _ = β * (z * β * z⁻¹) := by group
    rw [hxeq]
    exact (quadY G B t).mul_mem hβYt hconjβ
  have hxt : x * t = t * x := by
    dsimp only [x]
    calc z⁻¹ * z⁻¹ * t = z⁻¹ * (z⁻¹ * t) := by group
      _ = z⁻¹ * (t * z⁻¹) := by rw [hztinv]
      _ = z⁻¹ * t * z⁻¹ := by group
      _ = t * z⁻¹ * z⁻¹ := by rw [hztinv]
      _ = t * (z⁻¹ * z⁻¹) := by group
  have hx2 : x * x ≠ 1 := by
    intro h
    have hxx : (z⁻¹ * z⁻¹) * (z⁻¹ * z⁻¹) = 1 := by simpa [x] using h
    have h4 : (z⁻¹) ^ 4 = 1 := by
      rw [show (z⁻¹) ^ 4 = (z⁻¹ * z⁻¹) * (z⁻¹ * z⁻¹) by group]
      exact hxx
    have hz4 : z ^ 4 = 1 := by
      have h' := congrArg Inv.inv h4
      simpa using h'
    have hdvd : orderOf z ∣ 4 := orderOf_dvd_of_pow_eq_one hz4
    have hle : orderOf z ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 8 ≤ orderOf z := by
      rw [hzord]
      exact eight_le_two_mul_sub_outerTorusOrder hqodd hq7
    omega
  exact ⟨x, hxYt, hxJ, hxt, hx2⟩

theorem pslRange_le_quadY_sup {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKcard : Nat.card K = p ^ f) (hq : 7 ≤ p ^ f)
    {t β : PGL2 K} (htJ : t ∈ pslRange K) (hβJ : β ∉ pslRange K) (ht : t * t = 1)
    (ht1 : t ≠ 1) (hβ : β * β = 1) (hcomm : t * β = β * t) :
    pslRange K ≤ quadY (closure {t, β} ⊔ pslRange K) (closure {t, β}) t ⊔
      quadY (closure {t, β} ⊔ pslRange K) (closure {t, β}) β := by
  classical
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hq
    omega
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hKcard⟩
  have hcard : 3 < Nat.card K := by rw [hKcard]; omega
  have hqodd : Odd (Nat.card K) := odd_card_of_isOddPrimePower hK
  have hq7 : 7 ≤ Nat.card K := by rw [hKcard]; exact hq
  have hJ2 : (pslRange K).index = 2 := pslRange_index_eq_two hK
  have hJnorm : (pslRange K).Normal := pslRange_normal hK hcard
  let J : Subgroup (PGL2 K) := pslRange K
  let B : Subgroup (PGL2 K) := closure ({t, β} : Set (PGL2 K))
  let G : Subgroup (PGL2 K) := B ⊔ J
  let Yt : Subgroup (PGL2 K) := quadY G B t
  let Yβ : Subgroup (PGL2 K) := quadY G B β
  let H : Subgroup (PGL2 K) := (Yt ⊔ Yβ) ⊓ J
  have htB : t ∈ B := Subgroup.subset_closure (by simp)
  have hβB : β ∈ B := Subgroup.subset_closure (by simp)
  have hB_le_G : B ≤ G := le_sup_left
  have hβG : β ∈ G := hB_le_G hβB
  have hGtop : G = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hxJ : x ∈ J
    · exact Subgroup.mem_sup_right hxJ
    · have hxβJ : x * β ∈ J :=
        (Subgroup.mul_mem_iff_of_index_two hJ2).mpr (iff_of_false hxJ hβJ)
      have hxeq : x = (x * β) * β := by rw [mul_assoc, hβ, mul_one]
      rw [hxeq]
      exact G.mul_mem (Subgroup.mem_sup_right hxβJ) (Subgroup.mem_sup_left hβB)
  have hmemG : ∀ x : PGL2 K, x ∈ G := fun x => hGtop ▸ Subgroup.mem_top x
  have hB_le_Yt : B ≤ Yt := le_quadY_self G B t
  have hB_le_Yβ : B ≤ Yβ := le_quadY_self G B β
  have hHJ : H ≤ pslRange K := inf_le_right
  have htH : t ∈ H := ⟨Subgroup.mem_sup_left (hB_le_Yt htB), htJ⟩
  have hβH : ∀ x ∈ H, β * x * β⁻¹ ∈ H := by
    intro x hx
    obtain ⟨hxY, hxJ⟩ := hx
    refine ⟨?_, hJnorm.conj_mem x hxJ β⟩
    have hmap : (Yt ⊔ Yβ).map (MulAut.conj β).toMonoidHom ≤ Yt ⊔ Yβ := by
      rw [Subgroup.map_sup]
      exact sup_le_sup
        (map_conj_quadY_le (G := G) (B := B) (a := t) hβG hcomm.symm)
        (map_conj_quadY_le (G := G) (B := B) (a := β) hβG rfl)
    have hmem := hmap (Subgroup.mem_map.mpr ⟨x, hxY, rfl⟩)
    simpa [MulAut.conj_apply] using hmem
  have hP1g : ∀ x ∈ pslRange K, x * β = β * x → Odd (orderOf x) → x ∈ H := by
    intro x hxJ hxβ hxodd
    exact ⟨Subgroup.mem_sup_right
      (odd_mem_quadY_of_centralizer (G := G) (B := B) hK hcard ht ht1 htJ hβ hβJ hcomm
        (htYβ := hB_le_Yβ htB) hmemG x hxJ hxβ hxodd), hxJ⟩
  obtain ⟨x, hxYt, hxJ, hxt, hx2⟩ :=
    exists_mem_quadY_commuting (G := G) (B := B) hK hcard ht ht1 htJ hβ hβJ hcomm hβB
      hB_le_Yt hmemG hJ2 hqodd hq7
  have hxH : x ∈ H := ⟨Subgroup.mem_sup_left hxYt, hxJ⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hH : H = pslRange K :=
    eq_pslRange_of_commute (p := p) (f := f) hKcard hK hcard htJ ht ht1
      (by rw [pow_two]; exact hβ) hβJ hcomm H hHJ htH hβH hP1g hxH hxt hx2
  change pslRange K ≤ Yt ⊔ Yβ
  rw [← hH]
  exact inf_le_left

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
