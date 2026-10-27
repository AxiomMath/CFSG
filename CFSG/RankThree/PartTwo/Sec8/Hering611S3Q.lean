module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3QAut
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3QUni
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3QOrd
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
import CFSG.Quasithin.Vol2.Ch12Sec8Three

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

private theorem q_conj_fix_card_four {M : Type*} [Group M] (R : Subgroup M) [Finite R]
    (hR : Nat.card R = 4) {δ : M} (hδ3 : δ ^ 3 = 1) (hδR : ∀ r ∈ R, δ * r * δ⁻¹ ∈ R)
    {z : M} (hzR : z ∈ R) (hz1 : z ≠ 1) (hzδ : δ * z * δ⁻¹ = z) :
    ∀ r ∈ R, δ * r * δ⁻¹ = r := by
  classical
  have inj : ∀ x y : M, δ * x * δ⁻¹ = δ * y * δ⁻¹ → x = y := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hfix1 : δ * (1 : M) * δ⁻¹ = 1 := by group
  have hcube : ∀ x : M, δ * (δ * (δ * x * δ⁻¹) * δ⁻¹) * δ⁻¹ = x := by
    intro x
    calc δ * (δ * (δ * x * δ⁻¹) * δ⁻¹) * δ⁻¹ = δ ^ 3 * x * (δ ^ 3)⁻¹ := by
          rw [pow_three']; group
      _ = x := by rw [hδ3]; group
  intro r hr
  by_contra hne
  obtain ⟨t, ht⟩ : ∃ t, t = δ * r * δ⁻¹ := ⟨_, rfl⟩
  have htR : t ∈ R := by rw [ht]; exact hδR r hr
  have hr1 : r ≠ 1 := fun h => hne (by rw [h]; exact hfix1)
  have ht1 : t ≠ 1 := fun h => hr1 (inj r 1 ((ht.symm.trans h).trans hfix1.symm))
  have hzr : z ≠ r := fun h => hne (by rw [← h]; exact hzδ)
  have hzt : z ≠ t := fun h => hzr (inj z r (hzδ.trans (h.trans ht)))
  have hrt : r ≠ t := fun h => hne (ht.symm.trans h.symm)
  have exh : ∀ x ∈ R, x = 1 ∨ x = z ∨ x = r ∨ x = t := by
    intro x hx
    rcases CFSG.Quasithin.eq_or_eq_or_eq_or_eq_of_card_four hR (a := (⟨1, R.one_mem⟩ : R))
        (b := ⟨z, hzR⟩)
        (c := ⟨r, hr⟩) (d := ⟨t, htR⟩)
        (fun h => hz1 (congrArg Subtype.val h).symm)
        (fun h => hr1 (congrArg Subtype.val h).symm)
        (fun h => ht1 (congrArg Subtype.val h).symm)
        (fun h => hzr (congrArg Subtype.val h))
        (fun h => hzt (congrArg Subtype.val h))
        (fun h => hrt (congrArg Subtype.val h)) ⟨x, hx⟩ with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  rcases exh _ (hδR t htR) with h | h | h | h
  · exact ht1 (inj t 1 (h.trans hfix1.symm))
  · exact hzt (inj t z (h.trans hzδ.symm)).symm
  · have key := hcube r
    rw [← ht, h] at key
    exact hne key
  · exact absurd (ht.symm.trans (inj t r (h.trans ht))) hne

private theorem q_arith_card (c e n : ℕ) (hdvd : c ∣ 8) (hc3 : c % 3 = 1) (he : e ≤ 2)
    (hn : n = e * c) (hn3 : n % 3 = 1) : n = 1 ∨ n = 4 := by
  have hc8 : c ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases c <;> interval_cases e <;> omega

private theorem q_card_fpf {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 6)
    {β : MulAut (PSL2 K)} (hβ3 : β ^ 3 = 1)
    (hβI : β ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range)
    {R : Subgroup (MulAut (PSL2 K))} (hRP : R ≤ (pglAction K).range)
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1) (hRβ : ∀ r ∈ R, β * r * β⁻¹ ∈ R)
    (hfix : ∀ r ∈ R, β * r * β⁻¹ = r → r = 1) :
    Nat.card R = 1 ∨ Nat.card R = 4 := by
  set I : Subgroup (MulAut (PSL2 K)) := (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range
  set P : Subgroup (MulAut (PSL2 K)) := (pglAction K).range
  have h2 : I.relIndex P = 2 := index_inn_pglRange hK
  have hne0 : I.relIndex P ≠ 0 := by rw [h2]; norm_num
  have hidx : I.relIndex R ≤ 2 := (Subgroup.relIndex_le_of_le_right hRP hne0).trans h2.le
  have hmul : I.relIndex R * Nat.card ↥(I ⊓ R) = Nat.card ↥R := Subgroup.relIndex_mul_card I R
  have hpg : IsPGroup 2 ↥(I ⊓ R) := by
    intro g
    obtain ⟨k, hk⟩ := hR2 g.1 (Subgroup.mem_inf.mp g.2).2
    exact ⟨k, Subtype.ext hk⟩
  have hdvd : Nat.card ↥(I ⊓ R) ∣ 8 :=
    card_two_subgroup_inn_dvd_eight hK (I ⊓ R) hpg inf_le_left
  have hβIR : ∀ r ∈ I ⊓ R, β * r * β⁻¹ ∈ I ⊓ R := by
    intro r hr
    obtain ⟨hrI, hrR⟩ := Subgroup.mem_inf.mp hr
    exact Subgroup.mem_inf.mpr ⟨I.mul_mem (I.mul_mem hβI hrI) (I.inv_mem hβI), hRβ r hrR⟩
  have hm1 : Nat.card ↥(I ⊓ R) % 3 = 1 :=
    card_mod_three_of_fpf hβ3 hβIR (fun r hr h => hfix r (Subgroup.mem_inf.mp hr).2 h)
  have hmR : Nat.card ↥R % 3 = 1 := card_mod_three_of_fpf hβ3 hRβ hfix
  exact q_arith_card _ _ _ hdvd hm1 hidx hmul.symm hmR

private theorem q_mem_normalizer {M : Type*} [Group M] {Q : Subgroup M} {δ : M}
    (hδ3 : δ ^ 3 = 1) (hδQ : ∀ q ∈ Q, δ * q * δ⁻¹ ∈ Q) :
    δ ∈ Subgroup.normalizer (Q : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hδQ h hh, fun hh => ?_⟩
  have e : δ * (δ * (δ * h * δ⁻¹) * δ⁻¹) * δ⁻¹ = h := by
    calc δ * (δ * (δ * h * δ⁻¹) * δ⁻¹) * δ⁻¹ = δ ^ 3 * h * (δ ^ 3)⁻¹ := by
          rw [pow_three']; group
      _ = h := by rw [hδ3]; group
  have h2 := hδQ _ (hδQ _ hh)
  rwa [e] at h2

theorem theoremQ {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3 ^ 6) (hK3 : ringChar K = 3)
    {u : PSL2 K} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) {δ : MulAut (PSL2 K)} (hδ3 : δ ^ 3 = 1)
    (hδβ : δ * MulAut.conj u = MulAut.conj u * δ) {Q : Subgroup (MulAut (PSL2 K))}
    (hQ2 : IsPGroup 2 Q) (hQδ : ∀ q ∈ Q, δ * q * δ⁻¹ ∈ Q)
    (hQβ : ∀ q ∈ Q, MulAut.conj u * q * (MulAut.conj u)⁻¹ ∈ Q) {s : MulAut (PSL2 K)}
    (hsQ : s ∈ Q) (hsδ : δ * s = s * δ) (hsβ : MulAut.conj u * s ≠ s * MulAut.conj u) :
    ∀ q ∈ Q, δ * q = q * δ := by
  have hβ3 : MulAut.conj u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hβI : MulAut.conj u ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range :=
    MonoidHom.mem_range.mpr ⟨u, rfl⟩
  have hQpow : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1 := fun q hq => by
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hQ1δ : ∀ r ∈ Q ⊓ (pglAction K).range, δ * r * δ⁻¹ ∈ Q ⊓ (pglAction K).range := by
    intro r hr
    obtain ⟨hrQ, hrP⟩ := Subgroup.mem_inf.mp hr
    exact Subgroup.mem_inf.mpr ⟨hQδ r hrQ, conj_mem_pglRange δ hrP⟩
  have hQ1β : ∀ r ∈ Q ⊓ (pglAction K).range,
      MulAut.conj u * r * (MulAut.conj u)⁻¹ ∈ Q ⊓ (pglAction K).range := by
    intro r hr
    obtain ⟨hrQ, hrP⟩ := Subgroup.mem_inf.mp hr
    exact Subgroup.mem_inf.mpr ⟨hQβ r hrQ, conj_mem_pglRange (MulAut.conj u) hrP⟩
  have hfix : ∀ r ∈ Q ⊓ (pglAction K).range,
      MulAut.conj u * r * (MulAut.conj u)⁻¹ = r → r = 1 := by
    intro r hr hrf
    obtain ⟨hrQ, hrP⟩ := Subgroup.mem_inf.mp hr
    have hcomm : r * MulAut.conj u = MulAut.conj u * r := by
      rw [mul_inv_eq_iff_eq_mul] at hrf
      exact hrf.symm
    obtain ⟨k, hk⟩ := hQpow r hrQ
    exact eq_one_of_commute_conj_order_three hK3 hu3 hu1 hrP hcomm hk
  have hz1 : s * MulAut.conj u * s⁻¹ * (MulAut.conj u)⁻¹ ≠ 1 := by
    intro h
    apply hsβ
    have h' : s * MulAut.conj u * s⁻¹ = MulAut.conj u := mul_inv_eq_one.mp h
    calc MulAut.conj u * s = (s * MulAut.conj u * s⁻¹) * s := by rw [h']
      _ = s * MulAut.conj u := by group
  have hzQ : s * MulAut.conj u * s⁻¹ * (MulAut.conj u)⁻¹ ∈ Q := by
    have e : s * MulAut.conj u * s⁻¹ * (MulAut.conj u)⁻¹ =
        s * (MulAut.conj u * s⁻¹ * (MulAut.conj u)⁻¹) := by group
    rw [e]
    exact Q.mul_mem hsQ (hQβ _ (Q.inv_mem hsQ))
  have hzR : s * MulAut.conj u * s⁻¹ * (MulAut.conj u)⁻¹ ∈ Q ⊓ (pglAction K).range :=
    Subgroup.mem_inf.mpr ⟨hzQ, commutator_mem_pglRange s (MulAut.conj u)⟩
  have hzδ : δ * (s * MulAut.conj u * s⁻¹ * (MulAut.conj u)⁻¹) * δ⁻¹ =
      s * MulAut.conj u * s⁻¹ * (MulAut.conj u)⁻¹ := by
    have hcs : Commute δ s := hsδ
    have hcb : Commute δ (MulAut.conj u) := hδβ
    have hc : Commute δ (s * MulAut.conj u * s⁻¹ * (MulAut.conj u)⁻¹) :=
      ((hcs.mul_right hcb).mul_right hcs.inv_right).mul_right hcb.inv_right
    rw [hc.eq, mul_inv_cancel_right]
  have hcard : Nat.card ↥(Q ⊓ (pglAction K).range) = 4 := by
    rcases q_card_fpf (R := Q ⊓ (pglAction K).range) hK hβ3 hβI inf_le_right
        (fun r hr => hQpow r (Subgroup.mem_inf.mp hr).1) hQ1β hfix with h | h
    · exfalso
      obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.mp h
      haveI := hs
      apply hz1
      exact congrArg Subtype.val
        (Subsingleton.elim (⟨_, hzR⟩ : ↥(Q ⊓ (pglAction K).range)) 1)
    · exact h
  have hfixδ : ∀ r ∈ Q ⊓ (pglAction K).range, δ * r * δ⁻¹ = r :=
    q_conj_fix_card_four _ hcard hδ3 hQ1δ hzR hz1 hzδ
  have hδN : δ ∈ Subgroup.normalizer (Q : Set (MulAut (PSL2 K))) := q_mem_normalizer hδ3 hQδ
  have hDN : Subgroup.zpowers δ ≤ Subgroup.normalizer (Q : Set (MulAut (PSL2 K))) :=
    Subgroup.zpowers_le.mpr hδN
  have hQD : ⁅Q, Subgroup.zpowers δ⁆ ≤ Q ⊓ (pglAction K).range := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, commutator_mem_pglRange g h⟩
    have e : g * h * g⁻¹ * h⁻¹ = g * (h * g⁻¹ * h⁻¹) := by group
    rw [e]
    exact Q.mul_mem hg ((Subgroup.mem_normalizer_iff.mp (hDN hh) g⁻¹).mp (Q.inv_mem hg))
  have hQDD : ⁅⁅Q, Subgroup.zpowers δ⁆, Subgroup.zpowers δ⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro x hx h hh
    have hxQP := hQD hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hxδ : δ * x = x * δ := mul_inv_eq_iff_eq_mul.mp (hfixδ x hxQP)
    have hc : Commute x (δ ^ k) := (show Commute x δ from hxδ.symm).zpow_right k
    rw [commutatorElement_def, Subgroup.mem_bot, hc.eq]
    group
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers δ)) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hQ2
    rw [Nat.card_zpowers, hn]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hδ3)
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
  have hcomm :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_coprime hDN hcop
  have hbot : ⁅Q, Subgroup.zpowers δ⁆ = ⊥ := by
    rw [hcomm] at hQDD
    exact le_bot_iff.mp hQDD
  intro q hq
  have hmem : ⁅q, δ⁆ ∈ ⁅Q, Subgroup.zpowers δ⁆ :=
    Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers δ)
  rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
  have h' : q * δ * q⁻¹ = δ := mul_inv_eq_one.mp hmem
  calc δ * q = (q * δ * q⁻¹) * q := by rw [h']
    _ = q * δ := by group

end CFSG.RankThree.PartTwo.Sec8.Hering611
