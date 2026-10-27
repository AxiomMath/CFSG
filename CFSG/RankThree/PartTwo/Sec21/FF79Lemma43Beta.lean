module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Comp
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Setup

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem mem_H_of_2el {β : G} {H : Subgroup G} (hβ3 : β ^ 3 = 1) (hHβ : H ≤ Cen β)
    (hsup : Subgroup.zpowers β ⊔ H = Cen β) (hinf : Subgroup.zpowers β ⊓ H = ⊥)
    {x : G} (hx : x ∈ Cen β) (h2 : Is2El x) : x ∈ H := by
  rw [← hsup] at hx
  obtain ⟨a, ha, h, hh, rfl⟩ := s43_mem_sup_of_comm (A := Subgroup.zpowers β) (H := H)
    (fun a ha h hh => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact ((show Commute β h from s43_cen_comm (hHβ hh)).zpow_left i).eq) hx
  obtain ⟨m, hm⟩ := h2
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hc : Commute (β ^ i) h := ((show Commute β h from s43_cen_comm (hHβ hh)).zpow_left i)
  rw [hc.mul_pow] at hm
  have hmem : (β ^ i) ^ 2 ^ m ∈ Subgroup.zpowers β ⊓ H := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers β) i)
      _, ?_⟩
    have : (β ^ i) ^ 2 ^ m = (h ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm
    rw [this]; exact H.inv_mem (H.pow_mem hh _)
  rw [hinf, Subgroup.mem_bot] at hmem
  have h1 : Is2El (β ^ i) := ⟨m, hmem⟩
  have h3 : (β ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hβ3, one_zpow]
  have : β ^ i = 1 := h1.eq_one_of_pow_odd (by decide : Odd 3) h3
  rw [this, one_mul]; exact hh

theorem comm_of_split {R : Subgroup G} {c a d : G} (hcd : c * d = d * c) (hr : a * d ∈ R)
    (hrc : c * (a * d) * c⁻¹ ∈ R) : c * a * c⁻¹ * a⁻¹ ∈ R := by
  have h := R.mul_mem hrc (R.inv_mem hr)
  have e : c * (a * d) * c⁻¹ * (a * d)⁻¹ = c * a * c⁻¹ * a⁻¹ := by
    have : c * d * c⁻¹ = d := by rw [hcd]; group
    calc c * (a * d) * c⁻¹ * (a * d)⁻¹ = (c * a * c⁻¹) * (c * d * c⁻¹) * d⁻¹ * a⁻¹ := by group
      _ = (c * a * c⁻¹) * d * d⁻¹ * a⁻¹ := by rw [this]
      _ = c * a * c⁻¹ * a⁻¹ := by group
  rw [e] at h; exact h

theorem split_fix {K L : Subgroup G} (hKL : K ⊓ L = ⊥) {σ k l : G} (hσK : σ ∈ Nor K)
    (hσL : σ ∈ Nor L) (hk : k ∈ K) (hl : l ∈ L) (h : σ * (k * l) * σ⁻¹ = k * l) :
    σ * k * σ⁻¹ = k ∧ σ * l * σ⁻¹ = l := by
  have ha : σ * k * σ⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hσK k).mp hk
  have hb : σ * l * σ⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hσL l).mp hl
  have hab : (σ * k * σ⁻¹) * (σ * l * σ⁻¹) = k * l := by rw [← h]; group
  have h1 : k⁻¹ * (σ * k * σ⁻¹) = l * (σ * l * σ⁻¹)⁻¹ := by
    have : k⁻¹ * (σ * k * σ⁻¹) * (σ * l * σ⁻¹) = l := by
      calc k⁻¹ * (σ * k * σ⁻¹) * (σ * l * σ⁻¹) = k⁻¹ * ((σ * k * σ⁻¹) * (σ * l * σ⁻¹)) := by
            rw [mul_assoc]
        _ = l := by rw [hab]; group
    exact eq_mul_inv_of_mul_eq this
  have hmem : k⁻¹ * (σ * k * σ⁻¹) ∈ K ⊓ L :=
    Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem hk) ha, h1 ▸ L.mul_mem hl (L.inv_mem hb)⟩
  rw [hKL, Subgroup.mem_bot] at hmem
  have hk' : σ * k * σ⁻¹ = k := by
    have := congrArg (fun z => k * z) hmem
    simpa using this
  refine ⟨hk', ?_⟩
  rw [hk'] at hab
  exact mul_left_cancel hab

section Core

variable [Finite G]

theorem good_beta_core {β γ b σ : G} {H K L D : Subgroup G}
    (hβ3 : β ^ 3 = 1) (hHβ : H ≤ Cen β) (hsup : Subgroup.zpowers β ⊔ H = Cen β)
    (hinf : Subgroup.zpowers β ⊓ H = ⊥) (hKH : K ≤ H) (hLH : L ≤ H) (hLay : Lay H = K ⊔ L)
    (hKL : K ⊓ L = ⊥) (hKc : K ≤ CenS L) (hDH : D ≤ H)
    (hHD : ∀ h ∈ H, ∃ c ∈ D, ∃ m ∈ Lay H, h = c * m)
    (hDc : ∀ k : ℕ, 2 ^ k ∣ Nat.card D → k ≤ 1)
    (eK : K ≃* alternatingGroup (Fin 5)) (eL : L ≃* GL (Fin 3) (ZMod 2))
    (hγK : γ ∈ K) (hγ3 : orderOf γ = 3) (hbL : b ∈ L) (hb3 : orderOf b = 3)
    (hσo : orderOf σ = 2) (hσβ : σ ∈ Cen β) (hσγ : σ * γ = γ * σ) (hσb : σ * b = b * σ)
    (hσK : σ ∈ Nor K) (hσL : σ ∈ Nor L) (hA5 : FF79KO2A5) (hL3 : FF79KO2L3) :
    Good43 σ β := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ2 : σ * σ = 1 := by rw [← pow_two]; exact hσo ▸ pow_orderOf_eq_one σ
  have hσ2el : Is2El σ := ⟨1, by simpa [pow_two] using hσ2⟩
  have hσH : σ ∈ H := mem_H_of_2el hβ3 hHβ hsup hinf hσβ hσ2el
  intro Q hQ hQle hQn
  have hQH : Q ≤ H := fun q hq =>
    mem_H_of_2el hβ3 hHβ hsup hinf (hQle hq).1 (Is2El.of_mem_pGroup hQ hq)
  have hσcen : ∀ q ∈ Q, Commute σ q := fun q hq => s43_cen_comm (hQle hq).2
  let R : Subgroup G := Q ⊔ Subgroup.zpowers σ
  have hRdec : ∀ r ∈ R, ∃ q ∈ Q, ∃ i : ℤ, r = q * σ ^ i := by
    intro r hr
    obtain ⟨q, hq, h, hh, rfl⟩ := s43_mem_sup_of_comm (A := Q) (H := Subgroup.zpowers σ)
      (fun a ha h hh => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact (((hσcen a ha).zpow_left i).eq).symm) hr
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ⟨q, hq, i, rfl⟩
  have hσpow : ∀ i : ℤ, Is2El (σ ^ i) := by
    intro i
    rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast]; exact hσ2el.of_pow n
    · rw [zpow_neg, zpow_natCast]; exact (hσ2el.of_pow n).inv
  have hR2 : ∀ r ∈ R, Is2El r := by
    intro r hr
    obtain ⟨q, hq, i, rfl⟩ := hRdec r hr
    exact Is2El.mul (((hσcen q hq).zpow_left i).symm) (Is2El.of_mem_pGroup hQ hq) (hσpow i)
  have hRle : R ≤ H := sup_le hQH (Subgroup.zpowers_le.mpr hσH)
  have hRcen : ∀ r ∈ R, σ * r = r * σ := by
    intro r hr
    obtain ⟨q, hq, i, rfl⟩ := hRdec r hr
    exact ((hσcen q hq).mul_right (Commute.zpow_right (Commute.refl σ) i)).eq
  have hQR : Q ≤ R := le_sup_left
  have hσR : ∀ i : ℤ, σ ^ i ∈ R := fun i =>
    Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers σ) i)
  have hRn : ∀ c ∈ H, σ * c = c * σ → ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hc hσc r hr
    obtain ⟨q, hq, i, rfl⟩ := hRdec r hr
    have hcc : c ∈ Cen β ⊓ Cen σ := Subgroup.mem_inf.mpr ⟨hHβ hc, s43_mem_cen hσc⟩
    have h1 : c * σ ^ i * c⁻¹ = σ ^ i := by
      have : Commute c (σ ^ i) := ((show Commute σ c from hσc).symm).zpow_right i
      calc c * σ ^ i * c⁻¹ = (σ ^ i) * c * c⁻¹ := by rw [this.eq.symm]
        _ = σ ^ i := by group
    have h2 : c * (q * σ ^ i) * c⁻¹ = (c * q * c⁻¹) * (c * σ ^ i * c⁻¹) := by group
    rw [h2, h1]
    exact R.mul_mem (hQR (hQn c hcc q hq)) (hσR i)
  have hRM : ∀ r ∈ R, r ∈ Lay H → r = 1 := by
    intro r hrR hrM
    rw [hLay] at hrM
    obtain ⟨k, hk, l, hl, rfl⟩ := s43_mem_sup_of_comm (A := K) (H := L)
      (fun a ha h hh => (Subgroup.mem_centralizer_iff.mp (hKc ha) h hh).symm) hrM
    have hkl : k * l = l * k := (Subgroup.mem_centralizer_iff.mp (hKc hk) l hl).symm
    have hfix := split_fix hKL hσK hσL hk hl (by rw [hRcen _ hrR]; group)
    have hσk : σ * k = k * σ := by
      calc σ * k = (σ * k * σ⁻¹) * σ := by group
        _ = k * σ := by rw [hfix.1]
    have hσl : σ * l = l * σ := by
      calc σ * l = (σ * l * σ⁻¹) * σ := by group
        _ = l * σ := by rw [hfix.2]
    obtain ⟨m, hm⟩ := hR2 _ hrR
    rw [(show Commute k l from hkl).mul_pow] at hm
    have hmK : k ^ 2 ^ m ∈ K ⊓ L := Subgroup.mem_inf.mpr ⟨K.pow_mem hk _,
      by rw [eq_inv_of_mul_eq_one_left hm]; exact L.inv_mem (L.pow_mem hl _)⟩
    rw [hKL, Subgroup.mem_bot] at hmK
    have hk2 : Is2El k := ⟨m, hmK⟩
    have hl2 : Is2El l := ⟨m, by rw [hmK, one_mul] at hm; exact hm⟩
    have hk1 : k = 1 := by
      by_contra hk1
      refine comp_kill eK hA5 hσK hσ2 hγK hγ3 hσγ hk hk1 hk2 hσk ?_
      intro c hc hσc
      have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp (hKc hc) l hl).symm
      exact hR2 _ (comm_of_split hcl hrR (hRn c (hKH hc) hσc _ hrR))
    have hl1 : l = 1 := by
      by_contra hl1
      have hrR' : l * k ∈ R := by rw [← hkl]; exact hrR
      refine comp_kill eL hL3 hσL hσ2 hbL hb3 hσb hl hl1 hl2 hσl ?_
      intro c hc hσc
      have hck : c * k = k * c := Subgroup.mem_centralizer_iff.mp (hKc hk) c hc
      exact hR2 _ (comm_of_split hck hrR' (hRn c (hLH hc) hσc _ hrR'))
    rw [hk1, hl1, one_mul]
  have hcard : Nat.card R ∣ Nat.card D :=
    card_dvd_of_inf_trivial (fun g hg z hz => lay_conj_mem hg hz) (lay_le H) hRle hDH hHD hRM
  have hRp : IsPGroup 2 R := fun x => is2El_subtype x (hR2 x x.2)
  obtain ⟨a, ha⟩ := hRp.exists_card_eq
  have ha1 : a ≤ 1 := hDc a (ha ▸ hcard)
  have hle : Subgroup.zpowers σ ≤ R := le_sup_right
  have hcz : Nat.card (Subgroup.zpowers σ) = 2 := by rw [Nat.card_zpowers, hσo]
  have hRc : Nat.card R ≤ Nat.card (Subgroup.zpowers σ) := by
    rw [ha, hcz]
    calc 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) ha1
      _ = 2 := by norm_num
  have hReq : Subgroup.zpowers σ = R := Subgroup.eq_of_le_of_card_ge hle hRc
  exact hReq ▸ hQR

end Core

end CFSG.RankThree.PartTwo.Sec21.FF79
