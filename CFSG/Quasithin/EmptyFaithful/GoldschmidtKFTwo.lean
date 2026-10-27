module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFHyp
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Hyperplane

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem mem_of_odd_orderOf_of_mem_sup_zpowers {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {σ : G} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) (hN : σ ∈ Subgroup.normalizer (L : Set G)) {q : G}
    (hq : q ∈ L ⊔ Subgroup.zpowers σ) (hodd : Odd (orderOf q)) : q ∈ L := by
  have hsq : q * q ∈ L := by
    rcases SBd18.mem_sup_zpowers_cases hσ1 hσ2 hN hq with h | h
    · exact L.mul_mem h h
    · have hσ' : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
      have hconj : σ * (q * σ) * σ⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hN _).mp h
      have : q * q = (q * σ) * (σ * (q * σ) * σ⁻¹) := by
        rw [hσ']
        symm
        calc q * σ * (σ * (q * σ) * σ) = q * (σ * σ) * q * (σ * σ) := by group
          _ = q * q := by rw [hσ2]; group
      rw [this]
      exact L.mul_mem h hconj
  obtain ⟨k, hk⟩ := hodd
  have hpow : q ^ (orderOf q) = 1 := pow_orderOf_eq_one q
  have : q = (q * q) ^ (k + 1) := by
    calc q = q ^ (orderOf q + 1) := by rw [pow_succ, hpow, one_mul]
      _ = (q * q) ^ (k + 1) := by rw [hk, ← pow_two, ← pow_mul]; ring_nf
  rw [this]
  exact L.pow_mem hsq _

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

theorem KFHyp.oddCore_centralizer_sigma (h113 : StageLemma14113)
    (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) :
    ∃ F : Subgroup G, F ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card ↥F = 9 ∧
      F ≤ Subgroup.centralizer (V₁ : Set G) ∧
      ((CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({τ * f} : Set G))).map
        (Subgroup.centralizer ({τ * f} : Set G)).subtype) ≤ F := by
  classical
  obtain ⟨F, hFL, hFel, hF9, hFσ, hFodd, -⟩ := h.sigma_structure h113
  refine ⟨F, hFL, hFel, hF9, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (h.r.h1 hv)) x (hFL hx)).symm
  set σ : G := τ * f with hσ
  set C : Subgroup G := Subgroup.centralizer ({σ} : Set G) with hC
  set Q0 : Subgroup ↥C := CFSG.pPrimeCore 2 ↥C with hQ0
  set Q : Subgroup G := Q0.map C.subtype with hQ
  have hQC : ∀ q ∈ Q, q ∈ C := fun q hq => by
    obtain ⟨q0, -, rfl⟩ := hq
    exact q0.2
  have hQnorm : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    have hn : Q0.Normal := CFSG.pPrimeCore_normal
    exact ⟨⟨c, hc⟩ * q0 * ⟨c, hc⟩⁻¹, hn.conj_mem q0 hq0 ⟨c, hc⟩, rfl⟩
  have hQcard : Odd (Nat.card Q) := by
    have h1 : Nat.card Q = Nat.card Q0 := Subgroup.card_map_of_injective C.subtype_injective
    rw [h1]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hQodd : ∀ q ∈ Q, Odd (orderOf q) := fun q hq =>
    Odd.of_dvd_nat hQcard (Subgroup.orderOf_dvd_natCard Q hq)
  have hV1C : ∀ v ∈ V₁, v ∈ C := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.hcent v hv).symm
  have hVZ := h.r.ctx.hyp.hyp.elemAbelian
  have hV1el : IsElemAbelian 2 V₁ :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hVZ h.r.ctx.hyp.decomp.le₁
  have hV14 : 2 ^ 2 ≤ Nat.card V₁ := by
    rw [h.r.ctx.hyp.decomp.card₁]
    norm_num
  have hV1N : V₁ ≤ Subgroup.normalizer (Q : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hQnorm v (hV1C v hv) x hx
    · intro hx
      have := hQnorm v⁻¹ (C.inv_mem (hV1C v hv)) _ hx
      simpa [mul_assoc] using this
  have hcop : Nat.Coprime 2 (Nat.card Q) := Nat.coprime_two_left.mpr hQcard
  have hgen := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.generation_hyperplanes
    Nat.prime_two hV1el hV14 hV1N hcop
  have hQI : ∀ q ∈ Q, q ∈ I := by
    intro q hq
    rw [← hgen] at hq
    have hle : (⨆ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 V₁,
        Q ⊓ Subgroup.centralizer (B : Set G)) ≤ I := by
      refine iSup₂_le fun B hB => ?_
      obtain ⟨hBV, hBc⟩ := hB
      have hB2 : Nat.card B = 2 := by
        rw [h.r.ctx.hyp.decomp.card₁] at hBc
        omega
      have hBne : B ≠ ⊥ := by
        intro hb
        rw [hb, Subgroup.card_bot] at hB2
        omega
      obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
      have hbV : (b : G) ∈ V₁ := hBV b.2
      have hb1 : (b : G) ≠ 1 := fun h1 => hb (Subtype.ext h1)
      intro x hx
      refine h.hCv (b : G) hbV hb1 ?_
      have hsub : ({(b : G)} : Set G) ⊆ (B : Set G) := by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact b.2
      exact Subgroup.centralizer_le hsub hx.2
    exact hle hq
  have hQcent : ∀ q ∈ Q, ∀ v ∈ V₁, q * v = v * q := by
    intro q hq v hv
    have hqN : q ∈ Subgroup.normalizer (V₁ : Set G) := h.hI ▸ hQI q hq
    have h1 : q * v * q⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hqN v).mp hv
    have hcV : (q * v * q⁻¹) * v⁻¹ ∈ V₁ := V₁.mul_mem h1 (V₁.inv_mem hv)
    have hcQ : (q * v * q⁻¹) * v⁻¹ ∈ Q := by
      have := Q.mul_mem hq (hQnorm v (hV1C v hv) q⁻¹ (Q.inv_mem hq))
      simpa [mul_assoc] using this
    have hsq : ((q * v * q⁻¹) * v⁻¹) * ((q * v * q⁻¹) * v⁻¹) = 1 :=
      h.r.V_sq _ (h.r.ctx.hyp.decomp.le₁ hcV)
    have hord : orderOf ((q * v * q⁻¹) * v⁻¹) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have hone : (q * v * q⁻¹) * v⁻¹ = 1 := by
      have hodd := hQodd _ hcQ
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1' | h2'
      · exact orderOf_eq_one_iff.mp h1'
      · rw [h2'] at hodd
        exact absurd hodd (by decide)
    have : q * v * q⁻¹ = v := mul_inv_eq_one.mp hone
    calc q * v = (q * v * q⁻¹) * q := by group
      _ = v * q := by rw [this]
  have hQL : ∀ q ∈ Q, q ∈ L := by
    intro q hq
    have hmem : q ∈ Subgroup.centralizer (V₁ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hQcent q hq v hv).symm
    rw [h.hcl'] at hmem
    exact mem_of_odd_orderOf_of_mem_sup_zpowers h.sigma_ne_one h.sigma_sq
      (h.r.hNL h.sigma_mem_I) hmem (hQodd q hq)
  intro q hq
  refine hFodd q (hQL q hq) ?_ (hQodd q hq)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hQC q hq)).symm

end CFSG.Quasithin.SBd19F
