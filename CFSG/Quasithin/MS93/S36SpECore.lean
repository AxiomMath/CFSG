module

public import CFSG.Quasithin.MS93.S36SpESec
public import CFSG.Quasithin.MS93.S36SpEMod
public import CFSG.Quasithin.MS93.S36SpStmt

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36SP
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement

variable {G : Type} [Group G]

structure CoreData (M T L : Subgroup G) (k : ℕ) (ψ : MulAut ↥T) (Yp Ym Kp Km : Subgroup G) :
    Prop where
  crit' : ¬ tImage ψ (Z0q M T) ≤ pCoreOf 2 M
  index : (tImage ψ (pCoreOf 2 M)).relIndex (Z0q M T) = 2 ^ k
  Yp_ge : omegaOneCenterOf T ≤ Yp
  Yp_le : Yp ≤ tImage ψ (Z0q M T) ⊓ pCoreOf 2 M
  Yp_comm : ⁅Yp, pCoreOf 2 M⁆ ≤ Kp
  not_le : ¬ ⁅normalClosureIn M Yp, L⁆ ≤ Z0q M T
  comm_le : ∀ K : Subgroup G, K ≤ T → Z0q M T ≤ K → ⁅pCoreOf 2 M, K⁆ ≤ Z0q M T →
    (2 ^ k) ^ 3 ≤ (tImage ψ (pCoreOf 2 M)).relIndex K →
      ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ ≤ ⁅K, tImage ψ (Z0q M T)⁆
  key : 2 ≤ k → ∀ t ∈ tImage ψ (pCoreOf 2 M), ∃ l ∈ L, ActsLike M t l
  Ym_ge : omegaOneCenterOf T ≤ Ym
  Ym_le : Ym ≤ tImage ψ⁻¹ (Z0q M T) ⊓ pCoreOf 2 M
  Ym_comm : ⁅Ym, pCoreOf 2 M⁆ ≤ Km
  index_le : ∀ K : Subgroup G, K ≤ T → ⁅pCoreOf 2 M, K⁆ ≤ Z0q M T →
    (tImage ψ⁻¹ (pCoreOf 2 M)).relIndex K ≤ (2 ^ k) ^ 3
  Kp_le : Kp ≤ Z0q M T
  Kp_n : M ≤ Subgroup.normalizer (Kp : Set G)
  Kp_L : L ≤ Subgroup.centralizer (Kp : Set G)
  Kp_E : ∀ e ∈ tImage ψ (normalClosureIn M Ym), ∀ c ∈ Kp, e * c = c * e
  Km_n : M ≤ Subgroup.normalizer (Km : Set G)
  Km_Z : Km ≤ Z0q M T
  Km_le : tImage ψ Km ≤ Uq M T L
  K_inf : Kp ⊓ tImage ψ Km = ⊥
  side : (tImage ψ (pCoreOf 2 M)).relIndex (normalClosureIn M Yp) ≤
    (tImage ψ⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Ym)

section Closure

variable [Finite G] {M T L : Subgroup G}

theorem Z0q_le_center (h : PUHyp M T L) {z : G} (hz : z ∈ Z0q M T) {x : G}
    (hx : x ∈ pCoreOf 2 M) : z * x = x * z := by
  have h1 := PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M) (h.Z0q_le_Xq hz)
  exact (Subgroup.mem_centralizer_iff.1 h1.2 x hx).symm

theorem closure_facts (h : PUHyp M T L) {φ : MulAut ↥T} {Y K : Subgroup G}
    (hYge : omegaOneCenterOf T ≤ Y) (hYle : Y ≤ tImage φ (Z0q M T) ⊓ pCoreOf 2 M)
    (hYK : ⁅Y, pCoreOf 2 M⁆ ≤ K) (hKn : M ≤ Subgroup.normalizer (K : Set G)) :
    normalClosureIn M Y ≤ pCoreOf 2 M ∧ Z0q M T ≤ normalClosureIn M Y ∧
      ⁅normalClosureIn M Y, pCoreOf 2 M⁆ ≤ K ∧ ∀ r ∈ normalClosureIn M Y, r ^ 2 ∈ K := by
  have hYQ : Y ≤ pCoreOf 2 M := hYle.trans inf_le_right
  have hQM := pCoreOf_le' M
  have hYM : Y ≤ M := hYQ.trans hQM
  have hRQ : normalClosureIn M Y ≤ pCoreOf 2 M :=
    normalClosureIn_le_of_le hQM (le_normalizer_pCoreOf M) hYQ
  have hZR : Z0q M T ≤ normalClosureIn M Y :=
    normalClosureIn_le_of_le (normalClosureIn_le M Y) (le_normalizer_normalClosureIn M Y)
      (hYge.trans (le_normalClosureIn hYM))
  have hRK : ⁅normalClosureIn M Y, pCoreOf 2 M⁆ ≤ K :=
    commutator_normalClosureIn_le hYM (le_normalizer_pCoreOf M) hKn hYK
  refine ⟨hRQ, hZR, hRK, sq_mem_normalClosureIn hYM hKn (fun y hy => ?_)
    ((Subgroup.commutator_mono le_rfl hRQ).trans hRK)⟩
  obtain ⟨t, ht, rfl⟩ := mem_tImage.1 (hYle hy).1
  have h2 : t ^ 2 = 1 := Subtype.ext (h.isElemAbelian_Z0q.2 _ ht)
  rw [← Subgroup.coe_pow, ← map_pow, h2, map_one]
  rfl

omit [Finite G] in
theorem sq_mem_tImage {T : Subgroup G} (ψ : MulAut ↥T) {R K : Subgroup G}
    (hR : ∀ r ∈ R, r ^ 2 ∈ K) : ∀ e ∈ tImage ψ R, e ^ 2 ∈ tImage ψ K := by
  intro e he
  obtain ⟨t, ht, rfl⟩ := mem_tImage.1 he
  have h1 : ((t ^ 2 : ↥T) : G) ∈ K := by
    rw [Subgroup.coe_pow]
    exact hR _ ht
  have := apply_mem_tImage ψ h1
  rwa [map_pow, Subgroup.coe_pow] at this

omit [Finite G] in
theorem commute_comm_of_sq {M T R E K K' : Subgroup G} (hRn : M ≤ Subgroup.normalizer (R : Set G))
    (hEn : T ≤ Subgroup.normalizer (E : Set G)) (hEM : E ≤ M) (hRT : R ≤ T)
    (hRsq : ∀ r ∈ R, r ^ 2 ∈ K) (hEsq : ∀ e ∈ E, e ^ 2 ∈ K') (hKK : K ⊓ K' = ⊥)
    (hEK : ∀ e ∈ E, ∀ c ∈ K, e * c = c * e) {r e : G} (hr : r ∈ R) (he : e ∈ E) :
    (e * r * e⁻¹ * r⁻¹) ^ 2 = 1 ∧ r * (e * r * e⁻¹ * r⁻¹) = (e * r * e⁻¹ * r⁻¹) * r := by
  set d := e * r * e⁻¹ * r⁻¹ with hd
  have hdR : d ∈ R := R.mul_mem (conj_mem hRn (hEM he) hr) (R.inv_mem hr)
  have hdE : d ∈ E := by
    have e1 : d = e * (r * e⁻¹ * r⁻¹) := by rw [hd]; group
    rw [e1]
    exact E.mul_mem he (conj_mem hEn (hRT hr) (E.inv_mem he))
  have hd2 : d ^ 2 = 1 := by
    have h1 : d ^ 2 ∈ K ⊓ K' := ⟨hRsq d hdR, hEsq d hdE⟩
    rw [hKK] at h1
    exact h1
  refine ⟨hd2, ?_⟩
  have h2 : (e * r * e⁻¹) ^ 2 = r ^ 2 := by
    have e1 : (e * r * e⁻¹) ^ 2 = e * r ^ 2 * e⁻¹ := by rw [pow_two, pow_two]; group
    rw [e1, hEK e he _ (hRsq r hr), mul_inv_cancel_right]
  have h3 : e * r * e⁻¹ = d * r := by rw [hd]; group
  rw [h3, pow_two, pow_two] at h2
  have h4 : d * r * d = r := by
    have := mul_right_cancel (a := d * r * d) (b := r) (c := r) (by rw [← h2]; group)
    exact this
  have hdinv : d⁻¹ = d := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hd2]
  calc r * d = d * r * d * d := by rw [h4]
    _ = d * r * (d * d) := by group
    _ = d * r := by rw [← pow_two, hd2, mul_one]

end Closure

section Count

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem relIndex_mul_le [Finite G] {H C' R0 Z : Subgroup G} (hHR : H ⊓ R0 ≤ C') (hC : C' ≤ R0)
    (hZC : Z ≤ C') : H.relIndex Z * C'.relIndex R0 ≤ H.relIndex R0 := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex H C' R0
  rw [inf_eq_left.2 hC] at h1
  have h2 : H ⊓ C' = H ⊓ R0 := le_antisymm (inf_le_inf_left _ hC) (le_inf inf_le_left hHR)
  rw [h2, Subgroup.inf_relIndex_right] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _
    (Subgroup.relIndex_le_of_le_right hZC (relIndex_ne_zero_of_finite _ _))

theorem commute_of_mem_fix {R0 L Z K : Subgroup G} (hR0 : ⁅R0, L⁆ ⊔ Z = R0)
    (hRR : ∀ a ∈ R0, ∀ b ∈ R0, ⁅a, b⁆ ∈ K) (hKZ : K ≤ Z)
    (hKL : L ≤ Subgroup.centralizer (K : Set G))
    (hZc : ∀ z ∈ Z, ∀ r ∈ R0, z * r = r * z) (hZcomm : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hLR : L ≤ Subgroup.normalizer (R0 : Set G)) {d : G} (hd : d ∈ R0)
    (hdL : ∀ l ∈ L, l * d * l⁻¹ * d⁻¹ ∈ Z) : ∀ r ∈ R0, r * d = d * r := by
  set c : G → G := fun r => r * d * r⁻¹ * d⁻¹ with hc
  have hcK : ∀ r ∈ R0, c r ∈ K := fun r hr => hRR r hr d hd
  have hcZ : ∀ r ∈ R0, c r ∈ Z := fun r hr => hKZ (hcK r hr)
  have hcmul : ∀ x ∈ R0, ∀ y ∈ R0, c (x * y) = c x * c y := by
    intro x hx y hy
    have e1 : c (x * y) = (x * c y * x⁻¹) * c x := by simp only [hc]; group
    rw [e1]
    have h1 : x * c y * x⁻¹ = c y := by
      rw [← hZc _ (hcZ y hy) x hx, mul_inv_cancel_right]
    rw [h1, hZcomm _ (hcZ y hy) _ (hcZ x hx)]
  have hcinv : ∀ x ∈ R0, c x⁻¹ = (c x)⁻¹ := by
    intro x hx
    have h1 := hcmul x hx x⁻¹ (R0.inv_mem hx)
    rw [mul_inv_cancel] at h1
    have h0 : c 1 = 1 := by simp [hc]
    rw [h0] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  have hcconj : ∀ x ∈ R0, ∀ l ∈ L, c (l * x * l⁻¹) = c x := by
    intro x hx l hl
    set z := l * d * l⁻¹ * d⁻¹ with hz
    have hzZ : z ∈ Z := hdL l hl
    have hx' : l * x * l⁻¹ ∈ R0 := conj_mem hLR hl hx
    have h1 : l * c x * l⁻¹ = c x := by
      have := Subgroup.mem_centralizer_iff.1 (hKL hl) _ (hcK x hx)
      rw [← this, mul_inv_cancel_right]
    have h2 : l * c x * l⁻¹ = z * c (l * x * l⁻¹) * z⁻¹ := by
      simp only [hc, hz]
      have e2 : l * d * l⁻¹ = z * d := by rw [hz]; group
      have hzr : z * (l * x * l⁻¹) = (l * x * l⁻¹) * z := hZc z hzZ _ hx'
      calc l * (x * d * x⁻¹ * d⁻¹) * l⁻¹ =
            (l * x * l⁻¹) * (l * d * l⁻¹) * (l * x * l⁻¹)⁻¹ * (l * d * l⁻¹)⁻¹ := by group
        _ = (l * x * l⁻¹) * (z * d) * (l * x * l⁻¹)⁻¹ * (z * d)⁻¹ := by rw [e2]
        _ = z * ((l * x * l⁻¹) * d * (l * x * l⁻¹)⁻¹ * d⁻¹) * z⁻¹ := by
          have hzr' : (l * x * l⁻¹)⁻¹ * z = z * (l * x * l⁻¹)⁻¹ := by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hzr, mul_assoc, mul_inv_cancel, mul_one]
          calc (l * x * l⁻¹) * (z * d) * (l * x * l⁻¹)⁻¹ * (z * d)⁻¹
              = ((l * x * l⁻¹) * z) * d * (l * x * l⁻¹)⁻¹ * d⁻¹ * z⁻¹ := by group
            _ = (z * (l * x * l⁻¹)) * d * (l * x * l⁻¹)⁻¹ * d⁻¹ * z⁻¹ := by rw [hzr]
            _ = _ := by group
    rw [h1, hZcomm z hzZ _ (hcZ _ hx'), mul_inv_cancel_right] at h2
    exact h2.symm
  have hle : R0 ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [← hR0]
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro r hr l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcr : c ⁅r, l⁆ = 1 := by
        have e1 : ⁅r, l⁆ = r * (l * r * l⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e1, hcmul r hr _ (R0.inv_mem (conj_mem hLR hl hr)), hcinv _ (conj_mem hLR hl hr),
          hcconj r hr l hl, mul_inv_cancel]
      have := hcr
      simp only [hc] at this
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this
    · intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hZc z hz d hd
  intro r hr
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hr)

end Count

section Core

variable [Finite G] {M T L : Subgroup G}

theorem core_false
    (h14 : MS14AS) (hSQ : SQTKQuot) (h : PUHyp M T L) {k : ℕ} (hk : 1 ≤ k)
    (hcom : EndCommon M T L k) {ψ : MulAut ↥T} {Yp Ym Kp Km : Subgroup G}
    (hd : CoreData M T L k ψ Yp Ym Kp Km) : False := by
  set Q := pCoreOf 2 M with hQ
  set Z := Z0q M T with hZ
  set U := Uq M T L with hU
  set R := normalClosureIn M Yp with hR
  set Rm := normalClosureIn M Ym with hRm
  set E := tImage ψ Rm with hE
  set q := 2 ^ k with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hQM : Q ≤ M := pCoreOf_le' M
  have hTM : T ≤ M := h.le
  have hQT : Q ≤ T := h.pCore_le
  have hZn : M ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_Z0q M T
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf M
  have hLM : L ≤ M := h.L_le
  have hLn : M ≤ Subgroup.normalizer (L : Set G) := h.le_normalizer
  have hUZ : U ≤ Z := Uq_le_Z0q hLM
  have hZQ : Z ≤ Q := h.Z0q_le_pCoreOf
  have hZM : Z ≤ M := hZQ.trans hQM
  have hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z := fun z hz x hx => Z0q_le_center h hz hx
  have hZcomm : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' => hZc z hz z' (hZQ hz')
  obtain ⟨hRQ, hZR, hRK, hRsq⟩ := closure_facts h hd.Yp_ge hd.Yp_le hd.Yp_comm hd.Kp_n
  obtain ⟨hRmQ, hZRm, hRmK, hRmsq⟩ := closure_facts h hd.Ym_ge hd.Ym_le hd.Ym_comm hd.Km_n
  have hRn : M ≤ Subgroup.normalizer (R : Set G) := le_normalizer_normalClosureIn M Yp
  have hRmn : M ≤ Subgroup.normalizer (Rm : Set G) := le_normalizer_normalClosureIn M Ym
  have hRT : R ≤ T := hRQ.trans hQT
  have hRmT : Rm ≤ T := hRmQ.trans hQT
  have hRM : R ≤ M := hRQ.trans hQM
  have hET : E ≤ T := tImage_le ψ Rm
  have hEM : E ≤ M := hET.trans hTM
  have hEn : T ≤ Subgroup.normalizer (E : Set G) := le_normalizer_tImage ψ (hTM.trans hRmn)
  have hEQψ : E ≤ tImage ψ Q := tImage_mono ψ hRmQ
  have hEcomm : ⁅tImage ψ Q, E⁆ ≤ tImage ψ Km := by
    rw [hE, ← tImage_commutator ψ hQT hRmT]
    exact tImage_mono ψ (by rw [Subgroup.commutator_comm]; exact hRmK)
  have hEsq : ∀ e ∈ E, e ^ 2 ∈ tImage ψ Km := sq_mem_tImage ψ hRmsq
  have hKmQ : tImage ψ Km ≤ Q := hd.Km_le.trans (h.Uq_le_Xq.trans (Xq_le_pCoreOf M))
  have hKmZ : tImage ψ Km ≤ Z := hd.Km_le.trans hUZ
  have hdr : ∀ r ∈ R, ∀ e ∈ E, r * (e * r * e⁻¹ * r⁻¹) = (e * r * e⁻¹ * r⁻¹) * r :=
    fun r hr e he => (commute_comm_of_sq hRn hEn hEM hRT hRsq hEsq hd.K_inf hd.Kp_E hr he).2
  set R0 := ⁅R, L⁆ ⊔ Z with hR0
  have hRL : ⁅R, L⁆ = ⁅⁅R, L⁆, L⁆ :=
    commutator_eq_commutator_commutator hRM hLM hRn hLn h.perfect
  have hRLR : ⁅R, L⁆ ≤ R := commutator_le_left_of_le_normalizer (hLM.trans hRn)
  have hR0R : R0 ≤ R := sup_le hRLR hZR
  have hR0Q : R0 ≤ Q := hR0R.trans hRQ
  have hR0M : R0 ≤ M := hR0Q.trans hQM
  have hR0n : M ≤ Subgroup.normalizer (R0 : Set G) :=
    le_normalizer_sup (le_normalizer_commutator hRn hLn) hZn
  have hZR0 : Z ≤ R0 := le_sup_right
  have hR0L : ⁅R0, L⁆ ⊔ Z = R0 := by
    refine le_antisymm (sup_le (commutator_le_left_of_le_normalizer (hLM.trans hR0n)) hZR0) ?_
    refine sup_le ?_ le_sup_right
    rw [hRL]
    exact le_sup_of_le_left (Subgroup.commutator_mono le_sup_left le_rfl)
  have hR0Lnot : ¬ ⁅R0, L⁆ ≤ Z := by
    intro hle
    apply hd.not_le
    rw [hRL]
    exact (Subgroup.commutator_mono le_sup_left le_rfl).trans hle
  have hRR0 : ∀ a ∈ R0, ∀ b ∈ R0, ⁅a, b⁆ ∈ Kp := fun a ha b hb =>
    hRK (Subgroup.commutator_mem_commutator (hR0R ha) (hR0Q hb))
  have hZR0ne : Z ≠ R0 := by
    intro he
    apply hR0Lnot
    rw [← he]
    exact Uq_le_Z0q hLM
  set 𝒮 : Set (Subgroup G) :=
    {N | Z ≤ N ∧ N ≤ R0 ∧ N ≠ R0 ∧ M ≤ Subgroup.normalizer (N : Set G)} with h𝒮
  obtain ⟨N, ⟨hZN, hNR0, hNne, hNn⟩, hNmax⟩ :=
    (Set.toFinite 𝒮).exists_maximal ⟨Z, le_rfl, hZR0, hZR0ne, hZn⟩
  have hmax : ∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → N ≤ J → J ≤ R0 →
      J = N ∨ J = R0 := by
    intro J hJn hNJ hJR
    by_cases hJ : J = R0
    · exact Or.inr hJ
    · exact Or.inl (le_antisymm (hNmax ⟨hZN.trans hNJ, hJR, hJ, hJn⟩ hNJ) hNJ)
  have hR0N : R0 ≤ Subgroup.normalizer (N : Set G) := hR0M.trans hNn
  have hKpN : Kp ≤ N := hd.Kp_le.trans hZN
  obtain ⟨S, _, p, ρ, hs⟩ := exists_secMod hNR0 hR0n hNn fun a ha b hb => hKpN (hRR0 a ha b hb)
  have : Finite S := Finite.of_surjective p hs.surj
  have hsq : ∀ a ∈ R0, a ^ 2 ∈ N := fun a ha => hKpN (hRsq a (hR0R ha))
  have hQtriv : ∀ x ∈ Q, ∀ a ∈ R0, x * a * x⁻¹ * a⁻¹ ∈ N := by
    intro x hx a ha
    refine hKpN (hRK ?_)
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hx (hR0R ha)
  have hR0LN : ¬ ⁅R0, L⁆ ≤ N := fun hle => hNne (le_antisymm hNR0 (hR0L ▸ sup_le hle hZN))
  have hLnt : ∃ l ∈ L, ∃ a ∈ R0, l * a * l⁻¹ * a⁻¹ ∉ N := by
    by_contra hcon
    push Not at hcon
    exact hR0LN (commutator_le_of_centralizes hR0N hcon)
  have hρ : S38E.IsIrrRep L ρ := hs.isIrrRep hNR0 hLM hsq hQtriv hmax hLnt
  set D : Subgroup G := ρ.ker.map M.subtype with hD
  have hmemD : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ D := by
    intro m
    constructor
    · intro h1
      exact ⟨m, h1, rfl⟩
    · rintro ⟨m', hm', he⟩
      have : m' = m := Subtype.ext he
      rw [← this]
      exact hm'
  have hDE : D ⊓ E = Q ⊓ E := by
    apply le_antisymm
    · refine le_inf ?_ inf_le_right
      refine le_pCoreOf_of_commutator_le h hR0n hNn hR0LN (inf_le_right.trans hET) ?_
      refine commutator_le_of_centralizes hR0N fun y hy a ha => ?_
      have hyM : y ∈ M := hEM hy.2
      have h1 := (hmemD ⟨y, hyM⟩).2 hy.1
      exact (hs.rho_eq_one_iff ⟨y, hyM⟩).1 h1 a ha
    · refine le_inf (fun x hx => ?_) inf_le_right
      have hxM : x ∈ M := hQM hx.1
      exact (hmemD ⟨x, hxM⟩).1 ((hs.rho_eq_one_iff ⟨x, hxM⟩).2 fun a ha => hQtriv x hx.1 a ha)
  set Eb : Subgroup (MulAut S) := (E.subgroupOf M).map ρ with hEb
  have hcardEb : Nat.card Eb = (tImage ψ⁻¹ Q).relIndex Rm := by
    rw [hEb, SecData.card_map hEM hmemD, ← Subgroup.inf_relIndex_right, hDE,
      Subgroup.inf_relIndex_right]
    have := relIndex_tImage ψ (K := tImage ψ⁻¹ Q) hRmT
    rw [tImage_tImage_inv ψ hQT] at this
    exact this
  have hEb3 : Nat.card Eb ≤ q ^ 3 := by
    rw [hcardEb]
    refine hd.index_le Rm hRmT ?_
    rw [Subgroup.commutator_comm]
    exact hRmK.trans hd.Km_Z
  have hρQ : ∀ x : ↥M, (x : G) ∈ Q → ρ x = 1 := fun x hx =>
    (hs.rho_eq_one_iff x).2 fun a ha => hQtriv x hx a ha
  have hEbab : IsElemAbelian2 Eb := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      replace hx : (x : G) ∈ E := hx
      replace hy : (y : G) ∈ E := hy
      have hc : ⁅(x : G), (y : G)⁆ ∈ Q :=
        hKmQ (hEcomm (Subgroup.commutator_mem_commutator (hEQψ hx) hy))
      have h1 : ρ ⁅x, y⁆ = 1 := hρQ _ hc
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      rw [← map_mul, ← map_mul]
      rw [← map_mul, ← map_mul] at h1
      exact h1
    · rintro _ ⟨x, hx, rfl⟩
      replace hx : (x : G) ∈ E := hx
      rw [← map_pow]
      refine hρQ _ ?_
      rw [Subgroup.coe_pow]
      exact hKmQ (hEsq _ hx)
  set C' := fixSec R0 N E hR0N with hC'
  have hC'R0 : C' ≤ R0 := fixSec_le hR0N
  have hψQC' : tImage ψ Q ⊓ R0 ≤ C' := by
    rintro a ⟨haψ, haR⟩
    refine ⟨haR, fun e he => hZN (hKmZ ?_)⟩
    have : e * a * e⁻¹ * a⁻¹ = ⁅a, e⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.inv_mem _ (hEcomm (Subgroup.commutator_mem_commutator haψ he))
  have hZC' : Z ≤ C' := by
    intro z hz
    refine ⟨hZR0 hz, fun e he => hZN ?_⟩
    exact Z.mul_mem (conj_mem hZn (hEM he) hz) (Z.inv_mem hz)
  have hcount0 : q * C'.relIndex R0 ≤ (tImage ψ Q).relIndex R0 := by
    have := relIndex_mul_le hψQC' hC'R0 hZC'
    rwa [hd.index] at this
  have hR0R' : (tImage ψ Q).relIndex R0 ≤ (tImage ψ Q).relIndex R :=
    Subgroup.relIndex_le_of_le_right hR0R (relIndex_ne_zero_of_finite _ _)
  have hcountE : q * C'.relIndex R0 ≤ Nat.card Eb := by
    rw [hcardEb]
    exact hcount0.trans (hR0R'.trans hd.side)
  have hindex : (fixV Eb).index = C'.relIndex R0 := hs.index_fixV hEM hR0N
  have hcardS : Nat.card S = (fixV Eb).index * Nat.card (fixV Eb) := by
    rw [mul_comm, Subgroup.card_mul_index]
  have hcount : q * Nat.card S ≤ Nat.card Eb * Nat.card (fixV Eb) := by
    rw [hcardS, hindex, ← mul_assoc]
    exact Nat.mul_le_mul_right _ hcountE
  have htype : (k = 1 ∧ Nat.card (↥(S38E.IsIrrRep.imL L ρ) ⧸
        Subgroup.center ↥(S38E.IsIrrRep.imL L ρ)) = 360) ∨
      (2 ≤ k ∧ Nat.card (↥(S38E.IsIrrRep.imL L ρ) ⧸
        Subgroup.center ↥(S38E.IsIrrRep.imL L ρ)) = CFSG.Open.ordBC 2 (2 ^ k)) := by
    rw [card_quot_center_imL hρ h]
    exact card_lstar_of_isSp4DerSec h hcom.sp4
  have hkey : 2 ≤ k → Eb ≤ S38E.IsIrrRep.imL L ρ := by
    intro hk2
    rintro _ ⟨x, hx, rfl⟩
    replace hx : (x : G) ∈ E := hx
    obtain ⟨l, hl, hact⟩ := hd.key hk2 _ (hEQψ hx)
    have h1 := hact R0 N hR0n hNn hNR0 hR0Q
      ((Subgroup.commutator_mono hR0R le_rfl).trans (hRK.trans hKpN))
    refine ⟨⟨l, hLM hl⟩, Subgroup.mem_subgroupOf.2 hl, ?_⟩
    refine MulEquiv.ext fun s => ?_
    obtain ⟨a, rfl⟩ := hs.surj s
    rw [hs.conj _ a (conj_mem hR0n (hLM hl) a.2), hs.conj _ a (conj_mem hR0n x.2 a.2),
      hs.eq_iff]
    have h2 := h1 a a.2
    show ((l : G) * (a : G) * (l : G)⁻¹) * ((x : G) * (a : G) * (x : G)⁻¹)⁻¹ ∈ N
    have e1 : ((l : G) * (a : G) * (l : G)⁻¹) * ((x : G) * (a : G) * (x : G)⁻¹)⁻¹ =
        ((x : G) * (a : G) * (x : G)⁻¹ * ((l : G) * (a : G) * (l : G)⁻¹)⁻¹)⁻¹ := by group
    rw [e1]
    exact N.inv_mem h2
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hEb1 : Eb ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul] at hcount
    have := Subgroup.card_le_card_group (fixV (⊥ : Subgroup (MulAut S)))
    have h2 : 2 * Nat.card S ≤ q * Nat.card S := Nat.mul_le_mul_right _ hq2
    omega
  have hFF : IsFFModule ρ.range :=
    ⟨Eb, Subgroup.map_le_range _ _, hEb1, hEbab,
      (Nat.le_mul_of_pos_left _ (by omega)).trans hcount⟩
  obtain ⟨hS2, hEbcard, c, hc1, H, hHtop, hH⟩ := modLemma h14 hρ.sq (hρ.ffHyp h hSQ hFF)
    (Subgroup.map_le_range _ _) hEbab hk hcount hEb3 htype hkey
  have hfixpos : 0 < Nat.card (fixV Eb) := Nat.card_pos
  have hC'q : C'.relIndex R0 = q ^ 2 := by
    rw [← hindex]
    have h1 := hcardS.symm.trans hS2
    exact Nat.eq_of_mul_eq_mul_right hfixpos h1
  have hRq3 : q ^ 3 ≤ (tImage ψ Q).relIndex R := by
    have h1 := hcount0.trans hR0R'
    rw [hC'q] at h1
    calc q ^ 3 = q * q ^ 2 := by ring
      _ ≤ _ := h1
  have hR0Z : R0 ≤ Subgroup.normalizer (Z : Set G) := hR0M.trans hZn
  set C₀ := fixSec R0 Z E hR0Z with hC₀
  have hC₀C' : C₀ ≤ C' := fun a ha => ⟨ha.1, fun e he => hZN (ha.2 e he)⟩
  have hψQC₀ : tImage ψ Q ⊓ R0 ≤ C₀ := by
    rintro a ⟨haψ, haR⟩
    refine ⟨haR, fun e he => hKmZ ?_⟩
    have : e * a * e⁻¹ * a⁻¹ = ⁅a, e⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.inv_mem _ (hEcomm (Subgroup.commutator_mem_commutator haψ he))
  have hZC₀ : Z ≤ C₀ := fun z hz =>
    ⟨hZR0 hz, fun e he => Z.mul_mem (conj_mem hZn (hEM he) hz) (Z.inv_mem hz)⟩
  have hcount₀ : q * C₀.relIndex R0 ≤ q ^ 3 := by
    have := relIndex_mul_le hψQC₀ (hC₀C'.trans hC'R0) hZC₀
    rw [hd.index] at this
    calc q * C₀.relIndex R0 ≤ (tImage ψ Q).relIndex R0 := this
      _ ≤ Nat.card Eb := by rw [hcardEb]; exact hR0R'.trans hd.side
      _ = q ^ 3 := hEbcard
  have hC'C₀ : C' ≤ C₀ := by
    have h1 := Subgroup.relIndex_mul_relIndex C₀ C' R0 hC₀C' hC'R0
    rw [hC'q] at h1
    rw [← h1] at hcount₀
    have hq0 : 0 < q := by omega
    have h2 : C₀.relIndex C' ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have : q * (2 * q ^ 2) ≤ q * (C₀.relIndex C' * q ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlt)
      have h3 : q ^ 3 < q * (2 * q ^ 2) := by
        have : 0 < q ^ 3 := by positivity
        nlinarith
      omega
    have h3 : C₀.relIndex C' = 1 :=
      le_antisymm h2 (Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite _ _))
    exact Subgroup.relIndex_eq_one.1 h3
  have hNC' : N ≤ C' := fun n hn =>
    ⟨hNR0 hn, fun e he => N.mul_mem (conj_mem hNn (hEM he) hn) (N.inv_mem hn)⟩
  have hNE : ⁅N, E⁆ ≤ Z :=
    commutator_le_of_centralizes ((hNR0.trans hR0M).trans hZn) fun e he n hn =>
      (hC'C₀ (hNC' hn)).2 e he
  have hEQ : ¬ E ≤ Q := by
    intro hle
    apply hEb1
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.2 (hρQ x (hle hx))
  have hNL : ⁅N, L⁆ ≤ Z := comm_le_of_comm_le h hET hEQ hNn hZn hNE
  have hLR0 : L ≤ Subgroup.normalizer (R0 : Set G) := hLM.trans hR0n
  have hZcR0 : ∀ z ∈ Z, ∀ r ∈ R0, z * r = r * z := fun z hz r hr => hZc z hz r (hR0Q hr)
  have hNcomm : ∀ n ∈ N, ∀ r ∈ R0, r * n = n * r := by
    intro n hn
    refine commute_of_mem_fix hR0L hRR0 hd.Kp_le hd.Kp_L hZcR0 hZcomm hLR0 (hNR0 hn)
      fun l hl => ?_
    have h1 := hNL (Subgroup.commutator_mem_commutator hn hl)
    have e1 : l * n * l⁻¹ * n⁻¹ = ⁅n, l⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact Z.inv_mem h1
  set Rad := R0 ⊓ Subgroup.centralizer (R0 : Set G) with hRad
  have hRadn : M ≤ Subgroup.normalizer (Rad : Set G) :=
    le_normalizer_inf hR0n (le_normalizer_centralizer hR0n)
  have hNRad : N ≤ Rad := fun n hn =>
    ⟨hNR0 hn, Subgroup.mem_centralizer_iff.2 fun r hr => hNcomm n hn r hr⟩
  obtain ⟨c', rfl⟩ := hs.surj c
  have hc'N : (c' : G) ∉ N := fun hc => hc1 ((hs.ker c').2 hc)
  have hc'comm : ∀ r : ↥R0, p r ∉ H → (r : G) * c' = c' * r := by
    intro r hr
    obtain ⟨_, ⟨x, hx, rfl⟩, hxe⟩ := hH (p r) hr
    replace hx : (x : G) ∈ E := hx
    rw [hs.conj x r (conj_mem hR0n x.2 r.2), ← map_mul, hs.eq_iff] at hxe
    set n₀ := (x : G) * r * (x : G)⁻¹ * ((r : G) * c')⁻¹ with hn₀
    have hn₀N : n₀ ∈ N := by
      have : ((⟨(x : G) * r * (x : G)⁻¹, conj_mem hR0n x.2 r.2⟩ : ↥R0) : G) *
        ((r * c' : ↥R0) : G)⁻¹ = n₀ := by simp [hn₀]
      rw [← this]
      exact hxe
    have h1 := hdr r (hR0R r.2) x hx
    have e1 : (x : G) * r * (x : G)⁻¹ * (r : G)⁻¹ = n₀ * ((r : G) * c' * (r : G)⁻¹) := by
      rw [hn₀]
      group
    rw [e1] at h1
    have h2 : (r : G) * n₀ = n₀ * r := hNcomm n₀ hn₀N r r.2
    have h3 : (r : G) * ((r : G) * c' * (r : G)⁻¹) = ((r : G) * c' * (r : G)⁻¹) * r := by
      have h4 : n₀ * ((r : G) * ((r : G) * c' * (r : G)⁻¹)) =
          n₀ * (((r : G) * c' * (r : G)⁻¹) * r) := by
        rw [← mul_assoc, ← h2, mul_assoc, h1, mul_assoc]
      exact mul_left_cancel h4
    have h5 : (r : G) * c' * (r : G)⁻¹ = c' := by
      have h6 : (r : G) * ((r : G) * c' * (r : G)⁻¹) = (r : G) * c' := by
        rw [h3]
        group
      exact mul_left_cancel h6
    calc (r : G) * c' = (r : G) * c' * (r : G)⁻¹ * r := by group
      _ = c' * r := by rw [h5]
  have hc'Rad : (c' : G) ∈ Rad := by
    refine ⟨c'.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    by_cases hrH : p ⟨r, hr⟩ ∈ H
    · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∉ H := by
        by_contra hall
        push Not at hall
        exact hHtop (eq_top_iff.2 fun s _ => hall s)
      obtain ⟨r₁, rfl⟩ := hs.surj s₀
      have hr₂ : p (r₁⁻¹ * ⟨r, hr⟩) ∉ H := by
        intro hmem
        apply hs₀
        have : p r₁ = p ⟨r, hr⟩ * (p (r₁⁻¹ * ⟨r, hr⟩))⁻¹ := by
          rw [map_mul, map_inv]
          group
        rw [this]
        exact H.mul_mem hrH (H.inv_mem hmem)
      have h1 := hc'comm r₁ hs₀
      have h2 := hc'comm _ hr₂
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      calc r * c' = (r₁ : G) * ((r₁ : G)⁻¹ * r * c') := by group
        _ = (r₁ : G) * (c' * ((r₁ : G)⁻¹ * r)) := by rw [h2]
        _ = ((r₁ : G) * c') * ((r₁ : G)⁻¹ * r) := by group
        _ = (c' * r₁) * ((r₁ : G)⁻¹ * r) := by rw [h1]
        _ = c' * r := by group
    · exact hc'comm ⟨r, hr⟩ hrH
  have hRadR0 : Rad = R0 := by
    rcases hmax Rad hRadn hNRad inf_le_left with h1 | h1
    · exact absurd (h1 ▸ hc'Rad) hc'N
    · exact h1
  have hab : ∀ a ∈ R0, ∀ b ∈ R0, a * b = b * a := by
    intro a ha b hb
    have := (hRadR0 ▸ hb : b ∈ Rad).2
    exact (Subgroup.mem_centralizer_iff.1 this a ha)
  have hQR : ⁅Q, R⁆ ≤ Z := by
    rw [Subgroup.commutator_comm]
    exact hRK.trans hd.Kp_le
  have hψZ := hd.comm_le R hRT hZR hQR hRq3
  have hψZR : ⁅R, tImage ψ Z⁆ ≤ R :=
    commutator_le_left_of_le_normalizer ((tImage_le ψ Z).trans (hTM.trans hRn))
  have hQLR : ⁅Q, L⁆ ≤ R :=
    comm_le_of_comm_le h (tImage_le ψ Z) hd.crit' hQn hRn (hψZ.trans hψZR)
  have hVR0 : ⁅Q, L⁆ ≤ R0 := by
    rw [commutator_eq_commutator_commutator hQM hLM hQn hLn h.perfect]
    exact (Subgroup.commutator_mono hQLR le_rfl).trans le_sup_left
  have h3 : ⁅⁅R0, L⁆, Q⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm L Q, eq_bot_iff, Subgroup.commutator_le]
      intro v hv r hr
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab v (hVR0 hv) r hr
    · rw [eq_bot_iff, Subgroup.commutator_le]
      intro y hy l hl
      have hyK : y ∈ Kp := by
        rw [Subgroup.commutator_comm] at hy
        exact hRK ((Subgroup.commutator_mono hR0R le_rfl) hy)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.1 (hd.Kp_L hl) y hyK)
  have hR0LX : ⁅R0, L⁆ ≤ Xq M := by
    rw [Subgroup.commutator_le]
    intro r hr l hl
    have hmem : ⁅r, l⁆ ∈ ⁅R0, L⁆ := Subgroup.commutator_mem_commutator hr hl
    have hR0' : ⁅r, l⁆ ∈ R0 := commutator_le_left_of_le_normalizer hLR0 hmem
    have hcentQ : ⁅r, l⁆ ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 : ⁅⁅r, l⁆, x⁆ ∈ ⁅⁅R0, L⁆, Q⁆ := Subgroup.commutator_mem_commutator hmem hx
      rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hsq1 : ⁅r, l⁆ ^ 2 = 1 := by
      have hr' : l * r⁻¹ * l⁻¹ ∈ R0 := conj_mem hLR0 hl (R0.inv_mem hr)
      have e1 : ⁅r, l⁆ = r * (l * r⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hr2 : l * r ^ 2 * l⁻¹ = r ^ 2 := by
        have := Subgroup.mem_centralizer_iff.1 (hd.Kp_L hl) _ (hRsq r (hR0R hr))
        rw [← this, mul_inv_cancel_right]
      have hc : Commute r (l * r⁻¹ * l⁻¹) := hab r hr _ hr'
      have e2 : (l * r⁻¹ * l⁻¹) ^ 2 = (l * r ^ 2 * l⁻¹)⁻¹ := by
        rw [pow_two, pow_two]
        group
      rw [e1, hc.mul_pow, e2, hr2, mul_inv_cancel]
    exact Subgroup.subset_closure ⟨⟨hR0Q hR0', Subgroup.centralizer_le hQ.ge hcentQ⟩, hsq1⟩
  apply hR0Lnot
  rw [commutator_eq_commutator_commutator hR0M hLM hR0n hLn h.perfect]
  exact (Subgroup.commutator_mono hR0LX le_rfl).trans (hcom.comm_Xq.trans hUZ)

end Core

end CFSG.Quasithin.MS93.S36E
