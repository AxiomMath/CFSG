module

public import CFSG.Quasithin.H13.NQCatT513L225
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2PGL
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind

public section

namespace CFSG.Quasithin.H13.NQCat.T513

open CFSG.GorensteinWalter CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

theorem mem_of_odd_of_index_two {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2)
    {g : G} (hg : Odd (orderOf g)) : g ∈ H := by
  obtain ⟨k, hk⟩ := hg
  have h1 : g = (g * g) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [h1]
  exact H.pow_mem (Subgroup.mul_self_mem_of_index_two hH g) _

theorem ringAut_mul_self {K : Type} [Field K] {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hn2 : n ≤ 2)
    (hK : Nat.card K = p ^ n) (σ : K ≃+* K) : σ * σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hn hK
  have h1 : orderOf σ ∣ n := hcard ▸ orderOf_dvd_natCard σ
  have h2 : orderOf σ ∣ 2 := by
    interval_cases n
    · exact h1.trans (one_dvd 2)
    · exact h1
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem inner_of_odd_psl2 {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hσ : ∀ σ : K ≃+* K, σ * σ = 1) (α : MulAut (PSL2 K)) (hα : Odd (orderOf α)) :
    ∃ x : PSL2 K, α = MulAut.conj x := by
  obtain ⟨k, hk⟩ := hα
  set β := α ^ (k + 1) with hβdef
  have hβ : β * β = α := by
    rw [hβdef, ← pow_add, show k + 1 + (k + 1) = orderOf α + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  obtain ⟨g, σ, hgσ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_pglAction_mul_psl2FieldAut β
  have h1 : α = pglAction K (g * pgl2FieldAut K σ g) := by
    rw [← hβ, hgσ, map_mul,
      ← CFSG.RankThree.PartTwo.KFacts.psl2FieldAut_mul_pglAction_mul_inv σ g]
    calc pglAction K g * psl2FieldAut K σ * (pglAction K g * psl2FieldAut K σ)
        = pglAction K g * (psl2FieldAut K σ * pglAction K g * (psl2FieldAut K σ)⁻¹) *
            psl2FieldAut K (σ * σ) := by rw [map_mul]; group
      _ = _ := by rw [hσ σ, map_one, mul_one]
  set h := g * pgl2FieldAut K σ g
  have hho : Odd (orderOf h) := by
    rw [← orderOf_injective (pglAction K) CFSG.RankThree.PartTwo.KFacts.pglAction_injective h,
      ← h1]
    exact ⟨k, hk⟩
  obtain ⟨x, hx⟩ := mem_of_odd_of_index_two
    (CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pslRange_index_eq_two hK) hho
  exact ⟨x, by rw [h1, ← hx, pglAction_toPGL]⟩

section Facts

variable {A : Type} [Group A] {Q R S B D : Subgroup A}
variable {P : Type} [Group P] (e : ↥Q ⧸ Subgroup.center ↥Q ≃* P)

theorem conj_injective_of_center (hcen : Subgroup.center P = ⊥) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : x ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := DFunLike.congr_fun hx y
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * x = x * y * x⁻¹ * x := by rw [this]
      _ = x * y := by group
  rw [hcen, Subgroup.mem_bot] at hmem
  exact hmem

variable (hinn : ∀ α : MulAut P, Odd (orderOf α) → ∃ x, α = MulAut.conj x)

include hinn in
theorem aImg_D_inner [Finite A] (h : Star513 Q R S B D) :
    ∀ α ∈ aImg Q e D, ∃ x, α = MulAut.conj x := by
  intro α hα
  apply hinn
  have h1 : orderOf α ∣ Nat.card D :=
    (Subgroup.orderOf_dvd_natCard _ hα).trans (card_aImg_dvd Q e h.D_le_Q)
  exact Odd.of_dvd_nat h.D_odd h1

include hinn in
theorem iPart_D [Finite A] (h : Star513 Q R S B D) (hcen : Subgroup.center P = ⊥) :
    IsCyclic (iPart Q e D) ∧ Odd (Nat.card (iPart Q e D)) := by
  have hcj := conj_injective_of_center hcen
  have hinn' := aImg_D_inner e hinn h
  let f : ↥(iPart Q e D) →* ↥(aImg Q e D) :=
    ((MulAut.conj : P →* MulAut P).comp (iPart Q e D).subtype).codRestrict (aImg Q e D)
      fun y => y.2
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (hcj (congrArg Subtype.val hab))
    · rintro ⟨α, hα⟩
      obtain ⟨x, rfl⟩ := hinn' α hα
      exact ⟨⟨x, hα⟩, rfl⟩
  let ef := MulEquiv.ofBijective f hf
  refine ⟨?_, ?_⟩
  · have := isCyclic_aImg Q e h.D_le_Q h.D_cyclic
    exact isCyclic_of_surjective ef.symm.toMonoidHom ef.symm.surjective
  · rw [Nat.card_congr ef.toEquiv]
    exact Odd.of_dvd_nat h.D_odd (card_aImg_dvd Q e h.D_le_Q)

theorem pImg_SQ (h : Star513 Q R S B D) :
    IsPGroup 2 (pImg Q e (S ⊓ Q)) ∧ ¬ 2 ∣ (pImg Q e (S ⊓ Q)).index := by
  obtain ⟨-, hSQ2, hSQi⟩ := h.sylow_Q
  exact ⟨isPGroup_pImg Q e inf_le_right hSQ2,
    fun h2 => hSQi (h2.trans (Subgroup.index_map_dvd _ (toP_surjective Q e)))⟩

include hinn in
theorem perm_D [Finite A] (h : Star513 Q R S B D) (hcen : Subgroup.center P = ⊥) :
    ∀ t ∈ pImg Q e (S ⊓ Q), ∀ x ∈ iPart Q e D,
      ∃ x' ∈ iPart Q e D, ∃ t' ∈ pImg Q e (S ⊓ Q), t * x = x' * t' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  exact inner_perm Q e h.S_le_Q h.D_le_Q h.perm_D h.S_two (aImg_D_inner e hinn h)
    (conj_injective_of_center hcen) fun X hX hle => (hT2.toSylow hTi).is_maximal' hX hle

theorem toP_mem_normalizer_iPart [Finite P] (h : Star513 Q R S B D) {b : A} (hb : b ∈ B) :
    toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩ ∈ Subgroup.normalizer (iPart Q e D : Set P) := by
  have hbQ := h.R_le (h.hall_B.1 hb).1
  apply mem_normalizer_of_conj_mem
  intro x hx
  obtain ⟨d, hdN, hdD, hd⟩ := (mem_aImg Q e).1 (show MulAut.conj x ∈ aImg Q e D from hx)
  show MulAut.conj (toP Q e ⟨b, hbQ⟩ * x * (toP Q e ⟨b, hbQ⟩)⁻¹) ∈ aImg Q e D
  have hbd : b * d * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (h.B_le_D hb) d).mp hdD
  have hN : b * d * b⁻¹ ∈ Subgroup.normalizer (Q : Set A) := h.D_le_Q hbd
  have heq : autOf Q e ⟨b * d * b⁻¹, hN⟩ =
      MulAut.conj (toP Q e ⟨b, hbQ⟩ * x * (toP Q e ⟨b, hbQ⟩)⁻¹) := by
    have h1 : (⟨b * d * b⁻¹, hN⟩ : ↥(Subgroup.normalizer (Q : Set A))) =
        ⟨b, Subgroup.le_normalizer hbQ⟩ * ⟨d, hdN⟩ * ⟨b, Subgroup.le_normalizer hbQ⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, autOf_of_mem Q e hbQ, hd, map_mul, map_mul, map_inv]
  rw [← heq]
  exact autOf_mem_aImg Q e _ hbd

theorem toP_mem_normalizer_SR [Finite P] (h : Star513 Q R S B D) {b : A} (hb : b ∈ B) :
    toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩ ∈ Subgroup.normalizer (pImg Q e (S ⊓ R) : Set P) := by
  have hbQ := h.R_le (h.hall_B.1 hb).1
  apply mem_normalizer_of_conj_mem
  intro y hy
  obtain ⟨s, hsQ, hs, rfl⟩ := (mem_pImg Q e).1 hy
  have hbs : b * s * b⁻¹ ∈ S ⊓ R := (Subgroup.mem_normalizer_iff.mp (h.hall_B.1 hb).2 s).mp hs
  have : toP Q e ⟨b, hbQ⟩ * toP Q e ⟨s, hsQ⟩ * (toP Q e ⟨b, hbQ⟩)⁻¹ =
      toP Q e ⟨b * s * b⁻¹, h.R_le hbs.2⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact toP_mem_pImg Q e _ hbs

include hinn in
theorem le_normalizer_of_iPart [Finite A] (h : Star513 Q R S B D)
    (hD : iPart Q e D ≤ Subgroup.normalizer (pImg Q e R : Set P)) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  refine le_normalizer_of_pImg Q e h.R_le h.R_perfect h.D_le_Q fun d hd y hy => ?_
  obtain ⟨x, hx⟩ := aImg_D_inner e hinn h _ (autOf_mem_aImg Q e (h.D_le_Q hd) hd)
  have hxD : x ∈ iPart Q e D := by
    show MulAut.conj x ∈ aImg Q e D
    rw [← hx]
    exact autOf_mem_aImg Q e _ hd
  rw [hx, MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.mp (hD hxD) y).mp hy

theorem pImg_R_l24 [Finite A] (h : Star513 Q R S B D) (hZ2 : IsPGroup 2 (Subgroup.center ↥Q))
    (hP4 : ∀ X : Subgroup P, IsPGroup 2 X → Nat.card X ≤ 4) :
    Nonempty (↥(pImg Q e R) ≃* L24) := by
  obtain ⟨eX⟩ := exists_l24_of_lieModel h.R_type
  let f : ↥R →* ↥(pImg Q e R) :=
    ((toP Q e).comp (Subgroup.inclusion h.R_le)).codRestrict (pImg Q e R)
      fun r => toP_mem_pImg Q e (h.R_le r.2) r.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨r, hrQ, hrR, rfl⟩ := (mem_pImg Q e).1 hy
    exact ⟨⟨r, hrR⟩, rfl⟩
  have hker : IsPGroup 2 f.ker := by
    let g : ↥f.ker →* ↥(Subgroup.center ↥Q) :=
      ((Subgroup.inclusion h.R_le).comp f.ker.subtype).codRestrict _ fun r => by
        rw [← ker_toP Q e, MonoidHom.mem_ker]
        have := r.2
        rw [MonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
    refine hZ2.of_injective g fun a b hab => ?_
    have := congrArg (fun z : ↥(Subgroup.center ↥Q) => ((z : ↥Q) : A)) hab
    exact Subtype.ext (Subtype.ext this)
  exact nonempty_equiv_l24_of_surjective eX f hf hker fun X hX => by
    have := hP4 (X.map (pImg Q e R).subtype) (hX.map _)
    rwa [Subgroup.card_map_of_injective (pImg Q e R).subtype_injective] at this

theorem pImg_SQ_eq [Finite A] [Finite P] (h : Star513 Q R S B D) (eR : ↥(pImg Q e R) ≃* L24)
    (hP4 : ∀ X : Subgroup P, IsPGroup 2 X → Nat.card X ≤ 4) :
    pImg Q e (S ⊓ Q) = pImg Q e (S ⊓ R) := by
  have hle : pImg Q e (S ⊓ R) ≤ pImg Q e (S ⊓ Q) :=
    pImg_mono Q e (inf_le_inf_left _ h.R_le)
  obtain ⟨-, hSR2, hSRi⟩ := h.sylow_R
  set Y := (pImg Q e (S ⊓ R)).subgroupOf (pImg Q e R)
  let f : ↥R →* ↥(pImg Q e R) :=
    ((toP Q e).comp (Subgroup.inclusion h.R_le)).codRestrict (pImg Q e R)
      fun r => toP_mem_pImg Q e (h.R_le r.2) r.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨r, hrQ, hrR, rfl⟩ := (mem_pImg Q e).1 hy
    exact ⟨⟨r, hrR⟩, rfl⟩
  have hXY : ((S ⊓ R).subgroupOf R).map f ≤ Y := by
    rintro _ ⟨s, hs, rfl⟩
    exact toP_mem_pImg Q e _ hs
  have hYi : ¬ 2 ∣ Y.index := fun h2 =>
    hSRi ((h2.trans (Subgroup.index_dvd_of_le hXY)).trans (Subgroup.index_map_dvd _ hf))
  have h60 : Nat.card ↥(pImg Q e R) = 60 := CFSG.Walter.JT.card_of_psl24 eR
  have hY4 : 4 ≤ Nat.card Y := by
    have h1 := Subgroup.card_mul_index Y
    rw [h60] at h1
    have h2 : IsPGroup 2 Y := ((isPGroup_pImg Q e (inf_le_right.trans h.R_le) hSR2).of_equiv
      (Subgroup.subgroupOfEquivOfLe ((pImg_mono Q e inf_le_right))).symm)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [hk] at h1 ⊢
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hYc : Nat.card Y = Nat.card (pImg Q e (S ⊓ R)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pImg_mono Q e inf_le_right)).toEquiv
  obtain ⟨hT2, -⟩ := pImg_SQ e h
  have hT4 := hP4 _ hT2
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem exists_b [Finite A] (h : Star513 Q R S B D) (hZ2 : IsPGroup 2 (Subgroup.center ↥Q)) :
    ∃ (b : A) (hb : b ∈ B), orderOf (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB3 := card_B h
  let _ : Fintype ↥B := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card (G := ↥B) 3
    (by rw [← Nat.card_eq_fintype_card, hB3])
  refine ⟨b, b.2, ?_⟩
  have hbQ := h.R_le (h.hall_B.1 b.2).1
  have h1 : orderOf (toP Q e ⟨b, hbQ⟩) ∣ 3 := by
    rw [← hb, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk (b : A) hbQ]
    exact orderOf_map_dvd _ _
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
  · exfalso
    have hz : (⟨b, hbQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [← ker_toP Q e, MonoidHom.mem_ker, ← orderOf_eq_one_iff, h1]
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ2 ⟨_, hz⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hb] at hk
    rcases k with _ | k
    · norm_num at hk
    · have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
      rw [← hk] at h2
      omega
  · exact h1

end Facts

section Cases

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem eleven_le {p : ℕ} (hp : p.Prime) (h5 : p ^ 2 % 5 = 1) (h8 : p % 8 = 3 ∨ p % 8 = 5) :
    11 ≤ p := by
  by_contra h
  push Not at h
  interval_cases p <;> omega

theorem card_le_four_of_isPGroup {G : Type*} [Group G] [Finite G] {u : ℕ} (hu : Odd u)
    (hG : Nat.card G = 4 * u) (X : Subgroup G) (hX : IsPGroup 2 X) : Nat.card X ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  have h1 : 2 ^ k ∣ 4 * u := hk ▸ hG ▸ Subgroup.card_subgroup_dvd_card X
  have h2 : 2 ^ k ∣ 4 :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hu)).dvd_of_dvd_mul_right h1
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) h2

theorem normalizer_of_psl2_prime
    (h : Star513 Q R S B D) {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : Nat.card K = p) (h5 : p ^ 2 % 5 = 1) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : ↥Q ⧸ Subgroup.center ↥Q ≃* PSL2 K) (hZ2 : IsPGroup 2 (Subgroup.center ↥Q)) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp11 := eleven_le hp h5 h8
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  have hcen := psl2_center_eq_bot K
  have hinn : ∀ α : MulAut (PSL2 K), Odd (orderOf α) → ∃ x, α = MulAut.conj x :=
    inner_of_odd_psl2 hodd (ringAut_mul_self hp le_rfl (by norm_num) (by rw [hK, pow_one]))
  obtain ⟨u, hu, hPu, -⟩ := psl2_card_four_mul hp hK h8
  have hP4 := card_le_four_of_isPGroup hu hPu
  obtain ⟨eR⟩ := pImg_R_l24 e h hZ2 hP4
  obtain ⟨hDc, hDo⟩ := iPart_D e hinn h hcen
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hTeq := pImg_SQ_eq e h eR hP4
  obtain ⟨b, hb, hb3⟩ := exists_b e h hZ2
  apply le_normalizer_of_iPart e hinn h
  refine core_psl2_prime hK h8 hp11 (hT2.toSylow hTi) hDc hDo (perm_D e hinn h hcen) eR ?_
    (toP_mem_pImg Q e _ (h.hall_B.1 hb).1) hb3 (toP_mem_normalizer_iPart e h hb) ?_
  · show pImg Q e (S ⊓ Q) ≤ pImg Q e R
    rw [hTeq]
    exact pImg_mono Q e inf_le_right
  · show _ ∈ Subgroup.normalizer (pImg Q e (S ⊓ Q) : Set (PSL2 K))
    rw [hTeq]
    exact toP_mem_normalizer_SR e h hb

theorem normalizer_of_psl2_25 (h : Star513 Q R S B D)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5 ^ 2)
    (e : ↥Q ⧸ Subgroup.center ↥Q ≃* PSL2 K) (hZ : Subgroup.center ↥Q = ⊥) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : IsOddPrimePower (Nat.card K) := ⟨5, 2, by norm_num, by decide, by norm_num, hK⟩
  have hcen := psl2_center_eq_bot K
  have hinn : ∀ α : MulAut (PSL2 K), Odd (orderOf α) → ∃ x, α = MulAut.conj x :=
    inner_of_odd_psl2 hodd (ringAut_mul_self (by norm_num) (by norm_num) le_rfl hK)
  obtain ⟨hDc, hDo⟩ := iPart_D e hinn h hcen
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hinj : Function.Injective (toP Q e) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_toP, hZ]
  have hBQ : B ≤ Q := fun b hb => h.R_le (h.hall_B.1 hb).1
  have hB3 : Nat.card (pImg Q e B) = 3 := by
    rw [pImg, Subgroup.card_map_of_injective hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv, card_B h]
  have hBD : pImg Q e B ≤ Subgroup.normalizer (iPart Q e D : Set (PSL2 K)) := by
    intro y hy
    obtain ⟨b, hbQ, hb, rfl⟩ := (mem_pImg Q e).1 hy
    exact toP_mem_normalizer_iPart e h hb
  have hle := core_psl2_25 hK (hT2.toSylow hTi) hDc hDo (perm_D e hinn h hcen) hB3 hBD
  apply le_normalizer_of_iPart e hinn h
  intro x hx
  exact Subgroup.le_normalizer (pImg_mono Q e (fun b hb => (h.hall_B.1 hb).1) (hle hx))

theorem normalizer_of_psl2
    (h : Star513 Q R S B D)
    (hQ : (∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
        (IsPSL 2 p 1 ↥Q ∨ IsSL2 p ↥Q)) ∨ IsPSL 2 5 2 ↥Q) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  have hpsl : ∀ {K : Type} [Field K] [Finite K], (↥Q ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) →
      Subgroup.center ↥Q = ⊥ ∧ Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* PSL2 K) := by
    intro K _ _ e₀
    let e₁ : ↥Q ≃* PSL2 K :=
      e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    have hZ : Subgroup.center ↥Q = ⊥ := by
      have h1 := Subgroup.map_center_eq e₁
      rw [psl2_center_eq_bot K] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e₁.injective).mp h1
    exact ⟨hZ, ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans e₁)⟩⟩
  rcases hQ with ⟨p, hp, h5, h8, hQ | hQ⟩ | hQ
  · obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨hZ, ⟨e⟩⟩ := hpsl e₀
    exact normalizer_of_psl2_prime h hp (by rw [hK, pow_one]) h5 h8 e
      (hZ ▸ IsPGroup.of_bot)
  · obtain ⟨e₀⟩ := hQ
    have : Fact p.Prime := ⟨hp⟩
    let e : ↥Q ⧸ Subgroup.center ↥Q ≃* PSL2 (ZMod p) :=
      QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
    have hZ2 : IsPGroup 2 (Subgroup.center ↥Q) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [IsPGroup.iff_orderOf]
      intro z
      have hz : e₀ (z : ↥Q) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
        rw [← Subgroup.map_center_eq e₀]
        exact ⟨z, z.2, rfl⟩
      obtain ⟨r, hr, hre⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
      have hsq : (e₀ (z : ↥Q)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Fintype.card_fin] at hr
        rw [Matrix.SpecialLinearGroup.coe_pow, ← hre, Matrix.SpecialLinearGroup.coe_one,
          ← map_pow, hr, map_one]
      have hz2 : z ^ 2 = 1 := by
        apply Subtype.ext
        apply e₀.injective
        rw [Subgroup.coe_pow, map_pow, hsq, Subgroup.coe_one, map_one]
      have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
      · exact ⟨0, by rw [h1, pow_zero]⟩
      · exact ⟨1, by rw [h1, pow_one]⟩
    exact normalizer_of_psl2_prime h hp (ZMod.card p ▸ Nat.card_zmod p) h5 h8 e hZ2
  · obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨hZ, ⟨e⟩⟩ := hpsl e₀
    exact normalizer_of_psl2_25 h hK e hZ

end Cases

end CFSG.Quasithin.H13.NQCat.T513
