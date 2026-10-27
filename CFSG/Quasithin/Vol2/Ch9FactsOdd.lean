module

public import CFSG.Quasithin.Vol2.Ch9Facts
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.Quasithin.Vol2.Ch10SecKHBCb

public section

namespace CFSG.Quasithin.H13.Ch9.FactsOdd

open CFSG.Quasithin CFSG.QuasithinUnique Matrix
open CFSG.Quasithin.Vol2.Ch10.SecB

theorem card_le_relIndex_of_le_normalizer {Y : Type} [Group Y] [Finite Y] {S E : Subgroup Y}
    (hS : IsPGroup 2 S) (hE : Odd (Nat.card E)) (hEN : E ≤ Subgroup.normalizer (S : Set Y)) :
    Nat.card E ≤ S.relIndex (Subgroup.normalizer (S : Set Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hEN
  have hSE : E ⊓ S = ⊥ := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [ha]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hE)
  rw [hSE, Subgroup.card_bot, mul_one] at h1
  have h2 : Nat.card ↥(E ⊔ S) ≤ Nat.card ↥(Subgroup.normalizer (S : Set Y)) :=
    Subgroup.card_le_of_le (sup_le hEN Subgroup.le_normalizer)
  have h3 := Subgroup.relIndex_mul_card S (Subgroup.normalizer (S : Set Y))
  rw [inf_of_le_left Subgroup.le_normalizer] at h3
  rw [h1, ← h3] at h2
  exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos

theorem exists_le_normalizer_card_eq {Y X : Type} [Group Y] [Finite Y] [Group X] [Finite X]
    (e : Y ≃* X) {U₀ : Subgroup X} (hU₀ : IsSylowTwoOf U₀ ⊤) {E : Subgroup X}
    (hE : E ≤ Subgroup.normalizer (U₀ : Set X)) {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) :
    ∃ E' : Subgroup Y, E' ≤ Subgroup.normalizer (S : Set Y) ∧ Nat.card E' = Nat.card E := by
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf
    (CFSG.Quasithin.A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hS) hU₀
  set e₂ : Y ≃* X := e.trans (MulAut.conj g) with he₂
  have hS₂ : S.map e₂.toMonoidHom = U₀ := by
    rw [← hg, Subgroup.map_map]
    rfl
  refine ⟨E.map e₂.symm.toMonoidHom, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 : x ∈ (Subgroup.normalizer (S : Set Y)).map e₂.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq, hS₂]
      exact hE hx
    obtain ⟨y, hy, hyx⟩ := h1
    rw [← hyx]
    simpa using hy
  · exact (Nat.card_congr (E.equivMapOfInjective _ e₂.symm.injective).toEquiv).symm

theorem lt_relIndex_of_model {Y X : Type} [Group Y] [Finite Y] [Group X] [Finite X]
    (e : Y ≃* X) {U₀ : Subgroup X} (hU₀ : IsSylowTwoOf U₀ ⊤) {E : Subgroup X}
    (hE : E ≤ Subgroup.normalizer (U₀ : Set X)) (hEodd : Odd (Nat.card E)) {N : ℕ}
    (hEN : N < Nat.card E) {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) :
    N < S.relIndex (Subgroup.normalizer (S : Set Y)) := by
  obtain ⟨E', hE'N, hE'c⟩ := exists_le_normalizer_card_eq e hU₀ hE hS
  have h := card_le_relIndex_of_le_normalizer hS.2.1 (hE'c ▸ hEodd) hE'N
  omega

theorem odd_card_sup_zpowers {X : Type} [Group X] [Finite X] {a b : X} (hab : a * b = b * a)
    (ha : Odd (orderOf a)) (hb : Odd (orderOf b)) :
    Odd (Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b)) := by
  have hN : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have : b * a ^ k * b⁻¹ = a ^ k := by
        rw [((Commute.zpow_left (show Commute a b from hab) k)).symm.eq, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem_zpowers a k
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have h2 : x = b⁻¹ * a ^ k * b := by rw [hk]; group
      rw [h2]
      have : b⁻¹ * a ^ k * b = a ^ k := by
        rw [mul_assoc, ((Commute.zpow_left (show Commute a b from hab) k)).eq,
          inv_mul_cancel_left]
      rw [this]
      exact Subgroup.zpow_mem_zpowers a k
  have h := C5.card_sup_mul_card_inf_of_le_normalizer hN
  rw [Nat.card_zpowers, Nat.card_zpowers] at h
  rw [sup_comm]
  exact (hb.mul ha).of_dvd_nat (Dvd.intro _ h)

theorem lt_card_psu3 {Q : ℕ} (hQ : 4 ≤ Q) (hQ2 : Even Q) :
    Q - 1 < (Q ^ 2 - 1) / Nat.gcd 3 (Q + 1) := by
  set δ := Nat.gcd 3 (Q + 1) with hδ
  have hδ3 : δ ∣ 3 := Nat.gcd_dvd_left _ _
  have hδQ : δ ∣ Q + 1 := Nat.gcd_dvd_right _ _
  have hsq : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    zify [show 1 ≤ Q ^ 2 from Nat.one_le_pow _ _ (by omega), show 1 ≤ Q by omega]
    ring
  obtain ⟨r, hr⟩ := hδQ
  have hδpos : 0 < δ := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hr2 : 2 ≤ r := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hδ3 with h | h
    · rw [h] at hr; omega
    · rw [h] at hr
      obtain ⟨s, hs⟩ := hQ2
      omega
  rw [hsq, hr, show (Q - 1) * (δ * r) = δ * ((Q - 1) * r) by ring,
    Nat.mul_div_cancel_left _ hδpos]
  have : (Q - 1) * 2 ≤ (Q - 1) * r := Nat.mul_le_mul_left _ hr2
  omega

@[expose] noncomputable def diagThreeHom' {K : Type} [Field K] :
    Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun l := ⟨diagonal ![1, (l : K), ((l⁻¹ : Kˣ) : K)], by
    simp [det_diagonal, Fin.prod_univ_three]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' l m := by
    apply Subtype.ext
    show diagonal ![1, ((l * m : Kˣ) : K), (((l * m)⁻¹ : Kˣ) : K)] =
      diagonal ![1, (l : K), ((l⁻¹ : Kˣ) : K)] * diagonal ![1, (m : K), ((m⁻¹ : Kˣ) : K)]
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

theorem coe_diagThreeHom' {K : Type} [Field K] (l : Kˣ) :
    (diagThreeHom' l : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, (l : K), ((l⁻¹ : Kˣ) : K)] :=
  rfl

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem not_mem_zpowers_diagThree {K : Type} [Field K] {l : Kˣ} (hl : l ^ 3 ≠ 1) :
    proj 3 K (diagThreeHom' l) ∉ Subgroup.zpowers (proj 3 K (C10KH.diagThreeHom l)) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← map_zpow, ← map_zpow, proj_eq_proj_iff, ← map_inv] at hk
  obtain ⟨c, -, hc⟩ := hk
  rw [Matrix.SpecialLinearGroup.coe_mul, C10KH.coe_diagThreeHom, coe_diagThreeHom',
    diagonal_mul_diagonal] at hc
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  have h22 := congrFun (congrFun hc 2) 2
  simp only [diagonal_apply_eq, scalar_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one, one_mul, inv_inv]
    at h00 h11 h22
  set μ := l ^ k with hμ
  apply hl
  apply Units.ext
  have hμl : ((μ : Kˣ) : K) = l := by
    have h1 : ((μ⁻¹ : Kˣ) : K) = ((l⁻¹ : Kˣ) : K) := by rw [h00, ← h22]
    have h2 : μ⁻¹ = l⁻¹ := Units.ext h1
    rw [inv_inj.mp h2]
  have h3 : ((μ : Kˣ) : K) * l = ((l⁻¹ : Kˣ) : K) := by rw [h11, ← h22]
  rw [hμl] at h3
  have h4 : (l : K) * l * l = 1 := by
    rw [h3]
    exact Units.inv_mul l
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three, ← mul_assoc]
  exact h4

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem exists_odd_psl3 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) :
    ∃ E : Subgroup (projectiveSL 3 K),
      E ≤ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) ∧
      Odd (Nat.card E) ∧ Nat.card K - 1 < Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hl
  set d₁ := proj 3 K (C10KH.diagThreeHom l) with hd₁
  set d₂ := proj 3 K (diagThreeHom' l) with hd₂
  have hmem : ∀ A : SpecialLinearGroup (Fin 3) K, (∀ i j, i ≠ j →
      (A : Matrix (Fin 3) (Fin 3) K) i j = 0) →
      proj 3 K A ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
    intro A hA
    rw [normalizer_projUnitriangular (n := 3) 2]
    exact ⟨A, fun i j hij => hA i j (ne_of_gt hij), rfl⟩
  have hd₁N := hmem (C10KH.diagThreeHom l) fun i j hij => by
    rw [C10KH.coe_diagThreeHom, diagonal_apply_ne _ hij]
  have hd₂N := hmem (diagThreeHom' l) fun i j hij => by
    rw [coe_diagThreeHom', diagonal_apply_ne _ hij]
  have hcomm : d₁ * d₂ = d₂ * d₁ := by
    rw [hd₁, hd₂, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      C10KH.coe_diagThreeHom, coe_diagThreeHom', diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_comm]
  have ho₁ : orderOf d₁ = Nat.card K - 1 := by
    rw [hd₁, ← MonoidHom.comp_apply, orderOf_injective _ C10KH.projDiagThree_injective l, hl]
  have hodd : Odd (Nat.card K - 1) := by
    have := Fintype.ofFinite K
    obtain ⟨k, -, hk⟩ := FiniteField.card K 2
    rw [← Nat.card_eq_fintype_card] at hk
    rw [hk]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, (PNat.pos k).ne'⟩) odd_one
  have ho₂ : Odd (orderOf d₂) := by
    refine hodd.of_dvd_nat ?_
    rw [← hl]
    exact (orderOf_map_dvd _ _).trans (orderOf_map_dvd _ _)
  have hl3 : l ^ 3 ≠ 1 := by
    intro h3
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hl] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  refine ⟨Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂, sup_le (Subgroup.zpowers_le.mpr hd₁N)
    (Subgroup.zpowers_le.mpr hd₂N), odd_card_sup_zpowers hcomm (ho₁ ▸ hodd) ho₂, ?_⟩
  rw [← ho₁, ← Nat.card_zpowers]
  refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => ?_)
  apply not_mem_zpowers_diagThree hl3
  rw [h]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

section Sp4

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

noncomputable abbrev torusP (K : Type) [Field K] : (Fin 2 → Kˣ) →* StatedProj (StatedSp 2 K) :=
  (proj 2 K).comp torusHom

theorem torusP_injective {K : Type} [Field K] [CharP K 2] :
    Function.Injective (torusP K) :=
  CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo.comp torusHom_injective

theorem torusP_mem_normalizer {K : Type} [Field K] (x : Fin 2 → Kˣ) :
    torusP K x ∈ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) := by
  rw [projUnipotent]
  apply Subgroup.le_normalizer_map (proj 2 K)
  refine ⟨torusHom x, ?_, rfl⟩
  rw [normalizer_unipotent]
  exact torus_le_borelSubgroup (torusHom_mem_torus _)

theorem exists_odd_psp4 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)),
      E ≤ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) ∧
      Odd (Nat.card E) ∧ Nat.card K - 1 < Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hl
  set d₁ := torusP K (Pi.mulSingle 0 l) with hd₁
  set d₂ := torusP K (Pi.mulSingle 1 l) with hd₂
  have hcomm : d₁ * d₂ = d₂ * d₁ := by
    rw [hd₁, hd₂, ← map_mul, ← map_mul, mul_comm]
  have hinj₀ : Function.Injective ((torusP K).comp (MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) 0)) :=
    torusP_injective.comp fun a b h => by simpa using congrFun h 0
  have ho₁ : orderOf d₁ = Nat.card K - 1 := by
    rw [hd₁, show torusP K (Pi.mulSingle 0 l) =
      ((torusP K).comp (MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) 0)) l from rfl,
      orderOf_injective _ hinj₀ l, hl]
  have hodd : Odd (Nat.card K - 1) := by
    have := Fintype.ofFinite K
    obtain ⟨k, -, hk⟩ := FiniteField.card K 2
    rw [← Nat.card_eq_fintype_card] at hk
    rw [hk]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, (PNat.pos k).ne'⟩) odd_one
  have ho₂ : Odd (orderOf d₂) := by
    refine hodd.of_dvd_nat ?_
    rw [← hl, hd₂, show torusP K (Pi.mulSingle 1 l) =
      ((torusP K).comp (MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) 1)) l from rfl]
    exact orderOf_map_dvd _ _
  have hl1 : l ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hl
    omega
  refine ⟨Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂, sup_le
    (Subgroup.zpowers_le.mpr (torusP_mem_normalizer _))
    (Subgroup.zpowers_le.mpr (torusP_mem_normalizer _)), odd_card_sup_zpowers hcomm (ho₁ ▸ hodd)
    ho₂, ?_⟩
  rw [← ho₁, ← Nat.card_zpowers]
  refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => ?_)
  have hd₂mem : d₂ ∈ Subgroup.zpowers d₁ := by
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd₂mem
  rw [hd₁, hd₂, ← map_zpow] at hk
  have h2 := congrFun (torusP_injective hk) 1
  simp at h2
  exact hl1 h2.symm

end Sp4

theorem factBorelOddLarge_holds : FactBorelOddLarge := by
  intro Y _ _ m hY S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hY with ⟨hm, hY⟩ | ⟨hm, hY⟩ | ⟨hm, hY⟩
  ·
    have hidx : ¬ 2 ∣ S.index := by
      have h : ¬ 2 ∣ (S.subgroupOf ⊤).index := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
    let T : Sylow 2 Y := hS.2.1.toSylow hidx
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
    have hcard : Nat.card K = 2 ^ (2 * m) := by rw [hK, ← pow_mul, mul_comm]
    let e₀ : Y ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ m)) := e
    let e' := e₀.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative m hm hcard)
    obtain ⟨D, hD⟩ :=
      CFSG.Goldschmidt.G3a.exists_borelSetup (Or.inr (Or.inl ⟨m, hm, ⟨e'⟩⟩)) T
    have hDc := (hD.orders_psu3 hm e').2.2
    have h1 := card_le_relIndex_of_le_normalizer hS.2.1 hD.odd hD.le
    have h2 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h3 := lt_card_psu3 h2 (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    rw [← hDc] at h3
    exact lt_of_lt_of_le h3 h1
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
      (K := K) 2 (n := 3) (by norm_num)
    have hU₀ : IsSylowTwoOf (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular 3 K)
        ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
    have h8 : 8 ≤ Nat.card K := by
      rw [hK]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨E, hEN, hEodd, hEc⟩ := exists_odd_psl3 h8
    rw [hK] at hEc
    exact lt_relIndex_of_model
      (e.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 K)) hU₀ hEN hEodd hEc hS
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    obtain ⟨P, hP⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_projUnipotent
        (K := K) 2 (r := 2) (by norm_num)
    have hU₀ : IsSylowTwoOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent 2 K)
        ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨E, hEN, hEodd, hEc⟩ := exists_odd_psp4 h4
    rw [hK] at hEc
    exact lt_relIndex_of_model e hU₀ hEN hEodd hEc hS

end CFSG.Quasithin.H13.Ch9.FactsOdd
