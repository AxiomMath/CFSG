module

public import CFSG.LocalAnalysis.StandardType.GGResJFusion
import CFSG.GroupTheory.OmegaCentral.Cyclic
import CFSG.LocalAnalysis.StandardType.GGNbrU63StepTwo
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggExists_inv_le_of_isReflection {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs : Subgroup G} (hBs : IsMulCommutative Bs) (hBp : ∀ b ∈ Bs, b ^ p = 1)
    {τ : MulAut ↥Bs} (hτ : GGIsReflection p τ) :
    ∃ U : Subgroup G, Nat.card U ≤ p ∧
      ∀ (b : G) (hb : b ∈ Bs), ((τ ⟨b, hb⟩ : ↥Bs) : G) = b⁻¹ → b ∈ U := by
  classical
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.is_comm.comm a b
  let f : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * τ b
      map_one' := by rw [map_one, inv_one, one_mul]
      map_mul' := fun a b => by
        change (a * b)⁻¹ * τ (a * b) = (a⁻¹ * τ a) * (b⁻¹ * τ b)
        rw [map_mul, mul_inv_rev]
        have h1 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := hcomm b⁻¹ a⁻¹
        have h2 : b⁻¹ * τ a = τ a * b⁻¹ := hcomm b⁻¹ (τ a)
        calc b⁻¹ * a⁻¹ * (τ a * τ b) = (a⁻¹ * b⁻¹) * (τ a * τ b) := by rw [h1]
          _ = a⁻¹ * (b⁻¹ * (τ a * τ b)) := by rw [mul_assoc]
          _ = a⁻¹ * ((b⁻¹ * τ a) * τ b) := by rw [mul_assoc]
          _ = a⁻¹ * ((τ a * b⁻¹) * τ b) := by rw [h2]
          _ = (a⁻¹ * τ a) * (b⁻¹ * τ b) := by
            rw [mul_assoc (τ a) b⁻¹ (τ b), mul_assoc] }
  have hker : Nat.card f.ker = Nat.card {b : ↥Bs // τ b = b} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
    show f x = 1 ↔ τ x = x
    rw [show f x = x⁻¹ * τ x from rfl, inv_mul_eq_one, eq_comm]
  have hcard : Nat.card f.range * Nat.card f.ker = Nat.card ↥Bs := by
    rw [mul_comm]
    exact Subgroup.card_ker_mul_card_range f
  have hpker : p * Nat.card f.ker = Nat.card ↥Bs := by
    rw [hker, mul_comm]
    exact hτ.2
  have hfr : Nat.card f.range = p := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.ker)) ?_
    rw [hcard, hpker]
  refine ⟨f.range.map Bs.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Subtype.coe_injective]
    exact le_of_eq hfr
  · intro b hb hbinv
    set x : ↥Bs := ⟨b, hb⟩ with hxdef
    have hxp : x ^ p = 1 := by
      rw [hxdef]
      exact Subtype.ext (by simpa using hBp b hb)
    have hτx : τ x = x⁻¹ := by
      rw [hxdef]
      exact Subtype.ext hbinv
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    let j : ℕ := p / 2
    have hj : 2 * j = p - 1 := by
      have h := Nat.div_two_mul_two_add_one_of_odd hodd
      simp only [j] at h ⊢
      omega
    have hxpm1 : x ^ (p - 1) = x⁻¹ := by
      have hpos : 0 < p := (Fact.out : p.Prime).pos
      have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hpos
      have h1 : x ^ (p - 1) * x = 1 := by rw [← pow_succ, hp1, hxp]
      exact eq_inv_of_mul_eq_one_left h1
    have hfpow : f (x ^ j) = x := by
      calc f (x ^ j) = (x ^ j)⁻¹ * τ (x ^ j) := rfl
        _ = (x⁻¹) ^ j * (τ x) ^ j := by rw [← inv_pow, map_pow]
        _ = (x⁻¹) ^ j * (x⁻¹) ^ j := by rw [hτx]
        _ = (x⁻¹) ^ (j + j) := by rw [← pow_add]
        _ = (x⁻¹) ^ (2 * j) := by rw [two_mul]
        _ = (x ^ (2 * j))⁻¹ := by rw [inv_pow]
        _ = (x ^ (p - 1))⁻¹ := by rw [hj]
        _ = (x⁻¹)⁻¹ := by rw [hxpm1]
        _ = x := inv_inv x
    exact Subgroup.mem_map.mpr ⟨x, ⟨x ^ j, hfpow⟩, rfl⟩

private theorem ggJORSAux_aut_eq_one_or {G : Type} [Group G] {Bs J : Subgroup G}
    {τ : MulAut ↥Bs} (hτ : τ ^ 2 = 1) (hAτ : ggAutomizer J Bs = Subgroup.zpowers τ) :
    ∀ a ∈ ggAutomizer J Bs, a = 1 ∨ a = τ := by
  intro a ha
  rw [hAτ] at ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rcases Int.even_or_odd' k with ⟨r, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_ofNat, hτ, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_ofNat, hτ, one_zpow, one_mul]

private theorem ggJORSAux_no_p_torsion {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs J : Subgroup G} {τ : MulAut ↥Bs} (hτ : τ ^ 2 = 1)
    (hAτ : ggAutomizer J Bs = Subgroup.zpowers τ) :
    ∀ a ∈ ggAutomizer J Bs, ∀ k : ℕ, a ^ p ^ k = 1 → a = 1 := by
  intro a ha k hk
  rcases ggJORSAux_aut_eq_one_or hτ hAτ a ha with rfl | rfl
  · rfl
  · have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two Fact.out).mpr hp2.symm)
    have hd : orderOf a ∣ Nat.gcd 2 (p ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτ) (orderOf_dvd_of_pow_eq_one hk)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at hd
    exact orderOf_eq_one_iff.mp hd

theorem ggConj_eq_or_of_automizer_zpowers {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs J : Subgroup G} (hBs : IsMulCommutative Bs)
    (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {τ : MulAut ↥Bs} (hτ : τ ^ 2 = 1)
    (hAτ : ggAutomizer J Bs = Subgroup.zpowers τ)
    {Q : Subgroup G} (hQC : Q ≤ Subgroup.centralizer (Bs : Set G)) {m : G} (hm : m ∈ J)
    (hmQ : ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) :
    (∀ w ∈ Q, w ^ p = 1 → m * w * m⁻¹ = w) ∨
      ∀ (w : G) (hw : w ∈ Q) (hwp : w ^ p = 1),
        m * w * m⁻¹ = ((τ ⟨w, hSC w (hQC hw) hwp⟩ : ↥Bs) : G) := by
  classical
  have hτa := ggJORSAux_aut_eq_one_or hτ hAτ
  have hA := ggJORSAux_no_p_torsion hp2 hτ hAτ
  have hconjV : ∀ w ∈ Q ⊓ Bs, m * w * m⁻¹ ∈ Q ⊓ Bs := by
    intro w hw
    rw [Subgroup.mem_inf] at hw
    refine Subgroup.mem_inf.mpr ⟨hmQ w hw.1, hSC _ (hQC (hmQ w hw.1)) ?_⟩
    rw [conj_pow, hBp w hw.2, mul_one, mul_inv_cancel]
  let cV : ↥(Q ⊓ Bs) →* ↥(Q ⊓ Bs) :=
    { toFun := fun w => ⟨m * (w : G) * m⁻¹, hconjV w w.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        change m * ((a : G) * (b : G)) * m⁻¹ =
          (m * (a : G) * m⁻¹) * (m * (b : G) * m⁻¹)
        group }
  let toBs : ↥(Q ⊓ Bs) →* ↥Bs :=
    { toFun := fun w => ⟨(w : G), w.2.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  let cBs : ↥(Q ⊓ Bs) →* ↥Bs := toBs.comp cV
  let τH : ↥(Q ⊓ Bs) →* ↥Bs := (MulEquiv.toMonoidHom τ).comp toBs
  have hcover : ((⊤ : Subgroup ↥(Q ⊓ Bs)) : Set ↥(Q ⊓ Bs)) ⊆
      (MonoidHom.eqLocus cBs toBs : Set ↥(Q ⊓ Bs)) ∪
        (MonoidHom.eqLocus cBs τH : Set ↥(Q ⊓ Bs)) := by
    intro w _
    obtain ⟨a, ha, he⟩ := ggFusion_exists_automizer hBs hBp hSC hN hA
      (u := (w : G)) (n := m) w.2.2 hm (hconjV w w.2).2
    rcases hτa a ha with rfl | rfl
    · left
      exact Subtype.ext (by simpa [cBs, toBs, cV] using he.symm)
    · right
      exact Subtype.ext (by simpa [cBs, toBs, cV, τH] using he.symm)
  rcases SubgroupClass.subset_union.1 hcover with hA1 | hA2
  · left
    intro w hw hwp
    have hwB : w ∈ Bs := hSC w (hQC hw) hwp
    have hwV : w ∈ Q ⊓ Bs := ⟨hw, hwB⟩
    have hmem : (⟨w, hwV⟩ : ↥(Q ⊓ Bs)) ∈ MonoidHom.eqLocus cBs toBs :=
      hA1 (show (⟨w, hwV⟩ : ↥(Q ⊓ Bs)) ∈ (⊤ : Subgroup ↥(Q ⊓ Bs)) from trivial)
    have heq : cBs ⟨w, hwV⟩ = toBs ⟨w, hwV⟩ := hmem
    exact congrArg Subtype.val heq
  · right
    intro w hw hwp
    have hwB : w ∈ Bs := hSC w (hQC hw) hwp
    have hwV : w ∈ Q ⊓ Bs := ⟨hw, hwB⟩
    have hmem : (⟨w, hwV⟩ : ↥(Q ⊓ Bs)) ∈ MonoidHom.eqLocus cBs τH :=
      hA2 (show (⟨w, hwV⟩ : ↥(Q ⊓ Bs)) ∈ (⊤ : Subgroup ↥(Q ⊓ Bs)) from trivial)
    have heq : cBs ⟨w, hwV⟩ = τH ⟨w, hwV⟩ := hmem
    exact congrArg Subtype.val heq


theorem ggIsCyclic_of_le_of_automizer_refl {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs J : Subgroup G} (hBs : IsMulCommutative Bs)
    (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (hJ : commutator ↥J = ⊤) {τ : MulAut ↥Bs}
    (hτ : GGIsReflection p τ) (hAτ : ggAutomizer J Bs = Subgroup.zpowers τ)
    {Q : Subgroup G} (hQ : IsPGroup p Q) (hQJ : Q ≤ J) : IsCyclic Q := by
  classical
  have hτ2 : τ ^ 2 = 1 := hτ.1
  have hA : ∀ a ∈ ggAutomizer J Bs, ∀ k : ℕ, a ^ p ^ k = 1 → a = 1 :=
    ggJORSAux_no_p_torsion hp2 hτ2 hAτ
  have hQK : IsPGroup p (Q.comap J.subtype) :=
    hQ.comap_of_injective J.subtype J.subtype_injective
  obtain ⟨P, hQKP⟩ := hQK.exists_le_sylow
  have hP₀p : IsPGroup p ((P : Subgroup ↥J).map J.subtype) := P.isPGroup'.map _
  have hP₀J : (P : Subgroup ↥J).map J.subtype ≤ J := Subgroup.map_subtype_le _
  obtain ⟨g, hg, hgC⟩ :=
    ggSylow_exists_conj_mem_centralizer hBs hBp hSC hN hA hP₀p hP₀J
  set gK : ↥J := ⟨g, hg⟩ with hgKdef
  set S : Sylow p ↥J := gK • P with hSdef
  have hScent : ∀ x ∈ (S : Subgroup ↥J),
      ((x : ↥J) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    intro x hx
    have hx' : x ∈ ((gK • P : Sylow p ↥J) : Subgroup ↥J) := by rw [← hSdef]; exact hx
    rw [Sylow.coe_subgroup_smul] at hx'
    obtain ⟨p, hp, hpx⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj gK) ↑P).mp hx'
    have hxG : ((x : ↥J) : G) = g * ((p : ↥J) : G) * g⁻¹ := by
      rw [← hpx, hgKdef]
      simp [MulAut.conj_apply]
    rw [hxG]
    exact hgC ((p : ↥J) : G) (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
  have hcen : ∀ w ∈ (S : Subgroup ↥J), w ^ p = 1 →
      ∀ s ∈ (S : Subgroup ↥J), s * w = w * s := by
    intro w hw hwp s hs
    have hwC := hScent w hw
    have hwBs : ((w : ↥J) : G) ∈ Bs :=
      hSC _ hwC (by simpa using congrArg Subtype.val hwp)
    have hsC := hScent s hs
    have hcomm := Subgroup.mem_centralizer_iff.mp hsC ((w : ↥J) : G) hwBs
    exact J.subtype_injective (by rw [map_mul, map_mul]; exact hcomm.symm)
  have hmapC : ((S : Subgroup ↥J).map J.subtype) ≤
      Subgroup.centralizer (Bs : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    exact hScent y hy
  have hmapN : ∀ c : ↥J, c ∈ Subgroup.normalizer ((S : Subgroup ↥J) : Set ↥J) →
      ∀ q ∈ (S : Subgroup ↥J).map J.subtype,
        ((c : ↥J) : G) * q * ((c : ↥J) : G)⁻¹ ∈ (S : Subgroup ↥J).map J.subtype := by
    intro c hc q hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    refine Subgroup.mem_map.mpr ⟨c * y * c⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp hc y).mp hy
  have hact : ∀ c₁ ∈ Subgroup.normalizer ((S : Subgroup ↥J) : Set ↥J),
      ∀ c₂ ∈ Subgroup.normalizer ((S : Subgroup ↥J) : Set ↥J),
      (∀ w ∈ (S : Subgroup ↥J), w ^ p = 1 → c₁ * w * c₁⁻¹ = w) ∨
      (∀ w ∈ (S : Subgroup ↥J), w ^ p = 1 → c₂ * w * c₂⁻¹ = w) ∨
      ∀ w ∈ (S : Subgroup ↥J), w ^ p = 1 → c₁ * w * c₁⁻¹ = c₂ * w * c₂⁻¹ := by
    intro c₁ hc₁ c₂ hc₂
    have h₁ := ggConj_eq_or_of_automizer_zpowers hp2 hBs hBp hSC hN hτ2 hAτ hmapC
      c₁.2 (hmapN c₁ hc₁)
    have h₂ := ggConj_eq_or_of_automizer_zpowers hp2 hBs hBp hSC hN hτ2 hAτ hmapC
      c₂.2 (hmapN c₂ hc₂)
    rcases h₁ with h₁fix | h₁τ
    · refine Or.inl fun w hw hwp => ?_
      refine J.subtype_injective ?_
      have h := h₁fix ((w : ↥J) : G) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
        (by simpa using congrArg Subtype.val hwp)
      simpa using h
    rcases h₂ with h₂fix | h₂τ
    · refine Or.inr (Or.inl fun w hw hwp => ?_)
      refine J.subtype_injective ?_
      have h := h₂fix ((w : ↥J) : G) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
        (by simpa using congrArg Subtype.val hwp)
      simpa using h
    · refine Or.inr (Or.inr fun w hw hwp => ?_)
      refine J.subtype_injective ?_
      have e1 := h₁τ ((w : ↥J) : G) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
        (by simpa using congrArg Subtype.val hwp)
      have e2 := h₂τ ((w : ↥J) : G) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
        (by simpa using congrArg Subtype.val hwp)
      simpa using e1.trans e2.symm
  obtain ⟨U₀, hU₀card, hU₀inv⟩ := ggExists_inv_le_of_isReflection hp2 hBs hBp hτ
  let U : Subgroup ↥J := U₀.comap J.subtype
  have hU : Nat.card U ≤ p := by
    have hinj : Function.Injective (fun x : U => (⟨((x : ↥J) : G), x.2⟩ : U₀)) := by
      intro x y hxy
      have hval : ((x : ↥J) : G) = ((y : ↥J) : G) :=
        congrArg (fun z : U₀ => (z : G)) hxy
      exact Subtype.ext (J.subtype_injective hval)
    exact (Nat.card_le_card_of_injective
      (fun x : U => (⟨((x : ↥J) : G), x.2⟩ : U₀)) hinj).trans hU₀card
  have hUinv : ∀ c ∈ Subgroup.normalizer ((S : Subgroup ↥J) : Set ↥J),
      ∀ w ∈ (S : Subgroup ↥J), w ^ p = 1 → c * w * c⁻¹ = w⁻¹ → w ∈ U := by
    intro c hc w hw hwp hcw
    have hwC := hScent w hw
    have hwBs : ((w : ↥J) : G) ∈ Bs :=
      hSC _ hwC (by simpa using congrArg Subtype.val hwp)
    have hsel := ggConj_eq_or_of_automizer_zpowers hp2 hBs hBp hSC hN hτ2 hAτ hmapC
      c.2 (hmapN c hc)
    rcases hsel with hfix | hτact
    · have hfixG := hfix ((w : ↥J) : G) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
        (by simpa using congrArg Subtype.val hwp)
      have hcwG : ((c : ↥J) : G) * ((w : ↥J) : G) * ((c : ↥J) : G)⁻¹ =
          ((w : ↥J) : G)⁻¹ := by
        simpa using congrArg Subtype.val hcw
      have hwit : ((w : ↥J) : G) = ((w : ↥J) : G)⁻¹ := hfixG.symm.trans hcwG
      have hwG1 : ((w : ↥J) : G) = 1 := by
        have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
        have hp1 : 2 * (p / 2) + 1 = p := by
          have h := Nat.div_two_mul_two_add_one_of_odd hodd
          omega
        have hwpG : ((w : ↥J) : G) ^ p = 1 := by
          simpa using congrArg Subtype.val hwp
        have hsq : ((w : ↥J) : G) ^ 2 = 1 := by
          rw [pow_two]
          nth_rewrite 2 [hwit]
          exact mul_inv_cancel _
        rw [← hp1, pow_succ, pow_mul, hsq, one_pow, one_mul] at hwpG
        exact hwpG
      rw [show w = 1 from J.subtype_injective (by simpa using hwG1)]
      exact Subgroup.mem_comap.mpr (by simp)
    · have hτw : ((τ ⟨((w : ↥J) : G), hwBs⟩ : ↥Bs) : G) = ((w : ↥J) : G)⁻¹ := by
        have e : J.subtype c * J.subtype w * (J.subtype c)⁻¹ =
            ((τ ⟨((w : ↥J) : G), hwBs⟩ : ↥Bs) : G) := by
          simpa using hτact ((w : ↥J) : G) (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
            (by simpa using congrArg Subtype.val hwp)
        have e' : J.subtype c * J.subtype w * (J.subtype c)⁻¹ = (J.subtype w)⁻¹ := by
          rw [← map_mul, ← map_inv, ← map_mul]
          exact congrArg Subtype.val hcw
        rw [e] at e'
        exact e'
      exact Subgroup.mem_comap.mpr (hU₀inv _ hwBs hτw)
  have hScyc : IsCyclic (S : Subgroup ↥J) :=
    CFSG.GroupTheory.isCyclic_sylow_of_omega_central hp2 S hJ hcen hact U hU hUinv
  have : IsCyclic (S : Subgroup ↥J) := hScyc
  have hQKcyc : IsCyclic (Q.subgroupOf J) := by
    have hmap_le : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj gK)) (Q.comap J.subtype) ≤
        (S : Subgroup ↥J) := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      have hqP : q ∈ (P : Subgroup ↥J) := hQKP hq
      have hmem : MulAut.conj gK • q ∈ (S : Subgroup ↥J) := by
        have hScoe : (S : Subgroup ↥J) = ↑(gK • P) := by rw [hSdef]
        rw [hScoe, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul q (MulAut.conj gK) ↑P hqP
      simpa using hmem
    have hcyc : IsCyclic
        (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj gK)) (Q.comap J.subtype)) :=
      isCyclic_of_injective (Subgroup.inclusion hmap_le)
        (Subgroup.inclusion_injective hmap_le)
    exact (MulEquiv.isCyclic ((MulAut.conj gK).subgroupMap (Q.comap J.subtype))).mpr hcyc
  exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hQJ)).mp hQKcyc


theorem GGResHyp.isCyclic_of_le_J_of_oneRefl {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {τ : MulAut ↥Bs} (hτ : GGIsReflection p τ)
    (hA : ggAutomizer J Bs = Subgroup.zpowers τ) {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hQJ : Q ≤ J) : IsCyclic Q :=
  have hBs := hH.1.tableB_facts.2.1
  ggIsCyclic_of_le_of_automizer_refl hH.1.1.2.2.2.2.2.1.2.1 hBs.1 hBs.2 hH.1.2.1.2.2.2
    hH.Bs_le_normalizer_J hH.1.2.2.1.2.2.2.2.2.1.2.2.1 hτ hA hQ hQJ

@[expose] def GGResJOneReflLabelInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGResJOneReflLabel p lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E = p ^ 2 →
        ∃ F : Subgroup R, IsPGroup p F ∧ ¬ IsCyclic F)

theorem ggResJOneReflInput_of_labelInput (hL : GGResJOneReflLabelInput) :
    GGResJOneReflInput := by
  intro G _ _ p _ B Bs x L D J y K hH _ hJ τ hτ hA h2
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hM := largeEvenMarking_and_labelAll_simple (S := fun lab => GGResJOneReflLabel p lab)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsElemAbelian p E → Nat.card E = p ^ 2 → ∃ F : Subgroup R, IsPGroup p F ∧ ¬ IsCyclic F)
    (fun lab hlab hS => hL p hp2 lab hlab hS) (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨hJperf, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, hP'⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨F', hF', hnc⟩ := hP' (ggBeta J θ hBN).range
    (by rintro _ ⟨b, rfl⟩; exact ggBeta_mem J θ hBN h3 b)
    (isElemAbelian_range_ggBeta θ hBs hBN) ((NbrU63.card_range_ggBeta_eq hJperf θ hBN).trans h2)
  obtain ⟨S, hSJ, hSp, hSnc⟩ := exists_noncyclic_of_noncyclic_quot
    (θ.toMonoidHom.comp (QuotientGroup.mk' _))
    (θ.surjective.comp (QuotientGroup.mk'_surjective _)) hF' hnc
  exact hSnc (hH.isCyclic_of_le_J_of_oneRefl hτ hA hSp hSJ)

end CFSG.StandardType

end
