module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleDep
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleOrder
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleGramExtract
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleEmbed
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.StandardType.CoxTriple

open CFSG.LieType.RootSystem

private theorem ct_rt_conj_pow_two {G : Type*} [Group G] {g s : G} (hs : s ^ 2 = 1) :
    (g * s * g⁻¹) ^ 2 = 1 := by
  rw [conj_pow, hs]
  group

private theorem ct_rt_conj_mul_self {G : Type*} [Group G] {g s : G} (hs : s ^ 2 = 1) :
    (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
  rw [← pow_two]
  exact ct_rt_conj_pow_two hs

private theorem ct_rt_card_closure_pair_dvd {G : Type*} [Group G] {s t : G} {n : ℕ}
    (hs : s * s = 1) (ht : t * t = 1) (hn : orderOf (s * t) = n) :
    Nat.card (Subgroup.closure ({s, t} : Set G)) ∣ 2 * n := by
  let f : DihedralGroup n →* G := TauCeti.dihedralHom hs ht hn
  have hrange : f.range = Subgroup.closure ({s, t} : Set G) :=
    TauCeti.range_dihedralHom hs ht hn
  rw [← hrange]
  calc Nat.card ↥f.range
      = Nat.card (DihedralGroup n ⧸ f.ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
    _ ∣ Nat.card (DihedralGroup n) := Subgroup.card_quotient_dvd_card _
    _ = 2 * n := DihedralGroup.nat_card

private theorem ct_rt_card_sup_of_central {G : Type*} [Group G] {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) :
    Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q := by
  have hdecomp : ∀ y ∈ P ⊔ Q, ∃ p ∈ P, ∃ q ∈ Q, p * q = y := by
    intro y hy
    rw [Subgroup.sup_eq_closure] at hy
    refine Subgroup.closure_induction (p := fun z _ => ∃ p ∈ P, ∃ q ∈ Q, p * q = z)
      ?_ ?_ ?_ ?_ hy
    · intro x hx
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, Subgroup.one_mem Q, by rw [mul_one]⟩
      · exact ⟨1, Subgroup.one_mem P, x, hx, by rw [one_mul]⟩
    · exact ⟨1, Subgroup.one_mem P, 1, Subgroup.one_mem Q, by rw [mul_one]⟩
    · rintro x y _ _ ⟨p1, hp1, q1, hq1, rfl⟩ ⟨p2, hp2, q2, hq2, rfl⟩
      refine ⟨p1 * p2, Subgroup.mul_mem P hp1 hp2, q1 * q2, Subgroup.mul_mem Q hq1 hq2, ?_⟩
      calc (p1 * p2) * (q1 * q2) = p1 * (p2 * q1) * q2 := by group
        _ = p1 * (q1 * p2) * q2 := by rw [hcomm p2 hp2 q1 hq1]
        _ = p1 * q1 * (p2 * q2) := by group
    · rintro x _ ⟨p, hp, q, hq, rfl⟩
      refine ⟨p⁻¹, Subgroup.inv_mem P hp, q⁻¹, Subgroup.inv_mem Q hq, ?_⟩
      rw [hcomm p⁻¹ (Subgroup.inv_mem P hp) q⁻¹ (Subgroup.inv_mem Q hq), mul_inv_rev]
  let e : ↥P × ↥Q ≃ ↥(P ⊔ Q) :=
    Equiv.ofBijective
      (fun x : ↥P × ↥Q => (⟨x.1.1 * x.2.1, Subgroup.mul_mem (P ⊔ Q)
        (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩ : ↥(P ⊔ Q)))
      ⟨by
        rintro ⟨p1, q1⟩ ⟨p2, q2⟩ hh
        have hh' : p1.1 * q1.1 = p2.1 * q2.1 := by simpa using congrArg Subtype.val hh
        have h1 : (p2.1)⁻¹ * p1.1 = q2.1 * (q1.1)⁻¹ := by
          have := congrArg (fun z => (p2.1)⁻¹ * z * (q1.1)⁻¹) hh'
          simpa [mul_assoc] using this
        have hmemP : (p2.1)⁻¹ * p1.1 ∈ P :=
          Subgroup.mul_mem P (Subgroup.inv_mem P p2.2) p1.2
        have hmemQ : q2.1 * (q1.1)⁻¹ ∈ Q :=
          Subgroup.mul_mem Q q2.2 (Subgroup.inv_mem Q q1.2)
        have hbot : (p2.1)⁻¹ * p1.1 ∈ P ⊓ Q := ⟨hmemP, by rw [h1]; exact hmemQ⟩
        rw [hdisj, Subgroup.mem_bot] at hbot
        have hp : p1.1 = p2.1 := by
          calc p1.1 = p2.1 * ((p2.1)⁻¹ * p1.1) := by group
            _ = p2.1 * 1 := by rw [hbot]
            _ = p2.1 := mul_one _
        have hq : q1.1 = q2.1 :=
          mul_left_cancel (a := p2.1) (by simpa [hp] using hh')
        exact Prod.ext (Subtype.ext hp) (Subtype.ext hq), by
        intro y
        obtain ⟨p, hp, q, hq, hpq⟩ := hdecomp y.1 y.2
        exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), Subtype.ext hpq⟩⟩
  have he : Nat.card (↥P × ↥Q) = Nat.card ↥(P ⊔ Q) := Nat.card_congr e
  rw [Nat.card_prod] at he
  exact he.symm

theorem coxTriple_card_dvd_48
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (hord : ∀ (i j : I) (g h : (coxeterMatrix hC).Group),
      orderOf (g * (coxeterMatrix hC).simple i * g⁻¹ * (h * (coxeterMatrix hC).simple j * h⁻¹)) ≤ 4)
    (i₁ i₂ i₃ : I) (g₁ g₂ g₃ : (coxeterMatrix hC).Group)
    (h3 : orderOf (g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹ * (g₂ * (coxeterMatrix hC).simple i₂ * g₂⁻¹)) = 3) :
    Nat.card (Subgroup.closure ({g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹,
      g₂ * (coxeterMatrix hC).simple i₂ * g₂⁻¹, g₃ * (coxeterMatrix hC).simple i₃ * g₃⁻¹} :
        Set (coxeterMatrix hC).Group)) ∣ 48 := by
  let g : Fin 3 → (coxeterMatrix hC).Group := ![g₁, g₂, g₃]
  let i : Fin 3 → I := ![i₁, i₂, i₃]
  let T1 : (coxeterMatrix hC).Group := g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹
  let T2 : (coxeterMatrix hC).Group := g₂ * (coxeterMatrix hC).simple i₂ * g₂⁻¹
  let T3 : (coxeterMatrix hC).Group := g₃ * (coxeterMatrix hC).simple i₃ * g₃⁻¹
  change Nat.card (Subgroup.closure ({T1, T2, T3} : Set (coxeterMatrix hC).Group)) ∣ 48
  have hsq1 : (coxeterMatrix hC).simple i₁ ^ 2 = 1 := by
    simpa using CoxeterSystem.simple_sq (coxeterMatrix hC).toCoxeterSystem i₁
  have hsq2 : (coxeterMatrix hC).simple i₂ ^ 2 = 1 := by
    simpa using CoxeterSystem.simple_sq (coxeterMatrix hC).toCoxeterSystem i₂
  have hsq3 : (coxeterMatrix hC).simple i₃ ^ 2 = 1 := by
    simpa using CoxeterSystem.simple_sq (coxeterMatrix hC).toCoxeterSystem i₃
  have hT1p : T1 ^ 2 = 1 := by simpa [T1] using ct_rt_conj_pow_two (g := g₁) hsq1
  have hT2p : T2 ^ 2 = 1 := by simpa [T2] using ct_rt_conj_pow_two (g := g₂) hsq2
  have hT3p : T3 ^ 2 = 1 := by simpa [T3] using ct_rt_conj_pow_two (g := g₃) hsq3
  have hT1m : T1 * T1 = 1 := by simpa [T1] using ct_rt_conj_mul_self (g := g₁) hsq1
  have hT2m : T2 * T2 = 1 := by simpa [T2] using ct_rt_conj_mul_self (g := g₂) hsq2
  have hT3m : T3 * T3 = 1 := by simpa [T3] using ct_rt_conj_mul_self (g := g₃) hsq3
  have h3' : orderOf (T1 * T2) = 3 := by simpa [T1, T2] using h3
  have ht0 : T1 = coxRefl hC (g 0) (i 0) := by simp [T1, coxRefl, g, i]
  have ht1 : T2 = coxRefl hC (g 1) (i 1) := by simp [T2, coxRefl, g, i]
  have ht2 : T3 = coxRefl hC (g 2) (i 2) := by simp [T3, coxRefl, g, i]
  have h3c : orderOf (coxRefl hC (g 0) (i 0) * coxRefl hC (g 1) (i 1)) = 3 := by
    rw [← ht0, ← ht1]; exact h3'
  let P : Subgroup (coxeterMatrix hC).Group := Subgroup.closure ({T1, T2} : Set _)
  let Q : Subgroup (coxeterMatrix hC).Group := Subgroup.zpowers T3
  have hPcard : Nat.card ↥P ∣ 6 := by
    have h := ct_rt_card_closure_pair_dvd (s := T1) (t := T2) (n := 3) hT1m hT2m h3'
    simpa [P] using h
  have hQcard : Nat.card ↥Q ∣ 2 := by
    have h := ct_rt_card_closure_pair_dvd (s := T3) (t := T3) (n := 1) hT3m hT3m
      (by rw [hT3m]; exact orderOf_one)
    simpa [Q, Subgroup.zpowers_eq_closure, Set.pair_eq_singleton] using h
  have hHP : T3 ∈ P → Subgroup.closure ({T1, T2, T3} : Set (coxeterMatrix hC).Group) = P := by
    intro hmem3
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact hmem3
    · apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
  by_cases hdep : ∃ x y : ℚ, toRat (coxRoot hC (g 2) (i 2)) =
      x • toRat (coxRoot hC (g 0) (i 0)) + y • toRat (coxRoot hC (g 1) (i 1))
  ·
    have hmem3 : T3 ∈ P := by
      have h := coxTriple_dep hC hord i₁ i₂ i₃ g₁ g₂ g₃ h3 hdep
      simpa [P, T1, T2, T3] using h
    rw [hHP hmem3]
    exact dvd_trans hPcard (by norm_num)
  · by_cases hcomm : Commute T3 T1 ∧ Commute T3 T2
    ·
      by_cases hmem3 : T3 ∈ P
      · rw [hHP hmem3]
        exact dvd_trans hPcard (by norm_num)
      · have hT3_ne : T3 ≠ 1 := fun h => hmem3 (by rw [h]; exact Subgroup.one_mem P)
        have hQ2 : orderOf T3 = 2 := orderOf_eq_prime hT3p hT3_ne
        have hcommP : ∀ p ∈ P, Commute p T3 := by
          intro p hp
          dsimp only [P] at hp
          refine Subgroup.closure_induction (p := fun x _ => Commute x T3) ?_ ?_ ?_ ?_ hp
          · intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl
            · exact hcomm.1.symm
            · exact hcomm.2.symm
          · exact Commute.one_left T3
          · intro x y _ _ hx hy
            exact Commute.mul_left hx hy
          · intro x _ hx
            exact hx.inv_left
        have hcomm' : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := by
          intro p hp q hq
          change q ∈ Subgroup.zpowers T3 at hq
          rw [Subgroup.mem_zpowers_iff] at hq
          obtain ⟨n, rfl⟩ := hq
          exact ((hcommP p hp).zpow_right n).eq
        have hPQbot : P ⊓ Q = ⊥ := by
          apply le_antisymm _ bot_le
          intro x hx
          obtain ⟨hxP, hxQ⟩ := hx
          change x ∈ Subgroup.zpowers T3 at hxQ
          rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two hQ2] at hxQ
          rcases hxQ with rfl | rfl
          · exact Subgroup.mem_bot.mpr rfl
          · exact absurd hxP hmem3
        have hHPQ : Subgroup.closure ({T1, T2, T3} : Set (coxeterMatrix hC).Group) = P ⊔ Q := by
          have hset : ({T1, T2, T3} : Set (coxeterMatrix hC).Group) = {T1, T2} ∪ {T3} := by
            ext x
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
            tauto
          rw [hset, Subgroup.closure_union]
          dsimp only [P, Q]
          rw [Subgroup.zpowers_eq_closure]
        rw [hHPQ, ct_rt_card_sup_of_central hcomm' hPQbot]
        exact dvd_trans (by simpa using Nat.mul_dvd_mul hPcard hQcard) (by norm_num)
    ·
      have hnc : ¬ (Commute (coxRefl hC (g 2) (i 2)) (coxRefl hC (g 0) (i 0)) ∧
          Commute (coxRefl hC (g 2) (i 2)) (coxRefl hC (g 1) (i 1))) := by
        intro hc
        refine hcomm ⟨?_, ?_⟩
        · rw [ht2, ht0]; exact hc.1
        · rw [ht2, ht1]; exact hc.2
      obtain ⟨N, c, ε, hc, hε, hN, hgram⟩ :=
        coxTriple_gram_extract hC hord g i h3c hdep hnc
      have hemb := coxTriple_embed hC g i N c ε hc hε hN hgram
      rw [show Subgroup.closure ({T1, T2, T3} : Set (coxeterMatrix hC).Group) =
          Subgroup.closure ({coxRefl hC (g 0) (i 0), coxRefl hC (g 1) (i 1),
            coxRefl hC (g 2) (i 2)} : Set (coxeterMatrix hC).Group) by rw [ht0, ht1, ht2],
        hemb]
      exact card_gramReflGroup_dvd_48 hN

end CFSG.StandardType.CoxTriple

end
