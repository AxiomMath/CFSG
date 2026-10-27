module

public import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace E217R3

@[expose] def OddCube {X : Type*} [Group X] (v : X) : Prop :=
  ∀ g : X, ∀ n : ℕ, Odd n → (v * (g * v * g⁻¹)) ^ n = 1 → (v * (g * v * g⁻¹)) ^ 3 = 1

theorem OddCube.conj {X : Type*} [Group X] {v : X} (h : OddCube v) (k : X) :
    OddCube (k * v * k⁻¹) := by
  intro g n hn hy
  set g' : X := k⁻¹ * g * k with hg'
  have e : (k * v * k⁻¹) * (g * (k * v * k⁻¹) * g⁻¹) =
      k * (v * (g' * v * g'⁻¹)) * k⁻¹ := by
    rw [hg']
    group
  rw [e, conj_pow] at hy ⊢
  have h1 : (v * (g' * v * g'⁻¹)) ^ n = 1 := by
    calc (v * (g' * v * g'⁻¹)) ^ n = k⁻¹ * (k * (v * (g' * v * g'⁻¹)) ^ n * k⁻¹) * k := by group
      _ = 1 := by rw [hy]; group
  rw [h g' n hn h1]
  group

theorem OddCube.map {X Y : Type*} [Group X] [Group Y] {v : X} (h : OddCube v) (θ : X ≃* Y) :
    OddCube (θ v) := by
  intro g' n hn h1
  set g : X := θ.symm g' with hg
  have e : θ v * (g' * θ v * g'⁻¹) = θ (v * (g * v * g⁻¹)) := by
    rw [map_mul, map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply]
  rw [e, ← map_pow] at h1 ⊢
  have h2 : (v * (g * v * g⁻¹)) ^ n = 1 := θ.injective (by rw [h1, map_one])
  rw [h g n hn h2, map_one]

theorem OddCube.of_subgroup {X : Type*} [Group X] {K : Subgroup X} {v : X} (hv : v ∈ K)
    (h : ∀ g ∈ K, ∀ n : ℕ, Odd n → (v * (g * v * g⁻¹)) ^ n = 1 →
      (v * (g * v * g⁻¹)) ^ 3 = 1) : OddCube (⟨v, hv⟩ : ↥K) := by
  intro g n hn h1
  have h1' : (v * ((g : X) * v * (g : X)⁻¹)) ^ n = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  apply Subtype.ext
  have := h g g.2 n hn h1'
  simpa using this

theorem OddCube.of_component {X : Type*} [Group X] {A : Subgroup X} {a b : X} (ha : a ∈ A)
    (hb2 : b * b = 1) (hbA : ∀ g ∈ A, b * g = g * b) (h : OddCube (a * b)) :
    ∀ g ∈ A, ∀ n : ℕ, Odd n → (a * (g * a * g⁻¹)) ^ n = 1 → (a * (g * a * g⁻¹)) ^ 3 = 1 := by
  intro g hg n hn h1
  have e : (a * b) * (g * (a * b) * g⁻¹) = a * (g * a * g⁻¹) := by
    have h1 : b * g = g * b := hbA g hg
    have h2 : b * a = a * b := hbA a ha
    have h3 : b * g⁻¹ = g⁻¹ * b := hbA g⁻¹ (A.inv_mem hg)
    calc (a * b) * (g * (a * b) * g⁻¹) = a * (b * g) * a * (b * g⁻¹) := by group
      _ = a * (g * b) * a * (g⁻¹ * b) := by rw [h1, h3]
      _ = a * g * (b * a) * (g⁻¹ * b) := by group
      _ = a * g * (a * b) * (g⁻¹ * b) := by rw [h2]
      _ = a * g * a * (b * g⁻¹) * b := by group
      _ = a * g * a * (g⁻¹ * b) * b := by rw [h3]
      _ = a * g * a * g⁻¹ * (b * b) := by group
      _ = a * (g * a * g⁻¹) := by rw [hb2]; group
  have := h g n hn (by rw [e]; exact h1)
  rw [e] at this
  exact this

theorem OddCube.pow_three_of_inverted {X : Type*} [Group X] {w c : X} (h : OddCube w)
    (hw : w * w = 1) (hinv : w * c * w⁻¹ = c⁻¹) (hodd : Odd (orderOf c)) : c ^ 3 = 1 := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  rw [hwi] at hinv
  have hy : w * (c * w * c⁻¹) = (c⁻¹) ^ 2 := by
    calc w * (c * w * c⁻¹) = (w * c * w) * c⁻¹ := by group
      _ = (c⁻¹) ^ 2 := by rw [hinv]; group
  have h1 : (w * (c * w * c⁻¹)) ^ orderOf c = 1 := by
    rw [hy, ← pow_mul, mul_comm, pow_mul, inv_pow, pow_orderOf_eq_one]
    group
  have h3 := h c (orderOf c) hodd h1
  rw [hy, ← pow_mul] at h3
  have h6 : c ^ 6 = 1 := by
    have : (c⁻¹) ^ (2 * 3) = 1 := h3
    rw [inv_pow, inv_eq_one] at this
    simpa using this
  have hdvd : orderOf c ∣ 2 * 3 := orderOf_dvd_of_pow_eq_one h6
  have hcop : Nat.Coprime (orderOf c) 2 := (Nat.coprime_two_right.2 hodd)
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_left hdvd)

theorem OddCube.exists_card_cyclic {X : Type*} [Group X] {w : X} (h : OddCube w)
    (hw : w * w = 1) {C : Subgroup X} [Finite C] (hC : IsCyclic C)
    (hinv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹) :
    ∃ s : ℕ, Nat.card C = 2 ^ s ∨ Nat.card C = 2 ^ s * 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have hm : Nat.card C ≠ 0 := Nat.card_pos.ne'
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd hm
  refine ⟨s, ?_⟩
  have hord : orderOf ((g : X) ^ 2 ^ s) = t := by
    have e : ((g : X) ^ 2 ^ s) = ((g ^ 2 ^ s : C) : X) := by simp
    rw [e, Subgroup.orderOf_coe, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      ⟨t, by rw [← hg] at hst; exact hst⟩, hg, hst, Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hcm : ((g : X) ^ 2 ^ s) ∈ C := C.pow_mem g.2 _
  have h3 := h.pow_three_of_inverted hw (hinv _ hcm) (by rw [hord]; exact ht)
  have htd : t ∣ 3 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 htd with h1 | h1
  · left
    rw [hst, h1, mul_one]
  · right
    rw [hst, h1]

theorem eq_two_or_three_of_shape {a : ℕ} (ha : 2 ≤ a) (h1 : ∃ s : ℕ, a = 2 ^ s ∨ a = 2 ^ s * 3)
    (h2 : ∃ s : ℕ, a + 1 = 2 ^ s ∨ a + 1 = 2 ^ s * 3) : a = 2 ∨ a = 3 := by
  have odd_case : ∀ m : ℕ, (∃ s : ℕ, m = 2 ^ s ∨ m = 2 ^ s * 3) → m % 2 = 1 → m = 1 ∨ m = 3 := by
    rintro m ⟨s, hs | hs⟩ hm
    · rcases s with _ | s
      · left
        simpa using hs
      · rw [pow_succ] at hs
        omega
    · rcases s with _ | s
      · right
        simpa using hs
      · rw [pow_succ] at hs
        omega
  rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2
  · have := odd_case (a + 1) h2 (by omega)
    omega
  · have := odd_case a h1 ha2
    omega

variable {F : Type} [Field F]

theorem card_eq_five_or_seven [Finite F] (hF : ringChar F ≠ 2) (hq : 5 ≤ Nat.card F)
    {v : PSL(2, F)} (hv : v ≠ 1) (hv2 : v * v = 1) (h : OddCube v) :
    Nat.card F = 5 ∨ Nat.card F = 7 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    refine ⟨ringChar F, n, hp, ?_, n.pos, by rw [← hcard, hn]⟩
    exact hp.odd_of_ne_two hF
  have hconj : ∀ w : PSL(2, F), w ≠ 1 → w * w = 1 → OddCube w := by
    intro w hw1 hw2
    obtain ⟨k, hk⟩ := CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F hodd v w
      ⟨hv, by rw [pow_two]; exact hv2⟩ ⟨hw1, by rw [pow_two]; exact hw2⟩
    rw [← hk]
    exact h.conj k
  have hT : ∃ s : ℕ, (Fintype.card F - 1) / 2 = 2 ^ s ∨ (Fintype.card F - 1) / 2 = 2 ^ s * 3 := by
    have hw0 : CFSG.PSL2Table.splitWeyl F ≠ 1 := fun h1 => CFSG.PSL2Table.splitWeyl_not_mem
      (h1 ▸ (CFSG.PSL2Table.splitTorus F).one_mem)
    have := (hconj _ hw0 CFSG.PSL2Table.splitWeyl_mul_self).exists_card_cyclic
      CFSG.PSL2Table.splitWeyl_mul_self (C := CFSG.PSL2Table.splitTorus F)
      CFSG.PSL2Table.splitTorus_isCyclic (fun c hc => by
        rw [CFSG.PSL2Table.splitWeyl_conj hc])
    rwa [CFSG.Glauberman.Dickson.MaxStructure.card_splitTorus_eq hF] at this
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  have hS : ∃ s : ℕ, (Fintype.card F + 1) / 2 = 2 ^ s ∨ (Fintype.card F + 1) / 2 = 2 ^ s * 3 := by
    obtain ⟨w, hwS, hww, hinv, -⟩ := CFSG.PSL2Table.exists_nonsplitWeyl hF hν
    have hw1 : w ≠ 1 := fun h1 => hwS (h1 ▸ (CFSG.PSL2Table.nonsplitTorus ν).one_mem)
    have := (hconj w hw1 hww).exists_card_cyclic hww (C := CFSG.PSL2Table.nonsplitTorus ν)
      (CFSG.Glauberman.Dickson.MaxStructure.nonsplitTorus_isCyclic hν) hinv
    rwa [CFSG.Glauberman.Dickson.MaxStructure.card_nonsplitTorus_eq hF hν] at this
  have hodd2 : Fintype.card F % 2 = 1 := by
    rw [hcard]
    rcases hodd with ⟨p, n, hp, hpo, hn, hpn⟩
    rw [hpn]
    exact Nat.odd_iff.1 (hpo.pow)
  have ha : 2 ≤ (Fintype.card F - 1) / 2 := by omega
  have hab : (Fintype.card F - 1) / 2 + 1 = (Fintype.card F + 1) / 2 := by omega
  rw [← hab] at hS
  rcases eq_two_or_three_of_shape ha hT hS with h2 | h2
  · left
    omega
  · right
    omega

end E217R3

end CFSG.Quasithin
