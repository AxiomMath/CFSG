module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSLTwo
import CFSG.Dihedral.Glauberman.DicksonMaxUp

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix

variable {K : Type} [Field K]

@[expose] def uRoot (F₀ : Subfield K) (ρ : K) : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {g | ∃ a ∈ F₀, g = uSL (ρ * a)}
  one_mem' := ⟨0, F₀.zero_mem, by
    rw [mul_zero]
    exact (SpecialLinearGroup.transvection_coeff_zero _).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, F₀.add_mem ha hb, by rw [uSL_mul, mul_add]⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, F₀.neg_mem ha, by rw [mul_neg]; exact SpecialLinearGroup.transvection_inv _ _⟩

theorem card_uRoot (F₀ : Subfield K) {ρ : K} (hρ : ρ ≠ 0) :
    Nat.card (uRoot F₀ ρ) = Nat.card F₀ := by
  refine (Nat.card_congr (Equiv.ofBijective (fun a : F₀ => (⟨uSL (ρ * a), a, a.2, rfl⟩ :
    uRoot F₀ ρ)) ⟨?_, ?_⟩)).symm
  · intro a b hab
    have h0 : uSL (ρ * a) = uSL (ρ * b) := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel₀ hρ (uSL_injective h0))
  · rintro ⟨g, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem exists_odd_card_eq [Finite K] [CharP K 2] (F₀ : Subfield K) {ρ : K} (hρ : ρ ≠ 0)
    {n : ℕ} (hF₀ : Nat.card F₀ = 2 ^ n) (G : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hu : uRoot F₀ ρ ≤ G) (hU : ∀ x, uSL x ∈ G → ∃ a ∈ F₀, x = ρ * a) :
    ∃ m, Odd m ∧ Nat.card G = 2 ^ n * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R' := (uRoot F₀ ρ).subgroupOf G with hR'
  have hR'card : Nat.card R' = 2 ^ n := by
    rw [hR', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hu).toEquiv, card_uRoot F₀ hρ, hF₀]
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hR'card).exists_le_sylow
  have hρmem : uSL ρ ∈ uRoot F₀ ρ := ⟨1, F₀.one_mem, by rw [mul_one]⟩
  have hρ1 : uSL ρ ≠ 1 := by
    intro h1
    apply hρ
    apply uSL_injective
    rw [h1]
    exact (SpecialLinearGroup.transvection_coeff_zero _).symm
  set Q := (P : Subgroup G).map G.subtype with hQ
  have hQ2 : IsPGroup 2 Q := P.isPGroup'.map _
  have hρQ : uSL ρ ∈ Q :=
    ⟨⟨uSL ρ, hu hρmem⟩, hP (Subgroup.mem_subgroupOf.mpr hρmem), rfl⟩
  have hQG : Q ≤ G := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQle : Q ≤ uRoot F₀ ρ := by
    have : Nontrivial Q := ⟨⟨⟨uSL ρ, hρQ⟩, 1, fun h => hρ1 (congrArg Subtype.val h)⟩⟩
    have := hQ2.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center Q)
    have hzc := Subgroup.mem_center_iff.mp z.2 ⟨uSL ρ, hρQ⟩
    have hzc' : ((z : Q) : SpecialLinearGroup (Fin 2) K) * uSL ρ =
        uSL ρ * ((z : Q) : SpecialLinearGroup (Fin 2) K) := (congrArg Subtype.val hzc).symm
    obtain ⟨b, hb⟩ := exists_eq_uSL_of_commute hρ hzc'
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply hz
      apply Subtype.ext
      apply Subtype.ext
      rw [hb]
      exact SpecialLinearGroup.transvection_coeff_zero _
    intro x hx
    have hxc := Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩
    have hxc' : x * uSL b = uSL b * x := by
      have := congrArg Subtype.val hxc
      rw [← hb]
      exact this
    obtain ⟨b', rfl⟩ := exists_eq_uSL_of_commute hb0 hxc'
    obtain ⟨a, ha, hab⟩ := hU b' (hQG hx)
    exact ⟨a, ha, by rw [hab]⟩
  have hPR : (P : Subgroup G) = R' := by
    refine le_antisymm (fun g hg => ?_) hP
    rw [hR', Subgroup.mem_subgroupOf]
    exact hQle ⟨g, hg, rfl⟩
  refine ⟨(P : Subgroup G).index, ?_, ?_⟩
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (P.not_dvd_index))
  · rw [← Subgroup.card_mul_index (P : Subgroup G), hPR, hR'card]

theorem card_sup_eq_mul_of_disjoint {X : Type*} [Group X] [Finite X] (N C : Subgroup X)
    [N.Normal] (hd : Disjoint N C) : Nat.card ↥(N ⊔ C) = Nat.card N * Nat.card C := by
  have h1 := Subgroup.relIndex_sup_right C N
  have h2 := Subgroup.relIndex_mul_card N (C ⊔ N)
  have h3 := Subgroup.relIndex_mul_card N C
  rw [inf_eq_left.2 (le_sup_right : N ≤ C ⊔ N), h1] at h2
  have hbot : N ⊓ C = ⊥ := disjoint_iff.mp hd
  rw [hbot, Subgroup.card_bot, mul_one] at h3
  rw [sup_comm, ← h2, ← h3, mul_comm]

theorem card_dvd_of_dickson [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (G : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hG : ¬ ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card G = 2 ^ n * m) : Nat.card G ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K)) with hφdef
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφdef, QuotientGroup.ker_mk', center_slTwo_eq_bot]
  set H := G.map φ with hH
  have hHG : Nat.card H = Nat.card G := Subgroup.card_map_of_injective hφ
  have hHnc : ¬ IsMulCommutative H := by
    intro hc
    apply hG
    intro x hx y hy
    have := hc.is_comm.comm ⟨φ x, Subgroup.mem_map_of_mem φ hx⟩ ⟨φ y, Subgroup.mem_map_of_mem φ hy⟩
    apply hφ
    simpa using congrArg Subtype.val this
  have hcardH : Nat.card H = 2 ^ n * m := hHG.trans hcard
  have hq1 : 1 ≤ f := hf
  rw [← hHG]
  have hodd3 : Odd (2 ^ f - 1) := odd_two_pow_sub_one hq1
  have hg : Nat.gcd (2 ^ f - 1) 2 = 1 := Nat.Coprime.gcd_eq_one
    (Nat.coprime_two_right.mpr hodd3)
  have hdvdq : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
    have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show (2 ^ n) ^ 2 - 1 = (2 ^ n) ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    rw [e]
    exact Dvd.intro_left _ rfl
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hzc, -⟩ | ⟨-, ⟨e4⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨e5⟩⟩ |
      ⟨k, t, htk, -, N, C, hNn, -, hNc, hCcyc, hCc, hdisj, hsup⟩ | ⟨k, hk, -, ⟨e⟩⟩ |
      ⟨k, hk, -, ⟨e⟩⟩
  · exact absurd hEl.toIsMulCommutative hHnc
  · exact absurd ⟨⟨fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b⟩⟩ hHnc
  ·
    exfalso
    rw [hK, hg, Nat.div_one, Nat.div_one] at hz
    have hzodd : Odd z := by
      rcases hz with hz | hz
      · exact Odd.of_dvd_nat hodd3 hz
      · exact Odd.of_dvd_nat (odd_two_pow_add_one hq1) hz
    have := two_pow_mul_odd_inj hm hzodd (hcardH.symm.trans (by rw [hzc, pow_one]))
    omega
  ·
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr e4.toEquiv, nat_card_alternatingGroup]
      simp
      decide
    obtain ⟨h1, -⟩ := two_pow_mul_odd_inj hm (by decide : Odd 3)
      (hcardH.symm.trans (by rw [h12]; norm_num : Nat.card H = 2 ^ 2 * 3))
    subst h1
    rw [h12]
    norm_num
  ·
    exfalso
    have hodd : Odd (2 ^ (2 * f) - 1) := odd_two_pow_sub_one (by omega)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 16).trans h16))
  ·
    have h60 : Nat.card H = 60 := by
      rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup]
      simp
      decide
    obtain ⟨h1, -⟩ := two_pow_mul_odd_inj hm (by decide : Odd 15)
      (hcardH.symm.trans (by rw [h60]; norm_num : Nat.card H = 2 ^ 2 * 15))
    subst h1
    rw [h60]
    norm_num
  ·
    have hNC : Nat.card H = 2 ^ k * t := by
      rw [← hNc, ← hCc, ← card_sup_eq_mul_of_disjoint N C hdisj, hsup, Subgroup.card_top]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    ·
      exfalso
      have hN1 : N = ⊥ := by
        rw [← Subgroup.card_eq_one, hNc, pow_zero]
      rw [hN1, bot_sup_eq] at hsup
      rw [hsup] at hCcyc
      have : IsCyclic H := isCyclic_of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom (MulEquiv.surjective _)
      exact hHnc ⟨⟨fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b⟩⟩
    · have htodd : Odd t := Odd.of_dvd_nat (odd_two_pow_sub_one hkpos) htk
      obtain ⟨rfl, rfl⟩ := two_pow_mul_odd_inj hm htodd (hcardH.symm.trans hNC)
      rw [hcardH]
      exact Nat.mul_dvd_mul_left _ (htk.trans hdvdq)
  ·
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hcard' : Nat.card H = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_psl2_charTwo, GaloisField.card 2 k hk]
    have hodd : Odd ((2 ^ k) ^ 2 - 1) := by
      rw [← pow_mul]
      exact odd_two_pow_sub_one (by omega)
    obtain ⟨rfl, -⟩ := two_pow_mul_odd_inj hm hodd (hcardH.symm.trans hcard')
    rw [hcard']
  ·
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hcard' : Nat.card H = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hk,
        ← pow_mul, mul_comm k 2]
    have hodd : Odd ((2 ^ k) ^ 2 - 1) := by
      rw [← pow_mul]
      exact odd_two_pow_sub_one (by omega)
    obtain ⟨rfl, -⟩ := two_pow_mul_odd_inj hm hodd (hcardH.symm.trans hcard')
    rw [hcard']

theorem mul_pow_of_rootGroups [Finite K] [CharP K 2]
    (F₀ : Subfield K) {n : ℕ} (hn : 2 ≤ n) (hF₀ : Nat.card F₀ = 2 ^ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {ρ μ : K} (hρ : ρ ≠ 0) (hμ : μ ≠ 0)
    (G : Subgroup (SpecialLinearGroup (Fin 2) K)) (hu : ∀ a ∈ F₀, uSL (ρ * a) ∈ G)
    (hl : ∀ b ∈ F₀, lSL (μ * b) ∈ G) (hU : ∀ x, uSL x ∈ G → ∃ a ∈ F₀, x = ρ * a) :
    (ρ * μ) ^ (2 ^ (2 * n)) = ρ * μ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have huR : uRoot F₀ ρ ≤ G := by
    rintro _ ⟨a, ha, rfl⟩
    exact hu a ha
  obtain ⟨m, hm, hcard⟩ := exists_odd_card_eq F₀ hρ hF₀ G huR hU
  set g : SpecialLinearGroup (Fin 2) K := uSL ρ * lSL μ with hg
  have hgG : g ∈ G := G.mul_mem (by simpa using hu 1 F₀.one_mem) (by simpa using hl 1 F₀.one_mem)
  have hgM : (g : Matrix (Fin 2) (Fin 2) K) = !![1, ρ; 0, 1] * !![1, 0; μ, 1] := by
    rw [← uSL_coe, ← lSL_coe]
    rfl
  have htr : (g : Matrix (Fin 2) (Fin 2) K) 0 0 + (g : Matrix (Fin 2) (Fin 2) K) 1 1 = ρ * μ := by
    rw [hgM]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h2
  have hnc : ¬ ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro hc
    have h1 := hc _ (by simpa using hu 1 F₀.one_mem) _ (by simpa using hl 1 F₀.one_mem)
    have h00 := congrFun (congrFun (congrArg
      (fun X : SpecialLinearGroup (Fin 2) K => (X : Matrix (Fin 2) (Fin 2) K)) h1) 0) 0
    have e1 : ((uSL ρ * lSL μ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        !![1, ρ; 0, 1] * !![1, 0; μ, 1] := by
      rw [← uSL_coe, ← lSL_coe]
      rfl
    have e2 : ((lSL μ * uSL ρ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        !![1, 0; μ, 1] * !![1, ρ; 0, 1] := by
      rw [← uSL_coe, ← lSL_coe]
      rfl
    rw [e1, e2] at h00
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
    exact hρ (by simpa [hμ] using h00)
  have hdvd := card_dvd_of_dickson hn hf hK G hnc hm hcard
  have hodd : Odd (orderOf g) := odd_orderOf_of_trace_ne_zero (by rw [htr]; exact mul_ne_zero hρ hμ)
  have hord : orderOf g ∣ (2 ^ n) ^ 2 - 1 := by
    have h1 : orderOf g ∣ Nat.card G := by
      rw [← Subgroup.orderOf_mk g hgG]
      exact orderOf_dvd_natCard _
    have h2' : orderOf g ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := h1.trans hdvd
    have hcop : Nat.Coprime (orderOf g) (2 ^ n) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    exact hcop.dvd_of_dvd_mul_left h2'
  have hgq : g ^ (2 ^ (2 * n)) = g := by
    obtain ⟨c, hc⟩ := hord
    have hpos : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have e : 2 ^ (2 * n) = ((2 ^ n) ^ 2 - 1) + 1 := by rw [mul_comm, pow_mul]; omega
    rw [e, pow_succ, hc, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
  have htq := trace_pow_two_pow_eq hgq
  rw [htr] at htq
  exact htq

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
