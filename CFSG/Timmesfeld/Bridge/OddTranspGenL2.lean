module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.Timmesfeld.Bridge.OddTransp

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

@[expose] def InvolutionThreeGen (K : Type*) [Group K] : Prop :=
  ∀ t₁ t₂ : K, orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ → Commute t₁ t₂ →
    ∃ t₃ : K, orderOf t₃ = 2 ∧ Subgroup.closure {t₁, t₂, t₃} = ⊤

theorem InvolutionThreeGen.of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : InvolutionThreeGen L) : InvolutionThreeGen K := by
  intro t₁ t₂ h₁ h₂ hne hc
  obtain ⟨t₃, h₃, hgen⟩ := h (e t₁) (e t₂) (by rw [MulEquiv.orderOf_eq]; exact h₁)
    (by rw [MulEquiv.orderOf_eq]; exact h₂) (e.injective.ne hne) (hc.map e)
  refine ⟨e.symm t₃, by rw [MulEquiv.orderOf_eq]; exact h₃, ?_⟩
  have h1 := congrArg (Subgroup.map e.symm.toMonoidHom) hgen
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
  rw [← h1, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  simp

theorem four_dvd_card_of_commute {K : Type*} [Group K] [Finite K] {H : Subgroup K} {t₁ t₂ : K}
    (h₁ : t₁ * t₁ = 1) (h₂ : t₂ * t₂ = 1) (h₁' : t₁ ≠ 1) (h₂' : t₂ ≠ 1) (hne : t₁ ≠ t₂)
    (hc : Commute t₁ t₂) (ht₁ : t₁ ∈ H) (ht₂ : t₂ ∈ H) : 4 ∣ Nat.card H := by
  have hc' : t₂ * t₁ = t₁ * t₂ := hc.eq.symm
  have hl₁ : ∀ x : K, t₁ * (t₁ * x) = x := fun x => by rw [← mul_assoc, h₁, one_mul]
  have hc'' : ∀ x : K, t₂ * (t₁ * x) = t₁ * (t₂ * x) := fun x => by
    rw [← mul_assoc, hc', mul_assoc]
  have hi₁ : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right h₁
  have hi₂ : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right h₂
  let V : Subgroup K :=
    { carrier := {1, t₁, t₂, t₁ * t₂}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp [mul_assoc, h₁, h₂, hl₁, hc', hc'']
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp [hi₁, hi₂, hc'] }
  have hVH : V ≤ H := by
    intro x hx
    change x ∈ ({1, t₁, t₂, t₁ * t₂} : Set K) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact ht₁
    · exact ht₂
    · exact H.mul_mem ht₁ ht₂
  have hV : Nat.card V = 4 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    change ({1, t₁, t₂, t₁ * t₂} : Set K).ncard = 4
    have h12 : t₂ ≠ t₁ * t₂ := fun h => h₁' (by simpa using congrArg (· * t₂⁻¹) h.symm)
    have h1 : t₁ ∉ ({t₂, t₁ * t₂} : Set K) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, fun h => h₂' (by simpa using congrArg (t₁⁻¹ * ·) h.symm)⟩
    have h0 : (1 : K) ∉ ({t₁, t₂, t₁ * t₂} : Set K) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨Ne.symm h₁', Ne.symm h₂', fun h => hne ?_⟩
      rw [eq_inv_of_mul_eq_one_left h.symm, hi₂]
    rw [Set.ncard_insert_of_notMem h0, Set.ncard_insert_of_notMem h1, Set.ncard_pair h12]
  exact hV ▸ Subgroup.card_dvd_of_le hVH

theorem card_psl2Model {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (PSL2Model m) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have hKcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hneg_one : (-1 : GaloisField 2 m) = 1 := CharTwo.neg_eq 1
  have hcenter := huppert614_card_center_of_neg_one_eq_one hneg_one
  have hPSLcard := huppert614_card_psl_mul_center (K := GaloisField 2 m)
  rw [hcenter, mul_one, hKcard] at hPSLcard
  exact hPSLcard

theorem eq_two_of_two_pow_add_one_dvd {m N : ℕ} (hm : 2 ≤ m) (hN : N = 12 ∨ N = 24 ∨ N = 60)
    (h : 2 ^ m + 1 ∣ N) : m = 2 ∧ N = 60 := by
  have hle : 2 ^ m + 1 ≤ 60 := (Nat.le_of_dvd (by omega) h).trans (by omega)
  have hm6 : m < 6 := by
    by_contra hcon
    have : 2 ^ 6 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m <;> rcases hN with rfl | rfl | rfl
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem involutionThreeGen_psl2 {m : ℕ} (hm : 2 ≤ m) : InvolutionThreeGen (PSL2Model m) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hq4 : 4 ≤ 2 ^ m := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hev : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  have hodd₁ : Odd (2 ^ m - 1) := Nat.Even.sub_odd (by omega) hev odd_one
  have hodd₂ : Odd (2 ^ m + 1) := hev.add_one
  have hgcd₁ : Nat.gcd (2 ^ m - 1) 2 = 1 := Nat.coprime_two_right.mpr hodd₁
  have hgcd₂ : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr hodd₁
  have hcop : ∀ k : ℕ, Nat.Coprime (2 ^ m + 1) (2 ^ k) := fun k =>
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd₂)
  intro t₁ t₂ h₁ h₂ hne hc
  have ht₁ : t₁ * t₁ = 1 := by
    have := pow_orderOf_eq_one t₁
    rwa [h₁, pow_two] at this
  have ht₂ : t₂ * t₂ = 1 := by
    have := pow_orderOf_eq_one t₂
    rwa [h₂, pow_two] at this
  have ht₁' : t₁ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at h₁
    omega
  have ht₂' : t₂ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at h₂
    omega
  obtain ⟨T, w, hTcyc, hTcard, -, hwT, hw2, hwinv, -, -⟩ :=
    huppert_II_8_4_nonsplit_torus_reflection_data hF
  rw [hF, hgcd₁, Nat.div_one] at hTcard
  have : IsCyclic T := hTcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  have hgo : orderOf (g : PSL2Model m) = 2 ^ m + 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hTcard]
  have hw1 : w ≠ 1 := fun h1 => hwT (h1 ▸ T.one_mem)
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwg : w * (g : PSL2Model m) * w = (g : PSL2Model m)⁻¹ := by
    have := hwinv g g.2
    rwa [hwi] at this
  have hwg2 : w * (g : PSL2Model m) * (w * (g : PSL2Model m)) = 1 := by
    rw [← mul_assoc, hwg, inv_mul_cancel]
  have hwg1 : w * (g : PSL2Model m) ≠ 1 := by
    intro h1
    apply hwT
    rw [eq_inv_of_mul_eq_one_left h1]
    exact T.inv_mem g.2
  have hB : IsBenderGroup (PSL2Model m) := .isPSL2 m hm (MulEquiv.refl _)
  obtain ⟨c, hcw⟩ := isConj_iff.mp (Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hB hwo h₁)
  set t₃ := c * (w * (g : PSL2Model m)) * c⁻¹ with ht₃def
  have ht₃2 : t₃ * t₃ = 1 := by
    rw [ht₃def, show c * (w * (g : PSL2Model m)) * c⁻¹ * (c * (w * (g : PSL2Model m)) * c⁻¹) =
      c * (w * (g : PSL2Model m) * (w * (g : PSL2Model m))) * c⁻¹ by group, hwg2, mul_one,
      mul_inv_cancel]
  have ht₃1 : t₃ ≠ 1 := by
    intro h1
    apply hwg1
    have h2 : c⁻¹ * t₃ * c = 1 := by rw [h1]; group
    rw [ht₃def] at h2
    simpa [mul_assoc] using h2
  have hord₃ : orderOf t₃ = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht₃2) ht₃1
  refine ⟨t₃, hord₃, ?_⟩
  have h13 : t₁ * t₃ = c * (g : PSL2Model m) * c⁻¹ := by
    rw [ht₃def, ← hcw]
    calc c * w * c⁻¹ * (c * (w * (g : PSL2Model m)) * c⁻¹) =
        c * (w * w) * (g : PSL2Model m) * c⁻¹ := by group
      _ = c * (g : PSL2Model m) * c⁻¹ := by rw [hw2, mul_one]
  have h13o : orderOf (t₁ * t₃) = 2 ^ m + 1 := by
    rw [h13, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hgo]
  set H := Subgroup.closure ({t₁, t₂, t₃} : Set (PSL2Model m)) with hHdef
  have hm₁ : t₁ ∈ H := Subgroup.subset_closure (by simp)
  have hm₂ : t₂ ∈ H := Subgroup.subset_closure (by simp)
  have hm₃ : t₃ ∈ H := Subgroup.subset_closure (by simp)
  have h4 : 4 ∣ Nat.card H := four_dvd_card_of_commute ht₁ ht₂ ht₁' ht₂' hne hc hm₁ hm₂
  set x : H := ⟨t₁ * t₃, H.mul_mem hm₁ hm₃⟩ with hxdef
  have hxo : orderOf x = 2 ^ m + 1 := by rw [hxdef, Subgroup.orderOf_mk, h13o]
  have hq1 : 2 ^ m + 1 ∣ Nat.card H := hxo ▸ orderOf_dvd_natCard x
  by_contra hHtop
  have hcardH : Nat.card H ≠ Nat.card (PSL2Model m) := fun h =>
    hHtop (Subgroup.eq_top_of_card_eq H h)
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF H with
    ⟨k, -, hcard, -⟩ | ⟨z, hz, hcard, -⟩ | ⟨z, -, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨k, t, -, -, -, ht, E, C, -, -, hE, -, hC, -, -, -, φ, -, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩ |
      ⟨k, hk, ⟨e⟩⟩
  ·
    rw [hcard] at hq1
    have := (hcop k).eq_one_of_dvd hq1
    omega
  ·
    simp only [hgcd₂, Nat.div_one] at hz
    have hzodd : Odd z := by
      rcases hz with hz | hz
      · exact hodd₂.of_dvd_nat hz
      · exact hodd₁.of_dvd_nat hz
    rw [hcard] at h4
    obtain ⟨j, rfl⟩ := hzodd
    omega
  ·
    simp only [hgcd₂, Nat.div_one] at hz
    have hzodd : Odd z := by
      rcases hz with hz | hz
      · exact hodd₂.of_dvd_nat hz
      · exact hodd₁.of_dvd_nat hz
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h4
    obtain ⟨j, rfl⟩ := hzodd
    omega
  ·
    have h12 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [Nat.card_congr e.toEquiv, h12] at hq1
    have := (eq_two_of_two_pow_add_one_dvd hm (Or.inl rfl) hq1).2
    omega
  ·
    have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [Nat.card_congr e.toEquiv, h24] at hq1
    have := (eq_two_of_two_pow_add_one_dvd hm (Or.inr (Or.inl rfl)) hq1).2
    omega
  ·
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [Nat.card_congr e.toEquiv, h60] at hq1 hcardH
    have hm2 := (eq_two_of_two_pow_add_one_dvd hm (Or.inr (Or.inr rfl)) hq1).1
    subst hm2
    rw [card_psl2Model (by norm_num)] at hcardH
    exact hcardH (by norm_num)
  ·
    simp only [hgcd₂, Nat.div_one] at ht
    rw [Nat.card_congr e.toEquiv, SemidirectProduct.card, hE, hC] at hq1
    have hqt : 2 ^ m + 1 ∣ t := (hcop k).dvd_of_dvd_mul_left hq1
    have ht0 : 0 < t := hC ▸ Nat.card_pos
    have h1 := Nat.le_of_dvd ht0 hqt
    have h2 := Nat.le_of_dvd (by omega) ht
    omega
  ·
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hk
      omega
    have hkm : k ≠ m := by
      rintro rfl
      exact hcardH (Nat.card_congr e.toEquiv)
    have hklt : k < m := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hk) hkm
    have hpow : 2 ^ k < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hklt
    have hFk : Nat.card (GaloisField 2 k) = 2 ^ k := GaloisField.card 2 k hk0
    have hoddk : Odd (2 ^ k - 1) :=
      Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow' hk0).mpr even_two) odd_one
    have hgk : Nat.gcd (2 ^ k - 1) 2 = 1 := Nat.coprime_two_right.mpr hoddk
    have hxo' : orderOf (e x) = 2 ^ m + 1 := by rw [MulEquiv.orderOf_eq, hxo]
    have hdvd := CFSG.Glauberman.Dickson.psl2_orderOf_dvd hFk (e x)
    rw [hxo', hFk, hgk, Nat.div_one, Nat.div_one] at hdvd
    have h2k : 2 ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases hdvd with hd | hd | hd
    · have := Nat.le_of_dvd (by norm_num) hd
      omega
    · have := Nat.le_of_dvd (by omega) hd
      omega
    · have := Nat.le_of_dvd (by omega) hd
      omega
  ·
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hk
      omega
    have h2km : 2 * k ≤ m := Nat.le_of_dvd (by omega) hk
    have hFk : Nat.card (GaloisField 2 k) = 2 ^ k := GaloisField.card 2 k hk0
    rw [Nat.card_congr e.toEquiv, huppertXI13_card_pgl2, hFk] at hq1
    have hq2 : 2 ^ m + 1 ∣ (2 ^ k) ^ 2 - 1 := (hcop k).dvd_of_dvd_mul_left hq1
    have hsq : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
    rw [hsq] at hq2
    have hpow : 2 ^ (2 * k) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2km
    have h1 : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
    have := Nat.le_of_dvd (by
      have : 2 ^ 2 ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega) hq2
    omega

end CFSG.Timmesfeld.Bridge.OddTransp
