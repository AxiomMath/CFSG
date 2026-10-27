module

public import CFSG.Quasithin.Background.RonanE27S6
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Enc

public section

namespace CFSG.Quasithin.RonanE211

open Equiv CFSG.Quasithin CFSG.Quasithin.Ch3E213M.P6E CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Borel252.A6 CFSG.Quasithin.RonanE27
open scoped commutatorElement

@[expose] def rD : P6 := perm6 [[0, 1, 2, 3], [4, 5]]

@[expose] def sD : P6 := perm6 [[0, 2], [4, 5]]

theorem rD_mem : rD ∈ D0 := by
  rw [mem_D0]
  decide +kernel

theorem sD_mem : sD ∈ D0 := by
  rw [mem_D0]
  decide +kernel

theorem rD_sq : rD * rD = zA := by decide +kernel

theorem sD_conj : sD * rD * sD⁻¹ = rD⁻¹ := by decide +kernel

theorem zA_ne_one : zA ≠ 1 := by decide +kernel

theorem rD_sD_ne : rD * sD ≠ sD * rD := by decide +kernel

theorem rD_mem_S06 : rD ∈ S06 := Or.inl rD_mem

theorem sD_mem_S06 : sD ∈ S06 := Or.inl sD_mem

theorem zB_mem_S06 : zB ∈ S06 := zB_mem_extZ

theorem commutator_alt_six : commutator ↥(alternatingGroup (Fin 6)) = ⊤ := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (commutator ↥(alternatingGroup (Fin 6))).normal_of_characteristic.eq_bot_or_eq_top
    with h | h
  · exfalso
    have hc : ⁅(⟨rD, D0_le_A6 rD_mem⟩ : ↥(alternatingGroup (Fin 6))), ⟨sD, D0_le_A6 sD_mem⟩⁆ ∈
        commutator ↥(alternatingGroup (Fin 6)) := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact rD_sD_ne (congrArg Subtype.val hc)
  · exact h

theorem chk_zcent : ∀ y : P6, R6.enc y ∈ s06L → y * rD = rD * y → y * sD = sD * y →
    y * zB = zB * y → y = 1 ∨ y = zA ∨ y = zB ∨ y = zA * zB := by
  decide +kernel

theorem mem_Z6_of_central_S06 {y : P6} (hy : y ∈ S06) (h : ∀ s ∈ S06, y * s = s * y) :
    y = 1 ∨ y = zA ∨ y = zB ∨ y = zA * zB :=
  chk_zcent y (mem_S06_iff.1 hy) (h _ rD_mem_S06) (h _ sD_mem_S06) (h _ zB_mem_S06)

def r6pow (x : R6) : ℕ → R6
  | 0 => 1
  | n + 1 => r6pow x n * x

theorem enc_pow (c : P6) (n : ℕ) : R6.enc (c ^ n) = r6pow (R6.enc c) n := by
  induction n with
  | zero => rw [pow_zero, R6.enc_one, r6pow]
  | succ n ih => rw [pow_succ, R6.enc_mul, ih, r6pow]

theorem chk_pow60 : ∀ c : P6, r6pow (R6.enc c) 60 = 1 := by decide +kernel

theorem pow_sixty (c : P6) : c ^ 60 = 1 :=
  R6.enc_inj (by rw [enc_pow, chk_pow60 c, R6.enc_one])

theorem card_perm_six : Nat.card P6 = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem not_closure_pair_eq_top {y y' : P6} (hy : y * y = 1) (hy' : y' * y' = 1) :
    Subgroup.closure ({y, y'} : Set P6) ≠ ⊤ := by
  intro htop
  set c := y * y' with hc
  set N := Subgroup.zpowers c with hN
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hy'i : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hy'
  have hcinv : c⁻¹ = y' * y := by
    rw [hc, mul_inv_rev, hy'i, hyi]
  have hycy : y * c * y⁻¹ = c⁻¹ := by
    rw [hcinv, hc, hyi]
    calc y * (y * y') * y = (y * y) * y' * y := by group
      _ = y' * y := by rw [hy, one_mul]
  have hyc : ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : y * c ^ k * y⁻¹ = (y * c * y⁻¹) ^ k := (conj_zpow).symm
    rw [this, hycy]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) k
  have hall : ∀ x : P6, x ∈ N ∨ ∃ n ∈ N, x = n * y := by
    intro x
    have hx : x ∈ Subgroup.closure ({y, y'} : Set P6) := htop ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction (p := fun x _ => x ∈ N ∨ ∃ n ∈ N, x = n * y) ?_ ?_ ?_ ?_ hx
    · intro z hz
      rcases hz with h | h
      · rw [h]
        exact Or.inr ⟨1, Subgroup.one_mem _, by rw [one_mul]⟩
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        refine Or.inr ⟨y' * y, ?_, by rw [mul_assoc, hy, mul_one]⟩
        rw [← hcinv]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
    · exact Or.inl (Subgroup.one_mem _)
    · rintro a b - - (ha | ⟨n, hn, rfl⟩) (hb | ⟨m, hm, rfl⟩)
      · exact Or.inl (N.mul_mem ha hb)
      · exact Or.inr ⟨a * m, N.mul_mem ha hm, by rw [mul_assoc]⟩
      · refine Or.inr ⟨n * (y * b * y⁻¹), N.mul_mem hn (hyc b hb), ?_⟩
        group
      · refine Or.inl ?_
        have : n * y * (m * y) = n * (y * m * y⁻¹) * (y * y) := by group
        rw [this, hy, mul_one]
        exact N.mul_mem hn (hyc m hm)
    · rintro a - (ha | ⟨n, hn, rfl⟩)
      · exact Or.inl (N.inv_mem ha)
      · refine Or.inr ⟨y * n⁻¹ * y⁻¹, hyc _ (N.inv_mem hn), ?_⟩
        rw [inv_mul_cancel_right, mul_inv_rev, hyi]
  have hcard : Nat.card P6 ≤ 2 * Nat.card N := by
    let f : N ⊕ N → P6 := Sum.elim (fun n => (n : P6)) (fun n => (n : P6) * y)
    have hf : Function.Surjective f := by
      intro x
      rcases hall x with h | ⟨n, hn, rfl⟩
      · exact ⟨Sum.inl ⟨x, h⟩, rfl⟩
      · exact ⟨Sum.inr ⟨n, hn⟩, rfl⟩
    calc Nat.card P6 ≤ Nat.card (N ⊕ N) := Nat.card_le_card_of_surjective f hf
      _ = 2 * Nat.card N := by rw [Nat.card_sum]; ring
  have hord : Nat.card N ≤ 60 := by
    rw [hN, Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (pow_sixty c))
  rw [card_perm_six] at hcard
  omega

theorem chk_s06_exp : ∀ x : P6, R6.enc x ∈ s06L → r6pow (R6.enc x) 4 = 1 := by decide +kernel

theorem chk_s06_card : (Finset.univ.filter (fun x : P6 => R6.enc x ∈ s06L)).card = 16 := by
  decide +kernel

theorem card_S06 : Nat.card S06 = 16 := by
  classical
  have : Nat.card S06 = Nat.card {x : P6 // R6.enc x ∈ s06L} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_S06_iff)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact chk_s06_card

theorem isSylowTwoOf_S06 : IsSylowTwoOf S06 (⊤ : Subgroup P6) := by
  refine ⟨le_top, fun x => ?_, ?_⟩
  · refine ⟨2, Subtype.ext ?_⟩
    have h1 : (x : P6) ^ 4 = 1 :=
      R6.enc_inj (by rw [enc_pow, chk_s06_exp (x : P6) (mem_S06_iff.1 x.2), R6.enc_one])
    simpa using h1
  · change ¬ 2 ∣ S06.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    intro h
    have h2 : S06.index * Nat.card S06 = Nat.card P6 := Subgroup.index_mul_card S06
    rw [card_S06, card_perm_six] at h2
    have h3 : S06.index = 45 := by omega
    rw [h3] at h
    omega

theorem zA_mem_of_gen {V' : Subgroup P6}
    (hV' : ∀ v ∈ V', v = 1 ∨ v = zA ∨ v = zB ∨ v = zA * zB) {c : P6}
    (hgen : V' ⊔ V'.map (MulAut.conj c).toMonoidHom = ⊤) : zA ∈ V' := by
  by_contra hzA
  have hzB2 : zB * zB = 1 := zB_mul_self
  have hzAzB2 : (zA * zB) * (zA * zB) = 1 := by decide +kernel
  obtain ⟨y₀, hy₀2, hV'le⟩ : ∃ y₀ : P6, y₀ * y₀ = 1 ∧ ∀ v ∈ V', v = 1 ∨ v = y₀ := by
    by_cases hB : zB ∈ V'
    · refine ⟨zB, hzB2, fun v hv => ?_⟩
      rcases hV' v hv with h | h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hv) hzA
      · exact Or.inr h
      · exfalso
        apply hzA
        have : zA = (zA * zB) * zB := by
          rw [mul_assoc, zB_mul_self, mul_one]
        rw [this]
        exact V'.mul_mem (h ▸ hv) hB
    · refine ⟨zA * zB, hzAzB2, fun v hv => ?_⟩
      rcases hV' v hv with h | h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hv) hzA
      · exact absurd (h ▸ hv) hB
      · exact Or.inr h
  have hle : V' ≤ Subgroup.closure ({y₀, c * y₀ * c⁻¹} : Set P6) := by
    intro v hv
    rcases hV'le v hv with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hle' : V'.map (MulAut.conj c).toMonoidHom ≤
      Subgroup.closure ({y₀, c * y₀ * c⁻¹} : Set P6) := by
    rintro _ ⟨v, hv, rfl⟩
    rcases hV'le v hv with h | h
    · rw [h, map_one]; exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have htop : Subgroup.closure ({y₀, c * y₀ * c⁻¹} : Set P6) = ⊤ :=
    top_le_iff.1 (hgen ▸ sup_le hle hle')
  refine not_closure_pair_eq_top hy₀2 ?_ htop
  have : c * y₀ * c⁻¹ * (c * y₀ * c⁻¹) = c * (y₀ * y₀) * c⁻¹ := by group
  rw [this, hy₀2]
  group

end CFSG.Quasithin.RonanE211
