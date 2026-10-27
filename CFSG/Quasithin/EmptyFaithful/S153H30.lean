module

public import CFSG.Quasithin.EmptyFaithful.S153D30
public import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input30Blocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15330 T Mc M V₁ V₂ Yp I L t →
    (∃ n : ℕ, 1 < n ∧ IsPSL 2 2 n ↥(Star153 T I L)) →
    IsBorelIn (Star153 T I L) (Star153 T I (M ⊓ L)) →
      IsBlock2 I L ∧ ((∃ m : ℕ, 1 < m ∧ IsLin2Type L m) ∨ IsAltType L 5)

@[expose] def Input30NoA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15330 T Mc M V₁ V₂ Yp I L t →
    IsBorelIn (Star153 T I L) (Star153 T I (M ⊓ L)) →
    IsBlock2 I L → IsAltType L 5 → False

@[expose] def Input30AutCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15330 T Mc M V₁ V₂ Yp I L t →
    IsBorelIn (Star153 T I L) (Star153 T I (M ⊓ L)) →
    IsBlock2 I L → (∃ m : ℕ, 1 < m ∧ IsLin2Type L m) →
      ∀ s ∈ Sgp153 T V₁, (∀ y ∈ Yp, s * y = y * s) → ∀ l ∈ L, s * l = l * s

namespace S153H

section Orders

open CFSG.Assembly.LowTwoRank

theorem card_psl_two_two {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    1 ≤ n ∧ Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨⟨hp, hf, -⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  refine ⟨hf, ?_⟩
  have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2) (by norm_num)
  rw [Nat.card_congr e.toEquiv, h1, hK]
  have hodd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have : Odd (2 ^ n - 1) := by
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hf
      obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 2 * k := ⟨2 ^ (n - 1), by
        rw [← pow_succ']; congr 1; omega⟩
      exact ⟨k - 1, by omega⟩
    exact (Nat.coprime_two_left.mpr this)
  rw [hodd]
  simp [Finset.Icc_self]

theorem card_psl_three_two {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_psu_three_three {X : Type} [Group X] (h : IsPSU 3 3 1 X) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem card_alt_six {X : Type} [Group X] (h : IsAlt 6 X) : Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide


theorem pslTwo_card_ne {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (hm : m = 168 ∨ m = 360 ∨ m = 6048) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ m := by
  by_cases h4 : n ≤ 4
  · interval_cases n <;> omega
  · have h5 : 5 ≤ n := by omega
    have h32 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
    have hge : 32 * (32 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul h32 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h32 2) 1)
    omega

theorem not_iso_small {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    ¬ IsPSL 3 2 1 X ∧ ¬ IsAlt 6 X ∧ ¬ IsPSU 3 3 1 X := by
  obtain ⟨hn, hcard⟩ := card_psl_two_two h
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · exact pslTwo_card_ne hn (Or.inl rfl) (hcard.symm.trans (card_psl_three_two h'))
  · exact pslTwo_card_ne hn (Or.inr (Or.inl rfl)) (hcard.symm.trans (card_alt_six h'))
  · exact pslTwo_card_ne hn (Or.inr (Or.inr rfl)) (hcard.symm.trans (card_psu_three_three h'))

theorem not_normal_perm_eight {n : ℕ} (N : Subgroup (Equiv.Perm (Fin 8))) (hN : N.Normal)
    (h : IsPSL 2 2 n ↥N) : False := by
  obtain ⟨hn, hcard⟩ := card_psl_two_two h
  have hA : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hX : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide
  have hAcard : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
  have hNn : (N.subgroupOf (alternatingGroup (Fin 8))).Normal := hN.comap _
  rcases (haveI := hNn; hA.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 8)))) with
    hbot | htop
  ·
    have hdisj : N ⊓ alternatingGroup (Fin 8) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : alternatingGroup (Fin 8)) ∈ N.subgroupOf (alternatingGroup (Fin 8)) := hx.1
      rw [hbot] at this
      have h1 : (⟨x, hx.2⟩ : alternatingGroup (Fin 8)) = 1 := Subgroup.mem_bot.mp this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    have hinj : Function.Injective (fun x : N =>
        (QuotientGroup.mk (x : Equiv.Perm (Fin 8)) : Equiv.Perm (Fin 8) ⧸ alternatingGroup (Fin 8))) := by
      intro x y hxy
      have h1 : (x : Equiv.Perm (Fin 8))⁻¹ * y ∈ alternatingGroup (Fin 8) := QuotientGroup.eq.mp hxy
      have h2 : (x : Equiv.Perm (Fin 8))⁻¹ * y ∈ N := N.mul_mem (N.inv_mem x.2) y.2
      have h3 : (x : Equiv.Perm (Fin 8))⁻¹ * y ∈ N ⊓ alternatingGroup (Fin 8) := ⟨h2, h1⟩
      rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h3
      exact Subtype.ext h3
    have hle := Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card (Equiv.Perm (Fin 8) ⧸ alternatingGroup (Fin 8)) = 2 :=
      alternatingGroup.index_eq_two
    rw [h2, hcard] at hle
    have h4 : 2 ^ n ≥ 2 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h5 : (2 ^ n) ^ 2 - 1 ≥ 3 := by
      have := Nat.pow_le_pow_left h4 2
      omega
    have h6 : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≥ 2 * 3 := Nat.mul_le_mul h4 h5
    omega
  ·
    have hle : alternatingGroup (Fin 8) ≤ N := Subgroup.subgroupOf_eq_top.mp htop
    have hd1 : Nat.card (alternatingGroup (Fin 8)) ∣ Nat.card N := Subgroup.card_dvd_of_le hle
    have hd2 : Nat.card N ∣ Nat.card (Equiv.Perm (Fin 8)) := Subgroup.card_subgroup_dvd_card N
    rw [hAcard] at hd1
    rw [hX] at hd2
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hle2 : Nat.card N ≤ 40320 := Nat.le_of_dvd (by norm_num) hd2
    have hge : 20160 ≤ Nat.card N := Nat.le_of_dvd hpos hd1
    rw [hcard] at hle2 hge hd1 hd2
    by_cases h5 : n ≤ 5
    · interval_cases n <;> omega
    · have h6 : 6 ≤ n := by omega
      have h64 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h6
      have hge' : 64 * (64 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
        Nat.mul_le_mul h64 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h64 2) 1)
      omega


theorem not_normal_of_perm_eight {n : ℕ} {X : Type} [Group X] (N : Subgroup X) (hN : N.Normal)
    (h : IsPSL 2 2 n ↥N) (e : X ≃* Equiv.Perm (Fin 8)) : False := by
  have hN' : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
  have hiso : ↥N ≃* ↥(N.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective N e.toMonoidHom e.injective
  exact not_normal_perm_eight _ hN' (h.of_mulEquiv hiso)

end Orders

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem le_I_of_ctx (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) : L ≤ I :=
  le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1)

theorem V₁_le_Sgp153 (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) : V₁ ≤ Sgp153 T V₁ :=
  le_inf (c.ctx.hyp.decomp.le₁.trans c.ctx.hyp.hyp.VZ_le_T) Subgroup.le_normalizer

theorem isBorelIn_of_isPSL (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) {n : ℕ}
    (hn : IsPSL 2 2 n ↥(Star153 T I L)) :
    IsBorelIn (Star153 T I L) (Star153 T I (M ⊓ L)) := by
  rcases c.c28 with ⟨-, hB⟩ | ⟨h1, -, -⟩ | ⟨hS8, -⟩
  · exact hB
  · rcases h1 with h1 | h1 | h1
    · exact absurd h1 (not_iso_small hn).1
    · exact absurd h1 (not_iso_small hn).2.1
    · exact absurd h1 (not_iso_small hn).2.2
  · exfalso
    have hLI : L ≤ I := le_I_of_ctx c
    have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
    have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLI.trans hUN
    have hle : Star153 T I L ≤ Star153 T I I := autOn_le_autOn (UI153 T I) hLI
    have hnorm : Star153 T I I ≤ Subgroup.normalizer
        (Star153 T I L : Set (MulAut ↥(UI153 T I))) :=
      autOn_le_normalizer_autOn hUN hLU c.c27.normal
    have hN : ((Star153 T I L).subgroupOf (Star153 T I I)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm
    have hiso : IsPSL 2 2 n ↥((Star153 T I L).subgroupOf (Star153 T I I)) :=
      hn.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
    obtain ⟨e⟩ := hS8
    exact not_normal_of_perm_eight _ hN hiso e

theorem input15330_of_named_inputs (hBl : Input30Blocks) (hA5 : Input30NoA5)
    (hAut : Input30AutCent) : Input15330 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hex
  obtain ⟨n, hn, hpsl⟩ := hex
  have hbor : IsBorelIn (Star153 T I L) (Star153 T I (M ⊓ L)) :=
    isBorelIn_of_isPSL c hpsl
  obtain ⟨hblock, hlin | ha5⟩ := hBl G T Mc M V₁ V₂ Yp I L t c ⟨n, hn, hpsl⟩ hbor
  · have hcent := hAut G T Mc M V₁ V₂ Yp I L t c hbor hblock hlin
    have hLC : L ≤ Subgroup.centralizer (V₁ : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvS : v ∈ Sgp153 T V₁ := V₁_le_Sgp153 c hv
      have hvY : ∀ y ∈ Yp, v * y = y * v := fun y hy =>
        Subgroup.mem_centralizer_iff.mp (c.c29.cent hy) v hv
      exact hcent v hvS hvY l hl
    have hLM : L ≤ M := hLC.trans ((Subgroup.centralizer_le_normalizer _).trans c.c29.norm_le)
    exact c.conc.2.1 (le_inf hLM (le_I_of_ctx c))
  · exact hA5 G T Mc M V₁ V₂ Yp I L t c hbor hblock ha5

end S153H

end CFSG.Quasithin
