module

public import CFSG.Quasithin.H13.A7IrrPlus
public import Certificates.Certificate17011


public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB

theorem nat_card_SL_three_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_three]
  norm_num

theorem nat_card_SL_four_two : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

theorem center_SL_zmod_two_eq_bot {n : ℕ} (hn : 1 ≤ n) :
    center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rcases zmodTwo_eq_zero_or_one r with h0 | h1
  · rw [h0, Fintype.card_fin, zero_pow (by omega)] at hr
    exact absurd hr (by decide)
  · rw [mem_bot]
    apply Subtype.ext
    rw [← hrA, h1, map_one]
    rfl

theorem not_mulEquiv_SL_of_alternating_seven {Q : Type*} [Group Q] [Finite Q]
    (hA7 : Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 7))) {n : ℕ} (hn : n = 3 ∨ n = 4) :
    ¬ Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rintro ⟨e⟩
  obtain ⟨f⟩ := hA7
  have hZ : Nat.card (center Q) = 1 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      center_SL_zmod_two_eq_bot (by omega), card_bot]
  have hQ := card_eq_card_quotient_mul_card_subgroup (center Q)
  rw [hZ, mul_one, Nat.card_congr f.toEquiv, coord_card_alternating_seven,
    Nat.card_congr e.toEquiv] at hQ
  rcases hn with rfl | rfl
  · rw [nat_card_SL_three_two] at hQ
    omega
  · rw [nat_card_SL_four_two] at hQ
    omega

section Escape

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatConfig.exists_escape (h12213 : Stmt12_2_13) [Finite G] (hyp : Hyp1223 G T L V)
    (hA7 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7))) :
    ∃ v : V, v ≠ 1 ∧ ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  rcases h12213 G T L V hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hyp.notAlt hyp.maximal
      hyp.faithful hyp.quasisimple hyp.normalizes hyp.irrPlus with
    ⟨v, hv, hv1, hesc⟩ | ⟨n, hn, hQ, -⟩ | ⟨hQ, -⟩ | ⟨hQ, -⟩
  · exact ⟨⟨v, hv⟩, fun h => hv1 (congrArg Subtype.val h), hesc⟩
  · exact absurd hQ (not_mulEquiv_SL_of_alternating_seven hA7 hn)
  · exact absurd hQ (not_mulEquiv_SL_of_alternating_seven hA7 (Or.inl rfl))
  · exact absurd hQ (not_mulEquiv_SL_of_alternating_seven hA7 (Or.inr rfl))

theorem A7NatConfig.hammingNorm_eq_four_of_escape (h : A7NatConfig T L V ψ) {v : V}
    (hv1 : v ≠ 1) (hvM : ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G)) :
    hammingNorm (vec ψ v) = 4 := by
  have heven := even_hammingNorm_of_mem_evenWeight (vec_mem ψ v)
  have hne : hammingNorm (vec ψ v) ≠ 0 := by
    rw [Ne, hammingNorm_eq_zero, vec_eq_zero_iff]
    exact hv1
  have hle : hammingNorm (vec ψ v) ≤ 7 := by
    have := hammingNorm_le_card_fintype (x := vec ψ v)
    simpa using this
  obtain ⟨m, hm⟩ := heven
  have h246 : hammingNorm (vec ψ v) = 2 ∨ hammingNorm (vec ψ v) = 4 ∨
      hammingNorm (vec ψ v) = 6 := by omega
  rcases h246 with h2 | h4 | h6
  · exact absurd (h.wt26 v (Or.inl h2)) hvM
  · exact h4
  · exact absurd (h.wt26 v (Or.inr h6)) hvM

theorem A7NatConfig.centralizer_not_le_of_weight_four (h : A7NatConfig T L V ψ) {v : V}
    (hv1 : v ≠ 1) (hvM : ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G)) {e : V}
    (he : hammingNorm (vec ψ e) = 4) :
    ¬ centralizer ({(e : G)} : Set G) ≤ normalizer (L : Set G) := by
  have h4 := h.hammingNorm_eq_four_of_escape hv1 hvM
  obtain ⟨σ, hσ, hσv⟩ := exists_alt_permAct7_eq (h4.trans he.symm)
  obtain ⟨l, hl, hact⟩ := h.Lonto σ hσ
  let y : V := ⟨l * v * l⁻¹, (mem_normalizer_iff.1 (h.L_le hl) v).1 v.2⟩
  have hy : y = e := vec_injective ψ (by rw [hact v y rfl, hσv])
  have hye : l * (v : G) * l⁻¹ = e := congrArg Subtype.val hy
  intro heM
  apply hvM
  intro c hc
  have hlM : l ∈ normalizer (L : Set G) := le_normalizer hl
  have hc' : l * c * l⁻¹ ∈ centralizer ({(e : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hc ⊢
    rw [← hye]
    calc l * c * l⁻¹ * (l * (v : G) * l⁻¹) = l * (c * v) * l⁻¹ := by group
      _ = l * (v * c) * l⁻¹ := by rw [hc]
      _ = l * v * l⁻¹ * (l * c * l⁻¹) := by group
  have h1 := heM hc'
  have h2 := mul_mem (mul_mem (inv_mem hlM) h1) hlM
  rwa [show l⁻¹ * (l * c * l⁻¹) * l = c by group] at h2

theorem hammingNorm_vecFour : hammingNorm vecFour = 4 :=
  Certificates.certificate17011.1

theorem vecFour_mem : vecFour ∈ evenWeight 7 :=
  Certificates.certificate17011.2

end Escape

section Minimal

variable {G : Type} [Group G]

theorem exists_hStar_le_centralizer [Finite G] (T : Sylow 2 G) {M : Subgroup G} {e : G}
    (heT : e ∈ (T : Subgroup G)) (heZ : ∀ t ∈ (T : Subgroup G), t * e = e * t) (he1 : e ≠ 1)
    (hsolv : ∀ H : Subgroup G, (T : Subgroup G) ≤ H → Group.IsSolvable H → H ≤ M)
    (hesc : ¬ centralizer ({e} : Set G) ≤ M) :
    ∃ H : Subgroup G, IsHStar (T : Subgroup G) M H ∧ H ≤ centralizer ({e} : Set G) ∧
      ¬ Group.IsSolvable H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : (T : Subgroup G) ≤ centralizer ({e} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 (heZ t ht)
  set S : Set (Subgroup G) :=
    {H | (T : Subgroup G) ≤ H ∧ H ≤ centralizer ({e} : Set G) ∧ ¬ H ≤ M} with hS
  obtain ⟨H, hHmin⟩ := (Set.toFinite S).exists_minimal ⟨centralizer ({e} : Set G), hTC, le_rfl,
    hesc⟩
  obtain ⟨hTH, hHC, hHM⟩ := hHmin.1
  have heH : e ∈ H := hTH heT
  have hO2 : pCoreOf 2 H ≠ ⊥ := by
    intro h0
    set x : H := ⟨e, heH⟩ with hx
    set E : Subgroup H := zpowers x with hE
    have hEn : E.Normal := by
      constructor
      intro y hy g
      have hge : Commute g x := Subtype.ext (mem_centralizer_singleton_iff.1 (hHC g.2))
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
      rw [(hge.zpow_right m).eq, mul_inv_cancel_right]
      exact hy
    have hE2 : IsPGroup 2 E := by
      obtain ⟨k, hk⟩ := T.isPGroup' ⟨e, heT⟩
      have hxk : x ^ 2 ^ k = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      intro y
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 y.2
      refine ⟨k, Subtype.ext ?_⟩
      rw [SubgroupClass.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hxk, one_zpow]
      rfl
    have hEle : E ≤ CFSG.Open.pCore 2 ↥H := le_sSup ⟨hEn, hE2⟩
    have hxO : x ∈ CFSG.Open.pCore 2 ↥H := hEle (mem_zpowers x)
    have heO : e ∈ pCoreOf 2 H := ⟨x, hxO, rfl⟩
    rw [h0, mem_bot] at heO
    exact he1 heO
  refine ⟨H, ⟨⟨hTH, hO2⟩, hHM, fun Y hY hYH hYM => ?_⟩, hHC, fun hHs => hHM (hsolv H hTH hHs)⟩
  exact le_antisymm hYH (hHmin.2 ⟨hY.1, hYH.trans hHC, hYM⟩ hYH)

end Minimal

end CFSG.Quasithin.H13.A7
