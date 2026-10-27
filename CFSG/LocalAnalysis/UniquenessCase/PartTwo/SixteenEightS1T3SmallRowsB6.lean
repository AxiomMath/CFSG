module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCEngine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Perm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Exp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A6Mod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A6Good
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_eq_two_pow_mul_three_pow {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3) :
    n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 := by
  have hsupp : n.factorization.support ⊆ {2, 3} := by
    intro q hq
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hq
    obtain ⟨hqprime, hqdvd, -⟩ := hq
    rcases h q hqprime hqdvd with h2 | h3
    · exact Finset.mem_insert.2 (Or.inl h2)
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h3))
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ hsupp _ fun _ _ => pow_zero _,
    Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]

private theorem s16t3_subgroupOf_map_subtype {A B : Subgroup G} (hAB : A ≤ B)
    (Y : Subgroup ↥A) :
    (Y.map A.subtype).subgroupOf B = Y.map (Subgroup.inclusion hAB) := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, Subtype.ext (by simpa using hyx)⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, congrArg Subtype.val hyx⟩

private theorem s16t3_barSub_map_subtype {V₀ V S : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : S ≤ stabTil V₀ V) (Y : Subgroup ↥S) :
    barSub V₀ V hV (Y.map S.subtype) =
      Y.map ((actTil V₀ V hV).comp (Subgroup.inclusion hS)) := by
  unfold barSub
  rw [s16t3_subgroupOf_map_subtype hS Y, Subgroup.map_map]

theorem s16t3_exists_permuting_three_alt_six_k168
    (hset : Setting16 D V₀ V L) (h127 : R127 D) (h119 : F11.R119 D)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hA6 : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧
      Permutes Y D.T ∧ 9 ≤ Nat.card ↥Y := by
  classical
  obtain ⟨YL, YK, hYL, hYK⟩ :=
    s16t3_exists_covers_alt hset h127 h119 hT h7 (Or.inl hA6) hK
  obtain ⟨e⟩ := hA6
  obtain ⟨hSM, hSbar, -, hS23⟩ := s16t3_join_inf_cTilde hset hT h7 hYL hYK
  obtain ⟨J, hJM, hTJ, ⟨xJ, hJcard⟩, hJcyc⟩ := ThreeNat.exists_J_alt6 hT h7 e hK
  let S : Subgroup G := YL ⊔ YK ⊔ D.T
  have hSM' : S ≤ D.M := hSM
  have hDTS : D.T ≤ S := le_sup_right
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hMn : D.M ≤ normalizer (V : Set G) := hMst.trans (stabTil_le_normalizer V₀ V)
  have hSs : S ≤ stabTil V₀ V := hSM'.trans hMst
  let φ : ↥S →* MulAut (Vtil V₀ V hV) :=
    (barHom V₀ V hV hMst).comp (Subgroup.inclusion hSM')
  let T' : Subgroup ↥S := D.T.subgroupOf S
  have hT'2 : IsPGroup 2 ↥T' := D.sylowM.isPGroup.comap_subtype
  have hT'syl : ¬ 2 ∣ T'.index := by
    have hdvd : D.T.relIndex S ∣ D.T.index := Subgroup.relIndex_dvd_index_of_le hDTS
    have hodd : ¬ 2 ∣ D.T.index := by
      have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowG).2.2
      rwa [Subgroup.relIndex_top_right] at h2
    intro hdiv
    exact hodd (hdiv.trans hdvd)
  have hφeq : φ = (actTil V₀ V hV).comp (Subgroup.inclusion hSs) := by
    ext x
    rfl
  have hφker : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf S := by
    show ((barHom V₀ V hV hMst).comp (Subgroup.inclusion hSM')).ker = _
    rw [← MonoidHom.comap_ker, ker_barHom V₀ V hV hMn hMst,
      Subgroup.comap_inclusion_subgroupOf hSM']
  have hφrange : φ.range = barSub V₀ V hV S := by
    rw [hφeq, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hrange : φ.range = Mbar D.M V₀ V hV := by
    rw [hφrange]
    exact hSbar
  have hJrange : J ≤ φ.range := by
    rw [hrange]
    exact hJM
  have hTJ' : T'.map φ ≤ J := by
    rintro x ⟨t, ht, rfl⟩
    rw [hφeq]
    exact hTJ (actTil_mem_barSub V₀ V hV ht (hSs t.2))
  let ψ : ↥(J.comap φ) →* ↥J :=
    { toFun := fun x => ⟨φ x, x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hψsurj : Function.Surjective ψ := by
    intro j
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 (hJrange j.2)
    exact ⟨⟨s, by show φ s ∈ J; rw [hs]; exact j.2⟩, Subtype.ext hs⟩
  have hψker : ψ.ker = φ.ker.subgroupOf (J.comap φ) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  have hψcard : Nat.card ↥ψ.ker * Nat.card ↥J = Nat.card ↥(J.comap φ) :=
    Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψsurj
  have hkerle : φ.ker ≤ J.comap φ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact J.one_mem
  have hkerCard : Nat.card ↥ψ.ker = Nat.card ↥φ.ker := by
    rw [hψker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
  have hcard : Nat.card ↥(J.comap φ) = Nat.card ↥φ.ker * Nat.card ↥J := by
    rw [← hψcard, hkerCard]
  have hkerCard23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥φ.ker → p = 2 ∨ p = 3 := by
    intro p hp hpdvd
    have hEq : Nat.card ↥φ.ker =
        Nat.card ↥((YL ⊔ YK ⊔ D.T) ⊓ F11.CTilde D.M V₀ V) := by
      rw [hφker, ← Subgroup.inf_subgroupOf_right (F11.CTilde D.M V₀ V) S]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : F11.CTilde D.M V₀ V ⊓ S ≤ S)).toEquiv]
      exact congrArg (fun H : Subgroup G => Nat.card ↥H)
        (inf_comm (F11.CTilde D.M V₀ V) S)
    rw [hEq] at hpdvd
    exact hS23 p hp hpdvd
  have hcomap23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(J.comap φ) → p = 2 ∨ p = 3 := by
    intro p hp hpdvd
    rw [hcard] at hpdvd
    rcases hp.dvd_mul.1 hpdvd with h | h
    · exact hkerCard23 p hp h
    · rw [hJcard] at h
      rcases hp.dvd_mul.1 h with h2 | h3
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      · right
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
  haveI : Nonempty ↥(J.comap φ) := ⟨1⟩
  have hn0 : Nat.card ↥(J.comap φ) ≠ 0 := Nat.card_pos.ne'
  have hxy : Nat.card ↥(J.comap φ) =
      2 ^ (Nat.card ↥(J.comap φ)).factorization 2 *
        3 ^ (Nat.card ↥(J.comap φ)).factorization 3 :=
    s16t3_eq_two_pow_mul_three_pow hn0 hcomap23
  have h3dvd : 3 ^ 2 ∣ Nat.card ↥(J.comap φ) := by
    rw [hcard, hJcard]
    exact Dvd.dvd.mul_left (dvd_mul_left (3 ^ 2) (2 ^ xJ)) _
  have h3y : 2 ≤ (Nat.card ↥(J.comap φ)).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn0).mp h3dvd
  obtain ⟨Y', hY'3, hY'card, hY'perm, hY'map⟩ :=
    s16t3_exists_permuting_three_of_two_three φ hT'2 hT'syl hTJ' hxy
  let Y : Subgroup G := Y'.map S.subtype
  have hYM : Y ≤ D.M := (Subgroup.map_subtype_le Y').trans hSM'
  have hY3 : IsPGroup 3 ↥Y := hY'3.map S.subtype
  have hYcard : Nat.card ↥Y = 3 ^ (Nat.card ↥(J.comap φ)).factorization 3 := by
    show Nat.card ↥(Y'.map S.subtype) = _
    rw [Subgroup.card_map_of_injective S.subtype_injective, hY'card]
  have hbarY : barSub V₀ V hV Y = Y'.map φ := by
    show barSub V₀ V hV (Y'.map S.subtype) = Y'.map φ
    rw [s16t3_barSub_map_subtype hSs Y', hφeq]
  have hYJ : barSub V₀ V hV Y ≤ J := by
    rw [hbarY]
    exact Subgroup.map_le_iff_le_comap.mpr hY'map
  have hYS : Y ≤ YL ⊔ YK ⊔ D.T := Subgroup.map_subtype_le Y'
  have hYexp : ∀ y ∈ Y, y ^ 3 = 1 :=
    s16t3_exp_three_alt (m := 6) hset hT h7 hK (Or.inl rfl) e hYL hYK hJcyc hY3 hYS hYJ
  have hperm : Permutes Y D.T := by
    show (Y : Set G) * (D.T : Set G) = (D.T : Set G) * (Y : Set G)
    have hYcoe : (Y : Set G) = S.subtype '' (Y' : Set ↥S) := by
      change (Y'.map S.subtype : Set G) = S.subtype '' (Y' : Set ↥S)
      rw [Subgroup.coe_map]
    have hTmapS : T'.map S.subtype = D.T := Subgroup.map_subgroupOf_eq_of_le hDTS
    have hTcoe : (D.T : Set G) = S.subtype '' (T' : Set ↥S) := by
      rw [← hTmapS, Subgroup.coe_map]
    rw [hYcoe, hTcoe, ← Set.image_mul, ← Set.image_mul, hY'perm]
  have h9 : 9 ≤ Nat.card ↥Y := by
    rw [hYcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (Nat.card ↥(J.comap φ)).factorization 3 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  have hYnc : ¬ IsCyclic ↥Y := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Y)
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      show (g : G) ^ 3 = 1
      exact hYexp (g : G) g.2
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hg3
    have hdvd' : 3 ^ (Nat.card ↥(J.comap φ)).factorization 3 ∣ 3 := by
      rw [hg, hYcard] at hdvd
      exact hdvd
    have hle : 3 ^ (Nat.card ↥(J.comap φ)).factorization 3 ≤ 3 :=
      Nat.le_of_dvd (by norm_num) hdvd'
    omega
  exact ⟨Y, hYM, hY3, hYexp, hYnc, hperm, h9⟩

theorem s168e3_exists_permuting_three_alt_six_k168
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hA6 : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧
      Permutes Y D.T ∧ 9 ≤ Nat.card ↥Y :=
  s16t3_exists_permuting_three_alt_six_k168 c.setting c.std.h127 c.std.h119 hT h7 hA6 hK

theorem S16gRowCtx.false_of_alt_six_L3 (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) : False := by
  obtain ⟨Y, hYM, hY3, hYexp, hYnc, hperm, -⟩ :=
    s16t3_exists_permuting_three_alt_six_k168 h.setting h.std.h127 h.std.h119 hT h7 hL hK
  refine h.false_of_permuting_three_of_good h3 (h.mBarGT_two hT) hYM hY3 hYexp hYnc hperm ?_
  by_cases hV₀ : V₀ = ⊥
  · exact Or.inr (Or.inr (h.exists_good_vector_alt6 h3 hV₀ hT h7 hL hK))
  · exact Or.inl hV₀

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
