module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Perm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7ModB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Exp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7ExpA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7ExpB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCBase

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

theorem s16t3_exists_permuting_three_alt_seven_k168
    (hset : Setting16 D V₀ V L) (h127 : R127 D) (h119 : F11.R119 D)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧
      Permutes Y D.T ∧ 9 < Nat.card ↥Y := by
  classical
  obtain ⟨YL, YK, hYL, hYK⟩ := s16t3_exists_covers_alt hset h127 h119 hT h7 (Or.inr hL) hK
  obtain ⟨e⟩ := hL
  obtain ⟨hSM, hSbar, -, hS23⟩ := s16t3_join_inf_cTilde hset hT h7 hYL hYK
  obtain ⟨J, hJM, hTJ, ⟨xJ, hJcard⟩, hJcyc⟩ := s16t3_exists_J_alt7_aux hT h7 e hK
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
  have h3dvd : 3 ^ 3 ∣ Nat.card ↥(J.comap φ) := by
    rw [hcard, hJcard]
    exact Dvd.dvd.mul_left (dvd_mul_left (3 ^ 3) (2 ^ xJ)) _
  have h3y : 3 ≤ (Nat.card ↥(J.comap φ)).factorization 3 :=
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
    s16t3_exp_three_alt (m := 7) hset hT h7 hK (Or.inr rfl) e hYL hYK hJcyc hY3 hYS hYJ
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
    have h9 : 9 ≤ 3 ^ (Nat.card ↥(J.comap φ)).factorization 3 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (Nat.card ↥(J.comap φ)).factorization 3 :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hperm : Permutes Y D.T := by
    show (Y : Set G) * (D.T : Set G) = (D.T : Set G) * (Y : Set G)
    have hYcoe : (Y : Set G) = S.subtype '' (Y' : Set ↥S) := by
      change (Y'.map S.subtype : Set G) = S.subtype '' (Y' : Set ↥S)
      rw [Subgroup.coe_map]
    have hTmapS : T'.map S.subtype = D.T := Subgroup.map_subgroupOf_eq_of_le hDTS
    have hTcoe : (D.T : Set G) = S.subtype '' (T' : Set ↥S) := by
      rw [← hTmapS, Subgroup.coe_map]
    rw [hYcoe, hTcoe, ← Set.image_mul, ← Set.image_mul, hY'perm]
  have hbig : 9 < Nat.card ↥Y := by
    rw [hYcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ < 3 ^ (Nat.card ↥(J.comap φ)).factorization 3 :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact ⟨Y, hYM, hY3, hYexp, hYnc, hperm, hbig⟩

theorem s168e3_exists_permuting_three_alt_seven_k168
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hA7 : UC22.IsAlt ↥(lBar V₀ V hV L) 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧
      Permutes Y D.T ∧ 9 < Nat.card ↥Y :=
  s16t3_exists_permuting_three_alt_seven_k168 c.setting c.std.h127 c.std.h119
    hT h7 hA7 hK

theorem S16gRowCtx.false_of_alt_seven_L3 (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) : False := by
  obtain ⟨Y, hYM, hY3, hYexp, hYnc, hperm, hbig⟩ :=
    s16t3_exists_permuting_three_alt_seven_k168 h.setting h.std.h127 h.std.h119 hT h7 hL hK
  exact h.false_of_permuting_three h3 (h.mBarGT_two hT) hYM hY3 hYexp hYnc hperm
    (Or.inr hbig)

theorem s16t3_exists_permuting_three_alt_seven_k7
    (hset : Setting16 D V₀ V L) (h127 : R127 D) (h119 : F11.R119 D)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧
      Permutes Y D.T ∧ 9 ≤ Nat.card ↥Y := by
  classical
  let H := lBar V₀ V hV L
  let A := Mbar D.M V₀ V hV
  let K := s1t3KBar A H
  let Tb := barSub V₀ V hV D.T
  obtain ⟨e⟩ := hL
  obtain ⟨N, hNA, hHN, hNfix, hNcomm, hNKbot, hNKsup, hKcase⟩ := hT.structure_of_seven h7
  have hK7 : Nat.card ↥K = 7 := hK
  haveI hNnormA : (N.subgroupOf A).Normal :=
    s16t3_normal_of_sup_of_commute hNA hNKsup hNcomm
  have hAcard : Nat.card ↥A = Nat.card ↥N * Nat.card ↥K := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute N K hNcomm).1
    rw [hNKsup, hNKbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hAquot : Nat.card (A ⧸ N.subgroupOf A) = 7 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
    have hNcard : Nat.card ↥(N.subgroupOf A) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
    rw [hAcard, hNcard] at h1
    have h1' : Nat.card ↥K * Nat.card ↥N =
        Nat.card (A ⧸ N.subgroupOf A) * Nat.card ↥N := by
      rw [mul_comm (Nat.card ↥K) (Nat.card ↥N)]
      exact h1
    have hEq := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥N)) h1'
    rw [← hEq, hK7]
  have hTbN : Tb ≤ N := by
    intro t ht
    have htA : t ∈ A := hT.sylow.le ht
    obtain ⟨k, hk⟩ := hT.sylow.isPGroup ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hq2 : orderOf (QuotientGroup.mk' (N.subgroupOf A) ⟨t, htA⟩) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, show ((⟨t, htA⟩ : ↥A) ^ 2 ^ k) = 1 from Subtype.ext hk', map_one]
    have hq7 : orderOf (QuotientGroup.mk' (N.subgroupOf A) ⟨t, htA⟩) ∣ 7 := by
      rw [← hAquot]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) 7 :=
      Nat.Coprime.pow_left k (by norm_num)
    have hq1 := Nat.eq_one_of_dvd_coprimes hcop hq2 hq7
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hq1))
  let N1 := H ⊔ Tb
  have hN1A : N1 ≤ A := sup_le hT.le hT.sylow.le
  have hN1N : N1 ≤ N := sup_le hHN hTbN
  have hN1norm : N1 ≤ Subgroup.normalizer (H : Set (MulAut (Vtil V₀ V hV))) :=
    hN1A.trans hT.normal
  have hC1 : Subgroup.centralizer (H.subgroupOf N1 : Set ↥N1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxN : (x : MulAut (Vtil V₀ V hV)) ∈ N := hN1N x.2
    have hxK : (x : MulAut (Vtil V₀ V hV)) ∈ K := by
      refine ⟨hNA hxN, ?_⟩
      change (x : MulAut (Vtil V₀ V hV)) ∈
        Subgroup.centralizer (H : Set (MulAut (Vtil V₀ V hV)))
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hxh := (Subgroup.mem_centralizer_iff.1 hx)
        ⟨(h : MulAut (Vtil V₀ V hV)), Subgroup.mem_sup_left hh⟩
        (Subgroup.mem_subgroupOf.2 hh)
      exact congrArg Subtype.val hxh
    have hbot : (x : MulAut (Vtil V₀ V hV)) ∈ (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
      rw [← hNKbot]
      exact ⟨hxN, hxK⟩
    exact Subtype.ext (by simpa using hbot)
  have hTbSylN1 : CFSG.ABGLocalTools.IsSylowOf 2 Tb N1 :=
    hT.sylow.of_le (show Tb ≤ N1 from le_sup_right) hN1A
  obtain ⟨J1, hJ1N1, hTbJ1, hJ1card⟩ :=
    s16t3_exists_sylow_le_alt_seven (L := H) (N := N1) (P := Tb)
      (show H ≤ N1 from le_sup_left) hN1norm e hC1 hTbSylN1
  obtain ⟨YL, hYL⟩ := s16t3_exists_coverL_alt hset h127 h119 hT (Or.inr ⟨e⟩)
  let S : Subgroup G := YL ⊔ D.T
  have hSM : S ≤ D.M := sup_le hYL.1 D.sylowM.le
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hMn : D.M ≤ normalizer (V : Set G) := hMst.trans (stabTil_le_normalizer V₀ V)
  have hSs : S ≤ stabTil V₀ V := hSM.trans hMst
  let φ : ↥S →* MulAut (Vtil V₀ V hV) := (barHom V₀ V hV hMst).comp (Subgroup.inclusion hSM)
  have hφeq : φ = (actTil V₀ V hV).comp (Subgroup.inclusion hSs) := by ext x; rfl
  have hφrange : φ.range = N1 := by
    rw [hφeq, MonoidHom.range_comp, Subgroup.inclusion_range]
    change barSub V₀ V hV S = N1
    rw [show S = YL ⊔ D.T from rfl,
      s16t3_barSub_sup (hYL.1.trans hMst) (D.sylowM.le.trans hMst), hYL.2.2.1]
  have hDTS : D.T ≤ S := le_sup_right
  let T' : Subgroup ↥S := D.T.subgroupOf S
  have hT'2 : IsPGroup 2 ↥T' := D.sylowM.isPGroup.comap_subtype
  have hT'syl : ¬ 2 ∣ T'.index := by
    have hdvd : D.T.relIndex S ∣ D.T.index := Subgroup.relIndex_dvd_index_of_le hDTS
    have hodd : ¬ 2 ∣ D.T.index := by
      have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowG).2.2
      rwa [Subgroup.relIndex_top_right] at h2
    intro hdiv
    exact hodd (hdiv.trans hdvd)
  have hJ1range : J1 ≤ φ.range := by rw [hφrange]; exact hJ1N1
  have hTJ' : T'.map φ ≤ J1 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    rw [hφeq]
    exact hTbJ1 (actTil_mem_barSub V₀ V hV ht (hSs t.2))
  have hφker : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf S := by
    show ((barHom V₀ V hV hMst).comp (Subgroup.inclusion hSM)).ker = _
    rw [← MonoidHom.comap_ker, ker_barHom V₀ V hV hMn hMst,
      Subgroup.comap_inclusion_subgroupOf hSM]
  have hYLnormM : D.M ≤ Subgroup.normalizer (YL : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYL.1).1 hYL.2.1
  have hNnormYL : (YL.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show YL ≤ S from le_sup_left)).2
      (hSM.trans hYLnormM)
  have hkerCard : Nat.card ↥φ.ker = Nat.card ↥(S ⊓ F11.CTilde D.M V₀ V) := by
    rw [hφker, ← Subgroup.inf_subgroupOf_right (F11.CTilde D.M V₀ V) S]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : F11.CTilde D.M V₀ V ⊓ S ≤ S)).toEquiv]
    exact congrArg (fun H : Subgroup G => Nat.card ↥H) (inf_comm (F11.CTilde D.M V₀ V) S)
  have hker23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥φ.ker → p = 2 ∨ p = 3 := by
    intro p hp hpdvd
    have hqH : p ∣ Nat.card ↥(S ⊓ F11.CTilde D.M V₀ V) := by
      rwa [hkerCard] at hpdvd
    refine s16t3_prime_dvd_card_of_sup_of_normal_amb (N := YL) (P := D.T)
      (H := S ⊓ F11.CTilde D.M V₀ V) hNnormYL inf_le_left ?_ D.sylowM.isPGroup hp hqH
    intro q hq hqdvd
    have hEq : YL ⊓ (S ⊓ F11.CTilde D.M V₀ V) = YL ⊓ F11.CTilde D.M V₀ V := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, hx.2.2⟩
      · intro hx
        exact ⟨hx.1, ⟨Subgroup.mem_sup_left hx.1, hx.2⟩⟩
    rw [hEq] at hqdvd
    exact hYL.2.2.2.2.2.2.1 q hq hqdvd
  let ψ : ↥(J1.comap φ) →* ↥J1 :=
    { toFun := fun x => ⟨φ x, x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hψsurj : Function.Surjective ψ := by
    intro j
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 (hJ1range j.2)
    exact ⟨⟨s, by show φ s ∈ J1; rw [hs]; exact j.2⟩, Subtype.ext hs⟩
  have hψker : ψ.ker = φ.ker.subgroupOf (J1.comap φ) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx; exact congrArg Subtype.val hx
    · intro hx; exact Subtype.ext hx
  have hψcard : Nat.card ↥ψ.ker * Nat.card ↥J1 = Nat.card ↥(J1.comap φ) :=
    Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψsurj
  have hkerle : φ.ker ≤ J1.comap φ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact J1.one_mem
  have hkerCard' : Nat.card ↥ψ.ker = Nat.card ↥φ.ker := by
    rw [hψker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
  have hcard : Nat.card ↥(J1.comap φ) = Nat.card ↥φ.ker * Nat.card ↥J1 := by
    rw [← hψcard, hkerCard']
  have hJ1cardPow : ∃ x : ℕ, Nat.card ↥J1 = 2 ^ x * 3 ^ 2 := by
    obtain ⟨x, hx⟩ := hT.sylow.isPGroup.exists_card_eq
    refine ⟨x, ?_⟩
    rw [hJ1card, hx, show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.mul_comm]
  obtain ⟨xJ, hJ1card'⟩ := hJ1cardPow
  have hcomap23 : ∀ p : ℕ, p.Prime →
      p ∣ Nat.card ↥(J1.comap φ) → p = 2 ∨ p = 3 := by
    intro p hp hpdvd
    rw [hcard] at hpdvd
    rcases hp.dvd_mul.1 hpdvd with h | h
    · exact hker23 p hp h
    · rw [hJ1card'] at h
      rcases hp.dvd_mul.1 h with h2 | h3
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      · right
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
  haveI : Nonempty ↥(J1.comap φ) := ⟨1⟩
  have hn0 : Nat.card ↥(J1.comap φ) ≠ 0 := Nat.card_pos.ne'
  have hxy : Nat.card ↥(J1.comap φ) =
      2 ^ (Nat.card ↥(J1.comap φ)).factorization 2 *
        3 ^ (Nat.card ↥(J1.comap φ)).factorization 3 :=
    s16t3_eq_two_pow_mul_three_pow hn0 hcomap23
  have h3dvd : 3 ^ 2 ∣ Nat.card ↥(J1.comap φ) := by
    rw [hcard, hJ1card']
    exact dvd_mul_of_dvd_right (dvd_mul_left (3 ^ 2) (2 ^ xJ)) _
  have h3y : 2 ≤ (Nat.card ↥(J1.comap φ)).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn0).mp h3dvd
  obtain ⟨Y', hY'3, hY'card, hY'perm, hY'map⟩ :=
    s16t3_exists_permuting_three_of_two_three φ hT'2 hT'syl hTJ' hxy
  let Y : Subgroup G := Y'.map S.subtype
  have hYM : Y ≤ D.M := (Subgroup.map_subtype_le Y').trans hSM
  have hY3 : IsPGroup 3 ↥Y := hY'3.map S.subtype
  have hYcard : Nat.card ↥Y = 3 ^ (Nat.card ↥(J1.comap φ)).factorization 3 := by
    show Nat.card ↥(Y'.map S.subtype) = _
    rw [Subgroup.card_map_of_injective S.subtype_injective, hY'card]
  have hYS : Y ≤ YL ⊔ D.T := Subgroup.map_subtype_le Y'
  have hbarY : barSub V₀ V hV Y = Y'.map φ := by
    show barSub V₀ V hV (Y'.map S.subtype) = Y'.map φ
    rw [s16t3_barSub_map_subtype hSs Y', hφeq]
  have hYJ : barSub V₀ V hV Y ≤ J1 := by
    rw [hbarY]
    exact Subgroup.map_le_iff_le_comap.mpr hY'map
  have hDTnormYL : D.T ≤ Subgroup.normalizer (YL : Set G) := D.sylowM.le.trans hYLnormM
  have hYleYL : Y ≤ YL :=
    s16t3_le_of_isPGroup_three hDTnormYL D.sylowM.isPGroup hY3 hYS
  have hYexp : ∀ y ∈ Y, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨n, hn⟩ := hY3 ⟨y, hy⟩
    have hyn : y ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hyYL : y ∈ YL := hYleYL hy
    have hyM : y ∈ D.M := hYL.1 hyYL
    have hbar_mem : barHom V₀ V hV hMst ⟨y, hyM⟩ ∈ J1 := by
      apply hYJ
      exact actTil_mem_barSub V₀ V hV (X := Y) hy (hSs (hYS hy))
    have hbar3pow : (barHom V₀ V hV hMst ⟨y, hyM⟩) ^ 3 ^ n = 1 := by
      have hsub : (⟨y, hyM⟩ : ↥D.M) ^ 3 ^ n = 1 := Subtype.ext (by simpa using hyn)
      rw [← map_pow, hsub, map_one]
    have hP : IsPGroup 3 ↥(Subgroup.zpowers (barHom V₀ V hV hMst ⟨y, hyM⟩)) := by
      refine IsPGroup.of_card_dvd_pow (n := n) ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.2 hbar3pow
    have hzle : Subgroup.zpowers (barHom V₀ V hV hMst ⟨y, hyM⟩) ≤ H ⊔ Tb :=
      Subgroup.zpowers_le.mpr (hJ1N1 hbar_mem)
    have hzH : Subgroup.zpowers (barHom V₀ V hV hMst ⟨y, hyM⟩) ≤ H :=
      s16t3_le_of_isPGroup_three (hT.sylow.le.trans hT.normal) hT.sylow.isPGroup hP hzle
    have hbarH : barHom V₀ V hV hMst ⟨y, hyM⟩ ∈ H := hzH (Subgroup.mem_zpowers _)
    let nH : ↥H := ⟨barHom V₀ V hV hMst ⟨y, hyM⟩, hbarH⟩
    have hnbar : barHom V₀ V hV hMst ⟨y, hYL.1 hyYL⟩ = (nH : MulAut (Vtil V₀ V hV)) := rfl
    have hdvd : orderOf (((e nH : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) ∣ 3 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      have h1 : nH ^ 3 ^ n = 1 := Subtype.ext (by simpa using hbar3pow)
      calc ((e nH : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) ^ 3 ^ n
          = ((e (nH ^ 3 ^ n) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
            rw [map_pow, ← Subgroup.coe_pow]
        _ = 1 := by rw [h1, map_one]; rfl
    have hcyc : ((e nH : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).cycleType = 0 ∨
        ((e nH : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).cycleType = {3} ∨
        ((e nH : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).cycleType = {3, 3} := by
      refine s16t3_cycleType_of_isPGroup_three (n := 7) (by norm_num) _ ?_
      rw [IsPGroup.iff_card]
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      exact ⟨k, by rw [Nat.card_zpowers]; exact hk⟩
    exact s16t3_cube_of_cover_alt hset (Or.inr rfl) e hYL hyYL hyn (n := nH) hnbar hcyc
  have h9 : 9 ≤ Nat.card ↥Y := by
    rw [hYcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (Nat.card ↥(J1.comap φ)).factorization 3 :=
          Nat.pow_le_pow_right (by norm_num) h3y
  have hYnc : ¬ IsCyclic ↥Y := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Y)
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      show (g : G) ^ 3 = 1
      exact hYexp (g : G) g.2
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hg3
    have hdvd' : 3 ^ (Nat.card ↥(J1.comap φ)).factorization 3 ∣ 3 := by
      rw [hg, hYcard] at hdvd
      exact hdvd
    have hle : 3 ^ (Nat.card ↥(J1.comap φ)).factorization 3 ≤ 3 :=
      Nat.le_of_dvd (by norm_num) hdvd'
    have h9' : 9 ≤ 3 ^ (Nat.card ↥(J1.comap φ)).factorization 3 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (Nat.card ↥(J1.comap φ)).factorization 3 :=
            Nat.pow_le_pow_right (by norm_num) h3y
    omega
  have hperm : Permutes Y D.T := by
    show (Y : Set G) * (D.T : Set G) = (D.T : Set G) * (Y : Set G)
    have hYcoe : (Y : Set G) = S.subtype '' (Y' : Set ↥S) := by
      change (Y'.map S.subtype : Set G) = S.subtype '' (Y' : Set ↥S)
      rw [Subgroup.coe_map]
    have hTmapS : T'.map S.subtype = D.T := Subgroup.map_subgroupOf_eq_of_le hDTS
    have hTcoe : (D.T : Set G) = S.subtype '' (T' : Set ↥S) := by
      rw [← hTmapS, Subgroup.coe_map]
    rw [hYcoe, hTcoe, ← Set.image_mul, ← Set.image_mul, hY'perm]
  exact ⟨Y, hYM, hY3, hYexp, hYnc, hperm, h9⟩

theorem s168e3_exists_permuting_three_alt_seven_k7
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hA7 : UC22.IsAlt ↥(lBar V₀ V hV L) 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ IsPGroup 3 ↥Y ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ ¬ IsCyclic ↥Y ∧
      Permutes Y D.T ∧ 9 ≤ Nat.card ↥Y :=
  s16t3_exists_permuting_three_alt_seven_k7 c.setting c.std.h127 c.std.h119
    hT h7 hA7 hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
