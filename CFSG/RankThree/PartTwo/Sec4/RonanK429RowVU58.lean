module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58Inner
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU58OuterField
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgIso

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)

namespace RowV

open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesU58
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem orderOf_ne_ten_SUI (g : SUI) : orderOf g ≠ 10 := by
  intro h
  have h10 : g ^ 10 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one g
  have h2 : g ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have h5 : g ^ 5 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hU := eq_one_of_commute_of_pow_five' card_K_eq (B := mU (g ^ 2)) (U := mU (g ^ 5))
    (mU_mem _).2 (mU_mem _).1
    (by rw [← mU_pow, ← pow_mul, show 2 * 5 = 10 from rfl, h10, mU_one])
    (fun h => h2 (mU_injective (by rw [h, mU_one])))
    (by rw [← mU_pow, ← pow_mul, show 5 * 2 = 10 from rfl, h10, mU_one])
    (by rw [← mU_mul, ← mU_mul, ← pow_add, ← pow_add, add_comm])
  exact h5 (mU_injective (by rw [hU, mU_one]))

theorem centralizer_sq_eq {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) :
    Subgroup.centralizer ({g ^ 2} : Set G) = Subgroup.centralizer ({g} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : Commute x (g ^ 2) := h
    have e : g = (g ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hg, one_mul]
    have h' := hc.pow_right 2
    rw [← e] at h'
    exact h'
  · intro h
    have hc : Commute x g := h
    exact hc.pow_right 2

theorem false_of_outer {σ : MulAut SUI} (hσ3 : σ ^ 3 = 1)
    (hout : σ ∉ (MulAut.conj : SUI →* MulAut SUI).range) {Q : Subgroup SUI}
    (hQ : Q ≤ autFix σ) [Group.IsPerfect Q] (hT : IsType429 (Q ⧸ CFSG.pCore 2 Q)) : False := by
  obtain ⟨A, hA, φ, hσA, hφk⟩ := exists_unitary_field σ
  have hφ3 : φ ^ 3 = 1 := by
    have h := hφk 1 (by rw [pow_one]; exact hσ3)
    rwa [pow_one] at h
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    obtain ⟨g₀, hg₀⟩ := exists_SUI_conj_eq hA
    apply hout
    refine ⟨g₀, MulEquiv.ext fun x => Subtype.ext ?_⟩
    have h1 : glAut 1 ((x : SUI) : GL (Fin 5) K) = ((x : SUI) : GL (Fin 5) K) := by
      rw [map_one]
      rfl
    rw [MulAut.conj_apply, hσA x, h1, hg₀]
    simp
  have hφform : (∀ x : K, φ x = x ^ 4) ∨ ∀ x : K, φ x = x ^ 16 := by
    obtain ⟨σf, hσf, hord, hzp⟩ := RonanK432.exists_frob_gen
    haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [card_ringAut_K]; norm_num)
    have hφmem : φ ∈ Submonoid.powers σf := by
      rw [mem_powers_iff_mem_zpowers, hzp]
      exact Subgroup.mem_top φ
    obtain ⟨n, hn⟩ := hφmem
    have hn' : σf ^ n = φ := hn
    have h6 : σf ^ (3 * n) = 1 := by rw [pow_mul', hn', hφ3]
    have hdvd : 6 ∣ 3 * n := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one h6
    have hφ : σf ^ (n % 6) = φ := by rw [← hord, pow_mod_orderOf, hn']
    have hn6 : n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4 := by omega
    rcases hn6 with h0 | h2 | h4
    · exfalso
      rw [h0, pow_zero] at hφ
      exact hφ1 hφ.symm
    · left
      intro x
      rw [← hφ, h2, RonanK432.frob_pow_apply hσf]
      norm_num
    · right
      intro x
      rw [← hφ, h4, RonanK432.frob_pow_apply hσf]
      norm_num
  have hno7 : ∀ t : SUI, σ t = t → t ^ 7 = 1 → t = 1 := by
    intro t hσt ht7
    have h := hσA t
    rw [hσt] at h
    have h2 : ((t : SUI) : GL (Fin 5) K) * A = A * glAut φ ((t : SUI) : GL (Fin 5) K) := by
      calc ((t : SUI) : GL (Fin 5) K) * A =
            (A * glAut φ ((t : SUI) : GL (Fin 5) K) * A⁻¹) * A := by rw [← h]
        _ = A * glAut φ ((t : SUI) : GL (Fin 5) K) := by group
    have hAB := congrArg (fun X : GL (Fin 5) K => (X : Matrix (Fin 5) (Fin 5) K)) h2
    simp only [Units.val_mul, coe_glAut] at hAB
    apply mU_injective
    rw [mU_one]
    exact eq_one_of_twisted_pow_seven' card_K_eq (A := (A : Matrix (Fin 5) (Fin 5) K))
      (B := mU t) φ.toRingHom hφform (Units.isUnit A) hAB.symm (mU_mem t).2
      (by rw [← mU_pow, ht7, mU_one])
  have hQ7 : ∀ g : Q, g ^ 7 = 1 → g = 1 := fun g hg =>
    Subtype.ext (hno7 g (mem_autFix.mp (hQ g.2)) (by simpa using congrArg Subtype.val hg))
  have hQd : Nat.card Q ∣ 95033953989081169920 := by
    have h7 : ¬ 7 ∣ Nat.card Q := by
      intro h
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h
      have h1 := hQ7 g (by rw [← hg]; exact pow_orderOf_eq_one g)
      rw [h1, orderOf_one] at hg
      norm_num at hg
    have hcop : Nat.Coprime (Nat.card Q) 49 :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7).symm
    have hd : Nat.card Q ∣ 49 * 95033953989081169920 := by
      have h := Subgroup.card_subgroup_dvd_card Q
      rw [card_SUI] at h
      norm_num at h ⊢
      exact h
    exact hcop.dvd_of_dvd_mul_left hd
  have hX := isType429_m12_of_dvd (N := 95033953989081169920) (B := 361) (by norm_num)
    ((Subgroup.card_quotient_dvd_card _).trans hQd) (by norm_num) (by decide +kernel)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hT
  obtain ⟨ψ⟩ := hX
  obtain ⟨x0, hx0⟩ := exists_orderOf_ten_M12
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (ψ.symm x0)
  have h10 : 10 ∣ orderOf q := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 Q)) q
    rw [QuotientGroup.mk'_apply, hq, MulEquiv.orderOf_eq, hx0] at h
    exact h
  obtain ⟨m, hm⟩ := h10
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := orderOf_pos q
    omega
  have hord : orderOf (q ^ m) = 10 := by
    rw [orderOf_pow_of_dvd hm0 ⟨10, by rw [hm, mul_comm]⟩, hm, Nat.mul_div_cancel _ (by omega)]
  apply orderOf_ne_ten_SUI (q ^ m : Q)
  rw [Subgroup.orderOf_coe]
  exact hord

theorem noCfgS429_SUI : NoCfgS429 SUI := by
  intro A σ Q hc
  have hσ3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  haveI : Group.IsPerfect Q := hc.isPerfect
  by_cases hin : σ ∈ (MulAut.conj : SUI →* MulAut SUI).range
  · obtain ⟨s, rfl⟩ := hin
    have hs3 : s ^ 3 = 1 := by
      have h3' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow]; exact hσ3
      have hmem : s ^ 3 ∈ Subgroup.center SUI := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h := congrArg (fun τ : MulAut SUI => τ g) h3'
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [h]
          _ = s ^ 3 * g := by group
      rw [center_SUI, Subgroup.mem_bot] at hmem
      exact hmem
    have hs1 : s ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
    obtain ⟨x, v, hv⟩ := exists_conj_mem_A0 hs3
    have hv0 : Multiplicative.toAdd v ≠ 0 := by
      intro h0
      apply hs1
      have hv1 : v = 1 := Multiplicative.toAdd.injective h0
      rw [hv1, map_one] at hv
      have e : s = x⁻¹ * (x * s * x⁻¹) * x := by group
      rw [e, ← hv]
      group
    obtain ⟨π, -, i, hπ⟩ := exists_perm_std _ hv0
    set ψ : SUI ≃* SUI := (MulAut.conj x).trans (reindexSU π) with hψ
    have hψs : ψ s = bs i ∨ ψ s = bs i ^ 2 := by
      have e : ψ s = reindexSU π (δ (Multiplicative.ofAdd (Multiplicative.toAdd v))) := by
        rw [hψ, MulEquiv.trans_apply, MulAut.conj_apply, ← hv]
        rfl
      rw [e, reindexSU_δ]
      rcases hπ with h | h
      · left
        rw [h, res3_ext3]
      · right
        rw [h, res3_ext3, δ_two_smul]
    have hcent : Subgroup.centralizer ({ψ s} : Set SUI) =
        Subgroup.centralizer ({bs i} : Set SUI) := by
      rcases hψs with h | h
      · rw [h]
      · rw [h, centralizer_sq_eq (δ_pow_three _)]
    have hc' := hc.map ψ
    rw [Res423Two.mulAut_congr_conj] at hc'
    have hQ' : Q.map ψ.toMonoidHom ≤ Subgroup.centralizer ({bs i} : Set SUI) := by
      rw [← hcent, ← autFix_conj_eq_centralizer]
      exact hc'.le_autFix
    have hsn' : ((Q.map ψ.toMonoidHom).subgroupOf
        (Subgroup.centralizer ({bs i} : Set SUI))).IsSubnormal := by
      have h := hc'.isSubnormal
      rwa [autFix_conj_eq_centralizer, hcent] at h
    haveI := hc'.isPerfect
    have hT' := hc'.isType
    rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) i with rfl | rfl | rfl | rfl
    · exact false_of_bs0 hQ' hsn' hT'
    · exact false_of_bs1 hQ' hsn' hT'
    · exact false_of_bs2 hQ' hT'
    · exact false_of_bs3 hQ' hsn' hT'
  · exact false_of_outer hσ3 hin hc.le_autFix hc.isType

theorem noCfgS429_projSU_five_eight : NoCfgS429 (projSU 5 2 3) :=
  NoCfgS429.of_mulEquiv equivSUI noCfgS429_SUI

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
