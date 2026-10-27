module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessChain
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofHess
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddModel
public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec14.Res8Hess
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)
open CFSG.Open (pCoreOf)

variable {X : Type} [Group X] [Finite X]

section General

theorem three_lt_of_isoLThreePi {p e : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) (hp2 : p ≠ 2)
    (hiso : Sec4.IsoLThreePi X p e) : 3 < p := by
  have hmod : p ^ e % 3 ≠ 0 := by
    rcases hiso with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    apply hmod
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ, Nat.mul_mod_left]
  have := hp.out.two_le
  have : p ≠ 2 := hp2
  by_contra h
  interval_cases p <;> simp_all

theorem pCoreOf_two_le_theta (C : Subgroup X) :
    pCoreOf 2 C ≤ CFSG.inSubgroup (aschbacherSolvableCore 3) C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (pCoreOf 2 C) := (CFSG.pCore_isPGroup (p := 2) (G := ↥C)).map C.subtype
  refine le_theta_of_normal (Subgroup.map_subtype_le _) ?_ ?_ ?_
  · intro g hg v hv
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * v' * ⟨g, hg⟩⁻¹,
      (inferInstance : (CFSG.pCore 2 ↥C).Normal).conj_mem v' hv' ⟨g, hg⟩, rfl⟩
  · haveI := hp.isNilpotent
    infer_instance
  · obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

theorem le_pCoreOf_two_of_le_theta (C : Subgroup X)
    (hθ : ∀ a ∈ CFSG.inSubgroup (aschbacherSolvableCore 3) C,
      ∀ b ∈ CFSG.inSubgroup (aschbacherSolvableCore 3) C, a * b = b * a)
    {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hSθ : S ≤ CFSG.inSubgroup (aschbacherSolvableCore 3) C) : S ≤ pCoreOf 2 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := CFSG.inSubgroup (aschbacherSolvableCore 3) C with hθdef
  set N := layer θ hθ (Nat.card θ) with hN
  have hθC : θ ≤ C := Subgroup.map_subtype_le _
  have hNC : N ≤ C := (layer_le θ hθ _).trans hθC
  have hNp : IsPGroup 2 N := fun x => ⟨Nat.card θ, Subtype.ext (by
    rw [Subgroup.coe_pow, x.2.2, Subgroup.coe_one])⟩
  have hNn : (N.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNC]
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    refine ⟨Sec12.conj_mem_inSubgroup_theta (Subgroup.le_normalizer hg) hn.1, ?_⟩
    rw [conj_pow, hn.2, mul_one, mul_inv_cancel]
  have hSN : S ≤ N := by
    intro s hs
    refine ⟨hSθ hs, ?_⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS2) ⟨s, hs⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    refine pow_dvd_pow 2 ?_
    have h1 : 2 ^ k ≤ Nat.card θ := by
      rw [← hk, ← Subgroup.orderOf_mk s (hSθ hs)]
      exact Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard _)
    have h2 : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  exact hSN.trans (CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hNC hNn hNp)

theorem card_le_four_of_isElemAbelian_two {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hp2 : p ≠ 2)
    (hiso : Sec4.IsoLThreePi X p e) {V : Subgroup X} (hV : CFSG.Open.IsElemAbelian 2 V) :
    Nat.card V ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr := Sec14.Ronan148T.oddTwoRank X p e hp2 he hiso V
  have hp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hEtop : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup V) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x _ => Subtype.ext (by
      simpa using hV.2 _ x.2)⟩
    exact congrArg Subtype.val (hV.1.is_comm.comm (a : V) (b : V))
  have hk' : Nat.card (⊤ : Subgroup V) = 2 ^ k := by rw [Subgroup.card_top, hk]
  have hk2 := CFSG.SectionRank.le_pRank Nat.one_lt_two (le_refl (⊤ : Subgroup V)) hEtop hk'
  have hk3 : k ≤ 2 := hk2.trans hr
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 4 := by norm_num

end General

section Hessian

variable {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hp2 : p ≠ 2) (hiso : Sec4.IsoLThreePi X p e)
  {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
  (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
    ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
include he hp2 hiso hEe hE9 htr

theorem thetaC_comm_of_hessian {b : X} (hbE : b ∈ E) (hb1 : b ≠ 1) :
    ∀ x ∈ thetaC b, ∀ y ∈ thetaC b, x * y = y * x := by
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    exists_hessian_equiv he hiso hEe hE9 htr
  have := hK.finite
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) := by
    unfold Matrix.ProjGenLinGroup
    infer_instance
  have hd1 : dM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hdo
    omega
  have hb' : Φ.symm b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM := by
    rw [← hΦE] at hbE
    obtain ⟨w, hw, rfl⟩ := hbE
    simpa using hw
  have hb1' : Φ.symm b ≠ 1 := fun h => hb1 (by rw [← Φ.apply_symm_apply b, h, map_one])
  have hcomm := thetaC_comm hK hp2 hτ hτ1 hq hdM hcM hd1 hb' hb1'
  have hmap : (thetaC (Φ.symm b)).map Φ.toMonoidHom = thetaC b := by
    rw [thetaC_map_equiv, MulEquiv.apply_symm_apply]
  intro x hx y hy
  rw [← hmap] at hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  change Φ x' * Φ y' = Φ y' * Φ x'
  rw [← map_mul, ← map_mul, hcomm x' hx' y' hy']

theorem hessU_exists {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hES : E ≤ Subgroup.normalizer (S : Set X)) :
    ∃ b ∈ E, b ≠ 1 ∧ S ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS3 : ¬ 3 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  obtain ⟨b, hbE, hb1, hSb⟩ := le_thetaC_of_transitive he (three_lt_of_isoLThreePi he hp2 hiso)
    hiso hEe hE9 htr hS3 hES
  exact ⟨b, hbE, hb1, le_pCoreOf_two_of_le_theta _
    (thetaC_comm_of_hessian he hp2 hiso hEe hE9 htr hbE hb1) hS2 hSb⟩

theorem hessU_comm {b : X} (hbE : b ∈ E) (hb1 : b ≠ 1) :
    ∀ x ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)),
      ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)), x * y = y * x := fun x hx y hy =>
  thetaC_comm_of_hessian he hp2 hiso hEe hE9 htr hbE hb1 x (pCoreOf_two_le_theta _ hx) y
    (pCoreOf_two_le_theta _ hy)

theorem hessU_fixed {b c : X} (hbE : b ∈ E) (hb1 : b ≠ 1) (hcE : c ∈ E)
    (hcb : c ∉ Subgroup.zpowers b) :
    ∀ u ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)), c * u * c⁻¹ = u → u = 1 := by
  intro u hu hcu
  by_contra hu1
  apply hcb
  refine Sec14.Proof1413Res7.mem_zpowers_of_mem_thetaC he hiso hEe hE9 htr hbE hb1
    (pCoreOf_two_le_theta _ hu) hu1 hcE ?_
  calc u * c = c * u * c⁻¹ * c := by rw [hcu]
    _ = c * u := by group

theorem hessU_card_layer_one {b : X} (hbE : b ∈ E) (hb1 : b ≠ 1) :
    Nat.card (layer (pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
      (hessU_comm he hp2 hiso hEe hE9 htr hbE hb1) 1) ≤ 4 := by
  refine card_le_four_of_isElemAbelian_two he hp2 hiso ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · exact hessU_comm he hp2 hiso hEe hE9 htr hbE hb1 x (layer_le _ _ _ x.2) y
      (layer_le _ _ _ y.2)
  · intro x hx
    simpa using hx.2

theorem hessU_conj_mem {b c : X} (hbE : b ∈ E) (hcE : c ∈ E) :
    ∀ u ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)),
      c * u * c⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)) := by
  have hcC : c ∈ Subgroup.centralizer ({b} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨c, hcE⟩ ⟨b, hbE⟩)
  intro u hu
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hu
  exact Subgroup.mem_map.mpr ⟨⟨c, hcC⟩ * u' * ⟨c, hcC⟩⁻¹,
    (inferInstance : (CFSG.pCore 2 ↥(Subgroup.centralizer ({b} : Set X))).Normal).conj_mem u'
      hu' ⟨c, hcC⟩, rfl⟩

theorem exists_mem_not_mem_zpowers_of_hessian {b : X} (hbE : b ∈ E) :
    ∃ c ∈ E, c ∉ Subgroup.zpowers b := by
  by_contra h
  push Not at h
  have hle : E ≤ Subgroup.zpowers b := h
  have h1 := Subgroup.card_le_of_le hle
  rw [hE9, Nat.card_zpowers] at h1
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hEe.2 b hbE))
  omega

theorem hessU_layer_data {b : X} (hbE : b ∈ E) (hb1 : b ≠ 1) :
    IsPGroup 2 (pCoreOf 2 (Subgroup.centralizer ({b} : Set X))) ∧
      ∃ c ∈ E, (∀ u ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)),
        c * u * c⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set X))) ∧
        ∀ u ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)), c * u * c⁻¹ = u → u = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcE, hcb⟩ := exists_mem_not_mem_zpowers_of_hessian he hp2 hiso hEe hE9 htr hbE
  exact ⟨(CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.centralizer ({b} : Set X)))).map _,
    c, hcE, hessU_conj_mem he hp2 hiso hEe hE9 htr hbE hcE,
    hessU_fixed he hp2 hiso hEe hE9 htr hbE hb1 hcE hcb⟩

theorem hessU_layer_one_le {b : X} (hbE : b ∈ E) (hb1 : b ≠ 1) {W : Subgroup X}
    (hWU : W ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
    (hEW : E ≤ Subgroup.normalizer (W : Set X)) (hW1 : W ≠ ⊥) :
    layer (pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
      (hessU_comm he hp2 hiso hEe hE9 htr hbE hb1) 1 ≤ W := by
  obtain ⟨hU2, c, hcE, hcU, hfix⟩ := hessU_layer_data he hp2 hiso hEe hE9 htr hbE hb1
  exact layer_one_le_of_invariant _ _ hU2 hcU hfix
    (hessU_card_layer_one he hp2 hiso hEe hE9 htr hbE hb1) hWU
    (fun w hw => (Subgroup.mem_normalizer_iff.mp (hEW hcE) w).mp hw) hW1

end Hessian

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
