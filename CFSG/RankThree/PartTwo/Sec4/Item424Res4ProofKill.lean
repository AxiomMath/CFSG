module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofField
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item424Res4

theorem pow_three_eq_one_of_mem_closure {M : Type*} [Group M] {a b : M} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) {g : M} (hg : g ∈ Subgroup.closure ({a, b} : Set M)) :
    g ^ 3 = 1 := by
  have hpair : ({a, b} : Set M).Pairwise Commute := by
    rintro u (rfl | rfl) v (rfl | rfl) -
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hcomm := Subgroup.isMulCommutative_closure hpair
  induction hg using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | rfl
    · exact ha
    · exact hb
  | one => exact one_pow 3
  | mul u v hu hv hu3 hv3 =>
    have huv : Commute u v := congrArg Subtype.val (hcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    rw [huv.mul_pow, hu3, hv3, one_mul]
  | inv u hu hu3 => rw [inv_pow, hu3, inv_one]

theorem not_isType424_of_e9 {Γ : Type} [Group Γ] [Finite Γ] {L : Subgroup Γ}
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)) {x y : Γ} (hxL : x ∈ L)
    (hyL : y ∈ L) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hyx : y ∉ Subgroup.zpowers x) : ¬ Sec11.IsType424 (L ⧸ aschbacherSolvableCore 3 L) := by
  intro hT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set xl : L := ⟨x, hxL⟩ with hxl
  set yl : L := ⟨y, hyL⟩ with hyl
  have hxl3 : xl ^ 3 = 1 := Subtype.ext (by simpa [hxl] using hx3)
  have hyl3 : yl ^ 3 = 1 := Subtype.ext (by simpa [hyl] using hy3)
  have hxyl : xl * yl = yl * xl := Subtype.ext hxy
  have hθ : ∀ l : L, l ^ 3 = 1 → π l = 1 → l = 1 := fun l hl h1 => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Sec11.eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1) (by simpa using hl)
  set xb := π xl with hxb
  set yb := π yl with hyb
  have hxb1 : xb ≠ 1 := fun h => hx1 (congrArg Subtype.val (hθ xl hxl3 h))
  have hyb1 : yb ≠ 1 := fun h => hyx (by
    have h' : y = 1 := congrArg Subtype.val (hθ yl hyl3 h)
    rw [h']
    exact Subgroup.one_mem _)
  have hxb3 : xb ^ 3 = 1 := by rw [hxb, ← map_pow, hxl3, map_one]
  have hyb3 : yb ^ 3 = 1 := by rw [hyb, ← map_pow, hyl3, map_one]
  have hxyb : xb * yb = yb * xb := by rw [hxb, hyb, ← map_mul, hxyl, map_mul]
  have hP : IsPGroup 3 (Subgroup.closure ({xb, yb} : Set (L ⧸ aschbacherSolvableCore 3 L))) :=
    fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_three_eq_one_of_mem_closure hxyb hxb3 hyb3 g.2)⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hSc : IsCyclic S := Sec11.KS11LieProof.isCyclic_sylow_three_of_isType424 hT hLq S
  have hxS : xb ∈ S := hS (Subgroup.subset_closure (by simp))
  have hyS : yb ∈ S := hS (Subgroup.subset_closure (by simp))
  have hox : orderOf xb = 3 := orderOf_eq_prime hxb3 hxb1
  have hoy : orderOf yb = 3 := orderOf_eq_prime hyb3 hyb1
  have hzS : Subgroup.zpowers (⟨xb, hxS⟩ : S) = Subgroup.zpowers ⟨yb, hyS⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hox, hoy]
  have hyx' : (⟨yb, hyS⟩ : S) ∈ Subgroup.zpowers ⟨xb, hxS⟩ := by
    rw [hzS]
    exact Subgroup.mem_zpowers _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hyx'
  have hi' : xb ^ i = yb := congrArg Subtype.val hi
  have hw3 : (yl * (xl ^ i)⁻¹) ^ 3 = 1 := by
    have hc : Commute yl (xl ^ i)⁻¹ := ((Commute.zpow_right hxyl.symm i).inv_right)
    have hxi3 : (xl ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxl3, one_zpow]
    rw [hc.mul_pow, inv_pow, hxi3, inv_one, mul_one, hyl3]
  have hw1 : π (yl * (xl ^ i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, ← hxb, ← hyb, hi', mul_inv_cancel]
  have h5 := hθ _ hw3 hw1
  rw [mul_inv_eq_one] at h5
  have h6 : y = x ^ i := by
    have h7 := congrArg Subtype.val h5
    simpa [hxl, hyl] using h7
  exact hyx (h6 ▸ Subgroup.zpow_mem_zpowers x i)

theorem not_hasType424_of_quasisimple {Γ : Type} [Group Γ] [Finite Γ] (N : Subgroup Γ)
    (hN : CFSG.IsQuasisimple N) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ N) {x y : Γ}
    (hxN : x ∈ N) (hyN : y ∈ N) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x) :
    ¬ Sec11.KS11Lie2Proof.HasType424 Γ := by
  rintro ⟨L, ⟨hLp, hLsn, hLq⟩, hT⟩
  have hLN : L ≤ N := by
    have h1 : ⁅L, L⁆ = L := Subgroup.commutator_eq_self
    rw [← h1, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b
  have hsn : (L.subgroupOf N).IsSubnormal := hLsn.subgroupOf
  have hNL : N ≤ L := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hN hsn with
      htop | hcen
    · intro n hn
      have h2 : (⟨n, hn⟩ : N) ∈ L.subgroupOf N := htop ▸ Subgroup.mem_top _
      exact h2
    · exfalso
      have hcL : ⁅L, L⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha b hb
        have h2 : (⟨a, hLN ha⟩ : N) ∈ Subgroup.center N := hcen ha
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h2 ⟨b, hLN hb⟩)
      have hL1 : L = ⊥ := by
        rw [← hcL]
        exact Subgroup.commutator_eq_self.symm
      have hall : ∀ w : L, w = 1 := fun w => Subtype.ext (by
        have hw : (w : Γ) ∈ (⊥ : Subgroup Γ) := hL1 ▸ w.2
        simpa using hw)
      obtain ⟨u, v, huv⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hLq).exists_pair_ne
      obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
      rw [hall u', hall v'] at huv
      exact huv rfl
  exact not_isType424_of_e9 hLq (hNL hxN) (hNL hyN) hx1 hx3 hy3 hxy hyx hT

theorem not_isType424_of_inducedAut_eq {G : Type} [Group G] [Finite G] {M : Type} [Group M]
    {L K : Subgroup G} {c : G} (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)))
    {d φ : MulAut M} (hτ : KFacts.inducedAutHom L e ⟨c, hcN⟩ = d * φ * d⁻¹)
    (hφ : ¬ Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub φ)) :
    ¬ Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K) := by
  intro hT
  have : Finite M := Finite.of_equiv _ e.toEquiv
  have h1 := (Item424Res2.hasType424_fixSub_of_mem hcN hc3 hK hT).of_mulEquiv
    (Sec11.KS11Lie2Proof.fixSubCongr e (Item426.thetaAut L hcN))
  have h2 : MulAut.congr e (Item426.thetaAut L hcN) = MulAut.congr d φ := by
    have h3 : MulAut.congr e (Item426.thetaAut L hcN) = KFacts.inducedAutHom L e ⟨c, hcN⟩ := rfl
    rw [h3, hτ]
    ext m
    rfl
  rw [h2] at h1
  exact hφ (h1.of_mulEquiv (Sec11.KS11Lie2Proof.fixSubCongr d φ).symm)

end Item424Res4

end CFSG.RankThree.PartTwo.Sec4
