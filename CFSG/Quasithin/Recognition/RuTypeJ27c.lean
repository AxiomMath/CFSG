module

public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import Certificates.Certificate17033
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Recognition.RuTypeJ27a

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

namespace Sigma

theorem fix_order_five : ∀ g : SigmaL2F4, (g ^ 5 = 1 ∧ g ≠ 1) →
    ∀ v : Fin 2 → F4, sigmaAct g v = v → v = 0 :=
  Certificates.certificate17033.1

theorem card_centralizer_five : ∀ t : SigmaL2F4, (t ^ 5 = 1 ∧ t ≠ 1) →
    Fintype.card {g : SigmaL2F4 // g * t = t * g} = 5 :=
  Certificates.certificate17033.2

end Sigma

theorem le_eight_of_dvd_forty {k : ℕ} (h : 2 ^ k ∣ 40) : 2 ^ k ≤ 8 := by
  have hk : k ≤ 3 := by
    by_contra hk
    push Not at hk
    have := (pow_dvd_pow 2 hk).trans h
    norm_num at this
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk
    _ = 8 := by norm_num

variable {G : Type} [Group G]

noncomputable abbrev G5 (b : G) : Subgroup G := Subgroup.centralizer ({b} : Set G)

theorem mem_G5 {b x : G} : x ∈ G5 b ↔ x * b = b * x := Subgroup.mem_centralizer_singleton_iff

theorem pow_five_of_orderOf {b : G} (hb5 : orderOf b = 5) : b ^ 5 = 1 := by
  rw [← hb5]; exact pow_orderOf_eq_one b

noncomputable abbrev O5 (b : G) : Subgroup (G5 b) := CFSG.oddCore (G5 b)

theorem O5_odd [Finite G] (b : G) : Odd (Nat.card (O5 b)) :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := G5 b)

namespace RuDataM

variable (M : RuDataM G) [Finite G]

noncomputable abbrev T5 (b : G) : Subgroup G := ruQ M.T ⊓ G5 b

noncomputable abbrev CH5 (b : G) : Subgroup G := ruH M.T ⊓ G5 b

omit [Finite G] in
theorem T5_le_CH5 {b : G} : M.T5 b ≤ M.CH5 b := fun _ hx => ⟨pCoreOf_le 2 _ hx.1, hx.2⟩

omit [Finite G] in
theorem T5_le_G5 {b : G} : M.T5 b ≤ G5 b := inf_le_right

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem φ_b_props : M.φ ⟨b, hbH⟩ ^ 5 = 1 ∧ M.φ ⟨b, hbH⟩ ≠ 1 := by
  refine ⟨?_, fun h1 => ?_⟩
  · rw [← map_pow]
    have : (⟨b, hbH⟩ : ruH M.T) ^ 5 = 1 := Subtype.ext (by simpa using pow_five_of_orderOf hb5)
    rw [this, map_one]
  · have hk : (⟨b, hbH⟩ : ruH M.T) ∈ M.φ.ker := h1
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    have h2 : orderOf b ∣ 2 ^ 11 := by
      rw [← M.toRuData.card_Q]
      exact Subgroup.orderOf_dvd_natCard _ hk
    rw [hb5] at h2
    norm_num at h2

omit hb5 in
theorem z_mem_G5 : M.z ∈ G5 b := by
  rw [mem_G5]
  exact (M.Z_comm_H M.z_mem_Z hbH)

omit hb5 in
theorem z_mem_T5 : M.z ∈ M.T5 b :=
  ⟨M.U_le_Q (M.V_le_U M.z_mem_V), z_mem_G5 hbH⟩

theorem T5_le_HC : M.T5 b ≤ M.HC := by
  rintro q ⟨hq, hqb⟩
  replace hqb : q * b = b * q := mem_G5.mp hqb
  have e := M.ψQ_conj ⟨b, hbH⟩ ⟨q, hq⟩
  have hbq : (⟨b * q * b⁻¹, M.conj_mem_Q hbH hq⟩ : ruQ M.T) = ⟨q, hq⟩ :=
    Subtype.ext (by
      show b * q * b⁻¹ = q
      rw [← hqb, mul_inv_cancel_right])
  rw [hbq] at e
  have h0 := Sigma.fix_order_five _ (φ_b_props hbH hb5) _ e.symm
  have h1 : M.ψQ ⟨q, hq⟩ = 1 := Multiplicative.toAdd.injective h0
  have hk : (⟨q, hq⟩ : ruQ M.T) ∈ M.ψQ.ker := h1
  rw [M.ψQ_ker, Subgroup.mem_subgroupOf] at hk
  exact hk

theorem mem_Z_of_T5_U
    {x : G} (hx : x ∈ M.T5 b) (hU : x ∈ ruU M.L M.T) : x ∈ ruZ M.T := by
  have hxb := (mem_G5.mp hx.2)
  have e := M.ψU_conj ⟨b, hbH⟩ ⟨x, hU⟩
  have hbx : (⟨b * x * b⁻¹, M.conj_mem_U hbH hU⟩ : ruU M.L M.T) = ⟨x, hU⟩ :=
    Subtype.ext (by
      show b * x * b⁻¹ = x
      rw [← hxb, mul_inv_cancel_right])
  rw [hbx] at e
  have h0 := Sigma.fix_order_five _ (φ_b_props hbH hb5) _ e.symm
  have h1 : M.ψU ⟨x, hU⟩ = 1 := Multiplicative.toAdd.injective h0
  exact (M.ψU_eq_one_iff _).mp h1

theorem b_mem_K : b ∈ M.K := by
  refine M.mem_K_iff.mpr ⟨hbH, ?_⟩
  have h5 : (M.φ ⟨b, hbH⟩).right ^ 5 = 1 := by
    show (SemidirectProduct.rightHom (M.φ ⟨b, hbH⟩)) ^ 5 = 1
    rw [← map_pow, (φ_b_props hbH hb5).1, map_one]
  generalize (M.φ ⟨b, hbH⟩).right = r at h5
  revert r
  decide

theorem card_T5 : Nat.card (M.T5 b) = 8 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hTC := T5_le_HC hbH hb5
  have hUC : ruU M.L M.T ≤ M.HC := M.U_le_HC
  have hUn : ((ruU M.L M.T).subgroupOf M.HC).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact M.conj_mem_U (Subgroup.mem_inf.mp g.2).1 hx
  let f : M.T5 b →* ↥M.HC ⧸ (ruU M.L M.T).subgroupOf M.HC :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hTC)
  have h := Subgroup.card_ker_mul_card_range f
  have hker : Nat.card f.ker = 2 := by
    rw [← M.toRuData.card_Z]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, ?_⟩
        invFun := fun w => ⟨⟨w.1, ⟨M.U_le_Q (M.two.Z_le_U w.2), (mem_G5).mpr
          (M.Z_comm_H w.2 hbH)⟩⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
      exact mem_Z_of_T5_U hbH hb5 x.1.2 hx
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact M.two.Z_le_U w.2
  have hrange : Nat.card f.range = 4 := by
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hbU : ∀ n ∈ ruU M.L M.T, b * n * b⁻¹ ∈ ruU M.L M.T := fun n hn => M.conj_mem_U hbH hn
      have hy : (x : G)⁻¹ * (b * x * b⁻¹) ∈ ruU M.L M.T :=
        M.conj_HC_of_mem_K (b_mem_K hbH hb5) x.2
      have hU5 : ¬ 5 ∣ Nat.card (ruU M.L M.T) := by rw [M.toRuData.card_U]; norm_num
      obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset (pow_five_of_orderOf hb5) hbU hy hU5
      have hxn : (x : G) * n ∈ M.T5 b := by
        refine ⟨mul_mem (M.HC_le_Q x.2) (M.U_le_Q hn), (mem_G5).mpr ?_⟩
        calc (x : G) * n * b = b * ((x : G) * n) * b⁻¹ * b := by rw [hfix]
          _ = b * ((x : G) * n) := by group
      refine ⟨⟨_, hxn⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      show ((x : G) * n)⁻¹ * (x : G) ∈ ruU M.L M.T
      rw [mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem hn
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup ((ruU M.L M.T).subgroupOf M.HC)
    rw [M.card_HC, card_subgroupOf_of_le hUC, M.toRuData.card_U] at hq
    omega
  rw [hker, hrange] at h
  omega

theorem eq_z_of_T5
    {x : G} (hx : x ∈ M.T5 b) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) : x = M.z := by
  have hU := M.mem_U_of_HC_sq (T5_le_HC hbH hb5 hx) hx2
  rcases M.mem_Z_iff.mp (mem_Z_of_T5_U hbH hb5 hx hU) with h | h
  · exact absurd h hx1
  · exact h

theorem T5_quaternion : Nonempty (M.T5 b ≃* QuaternionGroup 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (M.T5 b) := by
    rw [IsPGroup.iff_card, card_T5 hbH hb5]
    exact ⟨3, by norm_num⟩
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
      (M.T5 b) := by
    intro u v _
    have hu : ((u : M.T5 b) : G) = M.z := by
      have h2 : ((u : M.T5 b) : G) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (u : M.T5 b)
        rw [u.2] at this
        simpa using congrArg Subtype.val this
      refine eq_z_of_T5 hbH hb5 (u : M.T5 b).2 h2 fun h1 => ?_
      have := u.2
      rw [show (u : M.T5 b) = 1 from Subtype.ext h1, orderOf_one] at this
      norm_num at this
    have hv : ((v : M.T5 b) : G) = M.z := by
      have h2 : ((v : M.T5 b) : G) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (v : M.T5 b)
        rw [v.2] at this
        simpa using congrArg Subtype.val this
      refine eq_z_of_T5 hbH hb5 (v : M.T5 b).2 h2 fun h1 => ?_
      have := v.2
      rw [show (v : M.T5 b) = 1 from Subtype.ext h1, orderOf_one] at this
      norm_num at this
    exact Subtype.ext (Subtype.ext (hu.trans hv.symm))
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hp hrank with
    hcyc | ⟨e, he, ⟨φ⟩⟩
  · exfalso
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = 8 := by
      rw [← card_T5 hbH hb5]
      exact orderOf_eq_card_of_forall_mem_zpowers hg
    have hg4 : g ^ 4 = 1 := by
      have hsq := M.sq_HC_mem_Z (T5_le_HC hbH hb5 g.2)
      apply Subtype.ext
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
      rcases M.mem_Z_iff.mp hsq with h | h
      · simp [h]
      · simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [h, M.z_sq]
    have := orderOf_dvd_of_pow_eq_one hg4
    rw [hord] at this
    norm_num at this
  · have hcard : Nat.card (QuaternionGroup (2 ^ e)) = 8 := by
      rw [Nat.card_congr φ.toEquiv, card_T5 hbH hb5]
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at hcard
    have he1 : e = 1 := by
      have h2e : 2 ^ e = 2 := by omega
      exact Nat.pow_right_injective (le_refl 2) (by simpa using h2e)
    subst he1
    exact ⟨φ.symm⟩

theorem card_CH5 : Nat.card (M.CH5 b) = 40 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hCH : M.CH5 b ≤ ruH M.T := inf_le_left
  let f : (M.CH5 b).subgroupOf (ruH M.T) →* SigmaL2F4 :=
    M.φ.comp ((M.CH5 b).subgroupOf (ruH M.T)).subtype
  have h := Subgroup.card_ker_mul_card_range f
  rw [card_subgroupOf_of_le hCH] at h
  have hker : Nat.card f.ker = 8 := by
    refine Eq.trans ?_ (card_T5 hbH hb5)
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1.1, ?_, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp x.1.2)).2⟩
        invFun := fun y => ⟨⟨⟨y.1, pCoreOf_le 2 _ (Subgroup.mem_inf.mp y.2).1⟩,
          Subgroup.mem_subgroupOf.mpr ⟨pCoreOf_le 2 _ (Subgroup.mem_inf.mp y.2).1,
            (Subgroup.mem_inf.mp y.2).2⟩⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have : x.1.1 ∈ M.φ.ker := hx
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · show M.φ ⟨y.1, _⟩ = 1
      have : (⟨y.1, pCoreOf_le 2 _ (Subgroup.mem_inf.mp y.2).1⟩ : ruH M.T) ∈ M.φ.ker := by
        rw [M.φ_ker, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_inf.mp y.2).1
      exact this
  have hrange : Nat.card f.range = 5 := by
    refine Eq.trans ?_ ((Nat.card_eq_fintype_card).trans
      (Sigma.card_centralizer_five _ (φ_b_props hbH hb5)))
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1, ?_⟩
        invFun := fun g => ⟨g.1, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun g => rfl }
    · obtain ⟨x, hx⟩ := y.2
      rw [← hx]
      have hb : (x : G) * b = b * x := (mem_G5.mp (Subgroup.mem_subgroupOf.mp x.2).2)
      show M.φ x.1 * M.φ ⟨b, hbH⟩ = M.φ ⟨b, hbH⟩ * M.φ x.1
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hb
    · obtain ⟨h, hh⟩ := M.φ_surj g.1
      have hbQ : ∀ q ∈ ruQ M.T, b * q * b⁻¹ ∈ ruQ M.T := fun q hq => M.conj_mem_Q hbH hq
      have hy : (h : G)⁻¹ * (b * h * b⁻¹) ∈ ruQ M.T := by
        have hmem : (h : G)⁻¹ * (b * h * b⁻¹) ∈ ruH M.T :=
          mul_mem (inv_mem h.2) (mul_mem (mul_mem hbH h.2) (inv_mem hbH))
        have hk : (⟨_, hmem⟩ : ruH M.T) ∈ M.φ.ker := by
          rw [MonoidHom.mem_ker]
          have e : (⟨_, hmem⟩ : ruH M.T) =
              h⁻¹ * (⟨b, hbH⟩ * h * ⟨b, hbH⟩⁻¹) := rfl
          rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, hh, ← g.2]
          group
        rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
        exact hk
      have hQ5 : ¬ 5 ∣ Nat.card (ruQ M.T) := by rw [M.toRuData.card_Q]; norm_num
      obtain ⟨q, hq, hfix⟩ := exists_fixed_mem_coset (pow_five_of_orderOf hb5) hbQ hy hQ5
      have hhq : (h : G) * q ∈ ruH M.T := mul_mem h.2 (pCoreOf_le 2 _ hq)
      have hb : (h : G) * q * b = b * (h * q) := by
        calc (h : G) * q * b = b * (h * q) * b⁻¹ * b := by rw [hfix]
          _ = b * (h * q) := by group
      refine ⟨⟨⟨_, hhq⟩, Subgroup.mem_subgroupOf.mpr ⟨hhq, (mem_G5).mpr hb⟩⟩, ?_⟩
      show M.φ ⟨(h : G) * q, hhq⟩ = g.1
      have hq1 : M.φ ⟨q, pCoreOf_le 2 _ hq⟩ = 1 := by
        have : (⟨q, pCoreOf_le 2 _ hq⟩ : ruH M.T) ∈ M.φ.ker := by
          rw [M.φ_ker, Subgroup.mem_subgroupOf]
          exact hq
        exact this
      have e : (⟨(h : G) * q, hhq⟩ : ruH M.T) = h * ⟨q, pCoreOf_le 2 _ hq⟩ := rfl
      rw [e, map_mul, hq1, mul_one, hh]
  rw [hker, hrange] at h
  omega

omit [Finite G] hb5 in
theorem zpowers_b_le_CH5 : Subgroup.zpowers b ≤ M.CH5 b := by
  rw [Subgroup.zpowers_le]
  exact ⟨hbH, (mem_G5.mpr rfl : b ∈ G5 b)⟩

theorem CH5_eq_mul {x : G} (hx : x ∈ M.CH5 b) :
    ∃ t ∈ M.T5 b, ∃ c ∈ Subgroup.zpowers b, x = c * t := by
  classical
  have hT : M.T5 b ≤ M.CH5 b := M.T5_le_CH5
  have hB := zpowers_b_le_CH5 hbH
  let F : Subgroup.zpowers b × M.T5 b → M.CH5 b := fun p =>
    ⟨(p.1 : G) * p.2, mul_mem (hB p.1.2) (hT p.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨c, t⟩ ⟨c', t'⟩ h
    have h1 : (c : G) * t = c' * t' := congrArg Subtype.val h
    have h2 : (c' : G)⁻¹ * c = t' * (t : G)⁻¹ := by
      calc (c' : G)⁻¹ * c = (c' : G)⁻¹ * (c * t) * (t : G)⁻¹ := by group
        _ = (c' : G)⁻¹ * (c' * t') * (t : G)⁻¹ := by rw [h1]
        _ = t' * (t : G)⁻¹ := by group
    have h5 : orderOf ((c' : G)⁻¹ * c) ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers b) (mul_mem (inv_mem c'.2) c.2)
      rwa [Nat.card_zpowers, hb5] at this
    have h8 : orderOf ((c' : G)⁻¹ * c) ∣ 8 := by
      rw [← card_T5 hbH hb5, h2]
      exact Subgroup.orderOf_dvd_natCard _ (mul_mem t'.2 (inv_mem t.2))
    have h3 : (c' : G)⁻¹ * c = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h5 h8)
    have hcc : (c : G) = c' := by
      calc (c : G) = c' * ((c' : G)⁻¹ * c) := by group
        _ = c' := by rw [h3, mul_one]
    have htt : (t : G) = t' := by
      have := h1
      rw [hcc] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext hcc) (Subtype.ext htt)
  have hbij : Function.Bijective F := hF.bijective_of_nat_card_le (le_of_eq (by
    rw [Nat.card_prod, Nat.card_zpowers, hb5, card_T5 hbH hb5, card_CH5 hbH hb5]))
  obtain ⟨⟨c, t⟩, hp⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨t, t.2, c, c.2, (congrArg Subtype.val hp).symm⟩

theorem eq_T5_of_le
    {P : Subgroup G} (hP : IsPGroup 2 P) (hTP : M.T5 b ≤ P)
    (hPB : P ≤ G5 b) : P = M.T5 b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : (M.T5 b).subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun x hx => ?_) hTP
    have : (⟨x, hx⟩ : P) ∈ (M.T5 b).subgroupOf P := htop ▸ Subgroup.mem_top _
    exact this
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨x, hxN, hxT⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hxP : (x : G) ∈ P := x.2
  have hxT' : (x : G) ∉ M.T5 b := fun h => hxT h
  have hzT := z_mem_T5 hbH
  have hxz : (x : G) * M.z * (x : G)⁻¹ = M.z := by
    have hmem : (x : G) * M.z * (x : G)⁻¹ ∈ M.T5 b :=
      (Subgroup.mem_normalizer_iff.mp hxN ⟨M.z, hTP hzT⟩).mp hzT
    refine eq_z_of_T5 hbH hb5 hmem (by rw [conj_pow, M.z_sq]; group) fun h => M.z_ne_one ?_
    calc M.z = (x : G)⁻¹ * ((x : G) * M.z * (x : G)⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hxH : (x : G) ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    calc M.z * x = (x : G) * M.z * (x : G)⁻¹ * x := by rw [hxz]
      _ = (x : G) * M.z := by group
  have hxC : (x : G) ∈ M.CH5 b := ⟨hxH, hPB hxP⟩
  set K := P ⊓ M.CH5 b
  have hTK : M.T5 b ≤ K := le_inf hTP (M.T5_le_CH5)
  have hKlt : M.T5 b < K := lt_of_le_of_ne hTK (fun h => hxT' (by rw [h]; exact ⟨hxP, hxC⟩))
  have hKp : IsPGroup 2 K := hP.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hKp)
  have hdvd : Nat.card K ∣ 40 := by
    rw [← card_CH5 hbH hb5]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hlt8 : 8 < Nat.card K := by
    rw [← card_T5 hbH hb5]
    exact Subgroup.card_lt_of_lt hKlt
  rw [hk] at hdvd hlt8
  have := le_eight_of_dvd_forty hdvd
  omega

@[expose] noncomputable def T5syl : Sylow 2 (G5 b) where
  toSubgroup := (M.T5 b).subgroupOf (G5 b)
  isPGroup' := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.iff_card.mpr ⟨3, (card_subgroupOf_of_le (M.T5_le_G5)).trans
      (card_T5 hbH hb5)⟩
  is_maximal' := by
    intro Q' hQ hTQ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQ' : IsPGroup 2 (Q'.map (G5 b).subtype) := hQ.map _
    have hle : M.T5 b ≤ Q'.map (G5 b).subtype := by
      intro x hx
      exact ⟨⟨x, M.T5_le_G5 hx⟩, hTQ (show (⟨x, M.T5_le_G5 hx⟩ : G5 b) ∈
        (M.T5 b).subgroupOf (G5 b) from hx), rfl⟩
    have heq := eq_T5_of_le hbH hb5 hQ' hle (Subgroup.map_subtype_le Q')
    apply le_antisymm _ hTQ
    intro y hy
    show (y : G) ∈ M.T5 b
    rw [← heq]
    exact ⟨y, hy, rfl⟩

noncomputable abbrev z5 : G5 b := ⟨M.z, z_mem_G5 hbH⟩

theorem coe_T5syl : (T5syl hbH hb5 : Subgroup (G5 b)) = (M.T5 b).subgroupOf (G5 b) := rfl

theorem z5_central : (QuotientGroup.mk (z5 hbH) : G5 b ⧸ O5 b) ∈
    Subgroup.center (G5 b ⧸ O5 b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Nonempty ((T5syl hbH hb5 : Subgroup (G5 b)) ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    rw [coe_T5syl hbH hb5, show (2 : ℕ) ^ (3 - 2) = 2 from rfl]
    obtain ⟨e⟩ := T5_quaternion hbH hb5
    exact ⟨(Subgroup.subgroupOfEquivOfLe (M.T5_le_G5)).trans e⟩
  have hzmem : z5 hbH ∈ (T5syl hbH hb5 : Subgroup (G5 b)) := by
    rw [coe_T5syl hbH hb5, Subgroup.mem_subgroupOf]
    exact z_mem_T5 hbH
  have hzord : orderOf (z5 hbH) = 2 := by
    refine orderOf_eq_prime (Subtype.ext (by simpa using M.z_sq)) fun h => M.z_ne_one ?_
    exact congrArg Subtype.val h
  exact CFSG.BrauerSuzuki.brauer_suzuki 3 le_rfl (T5syl hbH hb5) hq (z5 hbH) hzmem hzord

theorem exists_O5_mul
    (g : G5 b) : ∃ o ∈ O5 b, ((o⁻¹ * g : G5 b) : G) ∈ ruH M.T := by
  classical
  set u := z5 hbH
  set v := g * u * g⁻¹
  have hu2 : u * u = 1 := Subtype.ext (by
    show M.z * M.z = 1
    exact M.z_mul_self)
  have hv2 : v * v = 1 := by
    simp only [v]
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  set d := u * v
  have hd : d ∈ O5 b := by
    have hc := z5_central hbH hb5
    rw [Subgroup.mem_center_iff] at hc
    have h1 := hc (QuotientGroup.mk g)
    rw [← QuotientGroup.eq_one_iff]
    show (QuotientGroup.mk (u * (g * u * g⁻¹)) : G5 b ⧸ O5 b) = 1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      h1, mul_inv_cancel_right, ← QuotientGroup.mk_mul, hu2, QuotientGroup.mk_one]
  obtain ⟨j, hj⟩ := O5_odd b
  have hdm : d ^ (2 * j + 1) = 1 := by
    have h := pow_card_eq_one' (G := O5 b) (x := ⟨d, hd⟩)
    rw [hj] at h
    exact congrArg Subtype.val h
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hud : u * d = d⁻¹ * u := by
    simp only [d]
    rw [mul_inv_rev, hu', hv']
    calc u * (u * v) = (u * u) * v := by group
      _ = v := by rw [hu2, one_mul]
      _ = v * (u * u) := by rw [hu2, mul_one]
      _ = v * u * u := by group
  have hud' : u * d⁻¹ = d * u := by
    have h1 : d * (u * d) = d * (d⁻¹ * u) := by rw [hud]
    rw [mul_inv_cancel_left] at h1
    calc u * d⁻¹ = d * (u * d) * d⁻¹ := by rw [h1]
      _ = d * u := by group
  have hudj' : ∀ k : ℕ, u * (d⁻¹) ^ k = d ^ k * u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hud', ← mul_assoc, ← pow_succ]
  have h2j : d ^ (2 * j) = d⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hdm]
  have hconj : d ^ j * u * (d ^ j)⁻¹ = v := by
    calc d ^ j * u * (d ^ j)⁻¹ = d ^ j * (u * (d⁻¹) ^ j) := by rw [inv_pow]; group
      _ = d ^ j * (d ^ j * u) := by rw [hudj']
      _ = d ^ (2 * j) * u := by rw [← mul_assoc, ← pow_add, two_mul]
      _ = d⁻¹ * u := by rw [h2j]
      _ = u * d := by rw [hud]
      _ = v := by simp only [d]; rw [← mul_assoc, hu2, one_mul]
  refine ⟨d ^ j, pow_mem hd j, ?_⟩
  rw [M.mem_H_iff_comm]
  have hz : ((d ^ j)⁻¹ * g) * u * ((d ^ j)⁻¹ * g)⁻¹ = u := by
    calc ((d ^ j)⁻¹ * g) * u * ((d ^ j)⁻¹ * g)⁻¹ = (d ^ j)⁻¹ * (g * u * g⁻¹) * d ^ j := by group
      _ = (d ^ j)⁻¹ * (d ^ j * u * (d ^ j)⁻¹) * d ^ j := by rw [hconj]
      _ = u := by group
  have hz' := congrArg Subtype.val hz
  have e : (((d ^ j)⁻¹ * g : G5 b) : G) * M.z * (((d ^ j)⁻¹ * g : G5 b) : G)⁻¹ = M.z := hz'
  calc M.z * (((d ^ j)⁻¹ * g : G5 b) : G) =
      (((d ^ j)⁻¹ * g : G5 b) : G) * M.z * (((d ^ j)⁻¹ * g : G5 b) : G)⁻¹ *
        (((d ^ j)⁻¹ * g : G5 b) : G) := by rw [e]
    _ = (((d ^ j)⁻¹ * g : G5 b) : G) * M.z := by group

end Five

end RuDataM

end CFSG.Quasithin.RuType
