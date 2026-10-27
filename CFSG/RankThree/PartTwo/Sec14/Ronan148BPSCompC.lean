module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSCompB
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.GroupTheory.LocalCores.Components
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14
open CFSG.FiveTransitive.CharacteristicAutomorphism (quotient quotient_apply_mk)
open scoped commutatorElement Pointwise

theorem exists_fixed_lift {B H : Type*} [Group B] [Group H] [Finite B] [Finite H]
    (hB : IsPGroup 3 B) (σ : B →* MulAut H) (N : Subgroup H) [N.Characteristic]
    (hN3 : ¬ 3 ∣ Nat.card N) {h : H ⧸ N} (hfix : ∀ b, quotient N (σ b) h = h) :
    ∃ c ∈ fixSub σ, (c : H ⧸ N) = h := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmk_eq : ∀ x y : H, (x : H ⧸ N) = y ↔ x * y⁻¹ ∈ N := fun x y => by
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  obtain ⟨c, hcg, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hB σ N
    hN3 g).1 (by
    intro b x hx
    have hxg : (x : H ⧸ N) = g := (hmk_eq x g).mpr hx
    have hσx : ((σ b x : H) : H ⧸ N) = g := by
      have := quotient_apply_mk N (σ b) x
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at this
      rw [← this, hxg, hfix b]
    exact (hmk_eq _ _).mp hσx)
  exact ⟨c, hcfix, (hmk_eq c g).mpr hcg⟩

variable {Y : Type} [Group Y] [Finite Y]

theorem thetaAct_zpow_fix {W B : Subgroup Y} (hBW : B ≤ Subgroup.normalizer (W : Set Y))
    {J : Subgroup (↥W ⧸ aschbacherSolvableCore 3 ↥W)} {c : ↥B}
    (hc : ∀ j ∈ J, thetaAct hBW c j = j) (k : ℤ) : ∀ j ∈ J, thetaAct hBW (c ^ k) j = j := by
  intro j hj
  rw [map_zpow]
  induction k using Int.induction_on generalizing j with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, MulAut.mul_apply, hc j hj, ih j hj]
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply]
    have : (thetaAct hBW c)⁻¹ j = j := by
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hc j hj]
    rw [this, ih j hj]

section Faithful

variable {W P D Q : Subgroup Y}

theorem eq_one_of_centralizes_component (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP9 : Nat.card P = 9) (hPW : P ≤ Subgroup.normalizer (W : Set Y)) (hD : IsHyperplane P D)
    (hQW : Q ≤ W) (hQD : Q ≤ Subgroup.centralizer (D : Set Y)) (hQP : Q = ⁅Q, P⁆)
    (hQO : Q ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (D : Set Y)))
    (ha : CFSG.pPrimeCore 3 (↥W ⧸ aschbacherSolvableCore 3 ↥W) = ⊥)
    {J : Subgroup (↥W ⧸ aschbacherSolvableCore 3 ↥W)} (hJ : IsComponent J)
    (hPJ : ∀ p : ↥P, J.map (thetaAct hPW p).toMonoidHom = J)
    (hQJ : (Q.subgroupOf W).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W)) ≤
      Subgroup.normalizer (J : Set (↥W ⧸ aschbacherSolvableCore 3 ↥W)))
    (hQJ' : ¬ (Q.subgroupOf W).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W)) ≤
      Subgroup.centralizer (J : Set (↥W ⧸ aschbacherSolvableCore 3 ↥W)))
    {c : Y} (hc : c ∈ P) (hcJ : ∀ j ∈ J, thetaAct hPW ⟨c, hc⟩ j = j) : c = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := theta_characteristic ↥W
  set Ws := ↥W ⧸ aschbacherSolvableCore 3 ↥W
  set mk := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W) with hmk
  set Qs := (Q.subgroupOf W).map mk with hQs
  have hPp : IsPGroup 3 P := fun g => ⟨1, Subtype.ext (by simpa using hP.2 g g.2)⟩
  have hDp : IsPGroup 3 D := hPp.to_le hD.1
  have hDW : D ≤ Subgroup.normalizer (W : Set Y) := hD.1.trans hPW
  have hD3 : Nat.card D = 3 := by
    have := hD.2
    rw [hP9] at this
    omega
  have h3J := three_dvd_card_of_isComponent ha hJ
  by_contra hc1
  by_cases hcD : c ∈ D
  ·
    have hzD : Subgroup.zpowers c = D := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcD)
      rw [hD3, Nat.card_zpowers]
      have : orderOf c = 3 := orderOf_eq_prime (hP.2 c hc) hc1
      omega
    have hDJ : ∀ (d : ↥D) (j : Ws), j ∈ J → thetaAct hDW d j = j := by
      intro d j hj
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzD ▸ d.2 : (d : Y) ∈ Subgroup.zpowers c)
      have e : thetaAct hDW d = thetaAct hPW (⟨c, hc⟩ ^ k) := by
        ext w
        obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
        rw [thetaAct_mk, thetaAct_mk]
        congr 1
        apply Subtype.ext
        rw [conjAct_apply, conjAct_apply, ← hk]
        rfl
      rw [e]
      exact thetaAct_zpow_fix hPW hcJ k j hj
    set H₂ : Subgroup Ws := fixSub (thetaAct hDW) with hH₂
    set K := (pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (D : Set Y))).subgroupOf W with hK
    obtain ⟨hKfix, hKn, hK3⟩ := signalizer_data hDW
    set N₂ : Subgroup Ws := K.map mk with hN₂
    have hJH : J ≤ H₂ := fun j hj d => hDJ d j hj
    have hNH : N₂ ≤ H₂ := by
      rintro _ ⟨k, hk, rfl⟩ d
      change thetaAct hDW d ((k : ↥W) : Ws) = ((k : ↥W) : Ws)
      rw [thetaAct_mk, hKfix hk d]
    have hN3 : Nat.Coprime 3 (Nat.card N₂) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hK3
    have hHN : H₂ ≤ Subgroup.normalizer (N₂ : Set Ws) := by
      intro h hh
      obtain ⟨c', hc'F, hc'h⟩ := exists_fixed_lift hDp (conjAct hDW) (aschbacherSolvableCore 3 ↥W)
        (theta_not_dvd _) (h := h) (fun d => hh d)
      rw [← hc'h]
      refine mem_normalizer_of_conj_le fun n hn => ?_
      obtain ⟨k, hk, rfl⟩ := hn
      refine ⟨c' * k * c'⁻¹, (Subgroup.mem_normalizer_iff.mp (hKn hc'F) k).mp hk, ?_⟩
      rw [map_mul, map_mul, map_inv]
      rfl
    have hNn : (N₂.subgroupOf H₂).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
    have hJc : IsComponent (J.subgroupOf H₂) := CFSG.LocalCores.component_overgroup hJ hJH
    rcases CFSG.LocalCores.component_normal_subgroup hJc hNn with hle | hcomm
    ·
      have hJN : J ≤ N₂ := fun j hj => by
        have := hle (Subgroup.mem_subgroupOf.mpr (show ((⟨j, hJH hj⟩ : ↥H₂) : Ws) ∈ J from hj))
        exact Subgroup.mem_subgroupOf.mp this
      have := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hJN) hN3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp this h3J
    ·
      apply hQJ'
      rintro _ ⟨q, hq, rfl⟩
      have hqK : q ∈ K := Subgroup.mem_subgroupOf.mpr (hQO (Subgroup.mem_subgroupOf.mp hq))
      have hqN : mk q ∈ N₂ := ⟨q, hqK, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h1 := Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mpr (show ((⟨j, hJH hj⟩ : ↥H₂) : Ws) ∈ J from hj))
        (Subgroup.mem_subgroupOf.mpr (show ((⟨mk q, hNH hqN⟩ : ↥H₂) : Ws) ∈ N₂ from hqN))
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      have h2 := congrArg Subtype.val h1
      exact h2
  ·
    have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hP.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    set M₀ : Subgroup Y :=
      ((Subgroup.centralizer (J : Set Ws)).comap mk).map W.subtype with hM₀
    have hmemM₀ : ∀ w : ↥W, (w : Y) ∈ M₀ ↔ mk w ∈ Subgroup.centralizer (J : Set Ws) := by
      intro w
      constructor
      · rintro ⟨w', hw', hw'w⟩
        have : w' = w := Subtype.ext hw'w
        rw [← this]
        exact hw'
      · intro h
        exact ⟨w, h, rfl⟩
    have hM₀W : M₀ ≤ W := Subgroup.map_subtype_le _
    have hPM₀ : ∀ x ∈ P, ∀ w ∈ M₀, x * w * x⁻¹ ∈ M₀ := by
      intro x hx w hw
      have hwW : w ∈ W := hM₀W hw
      have hxw : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hPW hx) w).mp hwW
      have e : (⟨x * w * x⁻¹, hxw⟩ : ↥W) = conjAct hPW ⟨x, hx⟩ ⟨w, hwW⟩ := rfl
      refine (hmemM₀ ⟨_, hxw⟩).mpr ?_
      have hwC := (hmemM₀ ⟨w, hwW⟩).mp hw
      rw [e]
      change ((conjAct hPW ⟨x, hx⟩ ⟨w, hwW⟩ : ↥W) : Ws) ∈ _
      rw [← thetaAct_mk]
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hj' : j ∈ J.map (thetaAct hPW ⟨x, hx⟩).toMonoidHom := by rw [hPJ]; exact hj
      obtain ⟨j₀, hj₀, rfl⟩ := hj'
      change thetaAct hPW ⟨x, hx⟩ j₀ * thetaAct hPW ⟨x, hx⟩ (mk ⟨w, hwW⟩) =
        thetaAct hPW ⟨x, hx⟩ (mk ⟨w, hwW⟩) * thetaAct hPW ⟨x, hx⟩ j₀
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hwC j₀ hj₀]
    have hcomc : ∀ q ∈ Q, ∀ k : ℤ, ⁅q, c ^ k⁆ ∈ M₀ := by
      intro q hq k
      have hqW := hQW hq
      have hck : c ^ k ∈ P := P.zpow_mem hc k
      have hw : ⁅q, c ^ k⁆ ∈ W := by
        rw [commutatorElement_def]
        have : c ^ k * q⁻¹ * (c ^ k)⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hPW hck) q⁻¹).mp (W.inv_mem hqW)
        have e : q * c ^ k * q⁻¹ * (c ^ k)⁻¹ = q * (c ^ k * q⁻¹ * (c ^ k)⁻¹) := by group
        rw [e]
        exact W.mul_mem hqW this
      refine (hmemM₀ ⟨_, hw⟩).mpr ?_
      set σ := thetaAct hPW (⟨c, hc⟩ ^ k) with hσ
      set qs : Ws := ((⟨q, hqW⟩ : ↥W) : Ws) with hqs
      have hσfix := thetaAct_zpow_fix hPW hcJ k
      have hmkw : ((⟨⁅q, c ^ k⁆, hw⟩ : ↥W) : Ws) = qs * (σ qs)⁻¹ := by
        have e : (⟨⁅q, c ^ k⁆, hw⟩ : ↥W) = ⟨q, hqW⟩ *
            (conjAct hPW (⟨c, hc⟩ ^ k) ⟨q, hqW⟩)⁻¹ := by
          apply Subtype.ext
          change ⁅q, c ^ k⁆ = q * (((⟨c, hc⟩ ^ k : ↥P) : Y) * q * ((⟨c, hc⟩ ^ k : ↥P) : Y)⁻¹)⁻¹
          rw [commutatorElement_def, Subgroup.coe_zpow]
          group
        rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← thetaAct_mk]
      change ((⟨⁅q, c ^ k⁆, hw⟩ : ↥W) : Ws) ∈ _
      rw [hmkw, Subgroup.mem_centralizer_iff]
      intro j hj
      have hqsN : qs ∈ Subgroup.normalizer (J : Set Ws) := hQJ ⟨_, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
      have hj1 : qs⁻¹ * j * qs ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hqsN) j).mp hj
        rwa [inv_inv] at this
      have hσj1 : σ (qs⁻¹ * j * qs) = qs⁻¹ * j * qs := hσfix _ hj1
      rw [map_mul, map_mul, map_inv, hσfix j hj] at hσj1
      calc j * (qs * (σ qs)⁻¹) = qs * (qs⁻¹ * j * qs) * (σ qs)⁻¹ := by group
        _ = qs * ((σ qs)⁻¹ * j * σ qs) * (σ qs)⁻¹ := by rw [hσj1]
        _ = qs * (σ qs)⁻¹ * j := by group
    have hDc : D ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup Y) : Set Y) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro d hd
      exact hPc d (hD.1 hd) c hc
    have hcard : Nat.card (D ⊔ Subgroup.zpowers c : Subgroup Y) = 9 := by
      have hdvd := card_sup_dvd_card_mul hDc
      have hzc : Nat.card (Subgroup.zpowers c) = 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hP.2 c hc) hc1
      rw [hD3, hzc] at hdvd
      have hlt : Nat.card D < Nat.card (D ⊔ Subgroup.zpowers c : Subgroup Y) := by
        refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hcD ?_)
        rw [h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
      rw [hD3] at hlt
      have : Nat.card (D ⊔ Subgroup.zpowers c : Subgroup Y) ∈ Nat.divisors 9 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    have hPeq : D ⊔ Subgroup.zpowers c = P :=
      Subgroup.eq_of_le_of_card_ge (sup_le hD.1 (Subgroup.zpowers_le.mpr hc))
        (by rw [hcard, hP9])
    have hQM₀ : Q ≤ M₀ := by
      rw [hQP, Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨q, hq, x, hx, rfl⟩
      rw [← hPeq] at hx
      have hx' : x ∈ (D : Set Y) * (Subgroup.zpowers c : Set Y) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right D _ hDc]
        exact hx
      obtain ⟨d, hd, y, hy, rfl⟩ := hx'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hqd : q * d = d * q := (Subgroup.mem_centralizer_iff.mp (hQD hq) d hd).symm
      have e : ⁅q, d * c ^ k⁆ = d * ⁅q, c ^ k⁆ * d⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc q * (d * c ^ k) * q⁻¹ * (d * c ^ k)⁻¹ = (q * d) * c ^ k * q⁻¹ * (c ^ k)⁻¹ * d⁻¹ := by
              group
          _ = (d * q) * c ^ k * q⁻¹ * (c ^ k)⁻¹ * d⁻¹ := by rw [hqd]
          _ = d * (q * c ^ k * q⁻¹ * (c ^ k)⁻¹) * d⁻¹ := by group
      rw [e]
      exact hPM₀ d (hD.1 hd) _ (hcomc q hq k)
    apply hQJ'
    rintro _ ⟨q, hq, rfl⟩
    exact (hmemM₀ q).mp (hQM₀ (Subgroup.mem_subgroupOf.mp hq))

end Faithful

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS
