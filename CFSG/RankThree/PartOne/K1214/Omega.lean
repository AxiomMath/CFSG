module

public import CFSG.RankThree.PartOne.K1214.OmegaAlg
public import CFSG.RankThree.PartOne.K1214.RData
public import CFSG.RankThree.PartOne.K1214.Center
import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.Blueprint
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

theorem SylowShape.exists_equiv {p r e : ℕ} {Γ : Type*} [Group Γ] [Finite Γ] (hp : p.Prime)
    (N : Subgroup Γ) [N.Normal] (hN : ¬ p ∣ Nat.card N) (h : SylowShape p r e (Γ ⧸ N))
    {S : Subgroup Γ} (hS : IsPGroup p ↥S) (hidx : ¬ p ∣ S.index) :
    Nonempty (↥S ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) := by
  have : Fact p.Prime := ⟨hp⟩
  set π : Γ →* Γ ⧸ N := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hŜp : IsPGroup p ↥(S.map π) := hS.map π
  have hŜidx : ¬ p ∣ (S.map π).index := fun hd =>
    hidx (hd.trans (Subgroup.index_map_dvd S hsurj))
  have hNS : N ⊓ S = ⊥ := by
    have hp' : IsPGroup p ↥(N ⊓ S) := hS.to_inf_right
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hp'
    have hdvd : Nat.card ↥(N ⊓ S) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    rw [hj] at hdvd
    by_cases hj0 : j = 0
    · subst hj0
      exact Subgroup.eq_bot_of_card_eq _ (by simpa using hj)
    · exact absurd ((dvd_pow_self p hj0).trans hdvd) hN
  have hinj : Function.Injective (π.subgroupMap S) := by
    intro x y hxy
    have h1 : π (x : Γ) = π (y : Γ) := congrArg Subtype.val hxy
    have h2 : (x : Γ)⁻¹ * (y : Γ) ∈ N := QuotientGroup.eq.mp h1
    have h3 : (x : Γ)⁻¹ * (y : Γ) ∈ S := S.mul_mem (S.inv_mem x.2) y.2
    have h4 : (x : Γ)⁻¹ * (y : Γ) ∈ N ⊓ S := ⟨h2, h3⟩
    rw [hNS, Subgroup.mem_bot] at h4
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  let ψ : ↥S ≃* ↥(S.map π) := MulEquiv.ofBijective (π.subgroupMap S)
    ⟨hinj, MonoidHom.subgroupMap_surjective π S⟩
  obtain ⟨φ⟩ := h _ hŜp hŜidx
  exact ⟨ψ.trans φ⟩

theorem eq_bot_of_pGroup_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H N : Subgroup G} (hH : IsPGroup p ↥H)
    (hle : H ≤ N) (hN : ¬ p ∣ Nat.card N) : H = ⊥ := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hH
  have hdvd : Nat.card ↥H ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hle
  rw [hj] at hdvd
  by_cases hj0 : j = 0
  · subst hj0
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using hj)
  · exact absurd ((dvd_pow_self p hj0).trans hdvd) hN

section Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {b : G} {K I X P Q : Subgroup G}

theorem R_equiv (hRig : LieRigidity3) (h112 : InSec11Two) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I)
    (hKR : K = inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G))) :
    ∃ r e : ℕ, (r = 1 ∨ r = 2) ∧ 2 ≤ e ∧ Nat.card E = p ^ (r + 2) ∧
      Nonempty (↥(P ⊓ I) ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) := by
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  obtain ⟨r, e, hr, he, hEcard, hI, -⟩ := rData hRig ctx hL hF hKR
  have hRs := R_sylow ctx hL hC
  have hZ := zI_pPrime h112 ctx hL hF
  have hRp : IsPGroup p ↥((P ⊓ I).subgroupOf I) :=
    hRs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRs.1).symm
  obtain ⟨φ⟩ := SylowShape.exists_equiv hp (Subgroup.center ↥I) hZ hI hRp hRs.2.2
  exact ⟨r, e, hr, he, hEcard, ⟨(Subgroup.subgroupOfEquivOfLe hRs.1).symm.trans φ⟩⟩

omit [Finite G] in
theorem mem_normalizer_inf {c : G} {P I : Subgroup G} (hcP : c ∈ P)
    (hcI : c ∈ Subgroup.normalizer (I : Set G)) :
    c ∈ Subgroup.normalizer ((P ⊓ I : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨hP, hI⟩
    exact ⟨P.mul_mem (P.mul_mem hcP hP) (P.inv_mem hcP),
      (Subgroup.mem_normalizer_iff.1 hcI h).1 hI⟩
  · rintro ⟨hP, hI⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.1 hcI h).2 hI⟩
    have := P.mul_mem (P.mul_mem (P.inv_mem hcP) hP) hcP
    simpa [mul_assoc] using this

@[expose] def KFixedRes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      K = inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G))

theorem kf1214Omega_of (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes) :
    KF1214Omega := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF ha
  classical
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hcE := c_mem_E ctx
  have hEP := E_le_P hC
  have hcP : c ∈ P := hEP hcE
  have hcQ := c_not_mem_Q hF hC
  have hcp : c ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E ctx.hyp hcE
  obtain ⟨f, hfP, hPf⟩ := ha.P_gen
  obtain ⟨hQP, hQn⟩ := ha.Q_norm
  have hPp : IsPGroup p ↥P := P_isPGroup hC
  have hcI : c ∈ Subgroup.normalizer (I : Set G) := hC.P_norm hcP
  set R : Subgroup G := P ⊓ I with hRdef
  set Z : Subgroup G := Subgroup.centralizer (I : Set G) ⊓ P with hZdef
  have hQeq : Q = Z ⊔ R := hC.Q_eq
  obtain ⟨r, e, hr, he2, -, ⟨φR⟩⟩ := R_equiv hRig h112 ctx hL hC hF (hKR G p A c L E ctx b K I X P Q hL hC hF)
  have hZp : IsPGroup p ↥Z := hPp.to_le inf_le_right
  have hbA := hL.b_mem
  have hbE : b ∈ E := ctx.hyp.A_le_E hbA.1
  have hbZ : b ∈ Z := ⟨Subgroup.mem_centralizer_iff.2 fun i hi => by
    have := Subgroup.mem_centralizer_iff.1 (I_le_centralizer hL hi) b (Set.mem_singleton b)
    exact this.symm, hEP hbE⟩
  obtain ⟨e', ⟨φZ⟩⟩ := exists_equiv_fin_one hZp ha.C_cyc
  have he1' : 1 ≤ e' := by
    by_contra h0
    have he0 : e' = 0 := by omega
    subst he0
    have hcard : Nat.card ↥Z = 1 := by
      rw [Nat.card_congr φZ.toEquiv]
      simp
    have hb1 : (⟨b, hbZ⟩ : ↥Z) = 1 := (Nat.card_eq_one_iff_unique.1 hcard).1.elim _ _
    exact hbA.2.2 (congrArg Subtype.val hb1)
  have hcR := mem_normalizer_inf hcP hcI
  have hcZ : c ∈ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_centralizer_inf P I ⟨hcP, hcI⟩
  obtain ⟨hR1, hR2⟩ := act_subgroup hp5 hr (by omega) (Or.inr he2) φR hcR hcp
  obtain ⟨hZ1, hZ2⟩ := act_subgroup hp5 (Or.inl rfl) he1' (Or.inl rfl) φZ hcZ hcp
  have hRZ : ∀ r' ∈ R, ∀ z ∈ Z, r' * z = z * r' := fun r' hr' z hz =>
    Subgroup.mem_centralizer_iff.1 hz.1 r' hr'.2
  have hbot : R ⊓ Z = ⊥ := by
    refine eq_bot_of_pGroup_le (N := I ⊓ Subgroup.centralizer (I : Set G))
      (hPp.to_le (fun x hx => hx.1.1)) (fun x hx => ⟨hx.1.2, hx.2.1⟩) ?_
    rw [card_inf_centralizer]
    exact zI_pPrime h112 ctx hL hF
  have hRc : ∀ r' ∈ R, ∀ r'' ∈ R, r' * r'' = r'' * r' := fun r' hr' r'' hr'' => by
    have h1 : φR (⟨r', hr'⟩ * ⟨r'', hr''⟩) = φR (⟨r'', hr''⟩ * ⟨r', hr'⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (φR.injective h1)
  have hZc : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' => by
    have h1 : φZ (⟨z, hz⟩ * ⟨z', hz'⟩) = φZ (⟨z', hz'⟩ * ⟨z, hz⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (φZ.injective h1)
  obtain ⟨hQab, hQ1, hQ2⟩ := props_sup (p := p) hRZ hbot hRc hZc
    (fun r' hr' => (Subgroup.mem_normalizer_iff.1 hcR r').1 hr')
    (fun z hz => (Subgroup.mem_normalizer_iff.1 hcZ z).1 hz) hR1 hR2 hZ1 hZ2
  rw [← hQeq] at hQab hQ1 hQ2
  have hcQn : ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun q hq => by
    have := hQn.conj_mem ⟨q, hQP hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨c, hcP⟩
    simpa using Subgroup.mem_subgroupOf.1 this
  have hpowQ : ∀ (j : ℕ), ∀ q ∈ Q, (c ^ j * q) ^ p = q ^ p := by
    intro j q hq
    have hdQ : c * q * c⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hcQn q hq) (Q.inv_mem hq)
    have hdp := hQ1 q hq
    have hcd : c * (c * q * c⁻¹ * q⁻¹) = (c * q * c⁻¹ * q⁻¹) * c := by
      have := hQ2 _ hdQ hdp
      calc c * (c * q * c⁻¹ * q⁻¹) = (c * (c * q * c⁻¹ * q⁻¹) * c⁻¹) * c := by group
        _ = (c * q * c⁻¹ * q⁻¹) * c := by rw [this]
    exact pow_c_pow_mul hp hp2 rfl hcd hdp (hQab _ hdQ q hq) hcp j
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x ^ p = 1 → y ^ p = 1 → x * y = y * x := by
    intro x hx y hy hxp hyp
    obtain ⟨i, q, hq, rfl⟩ := exists_c_pow_mul hp hQP hQn hfP hPf hcP hcQ hcp hx hxp
    obtain ⟨j, q', hq', rfl⟩ := exists_c_pow_mul hp hQP hQn hfP hPf hcP hcQ hcp hy hyp
    have hq1 : q ^ p = 1 := by rw [← hpowQ i q hq]; exact hxp
    have hq1' : q' ^ p = 1 := by rw [← hpowQ j q' hq']; exact hyp
    have hcq : Commute c q := by
      have := hQ2 q hq hq1
      show c * q = q * c
      calc c * q = (c * q * c⁻¹) * c := by group
        _ = q * c := by rw [this]
    have hcq' : Commute c q' := by
      have := hQ2 q' hq' hq1'
      show c * q' = q' * c
      calc c * q' = (c * q' * c⁻¹) * c := by group
        _ = q' * c := by rw [this]
    have hqq' : Commute q q' := hQab q hq q' hq'
    exact Commute.mul_left (Commute.mul_right (Commute.pow_pow_self c i j) (hcq'.pow_left i))
      (Commute.mul_right (hcq.symm.pow_right j) hqq')
  have hS : IsElementaryAbelian p ↥(omegaOne p P) :=
    isElementaryAbelian_closure (fun x hx y hy => hcomm x hx.1 y hy.1 hx.2 hy.2) (fun x hx => hx.2)
  have hEle : E ≤ omegaOne p P := fun e he =>
    Subgroup.subset_closure ⟨hEP he, Sec12Three.pow_eq_one_of_mem_E ctx.hyp he⟩
  have hAc : omegaOne p P ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx a ha'
    have haΩ : a ∈ omegaOne p P := hEle (ctx.hyp.A_le_E ha')
    have := (IsMulCommutative.is_comm (M := ↥(omegaOne p P))).comm ⟨a, haΩ⟩ ⟨x, hx⟩
    exact congrArg Subtype.val this
  exact ctx.hyp.E_max (omegaOne p P) hS hAc hEle

end Ctx

end CFSG.RankThree.PartOne.K1214
