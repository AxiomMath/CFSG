module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaFixEq
public import CFSG.CGT.PushingUpLit.BHS6.NestedLinear
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Tools2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

def IsNaturalChiefSection (H U : Subgroup G) (m : ℕ) (Lo Hi : Subgroup G)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod Lo Hi))
    (hstep : IsChiefStep H U Lo Hi) : Prop :=
  letI : CommGroup (Ch3z.chiefMod Lo Hi) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod Lo Hi)) := l2ChiefSectionModule hE
  ∃ (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (ρ : Representation (ZMod 2) SL(2, GaloisField 2 m) (Additive (Ch3z.chiefMod Lo Hi)))
    (φ : Additive (Ch3z.chiefMod Lo Hi) ≃+ (Fin 2 → GaloisField 2 m)),
    (∀ (h : ↥H) (w : Ch3z.chiefMod Lo Hi),
      ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
        Additive.ofMul (l2ChiefSectionAction hstep hE h w)) ∧
    (∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)).mulVec (φ w))

def Str86CaseIIaFixEq (L1 L2 S : Subgroup G) (m : ℕ) (Lo Hi : Subgroup G) : Prop :=
  ∃ A : Subgroup G, IsElemAbelian 2 A ∧ A ≤ S ∧
    (centralizerMod Lo Hi A).relIndex Hi = 2 ^ m ∧
    (A ⊓ pCoreOf 2 (L2 ⊔ S)).relIndex A = 2 ^ m

theorem isNaturalChiefSection_of_eq {H U L N A : Subgroup G} {m : ℕ} (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H)) (hV : IsElemAbelian 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) (hA : IsElemAbelian 2 A)
    (hAH : A ≤ H) (hstep_eq : (centralizerMod L N A).relIndex N = 2 ^ m)
    (hA_eq : (A ⊓ pCoreOf 2 H).relIndex A = 2 ^ m) :
    IsNaturalChiefSection H U m L N
      (CFSG.Quasithin.isElemAbelian_chiefMod hstep hUH hV.isPGroup) hstep := by
  obtain ⟨e, ρ, φ, -, -, hcompat, hnatiso, -⟩ :=
    l2_chiefStep_natural hm2 hL2 hV hUH hstep hnc hA hAH hstep_eq hA_eq
  exact ⟨e, ρ, φ, hcompat, hnatiso⟩

private theorem chiefIota_eq_of_mul_inv_mem {L N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {u v : ↥N}
    (h : (u : G) * (v : G)⁻¹ ∈ L) : Ch3z.chiefIota hNL u = Ch3z.chiefIota hNL v := by
  have hmem : ((u * v⁻¹ : ↥N) : G) ∈ L := by simpa using h
  have h1 : Ch3z.chiefIota hNL (u * v⁻¹) = 1 :=
    (Ch3z.chiefIota_eq_one_iff hNL (u * v⁻¹)).mpr hmem
  have hstep : u = (u * v⁻¹) * v := by group
  calc Ch3z.chiefIota hNL u = Ch3z.chiefIota hNL ((u * v⁻¹) * v) :=
        congrArg (Ch3z.chiefIota hNL) hstep
    _ = Ch3z.chiefIota hNL (u * v⁻¹) * Ch3z.chiefIota hNL v := map_mul _ _ _
    _ = Ch3z.chiefIota hNL v := by rw [h1, one_mul]

theorem str86_natural_factor_torus_of_natural
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2)
    {Lo Hi : Subgroup G} (hstep : IsChiefStep (L2 ⊔ S) (str86U L1 L2 S) Lo Hi)
    (hnc : ¬ IsCentralStep (L2 ⊔ S) Lo Hi)
    (hUH : str86U L1 L2 S ≤ L2 ⊔ S)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod Lo Hi))
    (hnat : IsNaturalChiefSection (L2 ⊔ S) (str86U L1 L2 S) m Lo Hi hE hstep)
    {d : G} (hd : d ∈ (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) (hdo : Odd (orderOf d))
    (hd1 : d ≠ 1) {x : G} (hx : x ∈ Hi) (hxS : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Lo)
    (hxd : d * x * d⁻¹ * x⁻¹ ∈ Lo) : x ∈ Lo := by
  classical
  obtain ⟨e, ρ, φ, hcompat, hnatiso⟩ := hnat
  have hdH : d ∈ L2 ⊔ S := hd.1
  have hHL : L2 ⊔ S ≤ Subgroup.normalizer (Lo : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : L2 ⊔ S ≤ Subgroup.normalizer (Hi : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hHiU : Hi ≤ str86U L1 L2 S := hstep.1.1
  have hNL : Hi ≤ Subgroup.normalizer (Lo : Set G) := (hHiU.trans hUH).trans hHL
  letI : CommGroup (Ch3z.chiefMod Lo Hi) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod Lo Hi)) := l2ChiefSectionModule hE
  let dH : ↥(L2 ⊔ S) := ⟨d, hdH⟩
  let q : ↥(L2 ⊔ S) →* oTwoQuot ↥(L2 ⊔ S) := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L2 ⊔ S))
  let ψ : ↥(L2 ⊔ S) →* SL(2, GaloisField 2 m) := e.toMonoidHom.comp q
  let g : SL(2, GaloisField 2 m) := ψ dH
  let w : Additive (Ch3z.chiefMod Lo Hi) := Additive.ofMul (Ch3z.chiefIota hNL ⟨x, hx⟩)
  have hmem : d * x * d⁻¹ ∈ Hi := (Subgroup.mem_normalizer_iff.mp (hHN hdH) x).mp hx
  have hact : l2ChiefSectionAction hstep hE dH (Ch3z.chiefIota hNL ⟨x, hx⟩) =
      Ch3z.chiefIota hNL ⟨x, hx⟩ := by
    rw [l2ChiefSectionAction_eq_chiefPsi]
    rw [Ch3z.chiefPsi_iota hHL hHN hNL dH ⟨x, hx⟩ hmem]
    exact chiefIota_eq_of_mul_inv_mem hNL (by simpa using hxd)
  have hfix : (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)).mulVec (φ w) = φ w := by
    have h2 : ρ (e (QuotientGroup.mk dH)) w = w := by
      rw [hcompat dH (Ch3z.chiefIota hNL ⟨x, hx⟩), hact]
    have h1 := hnatiso (e (QuotientGroup.mk dH)) w
    rw [h2] at h1
    simpa [g, ψ, q] using h1.symm
  have hoddg : Odd (orderOf g) := by
    have hdvd : orderOf g ∣ orderOf dH := by
      have := orderOf_map_dvd ψ dH
      simpa [g] using this
    have h2 : orderOf dH = orderOf d := by
      simpa [dH] using (Subgroup.orderOf_coe dH).symm
    exact Odd.of_dvd_nat (h2 ▸ hdo) hdvd
  by_contra hxLo
  have hwne : w ≠ 0 := by
    intro h0
    refine hxLo ?_
    have h1 : Ch3z.chiefIota hNL ⟨x, hx⟩ = 1 := by
      have := congrArg Additive.toMul h0
      simpa [w] using this
    exact (Ch3z.chiefIota_eq_one_iff hNL ⟨x, hx⟩).mp h1
  have hvne : φ w ≠ 0 := fun h0 => hwne (φ.injective (by simpa using h0))
  have hgsmul : g • (φ w) = φ w := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.smul_eq_mulVec']
    exact hfix
  have hg1 : g = 1 := CFSG.CGT.PushingUpLit.BHS6.eq_one_of_odd_of_smul_eq hoddg hvne hgsmul
  have hq1 : q dH = 1 := e.injective (by rw [map_one]; exact hg1)
  have hdmemH : dH ∈ CFSG.Open.pCore 2 ↥(L2 ⊔ S) :=
    (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥(L2 ⊔ S)) dH).mp (by simpa [q] using hq1)
  have hdmem : d ∈ pCoreOf 2 (L2 ⊔ S) := Subgroup.mem_map.mpr ⟨dH, hdmemH, rfl⟩
  have hp2 : IsPGroup 2 (pCoreOf 2 (L2 ⊔ S)) :=
    IsPGroup.map (pCore_isPGroup (G := ↥(L2 ⊔ S)) (p := 2)) (Subgroup.subtype (L2 ⊔ S))
  obtain ⟨n, hn⟩ := hp2.exists_orderOf_eq_pow ⟨d, hdmem⟩
  have hn' : orderOf d = 2 ^ n := by simpa using hn
  have hoddn : Odd (2 ^ n) := hn' ▸ hdo
  have hn0 : 2 ^ n = 1 := by
    rcases n with _ | n
    · rfl
    · exact absurd (dvd_pow_self 2 (Nat.succ_ne_zero n)) hoddn.not_two_dvd_nat
  exact hd1 (orderOf_eq_one_iff.mp (hn'.trans hn0))

theorem str86_natural_factor_torus_of_fixEq
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2)
    {Lo Hi : Subgroup G} (hstep : IsChiefStep (L2 ⊔ S) (str86U L1 L2 S) Lo Hi)
    (hnc : ¬ IsCentralStep (L2 ⊔ S) Lo Hi)
    (hUH : str86U L1 L2 S ≤ L2 ⊔ S)
    (hV : IsElemAbelian 2 (str86U L1 L2 S)) (hm2 : 2 ≤ m)
    (hfix : Str86CaseIIaFixEq L1 L2 S m Lo Hi)
    {d : G} (hd : d ∈ (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) (hdo : Odd (orderOf d))
    (hd1 : d ≠ 1) {x : G} (hx : x ∈ Hi) (hxS : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Lo)
    (hxd : d * x * d⁻¹ * x⁻¹ ∈ Lo) : x ∈ Lo := by
  obtain ⟨A, hA, hAS, hstep_eq, hA_eq⟩ := hfix
  have hAH : A ≤ L2 ⊔ S := hAS.trans le_sup_right
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm2, hm⟩))
  have hL2sup : IsL2Quot m (oTwoQuot ↥(L2 ⊔ S)) := by
    obtain ⟨eL2⟩ := hm
    rw [sup_eq_of_S_eq_right hS2,
      show L2 ⊔ Q2 L1 L2 S = L2 ⊔ Q1 L2 L1 S by rw [Q1, Q2, P1, P2, bigB_comm]]
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL2⟩
  have hE : IsElemAbelian 2 (Ch3z.chiefMod Lo Hi) :=
    CFSG.Quasithin.isElemAbelian_chiefMod hstep hUH hV.isPGroup
  have hnat : IsNaturalChiefSection (L2 ⊔ S) (str86U L1 L2 S) m Lo Hi hE hstep :=
    isNaturalChiefSection_of_eq hm2 hL2sup hV hUH hstep hnc hA hAH hstep_eq hA_eq
  exact str86_natural_factor_torus_of_natural hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hstep hnc
    hUH hE hnat hd hdo hd1 hx hxS hxd

theorem str86_natural_factor_torus
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2)
    {Lo Hi : Subgroup G} (hstep : IsChiefStep (L2 ⊔ S) (str86U L1 L2 S) Lo Hi)
    (hnc : ¬ IsCentralStep (L2 ⊔ S) Lo Hi)
    {d : G} (hd : d ∈ (L2 ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) (hdo : Odd (orderOf d))
    (hd1 : d ≠ 1) {x : G} (hx : x ∈ Hi) (hxS : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Lo)
    (hxd : d * x * d⁻¹ * x⁻¹ ∈ Lo) : x ∈ Lo := by
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
    Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩
  have hm2 : 2 ≤ m := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hV : IsElemAbelian 2 (str86U L1 L2 S) :=
    isElemAbelian_str86U_of_caseII hF hSB hq hm2 hm hII hZ
  have hUH : str86U L1 L2 S ≤ L2 ⊔ S := by
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm2, hm⟩))
    have hQ2S : Q2 L1 L2 S ≤ S := le_sup_right.trans hS2.symm.le
    have hQ2norm : L2 ⊔ S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))
    have hUQ2 : str86U L1 L2 S ≤ Q2 L1 L2 S :=
      conjClosure_le fun g hg z hz => (Subgroup.mem_normalizer_iff.mp (hQ2norm hg) z).mp (hZ hz)
    exact (hUQ2.trans hQ2S).trans le_sup_right
  have hfix : Str86CaseIIaFixEq L1 L2 S m Lo Hi :=
    str86_caseIIa_two_fixEq hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hstep hnc
  exact str86_natural_factor_torus_of_fixEq hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hstep hnc
    hUH hV hm2 hfix hd hdo hd1 hx hxS hxd

end CFSG.Quasithin.Stroth
