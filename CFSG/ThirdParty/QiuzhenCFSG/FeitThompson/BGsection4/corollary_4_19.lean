module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_17
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_e

namespace CFSG
end CFSG
open CFSG
/-! # Corollary 4.19 from BG Section 4 -/

universe u

section Main

open scoped FixedPoints commutatorElement

private theorem CFSG.chiefFactor_quotient_isElementaryAbelian_of_isPFactor
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : Group.IsSolvable G) (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    IsElementaryAbelian p Uq := by
  classical
  have : Group.IsSolvable G := hsolv
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin := chiefFactor_quotient_minimal (G := G) cf
  have hUq_min :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using hmin
  have : Uq.Normal := hUq_min.1
  have : IsMinimalNormal Uq := {
    minimal := by
      intro K _ hKU
      by_cases hK : K = ⊥
      · exact Or.inl hK
      · exact Or.inr (hUq_min.2.2 K inferInstance hKU hK)
  }
  have : Group.IsSolvable (G ⧸ cf.V) := by infer_instance
  have : Group.IsSolvable Uq := by infer_instance
  have hUq_comm : IsMulCommutative Uq := minimalNormal_solvable_isMulCommutative Uq
  let e : cf.U ⧸ cf.V.subgroupOf cf.U ≃* Uq :=
    quotientSubgroupRangeEquiv cf.U cf.V
  have hUq_p : IsPGroup p Uq := hcf_p.of_equiv e
  have : Fact (IsPGroup p Uq) := ⟨hUq_p⟩
  have : Nontrivial Uq := (Subgroup.nontrivial_iff_ne_bot Uq).2 hUq_min.2.1
  let Ω : Subgroup Uq := omega₁ (G := Uq) (p := p)
  have hΩ_char : Ω.Characteristic := by
    simpa [Ω] using omega₁_characteristic (G := Uq) (p := p)
  let : Ω.Characteristic := hΩ_char
  have : (Ω.map Uq.subtype).Normal := by
    exact ConjAct.normal_of_characteristic_of_normal
  have hp_dvd_cardUq : p ∣ Nat.card Uq := by
    rcases hUq_p.card_eq_or_dvd with h1 | hdiv
    · exfalso
      have hcard_gt : 1 < Nat.card Uq :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · exact hdiv
  have hΩmap_ne_bot : Ω.map Uq.subtype ≠ ⊥ := by
    simpa [Ω] using omega₁_map_subtype_ne_bot (M := Uq) (p := p) hp_dvd_cardUq
  have hΩmap_eq_Uq : Ω.map Uq.subtype = Uq :=
    IsMinimalNormal.eq_of_ne_bot Uq (Ω.map Uq.subtype)
      (Subgroup.map_subtype_le (H := Uq) (K := Ω)) hΩmap_ne_bot
  have hΩ_top : Ω = ⊤ := by
    have hinj : Function.Injective (Subgroup.map Uq.subtype) :=
      Subgroup.map_injective (f := Uq.subtype) Uq.subtype_injective
    have htop_map : (⊤ : Subgroup Uq).map Uq.subtype = Uq := by
      simpa [MonoidHom.range_eq_map] using (Uq.range_subtype : Uq.subtype.range = Uq)
    apply hinj
    simpa [htop_map] using hΩmap_eq_Uq
  have hpow : ∀ x : Uq, x ^ p = 1 := by
    intro x
    have hxΩ : x ∈ Ω := by simp [hΩ_top]
    have hx' : x ∈ Subgroup.closure {y : Uq | y ^ (p ^ 1) = 1} := by
      simpa [Ω, omega₁, omega] using hxΩ
    refine
      Subgroup.closure_induction (k := {y : Uq | y ^ (p ^ 1) = 1})
        (p := fun z _hz => z ^ p = 1) (x := x) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simpa [pow_one] using hy
    · simp
    · intro a b _ha _hb ha hb
      calc
        (a * b) ^ p = a ^ p * b ^ p := by
          have hab : Commute a b := by
            rw [commute_iff_eq]
            exact hUq_comm.is_comm.comm a b
          exact hab.mul_pow p
        _ = 1 := by simp [ha, hb]
    · intro a _ha ha
      simp [ha]
  exact {
    toIsMulCommutative := hUq_comm
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hpow
  }


private theorem CFSG.chiefFactor_inf_sup_normal_coprime_le_lower_of_isPFactor
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hNcop : Nat.Coprime p (Nat.card N))
    (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p) :
    cf.U ⊓ (cf.V ⊔ N) ≤ cf.V := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  have : cf.U.Normal := cf.isChief.normal_H
  let K : Subgroup G := cf.U ⊓ (cf.V ⊔ N)
  have hV_le_K : cf.V ≤ K := by
    exact le_inf cf.isChief.lt.le le_sup_left
  have hK_le_U : K ≤ cf.U := inf_le_left
  have hK_normal : K.Normal := by
    change (cf.U ⊓ (cf.V ⊔ N)).Normal
    infer_instance
  rcases cf.isChief.is_maximal K hK_normal hV_le_K hK_le_U with hK_eq_V | hK_eq_U
  · exact hK_eq_V.le
  · have hU_le_sup : cf.U ≤ cf.V ⊔ N := by
      simpa [K] using hK_eq_U
    have : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    let Nq : Subgroup (G ⧸ cf.V) := N.map π
    have hUq_le_Nq : Uq ≤ Nq := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨u, huU, rfl⟩
      have huVN : u ∈ cf.V ⊔ N := hU_le_sup huU
      rcases (Subgroup.mem_sup_of_normal_left (s := cf.V) (t := N) (x := u)).1 huVN with
        ⟨v, hvV, n, hnN, hvnu⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨n, hnN, ?_⟩
      calc
        π n = π v * π n := by
          have hv1 : π v = 1 := (QuotientGroup.eq_one_iff (N := cf.V) (x := v)).2 hvV
          simp [hv1]
        _ = π (v * n) := by simp [π]
        _ = π u := by simp [hvnu]
    let e : cf.U ⧸ cf.V.subgroupOf cf.U ≃* Uq :=
      quotientSubgroupRangeEquiv cf.U cf.V
    have hUq_p : IsPGroup p Uq := hcf_p.of_equiv e
    have hUq_ne_bot : Uq ≠ ⊥ := by
      simpa [π, Uq] using (chiefFactor_quotient_minimal (G := G) cf).2.1
    have hp_dvd_cardUq : p ∣ Nat.card Uq := by
      rcases hUq_p.card_eq_or_dvd with h1 | hdiv
      · exfalso
        exact hUq_ne_bot (Subgroup.card_eq_one.mp h1)
      · exact hdiv
    have hNq_cop : Nat.Coprime p (Nat.card Nq) := by
      exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := N) π) hNcop
    have hUq_cop : Nat.Coprime p (Nat.card Uq) := by
      exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hUq_le_Nq) hNq_cop
    exact (((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hUq_cop) hp_dvd_cardUq).elim

private theorem CFSG.Op_p'p_characteristic_local
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] :
    (Op_p'p p H).Characteristic := by
  change ((pCore p (H ⧸ pPrimeCore p H)).comap (QuotientGroup.mk' (pPrimeCore p H))).Characteristic
  exact Subgroup.Characteristic.comap_quotient_mk
    (H := pPrimeCore p H) (K := pCore p (H ⧸ pPrimeCore p H))
    (pCore_characteristic (G := H ⧸ pPrimeCore p H) (p := p))

private theorem CFSG.prime_dvd_natCard_of_isPFactor_of_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p) {H : Subgroup G} (hcfU : cf.U ≤ H) :
    p ∣ Nat.card H := by
  have : cf.V.Normal := cf.isChief.normal_K
  let : (cf.V.subgroupOf cf.U).Normal :=
    Subgroup.Normal.subgroupOf (G := G) (hH := cf.isChief.normal_K) cf.U
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  let e : cf.U ⧸ cf.V.subgroupOf cf.U ≃* Uq :=
    quotientSubgroupRangeEquiv cf.U cf.V
  have hcard_eq : Nat.card (cf.U ⧸ cf.V.subgroupOf cf.U) = Nat.card Uq :=
    Nat.card_congr e.toEquiv
  have hUq_ne_bot : Uq ≠ ⊥ := by
    simpa [π, Uq] using (chiefFactor_quotient_minimal (G := G) cf).2.1
  have hp_dvd_card_quot : p ∣ Nat.card (cf.U ⧸ cf.V.subgroupOf cf.U) := by
    rcases hcf_p.card_eq_or_dvd with h1 | hdiv
    · exfalso
      apply hUq_ne_bot
      apply Subgroup.card_eq_one.mp
      rw [← hcard_eq]
      exact h1
    · exact hdiv
  exact dvd_trans
    (dvd_trans hp_dvd_card_quot (Subgroup.card_quotient_dvd_card (s := cf.V.subgroupOf cf.U)))
    (Subgroup.card_dvd_of_le hcfU)

private theorem CFSG.chiefFactor_upper_le_Op_p'p_sup_lower_of_isPFactor
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (GStar : Subgroup G) [GStar.Normal]
    (hrank : primeRank p GStar ≤ 2) (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p)
    (hcfU : cf.U ≤ GStar) :
    cf.U ≤ ((Op_p'p p ↥GStar).map GStar.subtype) ⊔ cf.V := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  have : cf.U.Normal := cf.isChief.normal_H
  have hcfV : cf.V ≤ GStar := cf.isChief.lt.le.trans hcfU
  let N0 : Subgroup GStar := Op_p'p p ↥GStar
  let N : Subgroup G := N0.map GStar.subtype
  have hN_le_GStar : N ≤ GStar := Subgroup.map_subtype_le (H := GStar) (K := N0)
  have hN0_subgroupOf : N.subgroupOf GStar = N0 := by
    simpa [N] using
      (Subgroup.comap_map_eq_self_of_injective (H := N0) (f := GStar.subtype) GStar.subtype_injective)
  have : N0.Characteristic := Op_p'p_characteristic_local (H := ↥GStar) (p := p)
  have : N.Normal := by
    simpa [N] using (inferInstance : (N0.map GStar.subtype).Normal)
  let L : Subgroup G := cf.V ⊔ N
  have : L.Normal := by
    change (cf.V ⊔ N).Normal
    infer_instance
  have hL_le_GStar : L ≤ GStar := sup_le hcfV hN_le_GStar
  let L0 : Subgroup GStar := L.subgroupOf GStar
  have : L0.Normal := by
    exact Subgroup.Normal.subgroupOf (G := G) (hH := inferInstance) GStar
  have hN0_le_L0 : N0 ≤ L0 := by
    intro x hx
    change ((x : G) ∈ L)
    have hxN : (x : G) ∈ N := Subgroup.mem_map_of_mem GStar.subtype hx
    exact (show N ≤ L from le_sup_right) hxN
  have hp_mem_GStar : p ∣ Nat.card GStar :=
    prime_dvd_natCard_of_isPFactor_of_le (cf := cf) hcf_p hcfU
  have hsolvGStar : Group.IsSolvable GStar := by infer_instance
  have hoddGStar : Odd (Nat.card GStar) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card GStar)
  have hcop_quot_N0 : Nat.Coprime p (Nat.card (↥GStar ⧸ N0)) := by
    simpa [N0] using
      (theorem_4_18_e (G := ↥GStar) (p := p) hsolvGStar hoddGStar hp_mem_GStar hrank).1
  have hcard_quot_dvd :
      Nat.card ((↥GStar ⧸ N0) ⧸ L0.map (QuotientGroup.mk' N0)) ∣ Nat.card (↥GStar ⧸ N0) := by
    exact Subgroup.card_quotient_dvd_card (s := L0.map (QuotientGroup.mk' N0))
  have hcard_quot_eq :
      Nat.card (↥GStar ⧸ L0) =
        Nat.card ((↥GStar ⧸ N0) ⧸ L0.map (QuotientGroup.mk' N0)) := by
    simpa using
      (Nat.card_congr
        (QuotientGroup.quotientQuotientEquivQuotient (N := N0) (M := L0) hN0_le_L0).toEquiv).symm
  have hcop_quot_L0 : Nat.Coprime p (Nat.card (↥GStar ⧸ L0)) := by
    rw [hcard_quot_eq]
    exact Nat.Coprime.of_dvd_right hcard_quot_dvd hcop_quot_N0
  let K : Subgroup G := cf.U ⊓ L
  have hV_le_K : cf.V ≤ K := by
    exact le_inf cf.isChief.lt.le le_sup_left
  have hK_le_U : K ≤ cf.U := inf_le_left
  have hK_normal : K.Normal := by
    change (cf.U ⊓ (cf.V ⊔ N)).Normal
    infer_instance
  rcases cf.isChief.is_maximal K hK_normal hV_le_K hK_le_U with hK_eq_V | hK_eq_U
  · exfalso
    let qL : G →* G ⧸ L := QuotientGroup.mk' L
    let Ubar : Subgroup (G ⧸ L) := cf.U.map qL
    let Hbar : Subgroup (G ⧸ L) := GStar.map qL
    have hLsub_eq_Vsub : L.subgroupOf cf.U = cf.V.subgroupOf cf.U := by
      ext x
      have hxU : (x : G) ∈ cf.U := x.property
      have hxK :
          ((x : G) ∈ K) ↔ ((x : G) ∈ cf.V) := by
        simp [hK_eq_V]
      have hxL :
          ((x : G) ∈ L) ↔ ((x : G) ∈ cf.V) := by
        simpa [K, hxU] using hxK
      simpa [Subgroup.mem_subgroupOf] using hxL
    have hcard_Ubar :
        Nat.card Ubar = Nat.card (cf.U ⧸ cf.V.subgroupOf cf.U) := by
      calc
        Nat.card Ubar = Nat.card (cf.U ⧸ L.subgroupOf cf.U) := by
          simpa [Ubar, qL] using (natCard_map_mk'_eq cf.U L)
        _ = Nat.card (cf.U ⧸ cf.V.subgroupOf cf.U) := by rw [hLsub_eq_Vsub]
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    let eU : cf.U ⧸ cf.V.subgroupOf cf.U ≃* Uq :=
      quotientSubgroupRangeEquiv cf.U cf.V
    have hcard_Uq : Nat.card Uq = Nat.card (cf.U ⧸ cf.V.subgroupOf cf.U) :=
      (Nat.card_congr eU.toEquiv).symm
    have hUq_ne_bot : Uq ≠ ⊥ := by
      simpa [π, Uq] using (chiefFactor_quotient_minimal (G := G) cf).2.1
    have hp_dvd_card_Ubar : p ∣ Nat.card Ubar := by
      have hp_dvd_card_quot : p ∣ Nat.card (cf.U ⧸ cf.V.subgroupOf cf.U) := by
        rcases hcf_p.card_eq_or_dvd with h1 | hdiv
        · exfalso
          exact hUq_ne_bot (Subgroup.card_eq_one.mp (hcard_Uq.trans h1))
        · exact hdiv
      rw [hcard_Ubar]
      exact hp_dvd_card_quot
    have hUbar_le_Hbar : Ubar ≤ Hbar := by
      exact Subgroup.map_mono hcfU
    have hcard_Hbar : Nat.card Hbar = Nat.card (↥GStar ⧸ L0) := by
      simpa [Hbar, qL, L0] using (natCard_map_mk'_eq GStar L)
    have hcop_Hbar : Nat.Coprime p (Nat.card Hbar) := by
      rw [hcard_Hbar]
      exact hcop_quot_L0
    have hcop_Ubar : Nat.Coprime p (Nat.card Ubar) := by
      exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hUbar_le_Hbar) hcop_Hbar
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hcop_Ubar) hp_dvd_card_Ubar
  · have hU_le_L : cf.U ≤ L := by
      simpa [K] using hK_eq_U
    simpa [L, sup_comm] using hU_le_L


private theorem CFSG.derivedSubgroup_le_centralizerOfChiefFactor_of_chief_conj_image_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (cf : ChiefFactor G) (himage_p :
      letI : cf.V.Normal := cf.isChief.normal_K
      let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
      letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      IsPGroup p ((derivedSubgroup G).map ((MulAut.conjNormal (H := Uq)).comp π)))
    (hpcore_bot :
      letI : cf.V.Normal := cf.isChief.normal_K
      let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
      letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      pCore p ((MulAut.conjNormal (H := Uq)).comp π).range = ⊥) :
    derivedSubgroup G ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
  let φ : G →* MulAut Uq := (MulAut.conjNormal (H := Uq)).comp π
  let A : Subgroup (MulAut Uq) := φ.range
  let φA : G →* A := φ.rangeRestrict
  let Dimg : Subgroup A := (derivedSubgroup G).map φA
  have hDimg_p : IsPGroup p Dimg := by
    have hmap_p : IsPGroup p ((derivedSubgroup G).map φ) := by
      simpa [φ, π, Uq] using himage_p
    have hDimg_map : Dimg.map A.subtype = (derivedSubgroup G).map φ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases Subgroup.mem_map.mp hy with ⟨g, hg, rfl⟩
        exact Subgroup.mem_map_of_mem φ hg
      · rintro ⟨g, hg, rfl⟩
        refine Subgroup.mem_map.mpr ?_
        exact ⟨φA g, Subgroup.mem_map_of_mem φA hg, rfl⟩
    have hDimg_map_p : IsPGroup p (Dimg.map A.subtype) := by
      rw [hDimg_map]
      exact hmap_p
    exact hDimg_map_p.of_equiv
      (Subgroup.equivMapOfInjective (f := A.subtype) Dimg A.subtype_injective).symm
  have hDimg_norm : Dimg.Normal := by
    exact Subgroup.Normal.map (inferInstance : (derivedSubgroup G).Normal) φA φ.rangeRestrict_surjective
  have hDimg_le_pcore : Dimg ≤ pCore p A := by
    exact le_sSup ⟨hDimg_norm, hDimg_p⟩
  have hDimg_bot : Dimg = ⊥ := by
    exact le_antisymm (hDimg_le_pcore.trans (by simpa [A, π, Uq] using hpcore_bot)) bot_le
  have hmap_bot : (derivedSubgroup G).map φ = ⊥ := by
    apply eq_bot_iff.2
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨g, hg, rfl⟩
    have hgA : φA g ∈ Dimg := Subgroup.mem_map_of_mem φA hg
    have hgAbot : φA g ∈ (⊥ : Subgroup A) := by
      simpa [hDimg_bot] using hgA
    have hgA_one : φA g = 1 := Subgroup.mem_bot.mp hgAbot
    change φ g = 1
    exact Subtype.ext_iff.mp hgA_one
  have hker : derivedSubgroup G ≤ φ.ker := by
    exact (Subgroup.map_eq_bot_iff (H := derivedSubgroup G) (f := φ)).1 hmap_bot
  refine (le_centralizerOfChiefFactor_iff (G := G) (H := (⊤ : Subgroup G))
    (N := derivedSubgroup G) (cf := cf)).2 ?_
  constructor
  · simp
  · rw [Subgroup.commutator_le]
    intro x hx u hu
    have hxker : φ x = 1 := by
      rw [← MonoidHom.mem_ker]
      exact hker hx
    let uq : Uq := ⟨π u, Subgroup.mem_map_of_mem π hu⟩
    have hfix : (MulAut.conjNormal (H := Uq) (π x)) uq = uq := by
      simpa [φ] using congrArg (fun a : MulAut Uq => a uq) hxker
    have hconj : π x * π u * (π x)⁻¹ = π u := by
      simpa [uq, MulAut.conjNormal_apply] using congrArg Subtype.val hfix
    have hcomm_eq_one : ⁅π x, π u⁆ = 1 := by
      rw [commutatorElement_def]
      calc
        π x * π u * (π x)⁻¹ * (π u)⁻¹ = π u * (π u)⁻¹ := by rw [hconj]
        _ = 1 := by simp
    have : π ⁅x, u⁆ = 1 := by
      simpa [map_commutatorElement] using hcomm_eq_one
    exact (QuotientGroup.eq_one_iff (N := cf.V) ⁅x, u⁆).1 this


private theorem CFSG.derived_image_isPGroup_of_mulAut_range_rank_le_two
    {G R : Type*} [Group G] [Finite G] [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    (hsolvG : Group.IsSolvable G) (hoddG : Odd (Nat.card G))
    (hR_rank : groupRank R ≤ 2) (φ : G →* MulAut R) :
    IsPGroup p ((derivedSubgroup G).map φ) := by
  classical
  let A : Subgroup (MulAut R) := φ.range
  let φA : G →* A := φ.rangeRestrict
  have hAodd : Odd (Nat.card A) := by
    exact hoddG.of_dvd_nat (Subgroup.card_dvd_of_surjective φ.rangeRestrict_surjective)
  have hsolvA : Group.IsSolvable A := by
    have : Group.IsSolvable G := hsolvG
    exact Group.isSolvable_of_surjective (f := φA) φ.rangeRestrict_surjective
  have hAder_p : IsPGroup p (derivedSubgroup A) := by
    exact theorem_4_17 (R := R) (A := A) (p := p) hpodd hsolvA hR_rank hAodd
  have hmap_der : (derivedSubgroup G).map φA = derivedSubgroup A := by
    simpa [derivedSubgroup, derivedSeries_one] using
      (map_derivedSeries_eq (f := φA) φ.rangeRestrict_surjective 1)
  have hmap_p : IsPGroup p ((derivedSubgroup G).map φA) := by
    rw [hmap_der]
    exact hAder_p
  have hmap_subtype_p : IsPGroup p (((derivedSubgroup G).map φA).map A.subtype) :=
    IsPGroup.map (p := p) (H := (derivedSubgroup G).map φA) hmap_p A.subtype
  have hmap_map : ((derivedSubgroup G).map φA).map A.subtype =
      (derivedSubgroup G).map φ := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨g, hg, rfl⟩
      exact Subgroup.mem_map_of_mem φ hg
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨g, hg, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨φA g, Subgroup.mem_map_of_mem φA hg, rfl⟩
  rw [hmap_map] at hmap_subtype_p
  exact hmap_subtype_p


private theorem CFSG.chiefFactor_derived_conj_image_isPGroup_of_covered_coprime_quotient_action
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} [M.Normal] (hMcop : Nat.Coprime p (Nat.card M))
    (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p)
    {R : Subgroup (G ⧸ M)} [R.Normal]
    (hU_le_R_sup : cf.U ≤ R.comap (QuotientGroup.mk' M) ⊔ cf.V)
    (hderR_p :
      let qM : G →* G ⧸ M := QuotientGroup.mk' M
      IsPGroup p ((derivedSubgroup G).map ((MulAut.conjNormal (H := R)).comp qM))) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
    IsPGroup p ((derivedSubgroup G).map (φ.comp π)) := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  let qM : G →* G ⧸ M := QuotientGroup.mk' M
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
  let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  have hM_inf_U_le_V : M ⊓ cf.U ≤ cf.V := by
    intro x hx
    exact chiefFactor_inf_sup_normal_coprime_le_lower_of_isPFactor
      (G := G) (p := p) (N := M) hMcop cf hcf_p
      ⟨hx.2, (by
        exact (Subgroup.mem_sup_of_normal_left (s := cf.V) (t := M) (x := x)).2
          ⟨1, cf.V.one_mem, x, hx.1, by simp⟩)⟩
  let D : Subgroup G := derivedSubgroup G
  let fR : D →* MulAut R := ((MulAut.conjNormal (H := R)).comp qM).comp D.subtype
  let fU : D →* MulAut Uq := ((φ.comp π).comp D.subtype)
  have hfactor : ∀ {x y : D}, fR x = fR y → fU x = fU y := by
    intro x y hxy
    ext u
    rcases Subgroup.mem_map.mp u.2 with ⟨u0, hu0U, hu0eq⟩
    have hu0_sup : u0 ∈ cf.V ⊔ R.comap qM := by
      simpa [qM, sup_comm] using hU_le_R_sup hu0U
    rcases (Subgroup.mem_sup_of_normal_left (s := cf.V) (t := R.comap qM) (x := u0)).1 hu0_sup with
      ⟨v, hvV, r, hrR, hvreq⟩
    have hrU : r ∈ cf.U := by
      have hv_inv : v⁻¹ ∈ cf.U := cf.U.inv_mem (cf.isChief.lt.le hvV)
      have hu0U' : u0 ∈ cf.U := hu0U
      have hr_eq : r = v⁻¹ * u0 := by
        have h := congrArg (fun t : G => v⁻¹ * t) hvreq
        simpa [mul_assoc] using h
      rw [hr_eq]
      exact cf.U.mul_mem hv_inv hu0U'
    have hconjR : (fR x) ⟨qM r, by simpa [Subgroup.mem_comap] using hrR⟩ =
        (fR y) ⟨qM r, by simpa [Subgroup.mem_comap] using hrR⟩ := by
      exact congrArg (fun e : MulAut R => e ⟨qM r, by simpa [Subgroup.mem_comap] using hrR⟩) hxy
    have hq_conj_eq : qM (x.1 * r * x.1⁻¹) = qM (y.1 * r * y.1⁻¹) := by
      simpa [fR, MulAut.conjNormal_apply] using congrArg Subtype.val hconjR
    have hdiff_M : (y.1 * r * y.1⁻¹)⁻¹ * (x.1 * r * x.1⁻¹) ∈ M := by
      exact QuotientGroup.eq.mp hq_conj_eq.symm
    have hdiff_U : (y.1 * r * y.1⁻¹)⁻¹ * (x.1 * r * x.1⁻¹) ∈ cf.U := by
      have hyU : y.1 * r * y.1⁻¹ ∈ cf.U := (cf.isChief.normal_H).conj_mem r hrU y.1
      have hxU : x.1 * r * x.1⁻¹ ∈ cf.U := (cf.isChief.normal_H).conj_mem r hrU x.1
      exact cf.U.mul_mem (cf.U.inv_mem hyU) hxU
    have hdiff_V : (y.1 * r * y.1⁻¹)⁻¹ * (x.1 * r * x.1⁻¹) ∈ cf.V :=
      hM_inf_U_le_V ⟨hdiff_M, hdiff_U⟩
    have hπ_conj_r_eq : π (x.1 * r * x.1⁻¹) = π (y.1 * r * y.1⁻¹) := by
      have hquot : π ((y.1 * r * y.1⁻¹)⁻¹ * (x.1 * r * x.1⁻¹)) = 1 :=
        (QuotientGroup.eq_one_iff (N := cf.V)
          (x := (y.1 * r * y.1⁻¹)⁻¹ * (x.1 * r * x.1⁻¹))).2 hdiff_V
      have hmul := congrArg (fun t : G ⧸ cf.V => π (y.1 * r * y.1⁻¹) * t) hquot
      simpa [π, map_mul, mul_assoc] using hmul
    have hπu_r : (u : G ⧸ cf.V) = π r := by
      calc
        (u : G ⧸ cf.V) = π u0 := hu0eq.symm
        _ = π (v * r) := by rw [hvreq]
        _ = π r := by
          have hv1 : π v = 1 := (QuotientGroup.eq_one_iff (N := cf.V) (x := v)).2 hvV
          calc
            π (v * r) = π v * π r := by simp [π]
            _ = 1 * π r := by rw [hv1]
            _ = π r := by simp
    calc
      (((fU x) u : Uq) : G ⧸ cf.V)
          = π x.1 * (u : G ⧸ cf.V) * (π x.1)⁻¹ := by
              simp [fU, φ, MulAut.conjNormal_apply]
      _ = π x.1 * π r * (π x.1)⁻¹ := by rw [hπu_r]
      _ = π (x.1 * r * x.1⁻¹) := by simp [π, map_mul, mul_assoc]
      _ = π (y.1 * r * y.1⁻¹) := hπ_conj_r_eq
      _ = π y.1 * π r * (π y.1)⁻¹ := by simp [π, map_mul, mul_assoc]
      _ = π y.1 * (u : G ⧸ cf.V) * (π y.1)⁻¹ := by rw [hπu_r]
      _ = (((fU y) u : Uq) : G ⧸ cf.V) := by
              simp [fU, φ, MulAut.conjNormal_apply]
  have hfrange_eq : fR.range = (derivedSubgroup G).map ((MulAut.conjNormal (H := R)).comp qM) := by
    calc
      fR.range = (⊤ : Subgroup D).map fR := MonoidHom.range_eq_map fR
      _ = ((⊤ : Subgroup D).map D.subtype).map ((MulAut.conjNormal (H := R)).comp qM) := by
            rw [Subgroup.map_map]
      _ = D.map ((MulAut.conjNormal (H := R)).comp qM) := by
            congr 1
            simpa [MonoidHom.range_eq_map] using
              (D.range_subtype : D.subtype.range = D)
      _ = (derivedSubgroup G).map ((MulAut.conjNormal (H := R)).comp qM) := rfl
  let H : Subgroup (MulAut R) := fR.range
  have hH_p : IsPGroup p H := by
    change IsPGroup p fR.range
    rw [hfrange_eq]
    simpa [qM] using hderR_p
  let rep : H → D := fun a => Classical.choose a.2
  have hrep : ∀ a : H, fR (rep a) = a := by
    intro a
    exact Classical.choose_spec a.2
  let ρ : H →* MulAut Uq := {
    toFun := fun a => fU (rep a)
    map_one' := by
      have h1 : fR (rep 1) = fR 1 := by
        calc
          fR (rep 1) = (1 : H) := hrep 1
          _ = fR 1 := by simp [H, fR]
      simpa [fU] using hfactor h1
    map_mul' := by
      intro a b
      have hmul : fR (rep (a * b)) = fR (rep a * rep b) := by
        calc
          fR (rep (a * b)) = a * b := hrep (a * b)
          _ = fR (rep a) * fR (rep b) := by rw [hrep a, hrep b]
          _ = fR (rep a * rep b) := by simp [fR]
      calc
        fU (rep (a * b)) = fU (rep a * rep b) := hfactor hmul
        _ = fU (rep a) * fU (rep b) := by simp [fU]
  }
  have hρrange_eq : ρ.range = fU.range := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨a, rfl⟩
      exact ⟨rep a, rfl⟩
    · intro hx
      rcases hx with ⟨d, rfl⟩
      let a : H := ⟨fR d, ⟨d, rfl⟩⟩
      refine ⟨a, ?_⟩
      change fU (rep a) = fU d
      exact hfactor (by simpa [a] using hrep a)
  have hfurange_eq : fU.range = (derivedSubgroup G).map ((MulAut.conjNormal (H := Uq)).comp π) := by
    calc
      fU.range = (⊤ : Subgroup D).map fU := MonoidHom.range_eq_map fU
      _ = ((⊤ : Subgroup D).map D.subtype).map (φ.comp π) := by
            rw [Subgroup.map_map]
      _ = D.map (φ.comp π) := by
            congr 1
            simpa [MonoidHom.range_eq_map] using
              (D.range_subtype : D.subtype.range = D)
      _ = (derivedSubgroup G).map (φ.comp π) := rfl
  have hρrange_p : IsPGroup p ρ.range := by
    have htop_p : IsPGroup p (⊤ : Subgroup H) := by
      simpa using hH_p.to_subgroup (⊤ : Subgroup H)
    have : IsPGroup p ((⊤ : Subgroup H).map ρ) :=
      IsPGroup.map (p := p) (H := (⊤ : Subgroup H)) htop_p ρ
    rw [MonoidHom.range_eq_map]
    exact this
  have hfurange_p : IsPGroup p fU.range := by
    rw [← hρrange_eq]
    exact hρrange_p
  rw [hfurange_eq] at hfurange_p
  exact hfurange_p

private theorem CFSG.chiefFactor_conj_range_pCore_eq_bot_local
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    {p : ℕ} [Fact p.Prime] (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
    pCore p φ.range = ⊥ := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal (G := G) cf
  let : Uq.Normal := hmin.1
  let : IsElementaryAbelian p Uq :=
    chiefFactor_quotient_isElementaryAbelian_of_isPFactor (G := G) (p := p) hsolv cf hcf_p
  let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  let A : Subgroup (MulAut Uq) := φ.range
  have hUq_p : IsPGroup p Uq := IsElementaryAbelian.isPGroup p Uq
  let P : Subgroup A := pCore p A
  have hP_p : IsPGroup p P := by
    dsimp [P]
    exact pCore_isPGroup (G := A) (p := p)
  have hUq_dvd : p ∣ Nat.card Uq := by
    have hUq_nontrivial : Nontrivial Uq := (Subgroup.nontrivial_iff_ne_bot Uq).2 hmin.2.1
    rcases (IsPGroup.nontrivial_iff_card (p := p) (G := Uq) (hG := hUq_p)).1 hUq_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn)
  let F : Subgroup Uq := fixedPointSubgroup P Uq
  have hF_ne_bot : F ≠ ⊥ := by
    have hone_fix : (1 : Uq) ∈ MulAction.fixedPoints P Uq := by
      simp [MulAction.mem_fixedPoints]
    obtain ⟨u, hu_fix, hu_ne_one'⟩ :=
      hP_p.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (α := Uq) hUq_dvd hone_fix
    have hu_ne_one : u ≠ 1 := by
      intro hu
      exact hu_ne_one' hu.symm
    intro hbot
    have hu_mem : u ∈ F := by
      simpa [F, FixedPoints.mem_subgroup] using
        MulAction.mem_fixedPoints.mp hu_fix
    have hu_bot : u ∈ (⊥ : Subgroup Uq) := by
      simpa [hbot] using hu_mem
    exact hu_ne_one (Subgroup.mem_bot.mp hu_bot)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  have hF_inv : IsInvariant A Uq F := by
    refine ⟨?_⟩
    intro a u
    constructor
    · intro hu
      change u ∈ fixedPointSubgroup P Uq at hu
      change a • u ∈ fixedPointSubgroup P Uq
      rw [FixedPoints.mem_subgroup] at hu ⊢
      exact smul_mem_fixedPoints_of_normal (H := P) a hu
    · intro hu
      change a • u ∈ fixedPointSubgroup P Uq at hu
      change u ∈ fixedPointSubgroup P Uq
      rw [FixedPoints.mem_subgroup] at hu ⊢
      have hsmul := smul_mem_fixedPoints_of_normal (H := P) a⁻¹ hu
      simpa [mul_smul] using hsmul
  let Fmap : Subgroup (G ⧸ cf.V) := F.map Uq.subtype
  have hFmap_normal : Fmap.Normal := by
    refine ⟨?_⟩
    intro x hx q
    rcases Subgroup.mem_map.mp hx with ⟨u, huF, rfl⟩
    let aq : A := ⟨φ q, ⟨q, rfl⟩⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨aq • u, (hF_inv.invariant aq u).1 huF, ?_⟩
    change (((φ q) u : Uq) : G ⧸ cf.V) = q * (u : G ⧸ cf.V) * q⁻¹
    simp [φ, MulAut.conjNormal_apply]
  have hFmap_le_Uq : Fmap ≤ Uq := by
    exact Subgroup.map_subtype_le F
  have hFmap_ne_bot : Fmap ≠ ⊥ := by
    intro hbot
    have : F = ⊥ := by
      exact
        (Subgroup.map_eq_bot_iff_of_injective (H := F) (f := Uq.subtype)
          Uq.subtype_injective).1 (by simpa [Fmap] using hbot)
    exact hF_ne_bot this
  have hFmap_eq_Uq : Fmap = Uq :=
    hmin.2.2 Fmap hFmap_normal hFmap_le_Uq hFmap_ne_bot
  have htop_map_Uq : (⊤ : Subgroup Uq).map Uq.subtype = Uq := by
    simpa [MonoidHom.range_eq_map] using
      (Uq.range_subtype : Uq.subtype.range = Uq)
  have hF_top : F = ⊤ := by
    have hinj : Function.Injective (Subgroup.map Uq.subtype) :=
      Subgroup.map_injective (f := Uq.subtype) Uq.subtype_injective
    apply hinj
    simpa [Fmap, htop_map_Uq] using hFmap_eq_Uq
  have htriv : ActsTrivially (A := P) (G := Uq) := by
    intro a u
    have huF : u ∈ F := by
      simp [F, hF_top]
    exact (FixedPoints.mem_subgroup (M := P) (a := u)).mp huF a
  have hsub : Subsingleton P := by
    refine ⟨?_⟩
    intro a b
    apply Subtype.ext
    ext u
    change ((a • u : Uq) : G ⧸ cf.V) = ((b • u : Uq) : G ⧸ cf.V)
    exact congrArg (fun x : Uq => (x : G ⧸ cf.V))
      ((htriv a u).trans (htriv b u).symm)
  have hcard_one : Nat.card P = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  change P = ⊥
  exact (Subgroup.card_eq_one (H := P)).1 hcard_one

private theorem CFSG.chiefFactor_conj_composed_range_pCore_eq_bot_local
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    {p : ℕ} [Fact p.Prime] (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p) :
    letI : cf.V.Normal := cf.isChief.normal_K
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    let φ : G →* MulAut Uq := (MulAut.conjNormal (H := Uq)).comp π
    pCore p φ.range = ⊥ := by
  classical
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
  let φ0 : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  let φ : G →* MulAut Uq := φ0.comp π
  have hrange : φ.range = φ0.range := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨π g, rfl⟩
    · rintro ⟨q, rfl⟩
      rcases QuotientGroup.mk'_surjective (N := cf.V) q with ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  have hbot : pCore p φ0.range = ⊥ := by
    simpa [φ0, π, Uq] using
      chiefFactor_conj_range_pCore_eq_bot_local (G := G) (p := p) hsolv cf hcf_p
  change pCore p φ.range = ⊥
  rw [hrange]
  exact hbot


private theorem CFSG.mapped_Op_p'p_map_pPrimeCore_eq_pCore_local
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (GStar : Subgroup G) [GStar.Normal] :
    let M : Subgroup G := (pPrimeCore p GStar).map GStar.subtype
    let N : Subgroup G := (Op_p'p p GStar).map GStar.subtype
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    N.map q = (pCore p (GStar ⧸ pPrimeCore p GStar)).map
      (QuotientGroup.map (pPrimeCore p GStar) M GStar.subtype (by
        intro x hx
        exact Subgroup.mem_map_of_mem GStar.subtype hx)) := by
  classical
  intro M N q
  let q0 : GStar →* GStar ⧸ pPrimeCore p GStar := QuotientGroup.mk' (pPrimeCore p GStar)
  let ψ : GStar ⧸ pPrimeCore p GStar →* G ⧸ M :=
    QuotientGroup.map (pPrimeCore p GStar) M GStar.subtype (by
      intro x hx
      exact Subgroup.mem_map_of_mem GStar.subtype hx)
  have hmapN0 : (Op_p'p p GStar).map q0 = pCore p (GStar ⧸ pPrimeCore p GStar) := by
    dsimp [Op_p'p, q0]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p GStar))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p GStar))
        (H := pCore p (GStar ⧸ pPrimeCore p GStar)))
  have hcomp : q.comp GStar.subtype = ψ.comp q0 := by
    ext x
    rfl
  calc
    N.map q = ((Op_p'p p GStar).map GStar.subtype).map q := rfl
    _ = (Op_p'p p GStar).map (q.comp GStar.subtype) := by rw [Subgroup.map_map]
    _ = (Op_p'p p GStar).map (ψ.comp q0) := by rw [hcomp]
    _ = ((Op_p'p p GStar).map q0).map ψ := by rw [Subgroup.map_map]
    _ = (pCore p (GStar ⧸ pPrimeCore p GStar)).map ψ := by rw [hmapN0]

private theorem CFSG.chiefFactor_upper_le_Op_p'p_map_comap_mk'_sup_lower
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (GStar : Subgroup G) [GStar.Normal]
    (hrank : primeRank p GStar ≤ 2) (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p)
    (hcfU : cf.U ≤ GStar) :
    let M : Subgroup G := (pPrimeCore p GStar).map GStar.subtype
    let N : Subgroup G := (Op_p'p p GStar).map GStar.subtype
    cf.U ≤ (N.map (QuotientGroup.mk' M)).comap (QuotientGroup.mk' M) ⊔ cf.V := by
  classical
  intro M N
  have hupper : cf.U ≤ N ⊔ cf.V := by
    simpa [N] using
      chiefFactor_upper_le_Op_p'p_sup_lower_of_isPFactor
        (G := G) (p := p) hsolv hodd GStar hrank cf hcf_p hcfU
  have hN_le_comap : N ≤ (N.map (QuotientGroup.mk' M)).comap (QuotientGroup.mk' M) := by
    intro x hx
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' M) hx
  exact hupper.trans (sup_le_sup hN_le_comap le_rfl)

public theorem CFSG.corollary_4_19 {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (GStar : Subgroup G) [GStar.Normal]
    (hrank : primeRank p GStar ≤ 2) (cf : ChiefFactor G) (hcf_p : cf.IsPFactor p)
    (hcfU : cf.U ≤ GStar) :
    derivedSubgroup G ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
  classical
  let M : Subgroup G := (pPrimeCore p GStar).map GStar.subtype
  let N : Subgroup G := (Op_p'p p GStar).map GStar.subtype
  have : M.Normal := by
    dsimp [M]
    infer_instance
  have hMcop : Nat.Coprime p (Nat.card M) := by
    have hcard : Nat.card M = Nat.card (pPrimeCore p GStar) := by
      exact Subgroup.card_map_of_injective (K := pPrimeCore p GStar) (f := GStar.subtype)
        GStar.subtype_injective
    rw [hcard]
    exact pPrimeCore_coprime_card (G := GStar) (p := p)
  have hU_le : cf.U ≤ (N.map (QuotientGroup.mk' M)).comap (QuotientGroup.mk' M) ⊔ cf.V := by
    simpa [M, N] using
      chiefFactor_upper_le_Op_p'p_map_comap_mk'_sup_lower
        (G := G) (p := p) hsolv hodd GStar hrank cf hcf_p hcfU
  have himage_p :
      letI : cf.V.Normal := cf.isChief.normal_K
      let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
      letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      IsPGroup p ((derivedSubgroup G).map ((MulAut.conjNormal (H := Uq)).comp π)) := by
    have : cf.V.Normal := cf.isChief.normal_K
    have : (Op_p'p p GStar).Characteristic := Op_p'p_characteristic_local (H := GStar) (p := p)
    have : N.Normal := by
      dsimp [N]
      infer_instance
    let qM : G →* G ⧸ M := QuotientGroup.mk' M
    let R : Subgroup (G ⧸ M) := N.map qM
    have : R.Normal := by
      dsimp [R, qM]
      exact (inferInstance : N.Normal).map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
    have hR_eq : R = (pCore p (GStar ⧸ pPrimeCore p GStar)).map
        (QuotientGroup.map (pPrimeCore p GStar) M GStar.subtype (by
          intro x hx
          exact Subgroup.mem_map_of_mem GStar.subtype hx)) := by
      simpa [R, qM, M, N] using
        mapped_Op_p'p_map_pPrimeCore_eq_pCore_local (G := G) (p := p) GStar
    have hR_p : IsPGroup p R := by
      rw [hR_eq]
      exact IsPGroup.map (p := p) (H := pCore p (GStar ⧸ pPrimeCore p GStar))
        (pCore_isPGroup (G := GStar ⧸ pPrimeCore p GStar) (p := p)) _
    have hR_rank : groupRank R ≤ 2 := by
      rw [hR_eq]
      let P : Subgroup (GStar ⧸ pPrimeCore p GStar) := pCore p (GStar ⧸ pPrimeCore p GStar)
      let ψ : GStar ⧸ pPrimeCore p GStar →* G ⧸ M :=
        QuotientGroup.map (pPrimeCore p GStar) M GStar.subtype (by
          intro x hx
          exact Subgroup.mem_map_of_mem GStar.subtype hx)
      have hψ_inj : Function.Injective ψ := by
        intro a b hab
        rcases QuotientGroup.mk'_surjective (N := pPrimeCore p GStar) a with ⟨x, rfl⟩
        rcases QuotientGroup.mk'_surjective (N := pPrimeCore p GStar) b with ⟨y, rfl⟩
        apply QuotientGroup.eq.mpr
        have hxyM : (GStar.subtype x)⁻¹ * GStar.subtype y ∈ M := QuotientGroup.eq.mp hab
        rcases hxyM with ⟨m, hm, hmxy⟩
        have hm_sub : m = x⁻¹ * y := by
          apply GStar.subtype_injective
          simpa [GStar.coe_mul, GStar.coe_inv, mul_assoc] using hmxy
        rw [hm_sub] at hm
        exact hm
      let eP : P ≃* P.map ψ := Subgroup.equivMapOfInjective P ψ hψ_inj
      have hP_rank : groupRank P ≤ 2 := by
        simpa [P] using groupRank_pCore_quotient_pPrimeCore_le_two (H := GStar) (p := p) hrank
      have hmap_rank : groupRank (P.map ψ) ≤ 2 :=
        (groupRank_le_of_equiv (R := P) (S := P.map ψ) eP).trans hP_rank
      simpa [P, ψ] using hmap_rank
    have hderR_p : IsPGroup p ((derivedSubgroup G).map ((MulAut.conjNormal (H := R)).comp qM)) := by
      have hp_mem_GStar : p ∣ Nat.card GStar :=
        prime_dvd_natCard_of_isPFactor_of_le (G := G) (p := p) cf hcf_p hcfU
      have hp_mem_G : p ∣ Nat.card G := hp_mem_GStar.trans (Subgroup.card_subgroup_dvd_card GStar)
      have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat hodd hp_mem_G
      let : Fact (IsPGroup p R) := ⟨hR_p⟩
      exact derived_image_isPGroup_of_mulAut_range_rank_le_two
        (G := G) (R := R) (p := p) hpodd hsolv hodd hR_rank
        ((MulAut.conjNormal (H := R)).comp qM)
    simpa [qM, R] using
      chiefFactor_derived_conj_image_isPGroup_of_covered_coprime_quotient_action
        (G := G) (p := p) (M := M) hMcop cf hcf_p (R := R)
        (by simpa [qM, R] using hU_le) (by simpa [qM, R] using hderR_p)
  have hpcore_bot :
      letI : cf.V.Normal := cf.isChief.normal_K
      let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
      letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      pCore p ((MulAut.conjNormal (H := Uq)).comp π).range = ⊥ := by
    simpa using chiefFactor_conj_composed_range_pCore_eq_bot_local
      (G := G) (p := p) hsolv cf hcf_p
  exact derivedSubgroup_le_centralizerOfChiefFactor_of_chief_conj_image_isPGroup
    (G := G) (p := p) cf himage_p hpcore_bot

end Main
