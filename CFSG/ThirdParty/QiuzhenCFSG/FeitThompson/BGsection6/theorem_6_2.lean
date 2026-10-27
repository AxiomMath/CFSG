module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.theorem_6_1
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct commutatorElement

/-! # Theorem 6.2 from BG Section 6 -/

private theorem CFSG.chief_conj_range_pCore_eq_bot_local
    {G : Type*} [Group G] [Finite G] (cf : ChiefFactor G) [cf.V.Normal]
    {p : ℕ} [Fact p.Prime]
    (hUq_elem :
      let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
      let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
      letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
      IsElementaryAbelian p (↥Uq)) :
    let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
    let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
    letI : Uq.Normal := cf.isChief.normal_H.map π (QuotientGroup.mk'_surjective cf.V)
    let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
    pCore p φ.range = ⊥ := by
  classical
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hmin :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal_local (G := G) cf
  let : Uq.Normal := hmin.1
  let : IsElementaryAbelian p (↥Uq) := by
    simpa [π, Uq] using hUq_elem
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
      simpa [F, fixedPointSubgroup, FixedPoints.mem_subgroup] using
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
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hu ⊢
      exact smul_mem_fixedPoints_of_normal (H := P) a hu
    · intro hu
      change a • u ∈ fixedPointSubgroup P Uq at hu
      change u ∈ fixedPointSubgroup P Uq
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hu ⊢
      have hsmul := smul_mem_fixedPoints_of_normal (H := P) a⁻¹ hu
      simpa [mul_smul] using hsmul
  let Fmap : Subgroup (G ⧸ cf.V) := F.map Uq.subtype
  have hFmap_normal : Fmap.Normal := by
    refine ⟨?_⟩
    intro x hx g
    rcases Subgroup.mem_map.mp hx with ⟨u, huF, rfl⟩
    let ag : A := ⟨φ g, ⟨g, rfl⟩⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨ag • u, (hF_inv.invariant ag u).1 huF, ?_⟩
    change (((φ g) u : Uq) : G ⧸ cf.V) = g * (u : G ⧸ cf.V) * g⁻¹
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
    have ha := htriv a u
    have hb := htriv b u
    change ((a : A) : MulAut Uq) u = u at ha
    change ((b : A) : MulAut Uq) u = u at hb
    exact congrArg Subtype.val (ha.trans hb.symm)
  have hcard_one : Nat.card P = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  change P = ⊥
  exact (Subgroup.card_eq_one (H := P)).1 hcard_one

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.odd_order_pstable_le_centralizerOfChiefFactor
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (ho : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Q A : Subgroup G} [Q.Normal]
    (hQp : IsPGroup p Q) (hAp : IsPGroup p A)
    (hcomm2 : ⁅⁅Q, A⁆, A⁆ = ⊥)
    (cf : ChiefFactor G) (hcfU_le_Q : cf.U ≤ Q) :
    A ≤ centralizerOfChiefFactor (G := G) (⊤ : Subgroup G) cf := by
  classical
  have hQA_cent : ⁅Q, A⁆ ≤ Subgroup.centralizer (A : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm2
  let Usub : Subgroup Q := cf.U.subgroupOf Q
  have hUsub_p : IsPGroup p Usub := hQp.to_subgroup Usub
  have hcfU_p : IsPGroup p cf.U := by
    exact hUsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := cf.U) (K := Q) hcfU_le_Q)
  have : cf.V.Normal := cf.isChief.normal_K
  let π : G →* G ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (G ⧸ cf.V) := cf.U.map π
  have hUq_min :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (G ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using chiefFactor_quotient_minimal_local (G := G) cf
  let : Uq.Normal := hUq_min.1
  have hUq_p : IsPGroup p Uq := by
    simpa [Uq, π] using hcfU_p.map π
  obtain ⟨q, hqprime, hUq_elem'⟩ :=
    chiefFactor_quotient_exists_isElementaryAbelian (G := G) inferInstance cf
  let : Fact q.Prime := ⟨hqprime⟩
  have hq_dvd_card : q ∣ Nat.card Uq := by
    have hUq_nontrivial : Nontrivial Uq := (Subgroup.nontrivial_iff_ne_bot Uq).2 hUq_min.2.1
    have hUq_q : IsPGroup q Uq := IsElementaryAbelian.isPGroup q Uq
    rcases (IsPGroup.nontrivial_iff_card (p := q) (G := Uq) (hG := hUq_q)).1 hUq_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self q (Nat.pos_iff_ne_zero.mp hn)
  rcases IsPGroup.iff_card.mp hUq_p with ⟨n, hn⟩
  have hq_eq_p : q = p := by
    exact Nat.prime_eq_prime_of_dvd_pow hqprime Fact.out (hn ▸ hq_dvd_card)
  have hUq_elem : IsElementaryAbelian p (↥Uq) := by
    simpa [hq_eq_p] using hUq_elem'
  let : IsElementaryAbelian p (↥Uq) := hUq_elem
  let : CommGroup Uq := IsMulCommutative.instCommGroup
  let φ : (G ⧸ cf.V) →* MulAut Uq := MulAut.conjNormal (H := Uq)
  have hφ_pcore_bot : pCore p φ.range = ⊥ := by
    simpa [π, Uq, φ] using
      chief_conj_range_pCore_eq_bot_local (G := G) (cf := cf) (p := p) hUq_elem
  have hquot_odd : Odd (Nat.card (G ⧸ cf.V)) := by
    exact odd_of_card_dvd ho (Subgroup.card_quotient_dvd_card (s := cf.V))
  have hφ_odd : Odd (Nat.card φ.range) := by
    have hker_odd : Odd (Nat.card ((G ⧸ cf.V) ⧸ φ.ker)) := by
      exact odd_of_card_dvd hquot_odd (Subgroup.card_quotient_dvd_card (s := φ.ker))
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact hker_odd
  let ρ : Representation (ZMod p) φ.range (Additive Uq) :=
    Theory.Representation.ofElementaryAbelianAction (A := φ.range) (G := Uq) (p := p)
  have hρ_faithful : Function.Injective ρ := by
    have hρker_bot : ρ.ker = ⊥ := by
      rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
      rw [fixingSubgroupOf_univ_eq_ker_toMulAut]
      exact (MonoidHom.ker_eq_bot_iff (φ.range.subtype)).2 φ.range.subtype_injective
    exact (MonoidHom.ker_eq_bot_iff ρ).1 hρker_bot
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have h83 :
      Odd p → pCore p φ.range = ⊥ → Odd (Nat.card φ.range) →
        ¬ PStableGroup p φ.range → False := by
    intro hpodd' hpcore' hodd'
    exact gorenstein_3_8_3_not_pStable_false
      (G := φ.range) (p := p) hpodd' hpcore' hodd'
  have hρ_pstable : PStableRepresentation p ρ := by
    have hφ_pstable : PStableGroup p φ.range :=
      pStable_of_odd_order_3_8_3 (G := φ.range) (p := p)
        h83 hpodd hφ_pcore_bot hφ_odd
    exact hφ_pstable (ZMod p) (Additive Uq) ρ hρ_faithful
  intro a ha
  let ψ : A →* φ.range :=
    ((φ.comp π).comp A.subtype).codRestrict φ.range (by
      intro x
      exact ⟨π (x : G), rfl⟩)
  let z : φ.range := ψ ⟨a, ha⟩
  have hz_p : IsPElement (p := p) z := by
    obtain ⟨n, hn'⟩ := (IsPGroup.iff_orderOf (p := p) (G := A)).1 hAp ⟨a, ha⟩
    have hdiv : orderOf z ∣ p ^ n := by
      exact (orderOf_map_dvd (ψ := ψ) ⟨a, ha⟩).trans (by simp [hn'])
    rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hdiv with ⟨m, _hm, hm⟩
    exact ⟨m, hm⟩
  have hdev (u : Uq) :
      (ρ z - 1) (Additive.ofMul u) = Additive.ofMul ((z • u) / u) := by
    rw [LinearMap.sub_apply, Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    change Additive.ofMul (z • u) - Additive.ofMul u = Additive.ofMul ((z • u) / u)
    rw [sub_eq_add_neg]
    simp [div_eq_mul_inv]
  have hfirst_fix (u : Uq) : z • (((z • u) / u : Uq)) = ((z • u) / u : Uq) := by
    rcases Subgroup.mem_map.mp u.2 with ⟨y, hyU, hy_eq⟩
    let uy : Uq := ⟨π y, Subgroup.mem_map_of_mem π hyU⟩
    have hu_eq : u = uy := Subtype.ext (by simpa [uy] using hy_eq.symm)
    subst hu_eq
    let d : Uq := ((z • uy) / uy : Uq)
    have hd_val : (d : G ⧸ cf.V) = π ⁅(a : G), y⁆ := by
      calc
        (d : G ⧸ cf.V) =
            ((z • uy : Uq) : G ⧸ cf.V) * ((uy : G ⧸ cf.V))⁻¹ := by
              simp [d, div_eq_mul_inv]
        _ =
            (π (a : G)) * π y * (π (a : G))⁻¹ * (π y)⁻¹ := by
              simp [z, ψ, uy, φ, π, MulAut.conjNormal_apply, mul_assoc]
        _ = π ⁅(a : G), y⁆ := by
              simp [π, commutatorElement_def, mul_assoc]
    have hcomm_mem' : ⁅y, (a : G)⁆ ∈ ⁅Q, A⁆ :=
      Subgroup.commutator_mem_commutator (hcfU_le_Q hyU) ha
    have hcomm_mem : ⁅(a : G), y⁆ ∈ ⁅Q, A⁆ := by
      simpa [commutatorElement_inv] using (⁅Q, A⁆).inv_mem hcomm_mem'
    have hcommU : ⁅(a : G), y⁆ ∈ cf.U := by
      have haya : (a : G) * y * (a : G)⁻¹ ∈ cf.U :=
        cf.isChief.normal_H.conj_mem y hyU (a : G)
      simpa [commutatorElement_def, mul_assoc] using cf.U.mul_mem haya (cf.U.inv_mem hyU)
    have hcent_d : ⁅(a : G), y⁆ ∈ Subgroup.centralizer (A : Set G) := hQA_cent hcomm_mem
    have hfix_d : (a : G) * ⁅(a : G), y⁆ * (a : G)⁻¹ = ⁅(a : G), y⁆ := by
      let c : G := ⁅(a : G), y⁆
      have hcomm : (a : G) * c = c * (a : G) := by
        simpa [c] using (Subgroup.mem_centralizer_iff.mp hcent_d) (a : G) ha
      calc
        (a : G) * ⁅(a : G), y⁆ * (a : G)⁻¹ = (a : G) * c * (a : G)⁻¹ := by rfl
        _ = c * (a : G) * (a : G)⁻¹ := by rw [hcomm]
        _ = c := by simp [mul_assoc]
        _ = ⁅(a : G), y⁆ := by rfl
    let d0 : Uq := ⟨π ⁅(a : G), y⁆, Subgroup.mem_map_of_mem π hcommU⟩
    have hd_eq : d = d0 := Subtype.ext (by simpa [d0] using hd_val)
    have hfix_d0 : z • d0 = d0 := by
      apply Subtype.ext
      calc
        ((z • d0 : Uq) : G ⧸ cf.V) =
            π ((a : G) * ⁅(a : G), y⁆ * (a : G)⁻¹) := by
              change
                π (a : G) * π ⁅(a : G), y⁆ * (π (a : G))⁻¹ =
                  π ((a : G) * ⁅(a : G), y⁆ * (a : G)⁻¹)
              rw [map_mul, map_mul, map_inv]
        _ = π ⁅(a : G), y⁆ := by
              simpa [π] using congrArg π hfix_d
        _ = (d0 : G ⧸ cf.V) := rfl
    change z • d = d
    simpa [hd_eq] using hfix_d0
  have hsq : (ρ z - 1) ^ 2 = 0 := by
    ext v
    cases v with
    | ofMul u =>
        rw [pow_two, Module.End.mul_eq_comp]
        have hsq_u : ((ρ z - 1) ∘ₗ (ρ z - 1)) (Additive.ofMul u) = 0 := by
          rw [LinearMap.comp_apply, hdev u, hdev (((z • u) / u : Uq))]
          change Additive.ofMul (z • (((z • u) / u : Uq)) / (((z • u) / u : Uq))) = Additive.ofMul 1
          exact congrArg Additive.ofMul (by simp [hfirst_fix u])
        simpa using
          congrArg (fun x : Additive Uq => (((x.toMul : Uq) : G ⧸ cf.V))) hsq_u
  have hzρ : ρ z = 1 := eq_one_of_pStable_square_zero ρ hρ_pstable hz_p hsq
  have hz_eq_one : z = 1 := hρ_faithful (by simpa using hzρ)
  have hphi_one : φ (π (a : G)) = 1 := by
    simpa [z, ψ] using congrArg Subtype.val hz_eq_one
  refine (mem_centralizerOfChiefFactor (G := G) (H := (⊤ : Subgroup G)) (cf := cf) (g := a)).2 ?_
  refine ⟨by simp, ?_⟩
  intro u hu
  let uq : Uq := ⟨π u, Subgroup.mem_map_of_mem π hu⟩
  have hfix_u : (φ (π (a : G))) uq = uq := by
    simpa using congrArg (fun f : MulAut Uq => f uq) hphi_one
  have hqeq : π ((a : G) * u * (a : G)⁻¹) = π u := by
    exact congrArg Subtype.val hfix_u
  have hdiv_mem : ((a : G) * u * (a : G)⁻¹) / u ∈ cf.V :=
    (QuotientGroup.eq_iff_div_mem (N := cf.V)
      (x := (a : G) * u * (a : G)⁻¹) (y := u)).1 hqeq
  simpa [commutatorElement_def, div_eq_mul_inv, mul_assoc] using hdiv_mem

private theorem CFSG.quotient_pPrimeCore_subgroupMap_injective_local
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hHp : IsPGroup p H) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore p G)).comp H.subtype) := by
  let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
  have hcoprime :
      Nat.Coprime (Nat.card H) (Nat.card (pPrimeCore p G)) := by
    rcases IsPGroup.iff_card.mp hHp with ⟨n, hcard⟩
    rw [hcard]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hinf_bot : H ⊓ pPrimeCore p G = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcoprime).eq_bot
  have hker_bot :
      (((q.comp H.subtype)).ker : Subgroup H) = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxM : ((x : H) : G) ∈ pPrimeCore p G := by
        exact
          (QuotientGroup.eq_one_iff (N := pPrimeCore p G) (x := ((x : H) : G))).1 hx
      have hxbot : ((x : H) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinf_bot]
        exact ⟨x.2, hxM⟩
      simpa using hxbot
    · intro hx
      change q ((x : H) : G) = 1
      have hx1 : x = 1 := by
        simpa [Subgroup.mem_bot] using hx
      rw [hx1]
      simp [q]
  exact (MonoidHom.ker_eq_bot_iff (q.comp H.subtype)).1 hker_bot

set_option maxHeartbeats 800000 in
public theorem CFSG.theorem_6_2
    {G : Type*} [Group G] [Group.IsSolvable G] (ho : Odd (Nat.card G))
    {p : ℕ} [inst : Fact p.Prime] (S : Sylow p G) :
    (centerIn (thompsonSubgroup S) ⊔ pPrimeCore p G).Normal := by
  classical
  let _ : Finite G := card_odd_finite ho
  let M : Subgroup G := pPrimeCore p G
  have hM_normal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hM_normal
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let Pbar : Sylow p (G ⧸ M) :=
    S.mapSurjective (f := q) (QuotientGroup.mk'_surjective M)
  let Z : Subgroup G := thompsonCenter (G := G) (S : Subgroup G)
  have hqinj : Function.Injective (q.comp (S : Subgroup G).subtype) := by
    simpa [M, q] using
      quotient_pPrimeCore_subgroupMap_injective_local
        (G := G) (p := p) (H := (S : Subgroup G)) S.isPGroup'
  have hZ_map :
      Z.map q = thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) := by
    let f : S →* ((S : Subgroup G).map q) :=
      (q.comp (S : Subgroup G).subtype).codRestrict ((S : Subgroup G).map q) (by
        intro x
        exact Subgroup.mem_map_of_mem q x.2)
    let e : S ≃* ((S : Subgroup G).map q) := by
      refine MulEquiv.ofBijective f ⟨?_, ?_⟩
      · intro a b hab
        exact hqinj <| by exact congrArg Subtype.val hab
      intro x
      rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    have hcomp :
        ((Subgroup.subtype ((S : Subgroup G).map q)).comp e.toMonoidHom) =
          q.comp (S : Subgroup G).subtype := by
      rfl
    calc
      Z.map q =
          ((thompsonCenter (G := S) (⊤ : Subgroup S)).map (S : Subgroup G).subtype).map q := by
            rw [thompsonCenter_top_map_subtype]
      _ = (thompsonCenter (G := S) (⊤ : Subgroup S)).map
            (q.comp (S : Subgroup G).subtype) := by
            rw [Subgroup.map_map]
      _ = ((thompsonCenter (G := S) (⊤ : Subgroup S)).map e.toMonoidHom).map
            (Subgroup.subtype ((S : Subgroup G).map q)) := by
            rw [Subgroup.map_map, hcomp]
      _ = (thompsonCenter (G := ((S : Subgroup G).map q))
            (⊤ : Subgroup ((S : Subgroup G).map q))).map
            (Subgroup.subtype ((S : Subgroup G).map q)) := by
            rw [thompsonCenter_top_map_mulEquiv]
      _ = thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) := by
            simpa [Pbar] using
              thompsonCenter_top_map_subtype (G := G ⧸ M) ((S : Subgroup G).map q)
  have hQ_solv : Group.IsSolvable (G ⧸ M) := by infer_instance
  let : Group.IsSolvable (G ⧸ M) := hQ_solv
  have hQ_odd : Odd (Nat.card (G ⧸ M)) := by
    dsimp [M]
    exact odd_of_card_dvd ho (Subgroup.card_quotient_dvd_card (s := pPrimeCore p G))
  have hQ_core : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p)
  have hZbar_le_Op :
      thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) ≤ Op_p'p p (G ⧸ M) := by
    let ZbarP : Subgroup Pbar :=
      (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))).subgroupOf
        (Pbar : Subgroup (G ⧸ M))
    have hZbar_normal : ZbarP.Normal := by
      simpa [ZbarP] using
        thompsonCenter_normal_subgroupOf_sylow (G := G ⧸ M) (p := p) Pbar
    have hZbar_comm : IsMulCommutative ZbarP := by
      let : IsMulCommutative
          (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))) :=
        thompsonCenter_isMulCommutative (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))
      simpa [ZbarP] using
        (inferInstance :
          IsMulCommutative
            ((thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))).subgroupOf
              (Pbar : Subgroup (G ⧸ M))))
    have hZbar_map_le :
        ZbarP.map Pbar.toSubgroup.subtype ≤ Op_p'p p (G ⧸ M) := by
      exact theorem_6_1 (G := G ⧸ M) (p := p) hQ_odd Pbar ZbarP
    have hZbar_map_eq :
        ZbarP.map Pbar.toSubgroup.subtype =
          thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) := by
      calc
        ZbarP.map Pbar.toSubgroup.subtype =
            thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) ⊓
              (Pbar : Subgroup (G ⧸ M)) := by
          simp [ZbarP]
        _ = thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) := by
          exact inf_eq_left.mpr
            (thompsonCenter_le (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)))
    rw [hZbar_map_eq] at hZbar_map_le
    exact hZbar_map_le
  have hZbar_le_pCore :
      thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    rwa [Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ M) (p := p) hQ_core] at hZbar_le_Op
  have hZbar_normal :
      (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))).Normal := by
    by_cases hpCorebar_bot : pCore p (G ⧸ M) = ⊥
    · have hZbar_bot :
          thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) = ⊥ := by
        apply le_antisymm
        · simpa [hpCorebar_bot] using hZbar_le_pCore
        · exact bot_le
      simp [hZbar_bot]
    · have hp2 : p ≠ 2 := by
        rcases IsPGroup.iff_card.mp (pCore_isPGroup (G := G ⧸ M) (p := p)) with ⟨n, hn⟩
        intro hp_eq
        subst hp_eq
        have hnpos : n ≠ 0 := by
          intro hn0
          apply hpCorebar_bot
          apply (Subgroup.eq_bot_iff_card _).2
          simpa [hn0] using hn
        have h2dvd_core : 2 ∣ Nat.card (pCore 2 (G ⧸ M)) := by
          rw [hn]
          exact dvd_pow_self 2 hnpos
        exact hQ_odd.not_two_dvd_nat
          (Nat.dvd_trans h2dvd_core (Subgroup.card_subgroup_dvd_card (pCore 2 (G ⧸ M))))
      have hQ_constrained : PConstrainedGroup (G := G ⧸ M) p := by
        intro Q hQp hQeq
        rw [hQ_core, bot_sup_eq,
          Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ M) (p := p) hQ_core] at hQeq
        rw [hQeq]
        exact
          (centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot
            (G := G ⧸ M) hQ_solv (p := p) hQ_core).trans <| by
              rw [← Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ M) (p := p) hQ_core]
      have hQ_stable' : PStableGroup' (G := G ⧸ M) p := by
        intro Q A htopQ_normal hQp hAp hA_norm hcomm2
        rw [hQ_core, bot_sup_eq] at htopQ_normal
        have hQ_normal : Q.Normal := htopQ_normal
        let : Q.Normal := hQ_normal
        let N : Subgroup (G ⧸ M) := Subgroup.normalizer (Q : Set (G ⧸ M))
        let C : Subgroup (G ⧸ M) := Subgroup.centralizer (Q : Set (G ⧸ M))
        have hnormQ_top : N = ⊤ := by
          dsimp [N]
          exact Subgroup.normalizer_eq_top (H := Q)
        have hC_normal : C.Normal := by
          simpa [C] using
            (inferInstance : (Subgroup.centralizer (Q : Set (G ⧸ M))).Normal)
        let : C.Normal := hC_normal
        let : (C.subgroupOf N).Normal := Subgroup.Normal.subgroupOf hC_normal N
        obtain ⟨r, f, hf0, hfr, hf_norm, hf_chief⟩ :=
          exists_chief_series_from_to Q hQ_normal
        have hf_le_Q : ∀ i, i ≤ r → f i ≤ Q := by
          intro i hi
          induction i with
          | zero =>
              simp [hf0]
          | succ i ih =>
              have hir : i < r := by omega
              exact (hf_chief i hir).lt.le.trans (ih (by omega))
        let cf : Fin r → ChiefFactor (G ⧸ M) := fun i =>
          ⟨f (i.1 + 1), f i.1, hf_chief i.1 i.2⟩
        let H : Subgroup (G ⧸ M) :=
          ⨅ i : Fin r, centralizerOfChiefFactor (G := G ⧸ M) (⊤ : Subgroup (G ⧸ M)) (cf i)
        have hA_le_H : A ≤ H := by
          intro a ha
          rw [Subgroup.mem_iInf]
          intro i
          have hA_le_cf :
              A ≤ centralizerOfChiefFactor (G := G ⧸ M) (⊤ : Subgroup (G ⧸ M)) (cf i) :=
            odd_order_pstable_le_centralizerOfChiefFactor
              (G := G ⧸ M) hQ_odd (p := p) hp2 hQp hAp hcomm2 (cf i)
              (hf_le_Q i.1 (Nat.le_of_lt i.2))
          exact hA_le_cf ha
        have hH_normal : H.Normal := by
          dsimp [H]
          refine Subgroup.normal_iInf_normal (fun i => ?_)
          simpa [cf] using
            (centralizerOfChiefFactor_normal (G := G ⧸ M) (H := (⊤ : Subgroup (G ⧸ M)))
              (hH := (inferInstance : (⊤ : Subgroup (G ⧸ M)).Normal)) (cf i))
        let : H.Normal := hH_normal
        have hH_normQ : H ≤ N := by
          rw [hnormQ_top]
          exact le_top
        let : MulDistribMulAction H Q :=
          Subgroup.conjMulDistribMulActionOfLeNormalizer H Q hH_normQ
        have hfix_eq_Csub :
            fixingSubgroupOf H Q (Set.univ : Set Q) = C.subgroupOf H := by
          ext h
          rw [mem_fixingSubgroup_iff]
          constructor
          · intro hh
            change (h : G ⧸ M) ∈ C
            rw [Subgroup.mem_centralizer_iff]
            intro x hx
            have hfix : h • (⟨x, hx⟩ : Q) = (⟨x, hx⟩ : Q) := hh ⟨x, hx⟩ (by trivial)
            have hconj : (h : G ⧸ M) * x * (h : G ⧸ M)⁻¹ = x := by
              simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using
                congrArg Subtype.val hfix
            simpa [mul_assoc] using
              (congrArg (fun t : G ⧸ M => t * (h : G ⧸ M)) hconj).symm
          · intro hhC x hx
            apply Subtype.ext
            have hcomm : x * (h : G ⧸ M) = (h : G ⧸ M) * x :=
              (Subgroup.mem_centralizer_iff.mp hhC) x (by simp)
            have hconj : (h : G ⧸ M) * x * (h : G ⧸ M)⁻¹ = x := by
              simpa [mul_assoc] using
                congrArg (fun t : G ⧸ M => t * (h : G ⧸ M)⁻¹) hcomm.symm
            simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using
              hconj
        have hker_normal : (fixingSubgroupOf H Q (Set.univ : Set Q)).Normal := by
          rw [hfix_eq_Csub]
          exact Subgroup.Normal.subgroupOf hC_normal H
        let πset : Set Nat.Primes := {⟨p, Fact.out⟩}
        have hQ_pi : IsPiGroup πset Q := by
          rw [IsPiGroup_iff πset Q]
          intro q hqdvd
          rcases hQp.exists_card_eq with ⟨n, hn⟩
          have hqdvd_pow : q.1 ∣ p ^ n := by
            simpa [hn] using hqdvd
          have hq_eq : q.1 = p := Nat.prime_eq_prime_of_dvd_pow q.2 Fact.out hqdvd_pow
          have hq_eq' : q = ⟨p, Fact.out⟩ := by
            apply Subtype.ext
            simpa using hq_eq
          dsimp [πset]
          exact Set.mem_singleton_iff.mpr hq_eq'
        let Gi : ℕ → Subgroup Q := fun i =>
          if hi : i ≤ r then (f i).subgroupOf Q else ⊥
        have hGi_zero : Gi 0 = ⊤ := by
          simp [Gi, hf0]
        have hGi_bot : Gi (r + 1) = ⊥ := by
          simp [Gi]
        have hGi_desc : ∀ i, Gi (i + 1) ≤ Gi i := by
          intro i x hx
          by_cases hi : i < r
          · have hi0 : i ≤ r := Nat.le_of_lt hi
            have hi1 : i + 1 ≤ r := Nat.succ_le_of_lt hi
            have hx' : (x : G ⧸ M) ∈ f (i + 1) := by
              simpa [Gi, hi1, Subgroup.mem_subgroupOf] using hx
            have hx'' : (x : G ⧸ M) ∈ f i := (hf_chief i hi).lt.le hx'
            simpa [Gi, hi0, Subgroup.mem_subgroupOf] using hx''
          · have hi1_not : ¬ i + 1 ≤ r := by omega
            have hxbot : x ∈ (⊥ : Subgroup Q) := by
              simpa [Gi, hi1_not] using hx
            by_cases hi0 : i ≤ r
            · have hi_eq : i = r := by omega
              simpa [Gi, hi0, hi_eq, hfr] using hxbot
            · simpa [Gi, hi0] using hxbot
        have hGi_normal : ∀ i, (Gi i).Normal := by
          intro i
          by_cases hi : i ≤ r
          · simpa [Gi, hi] using Subgroup.Normal.subgroupOf (hf_norm i hi) Q
          · simp [Gi, hi]
        have hGi_inv : ∀ i, IsInvariant H Q (Gi i) := by
          intro i
          by_cases hi : i ≤ r
          · have hH_norm_fi : H ≤ Subgroup.normalizer (f i : Set (G ⧸ M)) := by
              let : (f i).Normal := hf_norm i hi
              simpa using
                (Subgroup.le_normalizer_of_normal (H := f i) :
                  H ≤ Subgroup.normalizer (f i : Set (G ⧸ M)))
            refine ⟨?_⟩
            intro h x
            constructor
            · intro hx
              have hx' : (x : G ⧸ M) ∈ f i := by
                simpa [Gi, hi, Subgroup.mem_subgroupOf] using hx
              have hconj : (h : G ⧸ M) * (x : G ⧸ M) * (h : G ⧸ M)⁻¹ ∈ f i :=
                (Subgroup.mem_normalizer_iff.mp (hH_norm_fi h.2) (x : G ⧸ M)).1 hx'
              simpa [Gi, hi, Subgroup.mem_subgroupOf,
                Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using hconj
            · intro hx
              have hhInv : ((h : G ⧸ M)⁻¹) ∈ Subgroup.normalizer (f i : Set (G ⧸ M)) := by
                exact (Subgroup.normalizer (f i : Set (G ⧸ M))).inv_mem (hH_norm_fi h.2)
              have hx' : (h : G ⧸ M) * (x : G ⧸ M) * (h : G ⧸ M)⁻¹ ∈ f i := by
                simpa [Gi, hi, Subgroup.mem_subgroupOf,
                  Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH_normQ] using hx
              have hback :
                  ((h : G ⧸ M)⁻¹ * (((h : G ⧸ M) * (x : G ⧸ M) * (h : G ⧸ M)⁻¹)) *
                    (((h : G ⧸ M)⁻¹)⁻¹)) ∈ f i :=
                (Subgroup.mem_normalizer_iff.mp hhInv _).1 hx'
              have hx'' : (x : G ⧸ M) ∈ f i := by
                simpa [mul_assoc] using hback
              simpa [Gi, hi, Subgroup.mem_subgroupOf] using hx''
          · refine ⟨?_⟩
            intro h x
            constructor
            · intro hx
              have hxbot : x ∈ (⊥ : Subgroup Q) := by
                simpa [Gi, hi] using hx
              have hxEq : x = 1 := by simpa using hxbot
              subst x
              simp [Gi, hi]
            · intro hx
              have hxbot : h • x ∈ (⊥ : Subgroup Q) := by
                simpa [Gi, hi] using hx
              have hxEq : h • x = 1 := by
                simpa using hxbot
              have hx' : ((h : G ⧸ M) * (x : G ⧸ M) * (h : G ⧸ M)⁻¹) = 1 := by
                simpa using (congrArg Subtype.val hxEq : ((h • x : Q) : G ⧸ M) = 1)
              have hx'' : (x : G ⧸ M) = 1 := by
                calc
                  (x : G ⧸ M) =
                      (h : G ⧸ M)⁻¹ * (((h : G ⧸ M) * (x : G ⧸ M) * (h : G ⧸ M)⁻¹)) *
                        (h : G ⧸ M) := by group
                  _ = 1 := by simp [hx']
              have hxbot : x ∈ (⊥ : Subgroup Q) := by
                apply Subgroup.mem_bot.mpr
                apply Subtype.ext
                simpa using hx''
              simpa [Gi, hi] using hxbot
        have hGi_triv :
            ∀ i (aH : H) (x : Q), x ∈ Gi i → (aH • x) * x⁻¹ ∈ Gi (i + 1) := by
          intro i aH x hx
          by_cases hi : i < r
          · let cfi : ChiefFactor (G ⧸ M) := ⟨f (i + 1), f i, hf_chief i hi⟩
            have hH_cent :
                H ≤ centralizerOfChiefFactor (G := G ⧸ M) (⊤ : Subgroup (G ⧸ M)) cfi := by
              let j : Fin r := ⟨i, hi⟩
              have htmp :
                  H ≤ centralizerOfChiefFactor (G := G ⧸ M) (⊤ : Subgroup (G ⧸ M)) (cf j) :=
                iInf_le _ j
              simpa [cfi, cf, j] using htmp
            have hcomm_le : ⁅H, cfi.U⁆ ≤ cfi.V :=
                (le_centralizerOfChiefFactor_iff
                  (G := G ⧸ M) (H := (⊤ : Subgroup (G ⧸ M))) (N := H) (cf := cfi)).1 hH_cent |>.2
            have hxfi : (x : G ⧸ M) ∈ f i := by
              simpa [Gi, Nat.le_of_lt hi, Subgroup.mem_subgroupOf] using hx
            have hmem : ⁅(aH : G ⧸ M), (x : G ⧸ M)⁆ ∈ f (i + 1) := by
              exact hcomm_le (Subgroup.commutator_mem_commutator aH.property hxfi)
            have hi1 : i + 1 ≤ r := Nat.succ_le_of_lt hi
            simpa [Gi, hi1, Subgroup.mem_subgroupOf,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
              div_eq_mul_inv, commutatorElement_def, mul_assoc] using hmem
          · have hxbot : x ∈ (⊥ : Subgroup Q) := by
              by_cases hir : i ≤ r
              · have hi_eq : i = r := by omega
                simpa [Gi, hir, hi_eq, hfr] using hx
              · simpa [Gi, hir] using hx
            have hx_eq_one : x = 1 := by simpa using hxbot
            have hi1_not : ¬ i + 1 ≤ r := by omega
            subst x
            simp [Gi, hi1_not]
        have hstab :
            ∃ (ι : Type) (Gi' : ι → Subgroup Q) (next : ι → ι),
              StabilizesNormalSeries (G := Q) (A := H) Gi' next := by
          have hseries : StabilizesNormalSeries (G := Q) (A := H) Gi Nat.succ := by
            refine ⟨⟨0, r + 1, hGi_zero, hGi_bot, ⟨r + 1, ?_⟩⟩,
              hGi_desc, hGi_normal, hGi_inv, hGi_triv⟩
            simpa using Nat.succ_iterate 0 (r + 1)
          exact ⟨Nat, Gi, Nat.succ, hseries⟩
        have hHquot_pi :
            IsPiGroup πset (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := by
          exact lemma_1_9 (G := Q) (A := H) πset (inferInstance : Group.IsSolvable ↥Q) hQ_pi
            hstab hker_normal
        have hHquot_p :
            IsPGroup p (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := by
          refine (IsPGroup.iff_card (p := p) (G := H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q))).2 ?_
          have hpos : 0 < Nat.card (H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q)) := Nat.card_pos (α := H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q))
          refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_⟩
          intro q hqprime hqdvd
          let q' : Nat.Primes := ⟨q, hqprime⟩
          have hq_mem : q' ∈ πset := (IsPiGroup_iff πset _).1 hHquot_pi q' hqdvd
          have hq_eq' : q' = ⟨p, Fact.out⟩ := by
            exact Set.mem_singleton_iff.mp (by simpa [πset] using hq_mem)
          simpa using congrArg Subtype.val hq_eq'
        let qCN : N →* N ⧸ C.subgroupOf N := QuotientGroup.mk' (C.subgroupOf N)
        let φH : H →* N := H.subtype.codRestrict N (by
          intro h
          exact hH_normQ h.2)
        let ψH : H →* N ⧸ C.subgroupOf N := qCN.comp φH
        have hψH_ker : ψH.ker = fixingSubgroupOf H Q (Set.univ : Set Q) := by
          calc
            ψH.ker = C.subgroupOf H := by
              ext h
              change qCN (φH h) = 1 ↔ h ∈ C.subgroupOf H
              have hq :
                  qCN (φH h) = 1 ↔ φH h ∈ C.subgroupOf N := by
                simp [qCN]
              have hmem : φH h ∈ C.subgroupOf N ↔ h ∈ C.subgroupOf H := by
                change ((h : G ⧸ M) ∈ C) ↔ ((h : G ⧸ M) ∈ C)
                rfl
              exact hq.trans hmem
            _ = fixingSubgroupOf H Q (Set.univ : Set Q) := hfix_eq_Csub.symm
        let e1 :
            H ⧸ fixingSubgroupOf H Q (Set.univ : Set Q) ≃* H ⧸ ψH.ker :=
          QuotientGroup.quotientMulEquivOfEq hψH_ker.symm
        let e2 : H ⧸ ψH.ker ≃* ψH.range := QuotientGroup.quotientKerEquivRange ψH
        have hHrange_p : IsPGroup p ψH.range := hHquot_p.of_equiv (e1.trans e2)
        have hHrange_eq : ψH.range = (H.subgroupOf N).map qCN := by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨h, rfl⟩
            exact Subgroup.mem_map.mpr ⟨φH h, by
              show ((φH h : N) : G ⧸ M) ∈ H
              exact h.2, rfl⟩
          · intro hy
            rcases Subgroup.mem_map.mp hy with ⟨n, hn, rfl⟩
            let hH : H := ⟨(n : G ⧸ M), hn⟩
            refine ⟨hH, ?_⟩
            change qCN (φH hH) = qCN n
            have hφ : φH hH = n := by
              apply Subtype.ext
              rfl
            rw [hφ]
        have hHmap_p : IsPGroup p ((H.subgroupOf N).map qCN) := by
          rw [← hHrange_eq]
          exact hHrange_p
        have hHmap_normal : ((H.subgroupOf N).map qCN).Normal :=
          (Subgroup.Normal.subgroupOf hH_normal N).map qCN (QuotientGroup.mk'_surjective _)
        have hHmap_le_pCore : (H.subgroupOf N).map qCN ≤ pCore p (N ⧸ C.subgroupOf N) := by
          exact le_sSup ⟨hHmap_normal, hHmap_p⟩
        have hA_sub_le_H_sub : A.subgroupOf N ≤ H.subgroupOf N := by
          intro a ha
          exact hA_le_H ha
        have hAmap_le : (A.subgroupOf N).map qCN ≤ (H.subgroupOf N).map qCN :=
          Subgroup.map_mono hA_sub_le_H_sub
        have hfinal : (A.subgroupOf N).map qCN ≤ pCore p (N ⧸ C.subgroupOf N) :=
          hAmap_le.trans hHmap_le_pCore
        change (A.subgroupOf N).map (QuotientGroup.mk' (C.subgroupOf N)) ≤
            pCore p (N ⧸ C.subgroupOf N)
        simpa [qCN] using hfinal
      have hnormal_sup :
          (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)) ⊔
            pPrimeCore p (G ⧸ M)).Normal := by
        exact G_theorem_8_2_11 (G := G ⧸ M) (p := p) hp2 hpCorebar_bot
          hQ_constrained hQ_stable' Pbar
      rw [hQ_core, sup_bot_eq] at hnormal_sup
      exact hnormal_sup
  have hcomap_eq :
      Subgroup.comap q
          (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))) =
        Z ⊔ M := by
    have hqker : q.ker = M := by
      simp [q]
    calc
      Subgroup.comap q
          (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M))) =
          Subgroup.comap q (Z.map q) := by rw [← hZ_map]
      _ = Z ⊔ M := by
        simpa [hqker, sup_comm] using (Subgroup.comap_map_eq (f := q) (H := Z))
  have hcomap_normal :
      (Subgroup.comap q
        (thompsonCenter (G := G ⧸ M) (Pbar : Subgroup (G ⧸ M)))).Normal := inferInstance
  simpa [Z, M, thompsonCenter] using hcomap_eq ▸ hcomap_normal
