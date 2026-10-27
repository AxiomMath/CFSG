module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuotientCenterAutomorphism
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The fixed factor centralizes the component Sylow

The quotient action of the fixed factor preserves the generalized-dihedral
normalizer of the distinguished involution.  Its restriction to the
component Sylow is an odd-order automorphism of a dihedral `2`-group, hence
trivial; the odd centre then lifts this quotient centralization to the
component itself.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem eq_one_of_isPGroup_of_odd_order
    {A : Type u} [Group A] [Finite A]
    (hA : IsPGroup 2 A) {a : A} (ha : Odd (orderOf a)) : a = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) a
  have hord : orderOf a = 1 := by
    by_cases hk0 : k = 0
    · simpa [hk0] using hk
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have h2dvd : 2 ∣ orderOf a := by
        rw [hk]
        refine ⟨2 ^ (k - 1), ?_⟩
        calc
          2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
          _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (k - 1) := by rw [mul_comm]
      exact False.elim (ha.not_two_dvd_nat h2dvd)
  exact orderOf_eq_one_iff.mp hord

private theorem eq_one_of_odd_dvd_two_pow {n k : ℕ}
    (hn : Odd n) (hdiv : n ∣ 2 ^ k) : n = 1 := by
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdiv with ⟨j, hj, hnj⟩
  by_cases hj0 : j = 0
  · simpa [hj0] using hnj
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have htwo : 2 ∣ n := by
      rw [hnj]
      exact ⟨2 ^ (j - 1), by
        calc
          2 ^ j = 2 ^ (j - 1 + 1) := by congr 1; omega
          _ = 2 ^ (j - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (j - 1) := by rw [mul_comm]⟩
    exact False.elim (hn.not_two_dvd_nat htwo)

private theorem mulAut_eq_one_of_isKleinFour_fixed_two
    {A : Type u} [Group A] [Finite A]
    (hA : IsKleinFour A) (φ : MulAut A)
    {a b : A} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hφa : φ a = a) (hφb : φ b = b) : φ = 1 := by
  classical
  let : IsKleinFour A := hA
  let : Fintype A := Fintype.ofFinite A
  apply MulEquiv.ext
  intro x
  have huniv : ({a * b, a, b, (1 : A)} : Finset A) = Finset.univ :=
    IsKleinFour.eq_finset_univ ha hb hab
  have hxmem : x ∈ ({a * b, a, b, (1 : A)} : Finset A) := by
    rw [huniv]
    exact Finset.mem_univ x
  have hxcases : x = a * b ∨ x = a ∨ x = b ∨ x = 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hxmem
  rcases hxcases with h | h | h | h
  · rw [h, map_mul, hφa, hφb]
    simp
  · rw [h]
    simpa using hφa
  · rw [h]
    simpa using hφb
  · rw [h]
    simp

private theorem quotient_involution_of_involution_local
    {E : Type u} [Group E] [Finite E]
    (Z : Subgroup E) [Z.Normal] (hZodd : Odd (Nat.card Z))
    {x : E} (hx : IsInvolution x) :
    IsInvolution (QuotientGroup.mk' Z x) := by
  constructor
  · intro hqx
    have hxZ : x ∈ Z :=
      (QuotientGroup.eq_one_iff (N := Z) x).mp hqx
    let xZ : Z := ⟨x, hxZ⟩
    have hxZI : IsInvolution xZ := by
      constructor
      · intro hone
        exact hx.1 (congrArg Subtype.val hone)
      · exact Subtype.ext hx.2
    have hxZorder : orderOf xZ = 2 :=
      orderOf_eq_prime hxZI.2 hxZI.1
    have htwo : 2 ∣ Nat.card Z := by
      rw [← hxZorder]
      exact orderOf_dvd_natCard xZ
    exact hZodd.not_two_dvd_nat htwo
  · simpa using congrArg (QuotientGroup.mk' Z) hx.2

private theorem sylow_two_unique_in_dihedral_join
    {Q : Type u} [Group Q] [Finite Q]
    (T : Subgroup Q) (r : Q) (hTcyc : IsCyclic T)
    (hrI : IsInvolution r) (hrnotT : r ∉ T)
    (hrinv : ∀ x : Q, x ∈ T → r * x * r⁻¹ = x⁻¹)
    (P P' : Sylow 2 Q)
    (hPle : (P : Subgroup Q) ≤ T ⊔ Subgroup.zpowers r)
    (hP'le : (P' : Subgroup Q) ≤ T ⊔ Subgroup.zpowers r)
    (hrP : r ∈ (P : Subgroup Q))
    (hrP' : r ∈ (P' : Subgroup Q)) :
    P = P' := by
  classical
  let : IsCyclic T := hTcyc
  let : CommGroup T := IsCyclic.commGroup
  let RT : Sylow 2 T := Classical.choice Sylow.nonempty
  let R : Subgroup Q := (RT : Subgroup T).map T.subtype
  let V : Subgroup Q := R ⊔ Subgroup.zpowers r
  have hRp : IsPGroup 2 R := RT.isPGroup'.map T.subtype
  have hr2 : r ^ 2 = 1 := hrI.2
  have hr2' : r * r = 1 := by simpa [pow_two] using hr2
  have hr_inv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2'
  have hrorder : orderOf r = 2 := orderOf_eq_prime hr2 hrI.1
  have hZrp : IsPGroup 2 (Subgroup.zpowers r) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hrorder, pow_one]
  have hinvR : ∀ x : Q, x ∈ R → r * x * r⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hrinv (y : Q) y.2
  have hrnormR : r ∈ Subgroup.normalizer (R : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinvR x hx]
      exact R.inv_mem hx
    · intro hx
      have hconj : r * (r * x * r⁻¹) * r⁻¹ ∈ R := by
        rw [hinvR (r * x * r⁻¹) hx]
        exact R.inv_mem hx
      have hEq : r * (r * x * r⁻¹) * r⁻¹ = x := by
        rw [hr_inv]
        calc
          r * (r * x * r) * r = (r * r) * x * (r * r) := by group
          _ = x := by rw [hr2']; simp
      exact hEq ▸ hconj
  have hZrnorm : Subgroup.zpowers r ≤
      Subgroup.normalizer (R : Set Q) := Subgroup.zpowers_le.mpr hrnormR
  have hVp : IsPGroup 2 V :=
    IsPGroup.to_sup_of_normal_left' hRp hZrp hZrnorm
  have hu_mem_R (P0 : Sylow 2 Q) {x u : Q}
      (hxP : x ∈ (P0 : Subgroup Q))
      (huT : u ∈ T) (huP : u ∈ (P0 : Subgroup Q)) : u ∈ R := by
    let uT : T := ⟨u, huT⟩
    obtain ⟨k, hk⟩ :=
      (IsPGroup.iff_orderOf.mp P0.isPGroup') (⟨u, huP⟩ : P0)
    have huord : orderOf u = 2 ^ k := by
      calc
        orderOf u = orderOf (⟨u, huP⟩ : P0) := by
          calc
            orderOf u = orderOf ((⟨u, huP⟩ : P0) : Q) := rfl
            _ = orderOf (⟨u, huP⟩ : P0) := Subgroup.orderOf_coe _
        _ = 2 ^ k := hk
    have huTord : orderOf uT = 2 ^ k := by
      calc
        orderOf uT = orderOf u := by
          calc
            orderOf uT = orderOf ((uT : T) : Q) :=
              (Subgroup.orderOf_coe uT).symm
            _ = orderOf u := by rfl
        _ = 2 ^ k := huord
    have hUup : IsPGroup 2 (Subgroup.zpowers uT) := by
      apply IsPGroup.of_card (n := k)
      rw [Nat.card_zpowers, huTord]
    have huRT : Subgroup.zpowers uT ≤ (RT : Subgroup T) := by
      exact IsPGroup.le_sylow_of_normal hUup RT
    exact Subgroup.mem_map.mpr
      ⟨uT, huRT (Subgroup.mem_zpowers uT), rfl⟩
  have hP_le_V : (P : Subgroup Q) ≤ V := by
    intro x hx
    rcases (mem_sup_zpowers_of_involution_inverts hrnotT hr2' hrinv).mp
      (hPle hx) with ⟨u, huT, hxu | hxu⟩
    · rw [hxu]
      exact (le_sup_left : R ≤ V)
        (hu_mem_R P hx huT (by simpa [hxu] using hx))
    · have huP : u ∈ (P : Subgroup Q) := by
        have hmul : x * r ∈ (P : Subgroup Q) := P.mul_mem hx hrP
        have hEq : u = x * r := by
          calc
            u = u * (r * r) := by rw [hr2']; simp
            _ = (u * r) * r := by group
            _ = x * r := by rw [← hxu]
        rw [hEq]
        exact hmul
      have huR : u ∈ R := hu_mem_R P hx huT huP
      rw [hxu]
      exact Subgroup.mul_mem_sup (S := R)
        (T := Subgroup.zpowers r) huR (Subgroup.mem_zpowers r)
  have hP'_le_V : (P' : Subgroup Q) ≤ V := by
    intro x hx
    rcases (mem_sup_zpowers_of_involution_inverts hrnotT hr2' hrinv).mp
      (hP'le hx) with ⟨u, huT, hxu | hxu⟩
    · rw [hxu]
      exact (le_sup_left : R ≤ V)
        (hu_mem_R P' hx huT
          (by simpa [hxu] using hx))
    · have huP : u ∈ (P' : Subgroup Q) := by
        have hmul : x * r ∈ (P' : Subgroup Q) := P'.mul_mem hx hrP'
        have hEq : u = x * r := by
          calc
            u = u * (r * r) := by rw [hr2']; simp
            _ = (u * r) * r := by group
            _ = x * r := by rw [← hxu]
        rw [hEq]
        exact hmul
      have huR : u ∈ R := hu_mem_R P' hx huT huP
      rw [hxu]
      exact Subgroup.mul_mem_sup (S := R)
        (T := Subgroup.zpowers r) huR (Subgroup.mem_zpowers r)
  have hVP : V = (P : Subgroup Q) := P.is_maximal' hVp hP_le_V
  have hVP' : V = (P' : Subgroup Q) := P'.is_maximal' hVp hP'_le_V
  apply Sylow.ext
  exact hVP.symm.trans hVP'

/-! ## The residual-action endpoint -/

/-- The fixed factor in the aligned PSL₂ decomposition centralizes the
component Sylow.  The quotient hypotheses are deliberately explicit: they
are the reflected torus, normalizer, and Sylow-containment data produced by
`secondCase_psl2_alignedSylow_decomposition`.
-/
public theorem secondCase_psl2_fixed_factor_centralizes_componentSylow
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      (c.S : Subgroup G) ⊓ d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (s : d.E)
    (hsSE : s ∈ (SE : Subgroup d.E))
    (hsI : IsInvolution s)
    (hTcyc : IsCyclic T)
    (htT : QuotientGroup.mk' (Subgroup.center d.E)
      ⟨c.t, d.t_mem_E⟩ ∈ T)
    (hqsnotT : QuotientGroup.mk' (Subgroup.center d.E) s ∉ T)
    (hPdecomp :
      (SE.mapSurjective
          (QuotientGroup.mk'_surjective (Subgroup.center d.E)) :
        Subgroup (d.E ⧸ Subgroup.center d.E)) ≤
        T ⊔ Subgroup.zpowers
          (QuotientGroup.mk' (Subgroup.center d.E) s))
    (hnormalizer :
      Subgroup.normalizer (Subgroup.zpowers
        (QuotientGroup.mk' (Subgroup.center d.E)
          ⟨c.t, d.t_mem_E⟩) :
        Set (d.E ⧸ Subgroup.center d.E)) =
        T ⊔ Subgroup.zpowers
          (QuotientGroup.mk' (Subgroup.center d.E) s))
    (hTinv : ∀ x : d.E ⧸ Subgroup.center d.E, x ∈ T →
      QuotientGroup.mk' (Subgroup.center d.E) s * x *
        (QuotientGroup.mk' (Subgroup.center d.E) s)⁻¹ = x⁻¹)
    (B : Subgroup G)
    (hB : B = centralizerIn (c.U ⊓ w.M) (s : G)) :
    B ≤ Subgroup.centralizer
      (((SE : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G) := by
  classical
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let tE : d.E := ⟨c.t, d.t_mem_E⟩
  let qt : Q := q tE
  let qs : Q := q s
  let P : Sylow 2 Q :=
    SE.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center d.E))
  have hTcyc' : IsCyclic T := hTcyc
  have htI : IsInvolution tE := by
    constructor
    · intro h
      exact c.t_involution.1 (congrArg Subtype.val h)
    · apply Subtype.ext
      simpa [tE, pow_two] using c.t_involution.2
  have hqtI : IsInvolution qt := by
    change IsInvolution (QuotientGroup.mk' (Subgroup.center d.E) tE)
    exact quotient_involution_of_involution_local
      (Subgroup.center d.E) d.center_odd htI
  have htS : c.t ∈ (c.S : Subgroup G) :=
    c.S0_le_S c.t_mem_S0
  have htSE : tE ∈ (SE : Subgroup d.E) := by
    have htmap : c.t ∈ (SE : Subgroup d.E).map d.E.subtype := by
      rw [hSEamb]
      exact ⟨htS, d.t_mem_E⟩
    rcases Subgroup.mem_map.mp htmap with ⟨x, hx, hxeq⟩
    have hxt : x = tE := by
      apply Subtype.ext
      exact hxeq
    simpa [hxt] using hx
  have hqtP : qt ∈ (P : Subgroup Q) := by
    rw [show qt = q tE by rfl, Sylow.coe_mapSurjective]
    exact Subgroup.mem_map.mpr ⟨tE, htSE, rfl⟩
  have hqsI : IsInvolution qs := by
    change IsInvolution (q s)
    exact quotient_involution_of_involution_local
      (Subgroup.center d.E) d.center_odd hsI
  have hqsP : qs ∈ (P : Subgroup Q) := by
    rw [show qs = q s by rfl, Sylow.coe_mapSurjective]
    exact Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hPdecomp' : (P : Subgroup Q) ≤ T ⊔ Subgroup.zpowers qs := by
    change (SE.mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center d.E)) :
        Subgroup Q) ≤ T ⊔ Subgroup.zpowers qs
    change (SE.mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center d.E)) :
        Subgroup Q) ≤ T ⊔ Subgroup.zpowers qs at hPdecomp
    exact hPdecomp
  have hnormalizer' :
      Subgroup.normalizer (Subgroup.zpowers qt : Set Q) =
        T ⊔ Subgroup.zpowers qs := by
    change Subgroup.normalizer (Subgroup.zpowers (q tE) : Set Q) =
      T ⊔ Subgroup.zpowers (q s) at hnormalizer
    exact hnormalizer
  have hTinv' : ∀ x : Q, x ∈ T → qs * x * qs⁻¹ = x⁻¹ := by
    change ∀ x : Q, x ∈ T → q s * x * (q s)⁻¹ = x⁻¹ at hTinv
    exact hTinv
  have hEleM : d.E ≤ w.M := d.E_component.1
  let M0 : Type u := ↥w.M
  let E0 : Subgroup M0 := d.E.subgroupOf w.M
  have hE0normal : E0.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEleM]
    intro x y hx hy
    exact d.E_normal.2 y hy x hx
  let eE0 : E0 ≃* d.E := Subgroup.subgroupOfEquivOfLe hEleM
  let conj0 : M0 →* MulAut E0 := MulAut.conjNormal (H := E0)
  let conjE : M0 →* MulAut d.E :=
    (MulAut.congr eE0).toMonoidHom.comp conj0
  let qAut : MulAut d.E →* MulAut Q :=
    quotientCenterAutomorphism d.E
  let qAction : M0 →* MulAut Q := qAut.comp conjE
  have hqaction (m : M0) (x : d.E) :
      qAction m (q x) =
        q ⟨(m : G) * (x : G) * (m : G)⁻¹,
          d.E_normal.2 (m : G) m.2 (x : G) x.2⟩ := by
    change qAut (conjE m) (q x) = _
    rw [quotientCenterAutomorphism_apply_mk]
    apply congrArg q
    change eE0 ((conj0 m) (eE0.symm x)) = _
    apply Subtype.ext
    have hc := MulAut.conjNormal_apply
      (G := M0) (H := E0) m (eE0.symm x)
    exact congrArg (fun z : M0 => (z : G)) hc
  have hUleH : c.U ≤ c.H := by
    unfold CentralizerSetup.U oddCoreOf
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hP_preserved (b : G) (hb : b ∈ B) :
      (P : Subgroup Q).map
        (qAction ⟨b, (by
          have hbC : b ∈ centralizerIn (c.U ⊓ w.M) (s : G) := by
            rw [← hB]
            exact hb
          exact hbC.1.2)⟩).toMonoidHom = (P : Subgroup Q) := by
    have hbC : b ∈ centralizerIn (c.U ⊓ w.M) (s : G) := by
      rw [← hB]
      exact hb
    have hbU : b ∈ c.U := hbC.1.1
    have hbM : b ∈ w.M := hbC.1.2
    let m : M0 := ⟨b, hbM⟩
    have hbtcomm : b * c.t = c.t * b := by
      have hbH : b ∈ c.H := hUleH hbU
      rw [c.H_eq_centralizer] at hbH
      exact Subgroup.mem_centralizer_singleton_iff.mp hbH
    have hbt : b * c.t * b⁻¹ = c.t := by
      calc
        b * c.t * b⁻¹ = (c.t * b) * b⁻¹ := by rw [hbtcomm]
        _ = c.t := by simp
    have hbscomm : b * (s : G) = (s : G) * b := by
      exact (Subgroup.mem_centralizer_iff.mp hbC.2) (s : G) (by simp) |>.symm
    have hbs : b * (s : G) * b⁻¹ = (s : G) := by
      calc
        b * (s : G) * b⁻¹ = ((s : G) * b) * b⁻¹ := by rw [hbscomm]
        _ = (s : G) := by simp
    have hαqt : qAction m qt = qt := by
      change qAction m (q tE) = q tE
      rw [hqaction]
      have heq :
          (⟨(m : G) * (tE : G) * (m : G)⁻¹,
            d.E_normal.2 (m : G) m.2 (tE : G) tE.2⟩ : d.E) = tE := by
        apply Subtype.ext
        exact hbt
      rw [heq]
    have hαqs : qAction m qs = qs := by
      change qAction m (q s) = q s
      rw [hqaction]
      have heq :
          (⟨(m : G) * (s : G) * (m : G)⁻¹,
            d.E_normal.2 (m : G) m.2 (s : G) s.2⟩ : d.E) = s := by
        apply Subtype.ext
        exact hbs
      rw [heq]
    let αQ : MulAut Q := qAction m
    have hαQqt : αQ qt = qt := hαqt
    have hαQqs : αQ qs = qs := hαqs
    have hαQsurj : Function.Surjective αQ.toMonoidHom := by
      intro z
      rcases αQ.surjective z with ⟨w, hw⟩
      exact ⟨w, hw⟩
    have hP'leD :
        ((P.mapSurjective (f := αQ.toMonoidHom) hαQsurj : Sylow 2 Q) :
          Subgroup Q) ≤
          T ⊔ Subgroup.zpowers qs := by
      intro y hy
      change y ∈ (P : Subgroup Q).map αQ.toMonoidHom at hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hxN : x ∈ Subgroup.normalizer
          (Subgroup.zpowers qt : Set Q) := by
        rw [hnormalizer']
        exact hPdecomp' hx
      have hmap : αQ x ∈
          (Subgroup.normalizer (Subgroup.zpowers qt : Set Q)).map
            αQ.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
      rw [Subgroup.map_equiv_normalizer_eq] at hmap
      rw [MonoidHom.map_zpowers] at hmap
      have hαQqt' : αQ.toMonoidHom qt = qt := hαQqt
      rw [hαQqt'] at hmap
      rw [hnormalizer'] at hmap
      exact hmap
    have hqsP' : qs ∈
        ((P.mapSurjective (f := αQ.toMonoidHom) hαQsurj : Sylow 2 Q) :
          Subgroup Q) := by
      change qs ∈ (P : Subgroup Q).map αQ.toMonoidHom
      exact Subgroup.mem_map.mpr ⟨qs, hqsP, hαQqs⟩
    have hPPeq : P =
        (P.mapSurjective (f := αQ.toMonoidHom) hαQsurj : Sylow 2 Q) :=
      sylow_two_unique_in_dihedral_join T qs hTcyc' hqsI hqsnotT hTinv'
        P (P.mapSurjective (f := αQ.toMonoidHom) hαQsurj)
        hPdecomp' hP'leD hqsP hqsP'
    have hPmap : (P : Subgroup Q).map αQ.toMonoidHom = (P : Subgroup Q) := by
      have hco := congrArg (fun R : Sylow 2 Q => (R : Subgroup Q)) hPPeq
      simpa [P] using hco.symm
    exact hPmap
  intro b hb
  have hbC : b ∈ centralizerIn (c.U ⊓ w.M) (s : G) := by
    rw [← hB]
    exact hb
  have hbU : b ∈ c.U := hbC.1.1
  have hbM : b ∈ w.M := hbC.1.2
  let m : M0 := ⟨b, hbM⟩
  let αQ : MulAut Q := qAction m
  have hPmap : (P : Subgroup Q).map αQ.toMonoidHom = (P : Subgroup Q) := by
    exact hP_preserved b hb
  let αP0 : P ≃* (P : Subgroup Q).map αQ.toMonoidHom :=
    αQ.subgroupMap (P : Subgroup Q)
  let αP : MulAut P := αP0.trans (MulEquiv.subgroupCongr hPmap)
  let Pmodel : Sylow 2 (PSL2 K) :=
    P.mapSurjective (f := e.some.toMonoidHom) e.some.surjective
  obtain ⟨n, hn, ⟨eD⟩⟩ :=
    psl2_odd_hasDihedralSylowTwo_model K hK Pmodel
  have hPmodel : (Pmodel : Subgroup (PSL2 K)) =
      (P : Subgroup Q).map e.some.toMonoidHom := by
    simpa [Pmodel] using
      (Sylow.coe_mapSurjective (f := e.some.toMonoidHom)
        e.some.surjective P)
  let eP0 : P ≃* (P : Subgroup Q).map e.some.toMonoidHom :=
    e.some.subgroupMap (P : Subgroup Q)
  let eP : P ≃* (Pmodel : Subgroup (PSL2 K)) :=
    eP0.trans (MulEquiv.subgroupCongr hPmodel.symm)
  let ePD : P ≃* DihedralGroup (2 ^ n) := eP.trans eD
  have hm_pow : m ^ orderOf b = 1 := by
    apply Subtype.ext
    change b ^ orderOf b = 1
    exact pow_orderOf_eq_one b
  have hαQpow : αQ ^ orderOf b = 1 := by
    calc
      αQ ^ orderOf b = qAction (m ^ orderOf b) := by
        rw [map_pow]
      _ = qAction 1 := by rw [hm_pow]
      _ = 1 := map_one qAction
  have hbtcomm : b * c.t = c.t * b := by
    have hbH : b ∈ c.H := hUleH hbU
    rw [c.H_eq_centralizer] at hbH
    exact Subgroup.mem_centralizer_singleton_iff.mp hbH
  have hbt : b * c.t * b⁻¹ = c.t := by
    calc
      b * c.t * b⁻¹ = (c.t * b) * b⁻¹ := by rw [hbtcomm]
      _ = c.t := by simp
  have hbscomm : b * (s : G) = (s : G) * b := by
    exact (Subgroup.mem_centralizer_iff.mp hbC.2) (s : G) (by simp) |>.symm
  have hbs : b * (s : G) * b⁻¹ = (s : G) := by
    calc
      b * (s : G) * b⁻¹ = ((s : G) * b) * b⁻¹ := by rw [hbscomm]
      _ = (s : G) := by simp
  have hαQqt : αQ qt = qt := by
    change qAction m (q tE) = q tE
    rw [hqaction]
    have heq :
        (⟨(m : G) * (tE : G) * (m : G)⁻¹,
          d.E_normal.2 (m : G) m.2 (tE : G) tE.2⟩ : d.E) = tE := by
      apply Subtype.ext
      exact hbt
    rw [heq]
  have hαQqs : αQ qs = qs := by
    change qAction m (q s) = q s
    rw [hqaction]
    have heq :
        (⟨(m : G) * (s : G) * (m : G)⁻¹,
          d.E_normal.2 (m : G) m.2 (s : G) s.2⟩ : d.E) = s := by
      apply Subtype.ext
      exact hbs
    rw [heq]
  have hαP_apply' (x : P) : (αP x : Q) = αQ (x : Q) := by
    change ((αP0 x : (P : Subgroup Q).map αQ.toMonoidHom) : Q) =
      αQ (x : Q)
    rfl
  have hpow_apply : ∀ k : ℕ, ∀ x : P,
      ((αP ^ k) x : Q) = (αQ ^ k) (x : Q) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply]
      rw [ih, hαP_apply']
      rw [← MulAut.mul_apply, ← pow_succ]
  have hαPpow : αP ^ orderOf b = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    calc
      ((αP ^ orderOf b) x : Q) =
          (αQ ^ orderOf b) (x : Q) := hpow_apply _ x
      _ = ((1 : MulAut Q) (x : Q)) := by rw [hαQpow]
      _ = (x : Q) := by simp
  let qtP : P := ⟨qt, hqtP⟩
  let qsP : P := ⟨qs, hqsP⟩
  have hqtPne : qtP ≠ (1 : P) := by
    intro h
    apply hqtI.1
    exact congrArg Subtype.val h
  have hqsPne : qsP ≠ (1 : P) := by
    intro h
    apply hqsI.1
    exact congrArg Subtype.val h
  have hqtqsPne : qtP ≠ qsP := by
    intro h
    apply hqsnotT
    have h : qt = qs := congrArg Subtype.val h
    change qs ∈ T
    rw [← h]
    exact htT
  have hαPqt : αP qtP = qtP := by
    apply Subtype.ext
    rw [hαP_apply']
    exact hαQqt
  have hαPqs : αP qsP = qsP := by
    apply Subtype.ext
    rw [hαP_apply']
    exact hαQqs
  have hαPone : αP = 1 := by
    have hbodd : Odd (orderOf b) := by
      have hdvd : orderOf b ∣ Nat.card (↥c.U) :=
        Subgroup.orderOf_dvd_natCard c.U hbU
      exact Odd.of_dvd_nat hUodd hdvd
    have hαPodd : Odd (orderOf αP) := by
      apply Odd.of_dvd_nat hbodd
      exact (orderOf_dvd_iff_pow_eq_one).2 hαPpow
    by_cases hn2 : 2 ≤ n
    · have hαPgroup : IsPGroup 2 (MulAut P) :=
        (dihedral_mulAut_is_twoGroup hn2).of_equiv
          (MulAut.congr ePD).symm
      exact eq_one_of_isPGroup_of_odd_order hαPgroup hαPodd
    · have hn1 : n = 1 := by omega
      subst n
      have hKlein : IsKleinFour P := {
        card_four := by
          have hc := Nat.card_congr ePD.toEquiv
          exact hc.trans (inferInstance : IsKleinFour (DihedralGroup 2)).card_four
        exponent_two := by
          rw [Monoid.exponent_eq_of_mulEquiv ePD]
          exact (inferInstance : IsKleinFour (DihedralGroup 2)).exponent_two }
      exact mulAut_eq_one_of_isKleinFour_fixed_two hKlein αP
        hqtPne hqsPne hqtqsPne hαPqt hαPqs
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rcases Subgroup.mem_map.mp ha with ⟨aE, haSE, hxa⟩
  have hxa' : (aE : G) = a := hxa
  subst a
  have haP : q aE ∈ (P : Subgroup Q) := by
    rw [show P = SE.mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center d.E)) by rfl,
      Sylow.coe_mapSurjective]
    exact Subgroup.mem_map.mpr ⟨aE, haSE, rfl⟩
  have hαQfix : αQ (q aE) = q aE := by
    let aP : P := ⟨q aE, haP⟩
    have hfix := hαP_apply' aP
    rw [hαPone] at hfix
    exact hfix.symm
  let yE : d.E := ⟨b * (aE : G) * b⁻¹,
    d.E_normal.2 b hbM (aE : G) aE.2⟩
  have hqy : q yE = q aE := by
    calc
      q yE = αQ (q aE) := by
        simpa [yE, αQ] using (hqaction m aE).symm
      _ = q aE := hαQfix
  let zE : d.E := yE * aE⁻¹
  have hqz : q zE = 1 := by
    dsimp [zE]
    rw [map_mul, hqy, map_inv]
    simp
  have hzcenter : zE ∈ Subgroup.center (↥d.E) :=
    (QuotientGroup.eq_one_iff zE).mp hqz
  have hyaord : orderOf yE = orderOf aE := by
    calc
      orderOf yE = orderOf (yE : G) := (Subgroup.orderOf_coe yE).symm
      _ = orderOf ((MulAut.conj b) (aE : G)) := by
        rw [MulAut.conj_apply]
      _ = orderOf (aE : G) := MulEquiv.orderOf_eq (MulAut.conj b) (aE : G)
      _ = orderOf aE := Subgroup.orderOf_coe aE
  have hyaPow : yE ^ orderOf aE = 1 := by
    rw [← hyaord]
    exact pow_orderOf_eq_one yE
  have hzcomm : zE * aE = aE * zE :=
    (Subgroup.mem_center_iff.mp hzcenter aE).symm
  have hzcomm' : Commute zE aE := hzcomm
  have hyfactor : yE = zE * aE := by
    dsimp [zE]
    group
  have hzPow : zE ^ orderOf aE = 1 := by
    have hpow := hyaPow
    rw [hyfactor, hzcomm'.mul_pow] at hpow
    rw [pow_orderOf_eq_one aE] at hpow
    simpa using hpow
  have hzdiv : orderOf zE ∣ orderOf aE :=
    orderOf_dvd_of_pow_eq_one hzPow
  have hzodd : Odd (orderOf zE) := by
    have hzcard : orderOf zE ∣ Nat.card (↥(Subgroup.center (↥d.E))) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center (↥d.E)) hzcenter
    exact Odd.of_dvd_nat d.center_odd hzcard
  obtain ⟨k, hak⟩ :=
    (IsPGroup.iff_orderOf.mp SE.isPGroup') (⟨aE, haSE⟩ : SE)
  have haord : orderOf aE = 2 ^ k := by
    calc
      orderOf aE = orderOf ((⟨aE, haSE⟩ : SE) : d.E) := rfl
      _ = orderOf (⟨aE, haSE⟩ : SE) := Subgroup.orderOf_coe _
      _ = 2 ^ k := hak
  have hzordone : orderOf zE = 1 :=
    eq_one_of_odd_dvd_two_pow hzodd (by simpa [haord] using hzdiv)
  have hzone : zE = 1 := orderOf_eq_one_iff.mp hzordone
  have hyeq : yE = aE := by
    calc
      yE = zE * aE := hyfactor
      _ = 1 * aE := by rw [hzone]
      _ = aE := one_mul aE
  have hconj : b * (aE : G) * b⁻¹ = (aE : G) := by
    have h := congrArg (fun z : d.E => (z : G)) hyeq
    simpa [yE] using h
  have hcomm : b * (aE : G) = (aE : G) * b := by
    calc
      b * (aE : G) = (b * (aE : G) * b⁻¹) * b := by group
      _ = (aE : G) * b := by rw [hconj]
  exact hcomm.symm

end CFSG.GorensteinWalter
