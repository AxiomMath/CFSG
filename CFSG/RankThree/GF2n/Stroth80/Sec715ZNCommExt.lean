module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ComplementRange
public import CFSG.RankThree.GF2n.Stroth80.Sec715Split

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap CFSG.RankThree.GF2n.Stroth80.Sec715Torus
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem sec715Cm_extData {K : Type} [Field K] [Finite K] [CharP K 2]
    {R Zn Z0 Q : Subgroup G} {M₀ Mm : Type} [AddCommGroup M₀] [Finite M₀] [AddCommGroup Mm]
    [Finite Mm] [DistribMulAction ↥R M₀] [DistribMulAction ↥R Mm]
    [DistribMulAction (Gom (quadPlus 4 K)) M₀] [DistribMulAction (Gom (quadPlus 4 K)) Mm]
    (ρh : ↥R →* Gom (quadPlus 4 K)) (hρh : Function.Surjective ρh)
    (hsm₀ : ∀ (y : ↥R) (a : M₀), ρh y • a = y • a)
    (hsm₁ : ∀ (y : ↥R) (a : Mm), ρh y • a = y • a)
    {κ₀ : ↥Zn →* Multiplicative M₀} {κ : ↥Zn →* Multiplicative Mm}
    (hκ₀ : IsSecMod R Zn Z0 M₀ κ₀) (hκ : IsSecMod R Zn Q Mm κ)
    (hsec₀ : SecHyp R Zn Z0) (hsecQ : SecHyp R Zn Q) (hQZ0 : Q ≤ Z0) (hZ0Zn : Z0 ≤ Zn)
    (hZ0c : ∀ z ∈ Z0, ∀ y ∈ R, ⁅z, y⁆ ∈ Q) (hne : Zn ≠ Z0)
    (hirrG : ∀ U : Subgroup G, Z0 ≤ U → U ≤ Zn → (∀ ρ ∈ R, conjSubgroup ρ U = U) →
      U = Z0 ∨ U = Zn)
    (P : HypPair (quadPlus 4 K))
    (hdecP : IsCompl (fixedSub M₀ (Lom (quadPlus 4 K) P.e : Set (Gom (quadPlus 4 K))))
      (fixedSub M₀ (Lom (quadPlus 4 K) P.f : Set (Gom (quadPlus 4 K))))) :
    ∃ π : Mm →+ M₀, (∀ z : ↥Zn, π (Multiplicative.toAdd (κ z)) = Multiplicative.toAdd (κ₀ z)) ∧
      ExtData K 4 M₀ Mm (secSub κ Z0) π P := by
  classical
  have hZnn := hsecQ.normP
  have hπ0 : ∀ (z : ↥Zn) (m : Mm), κ z = Multiplicative.ofAdd m →
      Multiplicative.toAdd (κ₀ (Function.surjInv hκ.surj (Multiplicative.ofAdd m))) =
        Multiplicative.toAdd (κ₀ z) := by
    intro z m hz
    have h1 : κ (Function.surjInv hκ.surj (Multiplicative.ofAdd m)) = Multiplicative.ofAdd m :=
      Function.surjInv_eq hκ.surj _
    have h2 : κ (Function.surjInv hκ.surj (Multiplicative.ofAdd m)) = κ z := by rw [h1, hz]
    have h3 := (hκ.eq_iff _ z).mp h2
    have h4 : ((Function.surjInv hκ.surj (Multiplicative.ofAdd m) : ↥Zn) : G) * (z : G)⁻¹ ∈ Z0 :=
      hQZ0 h3
    rw [(hκ₀.eq_iff _ z).mpr h4]
  let π : Mm →+ M₀ := AddMonoidHom.mk'
    (fun m => Multiplicative.toAdd (κ₀ (Function.surjInv hκ.surj (Multiplicative.ofAdd m))))
    (by
      intro m m'
      obtain ⟨z, hz⟩ := hκ.surj (Multiplicative.ofAdd m)
      obtain ⟨z', hz'⟩ := hκ.surj (Multiplicative.ofAdd m')
      have hzz : κ (z * z') = Multiplicative.ofAdd (m + m') := by
        rw [map_mul, hz, hz', ofAdd_add]
      show Multiplicative.toAdd (κ₀ (Function.surjInv hκ.surj (Multiplicative.ofAdd (m + m')))) =
        Multiplicative.toAdd (κ₀ (Function.surjInv hκ.surj (Multiplicative.ofAdd m))) +
          Multiplicative.toAdd (κ₀ (Function.surjInv hκ.surj (Multiplicative.ofAdd m')))
      rw [hπ0 _ _ hzz, hπ0 _ _ hz, hπ0 _ _ hz', map_mul, toAdd_mul])
  have hπapp : ∀ z : ↥Zn, π (Multiplicative.toAdd (κ z)) = Multiplicative.toAdd (κ₀ z) :=
    fun z => hπ0 z _ (by rw [ofAdd_toAdd])
  refine ⟨π, hπapp, hκ₀.two, hκ.two, ?_, ?_, ?_, ?_, ?_, ?_, hdecP⟩
  ·
    intro g v hv
    obtain ⟨y, rfl⟩ := hρh g
    rw [hsm₁]
    obtain ⟨z, hzZ0, hzv⟩ := mem_secSub.mp hv
    have hv' : v = Multiplicative.toAdd (κ z) := by rw [hzv]; rfl
    rw [hv']
    apply sec715Spl_smul_eq hsecQ hκ
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hZ0c z hzZ0 y y.2)
  ·
    intro m
    obtain ⟨z, hz⟩ := hκ.surj (Multiplicative.ofAdd m)
    have hm : m = Multiplicative.toAdd (κ z) := by rw [hz]; rfl
    rw [hm, hπapp, toAdd_mem_secSub_iff hκ hQZ0 z, toAdd_eq_zero]
    exact hκ₀.ker z
  ·
    intro g m
    obtain ⟨y, rfl⟩ := hρh g
    rw [hsm₁, hsm₀]
    obtain ⟨z, hz⟩ := hκ.surj (Multiplicative.ofAdd m)
    have hm : m = Multiplicative.toAdd (κ z) := by rw [hz]; rfl
    have hyz : (y : G) * z * (y : G)⁻¹ ∈ Zn := hZnn y y.2 z z.2
    have h1 := hκ.act y z ⟨(y : G) * z * (y : G)⁻¹, hyz⟩ rfl
    have h2 := hκ₀.act y z ⟨(y : G) * z * (y : G)⁻¹, hyz⟩ rfl
    have e1 : y • Multiplicative.toAdd (κ z) =
        Multiplicative.toAdd (κ ⟨(y : G) * z * (y : G)⁻¹, hyz⟩) := by rw [h1, toAdd_ofAdd]
    have e2 : y • Multiplicative.toAdd (κ₀ z) =
        Multiplicative.toAdd (κ₀ ⟨(y : G) * z * (y : G)⁻¹, hyz⟩) := by rw [h2, toAdd_ofAdd]
    rw [hm, e1, hπapp, hπapp, e2]
  ·
    intro m₀
    obtain ⟨z, hz⟩ := hκ₀.surj (Multiplicative.ofAdd m₀)
    exact ⟨Multiplicative.toAdd (κ z), by rw [hπapp, hz]; rfl⟩
  ·
    intro W hW
    obtain ⟨U, hZU, hUZn, hUW⟩ := exists_secSub_eq hZ0Zn hκ₀ W
    have hUinv : ∀ ρ ∈ R, conjSubgroup ρ U = U := by
      intro ρ hρ
      rw [conjSubgroup_eq_self_iff_secSub hsec₀ hκ₀ ⟨ρ, hρ⟩ hZU hUZn, hUW]
      refine le_antisymm ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        have := hW (ρh ⟨ρ, hρ⟩) w hw
        rwa [hsm₀] at this
      · intro w hw
        refine ⟨(⟨ρ, hρ⟩ : ↥R)⁻¹ • w, ?_, ?_⟩
        · have := hW (ρh (⟨ρ, hρ⟩ : ↥R)⁻¹) w hw
          rwa [hsm₀] at this
        · show (⟨ρ, hρ⟩ : ↥R) • (⟨ρ, hρ⟩ : ↥R)⁻¹ • w = w
          rw [smul_inv_smul]
    rcases hirrG U hZU hUZn hUinv with h | h
    · left
      rw [← hUW, h, secSub_eq_bot hκ₀]
    · right
      rw [← hUW, h, secSub_eq_top hκ₀]
  ·
    have : ∃ z ∈ Zn, z ∉ Z0 := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hcon hZ0Zn)
    obtain ⟨z, hz, hzn⟩ := this
    refine ⟨⟨Multiplicative.toAdd (κ₀ ⟨z, hz⟩), 0, fun h => hzn ?_⟩⟩
    have h1 : κ₀ ⟨z, hz⟩ = 1 := toAdd_eq_zero.mp h
    exact (hκ₀.ker ⟨z, hz⟩).mp h1

theorem sec715Cm_final {K : Type} [Field K] [Finite K] [CharP K 2]
    {R Zn Z0 Q L : Subgroup G} {M₀ Mm : Type} [AddCommGroup M₀] [Finite M₀] [AddCommGroup Mm]
    [Finite Mm] [DistribMulAction ↥R M₀] [DistribMulAction ↥R Mm]
    [DistribMulAction (Gom (quadPlus 4 K)) M₀] [DistribMulAction (Gom (quadPlus 4 K)) Mm]
    (hK : 2 < Nat.card K) (ρh : ↥R →* Gom (quadPlus 4 K))
    (hsm₀ : ∀ (y : ↥R) (a : M₀), ρh y • a = y • a)
    (hsm₁ : ∀ (y : ↥R) (a : Mm), ρh y • a = y • a)
    {κ₀ : ↥Zn →* Multiplicative M₀} {κ : ↥Zn →* Multiplicative Mm}
    (hκ₀ : IsSecMod R Zn Z0 M₀ κ₀) (hκ : IsSecMod R Zn Q Mm κ)
    (hsec₀ : SecHyp R Zn Z0) (hsecQ : SecHyp R Zn Q) {π : Mm →+ M₀}
    {P : HypPair (quadPlus 4 K)} (H : ExtData K 4 M₀ Mm (secSub κ Z0) π P)
    (hCΓ : fixedSub M₀ (Lom (quadPlus 4 K) P.e : Set (Gom (quadPlus 4 K))) =
      secSub κ₀ (Zn ⊓ L))
    (hLR : L ≤ R) (hLmap : ∀ l : ↥R, (l : G) ∈ L → ρh l ∈ Lom (quadPlus 4 K) P.e)
    (hexA2 : ∃ y : ↥R, (y : G) ∈ L ∧ (ρh y).NonA2) :
    ∃ x ∈ L, (∀ a ∈ Zn ⊓ L, ∃ z ∈ Zn, ⁅x, z⁆ * a⁻¹ ∈ Z0) ∧
      ∀ l ∈ L, ∀ z ∈ Zn, ∃ z' ∈ Zn, ⁅l, z⁆ * ⁅x, z'⁆⁻¹ ∈ Q := by
  classical
  obtain ⟨y, hyL, hyn⟩ := hexA2
  have hy' : ρh y ∈ Lom (quadPlus 4 K) P.e := hLmap y hyL
  refine ⟨(y : G), hyL, ?_, ?_⟩
  ·
    intro a ha
    have haZn : a ∈ Zn := ha.1
    have hmem : Multiplicative.toAdd (κ₀ ⟨a, haZn⟩) ∈ fixedSub M₀
        (Lom (quadPlus 4 K) P.e : Set (Gom (quadPlus 4 K))) := by
      rw [hCΓ]
      exact mem_secSub.mpr ⟨⟨a, haZn⟩, ha, rfl⟩
    rw [← H.range_comm_nonA2 (by norm_num) hy' hyn] at hmem
    obtain ⟨m₀, hm₀⟩ := hmem
    obtain ⟨z, hz⟩ := hκ₀.surj (Multiplicative.ofAdd m₀)
    have hm : m₀ = Multiplicative.toAdd (κ₀ z) := by rw [hz]; rfl
    have hcz : ⁅(y : G), (z : G)⁆ ∈ Zn := by
      have h1 := hsecQ.normP y y.2 z z.2
      have e : ⁅(y : G), (z : G)⁆ = ((y : G) * z * (y : G)⁻¹) * (z : G)⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact Zn.mul_mem h1 (Zn.inv_mem z.2)
    have h2 := sec715Spl_comm_eq hsec₀ hκ₀ y z ⟨⁅(y : G), (z : G)⁆, hcz⟩ rfl
    have h3 : κ₀ ⟨⁅(y : G), (z : G)⁆, hcz⟩ = κ₀ ⟨a, haZn⟩ := by
      have h4 : comm M₀ (ρh y) m₀ = Multiplicative.toAdd (κ₀ ⟨a, haZn⟩) := hm₀
      rw [comm_apply, hsm₀, hm, h2] at h4
      exact Multiplicative.toAdd.injective h4
    refine ⟨z, z.2, ?_⟩
    have := (hκ₀.eq_iff ⟨⁅(y : G), (z : G)⁆, hcz⟩ ⟨a, haZn⟩).mp h3
    simpa using this
  ·
    intro l hl z hz
    have hlR : l ∈ R := hLR hl
    have hle := H.range_comm_le_of_nonA2 hK (by norm_num) hy' hyn (hLmap ⟨l, hlR⟩ hl)
    have hmem : comm Mm (ρh ⟨l, hlR⟩) (Multiplicative.toAdd (κ ⟨z, hz⟩)) ∈ (comm Mm (ρh y)).range :=
      hle ⟨_, rfl⟩
    obtain ⟨m', hm'⟩ := hmem
    obtain ⟨z', hz'⟩ := hκ.surj (Multiplicative.ofAdd m')
    have hm : m' = Multiplicative.toAdd (κ z') := by rw [hz']; rfl
    have hcz : ⁅l, z⁆ ∈ Zn := by
      have h1 := hsecQ.normP l hlR z hz
      have e : ⁅l, (z : G)⁆ = (l * z * l⁻¹) * (z : G)⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact Zn.mul_mem h1 (Zn.inv_mem hz)
    have hcz' : ⁅(y : G), (z' : G)⁆ ∈ Zn := by
      have h1 := hsecQ.normP y y.2 z' z'.2
      have e : ⁅(y : G), (z' : G)⁆ = ((y : G) * z' * (y : G)⁻¹) * (z' : G)⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact Zn.mul_mem h1 (Zn.inv_mem z'.2)
    have h2 := sec715Spl_comm_eq hsecQ hκ ⟨l, hlR⟩ ⟨z, hz⟩ ⟨⁅l, z⁆, hcz⟩ rfl
    have h2' := sec715Spl_comm_eq hsecQ hκ y z' ⟨⁅(y : G), (z' : G)⁆, hcz'⟩ rfl
    have h3 : κ ⟨⁅l, z⁆, hcz⟩ = κ ⟨⁅(y : G), (z' : G)⁆, hcz'⟩ := by
      have h4 : comm Mm (ρh y) m' = comm Mm (ρh ⟨l, hlR⟩) (Multiplicative.toAdd (κ ⟨z, hz⟩)) :=
        hm'
      rw [comm_apply, comm_apply, hsm₁, hsm₁, hm, h2'] at h4
      rw [h2] at h4
      exact Multiplicative.toAdd.injective h4.symm
    refine ⟨z', z'.2, ?_⟩
    have := (hκ.eq_iff ⟨⁅l, z⁆, hcz⟩ ⟨⁅(y : G), (z' : G)⁆, hcz'⟩).mp h3
    simpa using this

theorem sec715Cm_mem_Lom {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q X) {Y : Type*}
    [Group Y] (φ : Y →* GL ι K) (hφ : φ.range = X) {L : Subgroup Y} {u : ι → K}
    (hL : L.map φ = E.LomGL u) {y : Y} (hy : y ∈ L) : viaMatrix X E.equiv φ hφ y ∈ Lom Q u := by
  have h1 : φ y ∈ E.LomGL u := by
    rw [← hL]
    exact Subgroup.mem_map_of_mem φ hy
  obtain ⟨hA, hmem⟩ := mem_matrixOf_iff.1 h1
  exact hmem

theorem sec715Cm_assemble {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
    [CharP K 2] {R Zn Z0 Q L₁ L₂ : Subgroup G} {M₀ Mm : Type} [AddCommGroup M₀] [Finite M₀]
    [AddCommGroup Mm] [Finite Mm] [DistribMulAction ↥R M₀] [DistribMulAction ↥R Mm]
    [DistribMulAction (Gom (quadPlus 4 K)) M₀] [DistribMulAction (Gom (quadPlus 4 K)) Mm]
    (hK : 2 < Nat.card K) (E : ElemMatrixIso (quadPlus 4 K) (StatedOmega (StatedQuadPlus 4 K)))
    (φ : ↥R →* GL (Fin 4 ⊕ Fin 4) K) (hrange : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hsm₀ : ∀ (y : ↥R) (a : M₀), viaMatrix _ E.equiv φ hrange y •
      a = y • a)
    (hsm₁ : ∀ (y : ↥R) (a : Mm), viaMatrix _ E.equiv φ hrange y •
      a = y • a)
    {κ₀ : ↥Zn →* Multiplicative M₀} {κ : ↥Zn →* Multiplicative Mm}
    (hκ₀ : IsSecMod R Zn Z0 M₀ κ₀) (hκ : IsSecMod R Zn Q Mm κ) (hsec₀ : SecHyp R Zn Z0)
    (hsecQ : SecHyp R Zn Q) (hQZ0 : Q ≤ Z0) (hZ0Zn : Z0 ≤ Zn)
    (hZ0c : ∀ z ∈ Z0, ∀ y ∈ R, ⁅z, y⁆ ∈ Q) (hne : Zn ≠ Z0)
    (hirrG : ∀ U : Subgroup G, Z0 ≤ U → U ≤ Zn → (∀ ρ ∈ R, conjSubgroup ρ U = U) →
      U = Z0 ∨ U = Zn)
    {u u' : Fin 4 ⊕ Fin 4 → K} (hu : quadPlus 4 K u = 0) (hu' : quadPlus 4 K u' = 0)
    (huu' : polar (quadPlus 4 K) u u' ≠ 0) (hL₁R : L₁ ≤ R) (hL₂R : L₂ ≤ R)
    (hLu₁ : (L₁.subgroupOf R).map φ = E.LomGL u) (hLu₂ : (L₂.subgroupOf R).map φ = E.LomGL u')
    (hdec₀ : IsCompl (fixedSub M₀ ((L₁.subgroupOf R : Subgroup ↥R) : Set ↥R))
      (fixedSub M₀ ((L₂.subgroupOf R : Subgroup ↥R) : Set ↥R)))
    (hF₁ : fixedSub M₀ (Lom (quadPlus 4 K) u : Set (Gom (quadPlus 4 K))) =
      fixedSub M₀ ((L₁.subgroupOf R : Subgroup ↥R) : Set ↥R))
    (hF₂ : fixedSub M₀ (Lom (quadPlus 4 K) u' : Set (Gom (quadPlus 4 K))) =
      fixedSub M₀ ((L₂.subgroupOf R : Subgroup ↥R) : Set ↥R))
    (hC₁ : fixedSub M₀ ((L₁.subgroupOf R : Subgroup ↥R) : Set ↥R) = secSub κ₀ (Zn ⊓ L₁))
    (hC₂ : fixedSub M₀ ((L₂.subgroupOf R : Subgroup ↥R) : Set ↥R) = secSub κ₀ (Zn ⊓ L₂)) :
    (∃ x ∈ L₁, (∀ a ∈ Zn ⊓ L₁, ∃ z ∈ Zn, ⁅x, z⁆ * a⁻¹ ∈ Z0) ∧
      ∀ l ∈ L₁, ∀ z ∈ Zn, ∃ z' ∈ Zn, ⁅l, z⁆ * ⁅x, z'⁆⁻¹ ∈ Q) ∧
    (∃ x ∈ L₂, (∀ a ∈ Zn ⊓ L₂, ∃ z ∈ Zn, ⁅x, z⁆ * a⁻¹ ∈ Z0) ∧
      ∀ l ∈ L₂, ∀ z ∈ Zn, ∃ z' ∈ Zn, ⁅l, z⁆ * ⁅x, z'⁆⁻¹ ∈ Q) := by
  classical
  have hΦ := viaMatrix_surjective (e := E.equiv) φ hrange
  have hc0 : (polar (quadPlus 4 K) u u')⁻¹ ≠ 0 := inv_ne_zero huu'
  let P : HypPair (quadPlus 4 K) :=
    ⟨u, (polar (quadPlus 4 K) u u')⁻¹ • u', hu, by rw [map_smul_eq_sq, hu', mul_zero],
      by rw [polar_smul_right_eq, inv_mul_cancel₀ huu']⟩
  have hLomf : Lom (quadPlus 4 K) ((polar (quadPlus 4 K) u u')⁻¹ • u') =
      Lom (quadPlus 4 K) u' := Lom_smul hc0
  have hdecP : IsCompl (fixedSub M₀ (Lom (quadPlus 4 K) P.e : Set (Gom (quadPlus 4 K))))
      (fixedSub M₀ (Lom (quadPlus 4 K) P.f : Set (Gom (quadPlus 4 K)))) := by
    show IsCompl (fixedSub M₀ (Lom (quadPlus 4 K) u : Set (Gom (quadPlus 4 K))))
      (fixedSub M₀ (Lom (quadPlus 4 K) ((polar (quadPlus 4 K) u u')⁻¹ • u') :
        Set (Gom (quadPlus 4 K))))
    rw [hLomf, hF₁, hF₂]
    exact hdec₀
  obtain ⟨π, -, H⟩ := sec715Cm_extData (viaMatrix _ E.equiv φ hrange) hΦ hsm₀ hsm₁ hκ₀ hκ hsec₀
    hsecQ hQZ0 hZ0Zn hZ0c hne hirrG P hdecP
  have hQnd := nondegenerate_polarBilin_quadPlus 4 K
  have hι : 4 ≤ Fintype.card (Fin 4 ⊕ Fin 4) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have huu'' : polar (quadPlus 4 K) u' u ≠ 0 := by rwa [polar_comm]
  refine ⟨?_, ?_⟩
  · refine sec715Cm_final hK (viaMatrix _ E.equiv φ hrange) hsm₀ hsm₁ hκ₀ hκ hsec₀ hsecQ H ?_
      hL₁R (fun l hl => sec715Cm_mem_Lom E φ hrange hLu₁ (Subgroup.mem_subgroupOf.mpr hl)) ?_
    · show fixedSub M₀ (Lom (quadPlus 4 K) u : Set (Gom (quadPlus 4 K))) = _
      rw [hF₁, hC₁]
    · obtain ⟨y, hy, v, hv⟩ := exists_nonA2_of_map_Lom E hQnd hι φ hu huu'' hLu₁
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, ⟨v, by rw [viaMatrix_app]; exact hv⟩⟩
  · refine sec715Cm_final hK (viaMatrix _ E.equiv φ hrange) hsm₀ hsm₁ hκ₀ hκ hsec₀ hsecQ H.swap ?_
      hL₂R (fun l hl => ?_) ?_
    · show fixedSub M₀ (Lom (quadPlus 4 K) ((polar (quadPlus 4 K) u u')⁻¹ • u') :
        Set (Gom (quadPlus 4 K))) = _
      rw [hLomf, hF₂, hC₂]
    · show viaMatrix _ E.equiv φ hrange l ∈ Lom (quadPlus 4 K)
        ((polar (quadPlus 4 K) u u')⁻¹ • u')
      rw [hLomf]
      exact sec715Cm_mem_Lom E φ hrange hLu₂ (Subgroup.mem_subgroupOf.mpr hl)
    · obtain ⟨y, hy, v, hv⟩ := exists_nonA2_of_map_Lom E hQnd hι φ hu' huu' hLu₂
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, ⟨v, by rw [viaMatrix_app]; exact hv⟩⟩

end CFSG.RankThree.GF2n.Stroth80
