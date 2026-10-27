module

public import CFSG.Permutation.FiveTransitive.Degree24Order96TwelveAction

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

theorem fixed_action_ker_le_cycleSupport_ker_of_support_twelve
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (R : Subgroup P) (r : R)
    (hRgenerated :
      R = Subgroup.zpowers (r : P))
    (hrOrder : orderOf r = 3)
    (hrSupport :
      ((r : P) : Equiv.Perm X).support.card = 18) :
    let F : Set X := MulAction.fixedPoints R X
    let N : Subgroup P :=
      Subgroup.normalizer (R : Set P)
    let ρ : N →* Equiv.Perm F :=
      MulAction.toPermHom N F
    let ψ :=
      normalizerCycleSupportMap
        X P R r hRgenerated hrOrder
    ∀ (_hKerCard : Nat.card ρ.ker = 6)
      (t : ρ.ker),
      orderOf t = 2 →
      MulAut.conj
          ((((t : ρ.ker) : N) : P))
          (r : P) =
        (r : P)⁻¹ →
      (((((t : ρ.ker) : N) : P) :
          Equiv.Perm X).support.card = 12) →
      ρ.ker ≤ ψ.ker := by
  classical
  dsimp
  intro _hKerCard t htOrder hinverts htSupport
  let F : Set X := MulAction.fixedPoints R X
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let ψ :=
    normalizerCycleSupportMap
      X P R r hRgenerated hrOrder
  let rN : N :=
    ⟨(r : P), R.le_normalizer r.prop⟩
  have hrFixed : ρ rN = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact
      MulAction.mem_fixedPoints.mp x.2 r
  let rK : ρ.ker := ⟨rN, hrFixed⟩
  have hrKOrder : orderOf rK = 3 := by
    calc
      orderOf rK = orderOf (rK : N) :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf rN := by
        rfl
      _ = orderOf (rN : P) :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf (r : P) := by
        rfl
      _ = orderOf r :=
        Subgroup.orderOf_coe _
      _ = 3 := hrOrder
  have hfix :
      ∀ x : X,
        ((r : P) : Equiv.Perm X) x = x →
          ((((t : ρ.ker) : N) : P) :
            Equiv.Perm X) x = x := by
    intro x hx
    have hxF : x ∈ F := by
      rw [MulAction.mem_fixedPoints]
      intro a
      have haZ :
          (a : P) ∈
            Subgroup.zpowers (r : P) := by
        rw [← hRgenerated]
        exact a.prop
      obtain ⟨z, hz⟩ :=
        Subgroup.mem_zpowers_iff.mp haZ
      have hz' := congrArg Subtype.val hz
      rw [Subgroup.coe_zpow] at hz'
      change ((a : P) : Equiv.Perm X) x = x
      rw [← hz']
      exact
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
          hx z
    have htKer : ρ (t : N) = 1 := t.prop
    have happ :=
      congrFun
        (congrArg DFunLike.coe htKer)
        (⟨x, hxF⟩ : F)
    exact congrArg Subtype.val happ
  have hψt : ψ (t : N) = 1 := by
    exact
      cycleSupport_action_eq_one_of_inverting_support_eq_twelve
        X P R r hRgenerated (t : N)
          hrOrder hrSupport
          (by
            simpa only [MulAut.conj_apply, ρ,
              N, F] using hinverts)
          hfix
          (by
            simpa only [ρ, N, F] using htSupport)
  have hψr : ψ rN = 1 := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    obtain ⟨c, hc, hcb⟩ :=
      Finset.mem_image.mp b.2
    rw [normalizerCycleSupportMap_apply_val]
    change (r : P) • b.1 = b.1
    ext x
    rw [← hcb]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ :=
        Finset.mem_smul_finset.mp hx
      rw [← hyx]
      exact
        (Equiv.Perm.mem_cycleFactorsFinset_support
          hc y).2 hy
    · intro hx
      refine
        Finset.mem_smul_finset.mpr
          ⟨(((r : P) : Equiv.Perm X)⁻¹ x),
            ?_, ?_⟩
      · have hinvariant :=
          (Equiv.Perm.mem_cycleFactorsFinset_support
            hc
            (((r : P) : Equiv.Perm X)⁻¹ x)).1
            (by simpa using hx)
        exact hinvariant
      · change ((r : P) : Equiv.Perm X)
          (((r : P) : Equiv.Perm X)⁻¹ x) = x
        exact ((r : P) : Equiv.Perm X).apply_symm_apply x
  let K : Subgroup N := ρ.ker
  let ψK :
      K →*
        Equiv.Perm
          (cycleSupportFinset
            ((r : P) : Equiv.Perm X)) :=
    ψ.comp K.subtype
  let tK : K := t
  let L : Subgroup K :=
    Subgroup.closure ({rK, tK} : Set K)
  have hrKL : rK ∈ L := by
    exact Subgroup.subset_closure
      (Set.mem_insert rK {tK})
  have htKL : tK ∈ L := by
    exact Subgroup.subset_closure
      (Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton tK)))
  have hthreeDvd : 3 ∣ Nat.card L := by
    have hdiv :=
      Subgroup.card_dvd_of_le
        (Subgroup.zpowers_le.mpr hrKL)
    rwa [Nat.card_zpowers, hrKOrder] at hdiv
  have htKOrder : orderOf tK = 2 := by
    simpa only [tK, K, ρ, N, F] using htOrder
  have htwoDvd : 2 ∣ Nat.card L := by
    have hdiv :=
      Subgroup.card_dvd_of_le
        (Subgroup.zpowers_le.mpr htKL)
    rwa [Nat.card_zpowers, htKOrder] at hdiv
  have hsixDvd : 6 ∣ Nat.card L := by
    have hdiv : 2 * 3 ∣ Nat.card L :=
      (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd
        htwoDvd hthreeDvd
    norm_num at hdiv
    simpa only [Nat.card_eq_fintype_card] using hdiv
  have hLdvd : Nat.card L ∣ 6 := by
    have hdiv :=
      Subgroup.card_subgroup_dvd_card L
    rw [show Nat.card K = 6 by
      simpa only [K, ρ, N, F] using _hKerCard] at hdiv
    exact hdiv
  have hLcard : Nat.card L = 6 := by
    have hlower : 6 ≤ Nat.card L :=
      Nat.le_of_dvd Nat.card_pos hsixDvd
    have hupper : Nat.card L ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hLdvd
    omega
  have hLeqTop : L = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hLcard]
    simpa only [K, ρ, N, F] using _hKerCard.symm
  have hrKψ : rK ∈ ψK.ker := by
    rw [MonoidHom.mem_ker]
    change ψ (K.subtype rK) = 1
    rw [show K.subtype rK = rN by rfl]
    exact hψr
  have htKψ : tK ∈ ψK.ker := by
    rw [MonoidHom.mem_ker]
    change ψ (K.subtype tK) = 1
    rw [show K.subtype tK = (t : N) by rfl]
    exact hψt
  have hLle : L ≤ ψK.ker := by
    rw [Subgroup.closure_le]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact hrKψ
    · exact htKψ
  intro q hq
  let qK : K := ⟨q, hq⟩
  have hqL : qK ∈ L := by
    rw [hLeqTop]
    exact Subgroup.mem_top qK
  have hqψK : qK ∈ ψK.ker :=
    hLle hqL
  rw [MonoidHom.mem_ker] at hqψK ⊢
  change ψ (K.subtype qK) = 1 at hqψK
  change ψ q = 1
  rw [show K.subtype qK = q by rfl] at hqψK
  exact hqψK

end FiveTransitive.Degree24

end CFSG
