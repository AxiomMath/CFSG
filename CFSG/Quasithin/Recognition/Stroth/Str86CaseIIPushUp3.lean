module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIPushUp2
public import CFSG.Quasithin.Recognition.St84.Gen.PushZL2
public import CFSG.Quasithin.Recognition.Stroth.U3Vertex
public import CFSG.Quasithin.Background.HSU3Borel
public import CFSG.Quasithin.SteinbergBYEvenUnitaryTwoThreeControl
public import CFSG.Quasithin.Vol2.Ch3E215MC
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem5
public import CFSG.Quasithin.Vol2.Ch12Sec7L5t
public import CFSG.Quasithin.Recognition.Stroth.Str86Frame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell
open CFSG.Quasithin.F53Push CFSG.Quasithin.St84
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem pCore_subgroupOf_eq_of_pCoreOf_eq {X R : Subgroup G} (hR : R ≤ X)
    (h : pCoreOf 2 X = R) : pCore 2 ↥X = R.subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hR]
  exact h

private theorem isL2Quot_of_sup_quot_eq {X Q L : Subgroup G} {n : ℕ}
    (hXQ : pCoreOf 2 X = X ⊓ Q) (hLQ : pCoreOf 2 L = L ⊓ Q)
    (hXnorm : X ≤ Subgroup.normalizer (Q : Set G))
    (hLnorm : L ≤ Subgroup.normalizer (Q : Set G))
    (hsup : X ⊔ Q = L ⊔ Q) (h : IsL2Quot n (oTwoQuot ↥L)) :
    IsL2Quot n (oTwoQuot ↥X) := by
  have hpX' : pCore 2 ↥X = (X ⊓ Q).subgroupOf X :=
    pCore_subgroupOf_eq_of_pCoreOf_eq inf_le_left hXQ
  have hpL' : pCore 2 ↥L = (L ⊓ Q).subgroupOf L :=
    pCore_subgroupOf_eq_of_pCoreOf_eq inf_le_left hLQ
  have hpX : pCore 2 ↥X = Q.subgroupOf X := by
    rw [hpX', Subgroup.subgroupOf_inj]
    simpa using inf_comm X Q
  have hpL : pCore 2 ↥L = Q.subgroupOf L := by
    rw [hpL', Subgroup.subgroupOf_inj]
    simpa using inf_comm L Q
  haveI hNX : (Q.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hXnorm
  haveI hNL : (Q.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnorm
  haveI hNXsup : (Q.subgroupOf (X ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hXnorm
  haveI hNLsup : (Q.subgroupOf (L ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hLnorm
  let eX : oTwoQuot ↥X ≃* (↥X ⧸ Q.subgroupOf X) :=
    QuotientGroup.quotientMulEquivOfEq hpX
  let e2 : (↥X ⧸ Q.subgroupOf X) ≃*
      (↥(X ⊔ Q) ⧸ Q.subgroupOf (X ⊔ Q)) :=
    QuotientGroup.quotientInfEquivProdNormalizerQuotient X Q hXnorm
  let eY : ↥(X ⊔ Q) ≃* ↥(L ⊔ Q) := MulEquiv.subgroupCongr hsup
  let e3 : (↥(X ⊔ Q) ⧸ Q.subgroupOf (X ⊔ Q)) ≃*
      (↥(L ⊔ Q) ⧸ Q.subgroupOf (L ⊔ Q)) :=
    QuotientGroup.congr (Q.subgroupOf (X ⊔ Q)) (Q.subgroupOf (L ⊔ Q)) eY (by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        have hxy' : (x : G) = (y : G) := congrArg Subtype.val hxy
        show (y : G) ∈ Q
        rw [← hxy']
        exact Subgroup.mem_subgroupOf.mp hx
      · intro hy
        refine ⟨eY.symm y, ?_, eY.apply_symm_apply y⟩
        have hcoe : ((eY.symm y : ↥(X ⊔ Q)) : G) = (y : G) := rfl
        show (eY.symm y : G) ∈ Q
        rw [hcoe]
        exact Subgroup.mem_subgroupOf.mp hy)
  let e4 : (↥L ⧸ Q.subgroupOf L) ≃*
      (↥(L ⊔ Q) ⧸ Q.subgroupOf (L ⊔ Q)) :=
    QuotientGroup.quotientInfEquivProdNormalizerQuotient L Q hLnorm
  let eL : oTwoQuot ↥L ≃* (↥L ⧸ Q.subgroupOf L) :=
    QuotientGroup.quotientMulEquivOfEq hpL
  obtain ⟨eP⟩ := h
  exact ⟨(eX.trans (e2.trans (e3.trans (e4.symm.trans eL.symm)))).trans eP⟩

private theorem conjJoin_eq_conjJoinOf (A Z : Subgroup G) :
    F53Push.conjJoin A Z = conjJoinOf A Z := by
  rw [F53Push.conjJoin, conjJoinOf]
  rfl

private theorem exists_odd_mem_diff_borel {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hR111 : Hyp111R L1 L2 S) :
    ∃ g : G, g ∈ L1 ∧ Odd (orderOf g) ∧ g ∉ borelOf L1 S := by
  by_contra hcon
  push Not at hcon
  have hOle : oddOrderSubgroup L1 ≤ borelOf L1 S :=
    (Subgroup.closure_le (borelOf L1 S)).mpr fun x hx => hcon x hx.1 hx.2
  have hL1eq : L1 = (S ⊓ L1) ⊔ oddOrderSubgroup L1 := by
    have h := CFSG.Quasithin.sup_twoResidual_eq hF.1.h1.sylow
    rw [← CFSG.QuasithinUnique.Setup.oddOrderSubgroup_eq_twoResidual] at h
    exact h.symm
  have hS1le : S ⊓ L1 ≤ borelOf L1 S := CFSG.Quasithin.F1.sylow_le_borelOf L1 S
  have hL1le : L1 ≤ borelOf L1 S := by
    nth_rewrite 1 [hL1eq]
    exact sup_le hS1le hOle
  exact (not_le_of_gt (CFSG.Quasithin.F1.lt_borelOf hR111)) hL1le

private theorem le_normalizer_conjClosure_of_le_normalizer {K A X : Subgroup G}
    (hKX : K ≤ Subgroup.normalizer (X : Set G))
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) :
    K ≤ Subgroup.normalizer (conjClosure A X : Set G) := by
  rw [CFSG.Quasithin.conjClosure]
  refine CFSG.Quasithin.F7.le_normalizer_closure _ ?_
  intro k hk x hx
  obtain ⟨h, hh, a, ha, rfl⟩ := hx
  exact ⟨k * h * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hKX hk) h).mp hh,
    k * a * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hKA hk) a).mp ha, by group⟩

private theorem conj_mem_conjJoinOf_conj {b o : G} {Z : Subgroup G} {s : G}
    (hbZ : b ∈ Subgroup.normalizer (Z : Set G))
    (hs : s ∈ conjJoinOf (Subgroup.zpowers o) Z) :
    b * s * b⁻¹ ∈ conjJoinOf (Subgroup.zpowers (b * o * b⁻¹)) Z := by
  have hjoin : ∀ y : G, conjJoinOf (Subgroup.zpowers y) Z =
      ⨆ h : Subgroup.zpowers y, cj (h : G) Z := by
    intro y
    rw [conjJoinOf]
    exact iSup_subtype'
  rw [hjoin o] at hs
  rw [hjoin (b * o * b⁻¹)]
  rw [Subgroup.iSup_eq_closure] at hs ⊢
  refine Subgroup.closure_induction (p := fun s _ => b * s * b⁻¹ ∈
      Subgroup.closure (⋃ h : Subgroup.zpowers (b * o * b⁻¹), (cj (h : G) Z : Set G)))
    ?_ ?_ ?_ ?_ hs
  · intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨h, z, hz, rfl⟩ := hx
    have hmem : b * (h : G) * b⁻¹ ∈ Subgroup.zpowers (b * o * b⁻¹) := by
      have hh : (h : G) ∈ Subgroup.zpowers o := h.2
      rw [Subgroup.mem_zpowers_iff] at hh ⊢
      obtain ⟨k, hk⟩ := hh
      refine ⟨k, ?_⟩
      rw [← hk]
      simpa [MulAut.conj_apply, mul_assoc] using
        (map_zpow (MulAut.conj b) o k).symm
    have hz' : b * z * b⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hbZ z).mp hz
    have hmap : b * ((MulAut.conj (h : G)) z) * b⁻¹ ∈ cj (b * (h : G) * b⁻¹) Z := by
      refine Subgroup.mem_map.mpr ⟨b * z * b⁻¹, hz', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
      group
    exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨⟨b * (h : G) * b⁻¹, hmem⟩, hmap⟩)
  · simp
  · intro x y hx hy ihx ihy
    simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  · intro x hx ihx
    simpa [mul_assoc] using Subgroup.inv_mem _ ihx

def Str86BruhatCovering (L1 L2 S : Subgroup G) : Prop :=
  ∀ g : G, Odd (orderOf g) → g ∈ L1 → g ∉ bigB L1 L2 S →
    (P1 L1 L2 S : Set G) = (bigB L1 L2 S : Set G) ∪
      (bigB L1 L2 S : Set G) * ({g} : Set G) * (bigB L1 L2 S : Set G)

theorem bruhatCovering_of_sylowTwoTI {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hTI : SylowTwoTI (oTwoQuot ↥L1))
    (hidx : ((borelOf L1 S).subgroupOf L1).index =
      Nat.card (((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1))) + 1) :
    Str86BruhatCovering L1 L2 S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR111 : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have exists_g : ∃ g : G, g ∈ L1 ∧ Odd (orderOf g) ∧ g ∉ bigB L1 L2 S := by
    by_contra hcon
    push Not at hcon
    have hOddLe : oddOrderSubgroup L1 ≤ bigB L1 L2 S :=
      (Subgroup.closure_le (bigB L1 L2 S)).mpr fun x hx => hcon x hx.1 hx.2
    have hS1leB : S ⊓ L1 ≤ bigB L1 L2 S :=
      (CFSG.Quasithin.F1.sylow_le_borelOf L1 S).trans
        (le_sup_left.trans le_sup_left)
    have hL1eq : L1 = (S ⊓ L1) ⊔ oddOrderSubgroup L1 := by
      have h := CFSG.Quasithin.sup_twoResidual_eq hF.1.h1.sylow
      rw [← CFSG.QuasithinUnique.Setup.oddOrderSubgroup_eq_twoResidual] at h
      exact h.symm
    have hL1le : L1 ≤ bigB L1 L2 S := by
      nth_rewrite 1 [hL1eq]
      exact sup_le hS1leB hOddLe
    have hB1ltB : bigB L1 L2 S ⊓ L1 < L1 := by
      have h := CFSG.Quasithin.F1.lt_borelOf hR111
      rwa [inf_comm, CFSG.Quasithin.F1.inf_bigB_eq_borelOf]
    exact (not_le_of_gt hB1ltB) (le_inf hL1le le_rfl)
  obtain ⟨g, hgL1, hgodd, hgB⟩ := exists_g
  refine fun g' hg'odd hg'L1 hg'B => ?_
  have hmain : ∀ x ∈ L1, x ∈ borelOf L1 S ∨
      ∃ b1 ∈ borelOf L1 S, ∃ b2 ∈ borelOf L1 S, x = b1 * g * b2 := by
    let M := oTwoQuot ↥L1
    let π : ↥L1 →* M := QuotientGroup.mk' (pCore 2 ↥L1)
    let T : Subgroup M :=
      ((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1))
    let N : Subgroup M := ((borelOf L1 S).subgroupOf L1).map π
    have hdata := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hF.1.h1.sylow
    have hTp : IsPGroup 2 T := by simpa [T] using hdata.1
    have hTidx : ¬ 2 ∣ T.index := by simpa [T] using hdata.2.1
    have hNeq : N = Subgroup.normalizer (T : Set M) := by
      change Subgroup.map (QuotientGroup.mk' (pCore 2 ↥L1)) ((borelOf L1 S).subgroupOf L1) =
        Subgroup.normalizer
          (Subgroup.map (QuotientGroup.mk' (pCore 2 ↥L1)) ((S ⊓ L1).subgroupOf L1) :
            Set (oTwoQuot ↥L1))
      exact hdata.2.2
    have hTleN : T ≤ N := by
      rw [hNeq]
      exact Subgroup.le_normalizer
    have hker : π.ker ≤ (borelOf L1 S).subgroupOf L1 := by
      rw [show π.ker = pCore 2 ↥L1 from QuotientGroup.ker_mk' _]
      intro x hx
      have hx' : (x : G) ∈ pCoreOf 2 L1 := (F1.mem_pCore_iff_coe x).mp hx
      exact CFSG.Quasithin.F1.sylow_le_borelOf L1 S
        (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow hx')
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hNmap : N.index = ((borelOf L1 S).subgroupOf L1).index := by
      rw [show N = Subgroup.map π ((borelOf L1 S).subgroupOf L1) from rfl]
      exact Subgroup.index_map_eq ((borelOf L1 S).subgroupOf L1) hsurj hker
    have hNindex : N.index = Nat.card T + 1 := by
      rw [hNmap,
        show T = ((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1)) from rfl]
      exact hidx
    have hN2elem : ∀ w : M, w ∈ N → (∃ n : ℕ, w ^ (2 ^ n) = 1) → w ∈ T := by
      intro w hwN hw2
      have hTrelodd : ¬ 2 ∣ (T.subgroupOf N).index := by
        intro h2
        apply hTidx
        rw [← Subgroup.relIndex_mul_index hTleN]
        exact dvd_mul_of_dvd_left h2 _
      have hTsylN : IsSylowTwoOf T N :=
        ⟨hTleN, hTp, by simpa [Subgroup.relIndex] using hTrelodd⟩
      have hw2p : IsPGroup 2 (Subgroup.zpowers w) := by
        obtain ⟨n, hn⟩ := hw2
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
          (orderOf_dvd_of_pow_eq_one hn)
        refine IsPGroup.of_card (p := 2) (n := m) ?_
        rw [Nat.card_zpowers, hm]
      obtain ⟨c, hcN, hc⟩ := CFSG.Quasithin.H13.S127.L712.exists_conj_le (H := N) (T := T)
        (S := Subgroup.zpowers w) hTsylN hw2p
        (Subgroup.zpowers_le.mpr hwN)
      have hcw : c * w * c⁻¹ ∈ T := hc w (Subgroup.mem_zpowers w)
      have hcN' : c ∈ N := hcN
      have hNT : N ≤ Subgroup.normalizer (T : Set M) := by rw [hNeq]
      have hcNT : c⁻¹ ∈ Subgroup.normalizer (T : Set M) :=
        (Subgroup.normalizer _).inv_mem (hNT hcN')
      have hw : w ∈ T := by
        have := (Subgroup.mem_normalizer_iff.mp hcNT (c * w * c⁻¹)).mp hcw
        simpa [mul_assoc] using this
      exact hw
    have hyN : π ⟨g, hgL1⟩ ∉ N := by
      intro hy
      obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_map.mp hy
      have hk' : b⁻¹ * ⟨g, hgL1⟩ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hbπ, inv_mul_cancel]
      have hmem : ⟨g, hgL1⟩ ∈ (borelOf L1 S).subgroupOf L1 := by
        have hbB : b ∈ (borelOf L1 S).subgroupOf L1 := hb
        have := (borelOf L1 S).subgroupOf L1 |>.mul_mem hbB (hker hk')
        simpa using this
      exact hgB (by
        have := Subgroup.mem_subgroupOf.mp hmem
        exact (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S) this)
    have hInf : T ⊓ T.map (MulAut.conj (π ⟨g, hgL1⟩)).toMonoidHom = ⊥ := by
      let y : M := π ⟨g, hgL1⟩
      let Ty : Subgroup M := T.map (MulAut.conj y).toMonoidHom
      have hTyp : IsPGroup 2 Ty := hTp.map _
      have hTyidx : ¬ 2 ∣ Ty.index := by
        change ¬ 2 ∣ (T.map (MulAut.conj y).toMonoidHom).index
        have hidx : (T.map (MulAut.conj y).toMonoidHom).index = T.index :=
          Subgroup.index_map_equiv (H := T) (MulAut.conj y)
        rwa [hidx]
      have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (⊤ : Subgroup M) :=
        CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hTp, by simpa using hTidx⟩
      have hTysyl : CFSG.ABGLocalTools.IsSylowOf 2 Ty (⊤ : Subgroup M) :=
        CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hTyp, by simpa using hTyidx⟩
      have hne : T ≠ Ty := by
        intro heq
        have hyT : y ∈ Subgroup.normalizer (T : Set M) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          exact heq.symm
        apply hyN
        rwa [hNeq]
      have := SylowTwoTI.isSylowOf_inf_eq_bot hTI hTsyl hTysyl hne
      simpa [Ty] using this
    have hinj : Set.InjOn (fun s : M => ((s * π ⟨g, hgL1⟩ : M) : M ⧸ N)) (T : Set M) := by
      intro u hu u' hu' heq
      have h' : (u * π ⟨g, hgL1⟩)⁻¹ * (u' * π ⟨g, hgL1⟩) ∈ N := QuotientGroup.eq.mp heq
      have hzN : (π ⟨g, hgL1⟩)⁻¹ * (u⁻¹ * u') * π ⟨g, hgL1⟩ ∈ N := by
        have he : (π ⟨g, hgL1⟩)⁻¹ * (u⁻¹ * u') * π ⟨g, hgL1⟩ =
            (u * π ⟨g, hgL1⟩)⁻¹ * (u' * π ⟨g, hgL1⟩) := by group
        rwa [he]
      have hzT : u⁻¹ * u' ∈ T := T.mul_mem (T.inv_mem hu) hu'
      have hz2 : ∃ n : ℕ, (u⁻¹ * u') ^ (2 ^ n) = 1 := by
        obtain ⟨n, hn⟩ := hTp ⟨u⁻¹ * u', hzT⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
      have hconj2 : ∃ n : ℕ,
          ((π ⟨g, hgL1⟩)⁻¹ * (u⁻¹ * u') * π ⟨g, hgL1⟩) ^ (2 ^ n) = 1 := by
        obtain ⟨n, hn⟩ := hz2
        refine ⟨n, ?_⟩
        have hcongr := congrArg (MulAut.conj (π ⟨g, hgL1⟩)⁻¹) hn
        rw [map_pow, map_one] at hcongr
        simpa [MulAut.conj_apply, mul_assoc] using hcongr
      have hconjT : (π ⟨g, hgL1⟩)⁻¹ * (u⁻¹ * u') * π ⟨g, hgL1⟩ ∈ T :=
        hN2elem _ hzN hconj2
      have hmemTy : u⁻¹ * u' ∈ T.map (MulAut.conj (π ⟨g, hgL1⟩)).toMonoidHom := by
        refine Subgroup.mem_map.mpr ⟨(π ⟨g, hgL1⟩)⁻¹ * (u⁻¹ * u') * π ⟨g, hgL1⟩, hconjT, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
        group
      have hbot : u⁻¹ * u' ∈ (⊥ : Subgroup M) := by
        rw [← hInf]
        exact ⟨hzT, hmemTy⟩
      have hone : u⁻¹ * u' = 1 := Subgroup.mem_bot.mp hbot
      exact inv_mul_eq_one.mp hone
    have hcard : N.index ≤ (T : Set M).ncard + 1 := by
      have hEq : (T : Set M).ncard = Nat.card T :=
        (Nat.card_coe_set_eq (T : Set M)).symm
      rw [hNindex, hEq]
    have hbruM := CFSG.Quasithin.Ch3E215M.bruhat_of_injOn (L := M) (N := N)
      (y := π ⟨g, hgL1⟩) hyN (S := (T : Set M)) (fun _ hu => hTleN hu) hinj hcard
    have hbruL1 : ∀ x ∈ L1, x ∈ borelOf L1 S ∨
        ∃ b1 ∈ borelOf L1 S, ∃ b2 ∈ borelOf L1 S, x = b1 * g * b2 := by
      refine CFSG.Quasithin.Ch3E215M.bruhat_of_surjective
        (G₀ := G) (X := L1) (M := borelOf L1 S) (L := M) (g := g)
        (hg := hgL1) (ψ := π) (hker := hker) ?_
      intro y
      simpa [N, π] using hbruM y
    exact hbruL1
  have hB1leB : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hg'B1 : g' ∉ borelOf L1 S := fun h => hg'B (hB1leB h)
  have hcoverL1' : ∀ x ∈ L1, x ∈ borelOf L1 S ∨
      ∃ b1 ∈ borelOf L1 S, ∃ b2 ∈ borelOf L1 S, x = b1 * g' * b2 := by
    intro x hx
    rcases hmain x hx with hxB | ⟨b1, hb1, b2, hb2, rfl⟩
    · exact Or.inl hxB
    · rcases hmain g' hg'L1 with hgB1 | ⟨c1, hc1, c2, hc2, hgeq⟩
      · exact absurd hgB1 hg'B1
      · exact Or.inr ⟨b1 * c1⁻¹, (borelOf L1 S).mul_mem hb1 ((borelOf L1 S).inv_mem hc1),
          c2⁻¹ * b2, (borelOf L1 S).mul_mem ((borelOf L1 S).inv_mem hc2) hb2, by
          rw [hgeq]
          group⟩
  have hBleNL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (CFSG.Quasithin.F1.bigB_le_normalizer_left hR111).1
  have hBleP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hg'P1 : g' ∈ P1 L1 L2 S := (le_sup_left : L1 ≤ P1 L1 L2 S) hg'L1
  apply Set.eq_of_subset_of_subset
  · intro x hx
    obtain ⟨l, hl, b, hb, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hBleNL1).mp
        (by simpa [P1] using hx)
    rcases hcoverL1' l hl with hlB | ⟨b1, hb1, b2, hb2, hl_eq⟩
    · exact Or.inl ((bigB L1 L2 S).mul_mem (hB1leB hlB) hb)
    · refine Or.inr ?_
      rw [hl_eq]
      refine Set.mem_mul.mpr ⟨b1 * g', ?_, b2 * b, (bigB L1 L2 S).mul_mem (hB1leB hb2) hb, ?_⟩
      · exact Set.mem_mul.mpr ⟨b1, hB1leB hb1, g', by simp, rfl⟩
      · group
  · intro x hx
    rcases hx with hxB | hx
    · exact hBleP1 hxB
    · rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b2, hb2, rfl⟩ := hx
      rw [Set.mem_mul] at ha
      obtain ⟨b1, hb1, g0, hg0, rfl⟩ := ha
      simp only [Set.mem_singleton_iff] at hg0
      subst hg0
      exact (P1 L1 L2 S).mul_mem
        ((P1 L1 L2 S).mul_mem (hBleP1 hb1) hg'P1) (hBleP1 hb2)

theorem str86_bruhatCovering {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hB1 : VSzBig L1 ∨ VU3Big L1) :
    Str86BruhatCovering L1 L2 S := by
  classical
  let M := oTwoQuot ↥L1
  let π : ↥L1 →* M := QuotientGroup.mk' (pCore 2 ↥L1)
  let T : Subgroup M :=
    ((S ⊓ L1).subgroupOf L1).map (QuotientGroup.mk' (pCore 2 ↥L1))
  let N : Subgroup M := ((borelOf L1 S).subgroupOf L1).map π
  have hdata := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hF.1.h1.sylow
  have hTp : IsPGroup 2 T := by simpa [T] using hdata.1
  have hTidx : ¬ 2 ∣ T.index := by simpa [T] using hdata.2.1
  have hNeq : N = Subgroup.normalizer (T : Set M) := by
    change Subgroup.map (QuotientGroup.mk' (pCore 2 ↥L1)) ((borelOf L1 S).subgroupOf L1) =
      Subgroup.normalizer
        (Subgroup.map (QuotientGroup.mk' (pCore 2 ↥L1)) ((S ⊓ L1).subgroupOf L1) :
          Set (oTwoQuot ↥L1))
    exact hdata.2.2
  have hker : π.ker ≤ (borelOf L1 S).subgroupOf L1 := by
    rw [show π.ker = pCore 2 ↥L1 from QuotientGroup.ker_mk' _]
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 L1 := (F1.mem_pCore_iff_coe x).mp hx
    exact CFSG.Quasithin.F1.sylow_le_borelOf L1 S
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h1.sylow hx')
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNmap : N.index = ((borelOf L1 S).subgroupOf L1).index := by
    rw [show N = Subgroup.map π ((borelOf L1 S).subgroupOf L1) from rfl]
    exact Subgroup.index_map_eq ((borelOf L1 S).subgroupOf L1) hsurj hker
  rcases hB1 with hSz | hU3
  ·
    obtain ⟨a, ha, ⟨e⟩⟩ := hSz
    have hidx : ((borelOf L1 S).subgroupOf L1).index = Nat.card T + 1 := by
      let P : Sylow 2 M := hTp.toSylow hTidx
      have hPcoe : (P : Subgroup M) = T := rfl
      have hPcard : Nat.card (Sylow 2 M) =
          (Subgroup.normalizer ((P : Subgroup M) : Set M)).index :=
        P.card_eq_index_normalizer
      rw [← hNmap, hNeq, ← hPcoe, ← hPcard]
      simpa [hPcoe] using
        CFSG.ComponentClassification.Asc76X.card_sylow_of_mulEquiv_sz ha e P
    exact bruhatCovering_of_sylowTwoTI hF
      (str86_oTwoQuot_sylowTwoTI (Or.inl ⟨a, ha, ⟨e⟩⟩)) hidx
  ·
    obtain ⟨k, hk, F, hFld, hFin, hFc, hU3iso⟩ := hU3
    letI : Field F := hFld
    haveI : Finite F := hFin
    let q : ℕ := 2 ^ k
    have hTcard : Nat.card T = q ^ 3 := by
      rcases hU3iso with ⟨⟨eSU⟩⟩ | ⟨⟨ePSU⟩⟩
      ·
        let T' : Subgroup (StatedSU 3 (2 ^ k) F) := T.map eSU.toMonoidHom
        have hT'p : IsPGroup 2 T' := hTp.map eSU.toMonoidHom
        have hT'idx : ¬ 2 ∣ T'.index := by
          have hidx : T'.index = T.index := Subgroup.index_map_equiv (H := T) eSU
          rwa [hidx]
        let Tsyl : Sylow 2 (StatedSU 3 (2 ^ k) F) := hT'p.toSylow hT'idx
        have hcard' : Nat.card T' = q ^ 3 := by
          have hc := Sylow.card_eq_multiplicity Tsyl
          haveI : CharP F 2 :=
            CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := k) hFc
          have h2part := CFSG.Quasithin.H.SU3.card_statedSU_two (n := k) (K := F)
            (by omega) hFc
          rw [h2part] at hc
          simpa [Tsyl, q] using hc
        rwa [Subgroup.card_map_of_injective eSU.injective] at hcard'
      ·
        obtain ⟨r, hcardG, hrodd, -⟩ :=
          CFSG.Quasithin.SteinbergBY.card_PSU3_arith hk hFc
        let T' : Subgroup (StatedProj (StatedSU 3 (2 ^ k) F)) := T.map ePSU.toMonoidHom
        have hT'p : IsPGroup 2 T' := hTp.map ePSU.toMonoidHom
        have hT'idx : ¬ 2 ∣ T'.index := by
          have hidx : T'.index = T.index := Subgroup.index_map_equiv (H := T) ePSU
          rwa [hidx]
        let Tsyl : Sylow 2 (StatedProj (StatedSU 3 (2 ^ k) F)) :=
          hT'p.toSylow hT'idx
        have hcard' : Nat.card T' = q ^ 3 := by
          have hc := Sylow.card_eq_multiplicity Tsyl
          have hq0 : (2 ^ k) ^ 3 ≠ 0 := by positivity
          have hr0 : r ≠ 0 := by
            intro hr
            rw [hr, mul_zero] at hcardG
            exact Nat.card_pos.ne' hcardG
          have h2r : ¬ 2 ∣ r := by
            rw [← even_iff_two_dvd]
            exact Nat.not_even_iff_odd.mpr hrodd
          have hqfac : ((2 ^ k) ^ 3).factorization 2 = 3 * k := by
            rw [show (2 ^ k) ^ 3 = 2 ^ (3 * k) by rw [← pow_mul, mul_comm]]
            simp [Nat.Prime.factorization_pow Nat.prime_two]
          have hfac : (Nat.card (StatedProj (StatedSU 3 (2 ^ k) F))).factorization 2 =
              3 * k := by
            rw [hcardG, Nat.factorization_mul hq0 hr0]
            change ((2 ^ k) ^ 3).factorization 2 + r.factorization 2 = 3 * k
            rw [hqfac, Nat.factorization_eq_zero_of_not_dvd h2r, add_zero]
          rw [hfac] at hc
          have hc' : Nat.card T' = 2 ^ (3 * k) := by simpa [Tsyl] using hc
          have hgoal : Nat.card T' = (2 ^ k) ^ 3 := by
            rw [hc', show 2 ^ (3 * k) = (2 ^ k) ^ 3 by rw [← pow_mul, mul_comm]]
          simpa [q] using hgoal
        rwa [Subgroup.card_map_of_injective ePSU.injective] at hcard'
    have hidx : ((borelOf L1 S).subgroupOf L1).index = Nat.card T + 1 := by
      have hbi := index_borelOf_of_u3 (L := L1) (S := S) hk hFc hF.1.h1.sylow hU3iso
      rw [hbi, hTcard]
    exact bruhatCovering_of_sylowTwoTI hF
      (str86_oTwoQuot_sylowTwoTI (Or.inr (Or.inl ⟨k, hk, F, hFld, hFin, hFc, hU3iso⟩)))
      hidx

theorem str86_false_of_pushUp {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    {P : Subgroup G} (hP2 : IsPGroup 2 P) (hP1 : P ≤ P1 L1 L2 S)
    (hPn : P1 L1 L2 S ≤ Subgroup.normalizer (P : Set G)) (hPQ : ¬ P ≤ Q2 L1 L2 S)
    (hR : P2 L1 L2 S ≤ Subgroup.normalizer ((P ⊓ Q2 L1 L2 S : Subgroup G) : Set G)) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR111 : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  set B : Subgroup G := bigB L1 L2 S with hBdef
  set P₁ : Subgroup G := P1 L1 L2 S with hP₁def
  set P₂ : Subgroup G := P2 L1 L2 S with hP₂def
  set Q₂ : Subgroup G := Q2 L1 L2 S with hQ₂def
  set X : Subgroup G := conjClosure P P₂ with hXdef
  set R : Subgroup G := P ⊓ Q₂ with hRdef
  set Z : Subgroup G := pushZ X P with hZdef
  have hPleQ₁ : P ≤ Q1 L1 L2 S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP1 hPn hP2
  have hQleS : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)
  have hPS : P ≤ S := hPleQ₁.trans hQleS
  have hPleP₂ : P ≤ P₂ := by
    rw [hP₂def]
    exact hPS.trans (le_sup_right.trans le_sup_right)
  have hPB : B ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    exact hPn (le_sup_right (a := L1) hx)
  obtain ⟨hXsyl₀, hXcore₀, hXsup₀⟩ :=
    str86_pu_sylow hF hSB hB2 h2 hPS hPB hPQ hR
  have hXsyl : IsSylowTwoOf P X := by
    simpa [hXdef, hP₂def] using hXsyl₀
  have hXcore : pCoreOf 2 X = R := by
    simpa [hXdef, hP₂def, hQ₂def, hRdef] using hXcore₀
  have hXsup : X ⊔ Q₂ = L2 ⊔ Q₂ := by
    simpa [hXdef, hP₂def, hQ₂def] using hXsup₀
  have hXleP₂ : X ≤ P₂ := by
    rw [hXdef, hP₂def]
    refine conjClosure_le ?_
    intro h hh z hz
    exact P₂.mul_mem (P₂.mul_mem hh (hPleP₂ hz)) (P₂.inv_mem hh)
  have hP₂normX : P₂ ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact CFSG.Quasithin.le_normalizer_conjClosure P (P2 L1 L2 S)
  have hP₂char : CharTwo P₂ := by
    rw [hP₂def]
    have h := F1.parabolic_charTwo (Li := L2) (Lj := L1) (S := S) hR111.symm
    rwa [bigB_comm L1 L2 S] at h
  have hXchar : CharTwo X :=
    CFSG.Quasithin.A4.charTwo_of_normal hXleP₂ hP₂normX hP₂char
  have hQ₂leB : Q₂ ≤ B := by
    rw [hQ₂def, hBdef]
    have h := F1.pCoreOf_parabolic_le_bigB (Li := L2) (Lj := L1) (S := S) hR111.symm
    rwa [bigB_comm L1 L2 S] at h
  have hQ₂2 : IsPGroup 2 Q₂ := by
    rw [hQ₂def]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hXnormQ₂ : X ≤ Subgroup.normalizer (Q₂ : Set G) := by
    refine hXleP₂.trans ?_
    rw [hQ₂def]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hL2normQ₂ : L2 ≤ Subgroup.normalizer (Q₂ : Set G) := by
    refine (le_sup_left : L2 ≤ P₂).trans ?_
    rw [hQ₂def]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hXRnormal : ((X ⊓ Q₂).subgroupOf X).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
    exact (le_inf Subgroup.le_normalizer hXnormQ₂).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hXQleR : X ⊓ Q₂ ≤ R := by
    have h2' : IsPGroup 2 ↥(X ⊓ Q₂) := by
      apply IsPGroup.to_le (hK := hQ₂2)
      exact inf_le_right
    have h := CFSG.LieType.BorelTits.le_pCoreOf (r := 2) (N := X ⊓ Q₂) (H := X)
      inf_le_left hXRnormal h2'
    rw [hXcore] at h
    exact h
  have hXQeqR : X ⊓ Q₂ = R := by
    refine le_antisymm hXQleR ?_
    rw [hRdef]
    refine le_inf ?_ inf_le_right
    rw [hXdef]
    exact inf_le_left.trans (le_conjClosure P P₂)
  obtain ⟨n, hn⟩ := h2
  have hn2 : 2 ≤ n :=
    CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hn
  have hLQ : pCoreOf 2 L2 = L2 ⊓ Q₂ := by
    have h := F1.inf_pCoreOf_parabolic_eq (Li := L2) (Lj := L1) (S := S) hR111.symm
    rw [bigB_comm L1 L2 S] at h
    have h' : Q₂ ⊓ L2 = pCoreOf 2 L2 := by simpa [hQ₂def] using h
    rw [← h', inf_comm]
  have hXquot : IsL2Quot n (oTwoQuot ↥X) :=
    isL2Quot_of_sup_quot_eq (hXcore.trans hXQeqR.symm) hLQ hXnormQ₂ hL2normQ₂ hXsup hn
  have hZne : Z ≠ ⊥ := by
    rw [hZdef]
    exact pushZ_ne_bot_L2 hXquot hXsyl
  have hnc : NoCharNormal P X := by
    intro C hCP hCne hCchar hXC
    have hP1normC : P₁ ≤ Subgroup.normalizer (C : Set G) :=
      hPn.trans (CFSG.Quasithin.H13.Lem5.normalizer_le_normalizer_of_characteristic
        hCP hCchar)
    have hBnormC : B ≤ Subgroup.normalizer (C : Set G) :=
      (le_sup_right : B ≤ P₁).trans (by simpa [hP₁def] using hP1normC)
    have hL2leXB : L2 ≤ X ⊔ B := by
      have h1 : L2 ≤ L2 ⊔ Q₂ := le_sup_left
      rw [← hXsup] at h1
      exact h1.trans (sup_le le_sup_left (hQ₂leB.trans le_sup_right))
    have hP₂leXB : P₂ ≤ X ⊔ B := by
      rw [hP₂def]
      exact sup_le hL2leXB le_sup_right
    have hP₂normC : P₂ ≤ Subgroup.normalizer (C : Set G) :=
      hP₂leXB.trans (sup_le hXC hBnormC)
    have hG0normC : P₁ ⊔ P₂ ≤ Subgroup.normalizer (C : Set G) :=
      sup_le hP1normC hP₂normC
    have hC2 : IsPGroup 2 C := hP2.to_le hCP
    have hPleP₁ : P ≤ P₁ := by simpa [hP₁def] using hP1
    have hCle : C ≤ P₁ ⊔ P₂ := hCP.trans (hPleP₁.trans le_sup_left)
    have hCcore : C ≤ pCoreOf 2 (P₁ ⊔ P₂) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCle hG0normC hC2
    have hG0 : P₁ ⊔ P₂ = L1 ⊔ L2 ⊔ S := by
      rw [hP₁def, hP₂def]
      exact f112_parabolic_sup_eq L1 L2 S
    rw [hG0, hF.1.o2] at hCcore
    exact hCne (le_bot_iff.mp hCcore)

  obtain ⟨g, hgL1, hgodd, hgB1⟩ := exists_odd_mem_diff_borel hF hR111
  have hgB : g ∉ B := by
    intro hg
    apply hgB1
    have hmem : g ∈ L1 ⊓ bigB L1 L2 S := ⟨hgL1, hg⟩
    rwa [CFSG.Quasithin.F1.inf_bigB_eq_borelOf hR111] at hmem
  have hP1eq : (P1 L1 L2 S : Set G) = (B : Set G) ∪
      (B : Set G) * ({g} : Set G) * (B : Set G) := by
    simpa [hBdef] using
      (str86_bruhatCovering hF hB1) g hgodd hgL1 (by simpa [hBdef] using hgB)
  have hgP1 : g ∈ P₁ := by
    rw [hP₁def]
    exact (le_sup_left : L1 ≤ P1 L1 L2 S) hgL1
  have hBleNL1 : B ≤ Subgroup.normalizer (L1 : Set G) := by
    rw [hBdef]
    exact (CFSG.Quasithin.F1.bigB_le_normalizer_left hR111).1
  have hBleP₁ : B ≤ P₁ := by
    rw [hP₁def]
    exact le_sup_right
  have hBnormX : B ≤ Subgroup.normalizer (X : Set G) := by
    have hBleP₂ : B ≤ P₂ := by
      rw [hP₂def]
      exact le_sup_right
    exact hBleP₂.trans hP₂normX
  have hBnormΩ : B ≤ Subgroup.normalizer (omegaOneCenterOf P : Set G) := by
    rw [hBdef]
    exact hPB.trans (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf P)
  have hBnormZ : B ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZdef]
    exact le_normalizer_conjClosure_of_le_normalizer hBnormX hBnormΩ
  let Ng : B → Subgroup G := fun b =>
    conjJoinOf (Subgroup.zpowers ((b : G) * g * (b : G)⁻¹)) Z
  let N : Subgroup G := conjClosure Z P₁
  have hNnormP1 : P₁ ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure Z P₁
  have hconjP1 : ∀ b : B, (b : G) * g * (b : G)⁻¹ ∈ P₁ := by
    intro b
    have hbN : (b : G) ∈ Subgroup.normalizer (L1 : Set G) := hBleNL1 b.2
    have hconjL : (b : G) * g * (b : G)⁻¹ ∈ L1 :=
      (Subgroup.mem_normalizer_iff.mp hbN g).mp hgL1
    rw [hP₁def]
    exact (le_sup_left : L1 ≤ P1 L1 L2 S) hconjL
  have hstep : ∀ b : B, Ng b ≤ R ∧ X ≤ Subgroup.normalizer (Ng b : Set G) := by
    intro b
    have hbodd : Odd (orderOf ((b : G) * g * (b : G)⁻¹)) := by
      have h := (MulAut.conj (b : G)).orderOf_eq g
      rw [show (MulAut.conj (b : G)) g = (b : G) * g * (b : G)⁻¹ from rfl] at h
      rw [h]
      exact hgodd
    have hA : Subgroup.zpowers ((b : G) * g * (b : G)⁻¹) ≤
        Subgroup.normalizer (P : Set G) :=
      Subgroup.zpowers_le.mpr (hPn (hconjP1 b))
    have hAo : Odd (Nat.card ↥(Subgroup.zpowers ((b : G) * g * (b : G)⁻¹))) := by
      rw [Nat.card_zpowers]
      exact hbodd
    have h := conjJoinOf_pushZ_le_L2 (n := n) (by omega) hXchar hXquot hXsyl hnc hA hAo
    constructor
    · dsimp [Ng]
      rw [hXcore] at h
      simpa [hZdef] using h.1
    · dsimp [Ng]
      simpa [hZdef] using h.2
  have hNg_le_R : ∀ b : B, Ng b ≤ R := fun b => (hstep b).1
  have hXnormNg : ∀ b : B, X ≤ Subgroup.normalizer (Ng b : Set G) := fun b => (hstep b).2
  have hN_le_join : N ≤ (⨆ b : B, Ng b) := by
    change conjClosure Z P₁ ≤ (⨆ b : B, Ng b)
    refine CFSG.Quasithin.conjClosure_le ?_
    intro x hxP1 z hzZ
    have hdec : x ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, x = b₁ * g * b₂ := by
      have hx' : x ∈ (P1 L1 L2 S : Set G) := by simpa [hP₁def] using hxP1
      rw [hP1eq] at hx'
      rcases hx' with hxB | hx'
      · exact Or.inl hxB
      · simp only [Set.mem_mul, Set.mem_singleton_iff] at hx'
        obtain ⟨y, ⟨b₁, hb₁, b₂, hb₂, rfl⟩, b₃, hb₃, rfl⟩ := hx'
        subst hb₂
        exact Or.inr ⟨b₁, hb₁, b₃, hb₃, by group⟩
    rcases hdec with hxB | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    · have hxz : x * z * x⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hBnormZ hxB) z).mp hzZ
      have hZleNg1 : Z ≤ Ng ⟨1, B.one_mem⟩ := by
        dsimp [Ng]
        have h := F53Push.le_conjJoin (X := Subgroup.zpowers g) (J := Z)
        simpa only [Subgroup.coe_one, one_mul, mul_one, inv_one,
          conjJoin_eq_conjJoinOf] using h
      exact le_iSup Ng ⟨1, B.one_mem⟩ (hZleNg1 hxz)
    · have hz' : b₂ * z * b₂⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hBnormZ hb₂) z).mp hzZ
      have hgz : g * (b₂ * z * b₂⁻¹) * g⁻¹ ∈ conjJoinOf (Subgroup.zpowers g) Z := by
        have hmem : (MulAut.conj g) (b₂ * z * b₂⁻¹) ∈ cj g Z :=
          Subgroup.mem_map.mpr ⟨b₂ * z * b₂⁻¹, hz', rfl⟩
        have h := F53Push.cj_le_conjJoin (X := Subgroup.zpowers g) (J := Z)
          (Subgroup.mem_zpowers g) hmem
        simpa [MulAut.conj_apply, conjJoin_eq_conjJoinOf] using h
      have hconj := conj_mem_conjJoinOf_conj (b := b₁) (o := g) (Z := Z)
        (hBnormZ hb₁) hgz
      have heq : (b₁ * g * b₂) * z * (b₁ * g * b₂)⁻¹ =
          b₁ * (g * (b₂ * z * b₂⁻¹) * g⁻¹) * b₁⁻¹ := by group
      rw [heq]
      exact le_iSup Ng ⟨b₁, hb₁⟩ hconj
  have hjoin_le_N : (⨆ b : B, Ng b) ≤ N := by
    refine iSup_le fun b => ?_
    rw [show Ng b = conjJoinOf (Subgroup.zpowers ((b : G) * g * (b : G)⁻¹)) Z from rfl]
    rw [conjJoinOf]
    refine iSup₂_le fun h hh x hx => ?_
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hhP1 : h ∈ P₁ := (Subgroup.zpowers_le.mpr (hconjP1 b)) hh
    have hmem : (MulAut.conj h) z ∈ conjClosure Z P₁ := by
      simpa [MulAut.conj_apply] using CFSG.Quasithin.mem_conjClosure (H := P₁) hhP1 hz
    exact hmem
  have hNjoin : N = ⨆ b : B, Ng b := le_antisymm hN_le_join hjoin_le_N
  have hNleR : N ≤ R := by
    rw [hNjoin]
    exact iSup_le hNg_le_R
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := by
    rw [hNjoin]
    exact (le_iInf hXnormNg).trans (Subgroup.iInf_normalizer_le_normalizer_iSup Ng)
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := hBleP₁.trans hNnormP1
  have hP₂N : P₂ ≤ Subgroup.normalizer (N : Set G) := by
    have hL2leXB : L2 ≤ X ⊔ B := by
      have h1 : L2 ≤ L2 ⊔ Q₂ := le_sup_left
      rw [← hXsup] at h1
      exact h1.trans (sup_le le_sup_left (hQ₂leB.trans le_sup_right))
    have hP₂leXB : P₂ ≤ X ⊔ B := by
      rw [hP₂def]
      exact sup_le hL2leXB le_sup_right
    exact hP₂leXB.trans (sup_le hXN hBN)
  have hNQ₂ : N ≤ Q₂ := hNleR.trans inf_le_right
  have hN2 : IsPGroup 2 ↥N := IsPGroup.to_le hQ₂2 hNQ₂
  have hNleG0 : N ≤ P₁ ⊔ P₂ := hNleR.trans (by
    rw [hRdef]
    exact (inf_le_left : P ⊓ Q₂ ≤ P).trans (hP1.trans le_sup_left))
  have hG0normN : P₁ ⊔ P₂ ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hNnormP1 hP₂N
  have hNcore : N ≤ pCoreOf 2 (P₁ ⊔ P₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) (N := N) (H := P₁ ⊔ P₂)
      hNleG0 hG0normN hN2
  have hG0 : P₁ ⊔ P₂ = L1 ⊔ L2 ⊔ S := by
    rw [hP₁def, hP₂def]
    exact f112_parabolic_sup_eq L1 L2 S
  rw [hG0, hF.1.o2] at hNcore
  have hNbot : N = ⊥ := le_bot_iff.mp hNcore
  have hZleN : Z ≤ N := by
    change Z ≤ conjClosure Z P₁
    exact CFSG.Quasithin.le_conjClosure Z P₁
  have hZbot : Z = ⊥ := le_bot_iff.mp (hZleN.trans hNbot.le)
  exact hZne hZbot

end CFSG.Quasithin.Stroth

end
