module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_24SolvableOddP
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerZpowers
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise commutatorElement

/-- If the commutator of an odd `p`-subgroup with an involution lies in the
odd core, the solvable odd-core reduction puts it in the `p`-core. -/
public theorem commutator_le_pCore_of_le_pPrimeCore
    {X : Type u} [Group X] [Finite X]
    (P : Subgroup X) (p : ℕ) {t : X}
    (hp : p.Prime) (hpodd : Odd p)
    (ht : IsInvolution t) (hPp : IsPGroup p P)
    (hPinv : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer (P : Set X))
    (hcommO : ⁅P, Subgroup.zpowers t⁆ ≤ pPrimeCore 2 X) :
    ⁅P, Subgroup.zpowers t⁆ ≤ pCore p X := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup X := Subgroup.zpowers t
  let C : Subgroup X := ⁅P, Q⁆
  let O : Subgroup X := pPrimeCore 2 X
  let Y : Subgroup X := O ⊔ Q
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ht.2) ht.1
  have hQcard : Nat.card Q = 2 := by
    simp [Q, Nat.card_zpowers, htorder]
  have hQtwo : IsPGroup 2 Q := by
    refine IsPGroup.of_card (n := 1) ?_
    simp [hQcard]
  have hQcent : Q ≤ Subgroup.centralizer ({t} : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzt : z = t := by simpa using hz
    subst z
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    exact (Commute.refl t).zpow_right n
  have hQP : Q ≤ Subgroup.normalizer (P : Set X) := hQcent.trans hPinv
  have hCleP : C ≤ P := by
    simpa [C] using
      (Subgroup.le_normalizer_iff_commutator_le_left (H := Q) (K := P)).mp hQP
  have hCp : IsPGroup p C :=
    (hPp.to_subgroup (C.subgroupOf P)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hCleP)
  have hpne2 : p ≠ 2 := by
    intro h
    subst p
    exact hpodd.not_two_dvd_nat (by norm_num)
  have hcopQP : Nat.Coprime (Nat.card Q) (Nat.card P) :=
    IsPGroup.coprime_card_of_ne 2 p hpne2.symm Q P hQtwo hPp
  have hCself : ⁅C, Q⁆ = C := by
    simpa [C] using
      BenderSuzuki.ig1114_commutator_idempotent_of_coprime P Q hcopQP hQP
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using (pPrimeCore_coprime_card (p := 2) (G := X))
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  have hOQcop : Nat.Coprime (Nat.card O) (Nat.card Q) := by
    rw [hQcard]
    exact hOcop.symm
  have hOQdisj : Disjoint O Q :=
    Subgroup.disjoint_of_coprime_natCard hOQcop
  let OY : Subgroup Y := O.subgroupOf Y
  let QY : Subgroup Y := Q.subgroupOf Y
  have : O.Normal := by dsimp [O]; infer_instance
  have hcomp : OY.IsComplement' QY := by
    simpa [OY, QY, Y] using
      isComplement'_subgroupOf_sup_of_disjoint O Q hOQdisj
  have hOcard : Nat.card OY = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show O ≤ Y from le_sup_left)).toEquiv
  have : OY.Normal := by
    simpa [OY, Y] using (Subgroup.Normal.subgroupOf (inferInstance : O.Normal) Y)
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  let : Group.IsSolvable O := hOsolv
  have hOYsolv : Group.IsSolvable OY :=
    isSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (show O ≤ Y from le_sup_left)).symm
  let : Group.IsSolvable OY := hOYsolv
  have hQcomm : IsMulCommutative Q := by infer_instance
  have hQYcomm : IsMulCommutative QY :=
    isMulCommutative_of_surjective
      (Subgroup.subgroupOfEquivOfLe (show Q ≤ Y from le_sup_right)).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (show Q ≤ Y from le_sup_right)).symm.surjective
      hQcomm
  have hQYsolv : Group.IsSolvable QY :=
    Group.isSolvable_of_comm (fun a b => (IsMulCommutative.is_comm (M := QY)).comm a b)
  let : Group.IsSolvable QY := hQYsolv
  have hquotSolv : Group.IsSolvable (Y ⧸ OY) :=
    isSolvable_of_mulEquiv hcomp.symm.QuotientMulEquiv.symm
  let : Group.IsSolvable (Y ⧸ OY) := hquotSolv
  have hYsolv : Group.IsSolvable Y :=
    isSolvable_of_normal_subgroup_and_quotient OY
  have hQYtwo : IsPGroup 2 QY := by
    exact hQtwo.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show Q ≤ Y from le_sup_right)).symm
  have hQYindexOdd : Odd QY.index := by
    rw [hcomp.index_eq_card, hOcard]
    exact hOodd
  have hQYindex : ¬ 2 ∣ QY.index := hQYindexOdd.not_two_dvd_nat
  let QSyl : Sylow 2 Y := hQYtwo.toSylow hQYindex
  have hQSyl_eq : (QSyl : Subgroup Y) = QY := by
    simp [QSyl, IsPGroup.toSylow_coe hQYtwo hQYindex]
  have hSylowY : ∀ S : Sylow 2 Y, IsMulCommutative (S : Subgroup Y) := by
    intro S
    have hQSylcomm : IsMulCommutative (QSyl : Subgroup Y) := by
      rw [hQSyl_eq]
      exact hQYcomm
    exact isMulCommutative_of_surjective
      (Sylow.equiv S QSyl).symm.toMonoidHom
      (Sylow.equiv S QSyl).symm.surjective hQSylcomm
  have htY : t ∈ Y := (le_sup_right : Q ≤ Y) (Subgroup.mem_zpowers t)
  let tY : Y := ⟨t, htY⟩
  have htYinv : IsInvolution tY := by
    constructor
    · intro htone
      exact ht.1 (congrArg Subtype.val htone)
    · exact Subtype.ext ht.2
  have hCY : C ≤ Y := by
    simpa [C, O] using hcommO.trans le_sup_left
  let CY : Subgroup Y := C.subgroupOf Y
  have hCYp : IsPGroup p CY := by
    exact hCp.of_equiv (Subgroup.subgroupOfEquivOfLe hCY).symm
  have hCentNormC : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer (C : Set X) := by
    simpa [C] using le_normalizer_commutator_of_le_normalizer
      (Subgroup.centralizer ({t} : Set X)) P Q hPinv
        (centralizer_singleton_le_normalizer_zpowers t)
  have hCYinv : Subgroup.centralizer ({tY} : Set Y) ≤
      Subgroup.normalizer (CY : Set Y) := by
    intro y hy
    have hyX : (y : X) ∈ Subgroup.centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      have hzt : z = t := by simpa using hz
      subst z
      have h := hy tY (by simp)
      exact congrArg Subtype.val h
    have hynorm : (y : X) ∈ Subgroup.normalizer (C : Set X) := hCentNormC hyX
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      change (y : X) * (z : X) * (y : X)⁻¹ ∈ C
      exact (Subgroup.mem_normalizer_iff.mp hynorm (z : X)).1 hz
    · intro hz
      change (z : X) ∈ C
      exact (Subgroup.mem_normalizer_iff.mp hynorm (z : X)).2 hz
  have hCYself : ⁅CY, Subgroup.zpowers tY⁆ = CY := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    rw [Subgroup.map_subgroupOf_eq_of_le hCY]
    simpa [tY] using hCself
  have hCYcore : CY ≤ pCore p Y :=
    bender1970_2_4_solvable_oddP_selfCommutator_le_pCore
      (X := Y) (U := CY) (p := p) (t := tY)
      hYsolv hp hpodd hSylowY htYinv hCYp hCYinv hCYself
  have hCYsnCore : (CY.subgroupOf (pCore p Y)).IsSubnormal :=
    isSubnormal_of_isNilpotent (pCore_isNilpotent (p := p) (G := Y))
      (CY.subgroupOf (pCore p Y))
  have hCYsnY : CY.IsSubnormal :=
    Subgroup.IsSubnormal.trans hCYcore hCYsnCore
      (inferInstance : (pCore p Y).Normal).isSubnormal
  have hCYsnOY : (CY.subgroupOf OY).IsSubnormal := hCYsnY.subgroupOf
  let eOY : OY ≃* O :=
    Subgroup.subgroupOfEquivOfLe (show O ≤ Y from le_sup_left)
  have hmapC : (CY.subgroupOf OY).map eOY.toMonoidHom = C.subgroupOf O := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, hzx⟩
      change (z : X) ∈ C at hz
      subst x
      change (z : X) ∈ C
      exact hz
    · intro hx
      let zY : Y := ⟨(x : X), (le_sup_left : O ≤ Y) x.2⟩
      let zOY : OY := ⟨zY, x.2⟩
      have hzCY : zY ∈ CY := by
        change (x : X) ∈ C
        change (x : X) ∈ C at hx
        exact hx
      refine Subgroup.mem_map.mpr ⟨zOY, hzCY, ?_⟩
      apply Subtype.ext
      rfl
  have hCsnO : (C.subgroupOf O).IsSubnormal := by
    rw [← hmapC]
    exact hCYsnOY.map eOY.surjective
  have hCO : C ≤ O := by simpa [C, O] using hcommO
  have hCsnX : C.IsSubnormal :=
    Subgroup.IsSubnormal.trans hCO hCsnO
      (inferInstance : O.Normal).isSubnormal
  have hCtop : (C.subgroupOf (⊤ : Subgroup X)).IsSubnormal := hCsnX.subgroupOf
  have hle : C ≤ qCoreOf (⊤ : Subgroup X) p :=
    le_qCoreOf_of_isSubnormal_isPGroup (⊤ : Subgroup X) C p le_top hCtop hCp
  have hcoreTop : qCoreOf (⊤ : Subgroup X) p = pCore p X := by
    unfold qCoreOf
    change (pCore p (↥(⊤ : Subgroup X))).map
      (Subgroup.topEquiv (G := X)).toMonoidHom = pCore p X
    exact pCore_map_iso p (Subgroup.topEquiv (G := X))
  simpa [C, Q, hcoreTop] using hle

end CFSG.GorensteinWalter
