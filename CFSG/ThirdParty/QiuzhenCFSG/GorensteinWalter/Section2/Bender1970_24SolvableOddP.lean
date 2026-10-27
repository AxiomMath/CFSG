module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_24CoreFreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.theorem_9_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Bender §2.4, solvable odd-`p` branch

This module closes the core-free half of the solvable specialization of
Bender 1970, §2.4: if `O_p(X)=1`, `U` is a `p`-subgroup normalized by the
centralizer of the involution `t`, and `U=[U,⟨t⟩]`, then `U=1`.  The
argument runs through the Fitting normalizer `N_{F(X)}(C_{F(X)}(U))`,
the coprime double-commutator collapse, and the nilpotent normalizer
condition.
-/

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- The `O_p(X)=1` branch of Bender §2.4 / Gagen Lemma 13.4 for a
`p`-subgroup `U` with `[U,⟨t⟩]=U`: `U` is trivial. -/
public theorem bender1970_2_4_coreFree_selfCommutator_eq_bot
    {X : Type u} [Group X] [Finite X]
    (U : Subgroup X) (p : ℕ) {t : X}
    (hsolv : Group.IsSolvable X) (hp : p.Prime)
    (hSylowTwo : ∀ S : Sylow 2 X, IsMulCommutative (S : Subgroup X))
    (ht : IsInvolution t) (hUp : IsPGroup p U)
    (hpcore : pCore p X = ⊥)
    (hUinv : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer (U : Set X))
    (hUcomm : ⁅U, Subgroup.zpowers t⁆ = U) :
    U = ⊥ := by
  classical
  let F : Subgroup X := fittingSubgroup X
  let D : Subgroup X := F ⊓ Subgroup.centralizer (U : Set X)
  let R : Subgroup X := F ⊓ Subgroup.normalizer (D : Set X)
  have hFnil : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  have hFnormal : F.Normal := by
    dsimp [F]
    infer_instance
  have hRleF : R ≤ F := by
    dsimp [R]
    exact inf_le_left
  have hDleF : D ≤ F := by
    dsimp [D]
    exact inf_le_left
  have hRcomm : ⁅R, U⁆ ≤ D := by
    simpa [F, D, R] using
      (bender1970_2_4_coreFree_fittingNormalizer_commutator_le
        (X := X) (U := U) (p := p) (t := t)
        hsolv hp hSylowTwo ht hUp hpcore hUinv hUcomm)
  have hDcentU : D ≤ Subgroup.centralizer (U : Set X) := by
    dsimp [D]
    exact inf_le_right
  have hDU : ⁅D, U⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hDcentU
  have hUnormF : U ≤ Subgroup.normalizer (F : Set X) :=
    Subgroup.le_normalizer_of_normal
  have hUnormCU : U ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set X) : Set X) :=
    U.le_normalizer.trans (normalizer_le_normalizer_centralizer_subgroup U)
  have hUnormD : U ≤ Subgroup.normalizer (D : Set X) := by
    simpa [D] using
      ((le_inf hUnormF hUnormCU).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hUnormR : U ≤ Subgroup.normalizer (R : Set X) := by
    have hUnormND : U ≤
        Subgroup.normalizer (Subgroup.normalizer (D : Set X) : Set X) :=
      hUnormD.trans (Subgroup.normalizer (D : Set X)).le_normalizer
    simpa [R] using
      ((le_inf hUnormF hUnormND).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hUFleCore : U ⊓ F ≤ pCore p X :=
    pSubgroup_inf_normal_nilpotent_le_pCore U F p hp hUp hFnormal hFnil
  have hUFbot : U ⊓ F = ⊥ := by
    apply le_antisymm
    · exact hUFleCore.trans (le_of_eq hpcore)
    · exact bot_le
  have hRcop_p : Nat.Coprime p (Nat.card R) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
    intro hpdvd
    let : Fact p.Prime := ⟨hp⟩
    rcases exists_prime_orderOf_dvd_card' (G := R) p hpdvd with ⟨a, ha_order⟩
    let P : Subgroup X := Subgroup.zpowers ((a : R) : X)
    have hPR : P ≤ R := Subgroup.zpowers_le.2 a.property
    have horderG : orderOf ((a : R) : X) = p := by
      simpa [Subgroup.orderOf_coe] using ha_order
    have hPp : IsPGroup p P := by
      refine IsPGroup.of_card (n := 1) ?_
      simp [P, Nat.card_zpowers, horderG]
    have hPleF : P ≤ F := hPR.trans hRleF
    have hPleCore : P ≤ pCore p X := by
      have hPinf : P ⊓ F = P := inf_eq_left.mpr hPleF
      have h := pSubgroup_inf_normal_nilpotent_le_pCore
        P F p hp hPp hFnormal hFnil
      simpa [hPinf] using h
    have hPbot : P = ⊥ := le_bot_iff.mp (hPleCore.trans (le_of_eq hpcore))
    have ha_ne : (a : X) ≠ 1 := by
      intro ha
      have : p = 1 := by
        calc
          p = orderOf ((a : R) : X) := horderG.symm
          _ = 1 := by rw [ha]; simp
      exact hp.ne_one this
    have hPleBot : P ≤ ⊥ := le_of_eq hPbot
    exact ha_ne (Subgroup.mem_bot.mp (hPleBot (Subgroup.mem_zpowers ((a : R) : X))))
  have hcop : Nat.Coprime (Nat.card R) (Nat.card U) := by
    let : Fact p.Prime := ⟨hp⟩
    refine Nat.coprime_of_dvd ?_
    intro q hqprime hqR hqU
    rcases hUp.exists_card_eq with ⟨n, hn⟩
    have hqpow : q ∣ p ^ n := by
      rw [hn] at hqU
      exact hqU
    have hqp : q = p := Nat.prime_eq_prime_of_dvd_pow hqprime hp hqpow
    have hpdvdR : p ∣ Nat.card R := by simpa [hqp] using hqR
    exact ((Nat.Prime.coprime_iff_not_dvd hp).1 hRcop_p) hpdvdR
  have hdouble : ⁅⁅R, U⁆, U⁆ = ⊥ := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono hRcomm le_rfl).trans (le_of_eq hDU)
    · exact bot_le
  have hRU : ⁅R, U⁆ = ⊥ :=
    commutator_eq_bot_of_coprime_double_commutator_eq_bot (W := R) (R := U)
      hUnormR hcop.symm hdouble
  have hRcentU : R ≤ Subgroup.centralizer (U : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hRU
  have hRleD : R ≤ D := by
    intro x hx
    exact ⟨hRleF hx, hRcentU hx⟩
  have hDleR : D ≤ R := by
    intro x hx
    exact ⟨hDleF hx, D.le_normalizer hx⟩
  have hRD : R = D := le_antisymm hRleD hDleR
  let D' : Subgroup (↥F) := D.subgroupOf F
  have hnorm_eq : (Subgroup.normalizer (D : Set X)).subgroupOf F =
      Subgroup.normalizer (D' : Set (↥F)) :=
    Subgroup.subgroupOf_normalizer_eq hDleF
  have hnormD'_le : Subgroup.normalizer (D' : Set (↥F)) ≤ D' := by
    intro x hx
    have hxN : x ∈ (Subgroup.normalizer (D : Set X)).subgroupOf F := by
      rw [hnorm_eq]
      exact hx
    have hxN' : (x : X) ∈ Subgroup.normalizer (D : Set X) :=
      Subgroup.mem_subgroupOf.mp hxN
    have hxR : (x : X) ∈ R := ⟨x.2, hxN'⟩
    have hxD : (x : X) ∈ D := by rwa [← hRD]
    exact hxD
  have hnormD' : Subgroup.normalizer (D' : Set (↥F)) = D' :=
    le_antisymm hnormD'_le D'.le_normalizer
  let : Group.IsNilpotent (↥F) := hFnil
  have hnc : NormalizerCondition (↥F) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥F)
  have hD'top : D' = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) D' hnormD'
  have hDF : D = F := by
    apply le_antisymm hDleF
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥F) ∈ D' := by
      rw [hD'top]
      trivial
    exact hx'
  have hFcentU : F ≤ Subgroup.centralizer (U : Set X) := by
    rw [← hDF]
    exact hDcentU
  have hUcentF : U ≤ Subgroup.centralizer (F : Set X) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (Subgroup.mem_centralizer_iff.mp (hFcentU hf) u hu).symm
  have hUleF : U ≤ F :=
    hUcentF.trans
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
        (G := X) hsolv)
  have hUleCore : U ≤ pCore p X :=
    (le_inf le_rfl hUleF).trans hUFleCore
  exact le_bot_iff.mp (hUleCore.trans (le_of_eq hpcore))

/-- The solvable odd-`p` specialization of Bender §2.4: quotient by
`O_p(X)`, transfer the hypotheses with the coprime centralizer lemma, and
apply the core-free endpoint. -/
public theorem bender1970_2_4_solvable_oddP_selfCommutator_le_pCore
    {X : Type u} [Group X] [Finite X]
    (U : Subgroup X) (p : ℕ) {t : X}
    (hsolv : Group.IsSolvable X) (hp : p.Prime) (hpodd : Odd p)
    (hSylowTwo : ∀ S : Sylow 2 X, IsMulCommutative (S : Subgroup X))
    (ht : IsInvolution t) (hUp : IsPGroup p U)
    (hUinv : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer (U : Set X))
    (hUcomm : ⁅U, Subgroup.zpowers t⁆ = U) :
    U ≤ pCore p X := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let q : X →* X ⧸ (pCore p X) := QuotientGroup.mk' (pCore p X)
  let Ubar : Subgroup (X ⧸ (pCore p X)) := U.map q
  have hOp : IsPGroup p (pCore p X) :=
    pCore_isPGroup (G := X) (p := p)
  have hOnormal : (pCore p X).Normal := by
    infer_instance
  have hOodd : Odd (Nat.card (pCore p X)) := by
    rcases hOp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hpodd.pow
  have hOcop2 : Nat.Coprime 2 (Nat.card (pCore p X)) := hOodd.coprime_two_left
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htord : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using ht.2) ht.1
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    simp [Nat.card_zpowers, htord]
  let : Fact (IsPGroup 2 (Subgroup.zpowers t)) := ⟨hT2⟩
  have hC1 : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup X) : Set X) =
      Subgroup.centralizer ({t} : Set X) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzt : z = t := by simpa using hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp hx) t (Subgroup.mem_zpowers t)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      have htx : t * x = x * t :=
        Subgroup.mem_centralizer_iff.mp hx t (by simp)
      exact ((show Commute x t from htx.symm).zpow_right n).symm
  have hTmap : (Subgroup.zpowers t).map q = Subgroup.zpowers (q t) :=
    MonoidHom.map_zpowers q t
  have hC2 : Subgroup.centralizer ((Subgroup.zpowers (q t) : Subgroup (X ⧸ (pCore p X))) : Set (X ⧸ (pCore p X))) =
      Subgroup.centralizer ({q t} : Set (X ⧸ (pCore p X))) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzt : z = q t := by simpa using hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp hx) (q t) (Subgroup.mem_zpowers (q t))
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      have htx : (q t) * x = x * (q t) :=
        Subgroup.mem_centralizer_iff.mp hx (q t) (by simp)
      exact ((show Commute x (q t) from htx.symm).zpow_right n).symm
  have hmain' :=
    centralizer_map_quotient_eq_map_centralizer
      (G := X) (p := 2) (T := Subgroup.zpowers t) (M := (pCore p X))
      hOnormal hOcop2
  have hCeq : Subgroup.centralizer ({q t} : Set (X ⧸ (pCore p X))) =
      (Subgroup.centralizer ({t} : Set X)).map q := by
    rw [← hC2, ← hTmap, hmain', hC1]
  have hNormMap : (Subgroup.normalizer (U : Set X)).map q ≤
      Subgroup.normalizer (Ubar : Set (X ⧸ (pCore p X))) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨u, hu, rfl⟩
      have hxu : x * u * x⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp hx u).1 hu
      exact Subgroup.mem_map.mpr ⟨x * u * x⁻¹, hxu, by simp [map_mul, mul_assoc]⟩
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨u, hu, hz⟩
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (U : Set X) :=
        (Subgroup.normalizer (U : Set X)).inv_mem hx
      have hxu : x⁻¹ * u * x ∈ U := by
        simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp hxinv u).1 hu
      have hz' : z = q (x⁻¹ * u * x) := by
        calc
          z = (q x)⁻¹ * (q x * z * (q x)⁻¹) * q x := by group
          _ = (q x)⁻¹ * q u * q x := by rw [hz]
          _ = q (x⁻¹ * u * x) := by simp [map_mul, map_inv, mul_assoc]
      rw [hz']
      exact Subgroup.mem_map.mpr ⟨x⁻¹ * u * x, hxu, rfl⟩
  have hUinvbar : Subgroup.centralizer ({q t} : Set (X ⧸ (pCore p X))) ≤
      Subgroup.normalizer (Ubar : Set (X ⧸ (pCore p X))) := by
    intro y hy
    have hy' : y ∈ (Subgroup.centralizer ({t} : Set X)).map q := by
      rw [hCeq] at hy
      exact hy
    rcases Subgroup.mem_map.mp hy' with ⟨x, hxC, rfl⟩
    have hxN : x ∈ Subgroup.normalizer (U : Set X) := hUinv hxC
    exact hNormMap (Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩)
  have hUpbar : IsPGroup p Ubar := by
    simpa [Ubar] using (IsPGroup.map hUp q)
  have hUcommbar : ⁅Ubar, Subgroup.zpowers (q t)⁆ = Ubar := by
    have hmapComm : (⁅U, Subgroup.zpowers t⁆).map q =
        ⁅Ubar, Subgroup.zpowers (q t)⁆ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    rw [← hmapComm, hUcomm]
  have hsolvbar : Group.IsSolvable (X ⧸ (pCore p X)) := by
    let : Group.IsSolvable X := hsolv
    exact Group.isSolvable_of_surjective
      (f := QuotientGroup.mk' (pCore p X))
      (QuotientGroup.mk'_surjective (pCore p X))
  have hSylowBar : ∀ S : Sylow 2 (X ⧸ (pCore p X)),
      IsMulCommutative (S : Subgroup (X ⧸ (pCore p X))) := by
    intro Sbar
    have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective (pCore p X)
    rcases (Sylow.mapSurjective_surjective (p := 2) (f := q) hqsurj Sbar) with ⟨S, hS⟩
    have hSm : (S : Subgroup X).map q = (Sbar : Subgroup (X ⧸ (pCore p X))) := by
      rw [← Sylow.coe_mapSurjective hqsurj S]
      exact congrArg (fun X0 : Sylow 2 (X ⧸ (pCore p X)) => (X0 : Subgroup (X ⧸ (pCore p X)))) hS
    have hScomm : IsMulCommutative (S : Subgroup X) := hSylowTwo S
    rw [← hSm]
    exact isMulCommutative_map_of_surjective q hqsurj S hScomm
  have htbar : IsInvolution (q t) := by
    constructor
    · intro hq
      have htO : t ∈ (pCore p X) := (QuotientGroup.eq_one_iff (N := (pCore p X)) (x := t)).1 hq
      have h2dvd : 2 ∣ Nat.card (pCore p X) := htord ▸ (Subgroup.orderOf_dvd_natCard (pCore p X) htO)
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hOcop2) h2dvd
    · simpa [pow_two, map_mul] using congrArg q ht.2
  have hOmap : (pCore p X).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (H := (pCore p X)) (f := q)).2
    intro x hx
    exact (QuotientGroup.eq_one_iff (N := (pCore p X)) (x := x)).2 hx
  have hcorebar : pCore p (X ⧸ (pCore p X)) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup (G := X) (p := p) (H := (pCore p X)) hOp]
    exact hOmap
  have hUbot : Ubar = ⊥ :=
    bender1970_2_4_coreFree_selfCommutator_eq_bot
      (X := X ⧸ (pCore p X)) (U := Ubar) (p := p) (t := q t)
      hsolvbar hp hSylowBar htbar hUpbar hcorebar hUinvbar hUcommbar
  have hUleKer : U ≤ q.ker := by
    have hmap_bot : U.map q = ⊥ := by simpa [Ubar] using hUbot
    exact (Subgroup.map_eq_bot_iff (H := U) (f := q)).1 hmap_bot
  intro x hx
  have hxO : x ∈ (pCore p X) :=
    (QuotientGroup.eq_one_iff (N := (pCore p X)) (x := x)).1 (hUleKer hx)
  exact hxO

end CFSG.GorensteinWalter
