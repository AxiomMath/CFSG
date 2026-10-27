module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The non-two-group content of a D-group quotient

Each model occurring in `IsDGroupQuotient` has odd-order elements: `A₇` has
order divisible by three, while `PSL₂(K)` and `PGL₂(K)` contain the upper
unipotent subgroup of odd prime-power order.  Consequently the quotient by
the odd core cannot be a two-group.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- An odd-prime-power `PSL₂(K)` is not a `2`-group. -/
public theorem not_isPGroup_two_of_psl2_odd
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    ¬ IsPGroup 2 (PSL2 K) := by
  rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  intro htwo
  have hUtwo : IsPGroup 2 (psl2UpperUnipotentSubgroup K) :=
    htwo.to_subgroup (psl2UpperUnipotentSubgroup K)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hUtwo
  rw [psl2UpperUnipotentSubgroup_card, hcard] at hm
  have hpdiv : p ∣ p ^ n := dvd_pow_self p (by omega)
  have hpdivtwoPow : p ∣ 2 ^ m := by
    rw [← hm]
    exact hpdiv
  have hpdivtwo : p ∣ 2 := hp.dvd_of_dvd_pow hpdivtwoPow
  rcases (Nat.dvd_prime Nat.prime_two).mp hpdivtwo with hpone | hptwo
  · exact hp.ne_one hpone
  · subst p
    norm_num at hpodd

/-- An odd-prime-power `PGL₂(K)` is not a `2`-group. -/
public theorem not_isPGroup_two_of_pgl2_odd
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    ¬ IsPGroup 2 (PGL2 K) := by
  intro htwo
  let R : Subgroup (PGL2 K) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range
  have hRtwo : IsPGroup 2 R := htwo.to_subgroup R
  have hPSLtwo : IsPGroup 2 (PSL2 K) :=
    hRtwo.of_equiv (psl2EquivToPGLRange K).symm
  exact not_isPGroup_two_of_psl2_odd K hK hPSLtwo

/-- The quotient clause of a `D`-group is incompatible with the quotient by
the odd core being a two-group. -/
public theorem not_isPGroup_quotient_pPrimeCore_of_isDGroupQuotient
    {G : Type u} [Group G] [Finite G]
    (hD : IsDGroupQuotient G) :
    ¬ IsPGroup 2 (G ⧸ pPrimeCore 2 G) := by
  have hPSL := not_isPGroup_two_of_psl2_odd
  have hPGL := not_isPGroup_two_of_pgl2_odd
  have hA7 : ¬ IsPGroup 2 (alternatingGroup (Fin 7)) := by
    intro htwo
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp htwo
    have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have hthree : 3 ∣ 2 ^ n := by
      rw [← hn, hcard]
      norm_num
    have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
    norm_num at this
  intro htwo
  rcases hD with hA7model | ⟨L, _hLnormal, _hLindex, hLmodel⟩
  · exact hA7 (htwo.of_equiv hA7model.some)
  · have hLtwo : IsPGroup 2 L := htwo.to_subgroup L
    rcases hLmodel with hPSLmodel | hPGLmodel
    · rcases hPSLmodel with ⟨K, instK, finK, hK⟩
      let : Field K := instK
      let : Finite K := finK
      exact hPSL K hK.1 (hLtwo.of_equiv hK.2.some)
    · rcases hPGLmodel with ⟨K, instK, finK, hK⟩
      let : Field K := instK
      let : Finite K := finK
      exact hPGL K hK.1 (hLtwo.of_equiv hK.2.some)

/-- The `2`-core of a group isomorphic to odd `PSL₂(K)` is trivial for
`|K| > 3`. -/
public theorem pCore_two_eq_bot_of_mulEquiv_psl2_odd
    {G : Type u} [Group G] [Finite G]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : G ≃* PSL2 K) :
    pCore 2 G = ⊥ := by
  classical
  let T : Subgroup G := pCore 2 G
  have hTnorm : T.Normal := pCore_normal
  let T' : Subgroup (PSL2 K) := T.map e.toMonoidHom
  have hT'normal : T'.Normal :=
    Subgroup.Normal.map hTnorm e.toMonoidHom e.surjective
  have hsimple : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hT'bot : T' = ⊥ := by
    rcases hT'normal.eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · exfalso
      have hTp : IsPGroup 2 T := pCore_isPGroup
      have hT'p : IsPGroup 2 T' := IsPGroup.map hTp e.toMonoidHom
      have hwhole : IsPGroup 2 (PSL2 K) := by
        rw [htop] at hT'p
        exact hT'p.of_equiv (Subgroup.topEquiv (G := PSL2 K))
      exact not_isPGroup_two_of_psl2_odd K hK hwhole
  have hTleKer : T ≤ e.toMonoidHom.ker :=
    (Subgroup.map_eq_bot_iff T).mp (by simpa [T'] using hT'bot)
  have hker : e.toMonoidHom.ker = ⊥ :=
    MonoidHom.ker_eq_bot e.toMonoidHom e.injective
  exact le_bot_iff.mp (hTleKer.trans (le_of_eq hker))

/-- The `2`-core of a group isomorphic to odd `PGL₂(K)` is trivial for
`|K| > 3`. -/
public theorem pCore_two_eq_bot_of_mulEquiv_pgl2_odd
    {G : Type u} [Group G] [Finite G]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : G ≃* PGL2 K) :
    pCore 2 G = ⊥ := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let T : Subgroup G := pCore 2 G
  have hTnorm : T.Normal := pCore_normal
  let T' : Subgroup (PGL2 K) := T.map e.toMonoidHom
  have hT'normal : T'.Normal :=
    Subgroup.Normal.map hTnorm e.toMonoidHom e.surjective
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hJnormal : J.Normal := by infer_instance
  have hJpsl : Nonempty (commutator (PGL2 K) ≃* PSL2 K) :=
    commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      K hK hcard (MulEquiv.refl (PGL2 K))
  let hJsimple : IsSimpleGroup J :=
    (MulEquiv.isSimpleGroup_congr hJpsl.some).mpr
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
  have hJeq : J =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  let I : Subgroup J := (T' ⊓ J).subgroupOf J
  have hI_norm : I.Normal := by
    refine { conj_mem := ?_ }
    intro x hx g
    have hxT' : (x : PGL2 K) ∈ T' := hx.1
    have hxJ : (x : PGL2 K) ∈ J := x.2
    exact ⟨hT'normal.conj_mem (x : PGL2 K) hxT' (g : PGL2 K),
      hJnormal.conj_mem (x : PGL2 K) hxJ (g : PGL2 K)⟩
  have hIcases : I = ⊥ ∨ I = ⊤ := hI_norm.eq_bot_or_eq_top
  have hT'Jbot : T' ⊓ J = ⊥ := by
    rcases hIcases with hIbot | hItop
    · apply le_bot_iff.mp
      intro x hx
      have hxJ : x ∈ J := hx.2
      have hxI : (⟨x, hxJ⟩ : J) ∈ I := hx
      have hxI1 : (⟨x, hxJ⟩ : J) = 1 :=
        Subgroup.mem_bot.mp (by simpa [hIbot] using hxI)
      exact congrArg Subtype.val hxI1
    · exfalso
      have hT'2 : IsPGroup 2 T' := IsPGroup.map (pCore_isPGroup (G := G)) e.toMonoidHom
      have hJleT' : J ≤ T' := by
        intro x hxJ
        have hxI : (⟨x, hxJ⟩ : J) ∈ I := by
          rw [hItop]
          trivial
        have hxT'J : x ∈ T' ⊓ J := (Subgroup.mem_subgroupOf).mp hxI
        exact hxT'J.1
      let JT' : Subgroup T' := J.subgroupOf T'
      have hJT'2 : IsPGroup 2 JT' := hT'2.to_subgroup JT'
      have hJ2 : IsPGroup 2 J :=
        hJT'2.of_equiv (Subgroup.subgroupOfEquivOfLe hJleT')
      let eJ : J ≃* PSL2 K := hJpsl.some
      have hP2 : IsPGroup 2 (PSL2 K) := hJ2.of_equiv eJ
      exact not_isPGroup_two_of_psl2_odd K hK hP2
  let : T'.Normal := hT'normal
  let : J.Normal := hJnormal
  have hcomm_le : ⁅T', J⁆ ≤ T' ⊓ J := Subgroup.commutator_le_inf T' J
  have hcomm_bot : ⁅T', J⁆ = ⊥ :=
    le_bot_iff.mp (hcomm_le.trans (le_of_eq hT'Jbot))
  have hTC : T' ≤ Subgroup.centralizer (J : Set (PGL2 K)) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := T') (H₂ := J)).1 hcomm_bot
  have hCent : Subgroup.centralizer (J : Set (PGL2 K)) = ⊥ := by
    rw [hJeq]
    exact pgl2_psl2Range_centralizer_eq_bot K hK
  have hT'bot : T' = ⊥ := le_bot_iff.mp (hTC.trans (le_of_eq hCent))
  have hTleKer : T ≤ e.toMonoidHom.ker :=
    (Subgroup.map_eq_bot_iff T).mp (by simpa [T'] using hT'bot)
  have hker : e.toMonoidHom.ker = ⊥ :=
    MonoidHom.ker_eq_bot e.toMonoidHom e.injective
  exact le_bot_iff.mp (hTleKer.trans (le_of_eq hker))

/-- A `2`-subgroup is contained in a normal subgroup of odd index. -/
public theorem subgroup_le_of_isPGroup_coindex_odd
    {H : Type u} [Group H] [Finite H]
    (L : Subgroup H) (hLnorm : L.Normal) (hLindex : Odd L.index)
    (K : Subgroup H) (hKp : IsPGroup 2 K) :
    K ≤ L := by
  let : L.Normal := hLnorm
  let π : H →* H ⧸ L := QuotientGroup.mk' L
  have hQodd : Odd (Nat.card (H ⧸ L)) := by
    rw [← L.index_eq_card]
    exact hLindex
  intro x hx
  have hx2 : orderOf x ∣ Nat.card ↥K :=
    Subgroup.orderOf_dvd_natCard K hx
  have hmap : orderOf (π x) ∣ orderOf x := orderOf_map_dvd π x
  have hdivq : orderOf (π x) ∣ Nat.card (H ⧸ L) :=
    orderOf_dvd_natCard (π x)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hKp
  have hcop2 : Nat.Coprime 2 (Nat.card (H ⧸ L)) :=
    Nat.coprime_two_left.mpr hQodd
  have hcopPow : Nat.Coprime (2 ^ n) (Nat.card (H ⧸ L)) :=
    hcop2.pow_left n
  have hkdiv : orderOf (π x) ∣ 2 ^ n :=
    hmap.trans (by rw [hn] at hx2; exact hx2)
  have hord1 : orderOf (π x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopPow hkdiv hdivq
  have hq1 : π x = 1 := orderOf_eq_one_iff.mp hord1
  exact (QuotientGroup.eq_one_iff (N := L) x).mp hq1

/-- If `A / O₂'(A)` has a normal odd-index subgroup isomorphic to
`PSL₂(K)` or `PGL₂(K)` with `|K| > 3`, then the `2`-core of `A` is
trivial. -/
public theorem pCore_two_eq_bot_of_linear_quotient_large
    {A : Type u} [Group A] [Finite A]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (L : Subgroup (A ⧸ pPrimeCore 2 A))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (hLmodel : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) :
    pCore 2 A = ⊥ := by
  classical
  let O : Subgroup A := pPrimeCore 2 A
  let : O.Normal := by dsimp [O]; infer_instance
  let Q : Type u := A ⧸ O
  let q : A →* Q := QuotientGroup.mk' O
  let T : Subgroup A := pCore 2 A
  have hTnorm : T.Normal := pCore_normal
  let TQ : Subgroup Q := T.map q
  have hTQnorm : TQ.Normal :=
    Subgroup.Normal.map hTnorm q (QuotientGroup.mk'_surjective O)
  have hTp : IsPGroup 2 T := pCore_isPGroup
  have hTQp : IsPGroup 2 TQ := IsPGroup.map hTp q
  let : L.Normal := hLnormal
  have hTQleL : TQ ≤ L :=
    subgroup_le_of_isPGroup_coindex_odd L hLnormal hLindex TQ hTQp
  let TL : Subgroup (↥L) := TQ.subgroupOf L
  have hTLp : IsPGroup 2 TL :=
    hTQp.of_equiv (Subgroup.subgroupOfEquivOfLe hTQleL).symm
  have hTLnorm : TL.Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := TQ) ?_
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hTQnorm.conj_mem x hx (l : Q)
    · intro hx
      have hx' := hTQnorm.conj_mem ((l : Q) * x * (l : Q)⁻¹) hx ((l : Q)⁻¹)
      have hEq : (l : Q)⁻¹ * ((l : Q) * x * (l : Q)⁻¹) * ((l : Q)⁻¹)⁻¹ = x := by group
      simpa [hEq] using hx'
  have hTLleP : TL ≤ pCore 2 (↥L) := le_sSup ⟨inferInstance, hTLp⟩
  have hLcore : pCore 2 (↥L) = ⊥ := by
    rcases hLmodel with hpsl | hpgl
    · exact pCore_two_eq_bot_of_mulEquiv_psl2_odd K hK hcard hpsl.some
    · exact pCore_two_eq_bot_of_mulEquiv_pgl2_odd K hK hcard hpgl.some
  have hTLbot : TL = ⊥ := le_bot_iff.mp (hTLleP.trans (le_of_eq hLcore))
  have hTQbot : TQ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxL : x ∈ L := hTQleL hx
    have hxTL : (⟨x, hxL⟩ : ↥L) ∈ TL := hx
    have hx1 : (⟨x, hxL⟩ : ↥L) = 1 :=
      Subgroup.mem_bot.mp (by simpa [hTLbot] using hxTL)
    exact congrArg Subtype.val hx1
  have hTleKer : T ≤ q.ker :=
    (Subgroup.map_eq_bot_iff T).mp (by simpa [TQ] using hTQbot)
  have hker : q.ker = O := QuotientGroup.ker_mk' O
  have hTleO : T ≤ O := by simpa [hker] using hTleKer
  have hOodd : Odd (Nat.card ↥O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := A))
  have hTodd : Odd (Nat.card ↥T) :=
    Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hTleO)
  have hTcard1 : Nat.card ↥T = 1 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hTp
    have hn0 : n = 0 := by
      by_contra hn0'
      have h2dvd : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0'
      rw [← hn] at h2dvd
      exact hTodd.not_two_dvd_nat h2dvd
    rw [hn, hn0]
    norm_num
  exact (Subgroup.eq_bot_of_card_eq T hTcard1)

/-- If an element of an odd-index normal subgroup inverts every element of
an odd-order subgroup, then that subgroup is contained in the normal
subgroup after passing to the quotient. -/
public theorem subgroup_map_le_of_inverted_against_normal_odd_index
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (L : Subgroup H) (hLnorm : L.Normal)
    (hLindex : Odd L.index) (P : Subgroup G)
    (hPodd : Odd (Nat.card ↥P))
    (t : G) (htL : f t ∈ L)
    (htinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) :
    P.map f ≤ L := by
  let : L.Normal := hLnorm
  let π : H →* H ⧸ L := QuotientGroup.mk' L
  have hQodd : Odd (Nat.card (H ⧸ L)) := by
    rw [← L.index_eq_card]
    exact hLindex
  intro y hy
  rcases hy with ⟨x, hxP, rfl⟩
  by_contra hyL
  have hxord : orderOf x ∣ Nat.card ↥P :=
    Subgroup.orderOf_dvd_natCard P hxP
  have hfxodd : Odd (orderOf (f x)) :=
    Odd.of_dvd_nat hPodd ((orderOf_map_dvd f x).trans hxord)
  have hft : π (f t) = 1 :=
    (QuotientGroup.eq_one_iff (N := L) (f t)).2 htL
  have hinv_map : f t * f x * (f t)⁻¹ = (f x)⁻¹ := by
    simpa [map_mul, MonoidHom.map_inv] using congrArg f (htinv x hxP)
  have hpi'_conj : π (f t) * π (f x) * (π (f t))⁻¹ = (π (f x))⁻¹ := by
    simpa [map_mul, MonoidHom.map_inv] using congrArg π hinv_map
  have hpi'_inv : π (f x) = (π (f x))⁻¹ := by
    simpa [hft] using hpi'_conj
  have h2 : π (f x) * π (f x) = 1 := by
    calc
      π (f x) * π (f x) = π (f x) * (π (f x))⁻¹ := by rw [← hpi'_inv]
      _ = 1 := by simp
  have horder2 : orderOf (π (f x)) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h2)
  have horderQ : orderOf (π (f x)) ∣ Nat.card (H ⧸ L) :=
    orderOf_dvd_natCard (π (f x))
  have hcop : Nat.Coprime 2 (Nat.card (H ⧸ L)) :=
    Nat.coprime_two_left.mpr hQodd
  have hord1 : orderOf (π (f x)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horder2 horderQ
  have hπ1 : π (f x) = 1 := orderOf_eq_one_iff.mp hord1
  exact hyL ((QuotientGroup.eq_one_iff (N := L) (f x)).1 hπ1)

end CFSG.GorensteinWalter
