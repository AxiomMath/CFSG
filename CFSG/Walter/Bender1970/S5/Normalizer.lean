module

public import CFSG.Walter.Bender1970.S5.Solvable
public import CFSG.Walter.Transitivity
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem componentLayerOf_eq_bot_of_isSolvable {X : Subgroup G} (hX : Group.IsSolvable X) :
    componentLayerOf X = ⊥ := by
  refine le_bot_iff.mp (sSup_le fun K hK => ?_)
  have := isPerfect_of_isComponentOf hK
  exact absurd (eq_bot_of_isPerfect_of_le_isSolvable hK.1 hX) (ne_bot_of_isComponentOf hK)

theorem le_oddCoreOf_of_isSolvable {M D : Subgroup G} (hMs : Group.IsSolvable M)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hTab : IsMulCommutative (T : Subgroup G))
    (hDM : D ≤ M) (hTD : (T : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hD : Odd (Nat.card D)) : D ≤ oddCoreOf M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pPrimeCore 2 M with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set T' : Sylow 2 M := T.subtype hTM with hT'
  set Tb : Subgroup (M ⧸ Q) := (T' : Subgroup M).map π with hTb
  set Db : Subgroup (M ⧸ Q) := (D.subgroupOf M).map π with hDb
  set F := generalizedFittingSubgroupOf (⊤ : Subgroup (M ⧸ Q)) with hF
  have hMbs : Group.IsSolvable (M ⧸ Q) := Group.isSolvable_of_surjective hπs
  have hEb : componentLayerOf (⊤ : Subgroup (M ⧸ Q)) = ⊥ := by
    have : Group.IsSolvable (⊤ : Subgroup (M ⧸ Q)) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact componentLayerOf_eq_bot_of_isSolvable this
  have hFT : F ≤ Tb := by
    rw [hF, generalizedFittingSubgroupOf, hEb, sup_bot_eq]
    have hn : (CFSG.fittingSubgroupOf (⊤ : Subgroup (M ⧸ Q))).Normal :=
      normal_of_isNormalIn_top' (fittingSubgroupOf_isNormalIn ⊤)
    have hp : IsPGroup 2 (CFSG.fittingSubgroupOf (⊤ : Subgroup (M ⧸ Q))) :=
      CFSG.isPGroup_of_nilpotent_normal _ hn (CFSG.fittingSubgroupOf_isNilpotent _)
        (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    have h := hp.le_sylow_of_normal (T'.mapSurjective hπs)
    rwa [Sylow.coe_mapSurjective] at h
  have hTbc : ∀ x ∈ Tb, ∀ y ∈ Tb, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have hx' : (x : G) ∈ (T : Subgroup G) := hx
    have hy' : (y : G) ∈ (T : Subgroup G) := hy
    exact Subtype.ext (show (x : G) * y = y * x from
      congrArg Subtype.val (hTab.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩))
  have hTF : Tb ≤ F := fun x hx => Bender35.inf_centralizer_le_generalizedFitting ⊤
    ⟨trivial, Subgroup.mem_centralizer_iff.mpr fun y hy => (hTbc x hx y (hFT hy)).symm⟩
  have hTbp : IsPGroup 2 Tb := T'.isPGroup'.map π
  have hDbodd : ∀ x ∈ Db, Odd (orderOf x) := by
    rintro _ ⟨d, hd, rfl⟩
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd π d)
    have h1 : orderOf d ∣ Nat.card (D.subgroupOf M) := by
      have := orderOf_dvd_natCard (⟨d, hd⟩ : D.subgroupOf M)
      rwa [Subgroup.orderOf_mk] at this
    rw [natCard_subgroupOf_of_le hDM] at h1
    exact Odd.of_dvd_nat hD h1
  have hinter : ∀ x ∈ Db, x ∈ Tb → x = 1 := by
    intro x hxD hxT
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTbp) ⟨x, hxT⟩
    rw [Subgroup.orderOf_mk] at hk
    have h1 := hDbodd x hxD
    rw [hk] at h1
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exact absurd h1 (Nat.not_odd_iff_even.mpr ((Nat.even_pow' hk0.ne').mpr even_two))
  have hTbD : ∀ y ∈ Tb, ∀ d ∈ Db, y * d * y⁻¹ ∈ Db := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨d, hd, rfl⟩
    refine ⟨y * d * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hy' : (y : G) ∈ (T : Subgroup G) := hy
    have hd' : (d : G) ∈ D := hd
    show ((y * d * y⁻¹ : M) : G) ∈ D
    exact (Subgroup.mem_normalizer_iff.mp (hTD hy') d).mp hd'
  have hFn := generalizedFittingSubgroupOf_isNormalIn (⊤ : Subgroup (M ⧸ Q))
  have hcomm : ∀ d ∈ Db, ∀ y ∈ Tb, d * y = y * d := by
    intro d hd y hy
    have hc : d * y * d⁻¹ * y⁻¹ = 1 := by
      refine hinter _ ?_ ?_
      · have : d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) := by group
        rw [this]
        exact Db.mul_mem hd (hTbD y hy d⁻¹ (Db.inv_mem hd))
      · exact Tb.mul_mem (hFT (hFn.2 d trivial y (hTF hy))) (Tb.inv_mem hy)
    calc d * y = d * y * d⁻¹ * y⁻¹ * (y * d) := by group
      _ = y * d := by rw [hc, one_mul]
  have hDF : Db ≤ F := fun d hd => Bender35.inf_centralizer_le_generalizedFitting ⊤
    ⟨trivial, Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm d hd y (hFT hy)).symm⟩
  intro x hx
  have h1 : π ⟨x, hDM hx⟩ = 1 :=
    hinter _ ⟨⟨x, hDM hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      (hFT (hDF ⟨⟨x, hDM hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩))
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨x, hDM hx⟩, h1, rfl⟩

theorem oddCoreOf_le_centralizer_of_le {X : Subgroup G} {t : G} (htX : t ∈ X)
    (ht : orderOf t = 2)
    (hF : CFSG.fittingSubgroupOf X ≤ Subgroup.centralizer ({t} : Set G)) :
    oddCoreOf X ≤ Subgroup.centralizer ({t} : Set G) := by
  classical
  set Y := oddCoreOf X with hYdef
  set U := Subgroup.zpowers t with hU
  have hYn : IsNormalIn Y X := oddCoreOf_isNormalIn' X
  have hYodd : Odd (Nat.card Y) := odd_card_oddCoreOf X
  have hYs : Group.IsSolvable Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hYodd
  have hFY : CFSG.fittingSubgroupOf Y ≤ CFSG.fittingSubgroupOf X :=
    fittingSubgroupOf_le_of_isSubnormal hYn.1 (isSubnormal_subgroupOf_of_isNormalIn hYn)
  have hUF : U ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf Y : Set G) := by
    rw [hU, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro f hf
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hF (hFY hf)))
  have hUY : U ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_of_isNormalIn hYn htX)
  have hcop : Nat.Coprime (Nat.card U) (Nat.card Y) := by
    rw [hU, Nat.card_zpowers, ht]
    exact Nat.coprime_two_left.mpr hYodd
  have hFYn : IsNormalIn (CFSG.fittingSubgroupOf Y) Y := fittingSubgroupOf_isNormalIn Y
  have hcomm : ⁅Y, U⁆ ≤ CFSG.fittingSubgroupOf Y := by
    have h1 : ⁅Y, U⁆ ≤ Y ⊓ Subgroup.centralizer (CFSG.fittingSubgroupOf Y : Set G) := by
      rw [Subgroup.commutator_le]
      intro y hy u hu
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def, show y * u * y⁻¹ * u⁻¹ = y * (u * y⁻¹ * u⁻¹) by group]
        exact Y.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hUY hu) y⁻¹).mp (Y.inv_mem hy))
      · show ⁅y, u⁆ ∈ Subgroup.centralizer (CFSG.fittingSubgroupOf Y : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        have hf' : y⁻¹ * f * y ∈ CFSG.fittingSubgroupOf Y := by
          have := hFYn.2 y⁻¹ (Y.inv_mem hy) f hf
          rwa [inv_inv] at this
        have huf : u * f = f * u := ((Subgroup.mem_centralizer_iff.mp (hUF hu)) f hf).symm
        have huf' : u * (y⁻¹ * f * y) = (y⁻¹ * f * y) * u :=
          ((Subgroup.mem_centralizer_iff.mp (hUF hu)) _ hf').symm
        have hk1 : u⁻¹ * f = f * u⁻¹ := (Commute.inv_left (show Commute u f from huf)).eq
        rw [commutatorElement_def]
        calc f * (y * u * y⁻¹ * u⁻¹) = y * ((y⁻¹ * f * y) * u) * y⁻¹ * u⁻¹ := by group
          _ = y * (u * (y⁻¹ * f * y)) * y⁻¹ * u⁻¹ := by rw [huf']
          _ = y * u * y⁻¹ * (f * u⁻¹) := by group
          _ = y * u * y⁻¹ * (u⁻¹ * f) := by rw [hk1]
          _ = y * u * y⁻¹ * u⁻¹ * f := by group
    have h2 : Y ⊓ Subgroup.centralizer (CFSG.fittingSubgroupOf Y : Set G) ≤
        CFSG.fittingSubgroupOf Y := by
      intro x hx
      have hx' : x ∈ Y ⊓ Subgroup.centralizer (generalizedFittingSubgroupOf Y : Set G) := by
        refine ⟨hx.1, ?_⟩
        rw [generalizedFittingSubgroupOf, componentLayerOf_eq_bot_of_isSolvable hYs, sup_bot_eq]
        exact hx.2
      have := Bender35.inf_centralizer_le_generalizedFitting Y hx'
      rwa [generalizedFittingSubgroupOf, componentLayerOf_eq_bot_of_isSolvable hYs,
        sup_bot_eq] at this
    exact h1.trans h2
  have hUY' := le_centralizer_of_le_centralizer_commutator hUY hcop
    (Subgroup.le_centralizer_iff.mp (hcomm.trans (Subgroup.le_centralizer_iff.mp hUF)))
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (hUY' (Subgroup.mem_zpowers t))) y hy

namespace Bender52

variable (hG : BenderCounterexample G)
include hG

theorem isSolvable_centralizer
    {s : G} (hs : orderOf s = 2) :
    Group.IsSolvable (Subgroup.centralizer ({s} : Set G)) := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    omega
  obtain ⟨M, hM⟩ := hG.benderM_nonempty hs1
  have := bender1970_5_1 hG hs hM
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (centralizer_le_of_mem_benderM hM)) (Subgroup.inclusion_injective _)

theorem mem_qCoreOf_two
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) :
    t ∈ qCoreOf H 2 := by
  have hHs := bender1970_5_1 hG ht hH
  have hF := bender1970_4_1 hG ht hH
  rw [generalizedFittingSubgroupOf, componentLayerOf_eq_bot_of_isSolvable hHs, sup_bot_eq] at hF
  obtain ⟨t', ht', rfl⟩ := hF
  have h2 : (H.subtype t') ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one _
  refine ⟨t', mem_pCore_of_mem_normal_nilpotent Nat.prime_two inferInstance inferInstance ht'
    (k := 1) ?_, rfl⟩
  rw [pow_one]
  exact Subtype.ext h2

theorem le_of_isPGroup
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hOp : qCoreOf H p ≠ ⊥) {Q : Subgroup G} (hQp : IsPGroup p Q)
    (hTQ : (T : Subgroup G) ≤ Subgroup.normalizer (Q : Set G)) : Q ≤ H := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hHco := isCoatom_of_mem_benderM hH
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have htO := mem_qCoreOf_two hG ht hH
  set p' : Nat.Primes := ⟨p, hp⟩ with hp'
  set ℱ := section7HFamily (⊤ : Subgroup G) (T : Subgroup G) ({p'} : Set Nat.Primes) with hℱ
  have hmemℱ : ∀ {R : Subgroup G}, IsPGroup p R →
      (T : Subgroup G) ≤ Subgroup.normalizer (R : Set G) → R ∈ ℱ := by
    intro R hR hTR
    refine ⟨le_top, fun q hq => ?_, hTR⟩
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn] at hq
    exact Set.mem_singleton_iff.mpr
      (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 hp).mp (q.2.dvd_of_dvd_pow hq)))
  have hpg : ∀ R ∈ ℱ, IsPGroup p R := by
    intro R hR
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      fun {d} hd hdR => ?_)
    have h1 : (⟨d, hd⟩ : Nat.Primes) = p' := hR.2.1 ⟨d, hd⟩ hdR
    exact congrArg Subtype.val h1
  have hmax : ∀ R ∈ ℱ, ∃ P ∈ section7HStarFamily (⊤ : Subgroup G) (T : Subgroup G)
      ({p'} : Set Nat.Primes), R ≤ P := by
    intro R hR
    obtain ⟨P, ⟨hPℱ, hRP⟩, hPmax⟩ := Set.exists_max_image {P | P ∈ ℱ ∧ R ≤ P}
      (fun P => Nat.card P) (Set.toFinite _) ⟨R, hR, le_rfl⟩
    exact ⟨P, ⟨hPℱ, fun S hPS hS =>
      (Subgroup.eq_of_le_of_card_ge hPS (hPmax S ⟨hS, hRP.trans hPS⟩)).symm⟩, hRP⟩
  obtain ⟨P, hP, hOP⟩ := hmax (qCoreOf H p) (hmemℱ (qCoreOf_isPGroup H p)
    (hTH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p))))
  have hPp := hpg P hP.1
  have hTP : (T : Subgroup G) ≤ Subgroup.normalizer (P : Set G) := hP.1.2.2
  have hNO : Subgroup.normalizer (qCoreOf H p : Set G) = H :=
    hG.normalizer_eq_of_isNormalIn hHco (qCoreOf_normal_in H p) hOp
  have hCPH : Subgroup.centralizer ((P ⊓ H : Subgroup G) : Set G) ≤ H :=
    (Subgroup.centralizer_le (le_inf hOP (qCoreOf_normal_in H p).1)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNO.le)
  have htPH : ⁅P ⊓ H, Subgroup.zpowers t⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq']
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc1 : t * x * t⁻¹ * x⁻¹ ∈ qCoreOf H 2 := by
      rw [show t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) by group]
      exact (qCoreOf H 2).mul_mem htO ((qCoreOf_normal_in H 2).2 x hx.2 t⁻¹ (inv_mem htO))
    have hc2 : t * x * t⁻¹ * x⁻¹ ∈ P :=
      P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTP htT) x).mp hx.1) (P.inv_mem hx.1)
    have hc := eq_one_of_isPGroup_two_of_isPGroup hp hp2 (qCoreOf_isPGroup H 2) hPp hc1 hc2
    calc x * t = (t * x * t⁻¹ * x⁻¹)⁻¹ * (t * x) := by group
      _ = t * x := by rw [hc, inv_one, one_mul]
  have hcop : Nat.Coprime p (orderOf t) := by
    rw [ht]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hT1 := bender1970_1_1_thompson p hp (P ⊓ H) (Subgroup.zpowers t) P
    (hPp.to_le inf_le_left) hPp (Bender35.pResidualOf_zpowers_eq hp hcop)
    (inf_le_left.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr (hTP htT)) htPH
    (le_bot_iff.mp ((Subgroup.commutator_mono (le_inf inf_le_left (inf_le_right.trans hCPH))
      le_rfl).trans htPH.le))
  have hPH : P ≤ H := by
    intro x hx
    apply centralizer_le_of_mem_benderM hH
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hT1 (Subgroup.mem_zpowers t))) x hx
  have htrans := thompson_transitivity T (hG.hasAbelianSylowTwo T) (hG.three_le_rank_sylow T)
    (fun s hs => isSolvable_centralizer hG hs) (q := p') hp2
  obtain ⟨Q', hQ', hQQ'⟩ := hmax Q (hmemℱ hQp hTQ)
  obtain ⟨c, hc⟩ := htrans P hP Q' hQ'
  have hcH : (c : G) ∈ H := centralizer_le_of_mem_benderM hH
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htT) c.2)
  intro x hx
  have hxQ' := hQQ' hx
  rw [hc] at hxQ'
  obtain ⟨y, hy, hyx⟩ := hxQ'
  rw [← hyx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact H.mul_mem (H.mul_mem hcH (hPH hy)) (H.inv_mem hcH)

end Bender52

theorem bender1970_5_2
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) :
    Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTab := hG.hasAbelianSylowTwo T
  have hTc : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hHco := isCoatom_of_mem_benderM hH
  have hHA := hG.isAStar_of_isCoatom hHco
  have hHs := bender1970_5_1 hG ht hH
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hE := componentLayerOf_eq_bot_of_isSolvable hHs
  have htO := Bender52.mem_qCoreOf_two hG ht hH
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hT1 : (T : Subgroup G) ≠ ⊥ := fun h => ht1 (by rw [h] at htT; exact htT)
  have hTtop : (T : Subgroup G) ≠ ⊤ := fun h => hHco.1 (top_le_iff.mp (h ▸ hTH))
  by_cases hO : oddCoreOf H = ⊥
  ·
    have hHN : H ≤ Subgroup.normalizer ((T : Subgroup G) : Set G) :=
      le_of_oddCoreOf_le hHA (bender1970_4_3 hG ht hH) T hTH (by rw [hO]; exact bot_le)
        (by rw [hE]; exact bot_le) Subgroup.le_normalizer inf_le_right
    exact ((hHco.le_iff.mp hHN).resolve_left (hG.normalizer_ne_top hT1 hTtop)).le
  intro g hg
  set H' := H.map (MulAut.conj g).toMonoidHom with hH'def
  have hgt : orderOf (g * t * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hH' : H' ∈ benderM (g * t * g⁻¹) := map_conj_mem_benderM g hH
  have hTH' : (T : Subgroup G) ≤ H' := by
    intro x hx
    refine ⟨g⁻¹ * x * g, hTH ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      rwa [inv_inv] at this
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hFt : CFSG.fittingSubgroupOf H' ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [(show CFSG.fittingSubgroupOf H' = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf H')]
    refine iSup_le fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hq2 : q.1.1 = 2
    ·
      intro x hx
      rw [hq2] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      have hle : CFSG.pCore 2 H' ≤ ((T.subtype hTH' : Sylow 2 H') : Subgroup H') :=
        IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := H')) _
      have hxT : (x' : G) ∈ (T : Subgroup G) := hle hx'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hTc _ hxT t htT
    ·
      have hOq' : qCoreOf H' q.1.1 = (qCoreOf H q.1.1).map (MulAut.conj g).toMonoidHom :=
        qCoreOf_conjugateSubgroup H g q.1.1
      by_cases hOq : qCoreOf H q.1.1 = ⊥
      · rw [hOq', hOq, Subgroup.map_bot]
        exact bot_le
      have hle : qCoreOf H' q.1.1 ≤ H := Bender52.le_of_isPGroup hG ht hH T htT hq hq2 hOq
        (qCoreOf_isPGroup H' q.1.1)
        (hTH'.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H' q.1.1)))
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc1 : t * x * t⁻¹ * x⁻¹ ∈ qCoreOf H 2 := by
        rw [show t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) by group]
        exact (qCoreOf H 2).mul_mem htO ((qCoreOf_normal_in H 2).2 x (hle hx) t⁻¹ (inv_mem htO))
      have hc2 : t * x * t⁻¹ * x⁻¹ ∈ qCoreOf H' q.1.1 :=
        (qCoreOf H' q.1.1).mul_mem ((qCoreOf_normal_in H' q.1.1).2 t (hTH' htT) x hx)
          ((qCoreOf H' q.1.1).inv_mem hx)
      have hc := eq_one_of_isPGroup_two_of_isPGroup hq hq2 (qCoreOf_isPGroup H 2)
        (qCoreOf_isPGroup H' q.1.1) hc1 hc2
      calc x * t = (t * x * t⁻¹ * x⁻¹)⁻¹ * (t * x) := by group
        _ = t * x := by rw [hc, inv_one, one_mul]
  have hO'H : oddCoreOf H' ≤ H :=
    (oddCoreOf_le_centralizer_of_le (hTH' htT) ht hFt).trans (centralizer_le_of_mem_benderM hH)
  have hO'O : oddCoreOf H' ≤ oddCoreOf H := le_oddCoreOf_of_isSolvable hHs T hTH hTab hO'H
    (hTH'.trans (le_normalizer_of_isNormalIn (oddCoreOf_isNormalIn' H')))
    (odd_card_oddCoreOf H')
  have hcard : Nat.card (oddCoreOf H) ≤ Nat.card (oddCoreOf H') := by
    rw [hH'def, oddCoreOf_map_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hOeq : oddCoreOf H' = oddCoreOf H := Subgroup.eq_of_le_of_card_ge hO'O hcard
  have h1 := hG.normalizer_eq_of_isNormalIn hHco (oddCoreOf_isNormalIn' H) hO
  have h2 := hG.normalizer_eq_of_isNormalIn (isCoatom_of_mem_benderM hH')
    (oddCoreOf_isNormalIn' H') (hOeq ▸ hO)
  have hHH' : H' = H := by rw [← h2, hOeq, h1]
  exact hG.mem_of_map_conj_eq hHco hHH'

end CFSG.Walter

