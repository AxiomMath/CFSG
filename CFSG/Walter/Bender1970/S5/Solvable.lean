module

public import CFSG.Walter.Bender1970.S5.Tools
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Walter.Bender1970.S2.TwoSubgroup
public import CFSG.Walter.Bender1970.S4.Components

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_le_centralizer_self_of_isQuasisimple {L : Subgroup G}
    (hL : GorensteinWalter.IsQuasisimple L) : ¬ L ≤ Subgroup.centralizer (L : Set G) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_of_isQuasisimple hL
  exact hab (Subtype.ext ((Subgroup.mem_centralizer_iff.mp (h a.2)) b b.2).symm)

theorem eq_of_le_of_isTypeL2Even
    {J L U : Subgroup G} (hJ : GorensteinWalter.IsQuasisimple J)
    (hJ2 : IsTypeL2Even (J ⧸ Subgroup.center J)) (hL : GorensteinWalter.IsQuasisimple L)
    (hLJ : L ≤ J) (hUL : U ≤ L) (hUp : IsPGroup 2 U)
    (hUmax : ∀ S : Subgroup G, S ≤ J → IsPGroup 2 S → U ≤ S → S = U) : L = J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, ⟨e⟩⟩ := hJ2
  set φ : J →* PSL(2, GaloisField 2 f) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J)) with hφdef
  have hφ : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center J))
  have hker : φ.ker = Subgroup.center J := by
    ext x
    rw [MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hUJ : U ≤ J := hUL.trans hLJ
  have hUp' : IsPGroup 2 (U.subgroupOf J) := hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUJ).symm
  obtain ⟨P, hUP⟩ := hUp'.exists_le_sylow
  have hPU : (P : Subgroup J).map J.subtype = U := hUmax _ (Subgroup.map_subtype_le _)
    (P.isPGroup'.map _)
    (fun x hx => ⟨⟨x, hUJ hx⟩, hUP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩)
  have hPL : (P : Subgroup J) ≤ L.subgroupOf J := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hUL (hPU ▸ ⟨x, hx, rfl⟩))
  set Y := (L.subgroupOf J).map φ with hYdef
  have hPY : ((P.mapSurjective hφ : Sylow 2 PSL(2, GaloisField 2 f)) :
      Subgroup PSL(2, GaloisField 2 f)) ≤ Y := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hPL
  have : Group.IsPerfect L := Group.isPerfect_def.mpr hL.2.1
  have : Group.IsPerfect (L.subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLJ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLJ).symm.surjective
  by_cases hY : Y = ⊤
  · have hsup : L.subgroupOf J ⊔ Subgroup.center J = ⊤ := by
      rw [eq_top_iff]
      intro k _
      obtain ⟨y, hy, hyk⟩ := (hY ▸ Subgroup.mem_top (φ k) : φ k ∈ Y)
      have hz : y⁻¹ * k ∈ Subgroup.center J := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyk, inv_mul_cancel]
      have : k = y * (y⁻¹ * k) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hy hz
    have htop := eq_top_of_sup_center_eq_top hJ.2.1 hsup
    refine le_antisymm hLJ fun x hx => ?_
    have : (⟨x, hx⟩ : J) ∈ L.subgroupOf J := htop ▸ Subgroup.mem_top _
    exact this
  · exfalso
    have hYs : Group.IsSolvable Y := psl2_even_isSolvable_of_sylow_le hf _ hPY hY
    have : Group.IsPerfect Y := Group.IsPerfect.map _
    have hY1 : Y = ⊥ := eq_bot_of_isPerfect_of_le_isSolvable le_rfl hYs
    have hLZ : L.subgroupOf J ≤ Subgroup.center J := by
      intro x hx
      rw [← hker]
      have : φ x ∈ Y := ⟨x, hx, rfl⟩
      rw [hY1] at this
      exact this
    apply not_le_centralizer_self_of_isQuasisimple hL
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : (⟨a, hLJ ha⟩ : J) ∈ Subgroup.center J := hLZ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨b, hLJ hb⟩)

theorem componentLayerOf_eq
    {X L U : Subgroup G} (hL : GorensteinWalter.IsQuasisimple L)
    (hLX : L ≤ X) (hUL : U ≤ L) (hUp : IsPGroup 2 U)
    (hU1 : U ≠ ⊥) (hUmax : ∀ S : Subgroup G, IsPGroup 2 S → U ≤ S → S ≤ X → S = U)
    (hUF : U ≤ generalizedFittingSubgroupOf X)
    (hULc : U ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hJ2 : ∀ J : Subgroup G, IsComponentOf J X → L ≤ J → IsTypeL2Even (J ⧸ Subgroup.center J)) :
    componentLayerOf X = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := Group.isPerfect_def.mpr hL.2.1
  have hUX : U ≤ X := hUL.trans hLX
  have hcL : ⁅L, U⁆ ≤ L := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hUL.trans Subgroup.le_normalizer)
  have hLc : L ≤ ⁅L, U⁆ := by
    refine le_of_not_le_centralizer hL (Subgroup.normalizer_commutator_ge_left L U) le_rfl
      (hcL.trans Subgroup.le_normalizer) fun hC => hU1 ?_
    rw [← le_bot_iff, ← hULc]
    intro u hu
    refine ⟨hu, mem_centralizer_of_commutator_mem_center hL.2.1 fun x hx => ?_⟩
    have hmem : u * x * u⁻¹ * x⁻¹ ∈ ⁅L, U⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hu hx
    exact ⟨⟨_, hcL hmem⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hC y.2)) _ hmem).symm, rfl⟩
  have hcF : ⁅L, U⁆ ≤ generalizedFittingSubgroupOf X := by
    rw [Subgroup.commutator_le]
    intro l hl u hu
    rw [commutatorElement_def]
    exact (generalizedFittingSubgroupOf X).mul_mem
      ((generalizedFittingSubgroupOf_isNormalIn X).2 l (hLX hl) u (hUF hu))
      ((generalizedFittingSubgroupOf X).inv_mem (hUF hu))
  have hLE : L ≤ componentLayerOf X :=
    le_componentLayerOf_of_le_generalizedFittingSubgroupOf (hLc.trans hcF)
  have hUJ : ∀ J : Subgroup G, IsComponentOf J X → U ⊓ J ≠ ⊥ := by
    intro J hJ hbot
    have hUp' : IsPGroup 2 (U.subgroupOf X) :=
      hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
    obtain ⟨S, hUS⟩ := hUp'.exists_le_sylow
    have hSU : (S : Subgroup X).map X.subtype = U := hUmax _ (S.isPGroup'.map _)
      (fun x hx => ⟨⟨x, hUX hx⟩, hUS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩)
      (Subgroup.map_subtype_le _)
    have h2 : 2 ∣ Nat.card (J.subgroupOf X) := by
      rw [natCard_subgroupOf_of_le hJ.1]
      exact IsQuasisimple.two_dvd_card hJ.2.2
    apply sylow_inf_ne_bot_of_isSubnormal S hJ.2.1 h2
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxJ⟩
    have hxU : (x : G) ∈ U := hSU ▸ ⟨x, hxS, rfl⟩
    have : (x : G) ∈ U ⊓ J := ⟨hxU, hxJ⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  have hLJ : ∀ J : Subgroup G, IsComponentOf J X → L ≤ J := by
    intro J hJ
    refine le_of_not_le_centralizer hL
      (hLE.trans (componentLayerOf_le_normalizer_of_isComponentOf hJ))
      (inf_le_right : U ⊓ J ≤ J) ((inf_le_left.trans hUL).trans Subgroup.le_normalizer)
      fun hC => hUJ J hJ ?_
    rw [eq_bot_iff, ← hULc]
    exact le_inf inf_le_left (Subgroup.le_centralizer_iff.mp hC)
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Subgroup G, IsComponentOf J₀ X := by
    by_contra h
    push Not at h
    have hE : componentLayerOf X = ⊥ := le_bot_iff.mp (sSup_le fun J hJ => absurd hJ (h J))
    have : L = ⊥ := le_bot_iff.mp (hE ▸ hLE)
    exact (Subgroup.nontrivial_iff_ne_bot L).mp hL.1 this
  have huniq : ∀ J : Subgroup G, IsComponentOf J X → J = J₀ := by
    intro J hJ
    by_contra hne
    exact not_le_centralizer_self_of_isQuasisimple hL ((hLJ J hJ).trans
      ((le_centralizer_of_isComponentOf_ne hJ hJ₀ hne).trans
        (Subgroup.centralizer_le (hLJ J₀ hJ₀))))
  have hE : componentLayerOf X = J₀ :=
    le_antisymm (sSup_le fun J hJ => (huniq J hJ).le) (le_componentLayerOf_of_isComponentOf hJ₀)
  rw [hE]
  exact (eq_of_le_of_isTypeL2Even hJ₀.2.2 (hJ2 J₀ hJ₀ (hLJ J₀ hJ₀)) hL (hLJ J₀ hJ₀) hUL hUp
    fun S hSJ hSp hUS => hUmax S hSp hUS (hSJ.trans hJ₀.1)).symm

namespace Bender51

theorem exists_orderOf_eq_two_of_ne_bot {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    ∃ w ∈ P, orderOf w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hP1
  obtain ⟨k, hk, hcard⟩ := (IsPGroup.nontrivial_iff_card hP).mp inferInstance
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (hcard ▸ dvd_pow_self 2 hk.ne')
  exact ⟨w, w.2, by rw [Subgroup.orderOf_coe, hw]⟩

variable (hG : BenderCounterexample G)
include hG

theorem inf_eq_bot
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    {s : G} (hs : orderOf s = 2) {M : Subgroup G} (hM : M ∈ benderM s) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) (hsT : s ∈ (T : Subgroup G)) (hMH : M ≠ H) {K L : Subgroup G}
    (hK : IsComponentOf K H) (hL : IsComponentOf L M) :
    ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G)) ⊓
      ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
  by_contra hne
  obtain ⟨w, hw, hw2⟩ := exists_orderOf_eq_two_of_ne_bot
    (T.isPGroup'.to_le (inf_le_left.trans inf_le_left)) hne
  have h1 := Bender44.benderM_eq_singleton hG ht hH T htT hK (Or.inr hG.noJRComponents) hw.1 hw2
  have h2 := Bender44.benderM_eq_singleton hG hs hM T hsT hL (Or.inr hG.noJRComponents) hw.2 hw2
  exact hMH (Set.singleton_eq_singleton_iff.mp (h2.symm.trans h1))

theorem not_componentLayerOf_le
    {t : G} (ht : orderOf t = 2) {H : Subgroup G}
    (hH : H ∈ benderM t) {s : G} (hs : orderOf s = 2) {M : Subgroup G} (hM : M ∈ benderM s)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) (hsT : s ∈ (T : Subgroup G)) (hMH : M ≠ H)
    {K : Subgroup G} (hK : IsComponentOf K H) : ¬ componentLayerOf M ≤ H := by
  intro hE
  have hTab := hG.hasAbelianSylowTwo T
  have hTc : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hres : IsTypeJR (K ⧸ Subgroup.center K) ∨ NoJRComponents G := Or.inr hG.noJRComponents
  have hHco := isCoatom_of_mem_benderM hH
  have hMco := isCoatom_of_mem_benderM hM
  have hMA := hG.isAStar_of_isCoatom hMco
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hTM := hG.sylow_le_of_mem_benderM T hsT hM
  set U := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hUdef
  have hUp : IsPGroup 2 U := T.isPGroup'.to_le inf_le_left
  have hUab : IsMulCommutative U := ⟨⟨fun a b => Subtype.ext (hTc _ a.2.1 _ b.2.1)⟩⟩
  obtain ⟨U₀, hU₀U, hU₀⟩ :=
    exists_isKleinFour_le_of_not_isCyclic hUp hUab (Bender44.not_isCyclic hG ht hH T htT hK)
  have hU₀C : ∀ u ∈ U₀, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H := fun u hu hu1 =>
    centralizer_le_of_mem_benderM (by
      rw [Bender44.benderM_eq_singleton hG ht hH T htT hK hres (hU₀U hu)
        (Bender44.orderOf_eq_two_of_isKleinFour hU₀ hu hu1)]
      rfl)
  have hU₀M : U₀ ≤ M := (hU₀U.trans inf_le_left).trans hTM
  have hO : oddCoreOf M ≤ H := le_of_forall_centralizer_le_of_odd hU₀
    (hU₀M.trans (le_normalizer_of_isNormalIn (oddCoreOf_isNormalIn' M)))
    (odd_card_oddCoreOf M) hU₀C
  have hMH' := le_of_oddCoreOf_le hMA (bender1970_4_3 hG hs hM) T hTM hO hE hTH
    (inf_le_right.trans (Bender44.normalizer_le hG ht hH T htT hK hres))
  exact hMH ((hMco.le_iff.mp hMH').resolve_left hHco.1).symm

theorem le_generalizedFittingSubgroupOf_centralizer
    {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {K : Subgroup G} (hK : IsComponentOf K H) {R : Subgroup G} (hRK : R ≤ K)
    (hRnc : ¬ R ≤ Subgroup.centralizer (K : Set G))
    (hUel : ∀ u ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), u ^ 2 = 1)
    (hX : Subgroup.centralizer (R : Set G) ≠ ⊤) :
    (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≤
      generalizedFittingSubgroupOf (Subgroup.centralizer (R : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres : IsTypeJR (K ⧸ Subgroup.center K) ∨ NoJRComponents G := Or.inr hG.noJRComponents
  have hTab := hG.hasAbelianSylowTwo T
  have hTc : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  set U := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hUdef
  set X := Subgroup.centralizer (R : Set G) with hXdef
  set CK := Subgroup.centralizer (K : Set G) with hCK
  have hUp : IsPGroup 2 U := T.isPGroup'.to_le inf_le_left
  have hUab : IsMulCommutative U := ⟨⟨fun a b => Subtype.ext (hTc _ a.2.1 _ b.2.1)⟩⟩
  obtain ⟨U₀, hU₀U, hU₀⟩ :=
    exists_isKleinFour_le_of_not_isCyclic hUp hUab (Bender44.not_isCyclic hG ht hH T htT hK)
  have hUH : ∀ u ∈ U, u ≠ 1 → H ∈ benderM u ∧ orderOf u = 2 := fun u hu hu1 =>
    have hu2 : orderOf u = 2 := orderOf_eq_prime (hUel u hu) hu1
    ⟨by rw [Bender44.benderM_eq_singleton hG ht hH T htT hK hres hu hu2]; rfl, hu2⟩
  have hU₀C : ∀ u ∈ U₀, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H := fun u hu hu1 =>
    centralizer_le_of_mem_benderM (hUH u (hU₀U hu) hu1).1
  have hcop : ∀ {D : Subgroup G}, Odd (Nat.card D) → Nat.Coprime (Nat.card U) (Nat.card D) := by
    intro D hD
    obtain ⟨k, hk⟩ := hUp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hD)
  have hUF : U ≤ generalizedFittingSubgroupOf H := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem _
    · obtain ⟨hHu, hu2⟩ := hUH u hu hu1
      exact bender1970_4_1 hG hu2 hHu
  have hUFit : CFSG.fittingSubgroupOf H ≤ Subgroup.centralizer (U : Set G) := by
    rw [(show CFSG.fittingSubgroupOf H = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf H)]
    refine iSup_le fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    by_cases hq2 : q.1.1 = 2
    · rw [hq2] at hx
      exact hTc u hu.1 x (qCoreOf_two_le hK T hTH hx).1
    · by_cases hu1 : u = 1
      · rw [hu1, one_mul, mul_one]
      · obtain ⟨hHu, hu2⟩ := hUH u hu hu1
        exact (Subgroup.mem_centralizer_singleton_iff.mp
          (hG.qCoreOf_le_centralizer_of_mem_benderM hu2 hHu hq hq2 hx)).symm
  have hCKH : CK ≤ H := (Bender44.centralizer_le hG ht hH T htT hK hres).1
  set Y₀ := oddCoreOf CK with hY₀
  have hY₀n : IsNormalIn Y₀ CK := oddCoreOf_isNormalIn' CK
  have hUCK : U ≤ CK := inf_le_right
  have hUY₀ : U ≤ Subgroup.centralizer (Y₀ : Set G) := by
    refine le_centralizer_of_le_centralizer_commutator
      (hUCK.trans (le_normalizer_of_isNormalIn hY₀n)) (hcop (odd_card_oddCoreOf CK)) ?_
    have h1 : ⁅Y₀, U⁆ ≤ Y₀ ⊓ generalizedFittingSubgroupOf H := by
      rw [Subgroup.commutator_le]
      intro y hy u hu
      have hyH : y ∈ H := hCKH (hY₀n.1 hy)
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def, show y * u * y⁻¹ * u⁻¹ = y * (u * y⁻¹ * u⁻¹) by group]
        exact Y₀.mul_mem hy (hY₀n.2 u (hUCK hu) y⁻¹ (Y₀.inv_mem hy))
      · rw [commutatorElement_def]
        exact (generalizedFittingSubgroupOf H).mul_mem
          ((generalizedFittingSubgroupOf_isNormalIn H).2 y hyH u (hUF hu))
          ((generalizedFittingSubgroupOf H).inv_mem (hUF hu))
    have h2 : Y₀ ⊓ generalizedFittingSubgroupOf H ≤ CFSG.fittingSubgroupOf H := by
      refine le_trans (le_inf inf_le_right ?_) (inf_centralizer_le_fittingSubgroupOf H)
      rw [Subgroup.le_centralizer_iff]
      refine sSup_le fun J hJ => ?_
      by_cases hJK : J = K
      · rw [hJK]
        exact Subgroup.le_centralizer_iff.mp (inf_le_left.trans hY₀n.1)
      · have hJC : IsComponentOf J CK :=
          isComponentOf_of_le hJ (le_centralizer_of_isComponentOf_ne hJ hK hJK) hCKH
        have hsolv : Group.IsSolvable (Y₀ ⊓ generalizedFittingSubgroupOf H : Subgroup G) :=
          CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Odd.of_dvd_nat (odd_card_oddCoreOf CK)
            (Subgroup.card_dvd_of_le inf_le_left))
        have hN : CK ≤ Subgroup.normalizer
            ((Y₀ ⊓ generalizedFittingSubgroupOf H : Subgroup G) : Set G) := fun g hg =>
          mem_normalizer_inf (le_normalizer_of_isNormalIn hY₀n hg)
            (le_normalizer_of_isNormalIn (generalizedFittingSubgroupOf_isNormalIn H) (hCKH hg))
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (isComponentOf_commutator_eq_bot_of_isSolvable hJC hsolv (inf_le_left.trans hY₀n.1) hN)
    exact Subgroup.le_centralizer_iff.mp ((h1.trans h2).trans hUFit)
  have hXA : IsAStar X := hG.isAStar X hX
  set D := oddCoreOf X with hD
  have hDn : IsNormalIn D X := oddCoreOf_isNormalIn' X
  have hUX : U ≤ X := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun r hr => (Subgroup.mem_centralizer_iff.mp hu.2) r (hRK hr)
  have hDH : D ≤ H := le_of_forall_centralizer_le_of_odd hU₀
    ((hU₀U.trans hUX).trans (le_normalizer_of_isNormalIn hDn)) (odd_card_oddCoreOf X) hU₀C
  have hDN : D ≤ Subgroup.normalizer (K : Set G) := fun d hd =>
    mem_normalizer_of_mem_centralizer_of_le hK hRK hRnc (hDH hd) (hDn.1 hd)
  have hCKX : CK ≤ X := Subgroup.centralizer_le hRK
  have hUD : U ≤ Subgroup.centralizer (D : Set G) := by
    refine le_centralizer_of_le_centralizer_commutator
      (hUX.trans (le_normalizer_of_isNormalIn hDn)) (hcop (odd_card_oddCoreOf X)) ?_
    have h1 : ⁅D, U⁆ ≤ D ⊓ CK := by
      rw [Subgroup.commutator_le]
      intro d hd u hu
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [commutatorElement_def, show d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) by group]
        exact D.mul_mem hd (hDn.2 u (hUX hu) d⁻¹ (D.inv_mem hd))
      · show ⁅d, u⁆ ∈ Subgroup.centralizer (K : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hdk : d⁻¹ * k * d ∈ K := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDN hd)) k).mp hk
          rwa [inv_inv] at this
        have huk : Commute u k := ((Subgroup.mem_centralizer_iff.mp hu.2) k hk).symm
        have hudk : u * (d⁻¹ * k * d) = (d⁻¹ * k * d) * u :=
          ((Subgroup.mem_centralizer_iff.mp hu.2) _ hdk).symm
        have hk1 : u⁻¹ * k = k * u⁻¹ := (Commute.inv_left huk).eq
        rw [commutatorElement_def]
        calc k * (d * u * d⁻¹ * u⁻¹) = d * ((d⁻¹ * k * d) * u) * d⁻¹ * u⁻¹ := by group
          _ = d * (u * (d⁻¹ * k * d)) * d⁻¹ * u⁻¹ := by rw [hudk]
          _ = d * u * d⁻¹ * (k * u⁻¹) := by group
          _ = d * u * d⁻¹ * (u⁻¹ * k) := by rw [hk1]
          _ = d * u * d⁻¹ * u⁻¹ * k := by group
    have h2 : D ⊓ CK ≤ Y₀ := le_oddCoreOf_of_isNormalIn
      ⟨inf_le_right, fun g hg x hx => ⟨hDn.2 g (hCKX hg) x hx.1,
        CK.mul_mem (CK.mul_mem hg hx.2) (CK.inv_mem hg)⟩⟩
      (Odd.of_dvd_nat (odd_card_oddCoreOf X) (Subgroup.card_dvd_of_le inf_le_left))
    exact Subgroup.le_centralizer_iff.mp
      ((h1.trans h2).trans (Subgroup.le_centralizer_iff.mp hUY₀))
  exact bender1970_2_1_subgroup hXA hUX hUp hUD

theorem eq_of_isPGroup_of_le_centralizer
    {t : G} (ht : orderOf t = 2) {H : Subgroup G}
    (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : IsComponentOf K H) {R : Subgroup G} (hRK : R ≤ K)
    (hRinv : ∀ ℓ ∈ K, orderOf ℓ = 2 → ¬ R ≤ Subgroup.centralizer ({ℓ} : Set G))
    {S : Subgroup G} (hSp : IsPGroup 2 S)
    (hUS : (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≤ S)
    (hSR : S ≤ Subgroup.centralizer (R : Set G)) :
    S = (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres : IsTypeJR (K ⧸ Subgroup.center K) ∨ NoJRComponents G := Or.inr hG.noJRComponents
  have hTab := hG.hasAbelianSylowTwo T
  have hTc : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hHA := hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hH)
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  set U := (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) with hUdef
  have hUp : IsPGroup 2 U := T.isPGroup'.to_le inf_le_left
  have hUab : IsMulCommutative U := ⟨⟨fun a b => Subtype.ext (hTc _ a.2.1 _ b.2.1)⟩⟩
  obtain ⟨U₀, hU₀U, hU₀⟩ :=
    exists_isKleinFour_le_of_not_isCyclic hUp hUab (Bender44.not_isCyclic hG ht hH T htT hK)
  obtain ⟨u₀, hu₀, hu₀1, -⟩ := exists_mem_ne_one_ne (Q := U₀) (by rw [hU₀.card_four]; omega) 1
  have hu₀2 := Bender44.orderOf_eq_two_of_isKleinFour hU₀ hu₀ hu₀1
  have hCu₀ : Subgroup.centralizer ({u₀} : Set G) ≤ H := centralizer_le_of_mem_benderM (by
    rw [Bender44.benderM_eq_singleton hG ht hH T htT hK hres (hU₀U hu₀) hu₀2]; rfl)
  obtain ⟨P, hSP⟩ := hSp.exists_le_sylow
  have hPab := hG.hasAbelianSylowTwo P
  have hSH : S ≤ H := by
    intro x hx
    apply hCu₀
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hPab.is_comm.comm ⟨x, hSP hx⟩ ⟨u₀, hSP (hUS (hU₀U hu₀))⟩)
  obtain ⟨h, hhH, hh⟩ := exists_conj_le_sylow_of_isPGroup T hTH hSH hSp
  set T' : Sylow 2 G := h • T with hT'def
  have hT' : (T' : Subgroup G) = (T : Subgroup G).map (MulAut.conj h).toMonoidHom :=
    CFSG.Glauberman.sylow_smul_subgroup_eq_map_conj h T
  have hST' : S ≤ T' := by
    intro x hx
    rw [hT']
    refine ⟨h⁻¹ * x * h, hh x hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hT'H : (T' : Subgroup G) ≤ H := by
    rw [hT']
    rintro _ ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hhH (hTH hy)) (H.inv_mem hhH)
  have hT'ab := hG.hasAbelianSylowTwo T'
  have hKQ' := bender38Component hHA hK T' hT'H hT'ab
  have hKQ := bender38Component hHA hK T hTH hTab
  have hSK : S ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx
    obtain ⟨ℓ, hℓ, hconj⟩ := component_exists_inner hHA hK T' hT'H (hST' hx)
    have hℓR : R ≤ Subgroup.centralizer ({ℓ} : Set G) := by
      intro r hr
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hconj r (hRK hr)
      have h2 : x * r * x⁻¹ = r := by
        rw [← (Subgroup.mem_centralizer_iff.mp (hSR hx)) r hr, mul_inv_cancel_right]
      have h3 : ℓ * r * ℓ⁻¹ = r := h1.symm.trans h2
      calc r * ℓ = ℓ * r * ℓ⁻¹ * ℓ := by rw [h3]
        _ = ℓ * r := by group
    have hℓ1 : ℓ = 1 := by
      by_contra hℓ1
      exact hRinv ℓ hℓ.2 (orderOf_eq_prime (hKQ'.sq_eq_one ℓ hℓ) hℓ1) hℓR
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := hconj k hk
    rw [hℓ1, one_mul, inv_one, mul_one] at h1
    calc k * x = x * k * x⁻¹ * x := by rw [h1]
      _ = x * k := by group
  have hcardT' := card_sylow_eq_mul hHA hK T' hT'H hKQ'
  have hcardT := card_sylow_eq_mul hHA hK T hTH hKQ
  have hTT' : Nat.card (T' : Subgroup G) = Nat.card (T : Subgroup G) := by
    rw [T'.card_eq_multiplicity, T.card_eq_multiplicity]
  have hQQ' : Nat.card ((T' : Subgroup G) ⊓ K : Subgroup G) =
      Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) := by
    rw [hKQ'.card_eq, hKQ.card_eq]
  have hpos := Nat.card_pos (α := ((T : Subgroup G) ⊓ K : Subgroup G))
  have hU' : Nat.card ((T' : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) =
      Nat.card U := by
    rw [hTT', hQQ', hcardT] at hcardT'
    exact (Nat.eq_of_mul_eq_mul_right hpos hcardT').symm
  have hle : Nat.card S ≤ Nat.card U :=
    hU' ▸ Subgroup.card_le_of_le (le_inf hST' hSK)
  exact (Subgroup.eq_of_le_of_card_ge hUS hle).symm


theorem false_of_le_normalizer
    {t : G} (ht : orderOf t = 2) {H : Subgroup G}
    (hH : H ∈ benderM t) {s : G} (hs : orderOf s = 2) {M : Subgroup G} (hM : M ∈ benderM s)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) (hsT : s ∈ (T : Subgroup G)) (hMH : M ≠ H)
    {K L : Subgroup G} (hK : IsComponentOf K H) (hL : IsComponentOf L M)
    (hLM : M ≤ Subgroup.normalizer (L : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnoJR := hG.noJRComponents
  have hTab := hG.hasAbelianSylowTwo T
  have hTc : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hHco := isCoatom_of_mem_benderM hH
  have hMco := isCoatom_of_mem_benderM hM
  have hHA := hG.isAStar_of_isCoatom hHco
  have hMA := hG.isAStar_of_isCoatom hMco
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hTM := hG.sylow_le_of_mem_benderM T hsT hM
  have hKL2 := Bender44.isTypeL2Even hG ht hH T htT hK (Or.inr hnoJR) hK
  have hLL2 := Bender44.isTypeL2Even hG hs hM T hsT hL (Or.inr hnoJR) hL
  have hNTM := Bender44.normalizer_le hG hs hM T hsT hL (Or.inr hnoJR)
  have hKQ := bender38Component hHA hK T hTH hTab
  have hLQ := bender38Component hMA hL T hTM hTab
  have hUV := inf_eq_bot hG ht hH hs hM T htT hsT hMH hK hL
  obtain ⟨R, hRK, hRN, hRodd, hRtr, hRinv, hRgen⟩ :=
    exists_torus_of_isComponentOf hHA hK hKL2 T hTH
  have hTUQ : ∀ x ∈ (T : Subgroup G), ∃ w ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G),
      ∃ v ∈ (T : Subgroup G) ⊓ K, w * v = x := fun x hx => exists_mul_of_mem_sylow hHA hK T hTH hx
  have hRU : ∀ r ∈ R, ∀ w ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G),
      r * w = w * r := fun r hr w hw => (Subgroup.mem_centralizer_iff.mp hw.2) r (hRK hr)
  have hconjwv : ∀ r ∈ R, ∀ w ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), ∀ v : G,
      r * (w * v) * r⁻¹ = w * (r * v * r⁻¹) := fun r hr w hw v => by
    rw [← mul_assoc r w, hRU r hr w hw]
    group
  have hRT : R ≤ Subgroup.normalizer ((T : Subgroup G) : Set G) := fun r hr =>
    mem_normalizer_of_conj_mem' fun x hx => by
      obtain ⟨w, hw, v, hv, rfl⟩ := hTUQ x hx
      rw [hconjwv r hr w hw v]
      exact (T : Subgroup G).mul_mem hw.1 ((Subgroup.mem_normalizer_iff.mp (hRN hr) v).mp hv).1
  have hRM : R ≤ M := hRT.trans hNTM
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRM.trans hLM
  have hcommQ : ∀ r ∈ R, ∀ x ∈ (T : Subgroup G), r * x * r⁻¹ * x⁻¹ ∈ (T : Subgroup G) ⊓ K := by
    intro r hr x hx
    obtain ⟨w, hw, v, hv, rfl⟩ := hTUQ x hx
    have hrv : r * v * r⁻¹ ∈ (T : Subgroup G) ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp (hRN hr) v).mp hv
    have hprod : r * v * r⁻¹ * v⁻¹ ∈ (T : Subgroup G) :=
      (T : Subgroup G).mul_mem hrv.1 ((T : Subgroup G).inv_mem hv.1)
    have : r * (w * v) * r⁻¹ * (w * v)⁻¹ = r * v * r⁻¹ * v⁻¹ := by
      rw [hconjwv r hr w hw v]
      calc w * (r * v * r⁻¹) * (w * v)⁻¹ = w * (r * v * r⁻¹ * v⁻¹) * w⁻¹ := by group
        _ = r * v * r⁻¹ * v⁻¹ := by rw [hTc w hw.1 _ hprod, mul_inv_cancel_right]
    rw [this]
    exact ((T : Subgroup G) ⊓ K).mul_mem hrv (((T : Subgroup G) ⊓ K).inv_mem hv)
  have hCTR : ∀ x ∈ (T : Subgroup G), (∀ r ∈ R, r * x * r⁻¹ = x) →
      x ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) := by
    intro x hx hxR
    obtain ⟨w, hw, v, hv, rfl⟩ := hTUQ x hx
    by_cases hv1 : v = 1
    · rw [hv1, mul_one]
      exact hw
    · exfalso
      obtain ⟨v', hv', hv'1, hv'v⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ K)
        (by have := hKQ.four_le_card; omega) v
      obtain ⟨r, hr, hrv⟩ := hRtr v hv hv1 v' hv' hv'1
      apply hv'v
      rw [← hrv]
      have h1 := hxR r hr
      rw [hconjwv r hr w hw v] at h1
      exact mul_left_cancel h1
  have hRV : ∀ r ∈ R, ∀ x ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G),
      r * x * r⁻¹ ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) := fun r hr x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hRT hr) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (Bender35.mem_normalizer_centralizer (hRL hr)) x).mp hx.2⟩
  have hRTL : ∀ r ∈ R, ∀ x ∈ (T : Subgroup G) ⊓ L, r * x * r⁻¹ ∈ (T : Subgroup G) ⊓ L :=
    fun r hr x hx => ⟨(Subgroup.mem_normalizer_iff.mp (hRT hr) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hRL hr) x).mp hx.2⟩
  have hV1 : (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    intro h
    apply Bender44.not_isCyclic hG hs hM T hsT hL
    rw [h]
    exact isCyclic_of_subsingleton
  have hVQ1 : ∃ x ∈ ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) ⊓
      ((T : Subgroup G) ⊓ K), x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    apply hv1
    have hvU : v ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) :=
      hCTR v hv.1 fun r hr => by
        have h1 := hcon _ ⟨((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)).mul_mem
          (hRV r hr v hv) (((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)).inv_mem hv),
          hcommQ r hr v hv.1⟩
        rwa [mul_inv_eq_one] at h1
    have : v ∈ ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G)) ⊓
        ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) := ⟨hvU, hv⟩
    rw [hUV, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hQV : (T : Subgroup G) ⊓ K ≤ (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) := by
    obtain ⟨x, hx, hx1⟩ := hVQ1
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    obtain ⟨r, hr, hrxy⟩ := hRtr x hx.2 hx1 y hy hy1
    rw [← hrxy]
    exact hRV r hr x hx.1
  have hcardT := card_sylow_eq_mul hHA hK T hTH hKQ
  have hVQ : (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) = (T : Subgroup G) ⊓ K := by
    have hcomm : (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
      fun x hx => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
        fun y hy => hTc _ hy.1 _ hx.1)
    have h1 := card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hcomm (disjoint_iff.mpr hUV)
    have h2 := Subgroup.card_le_of_le (sup_le
      (inf_le_left : (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≤ T)
      (inf_le_left : (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤ T))
    rw [h1, hcardT] at h2
    exact (Subgroup.eq_of_le_of_card_ge hQV (Nat.le_of_mul_le_mul_left h2 Nat.card_pos)).symm
  have hRTLc : ∀ r ∈ R, ∀ y ∈ (T : Subgroup G) ⊓ L, r * y * r⁻¹ = y := by
    intro r hr y hy
    have h1 : r * y * r⁻¹ * y⁻¹ ∈ ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) ⊓
        ((T : Subgroup G) ⊓ L) :=
      ⟨hVQ ▸ hcommQ r hr y hy.1, ((T : Subgroup G) ⊓ L).mul_mem (hRTL r hr y hy)
        (((T : Subgroup G) ⊓ L).inv_mem hy)⟩
    rw [inf_inf_eq_bot T.isPGroup' hLQ, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  obtain ⟨SL, hSL⟩ := component_exists_sylow hL T hTM
  have hRCL : R ≤ Subgroup.centralizer (L : Set G) := by
    intro r hr
    exact mem_centralizer_of_isTypeL2Even hL.2.2 hLL2 (hRL hr)
      (Odd.of_dvd_nat hRodd (Subgroup.orderOf_dvd_natCard R hr)) SL
      fun x hx => hRTLc r hr x (hSL ▸ ⟨x, hx, rfl⟩)
  have hLX : L ≤ Subgroup.centralizer (R : Set G) := Subgroup.le_centralizer_iff.mp hRCL
  have hTLU : (T : Subgroup G) ⊓ L = (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) := by
    have hle : (T : Subgroup G) ⊓ L ≤ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) :=
      fun y hy => hCTR y hy.1 fun r hr => hRTLc r hr y hy
    have h1 := card_sylow_eq_mul hMA hL T hTM hLQ
    rw [hVQ, hcardT, mul_comm] at h1
    exact Subgroup.eq_of_le_of_card_ge hle
      (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).le
  have hUL : (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≤ L := hTLU ▸ inf_le_right
  have hUel : ∀ u ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), u ^ 2 = 1 :=
    fun u hu => hLQ.sq_eq_one u (hTLU ▸ hu)
  have hRnc : ¬ R ≤ Subgroup.centralizer (K : Set G) := by
    intro h
    obtain ⟨u, hu, hu1, -⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ K)
      (by have := hKQ.four_le_card; omega) 1
    obtain ⟨v, hv, hv1, hvu⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ K)
      (by have := hKQ.four_le_card; omega) u
    obtain ⟨r, hr, hruv⟩ := hRtr u hu hu1 v hv hv1
    apply hvu
    rw [← hruv, ← (Subgroup.mem_centralizer_iff.mp (h hr)) u hu.2, mul_inv_cancel_right]
  have hX : Subgroup.centralizer (R : Set G) ≠ ⊤ := by
    intro htop
    apply hRnc
    intro r hr
    have hrZ : r ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
      ((Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g)) r hr).symm
    rw [hG.center_eq_bot, Subgroup.mem_bot] at hrZ
    rw [hrZ]
    exact one_mem _
  have hXA := hG.isAStar _ hX
  have hUF := le_generalizedFittingSubgroupOf_centralizer hG ht hH T htT hK hRK hRnc hUel hX
  have hU1 : (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
    intro h
    apply Bender44.not_isCyclic hG ht hH T htT hK
    rw [h]
    exact isCyclic_of_subsingleton
  have hULc : ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G)) ⊓
      Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hUV]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hUp : IsPGroup 2 ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
    T.isPGroup'.to_le inf_le_left
  have hUab : IsMulCommutative ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) :
      Subgroup G) := ⟨⟨fun a b => Subtype.ext (hTc _ a.2.1 _ b.2.1)⟩⟩
  obtain ⟨U₀, hU₀U, hU₀⟩ :=
    exists_isKleinFour_le_of_not_isCyclic hUp hUab (Bender44.not_isCyclic hG ht hH T htT hK)
  have hU₀C : ∀ u ∈ U₀, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H := fun u hu hu1 =>
    centralizer_le_of_mem_benderM (by
      rw [Bender44.benderM_eq_singleton hG ht hH T htT hK (Or.inr hnoJR) (hU₀U hu)
        (Bender44.orderOf_eq_two_of_isKleinFour hU₀ hu hu1)]
      rfl)
  have hUX : (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.centralizer (R : Set G) := hUL.trans hLX
  have hLnH : ¬ L ≤ H := fun h =>
    hMH (Bender44.eq_of_le hG hs hM T hsT hL (Or.inr hnoJR) htT ht hH h).symm
  have hE := componentLayerOf_eq hL.2.2 hLX hUL hUp hU1
    (fun S hSp hUS hSX => eq_of_isPGroup_of_le_centralizer hG ht hH T htT hK hRK hRinv hSp hUS
      hSX) hUF hULc fun J hJ hLJ => by
        by_contra hJ2
        exact hLnH (hLJ.trans (le_of_isComponentOf_of_not_isTypeL2Even hXA (hU₀U.trans hUX)
          hU₀ hU₀C hJ hJ2))
  have hNL : Subgroup.normalizer (L : Set G) = M :=
    hG.normalizer_eq_of_isNormalIn hMco ⟨hL.1, fun g hg k hk =>
      (Subgroup.mem_normalizer_iff.mp (hLM hg) k).mp hk⟩ (ne_bot_of_isComponentOf hL)
  have hNR : Subgroup.normalizer (R : Set G) ≤ M := fun n hn => by
    have h1 := mem_normalizer_componentLayerOf (Bender35.mem_normalizer_centralizer hn)
    rw [hE, hNL] at h1
    exact h1
  have hKM : K ≤ M := hRgen M (fun k hk => hNTM (mem_normalizer_of_conj_mem' fun x hx => by
      obtain ⟨w, hw, v, hv, rfl⟩ := hTUQ x hx
      have hkw : k * w = w * k := (Subgroup.mem_centralizer_iff.mp hw.2) k hk.1
      have : k * (w * v) * k⁻¹ = w * (k * v * k⁻¹) := by rw [← mul_assoc k w, hkw]; group
      rw [this]
      exact (T : Subgroup G).mul_mem hw.1 ((Subgroup.mem_normalizer_iff.mp hk.2 v).mp hv).1))
    fun k hk => hNR hk.2
  exact hMH (Bender44.eq_of_le hG ht hH T htT hK (Or.inr hnoJR) hsT hs hM hKM)

end Bender51

theorem bender1970_5_1
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) : Group.IsSolvable H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hns
  have hE : componentLayerOf H ≠ ⊥ := by
    intro hE
    apply hns
    have := bender1970_4_3 hG ht hH
    have hker : (QuotientGroup.mk' ((componentLayerOf H).subgroupOf H)).ker = ⊥ := by
      rw [QuotientGroup.ker_mk', hE, Subgroup.bot_subgroupOf]
    exact Group.isSolvable_of_isSolvable_injective
      (f := QuotientGroup.mk' ((componentLayerOf H).subgroupOf H))
      ((MonoidHom.ker_eq_bot_iff _).mp hker)
  obtain ⟨T, htT⟩ := exists_sylow_two_mem ht
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, IsComponentOf K H := by
    by_contra h
    push Not at h
    exact hE (le_bot_iff.mp (sSup_le fun J hJ => absurd hJ (h J)))
  obtain ⟨s, hsT, hs, M, hM, hMH⟩ := hG.exists_mem_benderM_ne_of_mem_benderM ht hH T htT
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, IsComponentOf L M := by
    by_contra h
    push Not at h
    exact Bender51.not_componentLayerOf_le hG ht hH hs hM T htT hsT hMH hK
      ((sSup_le fun J hJ => absurd hJ (h J)).trans bot_le)
  have hTab := hG.hasAbelianSylowTwo T
  have hHA := hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hH)
  have hMA := hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hM)
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hTM := hG.sylow_le_of_mem_benderM T hsT hM
  by_cases hKn : H ≤ Subgroup.normalizer (K : Set G)
  · exact Bender51.false_of_le_normalizer hG hs hM ht hH T hsT htT (Ne.symm hMH) hL hK hKn
  by_cases hLn : M ≤ Subgroup.normalizer (L : Set G)
  · exact Bender51.false_of_le_normalizer hG ht hH hs hM T htT hsT hMH hK hL hLn
  have h1 := card_inf_lt_of_not_le_normalizer hHA hK T hTH hTab hKn
  have h2 := card_inf_lt_of_not_le_normalizer hMA hL T hTM hTab hLn
  have h3 := card_sylow_eq_mul hHA hK T hTH (bender38Component hHA hK T hTH hTab)
  have h4 := card_sylow_eq_mul hMA hL T hTM (bender38Component hMA hL T hTM hTab)
  have hUV := Bender51.inf_eq_bot hG ht hH hs hM T htT hsT hMH hK hL
  have hTc : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm : (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun y hy => hTc _ hy.1 _ hx.1)
  have h5 := card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hcomm (disjoint_iff.mpr hUV)
  have h6 := Subgroup.card_le_of_le (sup_le
    (inf_le_left : (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) ≤ T)
    (inf_le_left : (T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤ T))
  rw [h5] at h6
  have hu := Nat.card_pos (α := ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) :
    Subgroup G))
  have hv := Nat.card_pos (α := ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) :
    Subgroup G))
  have hTu : Nat.card (T : Subgroup G) <
      Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) *
        Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
    rw [h3]
    exact Nat.mul_lt_mul_of_pos_left h1 hu
  have hTv : Nat.card (T : Subgroup G) <
      Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) *
        Nat.card ((T : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
    rw [h4]
    exact Nat.mul_lt_mul_of_pos_left h2 hv
  have h7 := Nat.mul_lt_mul'' hTu hTv
  have h8 := Nat.mul_le_mul h6 h6
  nlinarith

end CFSG.Walter
