module

public import CFSG.GroupTheory.ExtraspecialThreeFive
public import CFSG.Quasithin.H13.NQS1312Z
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS3b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ2b
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPK3H

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K3)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem exists_elemAbelian_27_of_mem_inf_L
    (hK3 : K3) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {e : G} (he : e ∈ P ⊓ c.L) (heZ : e ∉ zSub P c.L) :
    ∃ A : Subgroup G, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      e ∈ A ∧ A ≤ P ⊓ c.L ∧ zSub P c.L ≤ A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := P ⊓ c.L
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let QL : Subgroup ↥c.L := Q.subgroupOf c.L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective O)
  have hScoe : (S : Subgroup c.Lbar) = QL.map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  obtain ⟨hScard, hSexp, hScenter, hScomm⟩ := hK3 c.Lbar hON S
  let f : ↥QL →* c.Lbar := π.comp QL.subtype
  have hdisj : QL ⊓ O = ⊥ := by
    have hQ3 : IsPGroup 3 QL := hQsyl.isPGroup.comap_subtype
    have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) QL O hQ3 hO2).eq_bot
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : QuotientGroup.mk' O (x : ↥c.L) = 1 := hx
    have hxO : (x : ↥c.L) ∈ O := (QuotientGroup.eq_one_iff (N := O) (x : ↥c.L)).mp hx'
    have hxbot : (x : ↥c.L) ∈ (⊥ : Subgroup ↥c.L) := by
      rw [← hdisj]
      exact ⟨x.2, hxO⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  let eQL₀ : ↥QL ≃* ↥f.range := MonoidHom.ofInjective hf_inj
  have hrange : f.range = (S : Subgroup c.Lbar) := by
    rw [hScoe]
    ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let eQL : ↥QL ≃* ↥S := eQL₀.trans (MulEquiv.subgroupCongr hrange)
  let eQ : ↥Q ≃* ↥S :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ≤ c.L)).symm.trans eQL
  have hcardQ : Nat.card ↥Q = 3 ^ 5 := by
    rw [Nat.card_congr eQ.toEquiv]
    exact hScard
  have hexpQ : ∀ x : ↥Q, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    exact c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP (x : G) x.2
  have hZS : Nat.card (Subgroup.center ↥S) = 3 := by
    have hmap := CFSG.center_map_subtype_eq_inf_centralizer (S : Subgroup c.Lbar)
    calc Nat.card (Subgroup.center ↥S)
        = Nat.card ↥((Subgroup.center ↥(S : Subgroup c.Lbar)).map
            (S : Subgroup c.Lbar).subtype) :=
          (Subgroup.card_map_of_injective (S : Subgroup c.Lbar).subtype_injective).symm
      _ = Nat.card ↥((S : Subgroup c.Lbar) ⊓
            Subgroup.centralizer ((S : Subgroup c.Lbar) : Set c.Lbar)) := by rw [hmap]
      _ = 3 := hScenter
  have hcommS_eq : commutator ↥S = Subgroup.center ↥S := by
    apply Subgroup.map_injective (S : Subgroup c.Lbar).subtype_injective
    calc Subgroup.map (S : Subgroup c.Lbar).subtype (commutator ↥S)
        = ⁅(S : Subgroup c.Lbar), (S : Subgroup c.Lbar)⁆ := by
          exact Subgroup.map_subtype_commutator (S : Subgroup c.Lbar)
      _ = (S : Subgroup c.Lbar) ⊓
            Subgroup.centralizer ((S : Subgroup c.Lbar) : Set c.Lbar) := hScomm
      _ = Subgroup.map (S : Subgroup c.Lbar).subtype (Subgroup.center ↥S) :=
          (CFSG.center_map_subtype_eq_inf_centralizer (S : Subgroup c.Lbar)).symm
  have hZQ : Nat.card (Subgroup.center ↥Q) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr eQ).toEquiv, hZS]
  have hcommQ : commutator ↥Q ≤ Subgroup.center ↥Q := by
    have hcenter_map : (Subgroup.center ↥Q).map eQ.toMonoidHom = Subgroup.center ↥S := by
      apply le_antisymm
      · rintro x ⟨y, hy, rfl⟩
        exact (Subgroup.centerCongr eQ ⟨y, hy⟩).2
      · intro x hx
        refine ⟨eQ.symm x, ?_, eQ.apply_symm_apply x⟩
        exact ((Subgroup.centerCongr eQ).symm ⟨x, hx⟩).2
    have hmapcomm : (commutator ↥Q).map eQ.toMonoidHom = commutator ↥S := by
      rw [show commutator ↥Q = ⁅(⊤ : Subgroup ↥Q), ⊤⁆ from rfl, Subgroup.map_commutator]
      rw [show commutator ↥S = ⁅(⊤ : Subgroup ↥S), ⊤⁆ from rfl]
      simp
    have hle : (commutator ↥Q).map eQ.toMonoidHom ≤
        (Subgroup.center ↥Q).map eQ.toMonoidHom := by
      rw [hmapcomm, hcenter_map, hcommS_eq]
    exact (Subgroup.map_le_map_iff_of_injective eQ.injective).mp hle
  have haZ : (⟨e, he⟩ : ↥Q) ∉ Subgroup.center ↥Q := by
    intro hcen
    have hmem : e ∈ (Subgroup.center ↥Q).map Q.subtype :=
      Subgroup.mem_map.mpr ⟨⟨e, he⟩, hcen, rfl⟩
    rw [CFSG.center_map_subtype_eq_inf_centralizer Q] at hmem
    exact heZ (by simpa [Q, zSub] using hmem)
  obtain ⟨E, -, haE, hEea, hE27⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_elemAbelian_27_of_index_le_three
      (R := ↥Q) hcardQ hexpQ hZQ hcommQ (H := ⊤) (by simp) (a := ⟨e, he⟩)
      (Subgroup.mem_top _) haZ
  let A : Subgroup G := E.map Q.subtype
  have hAea : CFSG.Open.IsElemAbelian 3 A := hEea.map Q.subtype
  have hA27 : Nat.card A = 27 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hE27]
  have heA : e ∈ A := Subgroup.mem_map.mpr ⟨⟨e, he⟩, haE, rfl⟩
  have hAPL : A ≤ P ⊓ c.L := by
    simpa [A, Q] using Subgroup.map_subtype_le (H := Q) E
  have hZcard : Nat.card (zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
  have hZcent : zSub P c.L ≤ Subgroup.centralizer ((zSub P c.L : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (⟨x, hx⟩ : ↥(zSub P c.L)).2.2 (y : G) hy.1
  have hZcomm : IsMulCommutative ↥(zSub P c.L) :=
    (Subgroup.le_centralizer_iff_isMulCommutative).mp hZcent
  have hZea : CFSG.Open.IsElemAbelian 3 (zSub P c.L) :=
    ⟨hZcomm, fun x hx =>
      c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP x hx.1⟩
  have hcommAZ : ∀ x ∈ A, ∀ y ∈ zSub P c.L, x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (⟨y, hy⟩ : ↥(zSub P c.L)).2.2 (x : G) (hAPL hx)
  have hZA : zSub P c.L ≤ A := by
    by_contra hnot
    have hinf : A ⊓ zSub P c.L = ⊥ := by
      have hdvd : Nat.card ↥(A ⊓ zSub P c.L) ∣ 3 := by
        rw [← hZcard]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hnot
        have heq : A ⊓ zSub P c.L = zSub P c.L :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZcard])
        exact heq ▸ inf_le_left
    have hsupEa : CFSG.Open.IsElemAbelian 3 (A ⊔ zSub P c.L) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hAea hZea hcommAZ
    have hcardSup : Nat.card ↥(A ⊔ zSub P c.L) = 81 := by
      have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A (zSub P c.L)
        hcommAZ).1
      rw [hinf, Subgroup.card_bot, hA27, hZcard] at h
      simpa using h
    have hZQle : zSub P c.L ≤ P ⊓ c.L := inf_le_left
    have hsupM : (A ⊔ zSub P c.L) ≤ D.M :=
      sup_le ((hAPL.trans inf_le_left).trans hP.le)
        ((hZQle.trans inf_le_left).trans hP.le)
    obtain ⟨k, hk⟩ := hsupEa.isPGroup.exists_card_eq
    have hk_le : k ≤ CFSG.Open.pRank 3 D.M :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hsupM hsupEa hk
    rw [c.pRank_three_M] at hk_le
    have hk4 : k = 4 := by
      have h34 : 3 ^ k = 3 ^ 4 := by
        rw [← hk, hcardSup]
        norm_num
      exact Nat.pow_right_injective (by norm_num : 1 < 3) h34
    omega
  exact ⟨A, hAea, hA27, heA, hAPL, hZA⟩

theorem Ia_eq_closure_three (hTC : IsTripleCover (↥(Ia c a) ⧸ CFSG.Open.pCore 2 ↥(Ia c a))
    (alternatingGroup (Fin 6))) :
    Ia c a = Subgroup.closure {x : G | x ∈ Ia c a ∧ orderOf x = 3} := by
  classical
  let L : Subgroup G := Ia c a
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  let X := ↥L ⧸ O
  haveI hO : O.Normal := CFSG.pCore_normal
  haveI : Group.IsPerfect ↥L := Ia_perfect c a
  have hperf : ⁅L, L⁆ = L := Subgroup.commutator_eq_self
  haveI hXperf : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  have hQ : CFSG.IsQuasisimple X := by
    refine ⟨hXperf, ?_, ?_⟩
    · obtain ⟨e⟩ := hTC.2
      haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact MulEquiv.isSimpleGroup e
    · obtain ⟨e⟩ := hTC.2
      haveI : Nontrivial (alternatingGroup (Fin 6)) :=
        alternatingGroup.nontrivial_of_three_le_card (by simp)
      haveI : Nontrivial (X ⧸ Subgroup.center X) := e.toEquiv.nontrivial
      by_contra h
      have hc : ∀ a b : X ⧸ Subgroup.center X, a * b = b * a := fun a b => by
        by_contra hab
        exact h ⟨a, b, hab⟩
      haveI : IsMulCommutative (X ⧸ Subgroup.center X) := ⟨⟨hc⟩⟩
      have hbot : commutator (X ⧸ Subgroup.center X) = ⊥ :=
        commutator_eq_bot (X ⧸ Subgroup.center X)
      have htop : commutator (X ⧸ Subgroup.center X) = ⊤ := Group.IsPerfect.commutator_eq_top
      have hEq : (⊤ : Subgroup (X ⧸ Subgroup.center X)) = ⊥ := by rw [← htop, hbot]
      exact (Subgroup.nontrivial_iff_ne_bot ⊤).mp inferInstance hEq
  have hHat : CFSG.Quasithin.IsHat X (alternatingGroup (Fin 6)) := ⟨hQ, hTC.1, hTC.2⟩
  have hgen : Subgroup.closure {y : X | orderOf y = 3} = ⊤ :=
    CFSG.Quasithin.H13.U3.NLine.closure_orderOf_three_hat6 hHat
  have hker3 : ∀ x ∈ (QuotientGroup.mk' O).ker, orderOf x ≠ 3 := by
    intro x hx h3
    rw [QuotientGroup.ker_mk'] at hx
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x, hx⟩
    have h1 : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h2 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h1
    rw [h3] at h2
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h2
    norm_num at h32
  have hX3 : 3 ∣ Nat.card X := by
    obtain ⟨e⟩ := hTC.2
    have hdvd : Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card X :=
      Subgroup.card_quotient_dvd_card (Subgroup.center X)
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have h3 : 3 ∣ Nat.card (X ⧸ Subgroup.center X) := by
      rw [Nat.card_congr e.toEquiv, h360]
      norm_num
    exact h3.trans hdvd
  have hle : L ≤ CFSG.Quasithin.thetaOf L :=
    CFSG.Quasithin.R3c2.le_thetaOf_of_surjection (H := L) le_rfl hperf hQ
      (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O) hker3 hgen hX3
  have hclos : CFSG.Quasithin.thetaOf L ≤ L :=
    (Subgroup.closure_le L).mpr fun x hx => hx.1
  have heq : L = CFSG.Quasithin.thetaOf L := le_antisymm hle hclos
  simpa [L, CFSG.Quasithin.thetaOf] using heq

theorem f9_perfectCore'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (haL : a ∈ P ⊓ c.L) (ha3 : orderOf a = 3) (haZ : a ∉ zSub P c.L)
    (hK2 : K2ONanCentralizer) :
    F9Input c P a := by
  obtain ⟨E, hEea, hE27, haE, hEPL, hZE⟩ :=
    exists_elemAbelian_27_of_mem_inf_L K3_holds' c hON hP haL haZ
  have hF9 : F9PerfectCore c P a :=
    f9PerfectCore_holds c hON hP hEea hE27 hZE hEPL haE haZ
  exact ⟨hF9.1, hF9.2.1, hF9.2.2, Ia_eq_closure_three c hF9.1⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
