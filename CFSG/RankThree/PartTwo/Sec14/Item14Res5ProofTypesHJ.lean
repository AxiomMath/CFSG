module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesModel
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS142J2Rigid : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 9 → ∀ τ : MulAut X, (∀ e ∈ E, τ e = e) →
      ∀ n : ℕ, ¬ 3 ∣ n → τ ^ n = 1 → τ = 1

@[expose] noncomputable def KS142J2List : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 9 → ∀ Y : Subgroup X, ¬ 3 ∣ Nat.card Y →
      E ≤ Subgroup.normalizer (Y : Set X) →
      (∀ Y' : Subgroup X, ¬ 3 ∣ Nat.card Y' → E ≤ Subgroup.normalizer (Y' : Set X) → Y ≤ Y' →
        Y' = Y) →
      (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
          Nonempty (↥Y ≃*
            ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
        ∃ a ∈ E, ∃ b ∈ E, ∃ d ∈ E, Subgroup.closure {a, b} = E ∧ d ≠ 1 ∧
          (∃ S : Sylow 3 X, d ∈ (S : Subgroup X) ∧
            (S : Subgroup X) ≤ Subgroup.centralizer ({d} : Set X)) ∧
          Subgroup.zpowers a ≠ Subgroup.zpowers d ∧ Subgroup.zpowers b ≠ Subgroup.zpowers d ∧
          Y = inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set X)) ⊔
              inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) ⊔
            (Y ⊓ Subgroup.centralizer ({d} : Set X))

namespace Res5Types

namespace Inner142

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G} (d : Inner142 A c L)
include d

variable [(ker142 A (lB A) c).Normal]

theorem bar_inf_centralizer (W : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))
    {x : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c} (hx : x ∈ img142 A (lB A) c L) :
    d.bar (W ⊓ Subgroup.centralizer ({x} : Set _)) =
      d.bar W ⊓ Subgroup.centralizer ({d.lbarEquiv.symm ⟨x, hx⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  rw [d.bar_inf]
  congr 1
  rw [bar, centralizer_subgroupOf hx, CFSG.RankThree.PartTwo.map_centralizer_singleton]

theorem bar_zpowers {x : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c}
    (hx : x ∈ img142 A (lB A) c L) :
    d.bar (Subgroup.zpowers x) = Subgroup.zpowers (d.lbarEquiv.symm ⟨x, hx⟩) := by
  have h : Subgroup.zpowers x =
      (Subgroup.zpowers (⟨x, hx⟩ : ↥(img142 A (lB A) c L))).map (img142 A (lB A) c L).subtype := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [bar, h, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
    (Subgroup.subtype_injective _), MonoidHom.map_zpowers]
  rfl

theorem isThreeCentralIn_of_bar {x : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c}
    (hx : x ∈ img142 A (lB A) c L) (S : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hxS : d.lbarEquiv.symm ⟨x, hx⟩ ∈ (S : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hSC : (S : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ≤
      Subgroup.centralizer ({d.lbarEquiv.symm ⟨x, hx⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    IsThreeCentralIn (img142 A (lB A) c L) x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := d.lbarEquiv with hψ
  have hψx : ψ (ψ.symm ⟨x, hx⟩) = ⟨x, hx⟩ := ψ.apply_symm_apply _
  have hsurj : Function.Surjective ψ.toMonoidHom := ψ.surjective
  refine ⟨hx, S.mapSurjective hsurj, ?_, ?_⟩
  · change ⟨x, hx⟩ ∈ (S : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)).map ψ.toMonoidHom
    exact ⟨_, hxS, hψx⟩
  · change (S : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)).map ψ.toMonoidHom ≤ _
    refine (Subgroup.map_mono hSC).trans ?_
    rw [CFSG.RankThree.PartTwo.map_centralizer_singleton, hψx]

end Inner142

end Res5Types

open Res5Gen Res5Types in
set_option maxHeartbeats 2000000 in
theorem step142TypesHJ_of
    (h131 : Item131) (hrig : KS142J2Rigid)
    (hlist : KS142J2List) : Step142TypesHJ := by
  intro G _ _ A c L h Q hQ hK ⟨φ⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspor := Sec13.sporadicModels131
  have hD := h.toSec13Data
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor hD
    (center_eq_bot_of_mulEquiv φ hspor.2.2.2)
    (not_isLThreePi_of_mulEquiv φ Item148PtRes2.not_isoLThreePi_J2)
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hEb
  have hE9 : Nat.card Eb = 9 := card_image_inf h h9
  have hφE : Eb.map (MulEquiv.refl (↥L ⧸ θ)).toMonoidHom = Eb := by
    ext x
    simp
  have hcent := cent_of_rigid h (MulEquiv.refl (↥L ⧸ θ)) hφE
    fun τ hτ n hn hτn => hrig (↥L ⧸ θ) ⟨φ⟩ Eb hE9 τ hτ n hn hτn
  have d : Inner142 A c L := ⟨h, hAc, hK, hcent⟩
  have : (ker142 A (lB A) c).Normal := ker142_normal hD.isElemAbelian.1 hD.mem_A
  obtain ⟨hQL, hQ3, hQE, hQmax⟩ := d.maximal_bar hQ
  set Qb := d.bar (img142 A (lB A) c Q) with hQb
  obtain ⟨⟨T, ⟨eT⟩⟩, a, ha, b, hb, e, he, hab, he1, ⟨S, heS, hSC⟩, hae, hbe, hY⟩ :=
    hlist (↥L ⧸ θ) ⟨φ⟩ Eb hE9 Qb hQ3 hQE fun Y' h3 hN hle => hQmax Y' h3 hN hle
  have hlift : ∀ x ∈ Eb, ∃ β : G, ∃ hβ : β ∈ A ⊓ L, QuotientGroup.mk' θ ⟨β, hβ.2⟩ = x := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, Subgroup.mem_subgroupOf.mp hβ, rfl⟩
  obtain ⟨βa, hβa, rfl⟩ := hlift a ha
  obtain ⟨βb, hβb, rfl⟩ := hlift b hb
  obtain ⟨βe, hβe, rfl⟩ := hlift e he
  have halpha_mem : ∀ (β : G) (hβ : β ∈ A ⊓ L),
      alpha142 A (lB A) c β hβ.1 ∈ img142 A (lB A) c L := fun β hβ =>
    ⟨⟨β, Subgroup.mem_sup_right hβ.1⟩, Subgroup.mem_subgroupOf.mpr hβ.2, rfl⟩
  have halpha_bar : ∀ (β : G) (hβ : β ∈ A ⊓ L),
      d.lbarEquiv.symm ⟨alpha142 A (lB A) c β hβ.1, halpha_mem β hβ⟩ =
        QuotientGroup.mk' θ ⟨β, hβ.2⟩ := by
    intro β hβ
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (d.lbarEquiv_mk ⟨β, hβ.2⟩).symm
  have hzp : ∀ (β β' : G) (hβ : β ∈ A ⊓ L) (hβ' : β' ∈ A ⊓ L),
      Subgroup.zpowers (QuotientGroup.mk' θ ⟨β, hβ.2⟩) ≠
        Subgroup.zpowers (QuotientGroup.mk' θ ⟨β', hβ'.2⟩) →
      Subgroup.zpowers (alpha142 A (lB A) c β hβ.1) ≠
        Subgroup.zpowers (alpha142 A (lB A) c β' hβ'.1) := by
    intro β β' hβ hβ' hne heq
    apply hne
    have h1 := congrArg d.bar heq
    rwa [d.bar_zpowers (halpha_mem β hβ), d.bar_zpowers (halpha_mem β' hβ'), halpha_bar β hβ,
      halpha_bar β' hβ'] at h1
  have hθa := d.thetaC_bar βa hβa
  have hθb := d.thetaC_bar βb hβb
  refine ⟨⟨T, ⟨((d.nonempty_bar_equiv hQL).some).trans eT⟩⟩, βa, hβa.1, βb, hβb.1, βe, hβe.1,
    ?_, ?_, ?_, hzp βa βe hβa hβe hae, hzp βb βe hβb hβe hbe, ?_⟩
  · refine d.bar_injective ((Subgroup.closure_le _).mpr ?_) d.img_A_le ?_
    · rintro _ (rfl | rfl)
      · exact halpha_mem βa hβa
      · exact halpha_mem βb hβb
    · rw [d.bar_closure_pair (halpha_mem βa hβa) (halpha_mem βb hβb), halpha_bar βa hβa,
        halpha_bar βb hβb, d.bar_A, ← hEb, hab]
  · intro h1
    apply he1
    have h2 : (⟨alpha142 A (lB A) c βe hβe.1, halpha_mem βe hβe⟩ :
        ↥(img142 A (lB A) c L)) = 1 := Subtype.ext h1
    rw [← halpha_bar βe hβe, h2, map_one]
  · refine d.isThreeCentralIn_of_bar (halpha_mem βe hβe) S ?_ ?_
    · rw [halpha_bar βe hβe]
      exact heS
    · rw [halpha_bar βe hβe]
      exact hSC
  · have hle : thetaC142 A (lB A) c (alpha142 A (lB A) c βa hβa.1) ⊔
        thetaC142 A (lB A) c (alpha142 A (lB A) c βb hβb.1) ≤ img142 A (lB A) c L :=
      sup_le hθa.1 hθb.1
    refine d.bar_injective hQL (sup_le hle (inf_le_left.trans hQL)) ?_
    rw [d.bar_sup hle (inf_le_left.trans hQL), d.bar_sup hθa.1 hθb.1, hθa.2, hθb.2,
      d.bar_inf_centralizer _ (halpha_mem βe hβe), halpha_bar βe hβe, ← hQb]
    exact hY

end CFSG.RankThree.PartTwo.Sec14
