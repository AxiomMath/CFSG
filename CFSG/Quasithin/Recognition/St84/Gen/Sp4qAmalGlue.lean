module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport

import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalModel
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalBorel
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDC
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalField
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalLocal
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSylow
import CFSG.Quasithin.Recognition.St84.Gen.AmalGlueDC
import CFSG.GH74.QTGen4.DSGen4.L34Generic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (radA1 radA2 card_radicals elementary_le_radA1_or_radA2)
open CFSG.Quasithin.H13.F431.SpModel CFSG.QuasithinUnique.Fin257.Sp4
open CFSG.GH74.QTGen4.DSGen4.L34

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem exists_image_pCoreOf_left (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (ψ : ↥(L2 ⊔ bigB L1 L2 S) ≃*
      ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f)))))
    (hS : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ x : ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))))) :
        antiSp (GaloisField 2 f)) ∈ antiUnipotent (GaloisField 2 f)) :
    ∃ E : Subgroup (antiSp (GaloisField 2 f)),
      E ≤ antiUnipotent (GaloisField 2 f) ∧ (∀ z ∈ E, z * z = 1) ∧
        Nat.card E = Nat.card (GaloisField 2 f) ^ 3 ∧
        (∀ y : ↥(L2 ⊔ bigB L1 L2 S), (y : G) ∈ pCoreOf 2 L1 ↔
          ((ψ y : ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) :
            Set (antiSp (GaloisField 2 f))))) : antiSp (GaloisField 2 f)) ∈ E) ∧
        (E = radA1 (GaloisField 2 f) ∨ E = radA2 (GaloisField 2 f)) := by
  classical
  let F := GaloisField 2 f
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q1 : Subgroup G := pCoreOf 2 L1
  let M2 : Subgroup (antiSp F) := Subgroup.normalizer (radA2 F : Set (antiSp F))
  let ι : ↥P2 →* antiSp F := M2.subtype.comp ψ.toMonoidHom
  have hιinj : Function.Injective ι := M2.subtype_injective.comp ψ.injective
  have hQ1P2 : Q1 ≤ P2 :=
    hH.pCoreOf_le_left.trans ((hD.le_right hH).trans le_sup_left)
  set E : Subgroup (antiSp F) := (Q1.subgroupOf P2).map ι with hE
  have hEmem : ∀ y : ↥P2, (y : G) ∈ Q1 ↔ ι y ∈ E := by
    intro y
    rw [hE, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      rw [hιinj hzy] at hz
      exact Subgroup.mem_subgroupOf.mp hz
  have hEU : E ≤ antiUnipotent F := by
    intro z hz
    rw [hE] at hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact (hS y).1 (hH.pCoreOf_le_left (Subgroup.mem_subgroupOf.mp hy))
  have hEsq : ∀ z ∈ E, z * z = 1 := by
    intro z hz
    rw [hE] at hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hy2 : y ^ 2 = 1 :=
      Subtype.ext (by simpa using hD.elem_left.2 (y : G) (Subgroup.mem_subgroupOf.mp hy))
    have h2 : ι y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    simpa [pow_two] using h2
  have hFcard : Nat.card F = 2 ^ f :=
    GaloisField.card (p := 2) (n := f) (by have h := hD.one_le; omega)
  have hEcard : Nat.card E = Nat.card F ^ 3 := by
    have h1 : Nat.card E = Nat.card Q1 := by
      rw [hE, Subgroup.card_map_of_injective hιinj]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ1P2).toEquiv
    calc Nat.card E = Nat.card Q1 := h1
      _ = 2 ^ (3 * f) := hD.card_left
      _ = (2 ^ f) ^ 3 := by rw [← pow_mul]; congr 1; omega
      _ = Nat.card F ^ 3 := by rw [hFcard]
  have hradA1 : Nat.card (radA1 F) = Nat.card F ^ 3 := (card_radicals (K := F)).2.1
  have hradA2 : Nat.card (radA2 F) = Nat.card F ^ 3 := (card_radicals (K := F)).2.2.1
  rcases elementary_le_radA1_or_radA2 (K := F) hEU hEsq with h1 | h2
  · exact ⟨E, hEU, hEsq, hEcard, hEmem,
      Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [hEcard, hradA1]))⟩
  · exact ⟨E, hEU, hEsq, hEcard, hEmem,
      Or.inr (Subgroup.eq_of_le_of_card_ge h2 (by rw [hEcard, hradA2]))⟩

theorem Sp4qLocalData.map_pCoreOf_left_eq_radA1 (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (ψ : ↥(L2 ⊔ bigB L1 L2 S) ≃*
      ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f)))))
    (hQ2 : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L2 ↔
      ((ψ x : ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))))) :
        antiSp (GaloisField 2 f)) ∈ radA2 (GaloisField 2 f))
    (hS : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
      ((ψ x : ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))))) :
        antiSp (GaloisField 2 f)) ∈ antiUnipotent (GaloisField 2 f)) :
    ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L1 ↔
      ((ψ x : ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))))) :
        antiSp (GaloisField 2 f)) ∈ radA1 (GaloisField 2 f) := by
  obtain ⟨E, -, -, -, hEmem, hE | hE⟩ := exists_image_pCoreOf_left hH hD ψ hS
  · intro x
    have h := hEmem x
    rw [hE] at h
    exact h
  · exfalso
    apply hD.pCoreOf_ne
    ext g
    constructor
    · intro hg
      have hgP2 : g ∈ L2 ⊔ bigB L1 L2 S :=
        hH.pCoreOf_le_left.trans ((hD.le_right hH).trans le_sup_left) hg
      have hm : ((ψ ⟨g, hgP2⟩ : ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) :
          Set (antiSp (GaloisField 2 f))))) : antiSp (GaloisField 2 f)) ∈ E :=
        (hEmem ⟨g, hgP2⟩).1 hg
      rw [hE] at hm
      exact (hQ2 ⟨g, hgP2⟩).2 hm
    · intro hg
      have hgP2 : g ∈ L2 ⊔ bigB L1 L2 S :=
        Subgroup.mem_sup_left ((CFSG.LieType.BorelTits.pCoreOf_le 2 L2) hg)
      have hm : ((ψ ⟨g, hgP2⟩ : ↥(Subgroup.normalizer (radA2 (GaloisField 2 f) :
          Set (antiSp (GaloisField 2 f))))) : antiSp (GaloisField 2 f)) ∈ E := by
        rw [hE]
        exact (hQ2 ⟨g, hgP2⟩).1 hg
      exact (hEmem ⟨g, hgP2⟩).2 hm

private theorem mem_other_iff_of_mem_normalizer {G Y : Type} [Group G] [Group Y]
    {P P' B S : Subgroup G} {M M' U : Subgroup Y} (ψ : ↥P ≃* ↥M)
    (hψN : ∀ x : ↥P, (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((ψ x : ↥M) : Y) ∈ Subgroup.normalizer (U : Set Y))
    (hB : B = P ⊓ Subgroup.normalizer (S : Set G))
    (hinf : P ⊓ P' = B)
    (hN : Subgroup.normalizer (U : Set Y) = M ⊓ M') :
    ∀ x : ↥P, (x : G) ∈ P' ↔ ((ψ x : ↥M) : Y) ∈ M' := by
  intro x
  constructor
  · intro hx
    have hx' : (x : G) ∈ P ⊓ P' := ⟨x.2, hx⟩
    rw [hinf, hB] at hx'
    have hψ : ((ψ x : ↥M) : Y) ∈ Subgroup.normalizer (U : Set Y) := (hψN x).mp hx'.2
    rw [hN] at hψ
    exact hψ.2
  · intro hx
    have hxM : ((ψ x : ↥M) : Y) ∈ M := (ψ x).2
    have hψ : ((ψ x : ↥M) : Y) ∈ Subgroup.normalizer (U : Set Y) := by
      rw [hN]
      exact ⟨hxM, hx⟩
    have hxN : (x : G) ∈ Subgroup.normalizer (S : Set G) := (hψN x).mpr hψ
    have hxB : (x : G) ∈ B := by
      rw [hB]
      exact ⟨x.2, hxN⟩
    have hx' : (x : G) ∈ P ⊓ P' := by
      rw [hinf]
      exact hxB
    exact hx'.2

private theorem isAmalgamOfGroup_sp4_of_amalgam_iso (hf : 2 ≤ f)
    (hiso : Nonempty ((RankTwoAmalgam.ofSubgroups
      (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)).Iso
      (RankTwoAmalgam.ofSubgroups
        (Subgroup.normalizer (radA1 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))))
        (Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))))))) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over f) := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card (p := 2) (n := f) (by omega)
  refine ⟨antiSp (GaloisField 2 f), inferInstance,
    Or.inr ⟨hf, lieModel_Sp (K := GaloisField 2 f) (n := f) hf hcard⟩,
    antiUnipotent (GaloisField 2 f), ?_⟩
  refine ⟨Subgroup.normalizer (radA1 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))),
    Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))), ?_, ?_⟩
  · exact isYAmalgamPair_of_borelData
      (borel_antiSp (F := GaloisField 2 f) (n := f) hf hcard)
      (O2_antiSp (F := GaloisField 2 f) (n := f) hf hcard)
  · simpa [f112Amalgam] using hiso

theorem isAmalgamOfGroup_sp4_of_dcSp4 (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (hDC : DCProp
      (Subgroup.normalizer (radA1 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))))
      (Subgroup.normalizer (radA2 (GaloisField 2 f) : Set (antiSp (GaloisField 2 f))))) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over f) := by
  classical
  let F := GaloisField 2 f
  let M1 : Subgroup (antiSp F) := Subgroup.normalizer (radA1 F : Set (antiSp F))
  let M2 : Subgroup (antiSp F) := Subgroup.normalizer (radA2 F : Set (antiSp F))
  let U : Subgroup (antiSp F) := antiUnipotent F
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q1 : Subgroup G := pCoreOf 2 L1
  have hR : Hyp111R L1 L2 S := hD.hyp111R hf hH
  have hcard : Nat.card F = 2 ^ f := GaloisField.card (p := 2) (n := f) (by omega)
  have hbigB1 : bigB L1 L2 S = P1 ⊓ Subgroup.normalizer (S : Set G) := by
    have h := bigB_eq_parabolic_inf hR
    rwa [inf_eq_left.mpr (hD.le_left hH)] at h
  have hbigB2 : bigB L1 L2 S = P2 ⊓ Subgroup.normalizer (S : Set G) := by
    have h := bigB_eq_parabolic_inf hR.symm
    rw [bigB_comm L1 L2 S, inf_eq_left.mpr (hD.le_right hH)] at h
    exact h
  have hN : Subgroup.normalizer (U : Set (antiSp F)) = M1 ⊓ M2 := by
    simpa [U, M1, M2, Sp44.B0] using
      (normalizer_radA1_inf_normalizer_radA2 (F := F) (n := f) hf hcard).symm
  obtain ⟨ψ₁, hψ₁Q, hψ₁S, hψ₁N⟩ :=
    (hD.isLinSemidirect_left hH (hD.linAction_left hf hH)).exists_mulEquiv_sylow
      (isLinSemidirect_radA1 (F := F) (n := f) hf hcard)
      (hD.isSylowTwoOf_sup_bigB_left hH)
      (isSylowTwoOf_antiUnipotent_normalizer_radA1 (F := F) (n := f) hf hcard)
  obtain ⟨ψ₂, hψ₂Q, hψ₂S, hψ₂N⟩ :=
    (hD.isLinSemidirect_right hH (hD.linAction_right hf hH)).exists_mulEquiv_sylow
      (isLinSemidirect_radA2 (F := F) (n := f) hf hcard)
      (hD.isSylowTwoOf_sup_bigB_right hH)
      (isSylowTwoOf_antiUnipotent_normalizer_radA2 (F := F) (n := f) hf hcard)
  have hB1 : ∀ x : ↥P1, (x : G) ∈ P2 ↔ ((ψ₁ x : ↥M1) : antiSp F) ∈ M2 :=
    mem_other_iff_of_mem_normalizer ψ₁ hψ₁N hbigB1 (parabolic_inf_parabolic hR) hN
  have hB2 : ∀ x : ↥P2, (x : G) ∈ P1 ↔ ((ψ₂ x : ↥M2) : antiSp F) ∈ M1 :=
    mem_other_iff_of_mem_normalizer ψ₂ hψ₂N hbigB2
      ((inf_comm P2 P1).trans (parabolic_inf_parabolic hR))
      (hN.trans (inf_comm M1 M2))
  have hQ1 : ∀ x : ↥P1, (x : G) ∈ Q1 ↔
      ((ψ₁ x : ↥M1) : antiSp F) ∈ pCoreOf 2 M1 := by
    intro x
    rw [pCoreOf_normalizer_radA1 (F := F) (n := f) hf hcard]; exact hψ₁Q x
  have hQ1' : ∀ x : ↥P2, (x : G) ∈ Q1 ↔
      ((ψ₂ x : ↥M2) : antiSp F) ∈ pCoreOf 2 M1 := by
    intro x
    rw [pCoreOf_normalizer_radA1 (F := F) (n := f) hf hcard]
    exact hD.map_pCoreOf_left_eq_radA1 hH ψ₂ hψ₂Q hψ₂S x
  have hiso : Nonempty ((RankTwoAmalgam.ofSubgroups P1 P2).Iso
      (RankTwoAmalgam.ofSubgroups M1 M2)) :=
    amalgam_iso_of_dcProp hDC ψ₁ ψ₂ hB1 hB2 hQ1 hQ1'
  exact isAmalgamOfGroup_sp4_of_amalgam_iso hf hiso

theorem isAmalgamOfGroup_sp4_of_sp4qLocalData (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over f) := by
  refine isAmalgamOfGroup_sp4_of_dcSp4 (by omega) hH hD (dcSp4_of_eight_le ?_)
  rw [GaloisField.card (p := 2) (n := f) (by omega)]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

end CFSG.Quasithin.F112R.St84
