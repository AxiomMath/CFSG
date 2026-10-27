module

public import CFSG.Quasithin.Background.C116Three.GroupDefs

import CFSG.Quasithin.EmptyFaithful.SBc13ACComp
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.C1GNA7Base

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem groupPair_conj_dichotomy {Q : Type} [Group Q] [Finite Q] {K : Subgroup Q} {t₀ tb : Q}
    (hK : K ∈ cComp (⊤ : Subgroup Q))
    (hconj : conjClosure K ⊤ = K ⊔ K.map (MulAut.conj t₀).toMonoidHom)
    (htbN : tb ∉ Subgroup.normalizer (K : Set Q)) :
    K.map (MulAut.conj tb).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom ∧
      ∀ c : Q, K.map (MulAut.conj c).toMonoidHom = K ∨
        K.map (MulAut.conj c).toMonoidHom = K.map (MulAut.conj tb).toMonoidHom := by
  have hsub : ∀ c : Q, K.map (MulAut.conj c).toMonoidHom ≤ conjClosure K ⊤ := by
    intro c y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact mem_conjClosure (Subgroup.mem_top c) hz
  have hcj : ∀ c : Q, K.map (MulAut.conj c).toMonoidHom ∈ cComp (⊤ : Subgroup Q) :=
    fun c => map_conj_mem_cComp hK (Subgroup.mem_top c)
  have hpair : ∀ c : Q, K.map (MulAut.conj c).toMonoidHom = K ∨
      K.map (MulAut.conj c).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom := fun c =>
    CFSG.Quasithin.SBc13.eq_or_eq_of_mem_cComp_of_le_sup hK (hcj t₀) (hcj c)
      ((hsub c).trans hconj.le)
  have htb : K.map (MulAut.conj tb).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom :=
    (CFSG.Quasithin.SBc13.eq_or_eq_of_mem_cComp_of_le_sup hK (hcj t₀) (hcj tb)
      ((hsub tb).trans hconj.le)).resolve_left
      (fun h => htbN (CFSG.Quasithin.A38.map_conj_eq_iff.mp h))
  refine ⟨htb, fun c => ?_⟩
  rcases hpair c with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans htb.symm)

theorem groupPair (h38 : A38ForSQTK) {H T L : Subgroup G} (hH : CharTwo H) (hT : IsSylowTwoOf T H)
    (hSQ : IsSQTKTC H) (hL : L ∈ cComp H) (hTN : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ t, GroupPair H T L t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hTH : T ≤ H := hT.1
  have hLb := modO2Image_mem_cComp hL
  have hTb := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hT)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  have hQ : SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) :=
    SQTKHyp.of_sqtkGroup ↥H (C1GN.isSQTKTC_iff_sqtkGroup.1 hSQ)
  have hnot : ¬ (modO2Image H L).Normal := fun hnorm => by
    have hn : (L.subgroupOf H).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
        (subgroupOf_mem_cComp hL) hnorm
    exact hTN (hTH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).1 hn))
  obtain ⟨hL1, hL2⟩ := h38 _ hQ _ hLb
  rcases hL1 with hnL | ⟨-, t₀, -, -, -, hconj⟩
  · exact absurd hnL hnot
  rcases hL2 _ hTb with ⟨hnorm, -, -⟩ | ⟨tb, htbT, htbn, -, -, hcomm, -, -, -⟩
  · exact absurd hnorm hnot
  obtain ⟨t', ht'T, rfl⟩ := htbT
  have htT : (t' : G) ∈ T := ht'T
  have ht_not : (t' : G) ∉ Subgroup.normalizer (L : Set G) := by
    intro hN
    apply htbn
    have hs'N : t' ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have := Subgroup.mem_normalizer_iff.mp hN (x : G)
      simpa using this
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨t', hs'N, rfl⟩
  have hLt : L.map (MulAut.conj (t' : G)).toMonoidHom ∈ cComp H :=
    map_conj_mem_cComp hL t'.2
  have hLtH : L.map (MulAut.conj (t' : G)).toMonoidHom ≤ H := le_of_mem_cComp hLt
  obtain ⟨-, hdQ⟩ := groupPair_conj_dichotomy hLb hconj htbn
  have hlift : ∀ y : ↥H, L.map (MulAut.conj (y : G)).toMonoidHom = L ∨
      L.map (MulAut.conj (y : G)).toMonoidHom = L.map (MulAut.conj (t' : G)).toMonoidHom := by
    intro y
    have hLy : L.map (MulAut.conj (y : G)).toMonoidHom ∈ cComp H :=
      map_conj_mem_cComp hL y.2
    rcases hdQ (QuotientGroup.mk' (CFSG.pCore 2 ↥H) y) with h | h
    · exact Or.inl (modO2Image_injOn H hLy hL (by rw [modO2Image_conj y]; exact h))
    · exact Or.inr (modO2Image_injOn H hLy hLt
        (by rw [modO2Image_conj y, modO2Image_conj t']; exact h))
  refine ⟨(t' : G), htT, ht_not, hLt, ?_, fun x hx => hlift ⟨x, hx⟩⟩
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haH : a ∈ H := hLH ha
  have hbH : b ∈ H := hLtH hb
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨a, haH⟩ ∈ modO2Image H L :=
    ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨b, hbH⟩ ∈
      (modO2Image H L).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) t')).toMonoidHom := by
    rw [← modO2Image_conj t']
    exact ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have h3 := Subgroup.commutator_mem_commutator h1 h2
  rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h3
  exact (CFSG.mem_openPCoreOf_iff _).mpr h3

end CFSG.Quasithin.C116Three
