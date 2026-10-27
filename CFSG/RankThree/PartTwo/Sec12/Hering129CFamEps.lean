module

import CFSG.RankThree.PartTwo.Sec12.Hering129CRed1
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam0

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Ronan148S

namespace Hering129C

section Eps

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb} {T : Type} [Group T]

theorem census_false_of_eps_model (hD : Census129 c a I X f) (ψ : Q ≃* T) {x : T}
    (hx : ψ c = x) (F : Subgroup T) (hFI : F ≤ I.map ψ.toMonoidHom)
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) (hxF : x ∈ F) (n : T)
    (hn : n ∈ Subgroup.normalizer (F : Set T))
    (hns : n ∉ Subgroup.normalizer (Subgroup.zpowers x : Set T)) : False := by
  subst hx
  set F' : Subgroup Q := F.map ψ.symm.toMonoidHom with hF'
  have hF'I : F' ≤ I := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hFI hy
    have : ψ.symm y = z := by
      rw [← hzy]
      exact ψ.symm_apply_apply z
    show ψ.symm y ∈ I
    rw [this]
    exact hz
  have hcF' : c ∈ F' := ⟨ψ c, hxF, ψ.symm_apply_apply c⟩
  have h := hD.eps F' hF'I (CFSG.Open.IsElemAbelian.map hFe _)
    (by rw [Subgroup.card_map_of_injective ψ.symm.injective, hF9]) hcF'
  have hn' : ψ.symm n ∈ Subgroup.normalizer (F' : Set Q) := by
    rw [hF', ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨n, hn, rfl⟩
  have h2 := h hn'
  apply hns
  have h3 : n ∈ (Subgroup.normalizer (Subgroup.zpowers c : Set Q)).map ψ.toMonoidHom :=
    ⟨ψ.symm n, h2, by simp⟩
  rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers] at h3
  exact h3

end Eps

section Centralizer

variable {S Lb : Type} [Group S] [Finite S] [Group Lb] {s : S} {J : Subgroup S} {g : ↥J →* Lb}

theorem PPair.eq_centralizer_of_card (h : PPair s J g) {M B : ℕ}
    (hC : Nat.card (Subgroup.centralizer ({s} : Set S)) = M) (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : ∀ t ∈ typeOrders425 M B, t = M) : J = Subgroup.centralizer ({s} : Set S) := by
  haveI := h.finite_Lb
  have hM := hfree _ (card_mem_typeOrders425 h.quasisimple_Lb hM0 hB
    (isType425_of_isType122 h.type_Lb) (h.card_Lb_dvd.trans hC.dvd))
  have hLJ : Nat.card Lb ∣ Nat.card J := Subgroup.card_dvd_of_surjective h.surjective
  have hle : Nat.card (Subgroup.centralizer ({s} : Set S)) ≤ Nat.card J := by
    rw [hC, ← hM]
    exact Nat.le_of_dvd Nat.card_pos hLJ
  exact Subgroup.eq_of_le_of_card_ge h.le_centralizer hle

end Centralizer

section Eq

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb} {T : Type} [Group T]

theorem census_map_eq_centralizer_of_quasisimple (hD : Census129 c a I X f) (ψ : Q ≃* T)
    {x : T} (hx : ψ c = x) (hCq : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({x} : Set T))) :
    I.map ψ.toMonoidHom = Subgroup.centralizer ({x} : Set T) := by
  subst hx
  have hCmap : (Subgroup.centralizer ({c} : Set Q)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ c} : Set T) :=
    Sec4.Ronan148S.map_centralizer_singleton_equiv ψ c
  have hKC : I.map ψ.toMonoidHom ≤ Subgroup.centralizer ({ψ c} : Set T) := by
    rw [← hCmap]
    exact Subgroup.map_mono hD.le_centralizer
  haveI := hD.isPerfect
  have hKp : Group.IsPerfect ↥(I.map ψ.toMonoidHom) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom.subgroupMap I)
      (ψ.toMonoidHom.subgroupMap_surjective I)
  have hnt : Nontrivial ↥(I.map ψ.toMonoidHom) :=
    ⟨⟨⟨ψ c, c, hD.c_mem, rfl⟩, 1, fun h => c_ne_one hD (ψ.injective
      (by simpa using congrArg Subtype.val h))⟩⟩
  have hsub := isSubnormal_map_subgroupOf ψ.toMonoidHom hD.le_centralizer hD.isSubnormal
  rw [hCmap] at hsub
  exact Sec4.Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hKC hCq hKp hnt hsub

end Eq

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
