module

public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftIndex
public import CFSG.Quasithin.EmptyFaithful.S14610Hat6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

variable {G : Type} [Group G] [Finite G]

theorem not_le_of_decomposition {T M H : Subgroup G} {u : G} {I I₂ K : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hKI : K ≤ I) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hT : F6.IsGoldschmidtTripleIn I (i1Of1469 T M I) I₂)
    (hint : imgMod3 I (i1Of1469 T M I) ⊓ imgMod3 I I₂ =
      imgMod3 I (i1Of1469 T M I ⊓ I₂))
    {Zb : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)} (hZn : Zb.Normal)
    (hdec : (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)) =
      imgMod3 I K ⊔ Zb ⊔ (imgMod3 I (i1Of1469 T M I) ⊓ imgMod3 I I₂))
    (hZ : ¬ twoResidual (imgMod3 I (i1Of1469 T M I)) ≤ Zb) : ¬ K ≤ M := by
  have S : Setting146 G T M := c.setting
  set I₁ := i1Of1469 T M I with hI₁
  have hI₁I : I₁ ≤ I := i1Of1469_le T M I
  have hTI₁ : T ⊓ I ≤ I₁ := le_sup_right
  have hinf : I₁ ⊓ I₂ = T ⊓ I := inf_eq_of_isSylowTwoOf hT hsyl hTI₁ c.le_I₂
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  set Z' : Subgroup ↥I := Zb.comap π with hZ'
  set P : Subgroup G := Z'.map I.subtype with hP
  have hPI : P ≤ I := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hZ'n : Z'.Normal := hZn.comap π
  have hPsub : P.subgroupOf I = Z' := Subgroup.comap_map_eq_self_of_injective I.subtype_injective Z'
  have hPnorm : I ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPI).mp (hPsub ▸ hZ'n)
  have hc3 := c.c3 P hPI (hI₁I.trans hPnorm)
  have hPM : P ≤ M := by
    rcases hc3 with hL | hP'
    · exfalso
      apply hZ
      set G₁ := I₁.subgroupOf I with hG₁
      have hres : twoResidual G₁ ≤ Z' := by
        intro x hx
        have hx1 : (x : G) ∈ twoResidual I₁ := by
          have h1 := E1.map_twoResidual I.subtype G₁
          rw [hG₁, Subgroup.map_subgroupOf_eq_of_le hI₁I] at h1
          rw [← h1]
          exact Subgroup.mem_map_of_mem _ hx
        rw [F6.twoResidual_eq_oTwoUpper] at hx1
        have hx2 : (x : G) ∈ P := hL (S.oTwoUpper_i1Of1469_le I hx1)
        obtain ⟨y, hy, hyx⟩ := hx2
        have : y = x := Subtype.ext hyx
        exact this ▸ hy
      have h2 := E1.map_twoResidual π G₁
      show twoResidual (G₁.map π) ≤ Zb
      rw [← h2]
      rintro _ ⟨x, hx, rfl⟩
      exact hres hx
    · exact fun x hx => (hP' hx).1
  intro hKM
  apply c.hI.1.2.2
  set K' := K.subgroupOf I with hK'
  have hker : π.ker ≤ Z' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    show π x ∈ Zb
    rw [hx]
    exact Zb.one_mem
  have hdec' : K' ⊔ Z' ⊔ (I₁ ⊓ I₂).subgroupOf I = ⊤ := by
    have hmapY : (K' ⊔ Z' ⊔ (I₁ ⊓ I₂).subgroupOf I).map π = ⊤ := by
      rw [Subgroup.map_sup, Subgroup.map_sup,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      have h1 : ((I₁ ⊓ I₂).subgroupOf I).map π = imgMod3 I (I₁ ⊓ I₂) := rfl
      have h2 : K'.map π = imgMod3 I K := rfl
      rw [h1, h2, ← hint]
      exact hdec.symm
    have hcomap := congrArg (Subgroup.comap π) hmapY
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr (hker.trans (le_sup_of_le_left le_sup_right)),
      Subgroup.comap_top] at hcomap
    exact hcomap
  have hmap := congrArg (Subgroup.map I.subtype) hdec'
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le hKI,
    Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hI₁I)] at hmap
  rw [← hmap]
  refine sup_le (sup_le hKM hPM) ?_
  rw [hinf]
  exact inf_le_left.trans S.hyp.m_max.1.2

end Gold14610

end CFSG.Quasithin
