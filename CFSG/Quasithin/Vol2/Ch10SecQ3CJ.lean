module

public import CFSG.Quasithin.Vol2.Ch10SecQ4S8
public import CFSG.Quasithin.Vol2.Ch10SecQ4S5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique SecF.C10P4F

variable {G : Type} [Group G] [Finite G]

theorem exists_le_autI_map' {V H T K : Subgroup G} (hel : IsElemAbelian 2 V)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT2 : IsPGroup 2 T) (hK : K ∈ cComp H)
    (hKT : H = K ⊔ T) (h2J : oTwoUpper H ≤ thompsonJ H)
    {I' : Finset (Subgroup (MulAut (IntMod V hel)))}
    (hJ : autI hel (thompsonJ H) = ⨆ L ∈ I', L)
    (hcomm : ∀ L ∈ I', ∀ L' ∈ I', L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    {K₀ : Subgroup (MulAut (IntMod V hel))} (hK₀ : K₀ ∈ I')
    (hCs : IsSimpleGroup ↥(oTwoUpper K₀))
    (hnc : ∃ a ∈ oTwoUpper K₀, ∃ b ∈ oTwoUpper K₀, a * b ≠ b * a) :
    ∃ t ∈ T, oTwoUpper K₀ ≤ autI hel (K.map (MulAut.conj t).toMonoidHom) := by
  set C := oTwoUpper K₀ with hC
  have hTH : T ≤ H := hKT ▸ le_sup_right
  have hJN : autI hel (thompsonJ H) ≤ Subgroup.normalizer (C : Set _) := by
    rw [hJ]
    refine iSup₂_le fun L hL => ?_
    refine le_trans ?_ (SecF.C10P4F.le_normalizer_oTwoUpper K₀)
    by_cases h : L = K₀
    · rw [h]; exact Subgroup.le_normalizer
    · exact SecE.le_normalizer_of_commute fun a ha b hb => hcomm L hL K₀ hK₀ h a ha b hb
  have hCO : C ≤ autI hel (oTwoUpper H) := by
    have hJH : thompsonJ H ≤ Subgroup.normalizer (V : Set G) := (thompsonJ_le_self H).trans hHN
    calc C ≤ oTwoUpper (autI hel (thompsonJ H)) :=
          oTwoUpper_mono (hJ ▸ le_iSup₂_of_le (f := fun L (_ : L ∈ I') => L) K₀ hK₀ le_rfl)
      _ = autI hel (oTwoUpper (thompsonJ H)) := SecE.oTwoUpper_autI hel hJH
      _ ≤ autI hel (oTwoUpper H) := autI_mono hel (oTwoUpper_mono (thompsonJ_le_self H))
  set N := conjClosure K T with hN
  have hNT : T ≤ Subgroup.normalizer (N : Set G) := le_normalizer_conjClosure K T
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hNH : N ≤ H := conjClosure_le fun t ht k hk =>
    H.mul_mem (H.mul_mem (hTH ht) (hKH hk)) (H.inv_mem (hTH ht))
  have hHeq : H = N ⊔ T :=
    le_antisymm (hKT ▸ sup_le_sup_right (le_conjClosure K T) T) (sup_le hNH hTH)
  have hOH : oTwoUpper H ≤ N := by
    rw [hHeq, SecB.oTwoUpper_sup_eq hT2 hNT]
    exact oTwoUpper_le N
  have hKs : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom ∈ cComp H := fun t ht =>
    H13.LocDbl.map_conj_mem_cComp hK (Subgroup.le_normalizer (hTH ht))
  by_contra hno
  push Not at hno
  have hcent : ∀ t ∈ T, ∀ a ∈ C, ∀ b ∈ autI hel (K.map (MulAut.conj t).toMonoidHom),
      a * b = b * a := by
    intro t ht
    have hKtN : N ≤ Subgroup.normalizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) :
        Set G) := conjClosure_le fun s hs k hk =>
      le_normalizer_of_mem_cComp (hKs t ht) (hKs s hs) ⟨k, hk, rfl⟩
    have hCN : C ≤ Subgroup.normalizer (autI hel (K.map (MulAut.conj t).toMonoidHom) : Set _) :=
      hCO.trans ((autI_mono hel hOH).trans (autI_le_normalizer hel hKtN))
    have hKtJ : K.map (MulAut.conj t).toMonoidHom ≤ thompsonJ H := by
      have h1 := oTwoUpper_mono (le_of_mem_cComp (hKs t ht))
      rw [← eq_oTwoUpper_of_perfect (perfect_of_mem_cComp (hKs t ht))] at h1
      exact h1.trans h2J
    have hi := (SecE.inf_eq_bot_or_le hCs hCN).resolve_right (hno t ht)
    exact SecE.commute_of_inf_eq_bot hi hCN ((autI_mono hel hKtJ).trans hJN)
  have hNP : N ≤ preI hel H hHN (Subgroup.centralizer (C : Set _)) := by
    refine conjClosure_le fun t ht k hk => ?_
    have hx : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
    have hxH : t * k * t⁻¹ ∈ H := le_of_mem_cComp (hKs t ht) hx
    refine (mem_preI hel).2 ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    rw [convHom_apply]
    exact hcent t ht a ha _ (convI_mem_autI hel hx _)
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  apply hab
  have hbP : b ∈ autI hel (preI hel H hHN (Subgroup.centralizer (C : Set _))) :=
    autI_mono hel (hOH.trans hNP) (hCO hb)
  obtain ⟨g, hgP, rfl⟩ := (mem_autI hel).1 hbP
  obtain ⟨hgH, hgc⟩ := (mem_preI hel).1 hgP
  rw [convHom_apply] at hgc
  exact Subgroup.mem_centralizer_iff.mp hgc a ha

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
