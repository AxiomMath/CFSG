module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_six_nonswap (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 2) (hp : (3 : ℕ) ∈ D.sig)
    (hLc : Subgroup.center ↥(lBar ⊥ V hV L) = ⊥) {J₀ J₁ : Subgroup (Vtil ⊥ V hV)}
    (hJ₀ : XMod.IsIrr ↥(lBar ⊥ V hV L) J₀) (hJ₁ : XMod.IsIrr ↥(lBar ⊥ V hV L) J₁)
    (hinf : J₀ ⊓ J₁ = ⊥) (hsup : J₀ ⊔ J₁ = wTil ⊥ V hV L)
    (hE₀ : Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₀)
    (hE₁ : Z391.EndUnitsTrivial (lBar ⊥ V hV L) J₁)
    (hψ₃ : ∀ n ∈ J₀, n ≠ 1 → ∃ ψ ∈ lBar ⊥ V hV L, orderOf ψ = 3 ∧ ψ n = n)
    {z : MulAut (Vtil ⊥ V hV)} (hz3 : z ^ 3 = 1)
    (hzL : ∀ l ∈ lBar ⊥ V hV L, z * l = l * z)
    (hzW : (J₀ ⊔ J₁).map z.toMonoidHom = J₀ ⊔ J₁) (hzne : ∃ u ∈ J₀ ⊔ J₁, z u ≠ u)
    (hall : ∀ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T),
      (lBar ⊥ V hV L).map (MulAut.conj w).toMonoidHom = lBar ⊥ V hV L) :
    Insp1613U D V := by
  have h : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hH : Hyp151 D ⊥ V L := hc.setting.hyp151
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hH.le
  obtain ⟨k, hkle, hk0, hkst⟩ := s16c13bcA_stable_member_le hJ₀ hJ₁ hinf hE₀ hE₁ hz3 hzL hzW hzne
    (s16c13bcA_wBar_isPGroup D hV) (fun w hw => s16c13bcA_mem_normalizer_of_map_eq (hall w hw))
    (fun w hw => by rw [hsup]; exact s16c13bcA_wTil_map_eq ⊥ V hV L (hall w hw))
  obtain ⟨n, hnJ, hn1, hnfix⟩ := s16_LemmaP_exists_fixed (s15_Infra_vtil_sq_eq_one ⊥ V hV)
    (s16c13bcA_wBar_isPGroup D hV) hk0 (fun w hw x hx => by
      have h1 : w x ∈ (J₀.map (z ^ k).toMonoidHom).map w.toMonoidHom := ⟨x, hx, rfl⟩
      rwa [hkst w hw] at h1)
  obtain ⟨ψ, hψL, hψo, hψn⟩ := s16c13bcA_six_psi hψ₃ hzL hnJ hn1
  obtain ⟨g, hgM, -, hgcomm, hfix⟩ := s16c13bcA_exists_other_conj D hV hH hs
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hψ'B : g * ψ * g⁻¹ ∈ (lBar ⊥ V hV L).map (MulAut.conj g).toMonoidHom := ⟨ψ, hψL, rfl⟩
  have hψ'o : orderOf (g * ψ * g⁻¹) = 3 := by
    have h1 := orderOf_injective (MulAut.conj g).toMonoidHom hinj ψ
    rw [hψo] at h1
    exact h1
  have hψ1 : ψ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hψo
    omega
  have hψ'1 : g * ψ * g⁻¹ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hψ'o
    omega
  obtain ⟨hab, hne⟩ := s16c13bcA_pair_of_conj hgcomm hLc hψL hψ'B hψ'1
  have hnW : n ∈ wTil ⊥ V hV L := hsup ▸ hkle hnJ
  have hψ'M : g * ψ * g⁻¹ ∈ Mbar D.M ⊥ V hV :=
    (Mbar D.M ⊥ V hV).mul_mem ((Mbar D.M ⊥ V hV).mul_mem hgM (hLM hψL))
      ((Mbar D.M ⊥ V hV).inv_mem hgM)
  exact s16c13bcA_insp_of_pair D h hp (hLM hψL) hψ'M hψo hψ'o hab hne hn1 (mem_fixV.2 hnfix)
    hψn (hfix _ hψ'B n hnW)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
