module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelOuter
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G} {S : Type} [Group S]
  {ψ : ↥(kGenIn V H) →* S} {ρ : ↥H →* MulAut S} {t₀ : S}

namespace Borel86Data

theorem conj_le_sup_ker (hD : Borel86Data V H T S ψ ρ t₀) {g : G}
    (hUT : conjSubgroup V g ≤ T) :
    conjSubgroup V g ≤ kGenIn V H ⊔ ρ.ker.map H.subtype := by
  intro u hu
  have huH : u ∈ H := hD.hyp.T_le_H (hUT hu)
  obtain ⟨s, hs⟩ := hD.rho_mem_range_conj hUT ⟨u, huH⟩ hu
  obtain ⟨k, rfl⟩ := hD.surj s
  have hkH : (k : G) ∈ H := hD.kGenIn_le k.2
  have hρk : ρ ⟨k, hkH⟩ = MulAut.conj (ψ k) := hD.rho_eq_conj ⟨k, hkH⟩ k rfl
  have hker : (⟨k, hkH⟩ : ↥H)⁻¹ * ⟨u, huH⟩ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρk, ← hs, inv_mul_cancel]
  have hu' : u = (k : G) * (((⟨k, hkH⟩ : ↥H)⁻¹ * ⟨u, huH⟩ : ↥H) : G) := by
    simp
  rw [hu']
  exact mul_mem (mem_sup_left k.2) (mem_sup_right ⟨_, hker, rfl⟩)

theorem false_of_normalizersInMTwo (hD : Borel86Data V H T S ψ ρ t₀)
    (hN : NormalizersInMTwo V H (E3.wClos V 0 T)) : False := by
  have hKH : kGenIn V H ≤ H := hD.kGenIn_le
  have hKn : H ≤ Subgroup.normalizer (kGenIn V H : Set G) :=
    hD.hyp.le_normalizer_kGenIn_of_eq_sup hD.eq_sup
  obtain ⟨y, hyR, hyt⟩ := exists_mem_normalizer_inf_not_fix hKH hKn hD.hyp.sylow_H hD.surj
    hD.act (fun h hh => hD.rho_apply_eq_of_mem_normalizer h (hD.hyp.T_le_normalizer hh))
    hD.lie.borel
  have hA : ∀ A ∈ E3.gammaSet V 0 T, A ≤ T ⊓ (kGenIn V H ⊔ ρ.ker.map H.subtype) := by
    rintro A ⟨hAT, g, hAg, hm⟩
    have hAV : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hD.hyp.elemAbelian.isPGroup g) hAg).1 hm
    subst hAV
    exact le_inf hAT (hD.conj_le_sup_ker hAT)
  have heq : E3.wClos V 0 T = E3.wClos V 0 (T ⊓ (kGenIn V H ⊔ ρ.ker.map H.subtype)) :=
    le_antisymm (E3.wClos_le_of_forall fun A hA' => E3.le_wClos ⟨hA A hA', hA'.2⟩)
      (E3.wClos_mono inf_le_left)
  have hyW : (y : G) ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
    rw [heq]
    exact E3.normalizer_le_normalizer_wClos _ hyR
  have hVW : V ≤ E3.wClos V 0 T :=
    E3.le_wClos ⟨hD.hyp.le_T, 1, by rw [conjSubgroup_one], by
      rw [conjSubgroup_one, E3.mQuot_self]⟩
  have hWT : E3.wClos V 0 T ≤ T := E3.wClos_le 0 T
  have hW1 : E3.wClos V 0 T ≠ ⊥ := ne_bot_of_le_ne_bot hD.hyp.ne_bot hVW
  have hW2 : IsPGroup 2 (E3.wClos V 0 T) := hD.hyp.sylow.2.1.to_le hWT
  have hWle : E3.wClos V 0 T ≤ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.normalizer (E3.wClos V 0 T : Set G) :=
    le_inf (hWT.trans hD.hyp.T_le_normalizer) Subgroup.le_normalizer
  have hyV := hN _ hW1 hW2 hWle inf_le_right ⟨y.2, hyW⟩
  exact hyt (hD.rho_apply_eq_of_mem_normalizer y hyV)

end Borel86Data

end CFSG.LocalAnalysis.WeakClosure81

end
