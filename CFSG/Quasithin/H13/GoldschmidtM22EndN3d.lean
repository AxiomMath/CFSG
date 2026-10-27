module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN2c
public import CFSG.Quasithin.H13.GoldschmidtM22EndS3

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem KK_le_HH (h : Hyp6Sec2 G T M L V) (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    KK T V ≤ HH T :=
  conjClosure_le fun _ hx _ hv => (HH T).mul_mem ((HH T).mul_mem hx (V_le_HH h hZ hv))
    ((HH T).inv_mem hx)

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

omit [Finite G] in
include P in
theorem conjSubgroup_eq_of_comm (a : ↥(HH T)) (haV : (a : G) ∈ V) (haC : (a : G) ∉ CHU T L V)
    (k e : ↥(HH T)) (hc : P.ψ (k * e⁻¹) * P.ψ a = P.ψ a * P.ψ (k * e⁻¹)) :
    conjSubgroup V (k : G) = conjSubgroup V (e : G) := by
  have hn : ((k * e⁻¹ : ↥(HH T)) : G) ∈ Subgroup.normalizer (V : Set G) :=
    ((P.swap_norm a haV haC).2 _).mpr hc
  have hk : (k : G) = ((k * e⁻¹ : ↥(HH T)) : G) * (e : G) := by simp
  rw [hk, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hn]

omit [Finite G] in
include P in
theorem conjSubgroup_le_sup (a g : ↥(HH T)) (haV : (a : G) ∈ V) (haC : (a : G) ∉ CHU T L V)
    (hg : ¬ Commute (P.ψ g) (P.ψ a)) (k : ↥(HH T)) :
    conjSubgroup V (k : G) ≤ V ⊔ conjSubgroup V (g : G) := by
  have hτ2 : (P.ψ a).support.card = 2 :=
    Equiv.Perm.card_support_eq_two.mpr (P.swap_norm a haV haC).1
  have hg' : P.ψ g * P.ψ a ≠ P.ψ a * P.ψ g := fun hc => hg hc
  rcases perm3_coset_cover _ _ (P.ψ k) hτ2 hg' with h1 | h2 | h3
  ·
    have : conjSubgroup V (k : G) = conjSubgroup V ((1 : ↥(HH T)) : G) :=
      conjSubgroup_eq_of_comm P a haV haC k 1 (by simpa using h1)
    rw [this, show ((1 : ↥(HH T)) : G) = 1 from rfl, conjSubgroup_one]
    exact le_sup_left
  · have : conjSubgroup V (k : G) = conjSubgroup V (g : G) :=
      conjSubgroup_eq_of_comm P a haV haC k g (by simpa [map_mul, map_inv] using h2)
    rw [this]
    exact le_sup_right
  · have : conjSubgroup V (k : G) = conjSubgroup V ((g * a : ↥(HH T)) : G) :=
      conjSubgroup_eq_of_comm P a haV haC k (g * a) (by simpa [map_mul, map_inv] using h3)
    rw [this]
    intro x hx
    have hx' : (a : G) * x * (a : G)⁻¹ ∈ conjSubgroup V (g : G) := by
      have := hx
      rw [show (((g * a : ↥(HH T)) : G)) = (g : G) * (a : G) from rfl,
        ← conjSubgroup_conjSubgroup, mem_conjSubgroup_iff] at this
      exact this
    have haY : (a : G) ∈ V ⊔ conjSubgroup V (g : G) := Subgroup.mem_sup_left haV
    have hY : (a : G) * x * (a : G)⁻¹ ∈ V ⊔ conjSubgroup V (g : G) :=
      Subgroup.mem_sup_right hx'
    have := (V ⊔ conjSubgroup V (g : G)).mul_mem ((V ⊔ conjSubgroup V (g : G)).mul_mem
      ((V ⊔ conjSubgroup V (g : G)).inv_mem haY) hY) haY
    simpa [mul_assoc] using this

omit [Finite G] in
include P in
theorem KK_eq_sup (a g : ↥(HH T)) (haV : (a : G) ∈ V) (haC : (a : G) ∉ CHU T L V)
    (hg : ¬ Commute (P.ψ g) (P.ψ a)) : KK T V = V ⊔ conjSubgroup V (g : G) := by
  refine le_antisymm (conjClosure_le fun k hk v hv => ?_) (sup_le (le_conjClosure _ _) ?_)
  · have hmem : (k : G) * v * (k : G)⁻¹ ∈ conjSubgroup V ((k : G)⁻¹) := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hv
    exact conjSubgroup_le_sup P a g haV haC hg ⟨(k : G)⁻¹, (HH T).inv_mem hk⟩ hmem
  · intro x hx
    have hv : (g : G) * x * (g : G)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
    have := mem_conjClosure ((HH T).inv_mem g.2) hv
    simpa [mul_assoc] using this

end PsiData

end CFSG.Quasithin.H13.GM22
