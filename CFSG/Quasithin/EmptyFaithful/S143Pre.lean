module

public import CFSG.Quasithin.Vol2.Ch12Sec8Three
public import CFSG.Quasithin.Vol2.Ch12Sec8Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_conj_eq_of_card_two {Z : Subgroup G} (hZ2 : Nat.card Z = 2) {z c : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hc : c * z * c⁻¹ = z) :
    c ∈ Subgroup.centralizer (Z : Set G) := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ2
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1, one_mul, mul_one]
  · have hwz : w = z := by
      have h1 := hy ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he))
      have h2 := hy ⟨z, hz⟩ (fun he => hz1 (congrArg Subtype.val he))
      exact congrArg Subtype.val (h1.trans h2.symm)
    rw [hwz]
    calc z * c = (c * z * c⁻¹) * c := by rw [hc]
      _ = c * z := by group

variable {T M L : Subgroup G}

namespace Hyp1281Two

theorem exists_mul_eq (h : Hyp1281Two G T M L) {m : G} (hm : m ∈ M) :
    ∃ l ∈ L, ∃ c ∈ M ⊓ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G), m = l * c := by
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  obtain ⟨z, hzZ⟩ : ∃ z : quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h.omegaOneCenter_ne_bot (by
      rw [eq_bot_iff]
      intro w hw
      have := hall ⟨w, hw⟩
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this)
  have hz1 : (z : G) ≠ 1 := fun he => hzZ (Subtype.ext he)
  have hzV : (z : G) ∈ VZ T M := le_conjClosure _ _ z.2
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 hm
  have hmz : m * z * m⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hmN _).mp hzV
  have hmz1 : m * z * m⁻¹ ≠ 1 := fun he => hz1 (by
    have : m⁻¹ * (m * z * m⁻¹) * m = 1 := by rw [he]; group
    simpa [mul_assoc] using this)
  obtain ⟨l, hlL, hl⟩ := h.exists_conj_eq hzV hmz hz1 hmz1
  refine ⟨l, hlL, l⁻¹ * m, ⟨M.mul_mem (M.inv_mem (h.le hlL)) hm, ?_⟩, by group⟩
  refine Subgroup.centralizer_le_normalizer _
    (mem_centralizer_of_conj_eq_of_card_two h.card_omegaOneCenter z.2 hz1 ?_)
  calc l⁻¹ * m * z * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * z * m⁻¹) * l := by group
    _ = z := by rw [← hl]; group

theorem sup_inf_normalizer_eq (h : Hyp1281Two G T M L) :
    L ⊔ (M ⊓ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) = M := by
  refine le_antisymm (sup_le h.le inf_le_left) fun m hm => ?_
  obtain ⟨l, hlL, c, hc, rfl⟩ := h.exists_mul_eq hm
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hc)

theorem eq_sup_of_inf_eq (h : Hyp1281Two G T M L)
    (hT : M ⊓ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) = T) : M = L ⊔ T := by
  rw [← h.sup_inf_normalizer_eq, hT]

theorem inf_eq_inf_normalizer (h : Hyp1281Two G T M L) (H : Subgroup G) :
    H ⊓ M = H ⊓ Subgroup.normalizer (VZ T M : Set G) := by
  rw [h.normalizer_VZ]

theorem conjSub_VZ_eq (h : Hyp1281Two G T M L) {m : G} (hm : m ∈ M) :
    (VZ T M).map (MulAut.conj m).toMonoidHom = VZ T M := by
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 hm
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hmN v).mp hv
  · intro hu
    refine ⟨m⁻¹ * u * m, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) u).mp hu
    simpa using this

end Hyp1281Two

end CFSG.Quasithin
