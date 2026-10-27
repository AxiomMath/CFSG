module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cFix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure NData (B V : Subgroup D) (x : D) (N : Subgroup D) : Prop where
  le_QB : N ≤ pCoreOf 2 B
  x_norm : x ∈ Subgroup.normalizer (N : Set D)
  U_le : conjClosure V B ≤ N
  card_N : Nat.card ↥N = 32
  not_cent : ∃ q ∈ N, ∃ u ∈ conjClosure V B, u * q ≠ q * u

section NB

variable [Finite D] {x a a₁ a₂ : D} {N : Subgroup D} (g : Gen3 A B z V x a a₁ a₂)
  (d : NData B V x N)

include g d

omit [Finite D] in
theorem NData.xc_mem {q : ↥(pCoreOf 2 B)} (hq : (q : D) ∈ N) :
    ((g.xc q : ↥(pCoreOf 2 B)) : D) ∈ N :=
  (Subgroup.mem_normalizer_iff.mp d.x_norm q).mp hq

theorem NData.exists_psi_ne_one (hU : Nat.card (conjClosure V B) = 8) :
    ∃ q : ↥(pCoreOf 2 B), (q : D) ∈ N ∧ psi g q ≠ 1 := by
  obtain ⟨q, hqN, u, hu, hne⟩ := d.not_cent
  refine ⟨⟨q, d.le_QB hqN⟩, hqN, fun h => hne ?_⟩
  have := (g.mem_ker_psi hU ⟨q, d.le_QB hqN⟩).mp (MonoidHom.mem_ker.mpr h)
  exact Subgroup.mem_centralizer_iff.mp this.2 u hu

theorem NData.exists_q₀ (hU : Nat.card (conjClosure V B) = 8) :
    ∃ q : ↥(pCoreOf 2 B), (q : D) ∈ N ∧ psi g q = (zel z, zel z) := by
  obtain ⟨q, hqN, hq⟩ := d.exists_psi_ne_one g hU
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  rcases hp : psi g q with ⟨e₀, e₁⟩
  rw [hp] at hq
  rcases g.zpowers_elem_cases e₀ with rfl | rfl <;> rcases g.zpowers_elem_cases e₁ with rfl | rfl
  · exact absurd rfl hq
  · refine ⟨g.xc (g.xc q), d.xc_mem g (d.xc_mem g hqN), ?_⟩
    have h1 : psi g (g.xc q) = (zel z, 1) := by rw [rot, hp]; simp
    rw [rot, h1]; simp
  · refine ⟨g.xc q, d.xc_mem g hqN, ?_⟩
    rw [rot, hp]; simp
  · exact ⟨q, hqN, hp⟩

theorem NData.psi_surjective (hU : Nat.card (conjClosure V B) = 8) (w : ↥(Subgroup.zpowers z) ×
    ↥(Subgroup.zpowers z)) : ∃ q : ↥(pCoreOf 2 B), (q : D) ∈ N ∧ psi g q = w := by
  obtain ⟨q₀, hq₀N, h₀⟩ := d.exists_q₀ g hU
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have h₂ : psi g (g.xc (g.xc q₀)) = (zel z, 1) := by rw [rot, h₁]; simp
  obtain ⟨w₀, w₁⟩ := w
  rcases g.zpowers_elem_cases w₀ with rfl | rfl <;> rcases g.zpowers_elem_cases w₁ with rfl | rfl
  · exact ⟨1, N.one_mem, map_one _⟩
  · exact ⟨g.xc q₀, d.xc_mem g hq₀N, h₁⟩
  · exact ⟨g.xc (g.xc q₀), d.xc_mem g (d.xc_mem g hq₀N), h₂⟩
  · exact ⟨q₀, hq₀N, h₀⟩

theorem NData.card_inf_centralizer (hU : Nat.card (conjClosure V B) = 8) :
    Nat.card ↥(N ⊓ Subgroup.centralizer (conjClosure V B : Set D)) = 8 := by
  let f : ↥N →* ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) :=
    (psi g).comp (Subgroup.inclusion d.le_QB)
  have hsurj : Function.Surjective f := fun w => by
    obtain ⟨q, hqN, hq⟩ := d.psi_surjective g hU w
    exact ⟨⟨q, hqN⟩, hq⟩
  have hker : f.ker = (N ⊓ Subgroup.centralizer (conjClosure V B : Set D)).subgroupOf N := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have := (g.mem_ker_psi hU (Subgroup.inclusion d.le_QB q)).mp (MonoidHom.mem_ker.mpr h)
      exact ⟨q.2, this.2⟩
    · intro h
      exact (g.mem_ker_psi hU (Subgroup.inclusion d.le_QB q)).mpr
        ⟨(pCoreOf 2 B).mem_carrier.mpr (d.le_QB q.2), h.2⟩
  have hmul := Subgroup.card_ker_mul_card_range f
  have hrange : Nat.card ↥f.range = 4 := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_prod,
      card_zpowers_eq_two g.hyp.natural]
  have hkc : Nat.card ↥f.ker = Nat.card ↥(N ⊓ Subgroup.centralizer (conjClosure V B : Set D)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hkc, hrange, d.card_N] at hmul
  omega

theorem NData.inf_centralizer_eq (hU : Nat.card (conjClosure V B) = 8) :
    N ⊓ Subgroup.centralizer (conjClosure V B : Set D) = conjClosure V B := by
  have hUK : conjClosure V B ≤ N ⊓ Subgroup.centralizer (conjClosure V B : Set D) :=
    fun u hu => ⟨d.U_le hu, Subgroup.mem_centralizer_iff.mpr fun w hw => g.U_comm hw hu⟩
  exact (Subgroup.eq_of_le_of_card_ge hUK (by rw [d.card_inf_centralizer g hU, hU])).symm

theorem NData.mem_U_of_psi_eq_one (hU : Nat.card (conjClosure V B) = 8) {q : ↥(pCoreOf 2 B)}
    (hqN : (q : D) ∈ N) (h : psi g q = 1) : (q : D) ∈ conjClosure V B :=
  (d.inf_centralizer_eq g hU).le ⟨hqN, ((g.mem_ker_psi hU q).mp (MonoidHom.mem_ker.mpr h)).2⟩

theorem NData.fixed_mem_zpowers (hU : Nat.card (conjClosure V B) = 8) {q : D} (hqN : q ∈ N)
    (hfix : x * q * x⁻¹ = q) : q ∈ Subgroup.zpowers z := by
  have hq : q ∈ pCoreOf 2 B := d.le_QB hqN
  have h1 : psi g ⟨q, hq⟩ = 1 := g.psi_eq_one_of_fixed hU ⟨q, hq⟩ (Subtype.ext hfix)
  have h3 : q ∈ conjClosure V B := d.mem_U_of_psi_eq_one g hU hqN h1
  have h4 : q ∈ conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D) := by
    refine ⟨h3, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc y * q = (y * q * y⁻¹) * y := by group
      _ = q * y := by rw [hfix]
  rw [g.U_inf_centralizer_x hU] at h4
  exact h4

end NB

end GoldAmL3c

end F6

end CFSG.Quasithin
