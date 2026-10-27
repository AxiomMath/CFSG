module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cPsi

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem zpowers_mul_comm (h : GoldHyp3 A B z V) {u w : D} (hu : u ∈ Subgroup.zpowers z)
    (hw : w ∈ Subgroup.zpowers z) : u * w = w * u := by
  rcases zpowers_cases h hu with rfl | rfl <;> rcases zpowers_cases h hw with rfl | rfl <;> simp

section Rot

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.U_le_QB : conjClosure V B ≤ pCoreOf 2 B := g.hyp.conjClosure_le_pCoreOf_right

theorem Gen3.a_mem_B : a ∈ B := pCoreOf_le 2 B (g.U_le_QB g.a_mem_U)

theorem Gen3.a₁_mem_B : a₁ ∈ B := pCoreOf_le 2 B (g.U_le_QB g.a₁_mem_U)

theorem Gen3.a₂_mem_B : a₂ ∈ B := pCoreOf_le 2 B (g.U_le_QB g.a₂_mem_U)

theorem Gen3.comm_a₂ (hU : Nat.card (conjClosure V B) = 8) (q : ↥(pCoreOf 2 B)) :
    a₂ * q * a₂⁻¹ * (q : D)⁻¹ =
      (a * q * a⁻¹ * (q : D)⁻¹) * (a₁ * q * a₁⁻¹ * (q : D)⁻¹) := by
  have hw₀ := g.hyp.commutator_mem a g.a_mem_U q q.2
  have hw₁ := g.hyp.commutator_mem a₁ g.a₁_mem_U q q.2
  have hcomm : a * (a₁ * q * a₁⁻¹ * (q : D)⁻¹) = (a₁ * q * a₁⁻¹ * (q : D)⁻¹) * a :=
    zpowers_comm_B g.hyp g.a_mem_B hw₁
  have key : (a * a₁) * q * (a * a₁)⁻¹ * (q : D)⁻¹ =
      (a * q * a⁻¹ * (q : D)⁻¹) * (a₁ * q * a₁⁻¹ * (q : D)⁻¹) := by
    calc (a * a₁) * q * (a * a₁)⁻¹ * (q : D)⁻¹
        = (a * (a₁ * q * a₁⁻¹ * (q : D)⁻¹)) * ((q : D) * a⁻¹ * (q : D)⁻¹) := by group
      _ = ((a₁ * q * a₁⁻¹ * (q : D)⁻¹) * a) * ((q : D) * a⁻¹ * (q : D)⁻¹) := by rw [hcomm]
      _ = (a₁ * q * a₁⁻¹ * (q : D)⁻¹) * (a * q * a⁻¹ * (q : D)⁻¹) := by group
      _ = (a * q * a⁻¹ * (q : D)⁻¹) * (a₁ * q * a₁⁻¹ * (q : D)⁻¹) :=
          zpowers_mul_comm g.hyp hw₁ hw₀
  rcases g.a₂_eq_or hU with e | e
  · rw [e]; exact key
  · rw [e]
    have hM : (a * a₁) * q * (a * a₁)⁻¹ ∈ B :=
      B.mul_mem (B.mul_mem (B.mul_mem g.a_mem_B g.a₁_mem_B) (pCoreOf_le 2 B q.2))
        (B.inv_mem (B.mul_mem g.a_mem_B g.a₁_mem_B))
    have hzM : z * ((a * a₁) * q * (a * a₁)⁻¹) * z⁻¹ = (a * a₁) * q * (a * a₁)⁻¹ := by
      have := g.z_comm hM
      rw [← this]; group
    calc z * a * a₁ * q * (z * a * a₁)⁻¹ * (q : D)⁻¹
        = (z * ((a * a₁) * q * (a * a₁)⁻¹) * z⁻¹) * (q : D)⁻¹ := by group
      _ = ((a * a₁) * q * (a * a₁)⁻¹) * (q : D)⁻¹ := by rw [hzM]
      _ = _ := key

@[expose] def Gen3.xc (q : ↥(pCoreOf 2 B)) : ↥(pCoreOf 2 B) :=
  ⟨x * q * x⁻¹, (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B g.x_mem) q).mp q.2⟩

theorem Gen3.psi_xc (hU : Nat.card (conjClosure V B) = 8) (q : ↥(pCoreOf 2 B)) :
    psi g (g.xc q) = ((psi g q).1 * (psi g q).2, (psi g q).1) := by
  have hw₀ := g.hyp.commutator_mem a g.a_mem_U q q.2
  have hw₁ := g.hyp.commutator_mem a₁ g.a₁_mem_U q q.2
  have hw₂ := g.hyp.commutator_mem a₂ g.a₂_mem_U q q.2
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show a * (x * q * x⁻¹) * a⁻¹ * (x * q * x⁻¹)⁻¹ =
      (a * q * a⁻¹ * (q : D)⁻¹) * (a₁ * q * a₁⁻¹ * (q : D)⁻¹)
    have e : a * (x * q * x⁻¹) * a⁻¹ * (x * q * x⁻¹)⁻¹ =
        x * (a₂ * q * a₂⁻¹ * (q : D)⁻¹) * x⁻¹ := by
      have ha : a = x * a₂ * x⁻¹ := g.conj_a₂.symm
      calc a * (x * q * x⁻¹) * a⁻¹ * (x * q * x⁻¹)⁻¹
          = (x * a₂ * x⁻¹) * (x * q * x⁻¹) * (x * a₂ * x⁻¹)⁻¹ * (x * q * x⁻¹)⁻¹ := by
            rw [← ha]
        _ = _ := by group
    rw [e, conj_zpowers_B g.hyp g.x_mem hw₂, g.comm_a₂ hU]
  · show a₁ * (x * q * x⁻¹) * a₁⁻¹ * (x * q * x⁻¹)⁻¹ = a * q * a⁻¹ * (q : D)⁻¹
    have e : a₁ * (x * q * x⁻¹) * a₁⁻¹ * (x * q * x⁻¹)⁻¹ =
        x * (a * q * a⁻¹ * (q : D)⁻¹) * x⁻¹ := by
      rw [g.a₁_eq]; group
    rw [e, conj_zpowers_B g.hyp g.x_mem hw₀]

@[expose] def zel (z : D) : ↥(Subgroup.zpowers z) := ⟨z, Subgroup.mem_zpowers z⟩

omit [Finite D] in
theorem Gen3.zel_mul_zel : zel z * zel z = 1 := Subtype.ext g.z_mul_z

omit [Finite D] in
theorem Gen3.zpowers_elem_cases (w : ↥(Subgroup.zpowers z)) : w = 1 ∨ w = zel z := by
  rcases zpowers_cases g.hyp w.2 with e | e
  · left; exact Subtype.ext e
  · right; exact Subtype.ext e

theorem Gen3.card_QB (hT : Nat.card ↥(A ⊓ B) = 64) : Nat.card ↥(pCoreOf 2 B) = 32 := by
  have h1 := card_eq_relIndex_mul g.hyp.gold.pCoreOf_right_le
  rw [g.hyp.gold.relIndex_pCoreOf_T_right, hT] at h1
  omega

theorem Gen3.card_QA (hT : Nat.card ↥(A ⊓ B) = 64) : Nat.card ↥(pCoreOf 2 A) = 32 := by
  have h1 := card_eq_relIndex_mul g.hyp.gold.pCoreOf_left_le
  rw [g.hyp.gold.relIndex_pCoreOf_T_left, hT] at h1
  omega

theorem Gen3.K_le_QA :
    pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) ≤ pCoreOf 2 A := by
  rw [g.hyp.pCoreOf_inf_centralizer_eq_coreIn]
  exact (coreIn_le_right _ _).trans inf_le_left

theorem Gen3.exists_psi_ne_one (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) : ∃ q : ↥(pCoreOf 2 B), psi g q ≠ 1 := by
  by_contra hno
  push Not at hno
  have hle : pCoreOf 2 B ≤ pCoreOf 2 A := fun q hq =>
    g.K_le_QA ((g.mem_ker_psi hU ⟨q, hq⟩).mp (MonoidHom.mem_ker.mpr (hno ⟨q, hq⟩)))
  have heq : pCoreOf 2 B = pCoreOf 2 A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [g.card_QA hT, g.card_QB hT])
  exact g.hyp.gold.pCoreOf_ne (by omega) heq.symm

theorem Gen3.exists_q₀ (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∃ q : ↥(pCoreOf 2 B), psi g q = (zel z, zel z) := by
  obtain ⟨q, hq⟩ := g.exists_psi_ne_one hU hT
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  rcases hp : psi g q with ⟨e₀, e₁⟩
  rw [hp] at hq
  rcases g.zpowers_elem_cases e₀ with rfl | rfl <;> rcases g.zpowers_elem_cases e₁ with rfl | rfl
  · exact absurd rfl hq
  · refine ⟨g.xc (g.xc q), ?_⟩
    have h1 : psi g (g.xc q) = (zel z, 1) := by rw [rot, hp]; simp
    rw [rot, h1]; simp
  · refine ⟨g.xc q, ?_⟩
    rw [rot, hp]; simp
  · exact ⟨q, hp⟩

theorem Gen3.psi_surjective (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) : Function.Surjective (psi g) := by
  obtain ⟨q₀, h₀⟩ := g.exists_q₀ hU hT
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have h₂ : psi g (g.xc (g.xc q₀)) = (zel z, 1) := by rw [rot, h₁]; simp
  rintro ⟨w₀, w₁⟩
  rcases g.zpowers_elem_cases w₀ with rfl | rfl <;> rcases g.zpowers_elem_cases w₁ with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨g.xc q₀, h₁⟩
  · exact ⟨g.xc (g.xc q₀), h₂⟩
  · exact ⟨q₀, h₀⟩

theorem Gen3.card_ker_psi (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64) :
    Nat.card ↥(psi g).ker = 8 := by
  have hmul := Subgroup.card_ker_mul_card_range (psi g)
  have hrange : (psi g).range = ⊤ := MonoidHom.range_eq_top.mpr (g.psi_surjective hU hT)
  have hcard : Nat.card ↥(psi g).range = 4 := by
    rw [hrange, Subgroup.card_top, Nat.card_prod, card_zpowers_eq_two g.hyp.natural]
  rw [hcard, g.card_QB hT] at hmul
  omega

theorem Gen3.U_eq_K (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64) :
    conjClosure V B = pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := by
  have hUK : conjClosure V B ≤ pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) :=
    fun u hu => ⟨g.U_le_QB hu, Subgroup.mem_centralizer_iff.mpr fun w hw => g.U_comm hw hu⟩
  have hmap : (psi g).ker.map (pCoreOf 2 B).subtype =
      pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (g.mem_ker_psi hU q).mp hq
    · intro hy
      exact ⟨⟨y, hy.1⟩, (g.mem_ker_psi hU ⟨y, hy.1⟩).mpr hy, rfl⟩
  have hcard : Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) = 8 := by
    rw [← hmap, Subgroup.card_map_of_injective (pCoreOf 2 B).subtype_injective]
    exact g.card_ker_psi hU hT
  exact Subgroup.eq_of_le_of_card_ge hUK (by rw [hcard, hU])

end Rot

end GoldAmL3c

end F6

end CFSG.Quasithin
