module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3dFix
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2DMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace Crit

theorem B_conj_c₂₃ (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) {b : D} (hb : b ∈ B) :
    b * g.c₂₃ * b⁻¹ = g.c₂₃ ∨ b * g.c₂₃ * b⁻¹ = g.a₃ * g.a ∨
      b * g.c₂₃ * b⁻¹ = g.a * g.a₂ := by
  have hT := cr.T_fixed_c₂₃ g h hU
  rcases coset_decomp h.gold.relIndex_right g.mem_B g.not_mem_T g.sq_not_mem_T hb with
    hTb | ⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩
  · exact Or.inl (hT b hTb)
  · right; left
    calc g.x * t * g.c₂₃ * (g.x * t)⁻¹ = g.x * (t * g.c₂₃ * t⁻¹) * g.x⁻¹ := by group
      _ = g.a₃ * g.a := by rw [hT t htT, g.x_conj_c₂₃]
  · right; right
    calc g.x * g.x * t * g.c₂₃ * (g.x * g.x * t)⁻¹
        = g.x * (g.x * (t * g.c₂₃ * t⁻¹) * g.x⁻¹) * g.x⁻¹ := by group
      _ = g.a * g.a₂ := by rw [hT t htT, g.x_conj_c₂₃, g.x_conj_a₃_mul_a]

theorem isNaturalAt_dual (cr : Crit A B z V) (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 16) :
    IsNaturalAt B (A ⊓ B) g.c₂₃ (conjClosure (Subgroup.zpowers g.c₂₃) B) := by
  have hcU : g.c₂₃ ∈ conjClosure V B := g.c₂₃_mem_U
  have hcT : g.c₂₃ ∈ A ⊓ B := h.gold.pCoreOf_left_le (h.conjClosure_le_pCoreOf_left hcU)
  have hZ : g.c₂₃ ∈ centerOf (A ⊓ B) :=
    ⟨hcT, Subgroup.mem_centralizer_iff.mpr fun t ht => mul_eq_of_conj_eq
      (cr.T_fixed_c₂₃ g h hU t ht)⟩
  have hsq : g.c₂₃ ^ 2 = 1 := by rw [pow_two]; exact g.c₂₃_sq h
  have hne : ∃ b ∈ B, b * g.c₂₃ * b⁻¹ ≠ g.c₂₃ := by
    refine ⟨g.x, g.mem_B, fun heq => ?_⟩
    rw [g.x_conj_c₂₃] at heq
    have hc : g.a₃ * g.a₂ = g.a₂ * g.a₃ := h.U_comm (g.a₃_mem_U) (g.a₂_mem_U)
    have h1 : g.a₃ * g.a₂ = g.a₃ * g.a := by
      calc g.a₃ * g.a₂ = g.a₂ * g.a₃ := hc
        _ = g.a₃ * g.a := heq.symm
    have h2 : g.a₂ = g.a := mul_left_cancel h1
    apply g.a₂_not_mem_sup h hU
    rw [h2]
    exact Subgroup.mem_sup_left g.mem_V
  obtain ⟨x', z'', V'', hx'B, hx'3, hx'ne, hz'', hnat, hzmem⟩ :=
    exists_natural_data h.gold.vertex_right hZ hsq hne
  have hp : x' * g.c₂₃ * x'⁻¹ = g.a₃ * g.a ∨ x' * g.c₂₃ * x'⁻¹ = g.a * g.a₂ := by
    rcases cr.B_conj_c₂₃ g h hU hx'B with e | e | e
    · exact absurd e hx'ne
    · exact Or.inl e
    · exact Or.inr e
  have hx'x'B : x' * x' ∈ B := B.mul_mem hx'B hx'B
  have hq0 : x' * x' * g.c₂₃ * (x' * x')⁻¹ ≠ g.c₂₃ := by
    intro heq
    apply hx'ne
    calc x' * g.c₂₃ * x'⁻¹ = x' * (x' * x' * g.c₂₃ * (x' * x')⁻¹) * x'⁻¹ := by rw [heq]
      _ = (x' * x' * x') * g.c₂₃ * (x' * x' * x')⁻¹ := by group
      _ = g.c₂₃ := by rw [hx'3]; group
  have hq : x' * x' * g.c₂₃ * (x' * x')⁻¹ = g.a₃ * g.a ∨
      x' * x' * g.c₂₃ * (x' * x')⁻¹ = g.a * g.a₂ := by
    rcases cr.B_conj_c₂₃ g h hU hx'x'B with e | e | e
    · exact absurd e hq0
    · exact Or.inl e
    · exact Or.inr e
  have hpq : x' * g.c₂₃ * x'⁻¹ ≠ x' * x' * g.c₂₃ * (x' * x')⁻¹ := by
    intro heq
    apply hx'ne
    have h1 : x'⁻¹ * (x' * g.c₂₃ * x'⁻¹) * x' = x'⁻¹ * (x' * x' * g.c₂₃ * (x' * x')⁻¹) * x' := by
      rw [heq]
    have e1 : x'⁻¹ * (x' * g.c₂₃ * x'⁻¹) * x' = g.c₂₃ := by group
    have e2 : x'⁻¹ * (x' * x' * g.c₂₃ * (x' * x')⁻¹) * x' = x' * g.c₂₃ * x'⁻¹ := by group
    rw [e1, e2] at h1
    exact h1.symm
  have hzeq : z'' = g.c₂₃ := by
    rw [hz'']
    rcases hp with e1 | e1 <;> rcases hq with e2 | e2
    · exact absurd (e1.trans e2.symm) hpq
    · rw [e1, e2]; exact g.c₁_mul_c₂ h
    · rw [e1, e2]; exact g.c₂_mul_c₁ h
    · exact absurd (e1.trans e2.symm) hpq
  rw [hzeq] at hnat
  have hV : V'' = conjClosure (Subgroup.zpowers g.c₂₃) B := hnat.V_eq
  rw [← hV]
  exact hnat

end Crit

namespace Crit

theorem conjClosure_U_le (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hVA : conjClosure (conjClosure (Subgroup.zpowers g.c₂₃) B) A ≤ pCoreOf 2 B) :
    conjClosure (conjClosure V B) A ≤ pCoreOf 2 B := by
  let S : Subgroup D :=
    { carrier := {u | ∀ a ∈ A, a * u * a⁻¹ ∈ pCoreOf 2 B}
      one_mem' := fun a _ => by simp
      mul_mem' := fun {u v} hu hv a ha => by
        have e : a * (u * v) * a⁻¹ = (a * u * a⁻¹) * (a * v * a⁻¹) := by group
        rw [e]; exact (pCoreOf 2 B).mul_mem (hu a ha) (hv a ha)
      inv_mem' := fun {u} hu a ha => by
        have e : a * u⁻¹ * a⁻¹ = (a * u * a⁻¹)⁻¹ := by group
        rw [e]; exact (pCoreOf 2 B).inv_mem (hu a ha) }
  have hVS : V ≤ S := fun v hv a ha =>
    h.le_pCoreOf_right
      ((Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 ha) v).mp hv)
  have hcV'' : g.c₂₃ ∈ conjClosure (Subgroup.zpowers g.c₂₃) B :=
    le_conjClosure _ B (Subgroup.mem_zpowers _)
  have hc1V'' : g.a₃ * g.a ∈ conjClosure (Subgroup.zpowers g.c₂₃) B := by
    have := mem_conjClosure g.mem_B (Subgroup.mem_zpowers g.c₂₃)
    rwa [g.x_conj_c₂₃] at this
  have ha₃S : g.a₃ ∈ S := by
    intro a ha
    have e : a * g.a₃ * a⁻¹ = (a * (g.a₃ * g.a) * a⁻¹) * (a * g.a * a⁻¹)⁻¹ := by group
    rw [e]
    refine (pCoreOf 2 B).mul_mem (hVA (mem_conjClosure ha hc1V'')) ((pCoreOf 2 B).inv_mem ?_)
    exact h.le_pCoreOf_right
      ((Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 ha) g.a).mp g.mem_V)
  have ha₂S : g.a₂ ∈ S := by
    intro a ha
    have e : a * g.a₂ * a⁻¹ = (a * g.c₂₃ * a⁻¹) * (a * g.a₃ * a⁻¹)⁻¹ := by
      have : g.a₂ = g.c₂₃ * g.a₃⁻¹ := by unfold Gens.c₂₃; group
      rw [this]; group
    rw [e]
    exact (pCoreOf 2 B).mul_mem (hVA (mem_conjClosure ha hcV'')) ((pCoreOf 2 B).inv_mem
      (ha₃S a ha))
  have hUS : conjClosure V B ≤ S :=
    (g.conjClosure_le_sup h).trans
      (sup_le (sup_le hVS (Subgroup.zpowers_le.mpr ha₂S)) (Subgroup.zpowers_le.mpr ha₃S))
  exact conjClosure_le fun a ha u hu => hUS hu a ha

end Crit

namespace Crit

theorem critDist_dual (g : Gens A B z V) (h : GoldHyp3 A B z V)
    (hb : ¬ 4 ≤ critDist (A ⊔ B) A B V)
    (hnat : IsNaturalAt B (B ⊓ A) g.c₂₃ (conjClosure (Subgroup.zpowers g.c₂₃) B)) :
    critDist (B ⊔ A) B A (conjClosure (Subgroup.zpowers g.c₂₃) B) = 2 := by
  have hyp : AmalgamHypV (B ⊔ A) B A (B ⊓ A) (conjClosure (Subgroup.zpowers g.c₂₃) B) :=
    h.gold.symm.amalgamHypV hnat
  have hV0 : conjClosure (Subgroup.zpowers g.c₂₃) B ≠ ⊥ := hnat.natural.ne_bot
  have hcU := g.c₂₃_mem_U
  have hzpU : Subgroup.zpowers g.c₂₃ ≤ conjClosure V B := Subgroup.zpowers_le.mpr hcU
  have hV''U : conjClosure (Subgroup.zpowers g.c₂₃) B ≤ conjClosure V B :=
    conjClosure_le fun k hk w hw =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B hk) w).mp (hzpU hw)
  have hBN : B ≤ Subgroup.normalizer
      ((conjClosure (Subgroup.zpowers g.c₂₃) B : Subgroup D) : Set D) :=
    le_normalizer_conjClosure _ B
  have hcl : conjClosure (conjClosure (Subgroup.zpowers g.c₂₃) B) B =
      conjClosure (Subgroup.zpowers g.c₂₃) B := conjClosure_eq_of_le_normalizer hBN
  have h2 : 2 ≤ critDist (B ⊔ A) B A (conjClosure (Subgroup.zpowers g.c₂₃) B) := by
    rw [le_critDist_iff hyp hV0 (by norm_num)]
    rw [show (2 : ℕ) = 1 + 1 from rfl, le_ballStab_succ_γ₀_iff rfl]
    refine ⟨fun v hv => ?_, ?_⟩
    · exact (h.gold.pCoreOf_left_le (h.conjClosure_le_pCoreOf_left (hV''U hv))).2
    · rw [hcl, (ballStab_one_γ₁ rfl).1]
      intro v hv
      have hvQ : v ∈ pCoreOf 2 A := h.conjClosure_le_pCoreOf_left (hV''U hv)
      refine ⟨pCoreOf_le 2 A hvQ, fun a ha => ?_⟩
      have h1 : a⁻¹ * v * a ∈ pCoreOf 2 A := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A (A.inv_mem ha)) v).mp
          hvQ
        simpa using this
      rw [inf_comm]
      exact h.gold.pCoreOf_left_le h1
  have h3 : ¬ 3 ≤ critDist (B ⊔ A) B A (conjClosure (Subgroup.zpowers g.c₂₃) B) := by
    intro h3
    rw [le_critDist_iff hyp hV0 (by norm_num)] at h3
    rw [show (3 : ℕ) = 2 + 1 from rfl, le_ballStab_succ_γ₀_iff rfl] at h3
    obtain ⟨-, h3'⟩ := h3
    rw [hcl, show (2 : ℕ) = 1 + 1 from rfl, le_ballStab_succ_γ₁_iff rfl] at h3'
    obtain ⟨-, h3''⟩ := h3'
    rw [(ballStab_one_γ₀ rfl).1] at h3''
    have hQB : coreIn (B ⊓ A) B ≤ pCoreOf 2 B :=
      le_pCoreOf_of_le_normalizer 2 (coreIn_le_left _ _) (le_normalizer_coreIn _ _)
        (h.gold.isSylowTwoOf_right.2.1.to_le ((coreIn_le_right _ _).trans (inf_comm B A).le))
    apply hb
    rw [h.four_le_critDist_iff]
    exact conjClosure_U_le g h (h3''.trans hQB)
  omega

end Crit

namespace GoldHyp3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}
  (h : GoldHyp3 A B z V)

include h

theorem card_conjClosure_eq_eight_of_not_four_le (hb : ¬ 4 ≤ critDist (A ⊔ B) A B V) :
    Nat.card (conjClosure V B) = 8 := by
  rcases h.card_conjClosure_eq with hU | hU
  · exact hU
  · exfalso
    obtain ⟨g⟩ := h.nonempty_gens
    obtain ⟨cr⟩ := h.nonempty_crit hb
    have hnat := cr.isNaturalAt_dual g h hU
    rw [inf_comm A B] at hnat
    have hcrit := Crit.critDist_dual g h hb hnat
    have h32 : 32 ≤ Nat.card ↥(B ⊓ A) := by
      rw [inf_comm]
      have := h.sixty_four_le_card_inf
      omega
    have hz : z ∈ centerOf (B ⊓ A) := by
      rw [inf_comm]; exact h.natural.z_mem
    have := GoldAmL2D.a1_trivial_of_critDist_two h.gold.symm h32 hnat hcrit z hz
      (h.z_mul_z) (fun y hy => mul_eq_of_conj_eq (h.central y hy))
    exact h.natural.z_ne this

theorem card_conjClosure_eq_eight_of_critDist_eq_three
    (hb : critDist (A ⊔ B) A B V = 3) : Nat.card (conjClosure V B) = 8 :=
  h.card_conjClosure_eq_eight_of_not_four_le (by omega)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
