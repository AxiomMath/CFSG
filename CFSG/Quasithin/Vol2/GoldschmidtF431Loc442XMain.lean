module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442XFix
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442XG

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.Loc442

universe u

section Centralizer

variable {Mb : Type u} [Group Mb]

theorem locX_card_centralizer {M2 : Subgroup Mb} {t : Mb} (ht : t ∈ M2)
    (h : Subgroup.centralizer ({t} : Set Mb) ≤ M2) :
    Nat.card (Subgroup.centralizer ({(⟨t, ht⟩ : M2)} : Set M2)) =
      Nat.card (Subgroup.centralizer ({t} : Set Mb)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : Mb), Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 x.2))⟩
      invFun := fun y => ⟨⟨y.1, h y.2⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

end Centralizer

section Main


variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {z t q : Mb} {Vb : Subgroup Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem loc442X (D : Loc442DatumX M1 M2 T z t Vb q) (C : F431Comp M1 M2 b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t)) :
    Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) ≤ b2.range := by
  by_contra hK
  set X := locX M2 b2 t (D.lie.T_le₂ D.lie.t_mem) with hX
  set V : Subgroup M := (Vb.subgroupOf M2).map b2 with hV
  have hVM2 : Vb ≤ M2 := D.V_le.trans D.lie.cent_t
  have hmemV : ∀ {y : M}, y ∈ V ↔ ∃ vb : M2, (vb : Mb) ∈ Vb ∧ b2 vb = y := Subgroup.mem_map
  have hXK : X ≤ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (D.locX_comm_t C hy)
  have hne : ¬ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) ≤ X := by
    intro h
    apply hK
    intro y hy
    obtain ⟨x, -, rfl⟩ := mem_locX.1 (h hy)
    exact ⟨x, rfl⟩
  have hVX : V ≤ X := by
    intro y hy
    obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hy
    exact mem_locX.2 ⟨vb, Subgroup.mem_centralizer_singleton_iff.1 (D.V_le hvb), rfl⟩
  have hVn : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V := by
    intro x hx v hv
    obtain ⟨xb, hxb, rfl⟩ := mem_locX.1 hx
    obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hv
    refine hmemV.2 ⟨xb * vb * xb⁻¹, ?_, by simp⟩
    exact D.V_norm _ (Subgroup.mem_centralizer_singleton_iff.2 hxb) _ hvb
  have hV4 : Nat.card V = 4 := by
    rw [hV, Subgroup.card_map_of_injective C.inj₂,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM2).toEquiv]
    exact D.V_card
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb'
    obtain ⟨va, hva, rfl⟩ := hmemV.1 ha
    obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hb'
    rw [← map_mul, ← map_mul]
    exact congrArg b2 (Subtype.ext (D.V_comm _ hva _ hvb))
  have hV2 : ∀ a ∈ V, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨va, hva, rfl⟩ := hmemV.1 ha
    rw [← map_pow, ← map_one b2]
    exact congrArg b2 (Subtype.ext (D.V_sq _ hva))
  have hqM2 : q ∈ M2 := D.lie.cent_t D.q_mem
  have hqX : b2 ⟨q, hqM2⟩ ∈ X :=
    mem_locX.2 ⟨⟨q, hqM2⟩, Subgroup.mem_centralizer_singleton_iff.1 D.q_mem, rfl⟩
  have hqV : ∀ v ∈ V, b2 ⟨q, hqM2⟩ * v = v * b2 ⟨q, hqM2⟩ := by
    intro v hv
    obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hv
    rw [← map_mul, ← map_mul]
    exact congrArg b2 (Subtype.ext (D.q_comm _ hvb))
  have hq2 : b2 ⟨q, hqM2⟩ ^ 2 ∈ V := hmemV.2 ⟨⟨q, hqM2⟩ ^ 2, D.q_sq, map_pow b2 _ 2⟩
  have hq2' : b2 ⟨q, hqM2⟩ ^ 2 ≠ 1 := by
    intro h
    rw [← map_pow, ← map_one b2] at h
    exact D.q_sq_ne (congrArg Subtype.val (C.inj₂ h))
  have hXc : Nat.Coprime (Nat.card X) 65 := by
    rw [hX, locX, Subgroup.card_map_of_injective C.inj₂,
      locX_card_centralizer (D.lie.T_le₂ D.lie.t_mem) D.lie.cent_t]
    exact D.Ct_cop
  refine acoreGCop hXK hne hVX hVn hV4 hVab hV2 ?_ hqX hqV hq2 hq2' hXc
  intro v hv hv1 g hg hgX
  exact D.locX_fix_V C hb hnc (hmemV.1 hv) hv1 (Subgroup.mem_centralizer_singleton_iff.1 hg) hgX

end Main

end CFSG.Quasithin
