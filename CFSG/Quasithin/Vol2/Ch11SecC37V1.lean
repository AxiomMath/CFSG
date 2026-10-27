module

public import CFSG.Quasithin.Vol2.Ch11SecC37B2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autOn_le_of_le {H₁ H₂ V : Subgroup G} (h : H₁ ≤ H₂) : autOn H₁ V ≤ autOn H₂ V :=
  Subgroup.map_mono fun _ hx => h hx

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem aStar_eq (hAS : FactAStarSylow) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    autOn (conjSubgroup (fsuV T I) g) (VZ T H) = autOn (T ⊓ oTwoUpper H) (VZ T H) := by
  have : IsMulCommutative ↥(VZ T H) := s.isElemAbelian_VZ.1
  have hS := s.aStar_sylow hAS hF h1102 hG2 h1122 h1134 h1135 h1136
  have hKS : QuasithinUnique.IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    F7.isSylowTwoOf_inf_normal s.sylow (oTwoUpper_le H)
      (s.T_le.trans (le_normalizer_oTwoUpper H))
  have hS' := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hKS (K_le_normalizer_VZ T H)
  set P : Subgroup (MulAut ↥(VZ T H)) := autOn T (VZ T H) ⊓ autOn (oTwoUpper H) (VZ T H)
  have hP2 : IsPGroup 2 ↥P := by
    have h1 : IsPGroup 2 ↥(autOn T (VZ T H)) := by
      refine IsPGroup.map ?_ _
      exact s.hyp.fsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe
        (s.T_le.trans (le_normalizer_VZ T H))).symm
    exact h1.to_le inf_le_left
  have hAP : autOn (conjSubgroup (fsuV T I) g) (VZ T H) ≤ P :=
    le_inf (autOn_le_of_le s.hAT) hS.1
  have hTP : autOn (T ⊓ oTwoUpper H) (VZ T H) ≤ P :=
    le_inf (autOn_le_of_le inf_le_left) hS'.1
  have h1 := (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 P inf_le_right hP2 hAP
  have h2 := (A4.isSylowTwoOf_iff_maximal.mp hS').2.2 P inf_le_right hP2 hTP
  exact le_antisymm (hAP.trans h2) (hTP.trans h1)

theorem comm_iff (hAS : FactAStarSylow) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) {u : G} (hu : u ∈ VZ T H) (x : G) :
    (∃ a ∈ conjSubgroup (fsuV T I) g, x = u * a * u⁻¹ * a⁻¹) ↔
      ∃ t ∈ T ⊓ oTwoUpper H, x = u * t * u⁻¹ * t⁻¹ := by
  have he := s.aStar_eq hAS hF h1102 hG2 h1122 h1134 h1135 h1136
  have hN : ∀ y ∈ H, y ∈ Subgroup.normalizer (VZ T H : Set G) := fun y hy =>
    le_normalizer_VZ T H hy
  have key : ∀ (y z : ↥(Subgroup.normalizer (VZ T H : Set G))),
      conjAct (VZ T H) y = conjAct (VZ T H) z → (y : G) * u * (y : G)⁻¹ = z * u * (z : G)⁻¹ := by
    intro y z hyz
    have := congrArg (fun φ : MulAut ↥(VZ T H) => ((φ ⟨u, hu⟩ : ↥(VZ T H)) : G)) hyz
    simpa only [conjAct_apply_coe] using this
  have hAT := s.hAT
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hmem : conjAct (VZ T H) ⟨a, hN a (s.T_le (hAT ha))⟩ ∈
        autOn (T ⊓ oTwoUpper H) (VZ T H) := he ▸ ⟨⟨a, _⟩, ha, rfl⟩
    obtain ⟨t, ht, hta⟩ := hmem
    refine ⟨t, ht, ?_⟩
    have h1 := key _ _ hta
    calc u * a * u⁻¹ * a⁻¹ = u * (a * u * a⁻¹)⁻¹ := by group
      _ = u * ((t : G) * u * (t : G)⁻¹)⁻¹ := by rw [h1]
      _ = u * t * u⁻¹ * (t : G)⁻¹ := by group
  · rintro ⟨t, ht, rfl⟩
    have hmem : conjAct (VZ T H) ⟨t, hN t (s.T_le ht.1)⟩ ∈
        autOn (conjSubgroup (fsuV T I) g) (VZ T H) := he.symm ▸ ⟨⟨t, _⟩, ht, rfl⟩
    obtain ⟨a, ha, hat⟩ := hmem
    refine ⟨a, ha, ?_⟩
    have h1 := key _ _ hat
    calc u * t * u⁻¹ * t⁻¹ = u * (t * u * t⁻¹)⁻¹ := by group
      _ = u * ((a : G) * u * (a : G)⁻¹)⁻¹ := by rw [h1]
      _ = u * a * u⁻¹ * (a : G)⁻¹ := by group

theorem lt_rParam (hF : SecA.NatFacts) (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder)
    (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4) : (n : ℕ∞) < E3.rParam (fsuV T I) := by
  obtain ⟨-, V₂, -, -, hV₂, -⟩ := SecA.exists_isVi hF h1102 s.hyp
  have h12 := SecA.IsVi.mono₁₂ hF h1102 s.hyp s.hV₁ hV₂
  have hnG2 : ¬ KindG2 L (fsuV T I) n := fun hk => by
    rcases s.kind h1134 with h | h
    · exact SecA.kind_not_SL3_G2 hG2 s.two_le h hk
    · exact SecA.kind_not_Sp4_G2 hG2 s.two_le h hk
  rcases (h1122 G T L I n n V₁ V₂ s.hyp s.hV₁ hV₂ (Or.inr ⟨hnG2, rfl⟩)).2.2.1 with h | ⟨-, -, hC⟩
  · exact h
  · exfalso
    apply hC
    have hN := (h1134 G T L I n V₁ H g s.hyp s.hV₁ s.h31 s.hnot s.hAT s.hAC).2.2.2
    intro x hx
    have hx1 : x ∈ Subgroup.centralizer (V₁ : Set G) := Subgroup.centralizer_le h12 hx
    exact (hN (Subgroup.centralizer_le_normalizer _ hx1)).1

theorem VZ_le_normalizer_A (hAS : FactAStarSylow) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    VZ T H ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
  have : IsMulCommutative ↥(VZ T H) := s.isElemAbelian_VZ.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : conjSubgroup (fsuV T I) g ≤ Subgroup.normalizer (VZ T H : Set G) :=
    s.hAT.trans (s.T_le.trans (le_normalizer_VZ T H))
  have hidx : (conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (VZ T H : Set G)).relIndex
      (conjSubgroup (fsuV T I) g) = 2 ^ n := by
    rw [← card_autOn_eq_relIndex hAN]
    exact s.card_aStar hAS hF h1102 hG2 h1122 h1134 h1135 h1136
  have hm : E3.mQuot (conjSubgroup (fsuV T I) g)
      (conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (VZ T H : Set G)) = n := by
    unfold E3.mQuot
    rw [hidx, padicValNat.prime_pow]
  have hr : (n : ℕ∞) < E3.rParam (conjSubgroup (fsuV T I) g) := by
    rw [E3.rParam_conj]
    exact s.lt_rParam hF h1102 hG2 h1122 h1134
  by_contra hne
  have hC : ¬ Subgroup.centralizer ((conjSubgroup (fsuV T I) g ⊓
      Subgroup.centralizer (VZ T H : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
    intro h
    apply hne
    intro v hv
    apply h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx.2 v hv).symm
  have h1 := E3.rParam_le_mQuot inf_le_left hC
  rw [hm] at h1
  exact absurd hr (not_lt.mpr h1)

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
