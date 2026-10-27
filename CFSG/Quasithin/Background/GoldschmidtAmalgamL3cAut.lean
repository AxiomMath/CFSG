module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5AutShape
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutHfpf
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutQ8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section AutFinal

variable {A B : Subgroup D} {z : D} {V : Subgroup D} [Finite D]

theorem autShapes_of_subAm (h : GoldHyp3 A B z V) (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 128) {A' B' : Subgroup D} (s : SubAm A B A' B') :
    (∃ A'' : Subgroup D, A'' ≤ A' ∧ A''.relIndex A' = 2 ∧ Vertex A'' (A'' ⊓ B') ∧
      Nonempty (↥(pCoreOf 2 A'') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
    (∃ q ∈ pCoreOf 2 A', ∃ q' ∈ pCoreOf 2 A', q * q' ≠ q' * q) ∧
    IsCentralProduct₂ ↥(pCoreOf 2 B') (QuaternionGroup 2) (QuaternionGroup 2) ∧
    (∀ y ∈ B', y ≠ 1 → y ^ 3 = 1 → ∀ q ∈ pCoreOf 2 B', y * q * y⁻¹ = q →
      ∀ v ∈ pCoreOf 2 B', q * v = v * q) := by
  obtain ⟨x, a, a₁, a₂, g⟩ := GoldHyp3.exists_gen3 h
  obtain ⟨A'', hle'', hi'', hv'', e₁, hnc⟩ := s.exists_A'' g hU hT
  have hd := s.nData g hU hT
  obtain ⟨q₀, hq₀N, h₀, -⟩ := hd.exists_q₀_invol g hU
  exact ⟨⟨A'', hle'', hi'', hv'', e₁⟩, hnc, hd.isCentralProduct₂ g hU,
    hd.hfpf g hU hq₀N h₀ s.v₂ rfl (s.x_mem g) fun hx => g.x_not ⟨s.le₁ hx.1, s.le₂ hx.2⟩⟩

theorem isGoldCaseAutM12Cat_of_subAm
    (h : GoldHyp3 A B z V)
    (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128) {A' B' : Subgroup D}
    (s : SubAm A B A' B') : IsGoldCaseAutM12Cat B A := by
  obtain ⟨⟨A'', hle'', hi'', hv'', e₁⟩, hnc, h₂, hfpf⟩ := autShapes_of_subAm h hU hT s
  exact GoldAmL5.isGoldCaseAutM12Cat_of_shape h.gold s.le₁ s.le₂ s.idx₁ s.idx₂ s.v₁ s.v₂ hle''
    hi'' hv'' e₁ hnc h₂ hfpf

end AutFinal

end GoldAmL3c

end F6

end CFSG.Quasithin
