module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.exists_actionHom_LB (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    ∃ Φ : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E),
      (∀ (r : ↥(LB M Q B)) (y : G), y ∈ Q →
        M₀.π ((r : G) * y * (r : G)⁻¹) = Φ r (M₀.π y)) ∧
      (∀ r : ↥(LB M Q B), Φ r = 1 ↔ (r : G) ∈ Q) ∧
      ∀ (r : ↥(LB M Q B)) e, M₀.Qf (Φ r e) = M₀.Qf e := by
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  exact ⟨φ.comp (Subgroup.inclusion hc.LB_le_H0),
    fun r y hy => hφπ (Subgroup.inclusion hc.LB_le_H0 r) y hy,
    fun r => hφker (Subgroup.inclusion hc.LB_le_H0 r),
    fun r e => hφiso (Subgroup.inclusion hc.LB_le_H0 r) e⟩

theorem card_eq_card_mul_range {H : Subgroup G} {X : Type*} [Group X] (hQH : Q ≤ H)
    (Φ : ↥H →* X) (hker : ∀ r : ↥H, Φ r = 1 ↔ (r : G) ∈ Q) :
    Nat.card H = Nat.card Q * Nat.card Φ.range := by
  have hkerΦ : Φ.ker = Q.subgroupOf H := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker s
  have h1 : Nat.card Φ.ker = Nat.card Q := by
    rw [hkerΦ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem Ctx.exists_mixed_root (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (hng : ¬ GenByB M Q B) : ∃ X : Subgroup G, Ctx M Q Z X ∧ ∃ x ∈ X, M₀.π x ∉ hc.Wn h := by
  by_contra hcon
  push Not at hcon
  apply hng
  have hQN : Q ≤ Lgen M B ⊔ Z := by
    calc Q = ⨆ (g : G) (_ : conjSubgroup g Z ≤ Q), conjSubgroup g Z := hc.hyp.gen
      _ ≤ Lgen M B ⊔ Z := by
        refine iSup₂_le fun g hg => ?_
        by_cases hZg : conjSubgroup g Z = Z
        · rw [hZg]
          exact le_sup_right
        · have hX : Ctx M Q Z (conjSubgroup g Z) := ⟨hc.hyp, ⟨g, rfl⟩, hg, hZg⟩
          intro x hx
          obtain ⟨n, hnN, hnQ, hnx⟩ := hcon _ hX x hx
          have hxQ : x ∈ Q := hg hx
          have hz : n⁻¹ * x ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hnQ hxQ).mp hnx
          have e : x = n * (n⁻¹ * x) := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right hz)
  have hNn : ∀ m ∈ M, ∀ x ∈ Lgen M B, m * x * m⁻¹ ∈ Lgen M B := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M B hm) x).mp hx
  exact (hc.eq_of_le_sup_Z hc.Lgen_le_Q hNn hQN).symm

theorem Ctx.img_eq_line_of_ne (hX : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {x : G}
    (hx : x ∈ B) (hπ : M₀.π x ≠ 0) :
    ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • M₀.π x := by
  obtain ⟨b, hb0, -, hB, -⟩ := hX.dictB h
  obtain ⟨s₀, hs₀⟩ := (hB _).mp (M₀.pi_mem_img hx (hX.le hx))
  have hs₀0 : s₀ ≠ 0 := fun h0 => hπ (by rw [hs₀, h0, zero_smul])
  intro v
  rw [hB]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨s * s₀⁻¹, ?_⟩
    rw [hs₀, smul_smul, mul_assoc, inv_mul_cancel₀ hs₀0, mul_one]
  · rintro ⟨s, rfl⟩
    exact ⟨s * s₀, by rw [hs₀, smul_smul]⟩

end CFSG.RankThree.GF2n.Stroth80
