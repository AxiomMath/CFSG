module

public import CFSG.Quasithin.Vol2.Ch11SecBK4S
public import CFSG.GroupTheory.SolvableMinimalNormalNode
public import CFSG.Quasithin.Vol2.Ch11G2Q8Siegel

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
open scoped IsMulCommutative

namespace BK4

variable {F : Type} [Field F] [CharP F 2]

theorem normalizer_U0_le_stabQ [Finite F] {h : ℕ} (hh : h ≤ 6) :
    Subgroup.normalizer (G2Q8.U0 F : Set ↥(cayleyGroup F)) ≤ G2Q8.stabQ (G2Q8.stdF F h) := by
  intro b hb
  have hS : G2Q8.U0Stable (G2Q8.gmapG b (G2Q8.stdF F h)) := by
    intro u hu x hx
    rw [G2Q8.mem_gmapG] at hx ⊢
    have hu' : b⁻¹ * u * b ∈ G2Q8.U0 F := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) u).mp hu
      rwa [inv_inv] at this
    have h1 := G2Q8.stdF_stable h _ hu' _ hx
    rwa [G2Q8.g2Act_mul_apply, G2Q8.g2Act_mul_apply, G2Q8.g2Act_apply_inv] at h1
  have heq := G2Q8.eq_stdF_of_card hS (i := h) (by rw [G2Q8.card_gmapG, G2Q8.card_stdF hh])
  refine G2Q8.mem_stabQ.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · rw [← heq, G2Q8.mem_gmapG, G2Q8.g2Act_inv_apply]
    exact hw
  · rw [← heq, G2Q8.mem_gmapG, G2Q8.g2Act_inv_apply] at hw
    exact hw

theorem le_U0_of_normalizes [Finite F] {n : ℕ} (hK : Nat.card F = 2 ^ n)
    {X : Subgroup ↥(cayleyGroup F)} (hX : IsPGroup 2 X)
    (hUX : G2Q8.U0 F ≤ Subgroup.normalizer (X : Set ↥(cayleyGroup F))) : X ≤ G2Q8.U0 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup := hX.to_sup_of_normal_left' G2Q8.isPGroup_U0 hUX
  have hmax := (IsPGroup.toSylow G2Q8.isPGroup_U0
    (G2Q8.not_two_dvd_index_U0 hK (one_le_of_card hK))).is_maximal' hsup le_sup_right
  intro x hx
  have hmem : x ∈ X ⊔ G2Q8.U0 F := le_sup_left (b := G2Q8.U0 F) hx
  rw [hmax] at hmem
  exact hmem

theorem le_normalizer_U0_of_isSolvable [Finite F] {n : ℕ} (hK : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) {Y : Subgroup ↥(cayleyGroup F)} (hY : Group.IsSolvable Y)
    (hU : G2Q8.U0 F ≤ Y) : Y ≤ Subgroup.normalizer (G2Q8.U0 F : Set ↥(cayleyGroup F)) := by
  have h4 := four_le_of_card hK hn
  have := G2Q8.finite_cayleyGroup (F := F)
  have hYne : (⊤ : Subgroup ↥Y) ≠ ⊥ := by
    intro h
    have h1 : (⟨G2Q8.tL 1, hU (tL_mem_U0 1)⟩ : ↥Y) ∈ (⊤ : Subgroup ↥Y) := Subgroup.mem_top _
    rw [h, Subgroup.mem_bot] at h1
    exact G2Q8.tL_one_ne_one (congrArg Subtype.val h1)
  have : Finite (Subgroup ↥Y) :=
    Finite.of_injective (fun K : Subgroup ↥Y => (K : Set ↥Y)) SetLike.coe_injective
  let 𝓝 : Set (Subgroup ↥Y) := {N | N.Normal ∧ N ≠ ⊥}
  obtain ⟨M, hM⟩ := 𝓝.toFinite.exists_minimal ⟨⊤, inferInstance, hYne⟩
  obtain ⟨hMn, hMb⟩ := hM.prop
  have hmin : ∀ K : Subgroup ↥Y, K.Normal → K ≠ ⊥ → K ≤ M → K = M := fun K hK hKb hKM =>
    le_antisymm hKM (hM.le_of_le ⟨hK, hKb⟩ hKM)
  obtain ⟨r, d, hr, -, hEA, hcard⟩ :=
    CFSG.SolvableHall.solvable_minimal_normal_elementary_abelian hY M hMb hmin
  set N := M.map Y.subtype with hN
  have hNY : N ≤ Y := Subgroup.map_subtype_le M
  have hNb : N ≠ ⊥ := fun h => hMb ((Subgroup.map_eq_bot_iff_of_injective M
    Y.subtype_injective).mp h)
  have hconj : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
    rintro y hy _ ⟨m, hm, rfl⟩
    exact ⟨⟨y, hy⟩ * m * ⟨y, hy⟩⁻¹, hMn.conj_mem m hm ⟨y, hy⟩, rfl⟩
  have hYN : Y ≤ Subgroup.normalizer (N : Set ↥(cayleyGroup F)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj y hy x, fun hx => ?_⟩
    have := hconj y⁻¹ (Y.inv_mem hy) _ hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this
  have hcardN : Nat.card N = r ^ d := by
    rw [hN, Subgroup.card_map_of_injective Y.subtype_injective, hcard]
  by_cases hr2 : r = 2
  swap
  ·
    exfalso
    have hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := hEA
      have h1 := mul_comm (⟨a, ha⟩ : ↥M) ⟨b, hb⟩
      exact congrArg (fun z : ↥M => ((z : ↥Y) : ↥(cayleyGroup F))) h1
    have hodd : Odd (Nat.card N) := by
      rw [hcardN]
      exact (hr.odd_of_ne_two hr2).pow
    exact hNb (eq_bot_of_odd_of_le_normalizer hK hn hY hU hNY hNc hodd (hU.trans hYN))
  subst hr2
  have hN2 : IsPGroup 2 N := by
    have := hEA
    exact (IsElementaryAbelian.isPGroup 2 ↥M).map Y.subtype
  have hNU := le_U0_of_normalizes hK hN2 (hU.trans hYN)
  let C : Submodule F (Ix3 → F) :=
    { carrier := {w | ∀ g ∈ N, g2Act g w = w}
      add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
      zero_mem' := fun g _ => map_zero _
      smul_mem' := fun c w hw g hg => by rw [G2Q8.g2Act_smul, hw g hg] }
  have hmemC : ∀ w, w ∈ C ↔ ∀ g ∈ N, g2Act g w = w := fun w => Iff.rfl
  have hfixC : ∀ y ∈ Y, ∀ w ∈ C, g2Act y w ∈ C := by
    intro y hy w hw g hg
    have hg' : y⁻¹ * g * y ∈ N := by
      have := hconj y⁻¹ (Y.inv_mem hy) g hg
      rwa [inv_inv] at this
    calc g2Act g (g2Act y w) = g2Act y (g2Act (y⁻¹ * g * y) w) := by
          rw [← G2Q8.g2Act_mul_apply, ← G2Q8.g2Act_mul_apply,
            show y * (y⁻¹ * g * y) = g * y by group]
      _ = g2Act y w := by rw [hw _ hg']
  obtain ⟨h, h6, hCh⟩ := G2Q8.eq_stdF_of_stable (S := C) fun u hu w hw => hfixC u (hU hu) w hw
  have hh1 : 1 ≤ h := by
    by_contra h0
    have h00 : h = 0 := by omega
    have hu0 : G2Q8.eu 0 (1 : F) ∈ C := fun g hg =>
      G2Q8.U0_fix_one (hNU hg) (G2Q8.mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩)
    rw [hCh, h00, G2Q8.stdF_zero] at hu0
    exact G2Q8.g2Act_eu_ne_zero 1 (by rw [map_one]; exact hu0)
  have hh5 : h ≤ 5 := by
    by_contra h7
    have h66 : h = 6 := by omega
    apply hNb
    refine eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr (G2Q8.cayley_eq_one fun w => ?_)
    have hw : w ∈ C := by rw [hCh, h66, G2Q8.stdF_six]; exact Submodule.mem_top
    exact hw g hg
  have hYC : Y ≤ G2Q8.stabQ (G2Q8.stdF F h) := by
    intro y hy
    rw [← hCh]
    refine G2Q8.mem_stabQ.mpr fun w => ⟨hfixC y hy w, fun hw => ?_⟩
    have := hfixC y⁻¹ (Y.inv_mem hy) _ hw
    rwa [G2Q8.g2Act_inv_apply] at this
  rcases stabQ_stdF_le (F := F) hh1 hh5 with h1 | h2
  · exact le_normalizer_of_le_stabQ_one h4 hK hY hU (hYC.trans h1)
  · exact le_normalizer_of_le_stabQ_one h4 hK hY hU
      (le_stabQ_one_of_le_stabQ_two h4 hY hU (hYC.trans h2))

theorem le_stabQ_of_isSolvable [Finite F] {n : ℕ} (hK : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    {Y : Subgroup ↥(cayleyGroup F)} (hY : Group.IsSolvable Y) (hU : G2Q8.U0 F ≤ Y) {h : ℕ}
    (hh : h ≤ 6) : Y ≤ G2Q8.stabQ (G2Q8.stdF F h) :=
  (le_normalizer_U0_of_isSolvable hK hn hY hU).trans (normalizer_U0_le_stabQ hh)

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
