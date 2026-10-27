module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Milestones.ASVolI.C1
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped MatrixGroups

theorem burnsideC121_eq_one_of_mulVec {F : Type} [Field F] (g : SL(2, F))
    (h : ∀ v : Fin 2 → F, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : g = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
  rw [h1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, Pi.single_apply]

theorem burnsideC121_card_commutator_sl2_two {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) : Nat.card (commutator SL(2, F)) = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])
  let φ : SL(2, F) →* SL(2, ZMod 2) := Matrix.SpecialLinearGroup.map e.toRingHom
  let ψ : SL(2, ZMod 2) →* SL(2, F) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφψ : ∀ g, φ (ψ g) = g := fun g => by
    ext i j
    simp [φ, ψ, Matrix.SpecialLinearGroup.map_apply_coe]
  have hψφ : ∀ g, ψ (φ g) = g := fun g => by
    ext i j
    simp [φ, ψ, Matrix.SpecialLinearGroup.map_apply_coe]
  have hφi : Function.Injective φ := fun a b hab => by
    rw [← hψφ a, ← hψφ b, hab]
  have hφs : Function.Surjective φ := fun g => ⟨ψ g, hφψ g⟩
  have hmap : (commutator SL(2, F)).map φ = commutator SL(2, ZMod 2) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 hφs]
  rw [← Subgroup.card_map_of_injective hφi, hmap]
  have h1 := CFSG.Quasithin.C1Pack.commutator_sl2_eq
  have h2 := CFSG.Quasithin.C1Pack.card_sl2A3
  unfold CFSG.Quasithin.C1Pack.SL2F2 at h1 h2
  rw [h1, h2]

section NatData

variable {Ω : Type} [Group Ω] {Y W : Subgroup Ω} {F : Type} [Field F]

theorem burnsideC121_inf_centralizer_le (α : ↥Y →* SL(2, F))
    (β : ↥W →* Multiplicative (Fin 2 → F)) (hαk : α.ker = (pCoreOf 2 Y).subgroupOf Y)
    (hβs : Function.Surjective β)
    (hβe : ∀ (k : ↥Y) (u v : ↥W), (v : Ω) = k * u * k⁻¹ →
      Multiplicative.toAdd (β v) =
        (α k : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    Y ⊓ Subgroup.centralizer (W : Set Ω) ≤ pCoreOf 2 Y := by
  rintro y ⟨hyY, hyC⟩
  have h1 : α ⟨y, hyY⟩ = 1 := by
    apply burnsideC121_eq_one_of_mulVec
    intro v
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
    have hc : (u : Ω) * y = y * u := Subgroup.mem_centralizer_iff.1 hyC u u.2
    have h2 := hβe ⟨y, hyY⟩ u u (by
      show (u : Ω) = y * u * y⁻¹
      rw [← hc, mul_inv_cancel_right])
    rw [hu] at h2
    exact h2.symm
  have h3 : (⟨y, hyY⟩ : ↥Y) ∈ α.ker := h1
  rw [hαk, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem burnsideC121_normal_dichotomy [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (α : ↥Y →* SL(2, F))
    (hαk : α.ker = (pCoreOf 2 Y).subgroupOf Y) (hαr : α.range = commutator SL(2, F))
    {N : Subgroup Ω} (hNY : N ≤ Y) (hYN : Y ≤ Subgroup.normalizer (N : Set Ω)) :
    N ≤ pCoreOf 2 Y ∨ ∀ y ∈ Y, ∃ m ∈ N, ∃ o ∈ pCoreOf 2 Y, y = m * o := by
  classical
  set N' : Subgroup SL(2, F) := (N.subgroupOf Y).map α with hN'
  have hN'le : N' ≤ α.range := by
    rintro _ ⟨m, -, rfl⟩
    exact ⟨m, rfl⟩
  have hN'n : ∀ g ∈ α.range, ∀ x ∈ N', g * x * g⁻¹ ∈ N' := by
    rintro _ ⟨k, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨k * m * k⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hm' : (m : Ω) ∈ N := hm
    show ((k * m * k⁻¹ : ↥Y) : Ω) ∈ N
    exact (Subgroup.mem_normalizer_iff.1 (hYN k.2) m).1 hm'
  have hdich : N' = ⊥ ∨ α.range ≤ N' := by
    by_cases hn2 : 2 ≤ n
    · have h4 : 4 ≤ Nat.card F := by
        rw [Nat.card_eq_fintype_card, hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : CharP F 2 := charP_of_card_eq_prime_pow hF
      have hs : IsSimpleGroup SL(2, F) := CFSG.Quasithin.C126.Nat.isSimpleGroup_sl2 h4
      have htop : α.range = ⊤ := by rw [hαr, CFSG.Quasithin.C126.Nat.commutator_sl2_eq_top h4]
      have hnorm : N'.Normal := ⟨fun x hx g => hN'n g (by rw [htop]; trivial) x hx⟩
      rcases hnorm.eq_bot_or_eq_top with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ le_top)
    · have hn1 : n = 1 := by omega
      subst hn1
      have h3 : Nat.card α.range = 3 := by
        rw [hαr]; exact burnsideC121_card_commutator_sl2_two (by simpa using hF)
      have hdvd : Nat.card (N'.subgroupOf α.range) ∣ 3 := by
        rw [← h3]; exact Subgroup.card_subgroup_dvd_card _
      have hcard : Nat.card (N'.subgroupOf α.range) = Nat.card N' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN'le).toEquiv
      rw [hcard] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact Or.inl (Subgroup.eq_bot_of_card_eq N' h)
      · right
        have hle : N'.subgroupOf α.range = ⊤ := by
          apply Subgroup.eq_top_of_card_eq
          rw [hcard, h, h3]
        intro x hx
        have : (⟨x, hx⟩ : ↥α.range) ∈ N'.subgroupOf α.range := by rw [hle]; trivial
        exact this
  rcases hdich with h | h
  · left
    intro m hm
    have hmem : α ⟨m, hNY hm⟩ ∈ N' := ⟨⟨m, hNY hm⟩, hm, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hk : (⟨m, hNY hm⟩ : ↥Y) ∈ α.ker := hmem
    rw [hαk, Subgroup.mem_subgroupOf] at hk
    exact hk
  · right
    intro y hy
    obtain ⟨m, hm, hmy⟩ := h ⟨⟨y, hy⟩, rfl⟩
    refine ⟨m, hm, (m : Ω)⁻¹ * y, ?_, by simp⟩
    have hk : (m⁻¹ * ⟨y, hy⟩ : ↥Y) ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmy, inv_mul_cancel]
    rw [hαk, Subgroup.mem_subgroupOf] at hk
    exact hk

end NatData

end CFSG.ASVolI
