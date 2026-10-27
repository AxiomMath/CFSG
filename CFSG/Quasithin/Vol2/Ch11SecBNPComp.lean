module

public import CFSG.Quasithin.Vol2.Ch11SecBNPSec
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open scoped Pointwise

theorem center_eq_bot_of_nonabelian {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hQ
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

theorem secAll_of_components {Γ : Type} [Group Γ] [Finite Γ] {P : GrpPred}
    (hP : IsoInv P) (𝒮 : Set (Subgroup Γ))
    (hS : ∀ S ∈ 𝒮, IsSimpleGroup ↥S ∧ (∃ a b : ↥S, a * b ≠ b * a) ∧ S.IsSubnormal ∧ P ↥S)
    (h2 : ∀ g : Γ, ∃ e : ℕ, g ^ 2 ^ e ∈ sSup 𝒮) : SecAll Γ P := by
  intro H₁ N _ hsn hs hnab
  set π := QuotientGroup.mk' N with hπ
  have hcomp : ∀ S ∈ 𝒮, CFSG.IsComponent S := fun S hS' => by
    obtain ⟨h1, h2, h3, -⟩ := hS S hS'
    exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h2).1, h3⟩
  by_cases hα : ∃ S ∈ 𝒮, S ≤ H₁ ∧ ¬ S.subgroupOf H₁ ≤ N
  ·
    obtain ⟨S, hS𝒮, hSH, hSN⟩ := hα
    obtain ⟨hSs, -, hSsn, hPS⟩ := hS S hS𝒮
    have h1 : ((S.subgroupOf H₁).map π).IsSubnormal :=
      hSsn.subgroupOf.map (QuotientGroup.mk'_surjective N)
    have htop : (S.subgroupOf H₁).map π = ⊤ := by
      rcases h1.eq_bot_or_top_of_isSimpleGroup hs with h | h
      · exfalso
        apply hSN
        intro x hx
        have : π x ∈ (S.subgroupOf H₁).map π := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff x).mp this
      · exact h
    let φ : ↥S →* ↥H₁ ⧸ N := π.comp (Subgroup.inclusion hSH)
    have hφs : Function.Surjective φ := by
      intro q
      have hq : q ∈ (S.subgroupOf H₁).map π := by rw [htop]; trivial
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨(x : Γ), hx⟩, rfl⟩
    have hφi : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
      · exact h
      · exfalso
        apply hSN
        intro x hx
        have hk : (⟨(x : Γ), hx⟩ : ↥S) ∈ φ.ker := by rw [h]; trivial
        rw [MonoidHom.mem_ker] at hk
        exact (QuotientGroup.eq_one_iff x).mp hk
    exact hP _ _ (MulEquiv.ofBijective φ ⟨hφi, hφs⟩).symm hPS
  ·
    push Not at hα
    set Nh : Subgroup Γ := N.map H₁.subtype with hNh
    set A : Subgroup Γ := sSup {S | S ∈ 𝒮 ∧ S ≤ H₁} with hA
    set C : Subgroup Γ := sSup {S | S ∈ 𝒮 ∧ ⁅S, H₁⁆ = ⊥} with hC
    have hAN : A ≤ Nh := sSup_le fun S ⟨hS𝒮, hSH⟩ x hx =>
      ⟨⟨x, hSH hx⟩, hα S hS𝒮 hSH (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
    have hNhH : Nh ≤ H₁ := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hCc : C ≤ Subgroup.centralizer (H₁ : Set Γ) :=
      sSup_le fun S ⟨_, hc⟩ => Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    have hsup : sSup 𝒮 ≤ A ⊔ C := sSup_le fun S hS𝒮 => by
      rcases CFSG.LocalCores.component_subnormal_subgroup (hcomp S hS𝒮) hsn with h | h
      · exact le_sup_of_le_left (le_sSup ⟨hS𝒮, h⟩)
      · exact le_sup_of_le_right (le_sSup ⟨hS𝒮, h⟩)
    have hZ := center_eq_bot_of_nonabelian hnab
    have hAC : A ≤ Subgroup.normalizer (C : Set Γ) :=
      ((hAN.trans hNhH).trans (Subgroup.le_centralizer_iff.mp hCc)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hcent : ∀ x : ↥H₁, (x : Γ) ∈ A ⊔ C → π x = 1 := by
      intro x hx
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A C hAC] at hx
      obtain ⟨a, ha, c, hc, hac⟩ := hx
      obtain ⟨n, hnN, hn⟩ := hAN ha
      have hcH : c ∈ H₁ := by
        have : c = a⁻¹ * x := by rw [← hac]; group
        rw [this]
        exact H₁.mul_mem (H₁.inv_mem (hNhH (hAN ha))) x.2
      set c' : ↥H₁ := ⟨c, hcH⟩
      have hxnc : x = n * c' := by
        apply Subtype.ext
        simp [c', ← hac, ← hn]
      have hc'Z : π c' ∈ Subgroup.center (↥H₁ ⧸ N) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
        have hyc : (y : Γ) * c = c * y := Subgroup.mem_centralizer_iff.mp (hCc hc) y y.2
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hyc
      rw [hZ, Subgroup.mem_bot] at hc'Z
      rw [hxnc, map_mul, hc'Z, mul_one]
      exact (QuotientGroup.eq_one_iff n).mpr hnN
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP2 : IsPGroup 2 (↥H₁ ⧸ N) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
      obtain ⟨e, he⟩ := h2 (x : Γ)
      refine ⟨e, ?_⟩
      rw [← map_pow]
      exact hcent _ (hsup (by simpa using he))
    have hnt := hP2.center_nontrivial
    rw [hZ] at hnt
    exact ((not_nontrivial_iff_subsingleton.mpr inferInstance) hnt).elim

end CFSG.Quasithin.Vol2.Ch11.SecB
