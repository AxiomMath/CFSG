module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5F

public section

namespace CFSG.Quasithin.Stroth.G5F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.LieType.Ree

theorem commutator_mem_pCoreOf_of_mem_zpowers {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {g : G} (hg : ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∀ x ∈ Subgroup.zpowers g, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.mem_normalizer_fintype fun l hl => by
    simpa using L.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 L (hg l hl)) hl
  have hgK : g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hgL
  have hpow : ∀ n : ℕ, ∀ l ∈ L, g ^ n * l * (g ^ n)⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro n
    induction n with
    | zero => intro l _; simp
    | succ n ih =>
      intro l hl
      have e : g ^ (n + 1) * l * (g ^ (n + 1))⁻¹ * l⁻¹ =
          g * (g ^ n * l * (g ^ n)⁻¹ * l⁻¹) * g⁻¹ * (g * l * g⁻¹ * l⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 L).mul_mem ((Subgroup.mem_normalizer_iff.mp hgK _).mp (ih l hl)) (hg l hl)
  intro x hx l hl
  obtain ⟨n, -, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hx : x ∈ Submonoid.powers g)
  exact hpow n l hl

theorem conf_fix {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : Hyp111 L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hQ : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10)
    {d₁ d₂ : G} {m₀ : ZMod (2 ^ (2 * a + 1) - 1)} (hd₁ : d₁ ∈ borelOf L1 S)
    (hd₂ : d₂ ∈ L1 ⊔ bigB L1 L2 S) (hodd₁ : Odd (orderOf d₁)) (hodd₂ : Odd (orderOf d₂))
    (hcomm : Commute d₁ d₂)
    (hN1L : ∀ x ∈ Subgroup.zpowers (d₁ ^ (-m₀).val * d₂), ∀ l ∈ L1,
      x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) :
    (∀ δ ∈ Subgroup.zpowers d₁, δ ≠ 1 →
        pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({δ} : Set G) =
          pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
            Subgroup.centralizer (Subgroup.zpowers d₁ : Set G)) ∧
      (∃ k : ℕ, (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
          Subgroup.centralizer (Subgroup.zpowers d₁ : Set G)).relIndex
            (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ (4 * k)) ∧
      ∃ k : ℕ, (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer
          ((Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂ : Subgroup G) : Set G)).relIndex
          (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
            Subgroup.centralizer (Subgroup.zpowers (d₁ ^ (-m₀).val * d₂) : Set G)) =
        (2 ^ (2 * a + 1)) ^ (4 * k) := by
  set g := d₁ ^ (-m₀).val * d₂ with hg
  have hd₁L : d₁ ∈ L1 ⊔ bigB L1 L2 S :=
    Subgroup.mem_sup_left ((show borelOf L1 S ≤ L1 from inf_le_left) hd₁)
  have hgcomm : Commute d₁ g := ((Commute.refl d₁).pow_right _).mul_right hcomm
  have hoddg : Odd (orderOf g) :=
    Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨Odd.of_dvd_nat hodd₁ (orderOf_pow_dvd _), hodd₂⟩)
      (hcomm.pow_left _).orderOf_mul_dvd_mul_orderOf
  have hD1N1 : Subgroup.zpowers d₁ ≤ Subgroup.normalizer (Subgroup.zpowers g : Set G) :=
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((hgcomm.zpow_right k).eq).symm)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQ' : Nat.card (Q1 L1 L2 S) < 2 ^ (16 * (2 * a + 1)) := by
    rw [show Nat.card (Q1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 10 from hQ, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨hA, ⟨k, hk⟩, ⟨k', hk'⟩⟩ := str83G5FactF_holds G L1 L2 S a hF ha hSz hB hQ'
    (Subgroup.zpowers d₁) (Subgroup.zpowers g) (Subgroup.zpowers_le.mpr hd₁)
    (by rwa [Nat.card_zpowers]) (Subgroup.zpowers_le.mpr (mul_mem (pow_mem hd₁L _) hd₂))
    (by rwa [Nat.card_zpowers]) hN1L hD1N1
  have hsup : Subgroup.zpowers d₁ ⊔ Subgroup.zpowers g =
      Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂ := by
    refine le_antisymm (sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_))
      (sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_))
    · exact mul_mem (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers d₁)) _)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers d₂))
    · rw [show d₂ = (d₁ ^ (-m₀).val)⁻¹ * g by rw [hg, inv_mul_cancel_left]]
      exact mul_mem (inv_mem (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers d₁)) _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  refine ⟨hA, ⟨k, ?_⟩, ⟨k', ?_⟩⟩
  · rw [show _ = 2 ^ (4 * (2 * a + 1) * k) from hk, ← pow_mul]
    ring_nf
  · rw [← hsup, show _ = 2 ^ (4 * (2 * a + 1) * k') from hk', ← pow_mul]
    ring_nf

theorem conf_fix_of_gen {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : Hyp111 L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hQ : Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10)
    {d₁ d₂ : G} {m₀ : ZMod (2 ^ (2 * a + 1) - 1)} (hd₁ : d₁ ∈ borelOf L1 S)
    (hd₂ : d₂ ∈ L1 ⊔ bigB L1 L2 S) (hodd₁ : Odd (orderOf d₁)) (hodd₂ : Odd (orderOf d₂))
    (hcomm : Commute d₁ d₂)
    (hN1L : ∀ l ∈ L1, d₁ ^ (-m₀).val * d₂ * l * (d₁ ^ (-m₀).val * d₂)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) :
    (∀ δ ∈ Subgroup.zpowers d₁, δ ≠ 1 →
        pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({δ} : Set G) =
          pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
            Subgroup.centralizer (Subgroup.zpowers d₁ : Set G)) ∧
      (∃ k : ℕ, (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
          Subgroup.centralizer (Subgroup.zpowers d₁ : Set G)).relIndex
            (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ (4 * k)) ∧
      ∃ k : ℕ, (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer
          ((Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂ : Subgroup G) : Set G)).relIndex
          (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
            Subgroup.centralizer (Subgroup.zpowers (d₁ ^ (-m₀).val * d₂) : Set G)) =
        (2 ^ (2 * a + 1)) ^ (4 * k) :=
  conf_fix hF ha hSz hB hQ hd₁ hd₂ hodd₁ hodd₂ hcomm
    (commutator_mem_pCoreOf_of_mem_zpowers hN1L)

end CFSG.Quasithin.Stroth.G5F

end
