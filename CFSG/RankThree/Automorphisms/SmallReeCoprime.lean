module

public import CFSG.RankThree.Automorphisms.SylowScalarFrattiniCoprime
public import CFSG.LieType.Ree.SmallReeModelSchreier

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial

theorem small_Ree_gamma_coprime_automorphism_subgroups_cyclic (a : ℕ) (ha : 1 ≤ a) (K : Type)
    [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hpΓ : ¬ p ∣ Nat.card (ReeTag.G2.reeGamma K a)) :
    ∀ P : Subgroup (MulAut (ReeTag.G2.reeGamma K a)), IsPGroup p P → IsCyclic P := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨hn, hηξ, hfaith, htrans, -, -, hreg, hcardΩ, -, -, ⟨⟨P, hPp, hPmax⟩, rfl⟩, hstab, hUn,
    -, hNUV⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  obtain ⟨-, -, -, -, -, -, -, hΦ₀, π, -, hπs, hπker, e₀, he₀, hT₀⟩ :=
    small_Ree_positive_Frattini_quotient a ha K hK
  set Γ := ReeTag.G2.reeGamma K a
  set B' := (ReeTag.G2.reeFixedBorel K a).subgroupOf Γ
  set U' := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf Γ
  set n' : Γ := ⟨_, hn⟩
  have hUΓ : ReeTag.G2.reeFixedPosUnipotent K a ≤ Γ := ReeTag.reeFixedPosUnipotent_le_reeGamma
  have hHΓ : ReeTag.G2.reeFixedTorus K a ≤ Γ :=
    ReeTag.reeFixedTorus_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma
  have hq : 3 ≤ 3 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 3
  have hq3 : 3 ≤ (3 ^ (2 * a + 1)) ^ 3 := hq.trans (Nat.le_self_pow (by norm_num) _)
  have hΩ : 3 ≤ Nat.card (Γ ⧸ B') := by
    rw [hcardΩ]
    omega
  set ι : U' ≃* ReeTag.G2.reeFixedPosUnipotent K a := Subgroup.subgroupOfEquivOfLe hUΓ
  set π' : U' →* Multiplicative K := π.comp ι.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπs.comp ι.surjective
  have hΦ' : frattini U' = π'.ker := by
    rw [frattini_eq_comap_mulEquiv ι, hπ', ← MonoidHom.comap_ker, hπker, hΦ₀]
  obtain ⟨e, he'⟩ : ∃ e : Additive (U' ⧸ frattini U') ≃+ K,
      ∀ x : U', e (Additive.ofMul (x : U' ⧸ frattini U')) = (π (ι x)).toAdd :=
    ⟨MulEquiv.toAdditiveLeft ((QuotientGroup.quotientMulEquivOfEq hΦ').trans
      (QuotientGroup.quotientKerEquivOfSurjective π' hπ's)), fun x => rfl⟩
  have hee : ∀ x : U', e (Additive.ofMul (x : U' ⧸ frattini U')) =
      e₀ (Additive.ofMul (ι x : ReeTag.G2.reeFixedPosUnipotent K a ⧸
        frattini (ReeTag.G2.reeFixedPosUnipotent K a))) := fun x => by
    rw [he₀, he']
  have hT : (((Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) :
      Set Γ)).subgroupOf (Subgroup.normalizer (U' : Set Γ))).map
        U'.normalizerMonoidHom).map (CFSG.LieType.Ree.frattiniScalarRep e) =
          scalarAddAut K := by
    rw [← hT₀]
    ext f
    constructor
    · rintro ⟨φ, ⟨t, ht, rfl⟩, rfl⟩
      have htH : ((t : Γ) : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a := by
        have h : (t : Γ) ∈ Subgroup.normalizer (U' : Set Γ) ⊓
            Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) :
              Set Γ) :=
          Subgroup.mem_inf.2 ⟨t.2, ht⟩
        rw [hNUV] at h
        exact h
      exact ⟨ReeTag.G2.reeFixedTorusConj K a ⟨_, htH⟩, ⟨_, rfl⟩,
        (frattiniScalarRep_eq_of_comm ι e e₀ hee fun x => Subtype.ext rfl).symm⟩
    · rintro ⟨φ, ⟨h, rfl⟩, rfl⟩
      have hmem : (⟨h, hHΓ h.2⟩ : Γ) ∈ Subgroup.normalizer (U' : Set Γ) ⊓
          Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) : Set Γ) := by
        rw [hNUV]
        exact h.2
      exact ⟨U'.normalizerMonoidHom ⟨_, (Subgroup.mem_inf.1 hmem).1⟩,
        ⟨⟨_, (Subgroup.mem_inf.1 hmem).1⟩, (Subgroup.mem_inf.1 hmem).2, rfl⟩,
        frattiniScalarRep_eq_of_comm ι e e₀ hee fun x => Subtype.ext rfl⟩
  have hUξ : U' ≤ MulAction.stabilizer Γ (QuotientGroup.mk 1 : Γ ⧸ B') := by
    rw [hstab]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ReeTag.reeFixedPosUnipotent_le_reeFixedBorel hx
  have hUn' : (U'.subgroupOf (MulAction.stabilizer Γ (QuotientGroup.mk 1 : Γ ⧸ B'))).Normal := by
    rw [hstab]
    exact hUn
  have hw : n' • (QuotientGroup.mk 1 : Γ ⧸ B') ≠ QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact hηξ
  exact Sylow_scalar_Frattini_coprime_automorphism_subgroups_cyclic hΩ
    (QuotientGroup.mk 1 : Γ ⧸ B') (ℓ := 3) ⟨U', hPp, hPmax⟩ hUξ hUn'
    (fun ω ω' hω hω' => (hreg ω ω' hω hω').exists) n' hw (by omega : 1 ≤ 2 * a + 1) hK e hT
    hp hpΓ

theorem small_Ree_coprime_automorphism_subgroups_cyclic (T : Type) [Group T] (ℓ f : ℕ)
    (hT : ReeTitsModel T .twistedG2 ℓ f) {p : ℕ} (hp : p.Prime) (hpT : ¬ p ∣ Nat.card T) :
    (∀ P : Subgroup (MulAut T), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut T, p ≤ Nat.card α.ker := by
  obtain ⟨-, -, hℓ, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T ℓ f hT
  obtain ⟨-, a', hfa', hmodel⟩ := hT
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  subst hℓ
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a' K hfa' hK ⟨e⟩
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa']
  have hpΓ : ¬ p ∣ Nat.card (ReeTag.G2.reeGamma K a') := by
    rw [← Nat.card_congr E.toEquiv]
    exact hpT
  have hcyc : ∀ P : Subgroup (MulAut T), IsPGroup p P → IsCyclic P := fun P hP =>
    isCyclic_of_isPGroup_of_mulEquiv E
      (small_Ree_gamma_coprime_automorphism_subgroups_cyclic a' (by omega) K hK' hp hpΓ) hP
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
