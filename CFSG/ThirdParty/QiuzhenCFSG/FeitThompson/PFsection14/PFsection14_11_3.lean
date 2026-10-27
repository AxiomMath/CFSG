module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_11_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.11.3)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

public theorem section14EtaData_of_sourceData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2
      P Q U V C D Sfam Tfam τS τT p q u v c d) :
    ∃ η : Fin q → Fin p → Section1.ClassFunction G,
      section14EtaData Smax Tmax W W1 W2 p q η := by
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, hNotation, _hChoice, _hMin⟩
  rcases hNotation with
    ⟨ω, ηNat, μ, ν, μsum, νsum, δ, δ', σ, hNotationFor⟩
  refine ⟨fun i j => ηNat (i : ℕ) (j : ℕ), ?_⟩
  exact
    ⟨ω, ηNat, μ, ν, μsum, νsum, δ, δ', σ, hNotationFor,
      by intro i j; rfl⟩

public theorem section14_eta_zero_zero_apply
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    (heta : section14EtaData Smax Tmax W W1 W2 p q η)
    {i : Fin q} {j : Fin p}
    (hi : (i : ℕ) = 0)
    (hj : (j : ℕ) = 0)
    (g : G) :
    η i j g = 1 := by
  rcases heta with
    ⟨ω, ηNat, _μ, _ν, _μsum, _νsum, _δ, _δ', σ, hNotationFor, hηFin⟩
  rcases hNotationFor with
    ⟨hω, hσ, hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩
  rcases hω with ⟨_h31, hq, hp, ωFin, hωFin, hωNat⟩
  rcases hσ with
    ⟨_hIso, _hVirt, _hInd, _hClass, hσprincipal, _hAgree, _hVanish⟩
  have hω00 : ω 0 0 = Section1.principalCharacter W := by
    calc
      ω 0 0 = ωFin ⟨0, hq⟩ ⟨0, hp⟩ := hωNat 0 0 hq hp
      _ = Section1.principalCharacter W := hωFin.principal
  have hη00 : ηNat 0 0 = Section1.principalCharacter G := by
    calc
      ηNat 0 0 = σ (ω 0 0) := hη 0 0 hq hp
      _ = σ (Section1.principalCharacter W) := by rw [hω00]
      _ = Section1.principalCharacter G := hσprincipal
  calc
    η i j g = ηNat (i : ℕ) (j : ℕ) g := by rw [hηFin i j]
    _ = ηNat 0 0 g := by rw [hi, hj]
    _ = (Section1.principalCharacter G) g := by rw [hη00]
    _ = 1 := Section1.principalCharacter_apply g

public theorem section14_characterValueOrder_natCard_of_irreducible_cyclic
    {H : Type u} [Group H] [Finite H] [IsCyclic H]
    {χ : Section1.ClassFunction H}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section3.characterValueOrder χ (Nat.card H) := by
  constructor
  · exact Nat.card_pos
  · intro g
    rcases hχ with ⟨n, ρ, hirr, hχeq⟩
    letI : CommGroup H := IsCyclic.commGroup
    haveI : IsMulCommutative H := ⟨⟨mul_comm⟩⟩
    haveI : Representation.IsIrreducible ρ := hirr
    have hdim : Module.finrank ℂ (Fin n → ℂ) = 1 :=
      Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)
    obtain ⟨c, hc, _hcuniq⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
    have hχc : χ g = c := by
      rw [hχeq, Representation.character, hc]
      simp [hdim]
    have hpow : (ρ g) ^ Nat.card H = 1 := by
      rw [← MonoidHom.map_pow, pow_card_eq_one', MonoidHom.map_one]
    have hsmul_one_pow_end (N : ℕ) :
        ((c • (1 : Module.End ℂ (Fin n → ℂ))) ^ N) =
          (c ^ N) • (1 : Module.End ℂ (Fin n → ℂ)) := by
      induction N with
      | zero => simp
      | succ N ih =>
          rw [pow_succ, ih, pow_succ]
          ext v i
          simp [mul_smul]
          ring
    have hsmul :
        (c ^ Nat.card H) • (1 : Module.End ℂ (Fin n → ℂ)) =
          (1 : Module.End ℂ (Fin n → ℂ)) := by
      calc
        (c ^ Nat.card H) • (1 : Module.End ℂ (Fin n → ℂ)) =
            ((c • (1 : Module.End ℂ (Fin n → ℂ))) ^ Nat.card H) := by
              rw [hsmul_one_pow_end]
        _ = (ρ g) ^ Nat.card H := by
              rw [hc]
              rfl
        _ = 1 := hpow
    have htrace := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) hsmul
    have hcpow : c ^ Nat.card H = 1 := by
      simpa [hdim] using htrace
    simpa [hχc] using hcpow

public theorem section14_exists_exactCharacterValueOrder_of_characterValueOrder
    {H : Type u} [Group H]
    {χ : Section1.ClassFunction H} {a0 : ℕ}
    (h0 : Section3.characterValueOrder χ a0) :
    ∃ a : ℕ, Section3.exactCharacterValueOrder χ a := by
  classical
  let P : ℕ → Prop := fun a => Section3.characterValueOrder χ a
  have hex : ∃ a, P a := ⟨a0, h0⟩
  let a : ℕ := Nat.find hex
  have ha : P a := Nat.find_spec hex
  refine ⟨a, ha, ?_⟩
  intro b hb
  by_contra hndvd
  have ha_pos : 0 < a := ha.1
  let r : ℕ := b % a
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    apply hndvd
    exact (Nat.dvd_iff_mod_eq_zero).2 (by simpa [r] using hr0)
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr_ne_zero
  have hr_lt : r < a := Nat.mod_lt b ha_pos
  have hb_eq : b = a * (b / a) + r := by
    dsimp [r]
    exact (Nat.div_add_mod b a).symm
  have hr_order : P r := by
    refine ⟨hr_pos, ?_⟩
    intro g
    have ha_g := ha.2 g
    have hb_g := hb.2 g
    calc
      χ g ^ r = (χ g ^ a) ^ (b / a) * χ g ^ r := by simp [ha_g]
      _ = χ g ^ (a * (b / a) + r) := by rw [pow_add, pow_mul]
      _ = χ g ^ b := by rw [← hb_eq]
      _ = 1 := hb_g
  have ha_le_r : a ≤ r := Nat.find_min' hex hr_order
  omega

public theorem section14_exists_exactCharacterValueOrder_of_irreducible_cyclic
    {H : Type u} [Group H] [Finite H] [IsCyclic H]
    {χ : Section1.ClassFunction H}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ a : ℕ, Section3.exactCharacterValueOrder χ a :=
  section14_exists_exactCharacterValueOrder_of_characterValueOrder
    (section14_characterValueOrder_natCard_of_irreducible_cyclic hχ)

public theorem section14_pf39_data_of_etaData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    (heta : section14EtaData Smax Tmax W W1 W2 p q η) :
    ∃ hqpos : 0 < q,
    ∃ hppos : 0 < p,
    ∃ ωFin : Fin q → Fin p → Section1.ClassFunction W,
    ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
    ∃ _ : Section3.hypothesis_3_1_statement W1 W2 W,
    ∃ _ : Section3.notation_3_3_statement W1 W2 W
      (Fin q) (Fin p) ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin,
    ∃ _ : Section3.theorem_3_2_map_statement W1 W2 W σ,
      (∀ i j, η i j = σ (ωFin i j)) := by
  rcases heta with
    ⟨ωNat, ηNat, _μ, _ν, _μsum, _νsum, _δ, _δ', σ, hNotationFor, hηFin⟩
  rcases hNotationFor with
    ⟨hωNat, hσ, hηNat, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωNat with ⟨h31, hqpos, hppos, ωFin, hωFin, hωNat_eq⟩
  refine ⟨hqpos, hppos, ωFin, σ, h31, hωFin, hσ, ?_⟩
  intro i j
  calc
    η i j = ηNat (i : ℕ) (j : ℕ) := hηFin i j
    _ = σ (ωNat (i : ℕ) (j : ℕ)) := hηNat (i : ℕ) (j : ℕ) i.isLt j.isLt
    _ = σ (ωFin i j) := by rw [hωNat_eq (i : ℕ) (j : ℕ) i.isLt j.isLt]

public def section14PF39SourceData
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ χ : Fin q → Fin p → Section1.ClassFunction G,
    Section3.IsOrthonormalDoubleFamily χ ∧
      (∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j)) ∧
        χ ⟨0, hqpos⟩ ⟨0, hppos⟩ = Section1.principalCharacter G ∧
          (∀ i j, i ≠ ⟨0, hqpos⟩ → j ≠ ⟨0, hppos⟩ →
            Section1.inducedCF W
                (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) =
              Section1.principalCharacter G - χ i ⟨0, hppos⟩ -
                χ ⟨0, hqpos⟩ j + χ i j) ∧
            (∀ i j, σ (ωFin i j) = χ i j) ∧
              (∀ {c b e : ℕ}, e.Coprime (c * b) →
                ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e) ∧
                ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
                  Section1.IsIrreducibleCharacterOnGroup ω' →
                    Section3.exactCharacterValueOrder ω' a →
                      ∀ g : G, (orderOf g).Coprime a →
                        ∃ r : ℚ, σ ω' g = (r : ℂ)

public def section14PF39CompatibilityData
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {p q : ℕ}
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Fin q → Fin p → Section1.ClassFunction G) : Prop :=
  (∀ i j, σ (ωFin i j) = χ i j) ∧
    (∀ {c b e : ℕ}, e.Coprime (c * b) →
      ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e) ∧
      ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
        Section1.IsIrreducibleCharacterOnGroup ω' →
          Section3.exactCharacterValueOrder ω' a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ r : ℚ, σ ω' g = (r : ℂ)


public theorem section14_pf39_pf35_data_of_sigma
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
    ∃ χ : Fin q → Fin p → Section1.ClassFunction G,
      Section3.IsOrthonormalDoubleFamily χ ∧
        (∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j)) ∧
          χ ⟨0, hqpos⟩ ⟨0, hppos⟩ = Section1.principalCharacter G ∧
            (∀ i j, i ≠ ⟨0, hqpos⟩ → j ≠ ⟨0, hppos⟩ →
              Section1.inducedCF W
                  (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) =
                Section1.principalCharacter G - χ i ⟨0, hppos⟩ -
                  χ ⟨0, hqpos⟩ j + χ i j) ∧
              ∀ i j, σ (ωFin i j) = χ i j := by
  rcases hσ with ⟨hisom, hvirt, hind, _hclass, hprincipal, _hagrees, _hvanish⟩
  let χ : Fin q → Fin p → Section1.ClassFunction G := fun i j => σ (ωFin i j)
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    calc
      Section1.scalarProduct G (χ x.1 x.2) (χ y.1 y.2) =
          Section1.scalarProduct W (ωFin x.1 x.2) (ωFin y.1 y.2) :=
        hisom _ _ (hω.is_class x.1 x.2) (hω.is_class y.1 y.2)
      _ = if x = y then 1 else 0 := by
        simpa using hω.orthonormal x y
  · intro i j
    have hvirtW : Theory.Character.IsVirtualCharacter (ωFin i j) :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hω.irreducible i j)
    have hvirtG : Theory.Character.IsVirtualCharacter (σ (ωFin i j)) :=
      hvirt (ωFin i j) hvirtW
    have hself :
        Section1.scalarProduct G (σ (ωFin i j)) (σ (ωFin i j)) = 1 := by
      calc
        Section1.scalarProduct G (σ (ωFin i j)) (σ (ωFin i j)) =
            Section1.scalarProduct W (ωFin i j) (ωFin i j) :=
          hisom _ _ (hω.is_class i j) (hω.is_class i j)
        _ = 1 := by
          simpa using hω.orthonormal (i, j) (i, j)
    exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirtG hself
  · change σ (ωFin ⟨0, hqpos⟩ ⟨0, hppos⟩) =
      Section1.principalCharacter G
    rw [hω.principal]
    exact hprincipal
  · intro i j hi hj
    change Section1.inducedCF W
        (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) =
      Section1.principalCharacter G - σ (ωFin i ⟨0, hppos⟩) -
        σ (ωFin ⟨0, hqpos⟩ j) + σ (ωFin i j)
    have hcf :
        Section2.CFOn W (Section3.cyclicTISet W1 W2 W)
          (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) :=
      Section3.alphaIJ_CFOn_cyclicTISet
        W1 W2 W (Fin q) (Fin p) ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin hω i j
    calc
      Section1.inducedCF W
          (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) =
          σ (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) :=
        (hind _ hcf).symm
      _ = σ (Section1.principalCharacter W) - σ (ωFin i ⟨0, hppos⟩) -
            σ (ωFin ⟨0, hqpos⟩ j) + σ (ωFin i j) := by
        simp [Section3.alphaIJ, map_sub, map_add]
      _ = Section1.principalCharacter G - σ (ωFin i ⟨0, hppos⟩) -
            σ (ωFin ⟨0, hqpos⟩ j) + σ (ωFin i j) := by
        rw [hprincipal]
  · intro i j
    rfl

public theorem section14PF39SourceData_of_pf35_compatibilityData
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Fin q → Fin p → Section1.ClassFunction G)
    (horth : Section3.IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ ⟨0, hqpos⟩ ⟨0, hppos⟩ = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ ⟨0, hqpos⟩ → j ≠ ⟨0, hppos⟩ →
      Section1.inducedCF W
          (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) =
        Section1.principalCharacter G - χ i ⟨0, hppos⟩ -
          χ ⟨0, hqpos⟩ j + χ i j)
    (hcompat : section14PF39CompatibilityData ωFin σ χ) :
    section14PF39SourceData hqpos hppos ωFin σ := by
  rcases hcompat with ⟨hσeq, hroot, hrat⟩
  exact ⟨χ, horth, hsigned, h00, hInd, hσeq, hroot, hrat⟩

public theorem section14_pf39_statement_from_pf35_data
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (hsource : section14PF39SourceData hqpos hppos ωFin σ) :
    Section3.proposition_3_9_statement W1 W2 W σ h31 hσ := by
  rcases hsource with
    ⟨χ, horth, hsigned, h00, hInd, hσeq, hroot, hrat⟩
  have hσ_eq : σ = Section3.sigmaOfPF35 ωFin χ :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hqpos⟩) (j0 := ⟨0, hppos⟩)
      (ω := ωFin) (χ := χ) h31 hω hσeq
  have hσ_pf35 :
      Section3.theorem_3_2_map_statement W1 W2 W
        (Section3.sigmaOfPF35 ωFin χ) := by
    simpa [← hσ_eq] using hσ
  have hrat_pf35 :
      ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
        Section1.IsIrreducibleCharacterOnGroup ω' →
          Section3.exactCharacterValueOrder ω' a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ r : ℚ, Section3.sigmaOfPF35 ωFin χ ω' g = (r : ℂ) := by
    intro ω' a hω' ha g hg
    rcases hrat hω' ha g hg with ⟨r, hr⟩
    exact ⟨r, by simpa [← hσ_eq] using hr⟩
  have h39_pf35 :
      Section3.proposition_3_9_statement W1 W2 W
        (Section3.sigmaOfPF35 ωFin χ) h31 hσ_pf35 :=
    Section3.proposition_3_9_of_rootAction_and_rationality_pf35
      W1 W2 W (Fin q) (Fin p) ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin χ
      h31 hω horth hsigned h00 hInd hroot hrat_pf35 hσ_pf35
  simpa [hσ_eq] using h39_pf35

public theorem section14_pf39_structured_b_from_pf35_data
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (χ : Fin q → Fin p → Section1.ClassFunction G)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin)
    (horth : Section3.IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ ⟨0, hqpos⟩ ⟨0, hppos⟩ = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ ⟨0, hqpos⟩ → j ≠ ⟨0, hppos⟩ →
      Section1.inducedCF W
          (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) =
        Section1.principalCharacter G - χ i ⟨0, hppos⟩ -
          χ ⟨0, hqpos⟩ j + χ i j)
    (hroot : ∀ {c b e : ℕ}, e.Coprime (c * b) →
      ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e) :
    Section3.proposition_3_9_statement_b_structured
      (Section3.sigmaOfPF35 ωFin χ) := by
  exact Section3.proposition_3_9_b_structured_of_rootAction_pf35
    W1 W2 W (Fin q) (Fin p) ⟨0, hqpos⟩ ⟨0, hppos⟩
    ωFin χ h31 hω horth hsigned h00 hInd hroot

public theorem section14_pf39_cyclotomic_model_of_mem_cyclotomicOrder
    {c b : ℕ} (hn : c * b ≠ 0) {η z : ℂ}
    (hη : IsPrimitiveRoot η (c * b))
    (hz : z ∈ Theory.Character.cyclotomicOrder η) :
    ∃ ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ,
    ∃ P : Polynomial ℤ,
    ∃ x : Section1.CyclotomicABField c b,
      z = ι x ∧
        x = Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
          (Section1.cyclotomicABRoot c b hn) P ∧
        ι (Section1.cyclotomicABRoot c b hn) = η := by
  letI : NeZero (c * b) := ⟨hn⟩
  let K := Section1.CyclotomicABField c b
  let ζ : K := Section1.cyclotomicABRoot c b hn
  have hζ : IsPrimitiveRoot ζ (c * b) := by
    dsimp [ζ, Section1.cyclotomicABRoot, K, Section1.CyclotomicABField]
    exact IsCyclotomicExtension.zeta_spec (c * b) ℚ (CyclotomicField (c * b) ℚ)
  have hirr : Irreducible (Polynomial.cyclotomic (c * b) ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos (c * b))
  let ηroot : primitiveRoots (c * b) ℂ := ⟨η, by
    rw [mem_primitiveRoots (NeZero.pos (c * b))]
    exact hη⟩
  let ι : K →ₐ[ℚ] ℂ := (hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm ηroot
  have hιζ : ι ζ = η := by
    change ((hζ.embeddingsEquivPrimitiveRoots ℂ hirr) ι : ℂ) = η
    simp [ι, ηroot]
  rcases Theory.Character.mem_cyclotomicOrder_iff_exists_intPolynomial_eval.mp hz with ⟨P, hP⟩
  let x : K := Polynomial.eval₂ (Int.castRingHom K) ζ P
  refine ⟨ι, P, x, ?_, ?_, ?_⟩
  · rw [← hP]
    change Polynomial.eval₂ (Int.castRingHom ℂ) η P = ι x
    rw [← hιζ]
    dsimp [x]
    exact (Polynomial.ringHom_eval₂_intCastRingHom P ι.toRingHom ζ).symm
  · rfl
  · exact hιζ

public theorem section14_pf39_complex_eval_of_cyclotomicAB_aut
    {c b : ℕ} (hn : c * b ≠ 0)
    (ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ)
    (P : Polynomial ℤ)
    (v : Gal((Section1.CyclotomicABField c b)/ℚ)) :
    ι (v (Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
      (Section1.cyclotomicABRoot c b hn) P)) =
      Polynomial.eval₂ (Int.castRingHom ℂ)
        (ι (v (Section1.cyclotomicABRoot c b hn))) P := by
  let K := Section1.CyclotomicABField c b
  let ζ : K := Section1.cyclotomicABRoot c b hn
  change ι (v (Polynomial.eval₂ (Int.castRingHom K) ζ P)) =
    Polynomial.eval₂ (Int.castRingHom ℂ) (ι (v ζ)) P
  have hvEval :
      v (Polynomial.eval₂ (Int.castRingHom K) ζ P) =
        Polynomial.eval₂ (Int.castRingHom K) (v ζ) P :=
    Polynomial.ringHom_eval₂_intCastRingHom P v.toRingEquiv.toRingHom ζ
  rw [hvEval]
  exact Polynomial.ringHom_eval₂_intCastRingHom P ι.toRingHom (v ζ)

public theorem section14_pf39_fixed_intPolynomial_of_complex_eval_fixed
    {c b : ℕ} (hn : c * b ≠ 0)
    (ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ)
    (P : Polynomial ℤ)
    (v : Gal((Section1.CyclotomicABField c b)/ℚ))
    (hfixed :
      Polynomial.eval₂ (Int.castRingHom ℂ)
        (ι (v (Section1.cyclotomicABRoot c b hn))) P =
      Polynomial.eval₂ (Int.castRingHom ℂ)
        (ι (Section1.cyclotomicABRoot c b hn)) P) :
    v (Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
        (Section1.cyclotomicABRoot c b hn) P) =
      Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
        (Section1.cyclotomicABRoot c b hn) P := by
  apply ι.injective
  change ι (v (Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
      (Section1.cyclotomicABRoot c b hn) P)) =
    ι (Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
      (Section1.cyclotomicABRoot c b hn) P)
  rw [section14_pf39_complex_eval_of_cyclotomicAB_aut hn ι P v]
  exact hfixed.trans
    (Polynomial.ringHom_eval₂_intCastRingHom P ι.toRingHom
      (Section1.cyclotomicABRoot c b hn)).symm

public theorem section14_pf39_complex_image_aut_root_eq_pow
    {c b : ℕ} (hn : c * b ≠ 0)
    (ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ)
    (v : Gal((Section1.CyclotomicABField c b)/ℚ)) :
    ∃ e : ℕ, e.Coprime (c * b) ∧
      ι (v (Section1.cyclotomicABRoot c b hn)) =
        ι (Section1.cyclotomicABRoot c b hn) ^ e := by
  letI : NeZero (c * b) := ⟨hn⟩
  let K := Section1.CyclotomicABField c b
  let ζ : K := Section1.cyclotomicABRoot c b hn
  let u : (ZMod (c * b))ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod (c * b) K v
  let e : ℕ := (u : ZMod (c * b)).val
  have hecop : e.Coprime (c * b) := by
    simpa [e] using ZMod.val_coe_unit_coprime u
  have hζ : IsPrimitiveRoot ζ (c * b) := by
    dsimp [ζ, Section1.cyclotomicABRoot, K, Section1.CyclotomicABField]
    exact IsCyclotomicExtension.zeta_spec (c * b) ℚ (CyclotomicField (c * b) ℚ)
  have hvζ : v ζ = ζ ^ e := by
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (c * b) K v hζ.pow_eq_one]
  refine ⟨e, hecop, ?_⟩
  rw [hvζ]
  exact map_pow ι ζ e

public theorem section14_pf39_fixed_cyclotomic_model_from_structured_b
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (χ : Fin q → Fin p → Section1.ClassFunction G)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin)
    (hsigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j))
    (hA :
      Section3.proposition_3_9_statement_a_galois
        (Section3.sigmaOfPF35 ωFin χ))
    (hstructured :
      Section3.proposition_3_9_statement_b_structured
        (Section3.sigmaOfPF35 ωFin χ))
    {ω' : Section1.ClassFunction W} {a : ℕ}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    (ha : Section3.exactCharacterValueOrder ω' a)
    (g : G) (hg : (orderOf g).Coprime a) :
    ∃ c b : ℕ,
    ∃ _ : c * b ≠ 0,
    ∃ ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ,
    ∃ x : Section1.CyclotomicABField c b,
      Section3.sigmaOfPF35 ωFin χ ω' g = ι x ∧
        (∀ v : Gal((Section1.CyclotomicABField c b)/ℚ), v x = x) := by
  have hk1 : IsCoprime (1 : ℤ) (a : ℤ) := by
    exact isCoprime_one_left
  rcases hstructured (ω' := ω') (a := a) (k := (1 : ℤ)) hω' ha hk1 with
    ⟨ωk, _hωk, hpow, c, b, _hcpart, hcard, _hcop, _v, _τ, _e,
      _hgal, _hτroot, _hecop, _hea, _heb, _hσ, _hargG, _hpoint⟩
  have hn : c * b ≠ 0 := Section1.nat_card_factor_ne_zero (G := G) hcard
  have hωk_eq : ωk = ω' := by
    ext x
    have hx := hpow x
    simpa using hx
  clear hpow hωk_eq
  let η : ℂ := Complex.exp (2 * Real.pi * Complex.I / (c * b))
  have hη : IsPrimitiveRoot η (c * b) :=
    by simpa [η] using Complex.isPrimitiveRoot_exp (c * b) hn
  have hcardF : Fintype.card G = c * b := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hηG : IsPrimitiveRoot η (Nat.card G) := by
    simpa [Nat.card_eq_fintype_card, hcardF] using hη
  have hz :
      Section3.sigmaOfPF35 ωFin χ ω' g ∈
        Theory.Character.cyclotomicOrder η := by
    exact Section3.proposition_3_9_c_value_mem_cyclotomicOrder_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hqpos⟩) (j0 := ⟨0, hppos⟩)
      (ω := ωFin) (χ := χ) hω hsigned hω' hηG g
  -- fixed, build the `ℚ_b` value model and prove it is fixed by extending
  -- each `ℚ_b` automorphism to `ℚ_{cb}` via PF `(1.9.a)`.
  refine ⟨c, b, hn, ?_⟩
  rcases section14_pf39_cyclotomic_model_of_mem_cyclotomicOrder hn hη hz with
    ⟨ι, P, x, hvalue, hx, hιζ⟩
  refine ⟨ι, x, hvalue, ?_⟩
  intro v
  rw [hx]
  refine section14_pf39_fixed_intPolynomial_of_complex_eval_fixed hn ι P v ?_
  rcases section14_pf39_complex_image_aut_root_eq_pow hn ι v with ⟨e, hecop, hvroot⟩
  rw [hvroot]
  rw [hιζ]
  obtain ⟨τ, hτroot⟩ := Section5.complex_galois_aut_pow_on_roots hecop
  have hecopG : e.Coprime (Nat.card G) := by
    simpa [Nat.card_eq_fintype_card, hcardF] using hecop
  have hτrootNat : ∀ z : ℂ, z ^ Nat.card G = 1 → τ z = z ^ e := by
    intro z hz
    exact hτroot z (by simpa [Nat.card_eq_fintype_card, hcardF] using hz)
  have hτcyc : Section3.cyclotomicGaloisAction (Nat.card G) τ :=
    ⟨e, hecopG, hτrootNat⟩
  have hec : e.Coprime c :=
    Nat.Coprime.of_dvd_right (Nat.dvd_mul_right c b) hecop
  have hea_nat : e.Coprime a :=
    Nat.Coprime.of_dvd_right _hcpart.1 hec
  have hk : IsCoprime (e : ℤ) (a : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hea_nat
  rcases hstructured (ω' := ω') (a := a) (k := (e : ℤ)) hω' ha hk with
    ⟨ωe, _hωe, hpowe, _ce, _be, _hcpart_e, _hcard_e, _hcop_e, _ve, _τe, _ee,
      _hgal_e, _hτroot_e, _hecop_e, _hea_e, _heb_e, _hσ_e, _harg_e, hpoint_e⟩
  have ha_dvd_card : a ∣ Nat.card G := by
    rw [hcard]
    exact dvd_mul_of_dvd_left _hcpart.1 b
  have hωroot_card : ∀ y : W, (ω' y) ^ Nat.card G = 1 := by
    intro y
    rcases ha_dvd_card with ⟨m, hm⟩
    rw [hm, pow_mul, ha.1.2 y, one_pow]
  have hconj_eq :
      Section3.classFunctionGaloisConjugate τ ω' = ωe := by
    ext y
    calc
      τ (ω' y) = (ω' y) ^ e := hτrootNat (ω' y) (hωroot_card y)
      _ = (ω' y) ^ (e : ℤ) := by simp
      _ = ωe y := (hpowe y).symm
  have hcomm :=
    hA (ω' := ω') τ hω' hτcyc
  have hτ_value :
      τ (Section3.sigmaOfPF35 ωFin χ ω' g) =
        Section3.sigmaOfPF35 ωFin χ ω' g := by
    calc
      τ (Section3.sigmaOfPF35 ωFin χ ω' g) =
          Section3.classFunctionGaloisConjugate τ
            (Section3.sigmaOfPF35 ωFin χ ω') g := rfl
      _ = Section3.sigmaOfPF35 ωFin χ
            (Section3.classFunctionGaloisConjugate τ ω') g := by
              rw [hcomm]
      _ = Section3.sigmaOfPF35 ωFin χ ωe g := by
              rw [hconj_eq]
      _ = Section3.sigmaOfPF35 ωFin χ ω' g := hpoint_e g hg
  have hvalue_eval :
      Section3.sigmaOfPF35 ωFin χ ω' g =
        Polynomial.eval₂ (Int.castRingHom ℂ) η P := by
    rw [hvalue, hx]
    rw [← hιζ]
    exact Polynomial.ringHom_eval₂_intCastRingHom P ι.toRingHom
      (Section1.cyclotomicABRoot c b hn)
  have hτ_eta : τ η = η ^ e := hτroot η hη.pow_eq_one
  have hτ_eval :
      τ (Polynomial.eval₂ (Int.castRingHom ℂ) η P) =
        Polynomial.eval₂ (Int.castRingHom ℂ) (η ^ e) P := by
    rw [← hτ_eta]
    exact Polynomial.ringHom_eval₂_intCastRingHom P τ.toRingEquiv.toRingHom η
  calc
    Polynomial.eval₂ (Int.castRingHom ℂ) (η ^ e) P =
        τ (Polynomial.eval₂ (Int.castRingHom ℂ) η P) := hτ_eval.symm
    _ = τ (Section3.sigmaOfPF35 ωFin χ ω' g) := by rw [hvalue_eval]
    _ = Section3.sigmaOfPF35 ωFin χ ω' g := hτ_value
    _ = Polynomial.eval₂ (Int.castRingHom ℂ) η P := hvalue_eval

public theorem section14_pf39_fixed_cyclotomic_model_source_bridge
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (χ : Fin q → Fin p → Section1.ClassFunction G)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin)
    (horth : Section3.IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ ⟨0, hqpos⟩ ⟨0, hppos⟩ = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ ⟨0, hqpos⟩ → j ≠ ⟨0, hppos⟩ →
      Section1.inducedCF W
          (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) =
        Section1.principalCharacter G - χ i ⟨0, hppos⟩ -
          χ ⟨0, hqpos⟩ j + χ i j)
    (hroot : ∀ {c b e : ℕ}, e.Coprime (c * b) →
      ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e)
    {ω' : Section1.ClassFunction W} {a : ℕ}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    (ha : Section3.exactCharacterValueOrder ω' a)
    (g : G) (hg : (orderOf g).Coprime a) :
    ∃ c b : ℕ,
    ∃ _ : c * b ≠ 0,
    ∃ ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ,
    ∃ x : Section1.CyclotomicABField c b,
      Section3.sigmaOfPF35 ωFin χ ω' g = ι x ∧
        (∀ v : Gal((Section1.CyclotomicABField c b)/ℚ), v x = x) := by
  have hstructured :
      Section3.proposition_3_9_statement_b_structured
        (Section3.sigmaOfPF35 ωFin χ) :=
    section14_pf39_structured_b_from_pf35_data
      hqpos hppos ωFin χ h31 hω horth hsigned h00 hInd hroot
  have hA :
      Section3.proposition_3_9_statement_a_galois
        (Section3.sigmaOfPF35 ωFin χ) :=
    Section3.proposition_3_9_a_galois_of_pf35
      W1 W2 W (Fin q) (Fin p) ⟨0, hqpos⟩ ⟨0, hppos⟩
      ωFin χ h31 hω horth hsigned h00 hInd
  exact section14_pf39_fixed_cyclotomic_model_from_structured_b
    hqpos hppos ωFin χ hω hsigned hA hstructured hω' ha g hg

public theorem section14_pf39_rationality_of_fixed_cyclotomic_model
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {p q c b : ℕ}
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (χ : Fin q → Fin p → Section1.ClassFunction G)
    {ω' : Section1.ClassFunction W} (g : G)
    (hn : c * b ≠ 0)
    (ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ)
    (x : Section1.CyclotomicABField c b)
    (hvalue : Section3.sigmaOfPF35 ωFin χ ω' g = ι x)
    (hfixed : ∀ v : Gal((Section1.CyclotomicABField c b)/ℚ), v x = x) :
    ∃ r : ℚ, Section3.sigmaOfPF35 ωFin χ ω' g = (r : ℂ) := by
  letI : NeZero (c * b) := ⟨hn⟩
  exact Section1.cyclotomicABField_complex_rat_of_fixed_gal ι x
    (Section3.sigmaOfPF35 ωFin χ ω' g) hvalue hfixed

public theorem section14_pf39_rationality_source_bridge
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ωFin : Fin q → Fin p → Section1.ClassFunction W)
    (χ : Fin q → Fin p → Section1.ClassFunction G)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin)
    (horth : Section3.IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ ⟨0, hqpos⟩ ⟨0, hppos⟩ = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ ⟨0, hqpos⟩ → j ≠ ⟨0, hppos⟩ →
      Section1.inducedCF W
          (Section3.alphaIJ W ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin i j) =
        Section1.principalCharacter G - χ i ⟨0, hppos⟩ -
          χ ⟨0, hqpos⟩ j + χ i j)
    (hσeq : ∀ i j, σ (ωFin i j) = χ i j)
    (hroot : ∀ {c b e : ℕ}, e.Coprime (c * b) →
      ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e) :
    ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
      Section1.IsIrreducibleCharacterOnGroup ω' →
        Section3.exactCharacterValueOrder ω' a →
          ∀ g : G, (orderOf g).Coprime a →
            ∃ r : ℚ, σ ω' g = (r : ℂ) := by
  intro ω' a hω' ha g hg
  have hσ_eq : σ = Section3.sigmaOfPF35 ωFin χ :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := ⟨0, hqpos⟩) (j0 := ⟨0, hppos⟩)
      (ω := ωFin) (χ := χ) h31 hω hσeq
  have hrat_pf35 :
      ∃ r : ℚ, Section3.sigmaOfPF35 ωFin χ ω' g = (r : ℂ) := by
    rcases section14_pf39_fixed_cyclotomic_model_source_bridge
        hqpos hppos ωFin χ h31 hω horth hsigned h00 hInd hroot
        hω' ha g hg with
      ⟨c, b, hn, ι, x, hvalue, hfixed⟩
    exact section14_pf39_rationality_of_fixed_cyclotomic_model
      ωFin χ g hn ι x hvalue hfixed
  rcases hrat_pf35 with ⟨r, hr⟩
  exact ⟨r, by simpa [hσ_eq] using hr⟩

public theorem section14_pf39_package_of_etaData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    (heta : section14EtaData Smax Tmax W W1 W2 p q η) :
    ∃ hqpos : 0 < q,
    ∃ hppos : 0 < p,
    ∃ ωFin : Fin q → Fin p → Section1.ClassFunction W,
    ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
    ∃ (h31 : Section3.hypothesis_3_1_statement W1 W2 W),
    ∃ _ : Section3.notation_3_3_statement W1 W2 W
      (Fin q) (Fin p) ⟨0, hqpos⟩ ⟨0, hppos⟩ ωFin,
    ∃ (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ),
      Section3.proposition_3_9_statement W1 W2 W σ h31 hσ ∧
        (∀ i j, ∃ a : ℕ,
          Section3.exactCharacterValueOrder (ωFin i j) a) ∧
          (∀ i j, η i j = σ (ωFin i j)) := by
  rcases section14_pf39_data_of_etaData heta with
    ⟨hqpos, hppos, ωFin, σ, h31, hω, hσ, hη⟩
  rcases section14_pf39_pf35_data_of_sigma
      hqpos hppos ωFin hω σ hσ with
    ⟨χ, horth, hsigned, h00, hInd, hσeq⟩
  have hroot : ∀ {c b e : ℕ}, e.Coprime (c * b) →
      ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e := by
    intro c b e he
    exact Section5.complex_galois_aut_pow_on_roots he
  have hrat : ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
      Section1.IsIrreducibleCharacterOnGroup ω' →
        Section3.exactCharacterValueOrder ω' a →
          ∀ g : G, (orderOf g).Coprime a →
            ∃ r : ℚ, σ ω' g = (r : ℂ) :=
    section14_pf39_rationality_source_bridge
      hqpos hppos ωFin χ σ h31 hω horth hsigned h00 hInd hσeq hroot
  have hcompat : section14PF39CompatibilityData ωFin σ χ := by
    exact ⟨hσeq, hroot, hrat⟩
  have hsource : section14PF39SourceData hqpos hppos ωFin σ :=
    section14PF39SourceData_of_pf35_compatibilityData
      hqpos hppos ωFin σ χ horth hsigned h00 hInd hcompat
  have h39 : Section3.proposition_3_9_statement W1 W2 W σ h31 hσ :=
    section14_pf39_statement_from_pf35_data
      hqpos hppos ωFin σ h31 hω hσ hsource
  have hexact :
      ∀ i j, ∃ a : ℕ, Section3.exactCharacterValueOrder (ωFin i j) a := by
    haveI : IsCyclic W := h31.2.2.2.1
    intro i j
    exact section14_exists_exactCharacterValueOrder_of_irreducible_cyclic
      (hω.irreducible i j)
  exact ⟨hqpos, hppos, ωFin, σ, h31, hω, hσ, h39, hexact, hη⟩

public theorem section14_eta_integer_values_of_pf39_package
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    (heta : section14EtaData Smax Tmax W W1 W2 p q η)
    {g : G} (hcopW : (orderOf g).Coprime (Nat.card W)) :
    ∃ value : Fin q × Fin p → ℤ,
      ∀ ij, η ij.1 ij.2 g = (value ij : ℂ) := by
  classical
  rcases section14_pf39_package_of_etaData heta with
    ⟨_hqpos, _hppos, ωFin, σ, h31, hω, _hσ, h39, hexact, hη⟩
  rcases h39 with ⟨_huniq, _h39a, _h39b, h39c⟩
  haveI : IsCyclic W := h31.2.2.2.1
  have hvalue : ∀ ij : Fin q × Fin p,
      ∃ n : ℤ, η ij.1 ij.2 g = (n : ℂ) := by
    intro ij
    rcases hexact ij.1 ij.2 with ⟨a, ha⟩
    have horderW : Section3.characterValueOrder (ωFin ij.1 ij.2) (Nat.card W) :=
      section14_characterValueOrder_natCard_of_irreducible_cyclic
        (hω.irreducible ij.1 ij.2)
    have hadvd : a ∣ Nat.card W := ha.2 (Nat.card W) horderW
    have hcopa : (orderOf g).Coprime a :=
      Nat.Coprime.coprime_dvd_right hadvd hcopW
    rcases h39c (hω.irreducible ij.1 ij.2) ha g hcopa with ⟨n, hn⟩
    exact ⟨n, by simpa [hη ij.1 ij.2] using hn⟩
  exact ⟨fun ij => Classical.choose (hvalue ij), fun ij =>
    Classical.choose_spec (hvalue ij)⟩

public theorem section14_normSq_ge_of_beta_zero_and_signed_expansion
    {G : Type u} [Group G]
    {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (β ψτ : Section1.ClassFunction G)
    (ε : Fin q → Fin p → ℤ)
    (g : G)
    (hβ : β g = 0)
    (hexp :
      β = (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) - ψτ ∨
        β = (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) +
          Section1.conjugateCharacter ψτ)
    (hsum :
      1 ≤ Complex.normSq
        ((∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) g)) :
    1 ≤ Complex.normSq (ψτ g) := by
  let s : Section1.ClassFunction G :=
    ∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)
  have hsval : 1 ≤ Complex.normSq (s g) := by
    simpa [s] using hsum
  rcases hexp with hminus | hplus
  · have hsg : s g = ψτ g := by
      have hg : (s - ψτ) g = 0 := by
        simpa [s, hminus] using hβ
      exact sub_eq_zero.mp (by simpa using hg)
    simpa [hsg] using hsval
  · have hcg : Section1.conjugateCharacter ψτ g = -s g := by
      have hg : (s + Section1.conjugateCharacter ψτ) g = 0 := by
        simpa [s, hplus] using hβ
      have hsum_zero : s g + Section1.conjugateCharacter ψτ g = 0 := by
        simpa using hg
      calc
        Section1.conjugateCharacter ψτ g =
            (s g + Section1.conjugateCharacter ψτ g) - s g := by ring
        _ = (0 : ℂ) - s g := by rw [hsum_zero]
        _ = -s g := by ring
    have hnormConj :
        Complex.normSq (Section1.conjugateCharacter ψτ g) =
          Complex.normSq (ψτ g) := by
      simp [Section1.conjugateCharacter]
    have hnorm : Complex.normSq (ψτ g) = Complex.normSq (s g) := by
      calc
        Complex.normSq (ψτ g) =
            Complex.normSq (Section1.conjugateCharacter ψτ g) := hnormConj.symm
        _ = Complex.normSq (-s g) := by rw [hcg]
        _ = Complex.normSq (s g) := by rw [Complex.normSq_neg]
    simpa [hnorm] using hsval

public theorem section14_not_mem_components_of_mem_G0
    {G : Type u} [Group G]
    {tildeAM : Set G}
    {W P Q : Subgroup G}
    {g : G}
    (hg : g ∈ theorem_14_11_3_G0 tildeAM W P Q) :
    g ∉ tildeAM ∧
      g ∉ conjugatesOfPuncturedSubgroup W ∧
      g ∉ conjugatesOfPuncturedSubgroup P ∧
      g ∉ conjugatesOfPuncturedSubgroup Q := by
  have h :
      ((g ∉ tildeAM ∧ g ∉ conjugatesOfPuncturedSubgroup W) ∧
          g ∉ conjugatesOfPuncturedSubgroup P) ∧
        g ∉ conjugatesOfPuncturedSubgroup Q := by
    simpa [theorem_14_11_3_G0, Set.mem_sdiff, Set.mem_union, not_or] using hg
  rcases h with ⟨⟨⟨hnotTilde, hnotW⟩, hnotP⟩, hnotQ⟩
  exact ⟨hnotTilde, hnotW, hnotP, hnotQ⟩


public theorem section14_eq_one_of_conj_mem_of_not_mem_conjugatesOfPuncturedSubgroup
    {G : Type u} [Group G]
    {H : Subgroup G}
    {g a : G}
    (hnot : g ∉ conjugatesOfPuncturedSubgroup H)
    (hgH : a * g * a⁻¹ ∈ H) :
    g = 1 := by
  by_contra hg1
  exact hnot ⟨a * g * a⁻¹, hgH, by
    intro hconj
    apply hg1
    have h := congrArg (fun z : G => a⁻¹ * z * a) hconj
    simpa [mul_assoc] using h, a⁻¹, by simp [mul_assoc]⟩

public theorem section14_one_le_intCast_mul_self_of_odd (n : ℤ)
    (hn : Odd n) :
    (1 : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
  have hn0 : n ≠ 0 := by
    intro hzero
    rw [hzero] at hn
    exact Int.not_odd_zero hn
  have hnatpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn0
  have hnat : 1 ≤ n.natAbs := Nat.succ_le_of_lt hnatpos
  have hsq_nat : (1 : ℕ) ≤ n.natAbs * n.natAbs := by
    nlinarith [hnat]
  have hsq_int_abs : (1 : ℤ) ≤ (n.natAbs * n.natAbs : ℕ) := by
    exact_mod_cast hsq_nat
  have hcast : ((n.natAbs * n.natAbs : ℕ) : ℤ) = n * n := by
    simp
  have hsq_int : (1 : ℤ) ≤ n * n := by
    simpa [hcast] using hsq_int_abs
  exact_mod_cast hsq_int

public theorem section14_normSq_ge_one_of_odd_integer_value {z : ℂ} {n : ℤ}
    (hz : z = (n : ℂ)) (hn : Odd n) :
    (1 : ℝ) ≤ Complex.normSq z := by
  rw [hz, Complex.normSq_intCast]
  exact section14_one_le_intCast_mul_self_of_odd n hn

public theorem section14_odd_integer_of_signed_one_plus_even_remainder
    {z : ℂ} {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1)
    (heven : ∃ m : ℤ, z - (eps : ℂ) = ((2 * m : ℤ) : ℂ)) :
    ∃ n : ℤ, Odd n ∧ z = (n : ℂ) := by
  rcases heven with ⟨m, hm⟩
  refine ⟨2 * m + eps, ?_, ?_⟩
  · rcases heps with rfl | rfl
    · refine ⟨m, ?_⟩
      ring
    · refine ⟨m - 1, ?_⟩
      ring
  · have hz : z = ((2 * m : ℤ) : ℂ) + (eps : ℂ) := by
      calc
        z = (z - (eps : ℂ)) + (eps : ℂ) := by ring
        _ = ((2 * m : ℤ) : ℂ) + (eps : ℂ) := by rw [hm]
    calc
      z = ((2 * m : ℤ) : ℂ) + (eps : ℂ) := hz
      _ = ((2 * m + eps : ℤ) : ℂ) := by norm_num

public theorem section14_even_signed_sum_of_fixedPointFree_pairing
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (pair : ι → ι)
    (n eps : ι → ℤ)
    (hpair_mem : ∀ i, i ∈ s → pair i ∈ s)
    (hpair_pair : ∀ i, i ∈ s → pair (pair i) = i)
    (hpair_ne : ∀ i, i ∈ s → pair i ≠ i)
    (hnpair : ∀ i, i ∈ s → n (pair i) = n i)
    (heps : ∀ i, i ∈ s → eps i = 1 ∨ eps i = -1) :
    ∃ m : ℤ, (∑ i ∈ s, eps i * n i) = 2 * m := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ s : Finset ι, s.card = k →
      (∀ i, i ∈ s → pair i ∈ s) →
      (∀ i, i ∈ s → pair (pair i) = i) →
      (∀ i, i ∈ s → pair i ≠ i) →
      (∀ i, i ∈ s → n (pair i) = n i) →
      (∀ i, i ∈ s → eps i = 1 ∨ eps i = -1) →
      ∃ m : ℤ, (∑ i ∈ s, eps i * n i) = 2 * m
  have hmain : ∀ k, P k := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih s hcard hmem hinv hne hn he
    by_cases hsempty : s = ∅
    · subst hsempty
      refine ⟨0, by simp⟩
    · rcases Finset.nonempty_iff_ne_empty.mpr hsempty with ⟨x, hx⟩
      let y := pair x
      have hy : y ∈ s := hmem x hx
      have hyx : y ≠ x := hne x hx
      let t : Finset ι := (s.erase x).erase y
      have hysx : y ∈ s.erase x := by
        simp [y, hy, hyx]
      have ht_card_lt : t.card < s.card := by
        have ht_sub : t ⊆ s.erase x := by
          intro z hz
          exact (Finset.mem_erase.mp hz).2
        exact lt_of_le_of_lt (Finset.card_le_card ht_sub) (Finset.card_erase_lt_of_mem hx)
      have hmem_t : ∀ i, i ∈ t → pair i ∈ t := by
        intro i hi
        have hi_s : i ∈ s := by
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
        have hpi_s : pair i ∈ s := hmem i hi_s
        have hpi_ne_x : pair i ≠ x := by
          intro hfix
          have hix : i = y := by
            calc
              i = pair (pair i) := (hinv i hi_s).symm
              _ = pair x := by rw [hfix]
              _ = y := rfl
          have hiy_not : i ≠ y := (Finset.mem_erase.mp hi).1
          exact hiy_not hix
        have hpi_ne_y : pair i ≠ y := by
          intro hfix
          have hpair_y : pair y = x := by
            simpa [y] using hinv x hx
          have hix : i = x := by
            calc
              i = pair (pair i) := (hinv i hi_s).symm
              _ = pair y := by rw [hfix]
              _ = x := hpair_y
          have hix_not : i ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
          exact hix_not hix
        simp [t, hpi_s, hpi_ne_x, hpi_ne_y]
      have hinv_t : ∀ i, i ∈ t → pair (pair i) = i := by
        intro i hi
        exact hinv i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
      have hne_t : ∀ i, i ∈ t → pair i ≠ i := by
        intro i hi
        exact hne i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
      have hn_t : ∀ i, i ∈ t → n (pair i) = n i := by
        intro i hi
        exact hn i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
      have he_t : ∀ i, i ∈ t → eps i = 1 ∨ eps i = -1 := by
        intro i hi
        exact he i ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
      rcases ih t.card (by simpa [hcard] using ht_card_lt) t rfl
          hmem_t hinv_t hne_t hn_t he_t with
        ⟨m, hm⟩
      have hsum_s :
          (∑ i ∈ s, eps i * n i) =
            eps x * n x + eps y * n y + ∑ i ∈ t, eps i * n i := by
        calc
          (∑ i ∈ s, eps i * n i) =
              ∑ i ∈ insert x (s.erase x), eps i * n i := by
            rw [Finset.insert_erase hx]
          _ = eps x * n x + ∑ i ∈ s.erase x, eps i * n i := by
            rw [Finset.sum_insert (show x ∉ s.erase x by simp)]
          _ = eps x * n x + (eps y * n y + ∑ i ∈ t, eps i * n i) := by
            rw [show (∑ i ∈ s.erase x, eps i * n i) =
                ∑ i ∈ insert y t, eps i * n i by
              rw [Finset.insert_erase hysx]]
            rw [Finset.sum_insert (show y ∉ t by simp [t])]
          _ = eps x * n x + eps y * n y + ∑ i ∈ t, eps i * n i := by
            ring
      have hny : n y = n x := hn x hx
      have hpair_term : ∃ mxy : ℤ, eps x * n x + eps y * n y = 2 * mxy := by
        rcases he x hx with hxeps | hxeps <;> rcases he y hy with hyeps | hyeps
        · refine ⟨n x, ?_⟩
          rw [hxeps, hyeps, hny]
          ring
        · refine ⟨0, ?_⟩
          rw [hxeps, hyeps, hny]
          ring
        · refine ⟨0, ?_⟩
          rw [hxeps, hyeps, hny]
          ring
        · refine ⟨-(n x), ?_⟩
          rw [hxeps, hyeps, hny]
          ring
      rcases hpair_term with ⟨mxy, hmxy⟩
      refine ⟨mxy + m, ?_⟩
      rw [hsum_s, hmxy, hm]
      ring
  exact hmain s.card s rfl hpair_mem hpair_pair hpair_ne hnpair heps

public def section14SignedEtaPairingData
    {G : Type u} [Group G] {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G) (g : G) : Prop :=
  ∃ hqpos : 0 < q,
  ∃ hppos : 0 < p,
  ∃ pair : Fin q × Fin p → Fin q × Fin p,
  ∃ value : Fin q × Fin p → ℤ,
    let base : Fin q × Fin p := (⟨0, hqpos⟩, ⟨0, hppos⟩)
    η base.1 base.2 g = 1 ∧
      (∀ ij, η ij.1 ij.2 g = (value ij : ℂ)) ∧
        (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
          pair ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p))) ∧
          (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
            pair (pair ij) = ij) ∧
            (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
              pair ij ≠ ij) ∧
              (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
                value (pair ij) = value ij)

public def section14ConjugateEtaPairingData
    {G : Type u} [Group G] {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G) (g : G) : Prop :=
  ∃ hqpos : 0 < q,
  ∃ hppos : 0 < p,
  ∃ pair : Fin q × Fin p → Fin q × Fin p,
  ∃ value : Fin q × Fin p → ℤ,
    let base : Fin q × Fin p := (⟨0, hqpos⟩, ⟨0, hppos⟩)
    η base.1 base.2 g = 1 ∧
      (∀ ij, η ij.1 ij.2 g = (value ij : ℂ)) ∧
        (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
          pair ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p))) ∧
          (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
            pair (pair ij) = ij) ∧
            (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
              pair ij ≠ ij) ∧
              (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
                η (pair ij).1 (pair ij).2 =
                  Section1.conjugateCharacter (η ij.1 ij.2))

public theorem section14SignedEtaPairingData_of_conjugateEtaPairingData
    {G : Type u} [Group G] {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G) (g : G)
    (hdata : section14ConjugateEtaPairingData η g) :
    section14SignedEtaPairingData η g := by
  rcases hdata with
    ⟨hqpos, hppos, pair, value, hbase, hvalue, hpair_mem, hpair_pair,
      hpair_ne, hconj_pair⟩
  refine ⟨hqpos, hppos, pair, value, hbase, hvalue, hpair_mem, hpair_pair,
    hpair_ne, ?_⟩
  intro ij hij
  have hconj_apply :
      η (pair ij).1 (pair ij).2 g = star (η ij.1 ij.2 g) := by
    simpa [Section1.conjugateCharacter] using congrFun (hconj_pair ij hij) g
  have hcomplex : (value (pair ij) : ℂ) = star (value ij : ℂ) := by
    rw [← hvalue (pair ij), ← hvalue ij]
    exact hconj_apply
  exact_mod_cast hcomplex

public theorem section14_fixed_irreducible_eq_principal_of_odd
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hodd : Odd (Nat.card G))
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hfixed : Section1.conjugateCharacter χ = χ) :
    χ = Section1.principalCharacter G := by
  classical
  rcases hχ with ⟨n, ρ, hirr, hχeq⟩
  have hfixedρ : ρ.character = Section1.conjugateCharacter ρ.character := by
    rw [← hχeq]
    exact hfixed.symm
  by_contra hne
  have hneρ : ρ.character ≠ Section1.principalCharacter G := by
    intro hρprin
    apply hne
    rw [hχeq, hρprin]
  exact (Section1.proposition_1_1 hodd ρ hirr hneρ) hfixedρ

public def section14OmegaConjugateIndexData
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G} {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ω : Fin q → Fin p → Section1.ClassFunction W) : Prop :=
  ∃ pair : Fin q × Fin p → Fin q × Fin p,
    let base : Fin q × Fin p := (⟨0, hqpos⟩, ⟨0, hppos⟩)
    (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
      pair ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p))) ∧
      (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
        pair (pair ij) = ij) ∧
        (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
          pair ij ≠ ij) ∧
          (∀ ij, Section1.conjugateCharacter (ω ij.1 ij.2) =
            ω (pair ij).1 (pair ij).2)

public theorem section14_omegaConjugateIndexData_of_notation
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G} {p q : ℕ}
    (hqpos : 0 < q) (hppos : 0 < p)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p)
      ⟨0, hqpos⟩ ⟨0, hppos⟩ ω) :
    section14OmegaConjugateIndexData hqpos hppos ω := by
  classical
  let base : Fin q × Fin p := (⟨0, hqpos⟩, ⟨0, hppos⟩)
  let pair : Fin q × Fin p → Fin q × Fin p := fun ij =>
    let h :=
      hω.all_irreducibles (Section1.conjugateCharacter (ω ij.1 ij.2))
        (Section1.isIrreducibleCharacterOnGroup_conjugateCharacter
          (hω.irreducible ij.1 ij.2))
    (Classical.choose h, Classical.choose (Classical.choose_spec h))
  have hpair_eq :
      ∀ ij, Section1.conjugateCharacter (ω ij.1 ij.2) =
        ω (pair ij).1 (pair ij).2 := by
    intro ij
    dsimp [pair]
    exact Classical.choose_spec
      (Classical.choose_spec
        (hω.all_irreducibles (Section1.conjugateCharacter (ω ij.1 ij.2))
          (Section1.isIrreducibleCharacterOnGroup_conjugateCharacter
            (hω.irreducible ij.1 ij.2))))
  have hbase_eq : ω base.1 base.2 = Section1.principalCharacter W := by
    simpa [base] using hω.principal
  have hodd : Odd (Nat.card W) := h31.2.2.2.2.1
  refine ⟨pair, ?_, ?_, ?_, hpair_eq⟩
  · intro ij hij
    have hij_ne_base : ij ≠ base := by
      simpa [base] using (Finset.mem_erase.mp hij).1
    have hpair_ne_base : pair ij ≠ base := by
      intro hpair_base
      have hconj_principal :
          Section1.conjugateCharacter (ω ij.1 ij.2) =
            Section1.principalCharacter W := by
        calc
          Section1.conjugateCharacter (ω ij.1 ij.2) =
              ω (pair ij).1 (pair ij).2 := hpair_eq ij
          _ = ω base.1 base.2 := by rw [hpair_base]
          _ = Section1.principalCharacter W := hbase_eq
      have hprincipal :
          ω ij.1 ij.2 = Section1.principalCharacter W := by
        calc
          ω ij.1 ij.2 =
              Section1.conjugateCharacter
                (Section1.conjugateCharacter (ω ij.1 ij.2)) := by
                exact (Section12.conjugateCharacter_involutive (ω ij.1 ij.2)).symm
          _ = Section1.conjugateCharacter (Section1.principalCharacter W) := by
                rw [hconj_principal]
          _ = Section1.principalCharacter W := Section12.conjugateCharacter_principalCharacter
      have hij_base : ij = base := by
        rcases hω.pairwise_eq (hprincipal.trans hbase_eq.symm) with ⟨hi, hj⟩
        exact Prod.ext hi hj
      exact hij_ne_base hij_base
    simpa [base] using hpair_ne_base
  · intro ij _hij
    have hdouble :
        ω (pair (pair ij)).1 (pair (pair ij)).2 = ω ij.1 ij.2 := by
      calc
        ω (pair (pair ij)).1 (pair (pair ij)).2 =
            Section1.conjugateCharacter (ω (pair ij).1 (pair ij).2) := by
              exact (hpair_eq (pair ij)).symm
        _ = Section1.conjugateCharacter
              (Section1.conjugateCharacter (ω ij.1 ij.2)) := by
              rw [hpair_eq ij]
        _ = ω ij.1 ij.2 := Section12.conjugateCharacter_involutive (ω ij.1 ij.2)
    rcases hω.pairwise_eq hdouble with ⟨hi, hj⟩
    exact Prod.ext hi hj
  · intro ij hij
    have hij_ne_base : ij ≠ base := by
      simpa [base] using (Finset.mem_erase.mp hij).1
    intro hpair_fixed
    have hfixed :
        Section1.conjugateCharacter (ω ij.1 ij.2) = ω ij.1 ij.2 := by
      simpa [hpair_fixed] using hpair_eq ij
    have hprincipal :
        ω ij.1 ij.2 = Section1.principalCharacter W :=
      section14_fixed_irreducible_eq_principal_of_odd
        hodd (hω.irreducible ij.1 ij.2) hfixed
    have hij_base : ij = base := by
      rcases hω.pairwise_eq (hprincipal.trans hbase_eq.symm) with ⟨hi, hj⟩
      exact Prod.ext hi hj
    exact hij_ne_base hij_base

public def section14EtaConjugateIndexData
    {G : Type u} [Group G] {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G) : Prop :=
  ∃ hqpos : 0 < q,
  ∃ hppos : 0 < p,
  ∃ pair : Fin q × Fin p → Fin q × Fin p,
    let base : Fin q × Fin p := (⟨0, hqpos⟩, ⟨0, hppos⟩)
    (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
      pair ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p))) ∧
      (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
        pair (pair ij) = ij) ∧
        (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
          pair ij ≠ ij) ∧
          (∀ ij, ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) →
            η (pair ij).1 (pair ij).2 =
              Section1.conjugateCharacter (η ij.1 ij.2))

public theorem section14_etaConjugateIndexData_of_etaData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    (heta : section14EtaData Smax Tmax W W1 W2 p q η) :
    section14EtaConjugateIndexData η := by
  classical
  rcases section14_pf39_package_of_etaData heta with
    ⟨hqpos, hppos, ωFin, σ, h31, hω, hσ, h39, _hexact, hη⟩
  rcases section14_pf39_pf35_data_of_sigma hqpos hppos ωFin hω σ hσ with
    ⟨χ, _horth, hsigned, _h00, _hInd, hσeq⟩
  rcases h39 with ⟨huniq, _h39a, _h39b, _h39c⟩
  rcases section14_omegaConjugateIndexData_of_notation
      hqpos hppos ωFin h31 hω with
    ⟨pair, hpair_mem, hpair_pair, hpair_ne, hωconj⟩
  refine ⟨hqpos, hppos, pair, hpair_mem, hpair_pair, hpair_ne, ?_⟩
  intro ij hij
  have hηsigned : Section3.IsSignedIrreducibleCharacter (η ij.1 ij.2) := by
    rw [hη ij.1 ij.2, hσeq ij.1 ij.2]
    exact hsigned ij.1 ij.2
  have hXsigned :
      Section3.IsSignedIrreducibleCharacter
        (Section1.conjugateCharacter (η ij.1 ij.2)) :=
    section14_signedIrreducible_conjugateCharacter hηsigned
  have hpair_irr :
      Section1.IsIrreducibleCharacterOnGroup
        (ωFin (pair ij).1 (pair ij).2) :=
    hω.irreducible (pair ij).1 (pair ij).2
  have hagree :
      ∀ x : G, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        Section1.conjugateCharacter (η ij.1 ij.2) x =
          ωFin (pair ij).1 (pair ij).2
            ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    calc
      Section1.conjugateCharacter (η ij.1 ij.2) x =
          star ((σ (ωFin ij.1 ij.2)) x) := by
            simp [Section1.conjugateCharacter, hη ij.1 ij.2]
      _ = star (ωFin ij.1 ij.2
            ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
            rw [hσ.2.2.2.2.2.1 (ωFin ij.1 ij.2)
              (hω.is_class ij.1 ij.2) x hx]
      _ = Section1.conjugateCharacter (ωFin ij.1 ij.2)
            ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
            rfl
      _ = ωFin (pair ij).1 (pair ij).2
            ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
            rw [hωconj ij]
  have hconj_sigma :
      Section1.conjugateCharacter (η ij.1 ij.2) =
        σ (ωFin (pair ij).1 (pair ij).2) :=
    huniq hpair_irr hXsigned hagree
  calc
    η (pair ij).1 (pair ij).2 =
        σ (ωFin (pair ij).1 (pair ij).2) := hη (pair ij).1 (pair ij).2
    _ = Section1.conjugateCharacter (η ij.1 ij.2) := hconj_sigma.symm

public theorem section14_eta_conjugate_entry_of_etaData
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    (heta : section14EtaData Smax Tmax W W1 W2 p q η)
    (i : Fin q) (j : Fin p) :
    ∃ i' : Fin q, ∃ j' : Fin p,
      η i' j' = Section1.conjugateCharacter (η i j) := by
  classical
  rcases section14_etaConjugateIndexData_of_etaData heta with
    ⟨hqpos, hppos, pair, _hpair_mem, _hpair_pair, _hpair_ne, hconj_pair⟩
  let base : Fin q × Fin p := (⟨0, hqpos⟩, ⟨0, hppos⟩)
  by_cases hij : (i, j) ∈ (Finset.univ.erase base : Finset (Fin q × Fin p))
  · exact ⟨(pair (i, j)).1, (pair (i, j)).2, hconj_pair (i, j) hij⟩
  · have hij_base : (i, j) = base := by
      by_contra hne
      apply hij
      simp [base, hne]
    have hi : (i : ℕ) = 0 := by
      simpa [base] using congrArg (fun ij : Fin q × Fin p => (ij.1 : ℕ)) hij_base
    have hj : (j : ℕ) = 0 := by
      simpa [base] using congrArg (fun ij : Fin q × Fin p => (ij.2 : ℕ)) hij_base
    have hηprincipal : η i j = Section1.principalCharacter G := by
      ext g
      simpa [Section1.principalCharacter] using
        section14_eta_zero_zero_apply (Smax := Smax) (Tmax := Tmax)
          (W := W) (W1 := W1) (W2 := W2) (heta := heta) hi hj g
    refine ⟨i, j, ?_⟩
    rw [hηprincipal]
    exact Section12.conjugateCharacter_principalCharacter.symm

public theorem section14ConjugateEtaPairingData_of_indexData
    {G : Type u} [Group G] [Finite G] {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G) (g : G)
    (heta : section14EtaData Smax Tmax W W1 W2 p q η)
    (hindex : section14EtaConjugateIndexData η)
    (value : Fin q × Fin p → ℤ)
    (hvalue : ∀ ij, η ij.1 ij.2 g = (value ij : ℂ)) :
    section14ConjugateEtaPairingData η g := by
  rcases hindex with
    ⟨hqpos, hppos, pair, hpair_mem, hpair_pair, hpair_ne, hconj_pair⟩
  refine ⟨hqpos, hppos, pair, value, ?_, hvalue, hpair_mem, hpair_pair,
    hpair_ne, hconj_pair⟩
  exact section14_eta_zero_zero_apply heta rfl rfl g

public theorem section14_signed_eta_even_remainder_of_pairingData
    {G : Type u} [Group G] {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ε : Fin q → Fin p → ℤ) (g : G)
    (hε : ∀ i j, ε i j = 1 ∨ ε i j = -1)
    (hpairData : section14SignedEtaPairingData η g) :
    ∃ eps0 : ℤ, (eps0 = 1 ∨ eps0 = -1) ∧
      ∃ m : ℤ,
        ((∑ i : Fin q, ∑ j : Fin p,
          ((ε i j : ℂ) • η i j)) g) - (eps0 : ℂ) = ((2 * m : ℤ) : ℂ) := by
  classical
  rcases hpairData with
    ⟨hqpos, hppos, pair, value, hbase, hvalue, hpair_mem, hpair_pair,
      hpair_ne, hvalue_pair⟩
  let base : Fin q × Fin p := (⟨0, hqpos⟩, ⟨0, hppos⟩)
  let s : Finset (Fin q × Fin p) := Finset.univ.erase base
  let epsPair : Fin q × Fin p → ℤ := fun ij => ε ij.1 ij.2
  have hepsPair : ∀ ij, ij ∈ s → epsPair ij = 1 ∨ epsPair ij = -1 := by
    intro ij _
    exact hε ij.1 ij.2
  have hpair_mem_s : ∀ ij, ij ∈ s → pair ij ∈ s := by
    intro ij hij
    change pair ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p))
    change ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) at hij
    exact hpair_mem ij hij
  have hpair_pair_s : ∀ ij, ij ∈ s → pair (pair ij) = ij := by
    intro ij hij
    change ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) at hij
    exact hpair_pair ij hij
  have hpair_ne_s : ∀ ij, ij ∈ s → pair ij ≠ ij := by
    intro ij hij
    change ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) at hij
    exact hpair_ne ij hij
  have hvalue_pair_s : ∀ ij, ij ∈ s → value (pair ij) = value ij := by
    intro ij hij
    change ij ∈ (Finset.univ.erase base : Finset (Fin q × Fin p)) at hij
    exact hvalue_pair ij hij
  rcases section14_even_signed_sum_of_fixedPointFree_pairing
      s pair value epsPair
      hpair_mem_s
      hpair_pair_s
      hpair_ne_s
      hvalue_pair_s
      hepsPair with
    ⟨m, hm⟩
  refine ⟨ε base.1 base.2, hε base.1 base.2, m, ?_⟩
  have hdouble :
      ((∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) g) =
        ∑ ij : Fin q × Fin p, ((ε ij.1 ij.2 * value ij : ℤ) : ℂ) := by
    calc
      ((∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) g) =
          ∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * η i j g := by
        simp
      _ = ∑ i : Fin q, ∑ j : Fin p, (ε i j : ℂ) * (value (i, j) : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        refine Finset.sum_congr rfl ?_
        intro j _hj
        rw [hvalue (i, j)]
      _ = ∑ ij : Fin q × Fin p, (ε ij.1 ij.2 : ℂ) * (value ij : ℂ) := by
        simpa using
          (Finset.sum_product'
            (s := (Finset.univ : Finset (Fin q)))
            (t := (Finset.univ : Finset (Fin p)))
            (f := fun i j => (ε i j : ℂ) * (value (i, j) : ℂ))).symm
      _ = ∑ ij : Fin q × Fin p, ((ε ij.1 ij.2 * value ij : ℤ) : ℂ) := by
        simp [Int.cast_mul]
  have hsplit :
      (∑ ij : Fin q × Fin p, ((ε ij.1 ij.2 * value ij : ℤ) : ℂ)) =
        (ε base.1 base.2 : ℂ) +
          (∑ ij ∈ s, ((epsPair ij * value ij : ℤ) : ℂ)) := by
    calc
      (∑ ij : Fin q × Fin p, ((ε ij.1 ij.2 * value ij : ℤ) : ℂ)) =
          ((ε base.1 base.2 * value base : ℤ) : ℂ) +
            ∑ ij ∈ s, ((ε ij.1 ij.2 * value ij : ℤ) : ℂ) := by
        rw [show (Finset.univ : Finset (Fin q × Fin p)) = insert base s by
          simp [s]]
        simp [s]
      _ = (ε base.1 base.2 : ℂ) +
            ∑ ij ∈ s, ((epsPair ij * value ij : ℤ) : ℂ) := by
        have hvbase : (value base : ℂ) = 1 := by
          rw [← hvalue base]
          exact hbase
        have hbaseTerm :
            ((ε base.1 base.2 * value base : ℤ) : ℂ) =
              (ε base.1 base.2 : ℂ) := by
          rw [Int.cast_mul, hvbase, mul_one]
        simp [epsPair, hbaseTerm]
  have hsum_even_complex :
      (∑ ij ∈ s, ((epsPair ij * value ij : ℤ) : ℂ)) = ((2 * m : ℤ) : ℂ) := by
    have hcast :
        (∑ ij ∈ s, ((epsPair ij * value ij : ℤ) : ℂ)) =
          ((∑ ij ∈ s, epsPair ij * value ij : ℤ) : ℂ) := by
      norm_num
    rw [hcast, hm]
  rw [hdouble, hsplit, hsum_even_complex]
  ring

public theorem section14_betaM_tau_eq_zero_of_not_mem_dadeSupport
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G}
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {βM : Section1.ClassFunction M}
    {βMτ : Section1.ClassFunction G}
    {R : G → Subgroup G}
    (hDade : Section12.dadeIsometryRelativeToTypeIASet M K R τM)
    (hβCFOn : Section2.CFOn M (Section12.typeIASet M K) βM)
    (hβMτ : βMτ = τM βM)
    {g : G}
    (hnotSupport : g ∉ Section2.dadeSupport (Section12.typeIASet M K) R) :
    βMτ g = 0 := by
  rcases hDade with ⟨_h22, hτM⟩
  rcases hτM with ⟨hAMG, hτM⟩
  rw [hβMτ, hτM βM hβCFOn]
  exact Section2.dadeTransform_eq_zero_of_not_mem_support
    R hAMG βM hnotSupport


public theorem section14_typeI_notation_8_10_A_eq_typeIASet
    {G : Type u} [Group G] [Finite G]
    {M K Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hTypeI : Section8.typeIDefinitionData M K)
    (h810 : Section8.notation_8_10_source_data M K Ms A A0 A1) :
    A = Section12.typeIASet M K := by
  rcases h810 with ⟨_hMmax, _hMF, hMs, _hA1, hcases⟩
  rcases hcases with hI | hP
  · rcases hI with ⟨_hTypeI', hA, _hA0⟩
    exact hA.trans (Section12.typeIASet_eq_section8CentralizerUnion M K).symm
  · exfalso
    rcases hP with ⟨_U, _W1, _W2, _hP, htypeP, _hA, _hA0, _hLate⟩
    rcases hMs with hMsI | hMsII | hMsIII | hMsIV | hMsV
    · rcases hMsI with ⟨_hI, hnotII, hnotIII, hnotIV, hnotV, _hMs⟩
      rcases htypeP with hII | hIII | hIV | hV
      · exact hnotII hII
      · exact hnotIII hIII
      · exact hnotIV hIV
      · exact hnotV hV
    · exact hMsII.1 hTypeI
    · exact hMsIII.1 hTypeI
    · exact hMsIV.1 hTypeI
    · exact hMsV.1 hTypeI

public theorem section14_typeI_notation_8_10_A0_eq_typeIASet
    {G : Type u} [Group G] [Finite G]
    {M K Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hTypeI : Section8.typeIDefinitionData M K)
    (h810 : Section8.notation_8_10_source_data M K Ms A A0 A1) :
    A0 = Section12.typeIASet M K := by
  rcases h810 with ⟨_hMmax, _hMF, hMs, _hA1, hcases⟩
  rcases hcases with hI | hP
  · rcases hI with ⟨_hTypeI', hA, hA0⟩
    exact hA0.trans (hA.trans (Section12.typeIASet_eq_section8CentralizerUnion M K).symm)
  · exfalso
    rcases hP with ⟨_U, _W1, _W2, _hP, htypeP, _hA, _hA0, _hLate⟩
    rcases hMs with hMsI | hMsII | hMsIII | hMsIV | hMsV
    · rcases hMsI with ⟨_hI, hnotII, hnotIII, hnotIV, hnotV, _hMs⟩
      rcases htypeP with hII | hIII | hIV | hV
      · exact hnotII hII
      · exact hnotIII hIII
      · exact hnotIV hIV
      · exact hnotV hV
    · exact hMsII.1 hTypeI
    · exact hMsIII.1 hTypeI
    · exact hMsIV.1 hTypeI
    · exact hMsV.1 hTypeI

public theorem section14_typeI_dadeSubgroup_eq_on_typeIASet_of_notation_8_14
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K Ms Ms' : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Set G)
    (B B0 B1 E tildeB tildeB0 tildeB1 : Set G)
    (R R' : G → Subgroup G)
    (hTypeI : Section8.typeIDefinitionData M K)
    (h810 : Section8.notation_8_10_source_data M K Ms A A0 A1)
    (h814 : Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R)
    (h810' : Section8.notation_8_10_source_data M K Ms' B B0 B1)
    (h814' : Section8.notation_8_14_source_data M B B0 B1 E tildeB tildeB0 tildeB1 R')
    {a : G} (ha : a ∈ Section12.typeIASet M K) :
    R a = R' a := by
  classical
  have hA0 : A0 = Section12.typeIASet M K :=
    section14_typeI_notation_8_10_A0_eq_typeIASet hTypeI h810
  have hB0 : B0 = Section12.typeIASet M K :=
    section14_typeI_notation_8_10_A0_eq_typeIASet hTypeI h810'
  rcases h814 with
    ⟨_hA1A, _hAA0, hD, hRbot, hUnique, hReq,
      _htildeA, _htildeA0, _htildeA1⟩
  rcases h814' with
    ⟨_hB1B, _hBB0, hE, hRbot', _hUnique', hReq',
      _htildeB, _htildeB0, _htildeB1⟩
  by_cases haD : a ∈ Section8.section8DSet M (Section12.typeIASet M K)
  · have haD' : a ∈ D := by
      simpa [hD, hA0] using haD
    have haE : a ∈ E := by
      simpa [hE, hB0] using haD
    rcases hUnique a haD' with ⟨L, hLmem, huniq⟩
    rcases section16_exists_mfSubgroup (G := G) L with ⟨LF, hLF⟩
    have hSet :
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)) = {L} := by
      ext N
      constructor
      · intro hN
        simpa using (huniq N hN)
      · intro hN
        have hNL : N = L := by
          simpa using hN
        simpa [hNL] using hLmem
    have hR : R a = elementCentralizerIn LF a :=
      hReq a haD' L LF hSet hLF
    have hR' : R' a = elementCentralizerIn LF a :=
      hReq' a haE L LF hSet hLF
    exact hR.trans hR'.symm
  · have haNotD : a ∈ A0 \ D := by
      refine ⟨?_, ?_⟩
      · simpa [hA0] using ha
      · intro haD'
        exact haD (by simpa [hD, hA0] using haD')
    have haNotE : a ∈ B0 \ E := by
      refine ⟨?_, ?_⟩
      · simpa [hB0] using ha
      · intro haE
        exact haD (by simpa [hE, hB0] using haE)
    exact (hRbot a haNotD).trans (hRbot' a haNotE).symm

public theorem section14_typeI_dadeSupport_eq_of_notation_8_14
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K Ms Ms' : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Set G)
    (B B0 B1 E tildeB tildeB0 tildeB1 : Set G)
    (R R' : G → Subgroup G)
    (hTypeI : Section8.typeIDefinitionData M K)
    (h810 : Section8.notation_8_10_source_data M K Ms A A0 A1)
    (h814 : Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R)
    (h810' : Section8.notation_8_10_source_data M K Ms' B B0 B1)
    (h814' : Section8.notation_8_14_source_data M B B0 B1 E tildeB tildeB0 tildeB1 R') :
    Section2.dadeSupport (Section12.typeIASet M K) R =
      Section2.dadeSupport (Section12.typeIASet M K) R' := by
  ext g
  constructor
  · rintro ⟨a, ha, h, hh, hconj⟩
    refine ⟨a, ha, h, ?_, hconj⟩
    have hReq :=
      section14_typeI_dadeSubgroup_eq_on_typeIASet_of_notation_8_14
        M K Ms Ms' A A0 A1 D tildeA tildeA0 tildeA1
        B B0 B1 E tildeB tildeB0 tildeB1 R R' hTypeI h810 h814 h810' h814' ha
    simpa [hReq] using hh
  · rintro ⟨a, ha, h, hh, hconj⟩
    refine ⟨a, ha, h, ?_, hconj⟩
    have hReq :=
      section14_typeI_dadeSubgroup_eq_on_typeIASet_of_notation_8_14
        M K Ms Ms' A A0 A1 D tildeA tildeA0 tildeA1
        B B0 B1 E tildeB tildeB0 tildeB1 R R' hTypeI h810 h814 h810' h814' ha
    simpa [hReq] using hh

public theorem section14_typeI_dadeSupport_eq_tildeA_of_notation_8_14
    {G : Type u} [Group G] [Finite G]
    (M K Ms : Subgroup G)
    (A A0 A1 D tildeAM tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G)
    (hTypeI : Section8.typeIDefinitionData M K)
    (h810 : Section8.notation_8_10_source_data M K Ms A A0 A1)
    (h814 : Section8.notation_8_14_source_data M A A0 A1 D tildeAM tildeA0 tildeA1 R) :
    Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM := by
  have hA : A = Section12.typeIASet M K :=
    section14_typeI_notation_8_10_A_eq_typeIASet hTypeI h810
  have hsupp :
      Section2.dadeSupport A R = tildeAM :=
    Section12.dadeSupport_eq_tildeA_of_notation_8_14_source_data
      M A A0 A1 D tildeAM tildeA0 tildeA1 R h814
  rwa [← hA] 

public theorem section14_theorem_14_11_3_dade_support_tildeA_witness_source_bridge
    {G : Type u} [Group G] [Finite G]
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
    (htilde : Section10.section10TildeAData M K tildeAM) :
    ∃ R : G → Subgroup G,
      Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
    Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM := by
  rcases h1410 with
    ⟨_hMmax, _hModd, _hVnorm, _hMF, hTypeI, hDade, _hMfam, _h52b, _hExt,
      _hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases hDade with ⟨R, hDadeR, hDadeSupport, _hDadeNotation⟩
  rcases htilde with ⟨Ms, A, A0, A1, D, tildeA0, tildeA1, R0, h810, h814⟩
  refine ⟨R, hDadeR, ?_⟩
  have hsupp0 :
      Section2.dadeSupport (Section12.typeIASet M K) R0 = tildeAM :=
    section14_typeI_dadeSupport_eq_tildeA_of_notation_8_14
      M K Ms A A0 A1 D tildeAM tildeA0 tildeA1 R0 hTypeI h810 h814
  -- `Dade_support ddMK = 'A~(M)` by `FTsupp_Frobenius` and
  -- `FT_DadeF_supportE`. The remaining source choice is that `(14.10)` and
  -- `section10TildeAData` use the same Type-I Dade support.
  exact hDadeSupport tildeAM
    ⟨Ms, A, A0, A1, D, tildeA0, tildeA1, R0, h810, h814⟩

public theorem section14_theorem_14_11_3_dade_support_nonmem_source_bridge
    {G : Type u} [Group G] [Finite G]
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
    (htilde : Section10.section10TildeAData M K tildeAM)
    {g : G} (hnotTilde : g ∉ tildeAM) :
    ∃ R : G → Subgroup G,
      Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
        g ∉ Section2.dadeSupport (Section12.typeIASet M K) R := by
  rcases section14_theorem_14_11_3_dade_support_tildeA_witness_source_bridge
      M K V Mfam τM τM₁ ψ βM tildeAM h1410 htilde with
    ⟨R, hDade, hsupp⟩
  refine ⟨R, hDade, ?_⟩
  intro hg
  exact hnotTilde (by simpa [hsupp] using hg)

public theorem section14_natCard_eq_mul_of_section12InternalDirectProduct
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W) :
    Nat.card W = Nat.card W1 * Nat.card W2 := by
  classical
  rcases hprod with ⟨_hW1le, _hW2le, hW, hdisj, hcent⟩
  have hW1norm : W1 ≤ Subgroup.normalizer (W2 : Set G) :=
    hcent.trans (centralizer_le_normalizer W2)
  have hinf : W2 ⊓ W1 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact Subgroup.disjoint_def.mp hdisj hx.2 hx.1
  have hcard :
      Nat.card (W2 ⊔ W1 : Subgroup G) = Nat.card W2 * Nat.card W1 :=
    appendixC_sup_natCard_eq_mul_of_inf_eq_bot_of_le_normalizer hW1norm hinf
  have hcard' :
      Nat.card (W1 ⊔ W2 : Subgroup G) = Nat.card W1 * Nat.card W2 := by
    simpa [sup_comm, mul_comm] using hcard
  simpa [hW] using hcard'

public theorem section14_order_coprime_card_W_of_pq_source
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    {g : G}
    (hcopP : (orderOf g).Coprime p)
    (hcopQ : (orderOf g).Coprime q) :
    (orderOf g).Coprime (Nat.card W) := by
  rcases hctx with ⟨hsource, _hqp⟩
  rcases hsource with
    ⟨hcase, _hSTypeP, _hTTypeP, hp, hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hchoice, _hmin⟩
  rcases hcase with
    ⟨hprod, _hWcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  have hcardW : Nat.card W = Nat.card W1 * Nat.card W2 :=
    section14_natCard_eq_mul_of_section12InternalDirectProduct hprod
  have hcopW1 : (orderOf g).Coprime (Nat.card W1) := by
    simpa [hq] using hcopQ
  have hcopW2 : (orderOf g).Coprime (Nat.card W2) := by
    simpa [hp] using hcopP
  rw [hcardW, Nat.coprime_mul_iff_right]
  exact ⟨hcopW1, hcopW2⟩

public theorem section14_typeP_MF_natCard_eq_prime_pow_of_case_9_7_b_source
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u) :
    Nat.card MF = p ^ q := by
  classical
  have hcase' : Section9.case_9_7_b_data M MF U W1 W2 ⊥ C p q u := by
    simpa [Section13.case_9_7_b_sourceDataForSection13] using hcase
  rcases Section9.case_9_7_b_quotient_card_sec9 hcase' with
    ⟨hnormal, hcardQuot⟩
  let H0sub : Subgroup MF := (⊥ : Subgroup G).subgroupOf MF
  haveI : H0sub.Normal := by
    simp [H0sub]
  have hH0sub_bot : H0sub = ⊥ := by
    dsimp [H0sub]
    exact section14_subgroupOf_eq_bot_of_eq_bot
      (C := (⊥ : Subgroup G)) (U := MF) rfl
  let e : MF ⧸ H0sub ≃* MF :=
    (QuotientGroup.quotientMulEquivOfEq hH0sub_bot).trans
      (QuotientGroup.quotientBot (G := MF))
  have hcardConj : Nat.card (MF ⧸ H0sub) = Nat.card MF :=
    Nat.card_congr e.toEquiv
  have hcardQuot' : Nat.card (MF ⧸ H0sub) = p ^ q := by
    simpa [H0sub] using hcardQuot
  exact hcardConj.symm.trans hcardQuot'

public theorem section14_typeP_MF_isPGroup_of_case_9_7_b_source
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u) :
    IsPGroup p MF := by
  exact IsPGroup.of_card (G := MF) (p := p) (n := q)
    (section14_typeP_MF_natCard_eq_prime_pow_of_case_9_7_b_source hcase)

public theorem section14_typeP_MF_sylow_of_case_9_7_b_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u) :
    ∃ P : Sylow p G, (P : Subgroup G) = MF := by
  classical
  have hcase' : Section9.case_9_7_b_data M MF U W1 W2 ⊥ C p q u := by
    simpa [Section13.case_9_7_b_sourceDataForSection13] using hcase
  have hp : Nat.Prime p := Section9.case_9_7_b_p_prime_sec9 hcase'
  have hq : Nat.Prime q := Section9.case_9_7_b_q_prime_sec9 hcase'
  have h92 : Section9.hypothesis_9_2_statement M MF U W1 W2 q :=
    Section9.case_9_7_b_hypothesis_9_2_sec9 hcase'
  have h92W1 : Section9.hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) :=
    Section9.hypothesis_9_2_with_card_W1_sec9 h92
  rcases Section9.msChoice_of_hypothesis_9_2_sec9 M MF U W1 W2 h92W1 with
    ⟨Ms, hMs⟩
  have hMFHall : IsHallSubgroup (subgroupPrimeSet MF) MF :=
    (Section8.theorem_8_11_of_msChoice (G := G) h92.maximal h92.mf hMs).2.1
  have hp_dvd_card : p ∣ Nat.card MF := by
    rw [section14_typeP_MF_natCard_eq_prime_pow_of_case_9_7_b_source hcase]
    exact dvd_pow_self p hq.ne_zero
  have hp_mem : (⟨p, hp⟩ : Nat.Primes) ∈ subgroupPrimeSet MF :=
    hMFHall.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hp_dvd_card
  have hnot_index : ¬ p ∣ MF.index := by
    intro hpidx
    exact (hMFHall.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpidx) hp_mem
  have hMFp : IsPGroup p MF :=
    section14_typeP_MF_isPGroup_of_case_9_7_b_source hcase
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := IsPGroup.toSylow (p := p) hMFp hnot_index
  exact ⟨P, by simp [P, IsPGroup.toSylow_coe]⟩

public theorem section14_exists_conj_prime_order_mem_sylow_centralized_of_not_coprime_order
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p)
    (P : Sylow p G)
    {g : G}
    (hnot : ¬ (orderOf g).Coprime p) :
    ∃ y a : G,
      a ∈ (P : Subgroup G) ∧ a ≠ 1 ∧
        y * g * y⁻¹ ∈ elementCentralizerIn ⊤ a := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hnot' : ¬ p.Coprime (orderOf g) := by
    intro h
    exact hnot (by simpa [Nat.Coprime, Nat.gcd_comm] using h)
  have hpdvd_order : p ∣ orderOf g := hp.dvd_iff_not_coprime.mpr hnot'
  have hpdvd_zpowers : p ∣ Nat.card (Subgroup.zpowers g) := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_zpowers] using hpdvd_order
  rcases exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers g) p hpdvd_zpowers with
    ⟨x, hxorder⟩
  let X : Subgroup G := Subgroup.zpowers (x : G)
  have hxPgroup : IsPGroup p X := by
    refine IsPGroup.of_card (G := X) (p := p) (n := 1) ?_
    have hcard : Nat.card X = p := by
      simpa [X, Nat.card_eq_fintype_card, Fintype.card_zpowers,
        Subgroup.orderOf_coe] using hxorder
    simpa [pow_one] using hcard
  rcases IsPGroup.exists_le_sylow (G := G) (p := p) hxPgroup with ⟨Q, hXQ⟩
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G Q P
  have hxQ : (x : G) ∈ (Q : Subgroup G) :=
    hXQ (Subgroup.mem_zpowers (x : G))
  let a : G := y * (x : G) * y⁻¹
  have haP : a ∈ (P : Subgroup G) := by
    have hxSmul : a ∈ ((y • Q : Sylow p G) : Subgroup G) := by
      change a ∈ MulAut.conj y • (Q : Set G)
      exact ⟨(x : G), hxQ, by simp [a, MulAut.conj_apply, mul_assoc]⟩
    simpa [hy] using hxSmul
  have hxne : (x : G) ≠ 1 := by
    intro hx1
    have horder_one : orderOf x = 1 :=
      orderOf_eq_one_iff.mpr (Subtype.ext hx1)
    have hp1 : p = 1 := hxorder.symm.trans horder_one
    exact hp.ne_one hp1
  have hane : a ≠ 1 := by
    intro ha1
    apply hxne
    have h := congrArg (fun z : G => y⁻¹ * z * y) ha1
    simpa [a, mul_assoc] using h
  have hx_zpowers : (x : G) ∈ Subgroup.zpowers g := x.2
  rcases Subgroup.mem_zpowers_iff.mp hx_zpowers with ⟨n, hn⟩
  have hcomm_xg : Commute (x : G) g := by
    simp [← hn]
  refine ⟨y, a, haP, hane, ?_⟩
  have hcomm : Commute (y * g * y⁻¹) a := by
    dsimp [a]
    simpa [mul_assoc] using hcomm_xg.symm.conj y
  exact ⟨by simp, by simpa [Subgroup.mem_centralizer_singleton_iff] using hcomm.eq⟩

public theorem section14_exists_conj_typeP_MF_element_centralized_of_not_coprime_order
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u)
    (hMFsylow : ∃ P : Sylow p G, (P : Subgroup G) = MF)
    {g : G}
    (hnot : ¬ (orderOf g).Coprime p) :
    ∃ y a : G,
      a ∈ MF ∧ a ≠ 1 ∧
        y * g * y⁻¹ ∈ elementCentralizerIn ⊤ a := by
  classical
  have hcase' : Section9.case_9_7_b_data M MF U W1 W2 ⊥ C p q u := by
    simpa [Section13.case_9_7_b_sourceDataForSection13] using hcase
  have hp : Nat.Prime p := Section9.case_9_7_b_p_prime_sec9 hcase'
  rcases hMFsylow with ⟨P, hP⟩
  rcases section14_exists_conj_prime_order_mem_sylow_centralized_of_not_coprime_order
      hp P hnot with
    ⟨y, a, haP, hane, hcent⟩
  exact ⟨y, a, by simpa [hP] using haP, hane, hcent⟩

public theorem section14_typeP_centralizer_le_M_of_case_9_7_b_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u)
    {a x : G}
    (haMF : a ∈ MF) (hane : a ≠ 1)
    (hxcent : x ∈ elementCentralizerIn ⊤ a) :
    x ∈ M := by
  classical
  have hcase' : Section9.case_9_7_b_data M MF U W1 W2 ⊥ C p q u := by
    simpa [Section13.case_9_7_b_sourceDataForSection13] using hcase
  have h92 : Section9.hypothesis_9_2_statement M MF U W1 W2 q :=
    Section9.case_9_7_b_hypothesis_9_2_sec9 hcase'
  have hTI :
      section16TISubset
        (section16NonidentityElements (section8FittingSubgroup M : Set G)) :=
    h92.typeIIToIVSourceCondition.2.2
  rcases h92.typePDefinitionData with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUle, _hUnil, _hW1norm,
      _hDercomp, _hMFnotcyc, _hsecond, hFitEq, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have haF : a ∈ section8FittingSubgroup M := by
    rw [← hFitEq]
    exact (show MF ≤ MF ⊔ subgroupCentralizerIn M MF from le_sup_left) haMF
  have hF_card_ne_one : Nat.card (section8FittingSubgroup M) ≠ 1 := by
    intro hcard
    have haBot : a ∈ (⊥ : Subgroup G) := by
      simpa [(Subgroup.eq_bot_iff_card (H := section8FittingSubgroup M)).2 hcard] using haF
    exact hane (by simpa using haBot)
  rcases Nat.exists_prime_and_dvd
      (n := Nat.card (section8FittingSubgroup M)) hF_card_ne_one with
    ⟨r, hrprime, hrdiv⟩
  let rP : Nat.Primes := ⟨r, hrprime⟩
  have hrF : rP ∈ subgroupPrimeSet (section8FittingSubgroup M) := by
    rw [subgroupPrimeSet]
    change r ∣ Nat.card (section8FittingSubgroup M)
    exact hrdiv
  have hM8 : M ∈ section8MaximalSubgroups G := by
    simpa [section8MaximalSubgroups, section9MaximalSubgroups] using h92.maximal
  have hnormF : Subgroup.normalizer (section8FittingSubgroup M : Set G) = M :=
    section8_normalizer_fittingSubgroup_eq (G := G) (M := M) (q := rP) hM8 hrF
  have hsharp_norm :
      Subgroup.normalizer
        (section16NonidentityElements (section8FittingSubgroup M : Set G)) = M := by
    calc
      Subgroup.normalizer
          (section16NonidentityElements (section8FittingSubgroup M : Set G))
          = Subgroup.normalizer (section8FittingSubgroup M : Set G) :=
            section14_normalizer_nonidentityElements_eq (section8FittingSubgroup M)
      _ = M := hnormF
  have hXti :
      section16TISubsetWithNormalizer
        (section16NonidentityElements (section8FittingSubgroup M : Set G)) M :=
    ⟨hTI, hsharp_norm⟩
  have hxCentralizer : x ∈ Subgroup.centralizer ({a} : Set G) := by
    simpa [elementCentralizerIn] using hxcent.2
  exact section14_centralizer_singleton_le_of_tiWithNormalizer_mem hXti
    ⟨haF, hane⟩ hane hxCentralizer

public theorem section14_typeP_mem_decomposition_of_mem_M
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    {x : G} (hxM : x ∈ M) :
    ∃ d w : G,
      d ∈ ambientDerivedSubgroup M ∧ w ∈ W1 ∧ x = d * w := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUle, _hUnil, _hW1norm,
      _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hcompLocal :
      ((ambientDerivedSubgroup M).subgroupOf M).IsComplement' (W1.subgroupOf M) :=
    Section12.section12ComplementIn_left_normal_isComplement'
      (G := G) (M := M) (K := ambientDerivedSubgroup M) (L := W1)
      hMcomp hDnormal
  let xM : M := ⟨x, hxM⟩
  rcases hcompLocal.existsUnique xM with ⟨⟨dM, wM⟩, hmul, _huniq⟩
  refine ⟨(dM : G), (wM : G), ?_, ?_, ?_⟩
  · exact dM.property
  · exact wM.property
  · exact (congrArg (fun z : M => (z : G)) hmul).symm

public theorem section14_typeP_derived_mem_decomposition_of_mem_derived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    {d : G} (hdD : d ∈ ambientDerivedSubgroup M) :
    ∃ m u : G, m ∈ MF ∧ u ∈ U ∧ d = m * u := by
  classical
  have hPOrig := hP
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUle, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have hMFnormD : (MF.subgroupOf (ambientDerivedSubgroup M)).Normal :=
    (Section13.section13_mf_normalIn_ambientDerived_of_typeP
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hPOrig).2
  have hcompLocal :
      (MF.subgroupOf (ambientDerivedSubgroup M)).IsComplement'
        (U.subgroupOf (ambientDerivedSubgroup M)) :=
    Section12.section12ComplementIn_left_normal_isComplement'
      (G := G) (M := ambientDerivedSubgroup M) (K := MF) (L := U)
      hDercomp hMFnormD
  let dD : ambientDerivedSubgroup M := ⟨d, hdD⟩
  rcases hcompLocal.existsUnique dD with ⟨⟨mD, uD⟩, hmul, _huniq⟩
  refine ⟨(mD : G), (uD : G), ?_, ?_, ?_⟩
  · exact mD.property
  · exact uD.property
  · exact (congrArg (fun z : ambientDerivedSubgroup M => (z : G)) hmul).symm

public theorem section14_typeP_mem_triple_decomposition_of_mem_M
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    {x : G} (hxM : x ∈ M) :
    ∃ m u w : G,
      m ∈ MF ∧ u ∈ U ∧ w ∈ W1 ∧ x = (m * u) * w := by
  classical
  rcases section14_typeP_mem_decomposition_of_mem_M hP hxM with
    ⟨d, w, hdD, hwW1, hx⟩
  rcases section14_typeP_derived_mem_decomposition_of_mem_derived hP hdD with
    ⟨m, u, hmMF, huU, hd⟩
  exact ⟨m, u, w, hmMF, huU, hwW1, by rw [hx, hd]⟩

public theorem section14_frobeniusJoin_centralizer_le_kernel
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R)
    {a x : G}
    (haK : a ∈ K) (hane : a ≠ 1)
    (hxKR : x ∈ K ⊔ R)
    (hxcent : x ∈ elementCentralizerIn ⊤ a) :
    x ∈ K := by
  classical
  by_contra hxnotK
  let S : Subgroup G := K ⊔ R
  let Ksub : Subgroup S := K.subgroupOf S
  let Rsub : Subgroup S := R.subgroupOf S
  have hfrobS : IsFrobeniusGroupWithKernelComplement Ksub Rsub := by
    simpa [section12FrobeniusJoinWithKernel, S, Ksub, Rsub] using hfrob
  haveI : Ksub.Normal := hfrobS.normal
  have hcentR :
      ∀ r : Rsub, r ≠ 1 → Section2.centralizerIn Ksub (r : S) = ⊥ := by
    intro r hr
    have hcentElem : elementCentralizerIn Ksub (r : S) = ⊥ :=
      (lemma_3_1 (G := S) Ksub Rsub hfrobS.kernel_ne_bot hfrobS.complement_ne_bot
        hfrobS.normal hfrobS.isComplement').1 hfrobS r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer, elementCentralizerIn]
      using hcentElem
  let xS : S := ⟨x, hxKR⟩
  have hxnotKsub : xS ∉ Ksub := by
    intro hxKsub
    exact hxnotK (by simpa [Ksub, xS, Subgroup.mem_subgroupOf] using hxKsub)
  have hcentBot : Section2.centralizerIn Ksub xS = ⊥ :=
    Section6.theorem_6_8_frobenius_complement_centralizerIn_eq_bot
      (K := Ksub) (R := Rsub) hfrobS.isComplement' hcentR hxnotKsub
  have haS : a ∈ S := Subgroup.mem_sup_left haK
  let aS : S := ⟨a, haS⟩
  have haKsub : aS ∈ Ksub := by
    simpa [Ksub, aS, Subgroup.mem_subgroupOf] using haK
  have hxcomm : x * a = a * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hxcent.2
  have haCentS : aS ∈ Subgroup.centralizer ({xS} : Set S) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact hxcomm.symm
  have haCentralizerIn : aS ∈ Section2.centralizerIn Ksub xS :=
    ⟨haKsub, haCentS⟩
  have haBot : aS ∈ (⊥ : Subgroup S) := by
    simpa [hcentBot] using haCentralizerIn
  have haOne : a = 1 := by
    have haSOne : aS = 1 := by simpa using haBot
    simpa [aS] using congrArg (fun z : S => (z : G)) haSOne
  exact hane haOne

public theorem section14_section12FrobeniusJoinWithKernel_of_quotientFrobenius_bot
    {G : Type u} [Group G] [Finite G]
    {MF U : Subgroup G}
    (hfrob : Section9.quotientFrobeniusWithKernelData MF (⊥ : Subgroup G) U) :
    section12FrobeniusJoinWithKernel MF U := by
  classical
  rcases hfrob with ⟨_hbotMF, hnormal, hfrobQuot⟩
  let S : Subgroup G := MF ⊔ U
  let N : Subgroup S := (⊥ : Subgroup G).subgroupOf S
  letI : N.Normal := by
    simp [N, S]
  have hNbot : N = ⊥ :=
    section14_subgroupOf_eq_bot_of_eq_bot (C := (⊥ : Subgroup G)) (U := S) rfl
  let e : S ⧸ N ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hNbot).trans
      (QuotientGroup.quotientBot (G := S))
  have hfrobMap :
      IsFrobeniusGroupWithKernelComplement
        (Subgroup.map e.toMonoidHom
          (Subgroup.map (QuotientGroup.mk' N) (MF.subgroupOf S)))
        (Subgroup.map e.toMonoidHom
          (Subgroup.map (QuotientGroup.mk' N) (U.subgroupOf S))) := by
    simpa [e, N, S] using
      section14_isFrobeniusGroupWithKernelComplement_map_mulEquiv
        (e := e) hfrobQuot
  have hKmap :
      Subgroup.map e.toMonoidHom
          (Subgroup.map (QuotientGroup.mk' N) (MF.subgroupOf S)) =
        MF.subgroupOf S := by
    simpa [e] using
      section14_quotient_bot_equiv_map_mk'_subgroup_eq
        (A := S) (N := N) hNbot (MF.subgroupOf S)
  have hRmap :
      Subgroup.map e.toMonoidHom
          (Subgroup.map (QuotientGroup.mk' N) (U.subgroupOf S)) =
        U.subgroupOf S := by
    simpa [e] using
      section14_quotient_bot_equiv_map_mk'_subgroup_eq
        (A := S) (N := N) hNbot (U.subgroupOf S)
  change IsFrobeniusGroupWithKernelComplement (MF.subgroupOf S) (U.subgroupOf S)
  rw [← hKmap, ← hRmap]
  exact hfrobMap

public theorem section14_typeP_Galois_frobenius_MF_U_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u)
    (hCbot : C = ⊥) :
    section12FrobeniusJoinWithKernel MF U := by
  have hcase' : Section9.case_9_7_b_data M MF U W1 W2 (⊥ : Subgroup G) C p q u := by
    simpa [Section13.case_9_7_b_sourceDataForSection13] using hcase
  have hquot : Section9.quotientFrobeniusWithKernelData MF (⊥ : Subgroup G) U :=
    Section9.theorem_9_10_quotient_frobenius_of_C_eq_bot_sec9
      M MF U W1 W2 (⊥ : Subgroup G) C p q u hCbot hcase'
  exact section14_section12FrobeniusJoinWithKernel_of_quotientFrobenius_bot hquot

public theorem section14_mem_conjugatesOfPuncturedSubgroup_of_typeP_coset_factor_ne_one
    {G : Type u} [Group G] [Finite G]
    {M MF U W W1 W2 : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    {m u0 w : G}
    (hmMF : m ∈ MF) (huU : u0 ∈ U) (hwW1 : w ∈ W1) (hwnone : w ≠ 1) :
    (m * u0) * w ∈ conjugatesOfPuncturedSubgroup W := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil,
      _hW1normU, hcompDU, _hMFnotCyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, hCent, _hHatW⟩
  rcases hprod with ⟨hW1leW, hW2leW, _hWsup, hWdisj, _hWcent⟩
  have hDnormM : (D.subgroupOf M).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hW1leM : W1 ≤ M := hcompMW1.2.1
  have hwM : w ∈ M := hW1leM hwW1
  have hnormD_mem : w ∈ Subgroup.normalizer (D : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hcompMW1.1).1 hDnormM) hwM
  have hnormD : Section2.normalizesSet (D : Set G) w := by
    intro z
    have hz := Subgroup.mem_normalizer_iff.mp hnormD_mem z
    simpa [Section2.conjBy] using hz.symm
  have hcopW1D : Nat.Coprime (Nat.card W1) (Nat.card D) := by
    simpa [D] using
      (Section9.typePDefinitionData_W1_card_coprime_ambientDerived_sec9
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
        ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD, _hUnil,
          _hW1normU, hcompDU, _hMFnotCyc, _hM2le, _hFitEq, _hFitLeD,
          _hW2le, _hW2cyc, _hW2ne, hCent, _hHatW⟩)
  have horderW1 : orderOf w ∣ Nat.card W1 :=
    Subgroup.orderOf_dvd_natCard W1 hwW1
  have hcop : Nat.Coprime (orderOf w) (Nat.card D) :=
    Nat.Coprime.coprime_dvd_left horderW1 hcopW1D
  have hPU_D : m * u0 ∈ D := by
    have hPU : m * u0 ∈ MF ⊔ U :=
      (MF ⊔ U).mul_mem (Subgroup.mem_sup_left hmMF) (Subgroup.mem_sup_right huU)
    simpa [D, hcompDU.2.2.1] using hPU
  rcases Section2.proposition_2_1 w D hnormD hcop with
    ⟨reps, _hreps_card, _hreps_mem, _hreps_disj, hunion⟩
  have hcoset : (m * u0) * w ∈ Section2.subgroupCosetByElement D w :=
    ⟨m * u0, hPU_D, rfl⟩
  rw [hunion] at hcoset
  rcases hcoset with ⟨x, _hxreps, hpiece⟩
  rcases hpiece with ⟨s, hs, hsconj⟩
  rcases hs with ⟨c, hcCent, hcs⟩
  have hCentW2 : Section2.centralizerIn D w = W2 := by
    simpa [D, Section2.centralizerIn, Section2.elementCentralizer, elementCentralizerIn]
      using hCent w hwW1 hwnone
  have hcW2 : c ∈ W2 := by
    simpa [hCentW2] using hcCent
  have hcwW : c * w ∈ W :=
    W.mul_mem (hW2leW hcW2) (hW1leW hwW1)
  have hcw_ne : c * w ≠ 1 := by
    intro hcw_one
    have hwW2 : w ∈ W2 := by
      have hw_eq : w = c⁻¹ := by
        calc
          w = 1 * w := by simp
          _ = (c⁻¹ * c) * w := by simp
          _ = c⁻¹ * (c * w) := by simp
          _ = c⁻¹ := by simp [hcw_one]
      simpa [hw_eq] using W2.inv_mem hcW2
    have hwbot : w ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hWdisj hwW1 hwW2
    exact hwnone (by simpa using hwbot)
  have htarget : (m * u0) * w = x * (c * w) * x⁻¹ := by
    simpa [Section2.conjugateImage, Section2.subgroupCosetByElement,
      Section2.rightTranslateSet, Section2.conjBy, hcs] using hsconj
  exact ⟨c * w, hcwW, hcw_ne, ⟨x, htarget⟩⟩

public theorem section14_typeP_Galois_W1_factor_eq_one_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u)
    {g y m u0 w : G}
    (hnotW : g ∉ conjugatesOfPuncturedSubgroup W)
    (_hnot : ¬ (orderOf g).Coprime p)
    (hmMF : m ∈ MF) (huU : u0 ∈ U) (hwW1 : w ∈ W1)
    (hxdec : y * g * y⁻¹ = (m * u0) * w) :
    w = 1 := by
  classical
  by_contra hwnone
  have hP : Section8.typePDefinitionData M MF U W1 W2 :=
    (Section9.case_9_7_b_hypothesis_9_2_sec9 hcase).typePDefinitionData
  have hmem_coset :
      (m * u0) * w ∈ conjugatesOfPuncturedSubgroup W :=
    section14_mem_conjugatesOfPuncturedSubgroup_of_typeP_coset_factor_ne_one
      hprod hP hmMF huU hwW1 hwnone
  have hmem_g : g ∈ conjugatesOfPuncturedSubgroup W := by
    rcases hmem_coset with ⟨x, hxW, hxne, a, ha⟩
    refine ⟨x, hxW, hxne, ⟨y⁻¹ * a, ?_⟩⟩
    calc
      g = y⁻¹ * (y * g * y⁻¹) * y := by group
      _ = y⁻¹ * ((m * u0) * w) * y := by rw [hxdec]
      _ = y⁻¹ * (a * x * a⁻¹) * y := by rw [ha]
      _ = (y⁻¹ * a) * x * (y⁻¹ * a)⁻¹ := by group
  exact hnotW hmem_g

public theorem section14_typeP_Galois_decomposition_contradiction
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u)
    (hCbot : C = ⊥)
    {g y a m u0 w : G}
    (hnotW : g ∉ conjugatesOfPuncturedSubgroup W)
    (hnotMF : g ∉ conjugatesOfPuncturedSubgroup MF)
    (hnot : ¬ (orderOf g).Coprime p)
    (haMF : a ∈ MF) (hane : a ≠ 1)
    (hxcent : y * g * y⁻¹ ∈ elementCentralizerIn ⊤ a)
    (hmMF : m ∈ MF) (huU : u0 ∈ U) (hwW1 : w ∈ W1)
    (hxdec : y * g * y⁻¹ = (m * u0) * w) :
    False := by
  classical
  have hw_eq_one : w = 1 :=
    section14_typeP_Galois_W1_factor_eq_one_source_bridge
      hprod hcase hnotW hnot hmMF huU hwW1 hxdec
  have hPU : m * u0 ∈ MF ⊔ U :=
    (MF ⊔ U).mul_mem (Subgroup.mem_sup_left hmMF) (Subgroup.mem_sup_right huU)
  have hxPU : y * g * y⁻¹ ∈ MF ⊔ U := by
    rw [hxdec, hw_eq_one, mul_one]
    exact hPU
  have hfrob : section12FrobeniusJoinWithKernel MF U :=
    section14_typeP_Galois_frobenius_MF_U_source_bridge hcase hCbot
  have hxMF : y * g * y⁻¹ ∈ MF :=
    section14_frobeniusJoin_centralizer_le_kernel
      hfrob haMF hane hxPU hxcent
  have hgOne : g = 1 :=
    section14_eq_one_of_conj_mem_of_not_mem_conjugatesOfPuncturedSubgroup
      hnotMF hxMF
  exact hnot (by simp [hgOne])

public theorem section14_coprime_typeP_Galois_core_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W W1 W2 C : Subgroup G}
    {p q u : ℕ}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hcase : Section13.case_9_7_b_sourceDataForSection13 M MF U W1 W2 C p q u)
    (hCbot : C = ⊥)
    {g : G}
    (hnotW : g ∉ conjugatesOfPuncturedSubgroup W)
    (hnotMF : g ∉ conjugatesOfPuncturedSubgroup MF) :
    (orderOf g).Coprime p := by
  classical
  have hMFsylow : ∃ P : Sylow p G, (P : Subgroup G) = MF :=
    section14_typeP_MF_sylow_of_case_9_7_b_source hcase
  have hcentralizer_from_not_coprime :
      ¬ (orderOf g).Coprime p →
        ∃ y a : G,
          a ∈ MF ∧ a ≠ 1 ∧
            y * g * y⁻¹ ∈ elementCentralizerIn ⊤ a := by
    intro hnot
    exact section14_exists_conj_typeP_MF_element_centralized_of_not_coprime_order
      hcase hMFsylow hnot
  by_contra hnot
  rcases hcentralizer_from_not_coprime hnot with
    ⟨y, a, haMF, hane, hxcent⟩
  have hxM : y * g * y⁻¹ ∈ M :=
    section14_typeP_centralizer_le_M_of_case_9_7_b_source
      hcase haMF hane hxcent
  have hcase' : Section9.case_9_7_b_data M MF U W1 W2 ⊥ C p q u := by
    simpa [Section13.case_9_7_b_sourceDataForSection13] using hcase
  have h92 : Section9.hypothesis_9_2_statement M MF U W1 W2 q :=
    Section9.case_9_7_b_hypothesis_9_2_sec9 hcase'
  rcases section14_typeP_mem_triple_decomposition_of_mem_M
      h92.typePDefinitionData hxM with
    ⟨m, u0, w, hmMF, huU, hwW1, hxdec⟩
  exact False.elim
    (section14_typeP_Galois_decomposition_contradiction
      hprod hcase hCbot hnotW hnotMF hnot haMF hane hxcent
      hmMF huU hwW1 hxdec)

public theorem section14_theorem_14_11_3_order_coprime_W_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              ψτ = τM₁ ψ →
                ∀ g : G, g ∉ tildeAM →
                  g ∉ conjugatesOfPuncturedSubgroup W →
                  g ∉ conjugatesOfPuncturedSubgroup P →
                  g ∉ conjugatesOfPuncturedSubgroup Q →
                    (orderOf g).Coprime (Nat.card W) := by
  intro hctx h143 h1410 htilde heta hKV hψτ g hnotTilde hnotW hnotP hnotQ
  have hctx_full := hctx
  rcases hctx with ⟨hsource, _hqp⟩
  rcases hsource with
    ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hchoice, hMin, _hFourSixS, _hFourSixT⟩
  haveI : IsMinCE G := hMin
  rcases hcase with
    ⟨hprod, _hWcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  have _h1410 := h1410
  have _htilde := htilde
  have _heta := heta
  have _hKV := hKV
  have _hψτ := hψτ
  have _hnotTilde := hnotTilde
  have hcaseS :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section14_theorem_14_6_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx_full h143
  have hcaseT :
      Section13.case_9_7_b_sourceDataForSection13 Tmax Q V W2 W1 D q p v :=
    (section14_theorem_14_4_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx_full h143).1
  have hCbot : C = ⊥ :=
    section14_C_eq_bot_of_pf13_12_source hctx_full.1
  have hDbot : D = ⊥ :=
    section14_C_eq_bot_of_pf13_12_source
      (section14_hypothesis_13_1_sourceData_swap hctx_full.1)
  have hcopP : (orderOf g).Coprime p :=
    section14_coprime_typeP_Galois_core_source_bridge
      hprod hcaseS hCbot hnotW hnotP
  have hprodT : section12InternalDirectProduct W2 W1 W :=
    Section13.section13_section12InternalDirectProduct_swap hprod
  have hcopQ : (orderOf g).Coprime q :=
    section14_coprime_typeP_Galois_core_source_bridge
      hprodT hcaseT hDbot hnotW hnotQ
  exact section14_order_coprime_card_W_of_pq_source hctx_full hcopP hcopQ

public theorem section14_theorem_14_11_3_eta_integer_values_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              ψτ = τM₁ ψ →
                ∀ g : G, g ∉ tildeAM →
                  g ∉ conjugatesOfPuncturedSubgroup W →
                  g ∉ conjugatesOfPuncturedSubgroup P →
                  g ∉ conjugatesOfPuncturedSubgroup Q →
                    ∃ value : Fin q × Fin p → ℤ,
                      ∀ ij, η ij.1 ij.2 g = (value ij : ℂ) := by
  intro hctx h143 h1410 htilde heta hKV hψτ g hnotTilde hnotW hnotP hnotQ
  have hcopW : (orderOf g).Coprime (Nat.card W) :=
    section14_theorem_14_11_3_order_coprime_W_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d η ψτ
      hctx h143 h1410 htilde heta hKV hψτ g hnotTilde hnotW hnotP hnotQ
  exact section14_eta_integer_values_of_pf39_package heta hcopW

public theorem section14_theorem_14_11_3_eta_integer_pairing_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              ψτ = τM₁ ψ →
                ∀ g : G, g ∉ tildeAM →
                  g ∉ conjugatesOfPuncturedSubgroup W →
                  g ∉ conjugatesOfPuncturedSubgroup P →
                  g ∉ conjugatesOfPuncturedSubgroup Q →
                    section14SignedEtaPairingData η g := by
  intro hctx h143 h1410 htilde heta hKV hψτ g hnotTilde hnotW hnotP hnotQ
  have _hctx := hctx
  have _h143 := h143
  have _h1410 := h1410
  have _htilde := htilde
  have _heta := heta
  have _hKV := hKV
  have _hψτ := hψτ
  have _hnotTilde := hnotTilde
  have _hnotW := hnotW
  have _hnotP := hnotP
  have _hnotQ := hnotQ
  rcases section14_theorem_14_11_3_eta_integer_values_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d η ψτ
      hctx h143 h1410 htilde heta hKV hψτ g hnotTilde hnotW hnotP hnotQ with
    ⟨value, hvalue⟩
  have hindex : section14EtaConjugateIndexData η :=
    section14_etaConjugateIndexData_of_etaData heta
  have hconjData : section14ConjugateEtaPairingData η g :=
    section14ConjugateEtaPairingData_of_indexData
      η g heta hindex value hvalue
  exact section14SignedEtaPairingData_of_conjugateEtaPairingData η g hconjData

public theorem section14_theorem_14_11_3_signed_eta_even_remainder_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (ψτ : Section1.ClassFunction G)
    (ε : Fin q → Fin p → ℤ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              ψτ = τM₁ ψ →
                (∀ i j, ε i j = 1 ∨ ε i j = -1) →
                  ∀ g : G, g ∉ tildeAM →
                    g ∉ conjugatesOfPuncturedSubgroup W →
                    g ∉ conjugatesOfPuncturedSubgroup P →
                    g ∉ conjugatesOfPuncturedSubgroup Q →
                      ∃ eps0 : ℤ, (eps0 = 1 ∨ eps0 = -1) ∧
                        ∃ m : ℤ,
                          ((∑ i : Fin q, ∑ j : Fin p,
                            ((ε i j : ℂ) • η i j)) g) - (eps0 : ℂ) =
                              ((2 * m : ℤ) : ℂ) := by
  intro hctx h143 h1410 htilde heta hKV hψτ hε g hnotTilde hnotW hnotP hnotQ
  have hpairData : section14SignedEtaPairingData η g :=
    section14_theorem_14_11_3_eta_integer_pairing_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d η ψτ
      hctx h143 h1410 htilde heta hKV hψτ g hnotTilde hnotW hnotP hnotQ
  exact section14_signed_eta_even_remainder_of_pairingData η ε g hε hpairData

public theorem section14_theorem_14_11_3_pointwise_even_remainder_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G)
    (ε : Fin q → Fin p → ℤ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  (∀ i j, ε i j = 1 ∨ ε i j = -1) →
                    ∀ g : G, g ∉ tildeAM →
                      g ∉ conjugatesOfPuncturedSubgroup W →
                      g ∉ conjugatesOfPuncturedSubgroup P →
                      g ∉ conjugatesOfPuncturedSubgroup Q →
                      βMτ g = 0 ∧
                        ∃ eps0 : ℤ, (eps0 = 1 ∨ eps0 = -1) ∧
                          ∃ m : ℤ,
                            ((∑ i : Fin q, ∑ j : Fin p,
                              ((ε i j : ℂ) • η i j)) g) - (eps0 : ℂ) =
                                ((2 * m : ℤ) : ℂ) := by
  intro hctx h143 h1410 htilde heta hKV hβMτ hψτ hε g hnotTilde hnotW hnotP hnotQ
  have h1410_full := h1410
  rcases
    section14_theorem_14_11_3_dade_support_nonmem_source_bridge
      M K V Mfam τM τM₁ ψ βM tildeAM h1410_full htilde hnotTilde with
    ⟨R, hDadeM, hnotSupport⟩
  have hrem :
      ∃ eps0 : ℤ, (eps0 = 1 ∨ eps0 = -1) ∧
        ∃ m : ℤ,
          ((∑ i : Fin q, ∑ j : Fin p,
            ((ε i j : ℂ) • η i j)) g) - (eps0 : ℂ) =
              ((2 * m : ℤ) : ℂ) :=
    section14_theorem_14_11_3_signed_eta_even_remainder_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d η ψτ ε
      hctx h143 h1410_full htilde heta hKV hψτ hε g hnotTilde hnotW hnotP hnotQ
  have hβCFOn : Section2.CFOn M (Section12.typeIASet M K) βM := by
    rcases h1410 with
      ⟨_hMmax, _hModd, _hVnorm, hKMF, _hTypeI, _hDadeM, hPunctM, _h52M,
        _hExtM, hψmem, _hψirr, hψdeg, hβM⟩
    simpa [hβM] using
      section14_betaInput_CFOn_typeIASet hKMF hPunctM hψmem hψdeg
  have hβzero : βMτ g = 0 :=
    section14_betaM_tau_eq_zero_of_not_mem_dadeSupport
      (M := M) (K := K) (τM := τM) (βM := βM) (βMτ := βMτ)
      (R := R) hDadeM hβCFOn hβMτ hnotSupport
  exact ⟨hβzero, hrem⟩

public theorem section14_theorem_14_11_3_pointwise_inputs_from_G0_subgroup_traces_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G)
    (ε : Fin q → Fin p → ℤ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  (∀ i j, ε i j = 1 ∨ ε i j = -1) →
                    ∀ g : G, g ∉ tildeAM →
                      g ∉ conjugatesOfPuncturedSubgroup W →
                      g ∉ conjugatesOfPuncturedSubgroup P →
                      g ∉ conjugatesOfPuncturedSubgroup Q →
                      βMτ g = 0 ∧
                        ∃ n : ℤ, Odd n ∧
                          ((∑ i : Fin q, ∑ j : Fin p,
                            ((ε i j : ℂ) • η i j)) g) = (n : ℂ) := by
  intro hctx h143 h1410 htilde heta hKV hβMτ hψτ hε g hnotTilde hnotW hnotP hnotQ
  rcases section14_theorem_14_11_3_pointwise_even_remainder_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d η βMτ ψτ ε
      hctx h143 h1410 htilde heta hKV hβMτ hψτ hε g hnotTilde hnotW hnotP hnotQ with
    ⟨hβzero, eps0, heps0, m, heven⟩
  rcases section14_odd_integer_of_signed_one_plus_even_remainder
      heps0 ⟨m, heven⟩ with
    ⟨n, hnOdd, hsum⟩
  exact ⟨hβzero, n, hnOdd, hsum⟩

public theorem section14_theorem_14_11_3_pointwise_inputs_from_G0_components_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G)
    (ε : Fin q → Fin p → ℤ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  (∀ i j, ε i j = 1 ∨ ε i j = -1) →
                    ∀ g : G, g ∉ tildeAM →
                      g ∉ conjugatesOfPuncturedSubgroup W →
                      g ∉ conjugatesOfPuncturedSubgroup P →
                      g ∉ conjugatesOfPuncturedSubgroup Q →
                      βMτ g = 0 ∧
                        ∃ n : ℤ, Odd n ∧
                          ((∑ i : Fin q, ∑ j : Fin p,
                            ((ε i j : ℂ) • η i j)) g) = (n : ℂ) := by
  intro hctx h143 h1410 htilde heta hKV hβMτ hψτ hε g hnotTilde hnotW hnotP hnotQ
  exact
    section14_theorem_14_11_3_pointwise_inputs_from_G0_subgroup_traces_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d η βMτ ψτ ε
      hctx h143 h1410 htilde heta hKV hβMτ hψτ hε g hnotTilde
      hnotW hnotP hnotQ

public theorem section14_theorem_14_11_3_pointwise_inputs_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G)
    (ε : Fin q → Fin p → ℤ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  (∀ i j, ε i j = 1 ∨ ε i j = -1) →
                    ∀ g : G, g ∈ theorem_14_11_3_G0 tildeAM W P Q →
                      βMτ g = 0 ∧
                        ∃ n : ℤ, Odd n ∧
                          ((∑ i : Fin q, ∑ j : Fin p,
                            ((ε i j : ℂ) • η i j)) g) = (n : ℂ) := by
  intro hctx h143 h1410 htilde heta hKV hβMτ hψτ hε g hg
  rcases section14_not_mem_components_of_mem_G0 hg with
    ⟨hnotTilde, hnotW, hnotP, hnotQ⟩
  exact
    section14_theorem_14_11_3_pointwise_inputs_from_G0_components_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d η βMτ ψτ ε
      hctx h143 h1410 htilde heta hKV hβMτ hψτ hε g
      hnotTilde hnotW hnotP hnotQ

public theorem section14_theorem_14_11_3_pointwise_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  theorem_14_11_2_data M K η βMτ ψτ e →
                    theorem_14_11_3_data (theorem_14_11_3_G0 tildeAM W P Q) ψτ := by
  intro hctx h143 h1410 htilde heta hKV hβMτ hψτ h112
  rcases h112 with ⟨_heq, _hmul, ε, hε, hexp⟩
  intro g hg
  rcases section14_theorem_14_11_3_pointwise_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d η βMτ ψτ ε
      hctx h143 h1410 htilde heta hKV hβMτ hψτ hε g hg with
    ⟨hβzero, n, hnOdd, hsumInt⟩
  have hsum :
      1 ≤ Complex.normSq
        ((∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) g) :=
    section14_normSq_ge_one_of_odd_integer_value hsumInt hnOdd
  exact
    section14_normSq_ge_of_beta_zero_and_signed_expansion
      η βMτ ψτ ε g hβzero hexp hsum

public theorem section14_theorem_14_11_3_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (ψτ : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            K ≠ V →
              ψτ = τM₁ ψ →
                theorem_14_11_3_data (theorem_14_11_3_G0 tildeAM W P Q) ψτ := by
  intro hctx h143 h1410 htilde hKV hψτ
  rcases section14EtaData_of_sourceData hctx.1 with ⟨η, heta⟩
  let βMτ : Section1.ClassFunction G := τM βM
  let e : ℕ := K.relIndex M
  have h112 : theorem_14_11_2_data M K η βMτ ψτ e :=
    section14_theorem_14_11_2_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η βMτ ψτ
      hctx h143 h1410 heta hKV rfl hψτ rfl
  exact section14_theorem_14_11_3_pointwise_source_bridge
    Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
    M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d e η βMτ ψτ
    hctx h143 h1410 htilde heta hKV rfl hψτ h112


end CFSG.Section14
