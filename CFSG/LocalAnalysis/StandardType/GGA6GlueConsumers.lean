module

public import CFSG.LocalAnalysis.StandardType.GGA6GlueDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedAssembly

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ggA6_quot_of_iso {X : Type} [Group X] {J : Subgroup X}
    (h : Nonempty (↥J ≃* alternatingGroup (Fin 6))) :
    Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := h
  have hZA : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have h1 := Subgroup.map_center_eq e
  rw [hZA] at h1
  have hZ : Subgroup.center ↥J = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

theorem ggA6NoJAt_of_quot
    {t : StatedLieTag} (hQ : GGA6QuotNoJAt t) : GGA6NoJAt t := by
  intro X _ _ n f ψ p G₀ D J hr hk hLie hp hp2 hDn hdiag hEA hDc hJ hA6
  exact hQ X n f ψ p G₀ D J hr hk hLie hp hp2 hDn hdiag hEA hDc hJ (ggA6_quot_of_iso hA6)

theorem ggA6_F4_core_of_quot
    (hF4 : GGA6QuotF4f) (hCls : GGA6F4ClassInput) : GGA6F4Core := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hr hk hLie hp hp2 hcop hBN hdiag hab hDB hDc hJ hx hx1 hLG hL
    hJL hDL hmk hA6
  have hf := hF4 X n f ψ p G₀ D J hr hk hLie hp hp2 (hDB.trans hBN)
    (fun d hd => hdiag d (hDB hd)) (ggA6_isElemAbelian_of_le hab hDB) hDc hJ
    (ggA6_quot_of_iso hA6)
  subst hf
  obtain ⟨hp3, m, hm, hLm⟩ := ggA6_F4_core_of_f_eq_one hCls X n ψ p G₀ B₁ D J L x hr hk hLie hp hp2
    hcop hBN hdiag hab hDB hDc hJ hx hx1 hLG hL hJL hDL hmk hA6
  exact ⟨hp3, rfl, m, hm, hLm⟩

theorem ggSixA6KnownRedAt_F4_of_quot
    (hF4 : GGA6QuotF4f) (hCls : GGA6F4ClassInput) :
    GGSixA6KnownRedAt .F4 := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hr hk hLie hp hp2 hcop hBN hdiag hab _ hDB hDc hJ hx hx1 hLG
    hL hJL hDL hmk hA6
  obtain ⟨hp3, hf, m, hm, hLm⟩ := ggA6_F4_core_of_quot hF4 hCls X n f ψ p G₀ B₁ D J L x hr hk hLie
    hp hp2 hcop hBN hdiag hab hDB hDc hJ hx hx1 hLG hL hJL hDL hmk hA6
  obtain ⟨hZ, hB⟩ := ggA6_center_le .F4 (Or.inr rfl) X n f ψ p G₀ B₁ hr hk hLie hp hp2 hcop hBN
    hdiag hab
  exact ⟨hp3, hf, Or.inr rfl, hZ, hB, m, hm, hLm⟩

theorem ggSixA6KnownRedRemaining_of_noJ
    (hE : ∀ t : StatedLieTag,
      (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) → GGA6QuotNoJAt t)
    (hF4 : GGA6QuotF4f) (hCls : GGA6F4ClassInput) : GGSixA6KnownRedRemaining :=
  ⟨ggSixA6KnownRedAt_of_noJ _ (ggA6NoJ_classical _ (Or.inl rfl)),
    ggSixA6KnownRedAt_of_noJ _ (ggA6NoJ_classical _ (Or.inr (Or.inl rfl))),
    ggSixA6KnownRedAt_PSp,
    ggSixA6KnownRedAt_of_noJ _ (ggA6NoJ_classical _ (Or.inr (Or.inr (Or.inl rfl)))),
    ggSixA6KnownRedAt_of_noJ _ (ggA6NoJ_classical _ (Or.inr (Or.inr (Or.inr rfl)))),
    ggSixA6KnownRedAt_F4_of_quot hF4 hCls,
    ggSixA6KnownRedAt_of_noJ _ (ggA6NoJAt_of_quot (hE _ (Or.inl rfl))),
    ggSixA6KnownRedAt_of_noJ _ (ggA6NoJAt_of_quot (hE _ (Or.inr (Or.inl rfl)))),
    ggSixA6KnownRedAt_of_noJ _ (ggA6NoJAt_of_quot (hE _ (Or.inr (Or.inr (Or.inl rfl))))),
    ggSixA6KnownRedAt_of_noJ _ (ggA6NoJAt_of_quot (hE _ (Or.inr (Or.inr (Or.inr rfl)))))⟩

end CFSG.StandardType.A6Red
