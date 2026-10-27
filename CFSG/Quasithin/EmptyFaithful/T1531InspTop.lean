module

public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.EmptyFaithful.T1531InspMod
public import CFSG.Quasithin.EmptyFaithful.T1531Cat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem perm_fin3_sign_eq_one_of_odd {σ : Equiv.Perm (Fin 3)} (h : Odd (orderOf σ)) :
    Equiv.Perm.sign σ = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : Equiv.Perm.sign σ ^ orderOf σ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [hk, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h1
  exact h1

theorem perm_fin3_eq_pow_of_sign_eq_one :
    ∀ σ τ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 → Equiv.Perm.sign τ = 1 → τ ≠ 1 →
      σ = 1 ∨ σ = τ ∨ σ = τ ^ 2 := by
  decide +kernel

section S3

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem oTwoUpper_G2_153 (r67 : Res15367 T Mc M V₁ V₂ E) (hT2 : IsPGroup 2 ↥(TE153 T E)) :
    oTwoUpper (G2_153 T E) = XE153 E :=
  oTwoUpper_sup_eq (oTwoUpper_oTwoUpper _).symm hT2 (inf_le_right.trans r67.XE_normal)

theorem XE_eq_oTwoUpper_of_S3 (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368 T Mc M E s)
    (hS3 : Nonempty (↥(Xdot153 T Mc M E s) ≃* Equiv.Perm (Fin 3))) :
    XE153 E = oTwoUpper (thompsonJ (G0_153 T Mc M E s)) := by
  obtain ⟨e⟩ := hS3
  have hT := isSylowTwoOf_TE_G0 c L r66 r67 gl r68
  have hXEJ := XE_le_thompsonJ c L r66 r67 gl r68
  have hXI : XE153 E ≤ G0_153 T Mc M E s :=
    (le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right
  have hXEidem : XE153 E = oTwoUpper (XE153 E) := (oTwoUpper_oTwoUpper _).symm
  have hKT : IsPGroup 2 ↥(pCoreOf 2 (G0_153 T Mc M E s)) := pCoreOf_isPGroup 2 _
  have hKN : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.normalizer (XE153 E : Set G) :=
    (pCoreOf_le_of_isSylowTwoOf hT).trans (inf_le_right.trans r67.XE_normal)
  have hXbar := barQ_XE_ne_bot r67 r68 hXI
  obtain ⟨w, hwX, hwodd, hw1⟩ : ∃ w ∈ barQ (G0_153 T Mc M E s)
      (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (XE153 E), Odd (orderOf w) ∧ w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hXbar
    have h1 := barQ_oTwoUpper (I := G0_153 T Mc M E s) (Q := CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      hXI
    rw [← hXEidem] at h1
    rw [h1]
    refine le_bot_iff.mp ((Subgroup.closure_le _).mpr fun x hx => ?_)
    simpa using hcon x hx.1 hx.2
  have hwN : w ∈ Xdot153 T Mc M E s := barQ_mono hXEJ hwX
  have hodd : ∀ u ∈ Xdot153 T Mc M E s, Odd (orderOf u) →
      u ∈ barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (XE153 E) := by
    intro u hu huodd
    have hsu : Equiv.Perm.sign (e ⟨u, hu⟩) = 1 :=
      perm_fin3_sign_eq_one_of_odd (by rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk])
    have hsw : Equiv.Perm.sign (e ⟨w, hwN⟩) = 1 :=
      perm_fin3_sign_eq_one_of_odd (by rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk])
    have hw1' : e ⟨w, hwN⟩ ≠ 1 := fun h => hw1 (by
      have := e.injective (h.trans (map_one e).symm)
      simpa using congrArg Subtype.val this)
    rcases perm_fin3_eq_pow_of_sign_eq_one _ _ hsu hsw hw1' with h | h | h
    · have : u = 1 := by
        have := e.injective (h.trans (map_one e).symm)
        simpa using congrArg Subtype.val this
      rw [this]
      exact Subgroup.one_mem _
    · have : u = w := by
        have := e.injective h
        simpa using congrArg Subtype.val this
      rw [this]
      exact hwX
    · have : u = w ^ 2 := by
        have := e.injective (h.trans (map_pow e _ 2).symm)
        simpa using congrArg Subtype.val this
      rw [this]
      exact Subgroup.pow_mem _ hwX 2
  have hy : ∀ y ∈ thompsonJ (G0_153 T Mc M E s), Odd (orderOf y) → y ∈ XE153 E := by
    intro y hyJ hyodd
    have hyI : y ∈ G0_153 T Mc M E s := (B6.thompsonJ_le _) hyJ
    have huN : (QuotientGroup.mk ⟨y, hyI⟩ : ↥(G0_153 T Mc M E s) ⧸
        CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) ∈ Xdot153 T Mc M E s :=
      Subgroup.mem_map.mpr ⟨⟨y, hyI⟩, hyJ, rfl⟩
    have huodd : Odd (orderOf (QuotientGroup.mk ⟨y, hyI⟩ : ↥(G0_153 T Mc M E s) ⧸
        CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) := by
      refine Odd.of_dvd_nat (n := orderOf y) hyodd ?_
      have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))
        (⟨y, hyI⟩ : ↥(G0_153 T Mc M E s))
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨x, hxX, hxu⟩ := mem_barQ.mp (hodd _ huN huodd)
    have h1 : x⁻¹ * ⟨y, hyI⟩ ∈ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
      QuotientGroup.eq.mp hxu
    have h2 : (x : G)⁻¹ * y ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
      rw [r68.pCore_eq]
      exact ⟨x⁻¹ * ⟨y, hyI⟩, h1, by simp⟩
    have hysup : y ∈ XE153 E ⊔ pCoreOf 2 (G0_153 T Mc M E s) := by
      have := Subgroup.mul_mem_sup hxX h2
      simpa using this
    exact mem_of_mem_sup_of_odd hKT hKN hysup hyodd
  refine le_antisymm ?_ ?_
  · calc XE153 E = oTwoUpper (XE153 E) := hXEidem
      _ ≤ oTwoUpper (thompsonJ (G0_153 T Mc M E s)) := oTwoUpper_mono hXEJ
  · refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨k, hy _ ((thompsonJ _).pow_mem hx _) ?_⟩
    have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
    rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm

end S3

section Top

theorem stage1531InspectBCat_of_inputs (h56 : AsB56) (hI1 : InspectListF618)
    (hI23 : InspectRemaining153) : Stage1531InspectBCat := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc
  have hT := isSylowTwoOf_TE_G0 c L r66 r67 gl r68
  have hSQ : SQTKGroup ↥(G0_153 T Mc M E s) := sqtkGroup_G0 c r68
  have hA : IsGoldschmidtAmalgam
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G1_153 T Mc M E s))
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G2_153 T E)) := by
    rcases r68.triple.goldschmidt_mod_pPrimeCore with ⟨-, hA, -⟩ | ⟨-, -, -, -, hcyc⟩
    · exact hA
    · exfalso
      apply hcyc
      have hpc : Open.pCore 2 ↥(G0_153 T Mc M E s) = CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
        Subgroup.map_injective (G0_153 T Mc M E s).subtype_injective r68.pCore_eq
      have hbot : (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (Open.pCore 2 ↥(G0_153 T Mc M E s))) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hpc]
      rw [hbot]
      infer_instance
  have hD : Open.pCore 2 (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) = ⊥ :=
    hA.pCore_eq_bot
  have hXEJ := XE_le_thompsonJ c L r66 r67 gl r68
  have hXI : XE153 E ≤ G0_153 T Mc M E s :=
    (le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right
  have hV0 : IsElemAbelian 2 (V0_153 T Mc M E s) := isElemAbelian_V0 c r68
  have hIN : G0_153 T Mc M E s ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := V0_normal
  have hVI : V0_153 T Mc M E s ≤ G0_153 T Mc M E s := V0_le_G0 r68
  have hQ : CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) =
      (G0_153 T Mc M E s ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)).subgroupOf
        (G0_153 T Mc M E s) := pPrimeCore_G0_eq c r67 r68
  have hB53 := b53Hyp_autI_thompsonJ hV0 hIN hVI _ hQ hD
    (sqtkGroup_of_le hSQ (B6.thompsonJ_le _))
  have hρ := rhoOf_injective hV0 hIN _ hQ
  have hmapN := map_rhoOf_barQ hV0 hIN _ hQ (B6.thompsonJ_le (G0_153 T Mc M E s))
  have hNne : autI hV0 (thompsonJ (G0_153 T Mc M E s)) ≠ ⊥ := by
    rw [← hmapN]
    intro h
    have h' := (Subgroup.map_eq_bot_iff_of_injective _ hρ).mp h
    exact barQ_XE_ne_bot r67 r68 hXI (le_bot_iff.mp ((barQ_mono hXEJ).trans h'.le))
  have hcases := h56 (IntMod (V0_153 T Mc M E s) hV0) (fun v => IntMod.sq_eq_one v) _ hNne hB53
  have hJI : thompsonJ (TE153 T E) ≤ G0_153 T Mc M E s := (B6.thompsonJ_le _).trans hT.1
  have hJD₁ : barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      (thompsonJ (TE153 T E)) ≤
      barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G1_153 T Mc M E s) :=
    barQ_mono ((B6.thompsonJ_le _).trans le_sup_right)
  have hJp : IsPGroup 2 ↥(barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      (thompsonJ (TE153 T E))) :=
    isPGroup_barQ hJI (hT.2.1.to_le (B6.thompsonJ_le _))
  have hD₁N : barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      (G1_153 T Mc M E s) ≤ Subgroup.normalizer
        (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
          (thompsonJ (TE153 T E)) : Set (↥(G0_153 T Mc M E s) ⧸
            CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) :=
    barQ_le_normalizer (G1_le_normalizer_thompsonJ_TE c L r67 gl)
  have hcomm : ⁅oTwoUpper (barQ (G0_153 T Mc M E s)
        (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G2_153 T E)),
      barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
        (thompsonJ (TE153 T E))⁆ =
      oTwoUpper (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
        (G2_153 T E)) := by
    have hG2I : G2_153 T E ≤ G0_153 T Mc M E s := le_sup_right
    rw [← barQ_oTwoUpper hG2I, oTwoUpper_G2_153 r67 hT.2.1, ← barQ_commutator hXI hJI]
    congr 1
    rw [← thompsonJ_R_eq r67 L]
    exact r67.XE_comm.symm
  have hN : barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      (thompsonJ (G0_153 T Mc M E s)) =
      Subgroup.normalClosure (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
        (thompsonJ (TE153 T E)) : Set (↥(G0_153 T Mc M E s) ⧸
          CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) := by
    apply le_antisymm
    · exact barQ_thompsonJ_le_of_normal hT Subgroup.subset_normalClosure
    · have := barQ_thompsonJ_normal (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      exact Subgroup.normalClosure_le_normal (barQ_mono (B6.thompsonJ_le_of_sylow hT))
  have hres := hI1 _ _ _ _ _ hA hconc hJD₁ hJp hD₁N hcomm hN (IntMod (V0_153 T Mc M E s) hV0)
    (fun v => IntMod.sq_eq_one v) (rhoOf hV0 hIN _ hQ) hρ (by rw [hmapN]; exact hB53)
    (by rw [hmapN]; exact hcases)
  by_cases hS3 : Nonempty (↥(Xdot153 T Mc M E s) ≃* Equiv.Perm (Fin 3))
  · exact Or.inl (XE_eq_oTwoUpper_of_S3 c L r66 r67 gl r68 hS3)
  · rcases hres with h | ⟨hlist, hO2⟩
    · exact absurd h hS3
    · exact Or.inr (hI23 G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc hlist hS3 hO2)

theorem stageTheorem1531_of_inputsInsp (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hF : F6.TheoremF618Cat) (i44 : Stage15344) (i46 : Stage15346Four) (i49c : Stage15349Core)
    (i50 : Stage15350) (i65 : Stage15365One) (i67r : Stage15367Rest) (i68t : Stage15368Two)
    (h56 : AsB56) (hI1 : InspectListF618) (hI23 : InspectRemaining153) : StageTheorem1531 :=
  stageTheorem1531_of_inputsCat h11 h113 hF i44 i46 i49c i50 i65 i67r i68t
    (stage1531InspectBCat_of_inputs h56 hI1 hI23)

end Top

end CFSG.Quasithin
