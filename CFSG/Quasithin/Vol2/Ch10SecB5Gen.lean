module

public import CFSG.Quasithin.Vol2.Ch10SecB5Three
public import CFSG.Quasithin.Vol2.Ch10SecBL32Gen
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3Sec1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem T1_ne_bot (h : MaxCtx T L I t Ψ c) : T1 T L ≠ ⊥ := by
  intro hb
  have hT0 : T0 T L = ⊥ := le_bot_iff.mp (hb ▸ SecA.T0_le_T1 h.hyp.fsu.maximal.1)
  have h1 := h.hC.T0
  rw [hT0, Subgroup.bot_subgroupOf, Subgroup.map_bot] at h1
  have h2 : Nat.card (⊥ : Subgroup (L32.Γ × L32.Γ)) = Nat.card (L32.U3.prod L32.U3) := by
    rw [h1]
  rw [Subgroup.card_bot, card_prod_self, card_U3] at h2
  omega

theorem inH_normalizer_T1 (h : MaxCtx T L I t Ψ c) :
    InH T (Subgroup.normalizer (T1 T L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨T1_normal h.h37 h.h38 h.hyp, fun hb => T1_ne_bot h (le_bot_iff.mp (hb ▸ ?_))⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
    (h.hyp.fsu.sylow.1.to_le inf_le_left)

theorem inH_HA (h : MaxCtx T L I t Ψ c) : InH T (preIn Ψ (A.prod A) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_sup_right, fun hb => SecA.pCoreOf_fsuM_ne_bot h.hyp.fsu.faithful ?_⟩
  refine le_bot_iff.mp (hb ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((SecA.pCoreOf_le_of_sylow h.hyp.fsu.sylow (SecA.le_fsuM T L)).trans le_sup_right) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
  exact (sup_le ((preIn_le Ψ _).trans (SecA.fsuL0_le_fsuM T L)) (SecA.le_fsuM T L)).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

theorem pCoreOf_GA_ne_bot (h311 : Theorem311Stmt) (h : MaxCtx T L I t Ψ c)
    (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb) :
    pCoreOf 2 (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := h.hyp
  obtain ⟨R₀, hR₀, hR₀T1, hnorm⟩ := h311 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow (Subgroup.normalizer (T1 T L : Set G)) (preIn Ψ (A.prod A) ⊔ T) (T1 T L)
    (inH_normalizer_T1 h) (inH_HA h) ⟨T, isUniqueMaxOver_T h hA⟩ (T1_ne_bot h) inf_le_left
    (isSylowTwoOf_T1 h hD) le_rfl
  intro hb
  apply hR₀
  refine le_bot_iff.mp (hb ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hR₀T1.trans (Subgroup.le_normalizer.trans le_sup_left)) hnorm
    (hyp.fsu.sylow.1.to_le (hR₀T1.trans inf_le_left)))

theorem fsuL0_perfect (h : MaxCtx T L I t Ψ c) : ⁅fsuL0 T L, fsuL0 T L⁆ = fsuL0 T L := by
  have hL := SecA.perfect_L h.hyp.fsu.maximal.1
  have hLt : ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ = CFSG.conjugate L t := by
    rw [SecA.conjugate_eq_map, ← Subgroup.map_commutator, hL]
  rw [SecA.fsuL0_eq_sup h.h37 h.h38 h.hyp h.ht h.htn]
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · have e : L ⊔ CFSG.conjugate L t =
        ⁅L, L⁆ ⊔ ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ := by rw [hL, hLt]
    calc L ⊔ CFSG.conjugate L t = ⁅L, L⁆ ⊔ ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ := e
      _ ≤ _ := sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)

theorem XOf_sup_eq (h : MaxCtx T L I t Ψ c) :
    XOf T L Ψ L32.Pa ⊔ XOf T L Ψ L32.Pb = fsuL0 T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := XOf T L Ψ L32.Pa ⊔ XOf T L Ψ L32.Pb with hYdef
  have hYL0 : Y ≤ fsuL0 T L := sup_le (XOf_le_fsuL0 h parData_a) (XOf_le_fsuL0 h parData_b)
  refine le_antisymm hYL0 ?_
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun s hs => by
    have h1 := (isXi_XOf h parData_a).2.1 hs
    have h2 := (isXi_XOf h parData_b).2.1 hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  have himg : imgIn Ψ Y = ⊤ := by
    refine eq_top_iff.mpr (L32.prod_sup_eq_top.symm.le.trans (sup_le ?_ ?_))
    · rw [← imgIn_XOf h parData_a]; exact imgIn_mono Ψ le_sup_left
    · rw [← imgIn_XOf h parData_b]; exact imgIn_mono Ψ le_sup_right
  have hsup : Y ⊔ pCoreOf 2 (fsuL0 T L) = fsuL0 T L := by
    refine le_antisymm (sup_le hYL0 (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) fun l hl => ?_
    have hq : Ψ ⟨l, hl⟩ ∈ imgIn Ψ Y := by rw [himg]; trivial
    obtain ⟨y, hyL0, hyY, hy⟩ := mem_imgIn.mp hq
    have h1 : Ψ (⟨y, hyL0⟩⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
    have h2 := (h.hC.ker _).mp h1
    have := Subgroup.mul_mem_sup hyY h2
    simpa using this
  have hL0 : fsuL0 T L = oTwoUpper (fsuL0 T L) := eq_oTwoUpper_of_perfect (fsuL0_perfect h)
  calc fsuL0 T L = oTwoUpper (fsuL0 T L) := hL0
    _ = oTwoUpper (Y ⊔ pCoreOf 2 (fsuL0 T L)) := by rw [hsup]
    _ = oTwoUpper Y := oTwoUpper_sup_eq (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
        ((SecA.pCoreOf_fsuL0_le_T0 h.hyp.fsu.sylow).trans (inf_le_left.trans hTY))
    _ ≤ Y := oTwoUpper_le Y

end CFSG.Quasithin.Vol2.Ch10.SecB
