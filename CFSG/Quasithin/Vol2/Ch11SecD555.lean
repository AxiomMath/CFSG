module

public import CFSG.Quasithin.Vol2.Ch11SecDNat
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch11SecDK
public import CFSG.Quasithin.Vol2.Ch11SecDDirect
public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem almostSpecialHyp_of (hNat : NatV3Fact) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1)
    (h1151 : Stmt11_5_1) (h : Hyp11 G T L I n) {V₁ V₃ H₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃) (hH₁ : InH (LOf L V₁ ⊔ T) H₁)
    (hH₁N : H₁ ≤ Subgroup.normalizer (V₁ : Set G)) :
    AlmostSpecialHyp V₃ V₁ (LOf L V₁) T H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset := natSetting11_of h1102 h1141 h hV₁
  obtain ⟨hV₁₃, F, _, _, -, hnat⟩ := hNat G T L I n V₁ V₃ hset (h1151 G T L I n h) hV₁ hV₃
  have hV₃V := SecA.IsVi.le_fsuV hV₃
  have hTL₁ : T ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun t ht =>
    mem_normalizer_lOf (h.normal ht) (SecA.IsVi.le_normalizer hV₁ ht)
  have hO2 : oTwoUpper (LOf L V₁) = LOf L V₁ :=
    C2Nine.oTwoUpper_eq_of_perfect (perfectCore_perfect _)
  have hlOne : lOne (LOf L V₁) V₁ = LOf L V₁ := by
    rw [lOne, inf_eq_left.mpr (lOf_le_normalizer L V₁), hO2]
  have hTH₁ : T ≤ H₁ := le_sup_right.trans hH₁.1
  have hlt : V₁ < V₃ := by
    refine lt_of_le_of_ne hV₁₃ fun heq => ?_
    obtain ⟨-, -, -, -, β, hβ, hβker, -⟩ := hnat
    obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd (Pi.single 0 1))
    have h1 : β v = 1 := by
      rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf, heq]
      exact v.2
    rw [h1] at hv
    have := congrArg (fun x : Multiplicative (Fin 2 → F) => Multiplicative.toAdd x 0) hv
    simp at this
  refine ⟨A1b.isElemAbelian_of_le hV₃V (SecA.isElemAbelian_fsuV h), SecA.IsVi.ne_bot h hV₁ le_rfl,
    hV₁₃, hO2.symm, hV₃V.trans (SecA.fsuV_le_T h), SecA.IsVi.le_normalizer hV₁,
    SecA.IsVi.le_normalizer hV₃, hTL₁, isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right,
    hH₁N, by rw [hlOne]; exact hH₁.1, isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTH₁,
    charTwo_of_inH h.fsu.qtke.2.1 (h.fsu.sylow.1.toSylow h.fsu.sylow.2) (H := H₁)
      (by rw [IsPGroup.toSylow_coe]; exact ⟨hTH₁, hH₁.2⟩), ?_⟩
  rw [hlOne]
  refine ⟨hlt, sup_le hnat.1 (SecA.IsVi.le_normalizer hV₃),
    sup_le (lOf_le_normalizer L V₁) (SecA.IsVi.le_normalizer hV₁), fun W hV₁W hWV₃ hWN => ?_⟩
  exact isNaturalSection_irred hnat hV₁W hWV₃ (le_sup_left.trans hWN)

theorem stmt11_5_5_of (hNat : NatV3Fact) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1)
    (h1151 : Stmt11_5_1) : Stmt11_5_5 := by
  intro G _ _ T L I n V₁ V₃ H₁ h hV₁ hV₃ hH₁ _ hH₁N
  have hA := almostSpecialHyp_of hNat h1102 h1141 h1151 h hV₁ hV₃ hH₁ hH₁N
  have hcc := hA.conjClosure_le_N
  have hU := hA.G22_one.2
  have hmem : ∀ u (hu : u ∈ conjClosure V₃ H₁), tmk V₁ ⟨u, hcc hu⟩ ∈
      omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H₁)) := fun u hu =>
    (secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu
  have h1 : conjClosure V₃ H₁ ≤ pCoreOf 2 H₁ := fun u hu =>
    (secMk_mem_secImg_iff hA.V₁_le_pCoreOf).1 (omegaOneCenterOf_le _ (hmem u hu))
  have h2 : ⁅conjClosure V₃ H₁, pCoreOf 2 H₁⁆ ≤ V₁ := by
    rw [Subgroup.commutator_le]
    intro u hu q hq
    have hqN : q ∈ Subgroup.normalizer (V₁ : Set G) :=
      hH₁N (CFSG.LieType.BorelTits.pCoreOf_le 2 H₁ hq)
    have hqQ : tmk V₁ ⟨q, hqN⟩ ∈ tildeOf V₁ (pCoreOf 2 H₁) := secMk_mem_secImg hq
    have hxy := (mem_centralizer_of_mem_omegaOneCenterOf (hmem u hu) hqQ).symm
    rw [commutatorElement_def]
    exact commutator_mem_of_secMk_commute hxy
  refine ⟨h1, h2, hA.G22_two, fun hK => ?_⟩
  have hset := natSetting11_of h1102 h1141 h hV₁
  obtain ⟨hV₁₃, F, _, _, hF, hnat⟩ := hNat G T L I n V₁ V₃ hset (h1151 G T L I n h) hV₁ hV₃
  have hNL₁ : ∀ x ∈ H₁, x ∈ Subgroup.normalizer (LOf L V₁ : Set G) := fun x hx => by
    rw [← hK]
    exact normalizer_le_normalizer_kOf L V₁ V₁ (hH₁N hx)
  have hnat' : ∀ x ∈ H₁, IsNaturalSection (LOf L V₁) (conjSubgroup V₃ x) V₁
      (CFSG.pCore 2 ↥(LOf L V₁)) (StatedSL 2 F) := fun x hx =>
    isNaturalSection_conj hnat (hNL₁ x hx) (hH₁N hx)
  set 𝒲 : Set (Subgroup G) := {W | ∃ x ∈ H₁, W = conjSubgroup V₃ x} with h𝒲
  have hV₁U : V₁ ≤ conjClosure V₃ H₁ := hV₁₃.trans (le_conjClosure V₃ H₁)
  have hle : ∀ x ∈ H₁, V₁ ≤ conjSubgroup V₃ x ∧ conjSubgroup V₃ x ≤ conjClosure V₃ H₁ := by
    intro x hx
    refine ⟨fun v hv => mem_conjSubgroup_iff.mpr (hV₁₃ ((Subgroup.mem_normalizer_iff.mp
      (hH₁N hx) v).mp hv)), fun w hw => ?_⟩
    have hw' := mem_conjClosure (H₁.inv_mem hx) (mem_conjSubgroup_iff.mp hw)
    simpa [mul_assoc] using hw'
  obtain ⟨s, W, hW𝒲, hind, hsum⟩ := exists_independent_decomposition (K := LOf L V₁) (𝒲 := 𝒲)
    ((Subgroup.commutator_mono le_rfl h1).trans h2) hV₁U (lOf_le_normalizer L V₁)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hle x hx).1, (hle x hx).2, (hnat' x hx).1⟩)
    (by
      rintro _ ⟨x, hx, rfl⟩ X hV₁X hXW hLX
      exact isNaturalSection_irred (hnat' x hx) hV₁X hXW hLX)
    (conjClosure_le fun x hx v hv => by
      refine Subgroup.mem_sup_right (le_iSup₂ (f := fun (W : Subgroup G) (_ : W ∈ 𝒲) => W)
        (conjSubgroup V₃ x⁻¹) ⟨x⁻¹, H₁.inv_mem hx, rfl⟩ ?_)
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hv)
  refine ⟨s, W, F, inferInstance, inferInstance, hF, fun i => ?_, hind, hsum, fun i => ?_⟩
  · obtain ⟨x, hx, hWi⟩ := hW𝒲 i
    rw [hWi]
    exact hle x hx
  · obtain ⟨x, hx, hWi⟩ := hW𝒲 i
    rw [hWi, hK]
    exact hnat' x hx

end CFSG.Quasithin.Vol2.Ch11.SecD
