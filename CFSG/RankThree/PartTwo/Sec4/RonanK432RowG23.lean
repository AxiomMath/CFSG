module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.HardMathSupport.Timmesfeld.LieRank.G2
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Adapters.TauCetiExceptional.BridgeG2
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.HardMathSupport.Timmesfeld.LieRank

namespace G23

section Module

variable {X : Type} [Group X] (D : CFSG.AGLEmbedding.ModuleSpec X 3)

theorem elt_witness {c d : Fin D.n → ZMod 3} {g : X} (hg : g * D.elt c * g⁻¹ = D.elt d)
    (h0 : d ≠ 0) (h1 : d ≠ c) (h2 : d ≠ -c) :
    (g * D.elt c * g⁻¹) * D.elt c = D.elt c * (g * D.elt c * g⁻¹) ∧
      g * D.elt c * g⁻¹ ∉ Subgroup.zpowers (D.elt c) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hg]
  refine ⟨D.mul_comm_of_mem (D.elt_mem d) (D.elt_mem c), fun hmem => ?_⟩
  rcases mem_zpowers_cases_of_pow_three (D.pow_eq_one_of_mem (D.elt_mem c)) hmem with h | h | h
  · exact h0 (D.elt_injective (h.trans D.elt_zero.symm))
  · exact h1 (D.elt_injective h)
  · exact h2 (D.elt_injective (h.trans (D.elt_neg c).symm))

end Module

section Root

theorem nai_eq_inv : nai = na⁻¹ := by
  unfold nai na
  group

theorem nbi_eq_inv : nbi = nb⁻¹ := by
  unfold nbi nb
  group

theorem conj_aX_one : nai * aX 1 * nai⁻¹ = aX 0 := by
  have h : aX 1 = na * aX 0 * nai := rfl
  rw [h, nai_eq_inv]
  group

theorem conj_aX_three : nbi * aX 3 * nbi⁻¹ = aX 2 := by
  have h : aX 3 = nb * aX 2 * nbi := rfl
  rw [h, nbi_eq_inv]
  group

theorem conj_tA : tA * aX 1 * tA⁻¹ = (aX 1)⁻¹ ∧ tA * aX 3 * tA⁻¹ = aX 3 := by
  obtain ⟨⟨-, ta1, ta3⟩, -⟩ := torus_facts
  have e1 : tA * aX 1 = aX 1 ^ 2 * tA := valHom_injective (by
    rw [map_mul, map_mul, map_pow, valHom_aX, valHom_tA]
    exact ta1)
  have e3 : tA * aX 3 = aX 3 * tA := valHom_injective (by
    rw [map_mul, map_mul, valHom_aX, valHom_tA]
    exact ta3)
  refine ⟨?_, ?_⟩
  · rw [e1, mul_inv_cancel_right, eq_inv_iff_mul_eq_one, ← pow_succ]
    exact specA.pow (1 : Fin 4)
  · rw [e3, mul_inv_cancel_right]

@[expose] def vec4 (c₀ c₁ c₂ c₃ : ZMod 3) : Fin specA.n → ZMod 3 := ![c₀, c₁, c₂, c₃]

theorem elt_vec4 (c₀ c₁ c₂ c₃ : ZMod 3) :
    specA.elt (vec4 c₀ c₁ c₂ c₃) =
      aX 0 ^ c₀.val * aX 1 ^ c₁.val * aX 2 ^ c₂.val * aX 3 ^ c₃.val :=
  elt_four _

theorem elt_vec4_zero (s : ZMod 3) : specA.elt (vec4 s 0 0 0) = aX 0 ^ s.val := by
  rw [elt_vec4]
  simp

theorem elt_vec4_one (s : ZMod 3) : specA.elt (vec4 0 s 0 0) = aX 1 ^ s.val := by
  rw [elt_vec4]
  simp

theorem elt_vec4_two (t : ZMod 3) : specA.elt (vec4 0 0 t 0) = aX 2 ^ t.val := by
  rw [elt_vec4]
  simp

theorem elt_vec4_three (t : ZMod 3) : specA.elt (vec4 0 0 0 t) = aX 3 ^ t.val := by
  rw [elt_vec4]
  simp

theorem conj_elt_one (s : ZMod 3) :
    nai * specA.elt (vec4 0 s 0 0) * nai⁻¹ = specA.elt (vec4 s 0 0 0) := by
  rw [elt_vec4_one, elt_vec4_zero, ← conj_aX_one, conj_pow]

theorem conj_elt_three (t : ZMod 3) :
    nbi * specA.elt (vec4 0 0 0 t) * nbi⁻¹ = specA.elt (vec4 0 0 t 0) := by
  rw [elt_vec4_three, elt_vec4_two, ← conj_aX_three, conj_pow]

theorem conj_elt_torus (s t : ZMod 3) :
    tA * specA.elt (vec4 0 s 0 t) * tA⁻¹ = specA.elt (vec4 0 (-s) 0 t) := by
  have h : vec4 0 s 0 t = vec4 0 s 0 0 + vec4 0 0 0 t := by
    have h4 : (![0, s, 0, t] : Fin 4 → ZMod 3) = ![0, s, 0, 0] + ![0, 0, 0, t] := by
      ext i
      fin_cases i <;> simp
    exact h4
  have h' : vec4 0 (-s) 0 t = -vec4 0 s 0 0 + vec4 0 0 0 t := by
    have h4 : (![0, -s, 0, t] : Fin 4 → ZMod 3) = -![0, s, 0, 0] + ![0, 0, 0, t] := by
      ext i
      fin_cases i <;> simp
    exact h4
  obtain ⟨t1, t3⟩ := conj_tA
  have c1 : tA * aX 1 ^ s.val * tA⁻¹ = (aX 1 ^ s.val)⁻¹ := by
    rw [← conj_pow, t1, inv_pow]
  have c3 : tA * aX 3 ^ t.val * tA⁻¹ = aX 3 ^ t.val := by
    rw [← conj_pow, t3]
  have e : ∀ x y : RG, tA * (x * y) * tA⁻¹ = (tA * x * tA⁻¹) * (tA * y * tA⁻¹) := fun x y => by
    group
  rw [h, h', specA.elt_add, specA.elt_add, specA.elt_neg, elt_vec4_one, elt_vec4_three, e, c1,
    c3]

end Root

section Centre

theorem neg_ne_self_of_ne_zero : ∀ s : ZMod 3, s ≠ 0 → -s ≠ s := by
  decide

theorem exists_witness_of_fixed (c : Fin 4 → ZMod 3) (hA : Ma.mulVec c = c)
    (hB : Mb.mulVec c = c) (hne : specA.elt c ≠ 1) :
    ∃ g : RG, (g * specA.elt c * g⁻¹) * specA.elt c = specA.elt c * (g * specA.elt c * g⁻¹) ∧
      g * specA.elt c * g⁻¹ ∉ Subgroup.zpowers (specA.elt c) := by
  have hc0 : c 0 = 0 := by
    have h := congrFun hA 1
    simpa [Ma, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using h
  have hc2 : c 2 = 0 := by
    have h := congrFun hB 3
    simpa [Mb, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using h
  obtain ⟨s, t, rfl⟩ : ∃ s t : ZMod 3, c = ![0, s, 0, t] :=
    ⟨c 1, c 3, by
      funext i
      fin_cases i <;> simp [hc0, hc2]⟩
  have hst : s ≠ 0 ∨ t ≠ 0 := by
    by_contra h
    obtain ⟨h1, h2⟩ := not_or.mp h
    obtain rfl : s = 0 := not_not.mp h1
    obtain rfl : t = 0 := not_not.mp h2
    apply hne
    have h1 : specA.elt (vec4 0 0 0 0) = 1 := by
      rw [elt_vec4]
      simp
    exact h1
  by_cases ht : t = 0
  · subst ht
    have hs : s ≠ 0 := hst.resolve_right (not_not.mpr rfl)
    refine ⟨nai, elt_witness specA (conj_elt_one s) ?_ ?_ ?_⟩
    · intro h
      have h4 : (![s, 0, 0, 0] : Fin 4 → ZMod 3) = 0 := h
      exact hs (by simpa using congrFun h4 0)
    · intro h
      have h4 : (![s, 0, 0, 0] : Fin 4 → ZMod 3) = ![0, s, 0, 0] := h
      exact hs (by simpa using congrFun h4 0)
    · intro h
      have h4 : (![s, 0, 0, 0] : Fin 4 → ZMod 3) = -![0, s, 0, 0] := h
      exact hs (by simpa using congrFun h4 0)
  by_cases hs : s = 0
  · subst hs
    refine ⟨nbi, elt_witness specA (conj_elt_three t) ?_ ?_ ?_⟩
    · intro h
      have h4 : (![0, 0, t, 0] : Fin 4 → ZMod 3) = 0 := h
      exact ht (by simpa using congrFun h4 2)
    · intro h
      have h4 : (![0, 0, t, 0] : Fin 4 → ZMod 3) = ![0, 0, 0, t] := h
      exact ht (by simpa using congrFun h4 2)
    · intro h
      have h4 : (![0, 0, t, 0] : Fin 4 → ZMod 3) = -![0, 0, 0, t] := h
      exact ht (by simpa using congrFun h4 2)
  · refine ⟨tA, elt_witness specA (conj_elt_torus s t) ?_ ?_ ?_⟩
    · intro h
      have h4 : (![0, -s, 0, t] : Fin 4 → ZMod 3) = 0 := h
      exact ht (by simpa using congrFun h4 3)
    · intro h
      have h4 : (![0, -s, 0, t] : Fin 4 → ZMod 3) = ![0, s, 0, t] := h
      exact neg_ne_self_of_ne_zero s hs (by simpa using congrFun h4 1)
    · intro h
      have h4 : (![0, -s, 0, t] : Fin 4 → ZMod 3) = -![0, s, 0, t] := h
      exact neg_ne_self_of_ne_zero t ht (by simpa [eq_comm] using congrFun h4 3)

end Centre

theorem listRow_of_subgroup_eq {G : Type} [Group G] [Finite G] {H K : Subgroup G} (h : H = K)
    (hH : ListRow ↥H) : ListRow ↥K := by
  subst h
  exact hH

end G23

section Rows

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem listRow_rg :
    ListRow ↥RG := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hAP, hxa, hxb, hPcard, -, hPcent⟩ := exists_sylow_of_two_gens specA actsBy_gxa
    actsBy_gxb gxa_pow gxb_pow comm_xb_xa distinct_nine
  refine listRow_of_sylow_center 6 P hPcard ?_ ?_
  · rw [card_RG]
    norm_num
  · intro u huP hu3 hcen
    have hspan : u ∈ specA.span := hPcent u huP fun a ha => (hcen a (hAP ha)).symm
    obtain ⟨c, rfl⟩ := specA.exists_elt hspan
    have hA : Ma.mulVec c = c := by
      have h1 : gxa * specA.elt c * gxa⁻¹ = specA.elt c := by
        rw [hcen gxa hxa]
        group
      rw [CFSG.AGLEmbedding.R3.conj_elt specA actsBy_gxa c] at h1
      exact specA.elt_injective h1
    have hB : Mb.mulVec c = c := by
      have h1 : gxb * specA.elt c * gxb⁻¹ = specA.elt c := by
        rw [hcen gxb hxb]
        group
      rw [CFSG.AGLEmbedding.R3.conj_elt specA actsBy_gxb c] at h1
      exact specA.elt_injective h1
    have hne : specA.elt c ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hu3
      exact absurd hu3 (by norm_num)
    exact G23.exists_witness_of_fixed c hA hB hne

theorem listRow_g23
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) : ListRow S := by
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  have hK : Nat.card (ZMod 3) = q.card := by
    rw [Nat.card_zmod, TauCeti.PrimePower.card_def]
    rfl
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q g2ThreeIndex.2 (by decide) (ZMod 3) hK
  let ψ : (TauCeti.CFSGIndex.lie g2ThreeIndex).Group ≃* R3 :=
    b.symm.trans adjointQuotientEquivR3
  have h3 : ListRow R3 := G23.listRow_of_subgroup_eq (rfl : RG = R3) listRow_rg
  let e' : R3 ≃* S := (e.trans ψ).symm
  exact ListRow.of_mulEquiv (S := R3) (T := S) e' h3

theorem outerRow_g23
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) : OuterRow S := by
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  have hM : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 3 1 :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e
      (Census.chevalleyExceptionalModel_G2_three q g2ThreeIndex.2 rfl rfl)
  apply outerRow_of_not_three_dvd_outer
  rw [CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.card_outer_G2_three S hM]
  norm_num

theorem rowOf_g23 :
    RowOf (TauCeti.CFSGIndex.lie g2ThreeIndex).Group := by
  intro S _ _ _ _ ⟨e⟩
  exact ⟨listRow_g23 e, outerRow_g23 e⟩

end Rows

end CFSG.RankThree.PartTwo.Sec4.RonanK432
