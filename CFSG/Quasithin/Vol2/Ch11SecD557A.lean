module

public import CFSG.Quasithin.Vol2.Ch11SecD557NatB
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Vol2.Ch11SecDNat

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem pCoreOf_le_centralizer_fsuV (h : Hyp11 G T L I n) :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨-, -, hZ⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥(L ⊔ T)) 2
  rintro _ ⟨o, ho, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨x, hx, rfl⟩ := SecA.fsuV_le_reducedAggregate h hv
  obtain ⟨-, h2, -⟩ := BlueprintB2.mem_centerTorsion_iff.mp (hZ hx)
  have ho' : o ∈ CFSG.pCore 2 ↥(L ⊔ T) := by assumption
  exact (congrArg Subtype.val (h2 o ho')).symm

theorem fsuV_eq_conjClosure (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : fsuV T I = conjClosure V₁ L := by
  obtain ⟨X, hX⟩ := exists_isCartanX h
  have htr := (h1141 G T L I n V₁ X h hV₁ hX).1.2
  have hLV := SecA.L_le_normalizer_fsuV h
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  refine le_antisymm (fun v hv => ?_) (conjClosure_le fun l hl w hw =>
    (Subgroup.mem_normalizer_iff.mp (hLV hl) w).mp (hV₁V hw))
  by_cases hv1 : v = 1
  · rw [hv1]
    exact Subgroup.one_mem _
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (SecA.IsVi.ne_bot h hV₁ le_rfl)
  have hw1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨l, hl, hlw⟩ := htr (x : G) (hV₁V x.2) v hv hw1 hv1
  rw [← hlw]
  exact mem_conjClosure hl x.2

theorem not_le_pCoreOf_of_not_comm (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hU : ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))) :
    ¬ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 (L ⊔ T) := by
  intro hle
  apply hU
  set U := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hUdef
  have hUC : U ≤ Subgroup.centralizer (fsuV T I : Set G) :=
    hle.trans (pCoreOf_le_centralizer_fsuV h)
  have hUN : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_conjClosure _ _
  have hUU : U ≤ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine conjClosure_le fun g hg v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (hUN (Subgroup.inv_mem _ hg)) u).mp hu
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp (hUC hu') v hv
    calc u * (g * v * g⁻¹) = g * (g⁻¹ * u * g) * v * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * u * g)) * g⁻¹ := by rw [mul_assoc g, hc.symm, ← mul_assoc]
      _ = g * v * g⁻¹ * u := by group
  exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp (hUU b.2) a a.2)⟩⟩

theorem almostSpecialL3Hyp_of (hNat : NatV3Fact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (he : Nonempty (↥(autOn L (fsuV T I)) ≃* SL(3, K)))
    (π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I)))
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π)
    (hU : ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))) :
    AlmostSpecialL3Hyp n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL3 : KindSL3 L (fsuV T I) n := ⟨K, inferInstance, inferInstance, hK, he⟩
  obtain ⟨V₃, hV₃, -⟩ := (h1110 G T L I n h).1 3 (by norm_num) le_rfl
  have hV₃eq : V₃ = fsuV T I := ((h1110 G T L I n h).2.2 V₁ V₃ hV₁ hV₃).1 hSL3
  have hset := natSetting11_of h1102 h1141 h hV₁
  obtain ⟨hV₁₃, F, _, _, -, hnat⟩ := hNat G T L I n V₁ V₃ hset (Or.inl hSL3) hV₁ hV₃
  rw [hV₃eq] at hnat hV₁₃
  have hTN : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hLV := SecA.L_le_normalizer_fsuV h
  have hlOne : LOf L V₁ ≤ lOne L V₁ := by
    have h1 : oTwoUpper (LOf L V₁) = LOf L V₁ :=
      C2Nine.oTwoUpper_eq_of_perfect (perfectCore_perfect _)
    rw [← h1]
    exact oTwoUpper_mono (perfectCore_le _)
  have hlOneL : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  have hlt : V₁ < fsuV T I := by
    refine lt_of_le_of_ne hV₁₃ fun heq => ?_
    obtain ⟨-, -, -, -, β, hβ, hβker, -⟩ := hnat
    obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd (Pi.single 0 1))
    have h1 : β v = 1 := by
      rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf, heq]
      exact v.2
    rw [h1] at hv
    have := congrArg (fun x : Multiplicative (Fin 2 → F) => Multiplicative.toAdd x 0) hv
    simp at this
  have hV₁O : V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      (h.fsu.sylow.1.to_le ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)))
  have hO2ne : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := fun hb =>
    SecA.IsVi.ne_bot h hV₁ le_rfl (le_bot_iff.mp (hb ▸ hV₁O))
  refine ⟨⟨SecA.isElemAbelian_fsuV h, SecA.IsVi.ne_bot h hV₁ le_rfl, hV₁₃,
    (C2Nine.oTwoUpper_eq_of_perfect hset.perfect).symm, SecA.fsuV_le_T h, hTN,
    SecA.T_le_normalizer_fsuV T I, h.normal,
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right, le_rfl,
    sup_le (hlOneL.trans inf_le_right) hTN, isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN,
    charTwo_of_inH h.fsu.qtke.2.1 (h.fsu.sylow.1.toSylow h.fsu.sylow.2)
      (H := Subgroup.normalizer (V₁ : Set G))
      (by rw [IsPGroup.toSylow_coe]; exact ⟨hTN, hO2ne⟩), ?_⟩, by have := h.one_lt; omega,
    fsuV_eq_conjClosure h1141 h hV₁, isNaturalSL3Module_of h1102 h1141 h hV₁ hK he π hπ,
    not_le_pCoreOf_of_not_comm h hU⟩
  refine ⟨hlt, sup_le ((hlOneL.trans inf_le_left).trans hLV) (SecA.T_le_normalizer_fsuV T I),
    sup_le (hlOneL.trans inf_le_right) hTN, fun W hV₁W hWV hWN => ?_⟩
  exact isNaturalSection_irred hnat hV₁W hWV (hlOne.trans (le_sup_left.trans hWN))

end CFSG.Quasithin.Vol2.Ch11.SecD
