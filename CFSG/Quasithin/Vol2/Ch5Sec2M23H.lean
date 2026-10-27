module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23K
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.Quasithin.Vol2.Ch5Sec2M23Alt7
import CFSG.GH74.Orders.LieType
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Alt7Inputs

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def IsL34FieldExt (G₀ T : Subgroup G) : Prop :=
  T ≤ Subgroup.normalizer (G₀ : Set G) ∧ G₀.relIndex (G₀ ⊔ T) = 2 ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ (e : ↥G₀ ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K) (t : G)
        (A : GL (Fin 3) K) (σ : K ≃+* K), t ∈ T ∧ σ ≠ RingEquiv.refl K ∧
        ∀ x y : ↥G₀, (y : G) = t * x * t⁻¹ →
          e y = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K A
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 3 K σ (e x))

@[expose] def Stmt5_2_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T →
      LieModel ↥(m23G0 M L H B D) .PSL 3 2 2 ∧ IsL34FieldExt (m23G0 M L H B D) T

section Images

variable {M2 : Subgroup G} {π : ↥M2 →* Equiv.Perm (Fin 7)} {U : Subgroup G}

theorem card_map_mul_card_inf (hker : π.ker = U.subgroupOf M2) {X : Subgroup G} (hX : X ≤ M2) :
    Nat.card ((X.subgroupOf M2).map π) * Nat.card ↥(X ⊓ U) = Nat.card X := by
  set φ := π.domRestrict (X.subgroupOf M2) with hφ
  have h1 : Nat.card φ.range = φ.ker.index := (Subgroup.index_ker φ).symm
  rw [MonoidHom.domRestrict_range] at h1
  have h2 := Subgroup.card_mul_index φ.ker
  have hmem : ∀ k : ↥(X.subgroupOf M2), k ∈ φ.ker ↔ (((k : M2) : G) ∈ U) := by
    intro k
    rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf]
  have h3 : Nat.card φ.ker = Nat.card ↥(X ⊓ U) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(((k : X.subgroupOf M2) : M2) : G),
          Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (k : X.subgroupOf M2).2,
            (hmem k).mp k.2⟩⟩
        invFun := fun g => ⟨⟨⟨g, hX (Subgroup.mem_inf.mp g.2).1⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp g.2).1⟩,
          (hmem _).mpr (Subgroup.mem_inf.mp g.2).2⟩
        left_inv := fun k => rfl
        right_inv := fun g => rfl }
  have h4 : Nat.card ↥(X.subgroupOf M2) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  rw [h1, ← h3, mul_comm, h2, h4]

theorem mem_of_map_mem (hker : π.ker = U.subgroupOf M2) {X : Subgroup G} (hUX : U ≤ X) {g : G}
    (hg : g ∈ M2) (h : π ⟨g, hg⟩ ∈ (X.subgroupOf M2).map π) : g ∈ X := by
  obtain ⟨x, hx, hπx⟩ := h
  have hk : x⁻¹ * ⟨g, hg⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπx, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have hxX : ((x : M2) : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  have e : g = (x : G) * ((x⁻¹ * ⟨g, hg⟩ : M2) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e]
  exact X.mul_mem hxX (hUX hk)

theorem map_mem_map {X : Subgroup G} {g : G} (hg : g ∈ M2) (hgX : g ∈ X) :
    π ⟨g, hg⟩ ∈ (X.subgroupOf M2).map π :=
  ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩

end Images

theorem card_eq_card_modO2_mul (X : Subgroup G) :
    Nat.card X = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * Nat.card ↥(pCoreOf 2 X) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)]
  congr 1
  rw [pCoreOf, Subgroup.card_map_of_injective X.subtype_injective]

theorem card_eq_of_isLin2Type {X : Subgroup G} {n : ℕ} (h : IsLin2Type X n) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.card ↥(pCoreOf 2 X) := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := h
  have h1 : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hαk).toEquiv).symm.trans
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv)
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card (α := F),
    hF] at h1
  rw [card_eq_card_modO2_mul X, h1]

theorem isLin2Type_oTwoUpper_of [Finite G] (h526 : Stmt5_2_6) (h1284 : Lemma128Four)
    (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hlt : oTwoUpper H < M2)
    (hmax : quasithinIsMaximalLocal T M2) : IsLin2Type (oTwoUpper H) n := by
  have h := hyp.toHyp5_0_1
  obtain ⟨-, hL₂K, -, -, -, hcases, -, -⟩ := h526 G T M L V H B D L₂ n hyp
  unfold Cases5_2_6 at hcases
  rcases hcases with c1 | c2 | c3 | c4 | c5 | c6 | c7
  · exact c1.2.2.2.2
  · exact c2.2.2.2.2
  · exact (hsp G T M L V H B D L₂ n hyp M2 hlt hmax (Or.inl c3)).elim
  · exact (hsp G T M L V H B D L₂ n hyp M2 hlt hmax (Or.inr (Or.inl c4))).elim
  · exact (hSz G T M L V H B D L₂ n hyp c5 M2 hlt hmax).elim
  · have hQ := hU4 G T M L V H B D L₂ n hyp c6 M2 hlt hmax
    exact (hsp G T M L V H B D L₂ n hyp M2 hlt hmax (Or.inr (Or.inr ⟨c6, hQ⟩))).elim
  ·
    exfalso
    have hKloc := hyp.isLocal_oTwoUpper hL₂K
    obtain ⟨-, -, -, -, ⟨F, hFf, hFfin, hF, ⟨e⟩⟩, -⟩ := c7
    have hEq : CFSG.Open.StatedSU 3 4 F = CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 2) F := rfl
    have hSU : IsSU3 (2 ^ 2) (ModO2 (oTwoUpper H)) := by
      refine ⟨F, hFf, hFfin, by rw [hF]; norm_num, ⟨?_⟩⟩
      exact ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥(oTwoUpper H))).trans e).trans
        (MulEquiv.subgroupCongr hEq)
    have hlist : A128FourList (ModO2 (oTwoUpper H)) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨2, Or.inr hSU⟩)))))))))))))
    exact hM23.2 (h1284 G h.qtke h.simple h.nonabelian T (oTwoUpper H) hKloc hlist)

theorem eq_seven_of_two_pow_mul_eq {k m : ℕ} (h : 2 ^ k * m = 40320) (hm : ¬ 2 ∣ m) : k = 7 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  have hk : k < 16 := by
    by_contra hk
    have h16 : 2 ^ 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 16 * 1 ≤ 2 ^ k * m := Nat.mul_le_mul h16 hm0
    omega
  interval_cases k <;> omega

theorem card_cases_of_dvd_card_A7 {n i a : ℕ} (hn : 2 ≤ n)
    (ha : a = 2 ^ n * ((2 ^ n) ^ 2 - 1) * 2 ^ i) (hdvd : a ∣ 2520) :
    (n = 2 ∧ (i = 0 ∨ i = 1)) ∨ a = 504 := by
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hale : a ≤ 2520 := Nat.le_of_dvd (by norm_num) hdvd
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
  · left
    refine ⟨rfl, ?_⟩
    by_contra hi
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    rw [pow_add] at ha
    have : 240 ∣ 2520 := by
      have h' : a = 240 * 2 ^ m := by rw [ha]; ring
      exact Dvd.dvd.trans (Dvd.intro _ h'.symm) hdvd
    norm_num at this
  · right
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [ha]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [pow_add] at ha
      have : 1008 ∣ 2520 := by
        have h' : a = 1008 * 2 ^ m := by rw [ha]; ring
        exact Dvd.dvd.trans (Dvd.intro _ h'.symm) hdvd
      norm_num at this
  · exfalso
    have hw : 16 ≤ 2 ^ n := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    have hw2 : 255 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 256 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have hi : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    have : 16 * 255 * 1 ≤ a := by
      rw [ha]
      exact Nat.mul_le_mul (Nat.mul_le_mul hw hw2) hi
    omega

section Lemma519

variable [Finite G]

theorem not_le_m23Gx (h516 : Stmt5_2_16) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hker : π.ker = (pCoreOf 2 M2).subgroupOf M2)
    (hrange : π.range = alternatingGroup (Fin 7)) (hcardM2 : Nat.card M2 = 40320)
    (hU16 : Nat.card ↥(pCoreOf 2 M2) = 16) : ¬ M2 ≤ m23Gx T M L H B D := by
  intro hM2X
  obtain ⟨hG0, -, hidx, -⟩ := h516 G T M L V H B D L₂ n hyp hM23
  set G0 := m23G0 M L H B D with hG0def
  have hcardG0 : Nat.card G0 = 20160 := by
    rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hG0]
    decide
  have hsimple : IsSimpleGroup ↥G0 :=
    (CFSG.LieType.Simplicity.fam_classical_converse _
      ((CFSG.Milestones.fam_classical_model_membership_alltags _).2
        ⟨_, _, _, _, CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hG0⟩)).2.2
  have hcardGx : Nat.card (m23Gx T M L H B D) = 40320 := by
    have h := Subgroup.relIndex_mul_card (H := G0) (K := G0 ⊔ T)
    rw [hidx, inf_of_le_left le_sup_left, hcardG0] at h
    exact h.symm
  have hEq : M2 = m23Gx T M L H B D :=
    Subgroup.eq_of_le_of_card_ge hM2X (by rw [hcardGx, hcardM2])
  have hG0M2 : G0 ≤ M2 := hEq ▸ le_sup_left
  set φ : ↥G0 →* Equiv.Perm (Fin 7) := π.comp (Subgroup.inclusion hG0M2) with hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
  ·
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hb
    have h1 : Nat.card G0 = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have h2 : φ.range ≤ π.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    have h3 := Subgroup.card_le_of_le h2
    rw [← h1, hrange, card_alternatingGroup_seven, hcardG0] at h3
    norm_num at h3
  ·
    have hG0U : G0 ≤ pCoreOf 2 M2 := fun x hx => by
      have h1 : (⟨x, hx⟩ : G0) ∈ φ.ker := ht ▸ Subgroup.mem_top _
      have h2 : Subgroup.inclusion hG0M2 ⟨x, hx⟩ ∈ π.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      exact h2
    have h3 := Subgroup.card_le_of_le hG0U
    rw [hcardG0, hU16] at h3
    norm_num at h3

theorem eq_setStabIn_of_card_map (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π)
    (hcardA : Nat.card (((oTwoUpper H).subgroupOf M2).map π) = 60) :
    H = setStabIn M2 π {5, 6} ∧ ∀ σ : Equiv.Perm (Fin 7), σ ∈ (H.subgroupOf M2).map π ↔
      Equiv.Perm.sign σ = 1 ∧ ((σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  set K := oTwoUpper H with hKdef
  set U := pCoreOf 2 M2 with hUdef
  have hker : π.ker = U.subgroupOf M2 := hS.ker_eq
  have hrange : π.range = alternatingGroup (Fin 7) := hS.range_eq
  have hKM2 : K ≤ M2 := hS.K_lt.le
  have hTM2 : T ≤ M2 := hS.T_le
  have hUM2 : U ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  have hTs : IsSylowTwoOf T M2 := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM2
  have hUT : U ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTs
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hHKT : H = K ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hTH
  have hHM2 : H ≤ M2 := hHKT.le.trans (sup_le hKM2 hTM2)
  have hUH : U ≤ H := hUT.trans hTH.1
  have hmapA : ∀ X : Subgroup G, (X.subgroupOf M2).map π ≤ alternatingGroup (Fin 7) :=
    fun X => hrange ▸ Subgroup.map_le_range π _
  have hsign : ∀ (g : G) (hg : g ∈ M2), Equiv.Perm.sign (π ⟨g, hg⟩) = 1 := fun g hg =>
    Equiv.Perm.mem_alternatingGroup.mp (hrange ▸ ⟨⟨g, hg⟩, rfl⟩)
  have hcardM2 : Nat.card M2 = 40320 := by
    have h1 := card_map_mul_card_inf hker (le_refl M2)
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, hrange, card_alternatingGroup_seven,
      inf_of_le_right hUM2, hU16] at h1
    exact h1.symm
  have hcardT : Nat.card T = 128 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTs.2.1
    have h2 := Subgroup.relIndex_mul_card (H := T) (K := M2)
    rw [inf_of_le_left hTM2, hk, hcardM2, mul_comm] at h2
    rw [hk, eq_seven_of_two_pow_mul_eq h2 hTs.2.2]
    norm_num
  set P := (T.subgroupOf M2).map π with hPdef
  have hcardP : Nat.card P = 8 := by
    have h1 : Nat.card P * Nat.card ↥(T ⊓ U) = Nat.card T := card_map_mul_card_inf hker hTM2
    rw [inf_of_le_right hUT, hcardT, hU16] at h1
    omega
  set A := (K.subgroupOf M2).map π with hAdef
  set Y := (H.subgroupOf M2).map π with hYdef
  have hTN : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun t ht k hk =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hTH.1 ht)) k).mp hk
  have hYeq : Y = P ⊔ A := by
    rw [hYdef, hHKT, Subgroup.subgroupOf_sup hKM2 hTM2, Subgroup.map_sup, sup_comm]
  have hPA : P ≤ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 7))) := by
    rintro _ ⟨t, ht, rfl⟩
    have htT : ((t : M2) : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨t * k * t⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hTN _ htT _ (Subgroup.mem_subgroupOf.mp hk)
    · rintro ⟨k, hk, hka⟩
      refine ⟨t⁻¹ * k * t, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have := hTN _ (T.inv_mem htT) _ (Subgroup.mem_subgroupOf.mp hk)
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
      · rw [map_mul, map_mul, map_inv, hka]
        group
  have hAY : A ≤ Y := hYeq ▸ le_sup_right
  have hPY : P ≤ Y := hYeq ▸ le_sup_left
  have hrel : A.relIndex Y = A.relIndex P := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hPA
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hPA
    rw [hYeq]
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient P A hPA).toEquiv).symm
  have hcardY : Nat.card Y = 120 := by
    have h1 := Subgroup.relIndex_mul_card (H := A) (K := Y)
    rw [inf_of_le_left hAY, hcardA, hrel] at h1
    have h2 : A.relIndex P ∣ 8 := hcardP ▸ Subgroup.relIndex_dvd_card A P
    have h3 : 8 ∣ Nat.card Y := hcardP ▸ Subgroup.card_dvd_of_le hPY
    have h4 : Nat.card Y ∣ 2520 := by
      have := Subgroup.card_dvd_of_le (hmapA H)
      rwa [card_alternatingGroup_seven] at this
    have h5 : A.relIndex P ≤ 8 := Nat.le_of_dvd (by norm_num) h2
    rw [← h1] at h3 h4 ⊢
    interval_cases (A.relIndex P) <;> omega
  have horb : ∀ i j : Fin 7, omegaTOrbit i = omegaTOrbit j → ∃ σ ∈ Y, σ i = j := by
    intro i j hij
    obtain ⟨g, hgT, hgij⟩ := (hS.orbits i j).mpr hij
    exact ⟨π g, ⟨g, Subgroup.mem_subgroupOf.mpr (hTH.1 hgT), rfl⟩, hgij⟩
  have hYmem := mem_iff_of_card (hmapA H) hcardY horb
  have hHstab : H = setStabIn M2 π {5, 6} := by
    ext g
    rw [mem_setStabIn]
    constructor
    · intro hg
      refine ⟨hHM2 hg, ?_⟩
      rw [smul_pair_set_eq_iff]
      exact ((hYmem _).mp (map_mem_map (hHM2 hg) hg)).2
    · rintro ⟨hgM2, hgs⟩
      rw [smul_pair_set_eq_iff] at hgs
      exact mem_of_map_mem hker hUH hgM2 ((hYmem _).mpr ⟨hsign g hgM2, hgs⟩)
  exact ⟨hHstab, hYmem⟩

theorem stmt5_2_19_of
    (hQ : Stmt5_2_8_Q) (h516 : Stmt5_2_16) (h526 : Stmt5_2_6)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) :
    Stmt5_2_19 := by
  intro G _ _ T M L V H B D L₂ n M2 π hyp hM23 hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  set K := oTwoUpper H with hKdef
  set U := pCoreOf 2 M2 with hUdef
  set Q := pCoreOf 2 K with hQdef
  have hker : π.ker = U.subgroupOf M2 := hS.ker_eq
  have hrange : π.range = alternatingGroup (Fin 7) := hS.range_eq
  have hKM2 : K ≤ M2 := hS.K_lt.le
  have hTM2 : T ≤ M2 := hS.T_le
  have hUM2 : U ≤ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2
  have hTs : IsSylowTwoOf T M2 := isSylowTwoOf_of_isSylowTwo hyp.sylow hTM2
  have hUT : U ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTs
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hHKT : H = K ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hTH
  have hHM2 : H ≤ M2 := hHKT.le.trans (sup_le hKM2 hTM2)
  have hUH : U ≤ H := hUT.trans hTH.1
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hmapA : ∀ X : Subgroup G, (X.subgroupOf M2).map π ≤ alternatingGroup (Fin 7) :=
    fun X => hrange ▸ Subgroup.map_le_range π _
  have hsign : ∀ (g : G) (hg : g ∈ M2), Equiv.Perm.sign (π ⟨g, hg⟩) = 1 := fun g hg =>
    Equiv.Perm.mem_alternatingGroup.mp (hrange ▸ ⟨⟨g, hg⟩, rfl⟩)
  have hcardM2 : Nat.card M2 = 40320 := by
    have h1 := card_map_mul_card_inf hker (le_refl M2)
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, hrange, card_alternatingGroup_seven,
      inf_of_le_right hUM2, hU16] at h1
    exact h1.symm
  have hLin := isLin2Type_oTwoUpper_of h526 h1284 hSz hU4 hsp hyp hM23 hS.K_lt hS.maximal
  have hcardK := card_eq_of_isLin2Type hLin
  set A := (K.subgroupOf M2).map π with hAdef
  have hA := card_map_mul_card_inf hker hKM2
  have hKN : ∀ k ∈ K, ∀ x ∈ K ⊓ U, k * x * k⁻¹ ∈ K ⊓ U := by
    intro k hk x hx
    obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), ?_⟩
    have hUN : M2 ≤ Subgroup.normalizer (U : Set G) :=
      Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)
    exact (Subgroup.mem_normalizer_iff.mp (hUN (hKM2 hk)) x).mp hxU
  have hKUQ : K ⊓ U ≤ Q := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hKN k hk x hx, fun hx => ?_⟩
      have := hKN k⁻¹ (K.inv_mem hk) _ hx
      simpa [mul_assoc] using this
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M2).to_le inf_le_right
  set j := (K ⊓ U).relIndex Q with hjdef
  have hjq : j * Nat.card ↥(K ⊓ U) = Nat.card Q := by
    have h2 := Subgroup.relIndex_mul_card (H := K ⊓ U) (K := Q)
    rwa [inf_of_le_left hKUQ] at h2
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  obtain ⟨i, hi⟩ : ∃ i, j = 2 ^ i := by
    have hjd : j ∣ 2 ^ e := he ▸ Dvd.intro _ hjq
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hjd
    exact ⟨i, hi⟩
  have hb0 : 0 < Nat.card ↥(K ⊓ U) := Nat.card_pos
  have haA : Nat.card A = 2 ^ n * ((2 ^ n) ^ 2 - 1) * 2 ^ i := by
    have h3 : Nat.card A * Nat.card ↥(K ⊓ U) =
        2 ^ n * ((2 ^ n) ^ 2 - 1) * 2 ^ i * Nat.card ↥(K ⊓ U) := by
      rw [hA, hcardK, ← hjq, hi]
      ring
    exact Nat.eq_of_mul_eq_mul_right hb0 h3
  have hAdvd : Nat.card A ∣ 2520 := by
    have := Subgroup.card_dvd_of_le (hmapA K)
    rwa [card_alternatingGroup_seven] at this
  have hK60 : Nat.card A = 60 ∧ Q ≤ U := by
    rcases card_cases_of_dvd_card_A7 h.two_le haA hAdvd with ⟨rfl, hi01⟩ | h504
    · rcases hi01 with rfl | rfl
      ·
        refine ⟨by rw [haA]; norm_num, ?_⟩
        have hj1 : j = 1 := by rw [hi]; norm_num
        have hKUeq : K ⊓ U = Q := Subgroup.eq_of_le_of_card_ge hKUQ
          (by rw [← hjq, hj1, one_mul])
        rw [← hKUeq]
        exact inf_le_right
      ·
        exfalso
        set Bq := (Q.subgroupOf M2).map π with hBq
        have hB := card_map_mul_card_inf hker (hQK.trans hKM2)
        have hQU : Q ⊓ U = K ⊓ U :=
          le_antisymm (inf_le_inf_right _ hQK) (le_inf hKUQ inf_le_right)
        rw [hQU, ← hjq, hi] at hB
        have hB2 : Nat.card Bq = 2 := Nat.eq_of_mul_eq_mul_right hb0 (by rw [hB]; norm_num)
        obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : Bq)).mp hB2
        have hQnK : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := fun k hk x hx =>
          (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.le_normalizer.trans
              (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) hk) x).mp hx
        have hconj : ∀ a ∈ A, ∀ b ∈ Bq, a * b * a⁻¹ ∈ Bq := by
          rintro _ ⟨k, hk, rfl⟩ _ ⟨x, hx, rfl⟩
          refine ⟨k * x * k⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          exact hQnK _ (Subgroup.mem_subgroupOf.mp hk) _ (Subgroup.mem_subgroupOf.mp hx)
        have hcomm : ∀ a ∈ A, (y : Equiv.Perm (Fin 7)) * a = a * y := by
          intro a ha
          have hmem : a * (y : Equiv.Perm (Fin 7)) * a⁻¹ ∈ Bq := hconj a ha y y.2
          have hne : (⟨_, hmem⟩ : Bq) ≠ 1 := by
            intro h1
            apply hy1
            have h2 := congrArg Subtype.val h1
            simp only [OneMemClass.coe_one] at h2
            apply Subtype.ext
            simp only [OneMemClass.coe_one]
            have h3 : a * (y : Equiv.Perm (Fin 7)) = a := by
              calc a * (y : Equiv.Perm (Fin 7)) = a * (y : Equiv.Perm (Fin 7)) * a⁻¹ * a := by
                    group
                _ = a := by rw [h2, one_mul]
            exact mul_eq_left.mp h3
          have h4 := hyu _ hne
          have h5 := congrArg Subtype.val h4
          simp only at h5
          calc (y : Equiv.Perm (Fin 7)) * a = a * (y : Equiv.Perm (Fin 7)) * a⁻¹ * a := by
                rw [h5]
            _ = a * y := by group
        have hyy : (y : Equiv.Perm (Fin 7)) * y = 1 := by
          by_contra hyy
          have hmem : (y : Equiv.Perm (Fin 7)) * y ∈ Bq := Bq.mul_mem y.2 y.2
          have hne : (⟨_, hmem⟩ : Bq) ≠ 1 := fun h1 => hyy (congrArg Subtype.val h1)
          have h4 := congrArg Subtype.val (hyu _ hne)
          simp only at h4
          apply hy1
          apply Subtype.ext
          simp only [OneMemClass.coe_one]
          exact mul_eq_right.mp h4
        have hyA : (y : Equiv.Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := hmapA Q y.2
        have hy1' : (y : Equiv.Perm (Fin 7)) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
        have hle := card_le_of_le_centralizer (hmapA K) hyA hy1' hyy hcomm
        rw [haA] at hle
        norm_num at hle
    · exact absurd h504 (card_ne_504 (hmapA K))
  obtain ⟨hcardA, -⟩ := hK60
  obtain ⟨hHstab, hYmem⟩ := eq_setStabIn_of_card_map hQ hyp hM23 hS hcardA
  have hHGx : H ≤ m23Gx T M L H B D := by
    refine hHKT.le.trans (sup_le ?_ le_sup_right)
    exact (le_sup_right : K ≤ D ⊔ (sec52S M H ⊓ L) ⊔ K).trans (le_sup_right.trans le_sup_left)
  refine ⟨le_antisymm ?_ (le_inf hHGx hHM2), hHstab⟩
  intro g hg
  obtain ⟨-, hgM2⟩ := Subgroup.mem_inf.mp hg
  set X := m23Gx T M L H B D ⊓ M2 with hXdef
  have hHX : H ≤ X := le_inf hHGx hHM2
  have hZ : ∀ σ : Equiv.Perm (Fin 7), Equiv.Perm.sign σ = 1 → Pres56 σ →
      σ ∈ (X.subgroupOf M2).map π := by
    intro σ h1 h2
    obtain ⟨m, hm, rfl⟩ := (hYmem σ).mpr ⟨h1, h2⟩
    exact ⟨m, Subgroup.mem_subgroupOf.mpr (hHX (Subgroup.mem_subgroupOf.mp hm)), rfl⟩
  rcases pres56_or_eq_alt (hmapA X) hZ with hp | hall
  · exact mem_of_map_mem hker hUH hgM2
      ((hYmem _).mpr ⟨hsign g hgM2, hp _ (map_mem_map hgM2 hg)⟩)
  · exfalso
    refine not_le_m23Gx h516 hyp hM23 hker hrange hcardM2 hU16 fun m hm => ?_
    have hmX := mem_of_map_mem hker (hUH.trans hHX) hm (hall _ (hrange ▸ ⟨⟨m, hm⟩, rfl⟩))
    exact (Subgroup.mem_inf.mp hmX).1

end Lemma519

end CFSG.Quasithin.H13
