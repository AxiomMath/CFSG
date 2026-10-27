module

public import CFSG.Quasithin.H13.L32ASk2
public import CFSG.Quasithin.H13.L32A773o

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Hyp147

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem setting147_hz (h : Hyp147 G T L V) (h12213 : Stmt12_2_13) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) : Setting147 G T L V (L32A.hz T V) := by
  have hT := h.isTSub_V1 hMod
  obtain ⟨-, hV1c, hTN⟩ := hT
  have hV1 : Nat.card (fsuV1 T V) = 2 := by rw [hV1c, pow_one]
  have hHN : L32A.hz T V = Subgroup.normalizer (fsuV1 T V : Set G) :=
    (L32A.normalizer_eq_centralizer_of_card_two hV1).symm
  refine ⟨h, ⟨⟨?_, ?_⟩, hHN.le, ?_⟩⟩
  · rw [hHN]
    exact sup_le ((oTwoUpper_le _).trans inf_le_right) hTN
  · have hp : IsPGroup 2 (fsuV1 T V) := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hV1)
    have hle : fsuV1 T V ≤ pCoreOf 2 (L32A.hz T V) :=
      le_pCoreOf_of_le_normalizer 2 (by rw [hHN]; exact Subgroup.le_normalizer) hHN.le hp
    intro hbot
    have h1 : fsuV1 T V = ⊥ := le_bot_iff.mp (hbot ▸ hle)
    rw [h1, Subgroup.card_bot] at hV1
    exact absurd hV1 (by norm_num)
  · rw [hHN]
    exact lemma12_8_3_four h12213 (h.hyp1281One h13322 hMod) (h.isTSub_V1 hMod)

end Hyp147

namespace L32A

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_cComp_eq {H K : Subgroup G} (hC : cComp H = {K}) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  have hK : K ∈ cComp H := by rw [hC]; rfl
  have h1 := cComp_map_mulEquiv (MulAut.conj g) hK
  have h2 : H.map (MulAut.conj g).toMonoidHom = H :=
    conjSub_eq_self_iff.mpr (Subgroup.le_normalizer hg)
  rw [h2, hC] at h1
  exact conjSub_eq_self_iff.mp h1

theorem oTwoUpper_eq_of_cComp_eq {H K T : Subgroup G} (hC : cComp H = {K}) (hHK : H = K ⊔ T)
    (hT : IsPGroup 2 T) : oTwoUpper H = K := by
  have hK : K ∈ cComp H := by rw [hC]; rfl
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    (hHK ▸ le_sup_right).trans (le_normalizer_of_cComp_eq hC)
  apply le_antisymm
  · rw [hHK]
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨a, ha, p, hp, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTK).1 hx
    obtain ⟨k, hk⟩ := hT ⟨p, hp⟩
    have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq ha (hTK hp) (2 ^ k)
    exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩
  · calc K = oTwoUpper K := (oTwoUpper_eq_of_perfect_F9 hK.2.1).symm
      _ ≤ oTwoUpper H := oTwoUpper_mono (hHK ▸ le_sup_left)

omit [Finite G] in
theorem le_normalizer_of_comm {U X Y : Subgroup G} (hab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hXU : X ≤ U) (hYU : Y ≤ U) : X ≤ Subgroup.normalizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hab x (hXU hx) y (hYU hy), mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 : x * y * x⁻¹ ∈ U := hYU hy
    have hyU : y ∈ U := by
      have := U.mul_mem (U.mul_mem (U.inv_mem (hXU hx)) h1) (hXU hx)
      simpa [mul_assoc] using this
    rwa [hab x (hXU hx) y hyU, mul_inv_cancel_right] at hy

omit [Finite G] in
theorem isIndecOnSection_of_isL24Section {K U U₀ D : Subgroup G} (hL24 : IsL24Section K U U₀)
    (hDU₀ : D ≤ U₀) (hU₀U : U₀ ≤ U) (hKU₀ : K ≤ Subgroup.normalizer (U₀ : Set G))
    (hc : ∀ c ∈ U₀, ∀ k ∈ K, k * c * k⁻¹ * c⁻¹ ∈ D)
    (hab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hUK : U = ⁅U, K⁆) : IsIndecOnSection K U D := by
  have hlt : ¬ U ≤ U₀ := by
    intro hle
    obtain ⟨-, π, β, -, -, hβs, hβk, -⟩ := hL24
    obtain ⟨x, hx⟩ := hβs (Multiplicative.ofAdd (fun _ => (1 : RuType.F4)))
    have h1 : x ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact hle x.2
    rw [MonoidHom.mem_ker, hx] at h1
    have h2 := congrArg (fun y : Multiplicative (Fin 2 → RuType.F4) => Multiplicative.toAdd y 0) h1
    simp at h2
  have key : ∀ A B : Subgroup G, D ≤ A → A ≤ U → B ≤ U →
      K ≤ Subgroup.normalizer (A : Set G) → K ≤ Subgroup.normalizer (B : Set G) →
      A ⊓ B = D → A ⊔ B = U → A ⊔ U₀ = U → B = D := by
    intro A B hDA hAU hBU hKA hKB hAB hABs hAU₀
    have hBK : ∀ b ∈ B, ∀ k ∈ K, k * b * k⁻¹ * b⁻¹ ∈ D := by
      intro b hb k hk
      have hbU : b ∈ ((A ⊔ U₀ : Subgroup G) : Set G) := by rw [hAU₀]; exact hBU hb
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_of_comm hab hAU hU₀U)]
        at hbU
      obtain ⟨a, ha, c, hcU, rfl⟩ := hbU
      have hka : k * a * k⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hKA hk) a).mp ha
      have hA : k * (a * c) * k⁻¹ * (a * c)⁻¹ ∈ A := by
        have e : k * (a * c) * k⁻¹ * (a * c)⁻¹ =
            (k * a * k⁻¹) * (k * c * k⁻¹ * c⁻¹) * a⁻¹ := by group
        rw [e]
        exact A.mul_mem (A.mul_mem hka (hDA (hc c hcU k hk))) (A.inv_mem ha)
      have hB : k * (a * c) * k⁻¹ * (a * c)⁻¹ ∈ B :=
        B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKB hk) _).mp hb) (B.inv_mem hb)
      rw [← hAB]
      exact ⟨hA, hB⟩
    have hUKA : ⁅U, K⁆ ≤ A := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      have hu' : u ∈ ((A ⊔ B : Subgroup G) : Set G) := by rw [hABs]; exact hu
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_of_comm hab hAU hBU)]
        at hu'
      obtain ⟨a, ha, b, hb, rfl⟩ := hu'
      have hka : k * a⁻¹ * k⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hKA hk) a⁻¹).mp (A.inv_mem ha)
      have hbk : b * k * b⁻¹ * k⁻¹ ∈ A := by
        have h1 := hBK b⁻¹ (B.inv_mem hb) k hk
        have hxU : k * b⁻¹ * k⁻¹ * b⁻¹⁻¹ ∈ U := hU₀U (hDU₀ h1)
        have e : b * k * b⁻¹ * k⁻¹ = b * (k * b⁻¹ * k⁻¹ * b⁻¹⁻¹) * b⁻¹ := by group
        rw [e, hab b (hBU hb) _ hxU, mul_inv_cancel_right]
        exact hDA h1
      have e : ⁅a * b, k⁆ = a * (b * k * b⁻¹ * k⁻¹) * (k * a⁻¹ * k⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact A.mul_mem (A.mul_mem ha hbk) hka
    have hUA : U ≤ A := hUK ▸ hUKA
    rw [← hAB]
    exact le_antisymm (le_inf (hBU.trans hUA) le_rfl) inf_le_right
  intro A B hDA hDB hAU hBU hKA hKB hAB hABs
  rcases hL24.eq_or_eq (D := A ⊔ U₀) le_sup_right (sup_le hAU hU₀U)
    (le_normalizer_sup_of hKA hKU₀) with hA | hA
  · rcases hL24.eq_or_eq (D := B ⊔ U₀) le_sup_right (sup_le hBU hU₀U)
      (le_normalizer_sup_of hKB hKU₀) with hB | hB
    · exfalso
      apply hlt
      rw [← hABs]
      exact sup_le (hA ▸ le_sup_left) (hB ▸ le_sup_left)
    · exact Or.inl (key B A hDB hBU hAU hKB hKA (by rw [inf_comm]; exact hAB)
        (by rw [sup_comm]; exact hABs) hB)
  · exact Or.inr (key A B hDA hAU hBU hKA hKB hAB hABs hA)

theorem isLieChar2_two_of_isAlt_five {X : Type} [Group X]
    (h : IsAlt 5 X) : A315.IsLieChar2 2 (X ⧸ Subgroup.center X) := by
  obtain ⟨e⟩ := h
  have hs : IsSimpleGroup X :=
    (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  have hc : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht
    · exact hb
    · exfalso
      let a : ↥(alternatingGroup (Fin 5)) :=
        ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
      let b : ↥(alternatingGroup (Fin 5)) :=
        ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
      have hab : a * b ≠ b * a := by decide
      have hz : e.symm a ∈ Subgroup.center X := by rw [ht]; trivial
      have := Subgroup.mem_center_iff.mp hz (e.symm b)
      apply hab
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact this.symm
  refine Or.inl (CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _
    ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e)⟩)

end L32A

theorem L32A.thm14_7_63_of (h12213 : Stmt12_2_13)
    (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule) (h40 : Thm14_7_40) (h48 : Lemma14_7_48)
    (h52 : Thm14_7_52) (h53 : Thm14_7_53) : Thm14_7_63 := by
  intro G _ _ T L V h
  have S := h.setting147_hz h12213 h13322 hMod
  obtain ⟨K, hC, hKT, hUK⟩ := h48 G T L V _ S
  have hK : K ∈ cComp (L32A.hz T V) := by rw [hC]; rfl
  obtain ⟨-, -, huniq, hU, hA5U3⟩ := h52 G T L V _ S K hK
  have hA5 : IsAlt 5 (L32A.cStar K) := hA5U3.resolve_right (h53 G T L V _ S K hK)
  have hTH : T ≤ L32A.hz T V := by rw [hKT]; exact le_sup_right
  have hL1H : L32A.l1 T L V ≤ L32A.hz T V := le_sup_left.trans S.hz.1.1
  have hKH : K ≤ L32A.hz T V := by rw [hKT]; exact le_sup_left
  have hH : L32A.hz T V = K ⊔ (L32A.l1 T L V ⊔ T) := by
    refine le_antisymm ?_ (sup_le hKH (sup_le hL1H hTH))
    rw [hKT]
    exact sup_le_sup_left le_sup_right K
  obtain ⟨hS5, hL24⟩ := h40 G T L V _ S K hK hH 2 (by norm_num)
    (L32A.isLieChar2_two_of_isAlt_five hA5)
  have hTp : IsPGroup 2 T := h.fsu.sylow.1
  have hkz : L32A.kz T V = K := L32A.oTwoUpper_eq_of_cComp_eq hC hKT hTp
  rw [hU] at hL24 hUK
  rw [← hkz] at hL24 hUK hK
  refine ⟨⟨S.hz.1, S.hz.2.2, S.hz.2.1⟩, fun H hH' => huniq H ⟨h, ⟨hH'.1, hH'.2.2, hH'.2.1⟩⟩,
    by rw [hkz]; exact hKT, hK, hS5, ?_, ⟨L32A.u0 T V, fun u => L32A.mem_u0_iff h hMod, hL24⟩⟩
  have hV1U : fsuV1 T V ≤ L32A.u0 T V := L32A.fsuV1_le_u0 h hMod
  have hUe := L32A.isElemAbelian_fsuU_of h hMod
  refine L32A.isIndecOnSection_of_isL24Section hL24 hV1U (centralizerMod_le_left _ _ _)
    ((oTwoUpper_le _).trans (L32A.hz_le_normalizer_u0 h hMod)) (fun c hc k hk => ?_)
    (fun x hx y hy => F7.isElemAbelian_comm hUe hx hy) hUK
  have h1 := ((L32A.mem_u0_iff h hMod).mp hc).2 k hk
  exact h1

end CFSG.Quasithin.H13
