module

public import CFSG.Quasithin.Vol2.KGFact4413Inv

public section

namespace CFSG.Quasithin.H13.KG4413

open CFSG.QuasithinUnique CFSG.Quasithin

variable {Y : Type} [Group Y]

theorem invOut_rel [Finite Y] {L S D : Subgroup Y} (h : CartanInv ↥L) (hSL : IsSylowTwoOf S L)
    (hDL : D ≤ L) (hDN : D ≤ Subgroup.normalizer (S : Set Y))
    (hND : L ⊓ Subgroup.normalizer (S : Set Y) ≤ D ⊔ S) (hDS : D ⊓ S = ⊥) :
    (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ∧
      ∃ w ∈ L, w ∉ Subgroup.normalizer (S : Set Y) ∧ ∀ d ∈ D, w * d * w⁻¹ = d⁻¹ := by
  set S' : Subgroup L := S.subgroupOf L with hS'
  set D' : Subgroup L := D.subgroupOf L with hD'
  have hnorm : ∀ k : ↥L, k ∈ Subgroup.normalizer (S' : Set ↥L) ↔
      (k : Y) ∈ Subgroup.normalizer (S : Set Y) :=
    E2.BorelLift.mem_normalizer_subgroupOf_iff hSL.1
  have hS'syl : IsSylowTwoOf S' ⊤ := by
    refine ⟨le_top, hSL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL.1).symm, ?_⟩
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact hSL.2.2
  have hD'N : D' ≤ Subgroup.normalizer (S' : Set ↥L) := fun d hd => (hnorm d).mpr (hDN hd)
  have hND' : Subgroup.normalizer (S' : Set ↥L) ≤ D' ⊔ S' := by
    intro y hy
    have hy' : (y : Y) ∈ ((D ⊔ S : Subgroup Y) : Set Y) := hND ⟨y.2, (hnorm y).mp hy⟩
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D S hDN] at hy'
    obtain ⟨d, hd, s, hs, hds⟩ := hy'
    have hye : y = ⟨d, hDL hd⟩ * ⟨s, hSL.1 hs⟩ := Subtype.ext hds.symm
    rw [hye]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hs)
  have hD'S' : D' ⊓ S' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyS⟩
    have : (y : Y) ∈ D ⊓ S := ⟨hyD, hyS⟩
    rw [hDS, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  obtain ⟨hab, w, hwN, hinv⟩ := h S' D' hS'syl hD'N hND' hD'S'
  refine ⟨fun a ha b hb => ?_, (w : Y), w.2, fun hw => hwN ((hnorm w).mpr hw), fun d hd => ?_⟩
  · have := hab ⟨a, hDL ha⟩ ha ⟨b, hDL hb⟩ hb
    exact congrArg Subtype.val this
  · have := hinv ⟨d, hDL hd⟩ hd
    exact congrArg Subtype.val this

theorem iSup_le_centralizer {𝒮 : Finset (Subgroup Y)} {y : Y}
    (h : ∀ L ∈ 𝒮, ∀ x ∈ L, x * y = y * x) :
    (⨆ L ∈ 𝒮, L) ≤ Subgroup.centralizer ({y} : Set Y) := by
  refine iSup₂_le fun L hL x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  exact (h L hL x hx).symm

theorem exists_mul_of_finset [DecidableEq (Subgroup Y)] (𝒮 : Finset (Subgroup Y))
    (hcomm : ∀ L ∈ 𝒮, ∀ L' ∈ 𝒮, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x)
    (w : Subgroup Y → Y) (hwL : ∀ L ∈ 𝒮, w L ∈ L) :
    ∃ x : Y, x ∈ ⨆ L ∈ 𝒮, L ∧ ∀ L ∈ 𝒮, ∀ y ∈ L, x * y * x⁻¹ = w L * y * (w L)⁻¹ := by
  induction 𝒮 using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, fun L hL => absurd hL (Finset.notMem_empty L)⟩
  | insert L₁ 𝒮 hL₁ ih =>
    have hcomm' : ∀ L ∈ 𝒮, ∀ L' ∈ 𝒮, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x :=
      fun L hL L' hL' hne => hcomm L (Finset.mem_insert_of_mem hL) L'
        (Finset.mem_insert_of_mem hL') hne
    obtain ⟨x, hx, hxact⟩ := ih hcomm' fun L hL => hwL L (Finset.mem_insert_of_mem hL)
    have hcomm₁ : ∀ L ∈ 𝒮, ∀ a ∈ L, ∀ b ∈ L₁, a * b = b * a := fun L hL a ha b hb =>
      hcomm L (Finset.mem_insert_of_mem hL) L₁ (Finset.mem_insert_self L₁ 𝒮)
        (fun h => hL₁ (h ▸ hL)) a ha b hb
    have hxc : ∀ b ∈ L₁, x * b = b * x := fun b hb =>
      Subgroup.mem_centralizer_iff.mp (iSup_le_centralizer (fun L hL a ha => hcomm₁ L hL a ha b hb)
        hx) b rfl |>.symm
    refine ⟨x * w L₁, ?_, fun L hL y hy => ?_⟩
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact (iSup₂_le fun L hL => le_iSup₂_of_le (f := fun L (_ : L ∈ insert L₁ 𝒮) => L) L
          (Finset.mem_insert_of_mem hL) le_rfl) hx
      · exact (le_iSup₂_of_le (f := fun L (_ : L ∈ insert L₁ 𝒮) => L) L₁
          (Finset.mem_insert_self L₁ 𝒮) le_rfl) (hwL L₁ (Finset.mem_insert_self L₁ 𝒮))
    · rcases Finset.mem_insert.mp hL with rfl | hL'
      · have hz : w L * y * (w L)⁻¹ ∈ L :=
          L.mul_mem (L.mul_mem (hwL L (Finset.mem_insert_self L 𝒮)) hy)
            (L.inv_mem (hwL L (Finset.mem_insert_self L 𝒮)))
        calc x * w L * y * (x * w L)⁻¹ = x * (w L * y * (w L)⁻¹) * x⁻¹ := by group
          _ = (w L * y * (w L)⁻¹) * x * x⁻¹ := by rw [hxc _ hz]
          _ = w L * y * (w L)⁻¹ := by group
      · have hwy : w L₁ * y = y * w L₁ :=
          (hcomm₁ L hL' y hy (w L₁) (hwL L₁ (Finset.mem_insert_self L₁ 𝒮))).symm
        calc x * w L₁ * y * (x * w L₁)⁻¹ = x * (w L₁ * y * (w L₁)⁻¹) * x⁻¹ := by group
          _ = x * y * x⁻¹ := by rw [hwy, mul_inv_cancel_right]
          _ = w L * y * (w L)⁻¹ := hxact L hL' y hy

theorem inv_mem_of_iSup {𝒮 : Finset (Subgroup Y)}
    (hcomm : ∀ L ∈ 𝒮, ∀ L' ∈ 𝒮, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x)
    (D : Subgroup Y → Subgroup Y) (w : Subgroup Y → Y) (hDL : ∀ L ∈ 𝒮, D L ≤ L)
    (hDab : ∀ L ∈ 𝒮, ∀ a ∈ D L, ∀ b ∈ D L, a * b = b * a)
    (hinv : ∀ L ∈ 𝒮, ∀ d ∈ D L, w L * d * (w L)⁻¹ = d⁻¹) {x : Y}
    (hx : ∀ L ∈ 𝒮, ∀ y ∈ L, x * y * x⁻¹ = w L * y * (w L)⁻¹) :
    (∀ a ∈ ⨆ L ∈ 𝒮, D L, ∀ b ∈ ⨆ L ∈ 𝒮, D L, a * b = b * a) ∧
      ∀ p ∈ ⨆ L ∈ 𝒮, D L, x * p * x⁻¹ = p⁻¹ := by
  have key : ∀ L ∈ 𝒮, ∀ L' ∈ 𝒮, D L' ≤ Subgroup.centralizer (D L : Set Y) := by
    intro L hL L' hL' e he
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    by_cases hLL : L = L'
    · subst hLL
      exact hDab L hL d hd e he
    · exact hcomm L hL L' hL' hLL d (hDL L hL hd) e (hDL L' hL' he)
  have hcen : (⨆ L ∈ 𝒮, D L) ≤ Subgroup.centralizer ((⨆ L ∈ 𝒮, D L : Subgroup Y) : Set Y) := by
    refine iSup₂_le fun L hL => ?_
    rw [Subgroup.le_centralizer_iff]
    exact iSup₂_le fun L' hL' => key L hL L' hL'
  have hab : ∀ a ∈ ⨆ L ∈ 𝒮, D L, ∀ b ∈ ⨆ L ∈ 𝒮, D L, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hcen hb) a ha)
  refine ⟨hab, ?_⟩
  let V : Subgroup Y :=
    { carrier := {p | p ∈ ⨆ L ∈ 𝒮, D L ∧ x * p * x⁻¹ = p⁻¹}
      one_mem' := ⟨Subgroup.one_mem _, by group⟩
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha.2, hb.2]
          _ = (a * b)⁻¹ := by rw [hab a ha.1 b hb.1, mul_inv_rev]⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
        calc x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
          _ = a⁻¹⁻¹ := by rw [ha.2]⟩ }
  have hV : (⨆ L ∈ 𝒮, D L) ≤ V := by
    refine iSup₂_le fun L hL d hd => ⟨?_, ?_⟩
    · exact (le_iSup₂_of_le (f := fun L (_ : L ∈ 𝒮) => D L) L hL le_rfl) hd
    · rw [hx L hL d (hDL L hL hd), hinv L hL d hd]
  exact fun p hp => (hV hp).2

end CFSG.Quasithin.H13.KG4413
