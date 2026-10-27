module

public import CFSG.Quasithin.Background.SmithC27RTypeGen
public import CFSG.Quasithin.Background.SmithC27AltSetup
public import CFSG.Quasithin.Background.C124AsmStmt

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem center_alternatingGroup_eq_bot' {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) :
    Subgroup.center (alternatingGroup (Fin m)) = ⊥ := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := C124.alt_noncomm hm
    have ha : a ∈ Subgroup.center (alternatingGroup (Fin m)) := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem card_alternatingGroup_fin' (m : ℕ) (hm : 2 ≤ m) :
    Nat.card ↥(alternatingGroup (Fin m)) = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

variable {H R M K V : Subgroup G}

theorem card_autOn_eq_360 (hs : StarHyp R K V) (hZ : Subgroup.center ↥(autOn K V) = ⊥)
    (hK : IsAltBlockType K 6 ∨ IsHatA6Block K) : Nat.card ↥(autOn K V) = 360 := by
  have key := hs.card_autOn_mul_card_center hZ
  rcases hK with ⟨-, α, hα, hαk, -⟩ | ⟨-, ⟨-, hc3, ⟨e⟩⟩, -⟩
  · let e6 : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(alternatingGroup (Fin 6)) :=
      (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    have hc : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
      have h1 := map_center_of_mulEquiv e6
      rw [center_alternatingGroup_eq_bot' (Or.inr (Or.inl rfl))] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e6.injective).1 h1
    rw [hc, Subgroup.card_bot, mul_one, Nat.card_congr e6.toEquiv,
      card_alternatingGroup_fin' 6 (by norm_num)] at key
    rw [key]
    decide
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin' 6 (by norm_num), hc3] at h1
    rw [hc3, h1] at key
    have h360 : (Nat.factorial 6 / 2) = 360 := by decide
    rw [h360] at key
    omega

theorem false_of_autOn_equiv_alt (hC124 : C124StatementSQTK (G := G)) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hnchi : ¬ IsChiBlock2 H K) (hnexc : ¬ IsExcA7Block K) {m : ℕ}
    (hm : m = 5 ∨ m = 7) (e : ↥(autOn K V) ≃* ↥(alternatingGroup (Fin m))) : False := by
  have hZ : Subgroup.center ↥(autOn K V) = ⊥ := by
    have h1 := map_center_of_mulEquiv e
    rw [center_alternatingGroup_eq_bot' (hm.elim Or.inl (fun h7 => Or.inr (Or.inr h7)))] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  have hKV := hs.K_le_normalizer_V
  let φ : ↥K →* ↥(alternatingGroup (Fin m)) :=
    e.toMonoidHom.comp (InternalSec.autOnHom hKV)
  have hφs : Function.Surjective φ :=
    e.surjective.comp (InternalSec.autOnHom_surjective hKV)
  have hker : φ.ker = (oTwoZIn K).subgroupOf K := by
    ext l
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker,
      InternalSec.mem_ker_autOnHom]
    exact ⟨fun hl => hs.inf_centralizer_le ⟨l.2, hl⟩, fun hl => hs.oTwoZIn_le_centralizer hZ hl⟩
  have halt : IsAltQuotient K (oTwoZIn K) m := ⟨φ, hφs, hker⟩
  obtain ⟨T, hT, hRT⟩ := hs.exists_sylow
  have hm' : m = 5 ∨ m = 7 ∨
      (m = 6 ∧ R ≤ K ⊔ ((K ⊔ R) ⊓ Subgroup.centralizer (V : Set G))) ∨
      (m = 6 ∧ Nat.card ↥(autOn R V) = 2) :=
    hm.elim Or.inl (fun h7 => Or.inr (Or.inl h7))
  have hcard : Nat.card ↥(autOn K V) = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin' m (by omega)]
  rcases hC124 (K ⊔ R) T V K R m h.charTwo_sup h.hypC23_sup.sqtk hs.red hT
      (hs.prod_of_le hRT) h.mem_cComp_sup h.charTwo hs.commutator_ne_bot halt
      h.pCoreOf_sup_le hRT hm' with
    ⟨C, hC1, hCB, hchar, hXC⟩ | hchi | ⟨-, hexc | h6⟩
  · exact not_le_normalizer_of_char_baum h hC1 hCB hchar hXC
  · apply hnchi
    have hKH : K ≤ H := le_of_mem_cComp h.comp
    refine ⟨⟨hchi.1.1, hKH, (isSubnormal_iff_subgroupOf hKH).mp
      (subnormal_of_mem_cComp h.comp)⟩, ?_⟩
    rcases hchi.2 with h1 | ⟨k, hk, -, hA⟩
    · exact Or.inl h1
    · exact Or.inr ⟨k, hk, hA⟩
  · exact hnexc hexc
  · have h360 := card_autOn_eq_360 hs hZ h6
    rw [hcard] at h360
    rcases hm with rfl | rfl <;> revert h360 <;> decide

end CFSG.Quasithin.SmithC27
