module

public import CFSG.LocalAnalysis.WeakClosure81.W16QCfg
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace KTCfg16

variable {U V₀ V I K T Q : Subgroup G}

private lemma w16q_mem_sup_of_comm {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hA : A ≤ Subgroup.centralizer (B : Set G) :=
    fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm
  have hN : A ≤ Subgroup.normalizer (B : Set G) :=
    le_trans hA (Subgroup.centralizer_le_normalizer (B : Set G))
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right A B hN
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← hcoe]
    exact hx
  exact Set.mem_mul.mp hx'

private lemma w16q_commutator_mem_centralizer (h : KTCfg16 U V₀ V I K T Q) {x y : G}
    (hx : x ∈ Q) (hy : y ∈ Q) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  have hI_le_centQ : I ≤ Subgroup.centralizer (Q : Set G) := fun i hi =>
    Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (h.Q_le hq) i hi).symm
  have hKQ_le_I : ⁅K, Q⁆ ≤ I :=
    Subgroup.commutator_le.mpr fun k hk q hq => h.comm_mem q hq k hk
  have hQK_le_I : ⁅Q, K⁆ ≤ I := by
    rw [Subgroup.commutator_comm Q K]
    exact hKQ_le_I
  have h1 : ⁅⁅Q, K⁆, Q⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hQK_le_I.trans hI_le_centQ)
  have h2 : ⁅⁅K, Q⁆, Q⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hKQ_le_I.trans hI_le_centQ)
  have h3 : ⁅⁅Q, Q⁆, K⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hQQ_le : ⁅Q, Q⁆ ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hmem : ⁅x, y⁆ ∈ Subgroup.centralizer (K : Set G) :=
    hQQ_le (Subgroup.commutator_mem_commutator hx hy)
  simpa only [commutatorElement_def] using hmem

theorem comm_of_mem_inf (h : KTCfg16 U V₀ V I K T Q) {A : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x a v : G} (hx : x ∈ A ⊓ Q) (ha : a ∈ A)
    (hv : v ∈ V) (hva : v⁻¹ * a ∈ Q) : x * v = v * x := by
  have hxA : x ∈ A := hx.1
  have hxQ : x ∈ Q := hx.2
  have hxT : x ∈ T := h.Q_le_T hxQ
  set y : G := v⁻¹ * a with hq_def
  have hyQ : y ∈ Q := hva
  have havy : v * y = a := by rw [hq_def]; group
  have hc1V₀ : x * v * x⁻¹ * v⁻¹ ∈ V₀ := h.comm_mem_V₀ x hxT v hv
  have hc2CK : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    w16q_commutator_mem_centralizer h hxQ hyQ
  have hxa : x * a = a * x := hA x hxA a ha
  have hmain : (x * v * x⁻¹ * v⁻¹) * v * (x * y * x⁻¹ * y⁻¹) = v := by
    have h := hxa
    rw [← havy] at h
    have h' := congrArg (fun z => z * x⁻¹ * y⁻¹) h
    have e2 : x * v * y * x⁻¹ * y⁻¹ = v := by simpa [mul_assoc] using h'
    have e1 : (x * v * x⁻¹ * v⁻¹) * v * (x * y * x⁻¹ * y⁻¹) =
        x * v * y * x⁻¹ * y⁻¹ := by group
    rw [e1, e2]
  have hv_c2 : v * (x * y * x⁻¹ * y⁻¹) = (x * v * x⁻¹ * v⁻¹)⁻¹ * v := by
    have h' := congrArg (fun z => (x * v * x⁻¹ * v⁻¹)⁻¹ * z) hmain
    simpa [mul_assoc] using h'
  have hc2 : x * y * x⁻¹ * y⁻¹ = v⁻¹ * (x * v * x⁻¹ * v⁻¹)⁻¹ * v := by
    have h' := congrArg (fun z => v⁻¹ * z) hv_c2
    simpa [mul_assoc] using h'
  have hc1V : x * v * x⁻¹ * v⁻¹ ∈ V := h.le_V (Subgroup.mem_sup_right hc1V₀)
  have hc1comm : v * (x * v * x⁻¹ * v⁻¹) = (x * v * x⁻¹ * v⁻¹) * v :=
    h.comm_V v hv (x * v * x⁻¹ * v⁻¹) hc1V
  have hc1inv : v⁻¹ * (x * v * x⁻¹ * v⁻¹)⁻¹ * v = (x * v * x⁻¹ * v⁻¹)⁻¹ := by
    have hcomm_inv : v⁻¹ * (x * v * x⁻¹ * v⁻¹)⁻¹ =
        (x * v * x⁻¹ * v⁻¹)⁻¹ * v⁻¹ := by
      have h' := congrArg Inv.inv hc1comm
      simpa [mul_inv_rev] using h'.symm
    calc
      v⁻¹ * (x * v * x⁻¹ * v⁻¹)⁻¹ * v
          = (v⁻¹ * (x * v * x⁻¹ * v⁻¹)⁻¹) * v := rfl
      _ = ((x * v * x⁻¹ * v⁻¹)⁻¹ * v⁻¹) * v := by rw [hcomm_inv]
      _ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by group
  have hc2c1 : x * y * x⁻¹ * y⁻¹ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by
    rw [hc2, hc1inv]
  have hc1CK : x * v * x⁻¹ * v⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    have h' : (x * y * x⁻¹ * y⁻¹)⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.centralizer (K : Set G)).inv_mem hc2CK
    simpa [hc2c1] using h'
  have hc1_bot : x * v * x⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h.inf_eq_bot]
    exact ⟨hc1V₀, hc1CK⟩
  have hc1_one : x * v * x⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.mp hc1_bot
  have hxv : x * v * x⁻¹ = v := by
    have h' := congrArg (fun z => z * v) hc1_one
    simpa [mul_assoc] using h'
  calc
    x * v = (x * v * x⁻¹) * x := by group
    _ = v * x := by rw [hxv]

theorem card_mul_card_eq (h : KTCfg16 U V₀ V I K T Q) :
    Nat.card T * Nat.card ↥(U ⊔ V₀) = Nat.card V * Nat.card Q := by
  have hVnorm : V ≤ Subgroup.normalizer (Q : Set G) := h.V_le_T.trans h.T_le
  have hVQ : V ⊔ Q = T := by
    apply le_antisymm
    · exact sup_le h.V_le_T h.Q_le_T
    · intro t ht
      obtain ⟨v, hv, hvq⟩ := h.exists_mul t ht
      have ht_eq : t = v * (v⁻¹ * t) := by group
      rw [ht_eq]
      exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hvq)
  have hVinfQ : V ⊓ Q = U ⊔ V₀ := by
    apply le_antisymm
    · exact h.inf_le
    · exact le_inf h.le_V (h.le_I.trans h.I_le_Q)
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hVnorm
  rw [hVQ, hVinfQ] at hprod
  exact hprod

theorem card_mul_le_of_offender (h : KTCfg16 U V₀ V I K T Q) {A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 T) (hAQ : ¬ A ≤ Q) :
    Nat.card I * Nat.card ↥(A ⊓ Q) ≤ Nat.card A * Nat.card ↥(U ⊔ V₀) := by
  obtain ⟨hA_le_T, hA_el, hA_card⟩ := mem_elemFamilyIn.mp hA
  have hA_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    (CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff.mp hA_el).1
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAQ
  have haT : a ∈ T := hA_le_T haA
  obtain ⟨v, hvV, hvqQ⟩ := h.exists_mul a haT
  set q : G := v⁻¹ * a with hq_def
  have hvq : v * q = a := by rw [hq_def]; group
  have hqQ : q ∈ Q := hvqQ
  have hv_not : v ∉ U ⊔ V₀ := by
    intro hvUV
    have hvQ : v ∈ Q := (h.le_I.trans h.I_le_Q) hvUV
    have haQ' : a ∈ Q := by
      rw [← hvq]
      exact Q.mul_mem hvQ hqQ
    exact haQ haQ'
  have hAI_le : A ⊓ I ≤ U ⊔ V₀ := by
    intro w hw
    have hwA : w ∈ A := hw.1
    have hwI : w ∈ I := hw.2
    have hwa : w * a = a * w := hA_comm w hwA a haA
    have hwq : w * q = q * w := Subgroup.mem_centralizer_iff.mp (h.Q_le hqQ) w hwI
    have hwv : w * v = v * w := by
      have h1 : w * v * q = v * w * q := by
        calc
          w * v * q = w * (v * q) := by group
          _ = w * a := by rw [hvq]
          _ = a * w := hwa
          _ = (v * q) * w := by rw [hvq]
          _ = v * (q * w) := by group
          _ = v * (w * q) := by rw [← hwq]
          _ = v * w * q := by group
      exact mul_right_cancel h1
    exact h.mem_of_comm v hvV hv_not w hwI hwv.symm
  have hAI_card : Nat.card ↥(A ⊓ I) ≤ Nat.card ↥(U ⊔ V₀) := Subgroup.card_le_of_le hAI_le
  have hAQ_el : IsElementaryAbelian 2 ↥(A ⊓ Q) :=
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_of_le inf_le_left hA_el
  have hI_el : IsElementaryAbelian 2 I :=
    CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff.mpr
      ⟨h.comm_I, fun x hx => by simpa [pow_two] using h.sq_I x hx⟩
  have hI_le_cent : I ≤ Subgroup.centralizer ((A ⊓ Q : Subgroup G) : Set G) := by
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (h.Q_le hx.2) i hi).symm
  have hB_el : IsElementaryAbelian 2 ↥((A ⊓ Q) ⊔ I) :=
    isElementaryAbelian_sup_of_le_centralizer hAQ_el hI_el hI_le_cent
  have hB_le_T : (A ⊓ Q) ⊔ I ≤ T :=
    sup_le (le_trans inf_le_left hA_le_T) (le_trans h.I_le_Q h.Q_le_T)
  have hB_card : Nat.card ↥((A ⊓ Q) ⊔ I) ≤ Nat.card A := by
    have h' := card_le_pow_pRank_of_le hB_le_T hB_el
    simpa [← hA_card] using h'
  have hcomm : ∀ x ∈ A ⊓ Q, ∀ y ∈ I, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (h.Q_le hx.2) y hy).symm
  have hprod := card_sup_mul_card_inf hcomm
  have hinf_eq : (A ⊓ Q) ⊓ I = A ⊓ I := by
    rw [inf_assoc, inf_eq_right.mpr h.I_le_Q]
  rw [hinf_eq] at hprod
  calc
    Nat.card I * Nat.card ↥(A ⊓ Q) = Nat.card ↥(A ⊓ Q) * Nat.card I := by rw [Nat.mul_comm]
    _ = Nat.card ↥((A ⊓ Q) ⊔ I) * Nat.card ↥(A ⊓ I) := by rw [← hprod]
    _ ≤ Nat.card A * Nat.card ↥(U ⊔ V₀) := Nat.mul_le_mul hB_card hAI_card

theorem sup_eq_of_offender (h : KTCfg16 U V₀ V I K T Q) {A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 T) (hAQ : ¬ A ≤ Q) : A ⊔ Q = T := by
  have hA_le_T : A ≤ T := (mem_elemFamilyIn.mp hA).1
  have hle : A ⊔ Q ≤ T := sup_le hA_le_T h.Q_le_T
  have hAnorm : A ≤ Subgroup.normalizer (Q : Set G) := hA_le_T.trans h.T_le
  have hAQ_prod : Nat.card ↥(A ⊔ Q) * Nat.card ↥(A ⊓ Q) = Nat.card A * Nat.card Q :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hAnorm
  have hchain : Nat.card T * Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q) ≤
      Nat.card ↥(A ⊔ Q) * Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q) := by
    calc
      Nat.card T * Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q)
          = (Nat.card T * Nat.card ↥(U ⊔ V₀)) * Nat.card ↥(A ⊓ Q) := by ring
      _ = (Nat.card V * Nat.card Q) * Nat.card ↥(A ⊓ Q) := by rw [card_mul_card_eq h]
      _ = Nat.card V * Nat.card ↥(A ⊓ Q) * Nat.card Q := by ring
      _ = Nat.card I * Nat.card ↥(A ⊓ Q) * Nat.card Q := by rw [← h.card_eq]
      _ ≤ Nat.card A * Nat.card ↥(U ⊔ V₀) * Nat.card Q :=
            mul_le_mul_left (card_mul_le_of_offender h hA hAQ) (Nat.card Q)
      _ = Nat.card A * Nat.card Q * Nat.card ↥(U ⊔ V₀) := by ring
      _ = Nat.card ↥(A ⊔ Q) * Nat.card ↥(A ⊓ Q) * Nat.card ↥(U ⊔ V₀) := by rw [← hAQ_prod]
      _ = Nat.card ↥(A ⊔ Q) * Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q) := by ring
  have hT_le : Nat.card T ≤ Nat.card ↥(A ⊔ Q) := by
    have hposZ : 0 < Nat.card ↥(U ⊔ V₀) :=
      Nat.card_pos_iff.mpr ⟨⟨1, (U ⊔ V₀).one_mem⟩, inferInstance⟩
    have hposAQ : 0 < Nat.card ↥(A ⊓ Q) :=
      Nat.card_pos_iff.mpr ⟨⟨1, (A ⊓ Q).one_mem⟩, inferInstance⟩
    have hpos : 0 < Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q) := Nat.mul_pos hposZ hposAQ
    have hchain' : (Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q)) * Nat.card T ≤
        (Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q)) * Nat.card ↥(A ⊔ Q) := by
      calc
        (Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q)) * Nat.card T
            = Nat.card T * Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q) := by ring
        _ ≤ Nat.card ↥(A ⊔ Q) * Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q) := hchain
        _ = (Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q)) * Nat.card ↥(A ⊔ Q) := by ring
    exact Nat.le_of_mul_le_mul_left hchain' hpos
  exact Subgroup.eq_of_le_of_card_ge hle hT_le

theorem inf_le_centralizer_of_offender (h : KTCfg16 U V₀ V I K T Q) {A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 T) (hAQ : ¬ A ≤ Q) : A ⊓ Q ≤ centralizer (V : Set G) := by
  have hA_le_T : A ≤ T := (mem_elemFamilyIn.mp hA).1
  have hA_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    (CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff.mp (mem_elemFamilyIn.mp hA).2.1).1
  have hAnorm : A ≤ Subgroup.normalizer (Q : Set G) := hA_le_T.trans h.T_le
  have hsup : A ⊔ Q = T := sup_eq_of_offender h hA hAQ
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvT : v ∈ T := h.V_le_T hv
  have hvAQs : v ∈ (A : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A Q hAnorm, hsup]
    exact hvT
  obtain ⟨a, haA, q, hqQ, haq⟩ := Set.mem_mul.mp hvAQs
  have hva : v⁻¹ * a ∈ Q := by
    have h' : v⁻¹ * a = q⁻¹ := by rw [← haq]; group
    rw [h']
    exact Q.inv_mem hqQ
  exact (comm_of_mem_inf h hA_comm hx haA hv hva).symm

theorem card_le_of_offender (h : KTCfg16 U V₀ V I K T Q) {A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 T) (hAQ : ¬ A ≤ Q) :
    Nat.card A ≤ Nat.card ↥(T ⊓ centralizer (V : Set G)) := by
  set B : Subgroup G := V ⊔ (A ⊓ Q) with hB_def
  have hV_comm : ∀ x ∈ V, ∀ y ∈ A ⊓ Q, x * y = y * x :=
    fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (inf_le_centralizer_of_offender h hA hAQ hy)) x hx
  have hprod : Nat.card B * Nat.card ↥(V ⊓ (A ⊓ Q)) = Nat.card V * Nat.card ↥(A ⊓ Q) := by
    rw [hB_def]
    exact card_sup_mul_card_inf hV_comm
  have hvi_le : V ⊓ (A ⊓ Q) ≤ U ⊔ V₀ := by
    have h1 : V ⊓ (A ⊓ Q) ≤ V ⊓ Q :=
      le_inf inf_le_left (le_trans inf_le_right inf_le_right)
    exact h1.trans (le_of_eq (by
      apply le_antisymm h.inf_le
      exact le_inf h.le_V (h.le_I.trans h.I_le_Q)))
  have hvi_card : Nat.card ↥(V ⊓ (A ⊓ Q)) ≤ Nat.card ↥(U ⊔ V₀) := Subgroup.card_le_of_le hvi_le
  have hV_le_centV : V ≤ Subgroup.centralizer (V : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (h.comm_V x hx y hy).symm
  have hB_le_T : B ≤ T := by
    rw [hB_def]
    exact sup_le h.V_le_T (le_trans inf_le_left (mem_elemFamilyIn.mp hA).1)
  have hB_le_centV : B ≤ Subgroup.centralizer (V : Set G) := by
    rw [hB_def]
    exact sup_le hV_le_centV (inf_le_centralizer_of_offender h hA hAQ)
  have hB_le : B ≤ T ⊓ Subgroup.centralizer (V : Set G) := le_inf hB_le_T hB_le_centV
  have hcard_eq : Nat.card T * Nat.card ↥(U ⊔ V₀) = Nat.card V * Nat.card Q := card_mul_card_eq h
  have hAT_prod : Nat.card T * Nat.card ↥(A ⊓ Q) = Nat.card A * Nat.card Q := by
    have hAnorm : A ≤ Subgroup.normalizer (Q : Set G) :=
      ((mem_elemFamilyIn.mp hA).1).trans h.T_le
    rw [← sup_eq_of_offender h hA hAQ]
    exact CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hAnorm
  have hchain : Nat.card A * Nat.card Q * Nat.card ↥(U ⊔ V₀) ≤
      Nat.card B * Nat.card Q * Nat.card ↥(U ⊔ V₀) := by
    calc
      Nat.card A * Nat.card Q * Nat.card ↥(U ⊔ V₀)
          = (Nat.card T * Nat.card ↥(A ⊓ Q)) * Nat.card ↥(U ⊔ V₀) := by rw [← hAT_prod]
      _ = Nat.card T * Nat.card ↥(U ⊔ V₀) * Nat.card ↥(A ⊓ Q) := by ring
      _ = (Nat.card V * Nat.card Q) * Nat.card ↥(A ⊓ Q) := by rw [hcard_eq]
      _ = Nat.card V * Nat.card ↥(A ⊓ Q) * Nat.card Q := by ring
      _ = (Nat.card B * Nat.card ↥(V ⊓ (A ⊓ Q))) * Nat.card Q := by rw [← hprod]
      _ ≤ Nat.card B * Nat.card ↥(U ⊔ V₀) * Nat.card Q :=
            mul_le_mul_left (mul_le_mul_right hvi_card (Nat.card B)) (Nat.card Q)
      _ = Nat.card B * Nat.card Q * Nat.card ↥(U ⊔ V₀) := by ring
  have hA_le_B : Nat.card A ≤ Nat.card B := by
    have hposQ : 0 < Nat.card Q := Nat.card_pos_iff.mpr ⟨⟨1, Q.one_mem⟩, inferInstance⟩
    have hposZ : 0 < Nat.card ↥(U ⊔ V₀) :=
      Nat.card_pos_iff.mpr ⟨⟨1, (U ⊔ V₀).one_mem⟩, inferInstance⟩
    have hpos : 0 < Nat.card Q * Nat.card ↥(U ⊔ V₀) := Nat.mul_pos hposQ hposZ
    have hchain' : (Nat.card Q * Nat.card ↥(U ⊔ V₀)) * Nat.card A ≤
        (Nat.card Q * Nat.card ↥(U ⊔ V₀)) * Nat.card B := by
      calc
        (Nat.card Q * Nat.card ↥(U ⊔ V₀)) * Nat.card A
            = Nat.card A * Nat.card Q * Nat.card ↥(U ⊔ V₀) := by ring
        _ ≤ Nat.card B * Nat.card Q * Nat.card ↥(U ⊔ V₀) := hchain
        _ = (Nat.card Q * Nat.card ↥(U ⊔ V₀)) * Nat.card B := by ring
    exact Nat.le_of_mul_le_mul_left hchain' hpos
  exact hA_le_B.trans (Subgroup.card_le_of_le hB_le)

end KTCfg16

end CFSG.LocalAnalysis.WeakClosure81

end
