module

public import CFSG.Quasithin.Vol2.Ch11SecO3YA
public import CFSG.Quasithin.Vol2.Ch11SecFKL1
public import CFSG.Quasithin.Vol2.Ch11SecO1J
public import CFSG.Quasithin.Vol2.Ch11SecO2B
public import CFSG.Quasithin.Vol2.Ch11SecFOblY
public import CFSG.Quasithin.Vol2.Ch11SecFU2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

theorem obl11_5_7Sp4Y_of (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1110 : Stmt11_1_0) (h1113 : Stmt11_1_3) (h1114 : Stmt11_1_4) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6) :
    Obl11_5_7Sp4Y := by
  intro G _ _ T L I n V₁ V₃ h hV₁ hV₃ hk _ _ hO _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  set G₁ := Subgroup.normalizer (V₁ : Set G) with hG₁
  set K := KOf L V₁ V₁ with hKdef
  set W := conjClosure (fsuV T I) G₁ with hWdef
  set U := conjClosure V₃ G₁ with hUdef
  set Y := Subgroup.centralizer (V₁ : Set G) ⊓ sectionCentralizer K (pCoreOf 2 K) with hYdef
  have hH₁ := inH_normalizer_V₁ h hV₁
  have hH₁M := normalizer_V₁_not_le h1154 h hV₁
  obtain ⟨hV₁₃, F, _, _, hF2, hnat⟩ :=
    SecD.natV3Fact_holds G T L I n V₁ V₃ hset (Or.inr hk) hV₁ hV₃
  have hV₃L : V₃ ≤ ⁅V₃, LOf L V₁⁆ ⊔ V₁ :=
    le_commutator_sup_of_isNaturalSection hnat hV₁₃ (SecD.lOf_le_normalizer L V₁)
  have hWL : ⁅W, LOf L V₁⁆ ≤ V₃ := commutator_conjClosure_lOf_le hF factSp4ZCent_holds
    factSp4VL1_holds h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk hO
  obtain ⟨-, hUQ, -, -⟩ := h1155 G T L I n V₁ V₃ G₁ h hV₁ hV₃ hH₁ hH₁M le_rfl
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 G₁ :=
    pCoreOf_le_pCoreOf_of_le_normalizer (kOf_le_normalizer_V₁ L V₁)
      (SecD.normalizer_le_normalizer_kOf L V₁ V₁)
  have hVO : ⁅V₃, pCoreOf 2 K⁆ ≤ V₁ :=
    (Subgroup.commutator_mono (le_conjClosure_self _ _) hOK).trans hUQ
  have hON : pCoreOf 2 K ≤ Subgroup.normalizer (V₃ : Set G) :=
    (SecD.pCoreOf_kOf_le_ROf h hV₁).2.trans (SecA.IsVi.le_normalizer hV₃)
  have hV₃W : V₃ ≤ W := (SecA.IsVi.le_fsuV hV₃).trans (le_conjClosure_self _ _)
  have hL₁K : LOf L V₁ ≤ K := le_conjClosure_self _ _
  have hyV₁ : ∀ y ∈ Y, ∀ z ∈ V₁, y * z * y⁻¹ ∈ V₁ := fun y hy z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp hy.1 z hz, mul_inv_cancel_right]
    exact hz
  have hA : ∀ y ∈ Y, ∀ v ∈ V₃, y * v * y⁻¹ ∈ V₃ := fun y hy =>
    O3.conj_mem_of_commutator hV₃L hV₁₃ hV₃W hWL hVO hON
      (le_normalizer_conjClosure _ _ (Y_le_normalizer_V₁ L V₁ hy)) hy.2.2.1 (hyV₁ y hy)
      fun a ha => hy.2.2.2 a (hL₁K ha)
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcopY := (h1156 G T L I n V₁ X G₁ h hV₁ hX hH₁ hH₁M le_rfl).1
  have hYV : Y ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (V₃ : Set G) :=
      SecD.mem_normalizer_of_conj (hA y hy) fun v hv => by
        simpa using hA y⁻¹ (Y.inv_mem hy) v hv
    have hcomm : ∀ a ∈ LOf L V₁, ∀ v ∈ V₃,
        y * (a * v * a⁻¹) * y⁻¹ * (a * (y * v * y⁻¹) * a⁻¹)⁻¹ ∈ V₁ := by
      intro a ha v hv
      have hoO : y * a * y⁻¹ * a⁻¹ ∈ pCoreOf 2 K := hy.2.2.2 a (hL₁K ha)
      have hw : a * (y * v * y⁻¹) * a⁻¹ ∈ V₃ :=
        (Subgroup.mem_normalizer_iff.mp (hnat.1 ha) _).mp (hA y hy v hv)
      have heq : y * (a * v * a⁻¹) * y⁻¹ * (a * (y * v * y⁻¹) * a⁻¹)⁻¹ =
          ⁅a * (y * v * y⁻¹) * a⁻¹, y * a * y⁻¹ * a⁻¹⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact V₁.inv_mem (hVO (Subgroup.commutator_mem_commutator hw hoO))
    have hcop : Nat.Coprime (orderOf y) (Fintype.card F - 1) := by
      have hdvd := orderOf_dvd_natCard (⟨y, hy⟩ : ↥Y)
      rw [Subgroup.orderOf_mk] at hdvd
      rw [hF2]
      exact Nat.Coprime.coprime_dvd_left hdvd hcopY
    have hsec : y ∈ sectionCentralizer V₃ V₁ :=
      ⟨hyN, Y_le_normalizer_V₁ L V₁ hy,
        O3.conj_comm_mem_of_isNaturalSection hnat hyN (hyV₁ y hy) hcomm hcop⟩
    exact inf_normalizer_V₁_le_normalizer_fsuV h1103 h hV₁
      ⟨(h1114 G T L I n V₁ V₃ h hV₁ hV₃).1 hsec, Y_le_normalizer_V₁ L V₁ hy⟩
  exact SecD.le_normalizer_sup hYV ((Y_le_normalizer_V₁ L V₁).trans
    (le_normalizer_conjClosure _ _))

end CFSG.Quasithin.Vol2.Ch11.SecF
