module

public import CFSG.RankThree.GF2n.Parrott.Section5Theorem5Local
public import CFSG.RankThree.GF2n.Parrott.Section5BadReduction
public import CFSG.RankThree.GF2n.Parrott.Section5HbadT
public import CFSG.RankThree.GF2n.Parrott.Section5HbadUT
public import CFSG.RankThree.GF2n.Parrott.Section5QuotientHypA1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

section Certified

theorem parrott_theorem5_of_theorem1_theoremA_one
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤)
    (hA1 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA1 w →
      Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨
        CFSG.Blueprint.LieModel K .PSU 6 2 1)
    (hD : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      centerIn (J z) ≠ centerIn (H z) → centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
      ¬ ParrottEqualityBranch (z := z) (D := D) h →
      ∀ P : GL8, (∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) →
      ∀ σ₂ : ↥(H z), orderOf σ₂ = 3 → qH (z := z) D σ₂ = s2A →
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ →
      ∀ y (hyH : y ∈ H z), orderOf y = 2 → y ≠ z →
      (∀ c ∈ H z,
        c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) →
      qH (z := z) D ⟨y, hyH⟩ = tA →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y)
    (hE : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      centerIn (J z) ≠ centerIn (H z) → centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
      ¬ ParrottEqualityBranch (z := z) (D := D) h →
      ∀ P : GL8, (∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) →
      ∀ σ₂ : ↥(H z), orderOf σ₂ = 3 → qH (z := z) D σ₂ = s2A →
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ →
      ∀ y (hyH : y ∈ H z), orderOf y = 2 → y ≠ z →
      (∀ c ∈ H z,
        c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) →
      qH (z := z) D ⟨y, hyH⟩ = uA * tA →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) :
    ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ≠
        centerIn (Subgroup.centralizer ({z} : Set G)) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by
  intro G _ _ z h hZ hHO
  classical
  obtain ⟨hN, ⟨D⟩⟩ := parrottQuotientDataExists h
  have hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h := fun hEq =>
    hHO (hThm1 G z h hN D hEq)
  exact parrott_theorem5_of_quotientData D h hZ hHO hIII (hT2_of_theoremA_one hA1 h hZ)
    fun P hP σ₂ hσ₂ hq₂ hc₂ => forall_exists_conj_mem_ne_of_qH_tA_utA D h hIII P hP hσ₂ hq₂ hc₂
      (hD G z h hN D hZ hHO hIII P hP σ₂ hσ₂ hq₂ hc₂)
      (hE G z h hN D hZ hHO hIII P hP σ₂ hσ₂ hq₂ hc₂)

theorem parrott_theorem5_export
    (hA1 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA1 w →
      Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨
        CFSG.Blueprint.LieModel K .PSU 6 2 1)
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤) :
    ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ≠
        centerIn (Subgroup.centralizer ({z} : Set G)) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 :=
  parrott_theorem5_of_theorem1_theoremA_one hThm1 hA1
    (fun _ _ _ _ h _ D _ _ _ P hP _ hσ₂ hq₂ hc₂ _ hyH hy _ hbad hq B hBC hBn _ hyB hzB hcard =>
      (exists_J_conj_mem_of_isConj_tA_of_forall_conj_not_mem_lemma54T₂ D h P hP hσ₂ hq₂ hc₂ hyH hy
        (hq ▸ IsConj.refl _) hbad B hBC hBn hyB hzB hcard).imp fun _ hc => ⟨J_le_H hc.1, hc.2⟩)
    fun _ _ _ _ h _ D hZ _ _ P hP _ _ _ _ _ hyH hy _ _ hq B hBC hBn _ hyB hzB hcard =>
      exists_conj_mem_of_isConj_utA D h hZ P hP hyH hy (hq ▸ IsConj.refl _) B hBC hBn hyB hzB hcard

end Certified

end CFSG.RankThree.GF2n.Parrott
