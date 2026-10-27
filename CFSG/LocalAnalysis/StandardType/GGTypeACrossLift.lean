module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyFourTypeA
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeRel
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeTypeAFrame
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Matrix SpecialLinear

theorem ggTypeACorankTwoExInput_of_crossLift (hF : GGTypeAFarCommuteGenInput)
    (h3 : GGTypeAThirdNbrInput) (hX : GGTypeACrossLiftInput) (hJ : GGTypeAJoinThreeInput) :
    GGTypeACorankTwoExInput := by
  intro G _ _ p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN hdiv hout
  have hNC : GGTypeANbrCfg p B Bs x L D J n f y K := ⟨hcfg, hOp, hInn, hNoTr, hN⟩
  obtain ⟨y₃, K₃, hN₃, hK₃⟩ := h3 G p B Bs x L D J n f y K hNC hdiv hout
  have hNC₃ : GGTypeANbrCfg p B Bs x L D J n f y₃ K₃ := ⟨hcfg, hOp, hInn, hNoTr, hN₃⟩
  have hn : 3 ≤ n := hN.2.2.1
  have hf : 1 ≤ f := hN.1.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  obtain ⟨φ₁, φ₂, φ₃, hφL, hk₁, hJ₁, hφK, hk₂, hc₂, hφK₃, hk₃, hc₃, hX'⟩ :=
    hX G p B Bs x L D J n f y K y₃ K₃ hNC hN₃ hdiv hK₃
  have hj : (⟨n - 1, by omega⟩ : Fin n).val + 1 = n := by simp only; omega
  have hfar₂ := hF G p B Bs x L D J n f y K hNC φ₁ φ₂ hφL hk₁ hφK hk₂ hJ₁ hc₂ ⟨0, by omega⟩
    ⟨n - 1, by omega⟩ rfl hj
  have hfar₃ := hF G p B Bs x L D J n f y₃ K₃ hNC₃ φ₁ φ₃ hφL hk₁ hφK₃ hk₃ hJ₁ hc₃ ⟨0, by omega⟩
    ⟨n - 1, by omega⟩ rfl hj
  have hT₁ := ggTypeAEndNode_of_compat h2 hn hc₂ hfar₂
  have hT₃ := ggTypeAEndNode_of_compat h2 hn hc₃ hfar₃
  have hKle := slCompat_range_le h2 (by omega) hc₂
  have hK₃le := slCompat_range_le h2 (by omega) hc₃
  rw [hφK, hφL] at hKle
  rw [hφK₃, hφL] at hK₃le
  obtain ⟨hcube, hcent⟩ := hX' ⟨n - 1, by omega⟩ hj
  set T₁ := φ₂ (weylRep n (GaloisField 2 f) ⟨n - 1, by omega⟩) with hT₁def
  set T₃ := φ₃ (weylRep n (GaloisField 2 f) ⟨n - 1, by omega⟩) with hT₃def
  have hT₁K : T₁ ∈ K := by rw [← hφK]; exact ⟨_, rfl⟩
  have hT₃K : T₃ ∈ K₃ := by rw [← hφK₃]; exact ⟨_, rfl⟩
  have hT₁G : T₁ ∈ ggG0 p B x L D J := hN.sup_le_ggG0 (Subgroup.mem_sup_right hT₁K)
  have hT₃G : T₃ ∈ ggG0 p B x L D J := hN₃.sup_le_ggG0 (Subgroup.mem_sup_right hT₃K)
  have h1 : T₁ * T₁ = 1 := hT₁.1
  have h3' : T₃ * T₃ = 1 := hT₃.1
  have e3 : T₁ * (T₁ * T₃ * T₁) * T₁ = T₃ := by
    calc T₁ * (T₁ * T₃ * T₁) * T₁ = (T₁ * T₁) * T₃ * (T₁ * T₁) := by group
      _ = T₃ := by rw [h1, one_mul, mul_one]
  refine ⟨φ₁, hφL, hk₁, T₁, T₁ * T₃ * T₁, hT₁G, mul_mem (mul_mem hT₁G hT₃G) hT₁G,
    ⟨hT₁, ?_, ?_, hcent⟩, ?_⟩
  · calc T₁ * T₃ * T₁ * (T₁ * T₃ * T₁) = T₁ * (T₃ * (T₁ * T₁) * T₃) * T₁ := by group
      _ = 1 := by rw [h1, mul_one, h3', mul_one, h1]
  · have e : T₁ * (T₁ * T₃ * T₁) = T₃ * T₁ := by
      calc T₁ * (T₁ * T₃ * T₁) = (T₁ * T₁) * T₃ * T₁ := by group
        _ = T₃ * T₁ := by rw [h1, one_mul]
    rw [e]
    exact hcube
  · intro y' K' hK'
    have hA : L ⊔ L.map (MulAut.conj T₁).toMonoidHom ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom ⊔
        L.map (MulAut.conj (T₁ * T₃ * T₁ * T₁)).toMonoidHom ⊔
        L.map (MulAut.conj (T₁ * (T₁ * T₃ * T₁) * T₁)).toMonoidHom :=
      le_sup_left.trans le_sup_left
    have hLM : L ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom ⊔
        L.map (MulAut.conj (T₁ * T₃ * T₁ * T₁)).toMonoidHom ⊔
        L.map (MulAut.conj (T₁ * (T₁ * T₃ * T₁) * T₁)).toMonoidHom :=
      le_sup_left.trans hA
    have hT₃M : L.map (MulAut.conj T₃).toMonoidHom ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom ⊔
        L.map (MulAut.conj (T₁ * T₃ * T₁ * T₁)).toMonoidHom ⊔
        L.map (MulAut.conj (T₁ * (T₁ * T₃ * T₁) * T₁)).toMonoidHom := by
      have e : L.map (MulAut.conj T₃).toMonoidHom =
          L.map (MulAut.conj (T₁ * (T₁ * T₃ * T₁) * T₁)).toMonoidHom := by rw [e3]
      rw [e]
      exact le_sup_right
    have hKM := hKle.trans hA
    have hK₃M := hK₃le.trans (sup_le hLM hT₃M)
    exact (hJ G p B Bs x L D J n f y K y₃ K₃ hNC hN₃ hdiv hK₃ y' K' hK').trans
      (sup_le (sup_le hLM hKM) hK₃M)

section TypeA

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveTypeA_of_corankTwoEx (hC : GGTypeACorankTwoExInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (h : GGTypeANbr p B Bs x L D J n f y K) (hdiv : p ∣ n + 3)
    (hout : ∃ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' ∧ ¬ K' ≤ L ⊔ K) :
    GGSecFiveTypeA p B x L D J (n + 1 + 1) (n + 1) f := by
  obtain ⟨φ₁, hφL, hker, T₁, T₂, hT₁G, hT₂G, hT, hnbr⟩ :=
    hC G p B Bs x L D J n f y K hcfg hOp hInn hNoTr h hdiv hout
  exact ggSecFiveTypeA_of_twoEndNodes h.2.2.1 h.1.1.2.1 φ₁ hφL hker hT hT₁G hT₂G hnbr

section Compat

theorem ggSecFiveCompat_of_corankTwoEx (hC : GGTypeACorankTwoExInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (h : GGTypeANbr p B Bs x L D J n f y K) (hdiv : p ∣ n + 3)
    (hout : ∃ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' ∧ ¬ K' ≤ L ⊔ K) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨φ₁, hφL, hker, T₁, T₂, hT₁G, hT₂G, hT, hnbr⟩ :=
    hC G p B Bs x L D J n f y K hcfg hOp hInn hNoTr h hdiv hout
  obtain ⟨ψ₀, hpres, hcomp⟩ := ggSecFiveCompat_of_twoEndNodesAt h.2.2.1 h.1.1.2.1 φ₁ hφL hker hT
    (le_ggG0_left p B x L D J) hT₁G hT₂G (le_sup_left.trans (le_sup_left.trans le_sup_left)) hnbr
  exact ⟨.PSL, n + 1 + 1 + 1, f, ψ₀, hpres, L, Or.inl rfl, hcomp⟩

end Compat

end TypeA

end CFSG.StandardType
