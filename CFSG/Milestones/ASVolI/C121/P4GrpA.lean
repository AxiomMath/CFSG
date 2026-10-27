module

public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.Background.C1PackS15212A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {Ω : Type} [Group Ω] [Finite Ω]

structure burnsideC121_p4_Hyp (X L T R V Y : Subgroup Ω) : Prop where
  hL : L = oTwoUpper X
  hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  hT : IsPGroup 2 T
  hSR : baum T ≤ R
  hRT : R ≤ T
  hQR : pCoreOf 2 X ≤ R
  hRX : R ≤ X
  red : IsTwoReducedIn X V
  hJZ : autOn (thompsonJ R) V =
    autOn (R ⊓ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω) :
      Subgroup Ω) : Set Ω)) V
  hYperf : Y = oTwoUpper Y
  hYX : Y ≤ X
  hYN : thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω)) ≤ Subgroup.normalizer (Y : Set Ω)
  hYC : Y ⊓ Subgroup.centralizer (V : Set Ω) = pCoreOf 2 Y
  hsyl : IsSylowTwoOf (autOn (thompsonJ R) V) (autOn (Y ⊔ thompsonJ R) V)
  hZY : ⁅V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω), Y⁆ ≠ ⊥

namespace burnsideC121_p4_Hyp

variable {X L T R V Y : Subgroup Ω} (h : burnsideC121_p4_Hyp X L T R V Y)
include h

theorem hV : IsElemAbelian 2 V := h.red.2.2.1

theorem hR2 : IsPGroup 2 R := h.hT.to_le h.hRT

theorem baum_eq : baum T = baum R := baum_eq_of_le h.hSR h.hRT

theorem J_le_S : thompsonJ R ≤ baum T := by
  rw [h.baum_eq]
  exact B6.thompsonJ_le_baum R

theorem S_le_R : baum T ≤ R := h.hSR

theorem S_le_X : baum T ≤ X := h.hSR.trans h.hRX

theorem J_le_X : thompsonJ R ≤ X := h.J_le_S.trans h.S_le_X

theorem X_le_NV : X ≤ Subgroup.normalizer (V : Set Ω) := h.red.2.1

theorem V_le_Q : V ≤ pCoreOf 2 X := C124.le_pCoreOf_of_reduced h.red

theorem Q_le_CV : pCoreOf 2 X ≤ Subgroup.centralizer (V : Set Ω) := C124.pCoreOf_le_centralizer h.red

theorem Q_le_X : pCoreOf 2 X ≤ X := pCoreOf_le 2 X

theorem Q_two : IsPGroup 2 (pCoreOf 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pCoreOf_isPGroup 2 X

theorem V_le_R : V ≤ R := h.V_le_Q.trans h.hQR

theorem mem_thompsonJ_of {z : Ω} (hzR : z ∈ R) (hz2 : z ^ 2 = 1)
    (hzC : z ∈ Subgroup.centralizer (thompsonJ R : Set Ω)) : z ∈ thompsonJ R := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian R
  have hzA : z ∈ A := by
    have hAJ : A ≤ thompsonJ R := B6.le_thompsonJ hA
    let B : Subgroup Ω := Subgroup.closure ((A : Set Ω) ∪ {z})
    have hcomm : ∀ a ∈ (A : Set Ω) ∪ {z}, ∀ b ∈ (A : Set Ω) ∪ {z}, a * b = b * a := by
      have hzc : ∀ a ∈ A, a * z = z * a := fun a ha =>
        (Subgroup.mem_centralizer_iff.1 hzC a (hAJ ha))
      rintro a (ha | ha) b (hb | hb)
      · exact B2F.isElemAbelian_comm hA.2.1 ha hb
      · rw [Set.mem_singleton_iff.1 hb]; exact hzc a ha
      · rw [Set.mem_singleton_iff.1 ha]; exact (hzc b hb).symm
      · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
    have hsq : ∀ a ∈ (A : Set Ω) ∪ {z}, a ^ 2 = 1 := by
      rintro a (ha | ha)
      · exact hA.2.1.2 a ha
      · rw [Set.mem_singleton_iff.1 ha]; exact hz2
    have hB : IsElemAbelian 2 B := B2F.isElemAbelian_closure hcomm hsq
    have hBR : B ≤ R := (Subgroup.closure_le R).2 (Set.union_subset hA.1
      (Set.singleton_subset_iff.2 hzR))
    have hAB : A ≤ B := fun a ha => Subgroup.subset_closure (Or.inl ha)
    have hcard := hA.2.2 B hBR hB
    have heq : A = B := Subgroup.eq_of_le_of_card_ge hAB hcard
    rw [heq]
    exact Subgroup.subset_closure (Or.inr rfl)
  exact B6.le_thompsonJ hA hzA

theorem ZV_le_omega :
    V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω) ≤ omegaOneCenterOf (thompsonJ R) := by
  intro z hz
  have hzJ := h.mem_thompsonJ_of (h.V_le_R hz.1) (h.hV.2 z hz.1) hz.2
  exact Subgroup.subset_closure ⟨⟨hzJ, hz.2⟩, h.hV.2 z hz.1⟩

theorem S_le_CZ : baum T ≤ R ⊓ Subgroup.centralizer
    ((V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω) : Subgroup Ω) : Set Ω) := by
  rw [h.baum_eq]
  exact inf_le_inf_left _ (Subgroup.centralizer_le h.ZV_le_omega)

theorem autOn_baum : autOn (baum T) V = autOn (thompsonJ R) V := by
  apply le_antisymm
  · rw [h.hJZ]
    exact autOn_le_autOn V h.S_le_CZ
  · exact autOn_le_autOn V h.J_le_S

theorem S_le_JC : baum T ≤ thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω)) := by
  intro s hs
  have hsN : s ∈ Subgroup.normalizer (V : Set Ω) := h.X_le_NV (h.S_le_X hs)
  have h1 : convI h.hV ⟨s, hsN⟩ ∈ autI h.hV (thompsonJ R) := by
    rw [autI_eq_autOn, ← h.autOn_baum, ← autI_eq_autOn h.hV]
    exact convI_mem_autI h.hV hs hsN
  obtain ⟨g, hgJ, hg⟩ := (mem_autI h.hV).1 h1
  have h2 : convI h.hV (g⁻¹ * ⟨s, hsN⟩) = 1 := by rw [map_mul, map_inv, hg, inv_mul_cancel]
  have h3 := (convI_eq_one_iff h.hV _).1 h2
  have h4 : (g : Ω)⁻¹ * s ∈ X ⊓ Subgroup.centralizer (V : Set Ω) :=
    ⟨X.mul_mem (X.inv_mem (h.J_le_X hgJ)) (h.S_le_X hs), by simpa using h3⟩
  have : s = (g : Ω) * ((g : Ω)⁻¹ * s) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgJ) (Subgroup.mem_sup_right h4)

theorem X_le_N_CX : X ≤ Subgroup.normalizer
    ((X ⊓ Subgroup.centralizer (V : Set Ω) : Subgroup Ω) : Set Ω) :=
  B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer h.X_le_NV)

theorem Y_le_L : Y ≤ L := by
  rw [h.hL, h.hYperf]
  exact oTwoUpper_mono h.hYX

theorem sylow_CX : IsSylowTwoOf (pCoreOf 2 (X ⊓ Subgroup.centralizer (V : Set Ω)))
    (X ⊓ Subgroup.centralizer (V : Set Ω)) := by
  obtain ⟨TX, hTX, hRTX⟩ := A4.exists_isSylowTwoOf_ge h.hRX h.hR2
  have hLX : L ≤ X := by rw [h.hL]; exact oTwoUpper_le X
  have hn : X ≤ Subgroup.normalizer (L : Set Ω) := by rw [h.hL]; exact le_normalizer_oTwoUpper X
  have hsup : oTwoUpper X ⊔ TX = X := C1Pack12.oTwoUpper_sup_eq_of_sylow hTX
  have hLT : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ TX, x = l * t := by
    intro x hx
    have hx' : x ∈ TX ⊔ L := by rw [sup_comm, h.hL, hsup]; exact hx
    obtain ⟨t, ht, l, hl, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer (hTX.1.trans hn)).1 hx'
    refine ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.1 (hn (hTX.1 ht)) l).1 hl, t, ht, by group⟩
  have hVL : ⁅V, L⁆ ≠ ⊥ := by
    intro hb
    apply h.hZY
    rw [eq_bot_iff, ← hb]
    exact Subgroup.commutator_mono inf_le_left h.Y_le_L
  obtain ⟨⟨hsyl, -⟩, -⟩ := C124.B2_10_2 h.hV h.red h.hQR hRTX hTX hLX hn hLT hVL (Or.inl h.hLq)
  exact hsyl

theorem pCore_CX : pCoreOf 2 (X ⊓ Subgroup.centralizer (V : Set Ω)) = pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans inf_le_left)
      (h.X_le_N_CX.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  · exact le_pCoreOf_of_le_normalizer 2 (le_inf (pCoreOf_le 2 X) h.Q_le_CV)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)

theorem sylow_Q : IsSylowTwoOf (pCoreOf 2 X) (X ⊓ Subgroup.centralizer (V : Set Ω)) := by
  rw [← h.pCore_CX]
  exact h.sylow_CX

theorem le_Q {P : Subgroup Ω} (hP : P ≤ X ⊓ Subgroup.centralizer (V : Set Ω))
    (hP2 : IsPGroup 2 P) : P ≤ pCoreOf 2 X := by
  obtain ⟨S', hS', hPS'⟩ := A4.exists_isSylowTwoOf_ge hP hP2
  have h1 : pCoreOf 2 (X ⊓ Subgroup.centralizer (V : Set Ω)) ≤ S' :=
    pCoreOf_le_of_isSylowTwoOf hS'
  have h2 := (A4.isSylowTwoOf_iff_maximal.1 h.sylow_CX).2.2 S' hS'.1 hS'.2.1 h1
  rw [h.pCore_CX] at h2
  exact hPS'.trans h2

theorem SQ_le_NY : baum T ⊔ pCoreOf 2 X ≤ Subgroup.normalizer (Y : Set Ω) :=
  sup_le (h.S_le_JC.trans h.hYN)
    ((le_inf h.Q_le_X h.Q_le_CV).trans (le_sup_right.trans h.hYN))

end burnsideC121_p4_Hyp

end CFSG.Quasithin
