module

public import CFSG.Quasithin.Recognition.Stroth.Str83G3Main
public import CFSG.Quasithin.Recognition.Stroth.BenderQrc
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Frame2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

@[expose] def QrcDisp (L1 L2 S : Subgroup G) (a : ℕ) : Prop :=
  ∀ t ∈ S, t * t ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) →
    t ∉ Subgroup.centralizer (Z2 L1 L2 S : Set G) →
    (2 ^ (2 * a + 1)) ^ 2 ≤
      (Z2 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Z2 L1 L2 S)

@[expose] def QrcHab (L1 L2 S : Subgroup G) (a : ℕ) : Prop :=
  ∀ A : Subgroup G, A ≤ S → (∀ x ∈ A, ∀ y ∈ A,
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) ∧
        x * x ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G)) →
    (A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex A ≤ 2 ^ (2 * a + 1)

@[expose] def QrcHV (L1 L2 S : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ pCoreOf 2 (L1 ⊔ S) → IsElemAbelian 2 E →
    ¬ E ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) →
    ((Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E) ^ 2 ≤
      (Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S)

theorem isElemAbelian_z2 : IsElemAbelian 2 (Z2 L1 L2 S) :=
  SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)

private theorem qrc_hA
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) :
    ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A →
      (A ⊓ pCoreOf 2 (L1 ⊔ S)).relIndex A ≤ 2 ^ (2 * a + 1) := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ (2 * a + 1)) := by
    obtain ⟨e⟩ := hSz
    exact Or.inl ⟨a, ha, rfl, ⟨e⟩⟩
  intro A hAS hAe
  rw [hpCore1]
  exact relIndex_inf_q1_le hF.1 hS1 hq hAS (fun x hx => by
    rw [hAe.2 x hx]
    exact (Q1 L1 L2 S).one_mem)

private theorem qrc_hsec
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hZ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    ∀ L N : Subgroup G,
      IsChiefStep (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) (L1 ⊔ S)) L N →
      ¬ IsCentralStep (L1 ⊔ S) L N →
      ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 (L1 ⊔ S) →
        (2 ^ (2 * a + 1)) ^ 2 ≤ (centralizerMod L N A).relIndex N := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hUQ1 : conjClosure (Z2 L1 L2 S) (L1 ⊔ S) ≤ Q1 L1 L2 S := by
    refine conjClosure_le fun g hg z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S) (hHleP1 hg)) z).mp (hZ hz)
  have hq : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) := by
    obtain ⟨e⟩ := hSz
    rw [hsup1]
    exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF.1)
      (Or.inl ⟨a, ha, rfl, ⟨e⟩⟩)
  intro L N hstep hnc A hAS hAe hAO
  have hU : IsPGroup 2 (conjClosure (Z2 L1 L2 S) (L1 ⊔ S)) :=
    (pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le hUQ1
  have hUH : conjClosure (Z2 L1 L2 S) (L1 ⊔ S) ≤ L1 ⊔ S := by
    refine conjClosure_le fun g hg z hz => ?_
    have hzS : z ∈ S := hQ1S (hZ hz)
    exact (L1 ⊔ S).mul_mem ((L1 ⊔ S).mul_mem hg ((le_sup_right : S ≤ L1 ⊔ S) hzS))
      ((L1 ⊔ S).inv_mem hg)
  have hA' : A ≤ L1 ⊔ S := hAS.trans le_sup_right
  exact sq_le_relIndex_centralizerMod_of_not_le hq hU hUH hstep hnc hA'
    (fun x hx => by
      rw [← pow_two, hAe.2 x hx]
      exact Subgroup.one_mem _) hAO

private theorem qrc_hsub
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) :
    ∀ I : Subgroup G, L1 ⊔ S ≤ Subgroup.normalizer (I : Set G) →
      IsElemAbelian 2 I → pCoreOf 2 (L1 ⊔ S) ≤ Subgroup.centralizer (I : Set G) →
      ¬ L1 ⊔ S ≤ Subgroup.centralizer (I : Set G) →
      ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A → ¬ A ≤ pCoreOf 2 (L1 ⊔ S) →
        (2 ^ (2 * a + 1)) ^ 2 ≤ (Subgroup.centralizer (A : Set G) ⊓ I).relIndex I := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hq : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) := by
    obtain ⟨e⟩ := hSz
    rw [hsup1]
    exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF.1)
      (Or.inl ⟨a, ha, rfl, ⟨e⟩⟩)
  intro I hHI hIe hO hHI' A hAS hAe hAO
  obtain ⟨t, htA, htO⟩ : ∃ t ∈ A, t ∉ pCoreOf 2 (L1 ⊔ S) := by
    by_contra hcon
    push Not at hcon
    exact hAO fun x hx => hcon x hx
  have hv : ∀ v ∈ I, v * v = 1 := fun v hv => by rw [← pow_two, hIe.2 v hv]
  have h := sq_le_relIndex_centralizer_of_pCoreOf_le hq hv hHI hO hHI'
    ((hAS.trans le_sup_right) htA) (by rw [← pow_two, hAe.2 t htA]) htO
  have hle : (I ⊓ Subgroup.centralizer ({t} : Set G)).relIndex I ≤
      (Subgroup.centralizer (A : Set G) ⊓ I).relIndex I := by
    rw [inf_comm I]
    refine Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)
    have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hx t htA
    exact le_inf (inf_le_left.trans hCA) inf_le_right
  exact h.trans hle

private theorem qrc_hV_of_disp
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hSQ2 : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S)
    (hdisp : QrcDisp L1 L2 S a) : QrcHV L1 L2 S := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  intro E hE hEe hEnc
  have hES : E ≤ S := hE.trans (by rw [hpCore1]; exact hQ1S)
  have hEr : (E ⊓ Q2 L1 L2 S).relIndex E ≤ 2 ^ (2 * a + 1) := by
    rw [Subgroup.inf_relIndex_left]
    calc (Q2 L1 L2 S).relIndex E ≤ (Q2 L1 L2 S).relIndex S :=
          Subgroup.relIndex_le_of_le_right hES (D15Proof.relIndex_ne_zero _ _)
      _ = 2 ^ (2 * a + 1) := by
          have h := str86_relIndex_q2_s (n := 2 * a + 1) hF hB (by omega) hL2
          simpa using h
  have hstep1 : (Subgroup.centralizer (Z2 L1 L2 S : Set G) ⊓ E).relIndex E ≤
      2 ^ (2 * a + 1) := by
    refine (Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)).trans hEr
    refine le_inf ?_ inf_le_left
    intro x hx
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hx.2
  obtain ⟨f, hfE, hfC⟩ : ∃ f ∈ E, f ∉ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hEnc fun x hx => hcon x hx
  have hfQ2 : f ∉ Q2 L1 L2 S := fun hmem =>
    hfC (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hmem)
  have hf2 : f * f ∈ Q2 L1 L2 S := by
    rw [← pow_two, hEe.2 f hfE]
    exact Subgroup.one_mem _
  have hf2C : f * f ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hf2
  have hdisp_f := hdisp f (hES hfE) hf2C hfC
  have hCE : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({f} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hx f hfE
  have hmono : (Z2 L1 L2 S ⊓ Subgroup.centralizer ({f} : Set G)).relIndex
      (Z2 L1 L2 S) ≤
      (Subgroup.centralizer (E : Set G) ⊓ Z2 L1 L2 S).relIndex (Z2 L1 L2 S) := by
    refine Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)
    calc Subgroup.centralizer (E : Set G) ⊓ Z2 L1 L2 S
        = Z2 L1 L2 S ⊓ Subgroup.centralizer (E : Set G) := inf_comm _ _
      _ ≤ Z2 L1 L2 S ⊓ Subgroup.centralizer ({f} : Set G) := inf_le_inf le_rfl hCE
  rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (Z2 L1 L2 S : Set G)) E,
    ← Subgroup.inf_relIndex_right (Subgroup.centralizer (E : Set G)) (Z2 L1 L2 S)]
  exact (Nat.pow_le_pow_left hstep1 2).trans (hdisp_f.trans (by
    simpa [inf_comm] using hmono))

private theorem qrc_false_of_disp
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ : ¬ thompsonJ S ≤ Q1 L1 L2 S)
    (hdisp : QrcDisp L1 L2 S a) (hV : QrcHV L1 L2 S) (hab : QrcHab L1 L2 S a) :
    False := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hD11 : D11Hyp (L2 ⊔ S) (L1 ⊔ S) S (Z2 L1 L2 S) (borelOf L1 S ⊔ S) :=
    d11Hyp_of_caseI hF hB ha hSz hL2 hZI
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hJ' : ¬ thompsonJ S ≤ pCoreOf 2 (L1 ⊔ S) := by
    rwa [hpCore1]
  have hA := qrc_hA hF hB ha hSz
  have hA' : ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A →
      (A ⊓ pCoreOf 2 (L1 ⊔ S)).relIndex A ≤ 2 ^ (2 * a + 1) := by
    intro A hAS hAe
    simpa [hpCore1] using hA A hAS hAe
  have hsec := qrc_hsec hF hB ha hSz (z2_le_q1_of_rq hF hB ha hSz hL2)
  have hsub := qrc_hsub hF hB ha hSz
  have hnot := d15_false_or_not_le (G₁ := L2 ⊔ S) (G₂ := L1 ⊔ S) (T := S)
    (V := Z2 L1 L2 S) (M₂ := borelOf L1 S ⊔ S) (q := 2 ^ (2 * a + 1))
    (r := 2 ^ (2 * a + 1)) hD11 hq hq hJ' hA' hsec hV hsub hdisp hab
  have hz := z2_le_q1_of_rq hF hB ha hSz hL2
  have hz' : Z2 L1 L2 S ≤ pCoreOf 2 (L1 ⊔ S) := by rwa [hpCore1]
  exact hnot hz'

private theorem qrc_false_of_not_ff
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ : ¬ thompsonJ S ≤ Q1 L1 L2 S)
    (hV : QrcHV L1 L2 S)
    (hnff : ¬ IsFFInt (L2 ⊔ S) (Z2 L1 L2 S) (isElemAbelian_z2 (L1 := L1) (L2 := L2) (S := S)))
    (hndual : ¬ IsDualFFInt (L2 ⊔ S) (Z2 L1 L2 S)
      (isElemAbelian_z2 (L1 := L1) (L2 := L2) (S := S))) :
    False := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
      congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hD11 : D11Hyp (L2 ⊔ S) (L1 ⊔ S) S (Z2 L1 L2 S) (borelOf L1 S ⊔ S) :=
    d11Hyp_of_caseI hF hB ha hSz hL2 hZI
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hJ' : ¬ thompsonJ S ≤ pCoreOf 2 (L1 ⊔ S) := by
    rwa [hpCore1]
  have hA := qrc_hA hF hB ha hSz
  have hA' : ∀ A : Subgroup G, A ≤ S → IsElemAbelian 2 A →
      (A ⊓ pCoreOf 2 (L1 ⊔ S)).relIndex A ≤ 2 ^ (2 * a + 1) := by
    intro A hAS hAe
    simpa [hpCore1] using hA A hAS hAe
  have hsec := qrc_hsec hF hB ha hSz (z2_le_q1_of_rq hF hB ha hSz hL2)
  have hsub := qrc_hsub hF hB ha hSz
  have hnot := d15_false_or_not_le' (G₁ := L2 ⊔ S) (G₂ := L1 ⊔ S) (T := S)
    (V := Z2 L1 L2 S) (M₂ := borelOf L1 S ⊔ S) (q := 2 ^ (2 * a + 1))
    hD11 hq hnff hndual hJ' hA' hsec hV hsub
  have hz := z2_le_q1_of_rq hF hB ha hSz hL2
  have hz' : Z2 L1 L2 S ≤ pCoreOf 2 (L1 ⊔ S) := by rwa [hpCore1]
  exact hnot hz'

theorem str83_c_eq_two_false
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ : ¬ thompsonJ S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L2 ⊔ S) (Z2 L1 L2 S) (Z2 L1 L2 S) 2) :
    False := by
  have hSQ2 : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S :=
    (str83_caseI_basics hF hB ha hSz hL2 hZI).2.2.2.1
  have hdisp : QrcDisp L1 L2 S a :=
    str83_disp_z2_ge_of_c_eq_two hF hB ha hSz hL2 hZI hser
  have hhab : QrcHab L1 L2 S a :=
    str83_relIndex_quadratic_le hF hB ha hSz hL2 hZI
  have hV := qrc_hV_of_disp hF hB ha hSz hL2 hSQ2 hdisp
  exact qrc_false_of_disp hF hB ha hSz hL2 hZI hJ hdisp hV hhab

theorem str83_st8_false
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ : ¬ thompsonJ S ≤ Q1 L1 L2 S)
    (hV : QrcHV L1 L2 S)
    (hnff : ¬ IsFFInt (L2 ⊔ S) (Z2 L1 L2 S)
      (isElemAbelian_z2 (L1 := L1) (L2 := L2) (S := S)))
    (hndual : ¬ IsDualFFInt (L2 ⊔ S) (Z2 L1 L2 S)
      (isElemAbelian_z2 (L1 := L1) (L2 := L2) (S := S))) :
    False :=
  qrc_false_of_not_ff hF hB ha hSz hL2 hZI hJ hV hnff hndual

end CFSG.Quasithin.Stroth

end
