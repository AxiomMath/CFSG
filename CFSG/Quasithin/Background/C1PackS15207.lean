module

public import CFSG.Quasithin.EmptyFaithful.S152Y24
public import CFSG.Quasithin.Background.C1PackS15348
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack152

variable {G : Type} [Group G]

theorem normalizes_of_commutator_le {X Y P : Subgroup G} (hP : IsPGroup 2 P)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hYP : Y ≤ Subgroup.normalizer (P : Set G))
    (hX : X = oTwoUpper X) (hc : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ P) :
    Y ≤ Subgroup.normalizer (X : Set G) := by
  have hconj : ∀ y ∈ Y, ∀ z ∈ X ⊔ P, y * z * y⁻¹ ∈ X ⊔ P := by
    intro y hy z hz
    rw [Subgroup.sup_eq_closure] at hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · have e : y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hc y hy z hz)) (Subgroup.mem_sup_left hz)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hYP hy) z).mp hz)
    | one => simp
    | mul a b _ _ iha ihb =>
      have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [e]
      exact (X ⊔ P).mul_mem iha ihb
    | inv a _ ih =>
      have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e]
      exact (X ⊔ P).inv_mem ih
  have hYN : Y ≤ Subgroup.normalizer ((X ⊔ P : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hconj y hy z, fun hz => ?_⟩
    have := hconj y⁻¹ (Y.inv_mem hy) _ hz
    simpa [mul_assoc] using this
  have hO : X = oTwoUpper (X ⊔ P) :=
    eq_oTwoUpper_of_pow_mem le_sup_left
      (fun x hx => C1Pack153.exists_pow_mem_of_mem_sup_two hP hPX hx) hX
  intro y hy
  have := normalizer_le_normalizer_oTwoUpper (X ⊔ P) (hYN hy)
  rwa [← hO] at this

theorem charTwo_of_le [Finite G] {K M : Subgroup G} (hM : CharTwo M) (hKM : K ≤ M)
    (hPK : pCoreOf 2 M ≤ K) : CharTwo K := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hM hKM hPK

end C1Pack152

theorem stageLemma15207_of_15203 (h3 : StageLemma15203) : StageLemma15207 := by
  intro G _ _ T Mc M hs Y₁ hY₁
  have c3 := h3 G T Mc M hs
  have hTM : T ≤ M := hs.mf.1.1.2
  have hYM : yOf152 T Mc M ≤ M := yOf152_le_M hs
  have hle : Y₁ ⊔ T ≤ yOf152 T Mc M ⊔ T := sup_le_sup_right hY₁.le T
  have hunique : IsUniqueM (yOf152 T Mc M ⊔ T) M := by
    refine ⟨⟨hY₁.unique.1.1, sup_le hYM hTM⟩, fun M' hM' => ?_⟩
    exact hY₁.unique.2 M' ⟨hM'.1, hle.trans hM'.2⟩
  have hSyl : IsSylowTwoOf T M := isSylowTwoOf_of_le151 hs.qtfe.sylow hTM
  have hPT : pCoreOf 2 M ≤ T := pCoreOf_le_of_isSylowTwoOf hSyl
  have hP2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hPM : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M
  have hcomm : ∀ y ∈ yOf152 T Mc M, ∀ x ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G),
      y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 M := fun y hy x hx =>
    c3.centralizes (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right hy) hx)
  have hAct : ∀ X : Subgroup G, X = oTwoUpper X →
      X ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) →
      T ≤ Subgroup.normalizer (X : Set G) → yOf152 T Mc M ≤ Subgroup.normalizer (X : Set G) :=
    fun X hXO hXC hTN =>
      C1Pack152.normalizes_of_commutator_le hP2 (hPT.trans hTN) (hYM.trans hPM) hXO
        (fun y hy x hx => hcomm y hy x (hXC hx))
  refine ⟨hunique, ?_, ?_⟩
  · intro X hX1 hXO hXC hTN
    have hYN := hAct X hXO hXC hTN
    have hXM : X ≤ M := hXC.trans inf_le_left
    have hK : X ⊔ T ≤ M := sup_le hXM hTM
    have hcharM : CharTwo M := by
      obtain ⟨S, hS⟩ := hs.qtfe.exists_sylow
      have hSM : (S : Subgroup G) ≤ M := hS ▸ hTM
      exact hs.qtfe.qtke.2.1 M hs.mf.1.1.1.1 ⟨S, hSM⟩
    have hCT : CharTwo (X ⊔ T) :=
      C1Pack152.charTwo_of_le hcharM hK (hPT.trans le_sup_right)
    have hXn : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hTN
    have hne : pCoreOf 2 X ≠ ⊥ :=
      C1Pack153.pCoreOf_ne_bot_of_normal hCT le_sup_left hXn hX1 hXO.symm
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
      ⟨pCoreOf 2 X, hne, pCoreOf_isPGroup 2 X, rfl⟩
    obtain ⟨M', hM'max, hM'le⟩ := exists_maxTwoLocal_ge hloc
    have hNle : Subgroup.normalizer (X : Set G) ≤ M' :=
      (normalizer_le_normalizer_pCoreOf (r := 2) X).trans hM'le
    have hM'eq : M' = M :=
      hunique.2 M' ⟨hM'max, sup_le (hYN.trans hNle) (hTN.trans hNle)⟩
    rw [← hM'eq]
    exact hNle
  · intro X _ hXO hXC hTN _
    refine C1Pack152.normalizes_of_commutator_le hP2 (hPT.trans hY₁.normalized)
      (hXC.trans inf_le_left |>.trans hPM) hY₁.eq_oTwo (fun x hx y hy => ?_)
    have h1 := hcomm y (hY₁.le hy) x (hXC hx)
    have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 M).inv_mem h1

end CFSG.Quasithin
