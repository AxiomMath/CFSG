module

public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenFr
public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenK

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem le_normalizer_sup_of_forall (c : MinCex193 D V₀ V p X) {g₀ : G} {K₀ : Subgroup G}
    (h₀ : Conf196 D V X g₀ K₀)
    (hall : ∀ (g₁ g₂ : G) (K₁ K₂ : Subgroup G), Conf196 D V X g₁ K₁ → Conf196 D V X g₂ K₂ →
      X ⊓ K₁ = X ⊓ K₂) :
    D.T ≤ normalizer (((X ⊓ K₀) ⊔ pCoreOf 2 (X ⊔ D.T) : Subgroup G) : Set G) := by
  set Q := pCoreOf 2 (X ⊔ D.T) with hQ
  set P := X ⊓ K₀ with hP
  have hHN : X ⊔ D.T ≤ normalizer ((X ⊔ Q : Subgroup G) : Set G) :=
    c.le_normalizer_sup_pCoreOf
  have hHQ : X ⊔ D.T ≤ normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hPQ : P ≤ normalizer (Q : Set G) := inf_le_left.trans (le_sup_left.trans hHQ)
  have hPS : ∀ t ∈ D.T, ∀ z ∈ P, t⁻¹ * z * t ∈ P ⊔ Q := by
    intro t ht z hz
    have h1 : Conf196 D V X (g₀ * t⁻¹) (conjSubgroup K₀ t⁻¹) := h₀.conj_T (D.T.inv_mem ht)
    have h2 : X ⊓ conjSubgroup K₀ t⁻¹ = X ⊓ K₀ := hall _ _ _ _ h1 h₀
    have hz1 : z ∈ X ⊓ conjSubgroup K₀ t⁻¹ := by rw [h2]; exact hz
    have hzK : t⁻¹ * z * t⁻¹⁻¹ ∈ K₀ := mem_conjSubgroup_iff.1 hz1.2
    have hinv : t⁻¹ ∈ X ⊔ D.T := Subgroup.mem_sup_right (D.T.inv_mem ht)
    have hzN : t⁻¹ * z * t⁻¹⁻¹ ∈ X ⊔ Q :=
      (Subgroup.mem_normalizer_iff.1 (hHN hinv) z).1 (Subgroup.mem_sup_left hz.1)
    have := h₀.inf_sup_pCoreOf_le c ⟨hzK, hzN⟩
    simpa using this
  have hPS' : ∀ t ∈ D.T, ∀ z ∈ P, t * z * t⁻¹ ∈ P ⊔ Q := fun t ht z hz => by
    simpa using hPS t⁻¹ (D.T.inv_mem ht) z hz
  have key : ∀ t ∈ D.T, ∀ z ∈ P ⊔ Q, t * z * t⁻¹ ∈ P ⊔ Q := by
    intro t ht z hz
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P Q hPQ] at hz
    obtain ⟨y, hy, q, hq, rfl⟩ := hz
    have e : t * (y * q) * t⁻¹ = (t * y * t⁻¹) * (t * q * t⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem _ (hPS' t ht y hy) (Subgroup.mem_sup_right ?_)
    exact (Subgroup.mem_normalizer_iff.1 (hHQ (Subgroup.mem_sup_right ht)) q).1 hq
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key t ht z, fun hz => ?_⟩
  have h3 := key t⁻¹ (D.T.inv_mem ht) _ hz
  have e : t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z := by group
  rwa [e] at h3

theorem le_of_le_sup_normalizer (c : MinCex193 D V₀ V p X) {S : Subgroup G}
    (hSN : S ≤ X ⊔ pCoreOf 2 (X ⊔ D.T)) (hQS : pCoreOf 2 (X ⊔ D.T) ≤ S)
    (hTS : D.T ≤ normalizer (S : Set G)) (hXS : X ≤ S ⊔ D.T) : X ≤ S := by
  set Q := pCoreOf 2 (X ⊔ D.T) with hQ
  have hQT : Q ≤ D.T := Hyp193.pCoreOf_le_T c.hyp
  have hXQ : X ≤ normalizer (Q : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  intro x hx
  have hx' : x ∈ D.T ⊔ S := by rw [sup_comm]; exact hXS hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D.T S hTS] at hx'
  obtain ⟨t, ht, u, hu, rfl⟩ := hx'
  have htN : t ∈ X ⊔ Q := by
    have h1 : t = (t * u) * u⁻¹ := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
      (Subgroup.inv_mem _ (hSN hu))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X Q hXQ] at htN
  obtain ⟨y, hy, q, hq, hyq⟩ := htN
  have hy1 : y = 1 := by
    have hyT : y ∈ D.T := by
      have : y = t * q⁻¹ := by rw [← hyq]; group
      rw [this]
      exact D.T.mul_mem ht (D.T.inv_mem (hQT hq))
    have : y ∈ X ⊓ D.T := ⟨hy, hyT⟩
    rwa [c.hyp.inf_T_eq_bot, Subgroup.mem_bot] at this
  have htQ : t ∈ Q := by
    have hyq' : y * q = t := hyq
    rw [← hyq', hy1, one_mul]
    exact hq
  exact Subgroup.mul_mem _ (hQS htQ) hu

theorem exists_inf_ne (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V') :
    ∃ (g₁ g₂ : G) (K₁ K₂ : Subgroup G), Conf196 D V X g₁ K₁ ∧ Conf196 D V X g₂ K₂ ∧
      X ⊓ K₁ ≠ X ⊓ K₂ := by
  classical
  by_contra hcon
  have hall : ∀ (g₁ g₂ : G) (K₁ K₂ : Subgroup G), Conf196 D V X g₁ K₁ → Conf196 D V X g₂ K₂ →
      X ⊓ K₁ = X ⊓ K₂ := by
    intro g₁ g₂ K₁ K₂ h₁ h₂
    by_contra h
    exact hcon ⟨g₁, g₂, K₁, K₂, h₁, h₂, h⟩
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  have hH := c.sup_eq_eGen_sup h162 h763
  set Q := pCoreOf 2 (X ⊔ D.T) with hQ
  have hQT : Q ≤ D.T := Hyp193.pCoreOf_le_T c.hyp
  have hPQ' : X ≤ normalizer (Q : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  by_cases hex : ∃ (g : G) (K : Subgroup G), Conf196 D V X g K
  · obtain ⟨g₀, K₀, h₀⟩ := hex
    set P := X ⊓ K₀ with hP
    have hPQ : P ≤ normalizer (Q : Set G) := inf_le_left.trans hPQ'
    have hTS := c.le_normalizer_sup_of_forall h₀ hall
    have hKle : ∀ (g : G) (K : Subgroup G), Conf196 D V X g K → K ≤ (P ⊔ Q) ⊔ D.T := by
      intro g K hc
      have h1 := hc.le_inf_sup_T c
      rw [hall g g₀ K K₀ hc h₀] at h1
      exact h1.trans (sup_le_sup_right le_sup_left _)
    have hE : E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ≤ (P ⊔ Q) ⊔ D.T := by
      refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
      obtain ⟨-, g, hAg, hm⟩ := hA
      have hAeq : A = conjSubgroup V g :=
        (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup c.isPGroup_V g) hAg).1 hm
      subst hAeq
      exact hKle g K ⟨hAT, hK⟩
    have hXS : X ≤ (P ⊔ Q) ⊔ D.T :=
      le_sup_left.trans (hH.symm.le.trans (sup_le hE le_sup_right))
    have hXS' : X ≤ P ⊔ Q :=
      c.le_of_le_sup_normalizer (sup_le_sup_right inf_le_left Q) le_sup_right hTS hXS
    have hXP : X ≤ P := by
      intro x hx
      have hx' := hXS' hx
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P Q hPQ] at hx'
      obtain ⟨y, hy, q, hq, rfl⟩ := hx'
      show y * q ∈ P
      have hyX : y ∈ X := (inf_le_left : P ≤ X) hy
      have hqX : q ∈ X := by
        have := X.mul_mem (X.inv_mem hyX) hx
        simpa using this
      have hq1 : q = 1 := by
        have : q ∈ X ⊓ Q := ⟨hqX, hq⟩
        rwa [c.hyp.inf_pCoreOf_eq_bot, Subgroup.mem_bot] at this
      rw [hq1, mul_one]
      exact hy
    have hXeq : P = X := le_antisymm inf_le_left hXP
    have hcard : Nat.card ↥P = p := h₀.card_inf_K c h162 h763
    rw [hXeq] at hcard
    exact c.hyp.noncyclic (isCyclic_of_prime_card (p := p) hcard)
  · have hE : E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_)
      exfalso
      obtain ⟨-, g, hAg, hm⟩ := hA
      have hAeq : A = conjSubgroup V g :=
        (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup c.isPGroup_V g) hAg).1 hm
      subst hAeq
      exact hex ⟨g, K, ⟨hAT, hK⟩⟩
    have hLT : X ⊔ D.T = D.T := by
      have h := hH
      rw [hE, bot_sup_eq] at h
      exact h.symm
    have hXT : X ≤ D.T := le_sup_left.trans hLT.le
    have hXbot : X ≤ ⊥ := by
      have : X ≤ X ⊓ D.T := le_inf le_rfl hXT
      rwa [c.hyp.inf_T_eq_bot] at this
    apply c.hyp.noncyclic
    rw [le_bot_iff.1 hXbot]
    infer_instance

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
