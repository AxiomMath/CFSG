module

public import CFSG.Quasithin.Background.C213NonQType
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.C213NonQCore

public section

namespace CFSG.Quasithin.C213NonQ

open CFSG.Open CFSG.QuasithinUnique

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem eq_one_of_mem_of_mem {A B : Subgroup Q} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hA : IsPGroup 2 ↥A) (hB : IsPGroup q ↥B) {c : Q} (hcA : c ∈ A) (hcB : c ∈ B) : c = 1 := by
  obtain ⟨m, hm⟩ := hA ⟨c, hcA⟩
  obtain ⟨n, hn⟩ := hB ⟨c, hcB⟩
  have h1 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hm)
  have h2 : orderOf c ∣ q ^ n := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
  have hcop : Nat.Coprime (2 ^ m) (q ^ n) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem fitting_le_centralizer {K M₀ R O : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q))
    (hFodd : Odd (Nat.card (CFSG.fittingSubgroup ↥K)))
    (hFM₀ : (CFSG.fittingSubgroup ↥K).map K.subtype ≤ M₀) (hO : IsPGroup 2 ↥O)
    (hRO : ∀ m ∈ M₀, ∀ r ∈ R, m * r * m⁻¹ * r⁻¹ ∈ O) :
    (CFSG.fittingSubgroup ↥K).map K.subtype ≤ Subgroup.centralizer (R : Set Q) := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore, Subgroup.map_iSup, iSup_le_iff]
  rintro ⟨p, hp⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  by_cases hpF : p ∣ Nat.card (CFSG.fittingSubgroup ↥K)
  · have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hFodd
      omega
    have hle : (CFSG.pCore p ↥K).map K.subtype ≤ (CFSG.fittingSubgroup ↥K).map K.subtype :=
      Subgroup.map_mono (CFSG.pCore_le_fitting _ p)
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hfO : f ∈ CFSG.pCore p Q := map_pCore_le_pCore hK p hf
    have hc1 : f * r * f⁻¹ * r⁻¹ ∈ O := hRO f (hFM₀ (hle hf)) r hr
    have hc2 : f * r * f⁻¹ * r⁻¹ ∈ CFSG.pCore p Q := by
      have h3 : r * f⁻¹ * r⁻¹ ∈ CFSG.pCore p Q :=
        CFSG.pCore_normal.conj_mem _ ((CFSG.pCore p Q).inv_mem hfO) r
      rw [show f * r * f⁻¹ * r⁻¹ = f * (r * f⁻¹ * r⁻¹) by group]
      exact (CFSG.pCore p Q).mul_mem hfO h3
    have h4 := eq_one_of_mem_of_mem hpp hp2 hO CFSG.pCore_isPGroup hc1 hc2
    calc r * f = (f * r * f⁻¹ * r⁻¹)⁻¹ * f * r := by group
      _ = f * r := by rw [h4, inv_one, one_mul]
  · have hbot : CFSG.pCore p ↥K = ⊥ := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥K)).exists_card_eq
      have hdvd : Nat.card (CFSG.pCore p ↥K) ∣ Nat.card (CFSG.fittingSubgroup ↥K) :=
        Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting _ p)
      rcases k with _ | k
      · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hk)
      · exfalso
        apply hpF
        rw [hk] at hdvd
        exact (dvd_pow_self p (by omega)).trans hdvd
    rw [hbot, Subgroup.map_bot]
    exact bot_le

theorem fitting_ne_top {K : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q)) :
    CFSG.fittingSubgroup ↥K ≠ ⊤ := by
  intro htop
  have hnil : Group.IsNilpotent ↥(CFSG.fittingSubgroup ↥K) := CFSG.fittingSubgroup_nilpotent
  rw [htop] at hnil
  have : Group.IsNilpotent ↥K := by
    have e : ↥(⊤ : Subgroup ↥K) ≃* ↥K := Subgroup.topEquiv
    exact Group.nilpotent_of_surjective e.toMonoidHom e.surjective
  exact not_isSolvable_of_mem_cComp hK inferInstance

theorem inf_centralizer_le_fitting {K : Subgroup Q}
    (hgF : CFSG.generalizedFitting ↥K = CFSG.fittingSubgroup ↥K) :
    K ⊓ Subgroup.centralizer (((CFSG.fittingSubgroup ↥K).map K.subtype : Subgroup Q) : Set Q) ≤
      (CFSG.fittingSubgroup ↥K).map K.subtype := by
  rintro x ⟨hxK, hxC⟩
  have h1 : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.centralizer
      ((CFSG.generalizedFitting ↥K : Subgroup ↥K) : Set ↥K) := by
    rw [hgF, Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ ⟨f, hf, rfl⟩)
  have h2 := CFSG.centralizer_generalizedFitting_le ↥K h1
  rw [hgF] at h2
  exact ⟨_, h2, rfl⟩

theorem le_normalizer_of_centralizes {K R : Subgroup Q} (h37 : A37Statement Q)
    (hK : K ∈ cComp (⊤ : Subgroup Q))
    (hgF : CFSG.generalizedFitting ↥K = CFSG.fittingSubgroup ↥K)
    (hRF : (CFSG.fittingSubgroup ↥K).map K.subtype ≤ Subgroup.centralizer (R : Set Q)) :
    R ≤ Subgroup.normalizer (K : Set Q) := by
  intro r hr
  set K' := K.map (MulAut.conj r).toMonoidHom with hK'
  have hK'c : K' ∈ cComp (⊤ : Subgroup Q) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj r) hK
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj r).surjective] at h1
  by_cases hKK : K' = K
  · have : r ∈ Subgroup.normalizer (K : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have : r * x * r⁻¹ ∈ K' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
        rwa [hKK] at this
      · intro hx
        have hx' : r * x * r⁻¹ ∈ K' := by rw [hKK]; exact hx
        obtain ⟨y, hy, hyx⟩ := hx'
        have : y = x := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
          exact mul_left_cancel (mul_right_cancel hyx)
        rwa [← this]
    exact this
  · exfalso
    have hcomm := h37 K hK K' hK'c (Ne.symm hKK)
    have hFK' : (CFSG.fittingSubgroup ↥K).map K.subtype ≤ K' := by
      intro f hf
      have hfK : f ∈ K := by
        obtain ⟨f', -, rfl⟩ := hf
        exact f'.2
      refine ⟨f, hfK, ?_⟩
      have := Subgroup.mem_centralizer_iff.mp (hRF hf) r hr
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [this, mul_inv_cancel_right]
    apply fitting_ne_top hK
    rw [eq_top_iff]
    intro x _
    have hx := inf_centralizer_le_fitting hgF ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun f hf => by
      have h1 := Subgroup.commutator_mem_commutator x.2 (hFK' hf)
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm⟩
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show y = x from Subtype.ext hyx] at hy

theorem mem_cComp_top (h36 : A36Statement Q) (h37 : A37Statement Q) (h39 : A39Statement Q)
    {M M₀ L R O : Subgroup Q} (hFM : CFSG.generalizedFitting Q ≤ M) (hL : L ∈ cComp M)
    (hLM₀ : L ≤ M₀) (hR : IsPGroup 2 ↥R) (hO : IsPGroup 2 ↥O)
    (hRO : ∀ m ∈ M₀, ∀ r ∈ R, m * r * m⁻¹ * r⁻¹ ∈ O)
    (hstep : ∀ K ∈ cComp (⊤ : Subgroup Q), K ≤ M → ⁅K, L⁆ = K → K = L)
    (hcgs : ∀ K ∈ cComp (⊤ : Subgroup Q), R ≤ Subgroup.centralizer (K : Set Q) → K ≤ M) :
    L ∈ cComp (⊤ : Subgroup Q) := by
  have hLp := perfect_of_mem_cComp hL
  have hLS := le_cCompSpan h39 hLp
  obtain ⟨K, hK, hKL⟩ := exists_commutator_eq hLp (ne_bot_of_mem_cComp hL) hLS
  have hLK := le_normalizer_of_le_cCompSpan hLS hK
  by_cases hKM : K ≤ M
  · rw [← hstep K hK hKM hKL]
    exact hK
  exfalso
  have h36K := h36 K hK
  have h34 : A36Case3 ↥K ∨ A36Case4 ↥K := by
    rcases h36K.1 with ⟨hc, -, -⟩ | ⟨hc, -, -⟩ | h3 | h4
    · exact absurd ((le_generalizedFitting_of_isComponent hc).trans hFM) hKM
    · exact absurd ((le_generalizedFitting_of_isComponent hc).trans hFM) hKM
    · exact Or.inl h3
    · exact Or.inr h4
  have hgF : CFSG.generalizedFitting ↥K = CFSG.fittingSubgroup ↥K := by
    rcases h34 with ⟨-, -, -, h, -⟩ | ⟨h, -⟩ <;> exact h
  have hFodd : Odd (Nat.card (CFSG.fittingSubgroup ↥K)) := by
    rw [h36K.2.1.1]
    exact A37.odd_card_oddCore _
  have hFL := fitting_le_of_case34 hK h36K h34 hFM hL hLK hKL
  have hRF := fitting_le_centralizer hK hFodd (hFL.trans hLM₀) hO hRO
  have hRK := le_normalizer_of_centralizes h37 hK hgF hRF
  have hRC : R ≤ Subgroup.centralizer (K : Set Q) := by
    intro r hr
    have hrK : r ∈ Subgroup.centralizer (K : Set Q) := by
      obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
      refine mem_centralizer_of_two_pow
        (le_normalizer_map_of_characteristic Subgroup.le_normalizer _)
        (inf_centralizer_le_fitting hgF) ?_ (hRK hr) ?_ (n := n) (congrArg Subtype.val hn)
      · rw [Subgroup.card_map_of_injective K.subtype_injective]
        exact hFodd
      · rw [Subgroup.mem_centralizer_iff]
        intro f hf
        exact (Subgroup.mem_centralizer_iff.mp (hRF hf) r hr).symm
    exact hrK
  exact hKM (hcgs K hK hRC)

end CFSG.Quasithin.C213NonQ
