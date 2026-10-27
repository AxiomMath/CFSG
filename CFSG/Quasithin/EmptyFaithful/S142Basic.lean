module

public import CFSG.Quasithin.EmptyFaithful.S14118
public import CFSG.Quasithin.Vol2.Ch3Basic
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin

open CFSG.Open

section Conj

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_quasithinOmegaOneCenter (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ quasithinOmegaOneCenter T,
      g * x * g⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro g hg x hx
    have hle : quasithinOmegaOneCenter T ≤
        (quasithinOmegaOneCenter T).comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      obtain ⟨⟨hzT, hzC⟩, hz2⟩ := hz
      show (MulAut.conj g) z ∈ quasithinOmegaOneCenter T
      rw [MulAut.conj_apply]
      apply Subgroup.subset_closure
      refine ⟨⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzT, ?_⟩, ?_⟩
      · show g * z * g⁻¹ ∈ Subgroup.centralizer (T : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have hs : g⁻¹ * t * g ∈ T := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) t).mp ht
          simpa using this
        have hzs := (Subgroup.mem_centralizer_iff.mp hzC) _ hs
        calc t * (g * z * g⁻¹) = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [hzs]
          _ = g * z * g⁻¹ * t := by group
      · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem conj_mem_conjClosure {Z H : Subgroup G} {g : G}
    (hgZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) (hgH : ∀ h ∈ H, g * h * g⁻¹ ∈ H) {x : G}
    (hx : x ∈ conjClosure Z H) : g * x * g⁻¹ ∈ conjClosure Z H := by
  have hle : conjClosure Z H ≤ (conjClosure Z H).comap (MulAut.conj g).toMonoidHom := by
    refine conjClosure_le fun h hh z hz => ?_
    show (MulAut.conj g) (h * z * h⁻¹) ∈ conjClosure Z H
    rw [MulAut.conj_apply]
    have := mem_conjClosure (hgH h hh) (hgZ z hz)
    rw [show g * (h * z * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ by
      group]
    exact this
  exact hle hx

end Conj

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace Hyp1421

theorem ne_centralizer (h : Hyp1421 G T M) :
    M ≠ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro heq
  obtain ⟨M', hM', hne⟩ := h.two_maximal
  have hle : M' ≤ M := le_of_ordLE_of_centralizer_le (h.m_greatest M' hM') heq.ge
  exact hne (hM'.1.2 M h.m_max.1.1.1 hle).symm

theorem toQTFE14 (h : Hyp1421 G T M) :
    quasithinQTFE14Cat G T (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) where
  simple := h.simple
  nonabelian := h.nonabelian
  qtke := h.qtke
  sylow := h.sylow
  faithful_empty := h.faithful_empty
  mc_max := h.mc_max
  t_le_mc := Subgroup.le_centralizer_iff.mp
    ((quasithinOmegaOneCenter_le_center T).trans inf_le_right)
  centralizer_le_mc := le_rfl
  mc_unique := fun M' hM' hle => h.mc_max.2 M' hM'.1 hle
  two_maximal := ⟨M, h.m_max.1.1, h.m_max.1.2, h.ne_centralizer⟩

theorem card_omegaOneCenter (h : Hyp1421 G T M) : Nat.card (quasithinOmegaOneCenter T) = 2 :=
  card_omegaOneCenter_eq_two_of_card_VZ_eq_four h.toQTFE14 h.m_max.1 h.ne_centralizer h.rank_two

theorem inM_iff (h : Hyp1421 G T M) {K : Subgroup G} :
    InM T K ↔ K = M ∨ K = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  constructor
  · intro hK
    by_cases hKM : K = M
    · exact Or.inl hKM
    right
    obtain ⟨S, hS⟩ := h.toQTFE14.exists_sylow
    have hv : ∀ K, InM T K → IsHv T K := fun K hK => by
      have := isHv_of_inM h.qtke.2.1 S (hS ▸ hK)
      rwa [hS] at this
    have hVle : VZ T K ≤ VZ T M := VZ_le_of_ordLE (h.m_greatest K hK)
    have hVne : VZ T K ≠ VZ T M := fun heq => hKM (eq_of_VZ_eq (hv K hK) (hv M h.m_max.1) heq)
    have hcard := card_le_two_of_le_of_ne_of_card_four hVle hVne h.rank_two
    have hVZ : quasithinOmegaOneCenter T = VZ T K :=
      Subgroup.eq_of_le_of_card_ge (le_conjClosure _ _) (by rw [h.card_omegaOneCenter]; exact hcard)
    have hKN : K ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      hVZ ▸ le_normalizer_conjClosure _ _
    have hKC := hKN.trans (normalizer_le_centralizer_of_card_two h.card_omegaOneCenter)
    exact (hK.1.2 _ h.mc_max.1 hKC).symm
  · rintro (rfl | rfl)
    · exact h.m_max.1
    · exact h.toQTFE14.inM_mc

private theorem s142_normalizer_VZ_eq {Mc : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    {K : Subgroup G} (hK : InM T K) : Subgroup.normalizer (VZ T K : Set G) = K := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hSK : (S : Subgroup G) ≤ K := hS ▸ hK.2
  have hF : K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K :=
    h.qtke.2.1 K hK.1.1 ⟨S, hSK⟩
  have hVred : IsTwoReducedIn K (VZ T K) := by
    have := isTwoReducedIn_conjClosure K S hSK hF le_rfl
    rwa [hS] at this
  have hVne : VZ T K ≠ ⊥ := fun hb =>
    h.omegaOneCenter_ne_bot (le_bot_iff.mp (hb ▸ le_conjClosure _ _))
  exact hK.1.2 _ ⟨_, hVne, isPGroup_of_isElemAbelian hVred.2.2.1, rfl⟩ hVred.2.1

theorem normalizer_le (h : Hyp1421 G T M) :
    Subgroup.normalizer (T : Set G) ≤
      M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hNZ := normalizer_le_normalizer_quasithinOmegaOneCenter T
  have hNC : Subgroup.normalizer (T : Set G) ≤
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    hNZ.trans (normalizer_le_centralizer_of_card_two h.card_omegaOneCenter)
  refine le_inf (fun g hg => ?_) hNC
  have hgZ : ∀ z ∈ quasithinOmegaOneCenter T, g * z * g⁻¹ ∈ quasithinOmegaOneCenter T :=
    fun z hz => (Subgroup.mem_normalizer_iff.mp (hNZ hg) z).mp hz
  have hgZ' : ∀ z ∈ quasithinOmegaOneCenter T, g⁻¹ * z * g⁻¹⁻¹ ∈ quasithinOmegaOneCenter T :=
    fun z hz => (Subgroup.mem_normalizer_iff.mp (hNZ (inv_mem hg)) z).mp hz
  set Mg : Subgroup G := M.map (MulAut.conj g).toMonoidHom with hMg
  have hmemMg : ∀ x, x ∈ Mg ↔ g⁻¹ * x * g ∈ M := by
    intro x
    rw [hMg, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hMgloc : quasithinIsMaxTwoLocal Mg := by
    have h1 := h.m_max.1.1
    refine ⟨?_, fun H hH hle => ?_⟩
    · obtain ⟨P, hP, hP2, hPM⟩ := h1.1
      refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, hP2.map _, ?_⟩
      · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
      · rw [hMg, hPM]
        exact Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)
    ·
      have hH' : IsTwoLocal (H.map (MulAut.conj g⁻¹).toMonoidHom) := by
        obtain ⟨P, hP, hP2, hPH⟩ := hH
        refine ⟨P.map (MulAut.conj g⁻¹).toMonoidHom, ?_, hP2.map _, ?_⟩
        · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective]
        · rw [hPH]
          exact Subgroup.map_equiv_normalizer_eq P (MulAut.conj g⁻¹)
      have hMH : M ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
        intro m hm
        rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
        apply hle
        rw [hmemMg]
        simpa [mul_assoc] using hm
      have heq := h1.2 _ hH' hMH
      ext x
      rw [hmemMg, ← heq, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  have hTMg : T ≤ Mg := by
    intro t ht
    rw [hmemMg]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) t).mp ht
    simp only [inv_inv] at this
    exact h.m_max.1.2 this
  rcases h.inM_iff.mp ⟨hMgloc, hTMg⟩ with hMgM | hMgC
  ·
    have hgM : ∀ m ∈ M, g * m * g⁻¹ ∈ M := fun m hm => by
      rw [← hMgM, hmemMg]
      simpa [mul_assoc] using hm
    have hgM' : ∀ m ∈ M, g⁻¹ * m * g⁻¹⁻¹ ∈ M := fun m hm => by
      rw [inv_inv, ← (hmemMg m)]
      rwa [hMgM]
    have hgV : g ∈ Subgroup.normalizer (VZ T M : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨conj_mem_conjClosure hgZ hgM, fun hx => ?_⟩
      have := conj_mem_conjClosure hgZ' hgM' hx
      show x ∈ conjClosure (quasithinOmegaOneCenter T) M
      simpa [mul_assoc] using this
    rw [← s142_normalizer_VZ_eq h.toQTFE14 h.m_max.1]
    exact hgV
  ·
    exfalso
    have hgC := hNC hg
    have hMC : M ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      intro m hm
      have h1 : g * m * g⁻¹ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
        rw [← hMgC, hmemMg]
        simpa [mul_assoc] using hm
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hgC) h1) hgC
      simpa [mul_assoc] using this
    exact h.ne_centralizer (h.m_max.1.1.2 _ h.mc_max.1 hMC).symm

theorem isUniqueM_centralizer (h : Hyp1421 G T M) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ M) :
    IsUniqueM H (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
  have key : ∀ M', InM H M' →
      M' = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro M' hM'
    rcases h.inM_iff.mp ⟨hM'.1, hH.1.trans hM'.2⟩ with rfl | hc
    · exact absurd hM'.2 hHM
    · exact hc
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hH.2
  exact ⟨key M' hM' ▸ hM', key⟩

theorem minParabolic (h : Hyp1421 G T M) {H : Subgroup G} (hH : IsHStar T M H) :
    MinParabolic H T (H ⊓ M) := by
  obtain ⟨S, hS⟩ := h.toQTFE14.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ h.m_max.1.2
  have hH' : IsHStar (S : Subgroup G) M H := hS ▸ hH
  have hN : Subgroup.normalizer (T : Set G) ≤ M := h.normalizer_le.trans inf_le_left
  refine ⟨?_, hH.not_le_normalizer hN, ?_⟩
  · have := isSylowTwoOf_of_sylow S (hS ▸ hH.1.1)
    rwa [hS] at this
  · have := hH'.isUniqueMaxOver S hSM
    rwa [hS] at this

end Hyp1421

end CFSG.Quasithin
