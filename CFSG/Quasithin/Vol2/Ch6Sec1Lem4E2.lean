module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4E1
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_mem_cComp_ch614 {H K : Subgroup G} {g : G} (hK : K ∈ cComp H) (hg : g ∈ H) :
    K.map (MulAut.conj g).toMonoidHom ∈ cComp H := by
  have h := cComp_map_mulEquiv (MulAut.conj g) hK
  rwa [show H.map (MulAut.conj g).toMonoidHom = H from
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)] at h

omit [Finite G] in
theorem mem_map_conj_ch614 {K : Subgroup G} {g x : G} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

omit [Finite G] in
theorem conj_mem_map_conj_ch614 {K : Subgroup G} {g k : G} (hk : k ∈ K) :
    g * k * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
  mem_map_conj_ch614.mpr (by simpa [mul_assoc] using hk)

theorem le_centralizerMod_of_commutator_ch614 {M₁ K Y : Subgroup G} (hYM : Y ≤ M₁)
    (hc : ⁅Y, K⁆ ≤ pCoreOf 2 K) : Y ≤ centralizerMod (pCoreOf 2 K) M₁ K := by
  intro y hy
  have hyc : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 K := fun k hk => by
    have := hc (Subgroup.commutator_mem_commutator hy hk)
    rwa [commutatorElement_def] at this
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := by
    apply mem_normalizer_of_conj_mem_ch614
    intro k hk
    have e : y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k := by group
    rw [e]
    exact K.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 K (hyc k hk)) hk
  exact ⟨hYM hy, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hyK, hyc⟩


theorem conjClosure_le_sup_ch614 (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {M₁ K₁ T : Subgroup G}
    (hM₁ : pCoreOf 2 M₁ ≠ ⊥) (hK₁ : K₁ ∈ cComp M₁) (hTM : T ≤ M₁) :
    conjClosure K₁ T ≤ K₁ ⊔ centralizerMod (pCoreOf 2 K₁) M₁ K₁ := by
  refine conjClosure_le fun t ht k hk => ?_
  have hK' : K₁.map (MulAut.conj t).toMonoidHom ∈ cComp M₁ :=
    map_conj_mem_cComp_ch614 hK₁ (hTM ht)
  have hk' : t * k * t⁻¹ ∈ K₁.map (MulAut.conj t).toMonoidHom := conj_mem_map_conj_ch614 hk
  by_cases heq : K₁.map (MulAut.conj t).toMonoidHom = K₁
  · rw [heq] at hk'
    exact (le_sup_left : K₁ ≤ K₁ ⊔ centralizerMod (pCoreOf 2 K₁) M₁ K₁) hk'
  · have hc := (lemma_1_2_1_two hK hs hnab h37 hM₁ hK' hK₁ heq).1
    have hle := le_centralizerMod_of_commutator_ch614 (le_of_mem_cComp hK')
      (hc.trans inf_le_right)
    exact (le_sup_right : centralizerMod (pCoreOf 2 K₁) M₁ K₁ ≤ _) (hle hk')

theorem le_normalizer_of_le_ch614 (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {M₁ K₁ T X : Subgroup G}
    (hM₁ : pCoreOf 2 M₁ ≠ ⊥) (hK₁ : K₁ ∈ cComp M₁) (hTM : T ≤ M₁)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hXK : X ≤ K₁)
    (hX : ¬ ⁅X, K₁⁆ ≤ pCoreOf 2 K₁) : T ≤ Subgroup.normalizer (K₁ : Set G) := by
  intro t ht
  have hK' : K₁.map (MulAut.conj t).toMonoidHom ∈ cComp M₁ :=
    map_conj_mem_cComp_ch614 hK₁ (hTM ht)
  have hXK' : X ≤ K₁.map (MulAut.conj t).toMonoidHom := by
    intro x hx
    rw [mem_map_conj_ch614]
    apply hXK
    have := (Subgroup.mem_normalizer_iff.mp (hTX (T.inv_mem ht)) x).mp hx
    simpa using this
  by_cases heq : K₁.map (MulAut.conj t).toMonoidHom = K₁
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  · exfalso
    have hc := (lemma_1_2_1_two hK hs hnab h37 hM₁ hK' hK₁ heq).1
    exact hX ((Subgroup.commutator_mono hXK' le_rfl).trans (hc.trans inf_le_right))

theorem le_normalizer_of_commutator_le_ch614 {A B : Subgroup G} (h : ⁅A, B⁆ ≤ B) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  apply mem_normalizer_of_conj_mem_ch614
  intro b hb
  have hc := h (Subgroup.commutator_mem_commutator ha hb)
  rw [commutatorElement_def] at hc
  have e : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
  rw [e]
  exact B.mul_mem hc hb

theorem conj_le_normalizer_conj_ch614 (hK : quasithinIsQTKECat G) (hsG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {M₁ K₁ T : Subgroup G}
    (hM₁ : pCoreOf 2 M₁ ≠ ⊥) (hK₁ : K₁ ∈ cComp M₁) (hTM : T ≤ M₁) :
    ∀ s ∈ T, ∀ t ∈ T, K₁.map (MulAut.conj s).toMonoidHom ≤
      Subgroup.normalizer ((K₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro s hs t ht
  have hKs := map_conj_mem_cComp_ch614 hK₁ (hTM hs)
  have hKt := map_conj_mem_cComp_ch614 hK₁ (hTM ht)
  by_cases heq : K₁.map (MulAut.conj s).toMonoidHom = K₁.map (MulAut.conj t).toMonoidHom
  · rw [heq]
    exact Subgroup.le_normalizer
  · apply le_normalizer_of_commutator_le_ch614
    have hc := (lemma_1_2_1_two hK hsG hnab h37 hM₁ hKs hKt heq).1
    exact hc.trans (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))

end CFSG.Quasithin.H13
