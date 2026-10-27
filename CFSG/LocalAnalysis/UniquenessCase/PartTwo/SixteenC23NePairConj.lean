module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_pairconj_mem_cTilde {M V₀ V : Subgroup G} {x : G} :
    x ∈ F11.CTilde M V₀ V ↔
      x ∈ M ∧ x ∈ Subgroup.normalizer (V₀ : Set G) ∧ ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ V₀ := by
  unfold F11.CTilde
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h
    have h1 := h 1 V.one_mem
    exact ⟨h1.1, h1.2.1, fun v hv => (h v hv).2.2⟩
  · rintro ⟨h1, h2, h3⟩ v hv
    exact ⟨h1, h2, h3 v hv⟩

theorem c23ne_cTilde_conj (M Y V : Subgroup G) (g : G) :
    F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g) =
      conjSubgroup (F11.CTilde M Y V) g := by
  ext x
  rw [mem_conjSubgroup_iff]
  simp only [c23ne_pairconj_mem_cTilde]
  constructor
  · rintro ⟨hxM, hxN, hx⟩
    refine ⟨mem_conjSubgroup_iff.1 hxM, ?_, ?_⟩
    · have hxN' : x ∈ conjSubgroup (Subgroup.normalizer (Y : Set G)) g := by
        rwa [E3.conjSubgroup_normalizer Y g]
      exact mem_conjSubgroup_iff.1 hxN'
    · intro v hv
      have hv' : g⁻¹ * v * g ∈ conjSubgroup V g := by
        rw [mem_conjSubgroup_iff]
        have h : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
        rwa [h]
      have h := hx (g⁻¹ * v * g) hv'
      rw [mem_conjSubgroup_iff] at h
      convert h using 1
      group
  · rintro ⟨hxM, hxN, hx⟩
    refine ⟨mem_conjSubgroup_iff.2 hxM, ?_, ?_⟩
    · rw [← E3.conjSubgroup_normalizer Y g]
      exact mem_conjSubgroup_iff.2 hxN
    · intro v hv
      have hv' : g * v * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hv
      have h := hx (g * v * g⁻¹) hv'
      rw [mem_conjSubgroup_iff]
      convert h using 1
      group

private theorem c23ne_pairconj_commElt_conj (W : Subgroup G) (t g : G) :
    commElt (conjSubgroup W g) t = conjSubgroup (commElt W (g * t * g⁻¹)) g := by
  apply le_antisymm
  · rw [commElt, Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    change w⁻¹ * t⁻¹ * w * t ∈ conjSubgroup (commElt W (g * t * g⁻¹)) g
    rw [mem_conjSubgroup_iff]
    refine Subgroup.subset_closure ⟨g * w * g⁻¹, mem_conjSubgroup_iff.1 hw, ?_⟩
    show g * (w⁻¹ * t⁻¹ * w * t) * g⁻¹ = _
    group
  · change Subgroup.map (MulAut.conj g⁻¹).toMonoidHom (commElt W (g * t * g⁻¹)) ≤
      commElt (conjSubgroup W g) t
    rw [commElt, MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨g⁻¹ * v * g, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have h : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
      rwa [h]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

private theorem c23ne_pairconj_mSub_conjSubgroup (A : Subgroup G) (g : G) :
    mSub (conjSubgroup A g) = mSub A := by
  unfold mSub rk
  rw [E3.card_conjSubgroup]

private theorem c23ne_pairconj_centralizer_singleton_conj (w g : G) :
    conjSubgroup (Subgroup.centralizer ({g * w * g⁻¹} : Set G)) g =
      Subgroup.centralizer ({w} : Set G) := by
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : g * (x * w) * g⁻¹ = g * (w * x) * g⁻¹ := by
      calc g * (x * w) * g⁻¹ = (g * x * g⁻¹) * (g * w * g⁻¹) := by group
        _ = (g * w * g⁻¹) * (g * x * g⁻¹) := h
        _ = g * (w * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  · intro h
    calc (g * x * g⁻¹) * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [h]
      _ = (g * w * g⁻¹) * (g * x * g⁻¹) := by group

private theorem c23ne_pairconj_mul_comm_conj {t y g : G}
    (h : (g * t * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * t * g⁻¹)) :
    t * y = y * t := by
  have h' : g * (t * y) * g⁻¹ = g * (y * t) * g⁻¹ := by
    calc g * (t * y) * g⁻¹ = (g * t * g⁻¹) * (g * y * g⁻¹) := by group
      _ = (g * y * g⁻¹) * (g * t * g⁻¹) := h
      _ = g * (y * t) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h')

private theorem c23ne_pairconj_mQuot_conj {M Y V N₁ N₂ : Subgroup G} (g : G)
    (hrank : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 2 E →
      (∀ e ∈ E, e ∈ normalizer (N₁ : Set G)) → (∀ e ∈ E, ∀ y ∈ N₂, e * y = y * e) →
        E3.mQuot E (F11.CTilde M Y V) ≤ 2)
    (E : Subgroup G) (hE : E ≤ conjSubgroup M g) (hEab : IsElemAbelian 2 E)
    (hEnorm : ∀ e ∈ E, e ∈ normalizer ((conjSubgroup N₁ g) : Set G))
    (hEcent : ∀ e ∈ E, ∀ y ∈ conjSubgroup N₂ g, e * y = y * e) :
    E3.mQuot E (F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g)) ≤ 2 := by
  have hE₀le : conjSubgroup E g⁻¹ ≤ M := by
    have h := E3.conjSubgroup_mono_left g⁻¹ hE
    rwa [E3.conjSubgroup_conj_inv M g] at h
  have hE₀ab : IsElemAbelian 2 (conjSubgroup E g⁻¹) :=
    E3.isElemAbelian_conjSubgroup hEab g⁻¹
  have hE₀norm : ∀ e ∈ conjSubgroup E g⁻¹, e ∈ normalizer (N₁ : Set G) := by
    have h := E3.conjSubgroup_mono_left g⁻¹ hEnorm
    rw [E3.conjSubgroup_normalizer (conjSubgroup N₁ g) g⁻¹,
      E3.conjSubgroup_conj_inv N₁ g] at h
    exact h
  have hE₀cent : ∀ e ∈ conjSubgroup E g⁻¹, ∀ y ∈ N₂, e * y = y * e := by
    intro e he y hy
    have he1 : g⁻¹ * e * g ∈ E := by simpa using mem_conjSubgroup_iff.1 he
    have hy1 : g⁻¹ * y * g ∈ conjSubgroup N₂ g := by
      rw [mem_conjSubgroup_iff]
      have h : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rwa [h]
    have h1 := hEcent (g⁻¹ * e * g) he1 (g⁻¹ * y * g) hy1
    have h2 : g⁻¹ * (e * y) * g = g⁻¹ * (y * e) * g := by
      calc g⁻¹ * (e * y) * g = (g⁻¹ * e * g) * (g⁻¹ * y * g) := by group
        _ = (g⁻¹ * y * g) * (g⁻¹ * e * g) := h1
        _ = g⁻¹ * (y * e) * g := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hres := hrank (conjSubgroup E g⁻¹) hE₀le hE₀ab hE₀norm hE₀cent
  have hq : E3.mQuot E
      (F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g)) =
      E3.mQuot (conjSubgroup E g⁻¹) (F11.CTilde M Y V) := by
    have h := E3.mQuot_conjSubgroup (conjSubgroup E g⁻¹) (F11.CTilde M Y V) g
    rw [E3.conjSubgroup_inv_conj E g, ← c23ne_cTilde_conj M Y V g] at h
    exact h
  rwa [hq]

theorem c23ne_pair_conj {M V₀ V N₁ N₂ Y : Subgroup G} (g : G) (h : C23NePair M V₀ V N₁ N₂ Y) :
    C23NePair (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) (conjSubgroup N₁ g)
      (conjSubgroup N₂ g) (conjSubgroup Y g) := by
  refine
    { elem := E3.isElemAbelian_conjSubgroup h.elem g
      norm := ?_
      normV₀ := ?_
      normY := ?_
      le₁ := E3.conjSubgroup_mono_left g h.le₁
      le₂ := E3.conjSubgroup_mono_left g h.le₂
      sup := ?_
      inf := ?_
      leY := E3.conjSubgroup_mono_left g h.leY
      rank_V := ?_
      rank_N₁ := ?_
      rank_N₂ := ?_
      rank_V₀ := ?_
      rank_Y := ?_
      perm := ?_
      cent := ?_
      oneSided := ?_
      rankLe := ?_
      rankLe' := ?_ }
  · rw [← E3.conjSubgroup_normalizer V g]
    exact E3.conjSubgroup_mono_left g h.norm
  · rw [← E3.conjSubgroup_normalizer V₀ g]
    exact E3.conjSubgroup_mono_left g h.normV₀
  · rw [← E3.conjSubgroup_normalizer Y g]
    exact E3.conjSubgroup_mono_left g h.normY
  · rw [← h.sup]
    exact (Subgroup.map_sup N₁ N₂ (MulAut.conj g⁻¹).toMonoidHom).symm
  · rw [← h.inf]
    exact (E3.conjSubgroup_inf N₁ N₂ g).symm
  · rw [c23ne_pairconj_mSub_conjSubgroup V g]; exact h.rank_V
  · rw [c23ne_pairconj_mSub_conjSubgroup N₁ g]; exact h.rank_N₁
  · rw [c23ne_pairconj_mSub_conjSubgroup N₂ g]; exact h.rank_N₂
  · rw [c23ne_pairconj_mSub_conjSubgroup V₀ g]; exact h.rank_V₀
  · rw [c23ne_pairconj_mSub_conjSubgroup Y g]; exact h.rank_Y
  · rintro m' hm'
    have hm : g * m' * g⁻¹ ∈ M := mem_conjSubgroup_iff.1 hm'
    have e₁ : conjSubgroup (conjSubgroup N₁ g) m' =
        conjSubgroup (conjSubgroup N₁ (g * m' * g⁻¹)) g := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    have e₂ : conjSubgroup (conjSubgroup N₂ g) m' =
        conjSubgroup (conjSubgroup N₂ (g * m' * g⁻¹)) g := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    obtain ⟨hn₁, hn₂⟩ | ⟨hn₁, hn₂⟩ := h.perm (g * m' * g⁻¹) hm
    · left
      exact ⟨by rw [e₁, hn₁], by rw [e₂, hn₂]⟩
    · right
      exact ⟨by rw [e₁, hn₁], by rw [e₂, hn₂]⟩
  · rintro w hw hw1
    have hw₀ : g * w * g⁻¹ ∈ (N₁ : Set G) ∪ (N₂ : Set G) := by
      rcases hw with hw | hw
      · exact Or.inl (mem_conjSubgroup_iff.1 hw)
      · exact Or.inr (mem_conjSubgroup_iff.1 hw)
    have hw₀1 : g * w * g⁻¹ ≠ 1 := by
      intro h1
      apply hw1
      have h2 : g * w * g⁻¹ = g * 1 * g⁻¹ := by simpa using h1
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← c23ne_pairconj_centralizer_singleton_conj w g]
    exact E3.conjSubgroup_mono_left g (h.cent (g * w * g⁻¹) hw₀ hw₀1)
  · rintro t' ht' ht'2 ht'V ht'm
    have ht : g * t' * g⁻¹ ∈ M := mem_conjSubgroup_iff.1 ht'
    have ht2 : (g * t' * g⁻¹) ^ 2 = 1 := by
      have h : (g * t' * g⁻¹) ^ 2 = g * t' ^ 2 * g⁻¹ := by
        rw [pow_two, pow_two]
        group
      rw [h, ht'2]
      simp
    have htV : ¬ V ≤ Subgroup.centralizer ({g * t' * g⁻¹} : Set G) := by
      intro hV
      apply ht'V
      have h1 := E3.conjSubgroup_mono_left g hV
      rwa [c23ne_pairconj_centralizer_singleton_conj t' g] at h1
    have htm : mSub (commElt V (g * t' * g⁻¹)) ≤ 2 := by
      have h1 := ht'm
      rwa [c23ne_pairconj_commElt_conj V t' g,
        c23ne_pairconj_mSub_conjSubgroup (commElt V (g * t' * g⁻¹)) g] at h1
    rcases h.oneSided (g * t' * g⁻¹) ht ht2 htV htm with ⟨h1, hY⟩ | ⟨h2, hinf, hblock⟩
    · left
      refine ⟨?_, ?_⟩
      · rwa [c23ne_pairconj_commElt_conj V t' g,
          c23ne_pairconj_mSub_conjSubgroup (commElt V (g * t' * g⁻¹)) g]
      · rw [c23ne_pairconj_commElt_conj V t' g, hY]
    · right
      refine ⟨?_, ?_, ?_⟩
      · rwa [c23ne_pairconj_commElt_conj V t' g,
          c23ne_pairconj_mSub_conjSubgroup (commElt V (g * t' * g⁻¹)) g]
      · rw [c23ne_pairconj_commElt_conj V t' g, ← E3.conjSubgroup_inf, hinf,
          E3.conjSubgroup_bot]
      · rcases hblock with ⟨hcomm, hle⟩ | ⟨hcomm, hle⟩
        · left
          refine ⟨?_, ?_⟩
          · intro y hy
            exact c23ne_pairconj_mul_comm_conj
              (hcomm (g * y * g⁻¹) (mem_conjSubgroup_iff.1 hy))
          · rw [c23ne_pairconj_commElt_conj V t' g]
            exact E3.conjSubgroup_mono_left g hle
        · right
          refine ⟨?_, ?_⟩
          · intro y hy
            exact c23ne_pairconj_mul_comm_conj
              (hcomm (g * y * g⁻¹) (mem_conjSubgroup_iff.1 hy))
          · rw [c23ne_pairconj_commElt_conj V t' g]
            exact E3.conjSubgroup_mono_left g hle
  · intro E hE hEab hEnorm hEcent
    exact c23ne_pairconj_mQuot_conj (M := M) (Y := Y) (V := V) (N₁ := N₁) (N₂ := N₂) g h.rankLe
      E hE hEab hEnorm hEcent
  · intro E hE hEab hEnorm hEcent
    exact c23ne_pairconj_mQuot_conj (M := M) (Y := Y) (V := V) (N₁ := N₂) (N₂ := N₁) g h.rankLe'
      E hE hEab hEnorm hEcent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
