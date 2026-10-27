module

public import CFSG.Quasithin.Vol2.Ch10SecKRTa
public import CFSG.Quasithin.Vol2.Ch10SecQ9H59

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

omit [Finite G] in
theorem mem_normalizer_of_map_eq {X : Subgroup G} {t : G}
    (h : X.map (MulAut.conj t).toMonoidHom = X) : t ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨x, hx, hxg⟩ := hg
    have : x = g := by simpa [MulAut.conj_apply] using hxg
    rwa [← this]

theorem orbit (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (cfg : B0KConfig G T L I H K M₁ J n m) (hTJ : ¬ T ≤ Subgroup.normalizer (J : Set G)) :
    ∃ t ∈ T, J.map (MulAut.conj t).toMonoidHom ≠ J ∧
      J.map (MulAut.conj t).toMonoidHom ∈ cComp M₁ ∧
      (∀ s ∈ M₁, J.map (MulAut.conj s).toMonoidHom = J ∨
        J.map (MulAut.conj s).toMonoidHom = J.map (MulAut.conj t).toMonoidHom) ∧
      IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) := by
  rcases Vol2Native.lemma_1_2_1_three (localSQTK cfg) h37 h38 (pCoreOf_ne_bot cfg) cfg.hJ with
    hn | ⟨h2, hA⟩
  · exact absurd ((T_le cfg).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (J_le cfg)).mp hn)) hTJ
  obtain ⟨t, ht, htJ⟩ := IsConcreteLE.not_le_iff_exists.mp hTJ
  have hne : J.map (MulAut.conj t).toMonoidHom ≠ J := fun h => htJ (mem_normalizer_of_map_eq h)
  have hJt : J.map (MulAut.conj t).toMonoidHom ∈ cComp M₁ :=
    LocDbl.map_conj_mem_cComp cfg.hJ (Subgroup.le_normalizer (T_le cfg ht))
  refine ⟨t, ht, hne, hJt, fun s hs => ?_, Vol2Native.L122A.isSimpleGroup_of_a38Types hA⟩
  by_contra hcon
  push Not at hcon
  have hfin : (conjSubgroupsBy M₁ J).Finite := Set.toFinite _
  have h1 : J ∈ conjSubgroupsBy M₁ J := ⟨1, M₁.one_mem, by ext x; simp⟩
  have h3 : ({J, J.map (MulAut.conj t).toMonoidHom, J.map (MulAut.conj s).toMonoidHom} :
      Set (Subgroup G)) ⊆ conjSubgroupsBy M₁ J := by
    rintro X (rfl | rfl | rfl)
    · exact h1
    · exact ⟨t, T_le cfg ht, rfl⟩
    · exact ⟨s, hs, rfl⟩
  have h4 := Set.ncard_le_ncard h3 hfin
  rw [Set.ncard_eq_three.mpr ⟨_, _, _, hne.symm, (Ne.symm hcon.1), (Ne.symm hcon.2), rfl⟩,
    h2] at h4
  omega

omit [Finite G] in
theorem map_conj_map_conj (X : Subgroup G) (s t : G) :
    (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom =
      X.map (MulAut.conj (s * t)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem T_le_normalizer_sup (cfg : B0KConfig G T L I H K M₁ J n m) {t : G} (ht : t ∈ T)
    (horb : ∀ s ∈ M₁, J.map (MulAut.conj s).toMonoidHom = J ∨
      J.map (MulAut.conj s).toMonoidHom = J.map (MulAut.conj t).toMonoidHom) :
    T ≤ Subgroup.normalizer ((J ⊔ J.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have hle : ∀ s ∈ M₁, J.map (MulAut.conj s).toMonoidHom ≤ J ⊔ J.map (MulAut.conj t).toMonoidHom :=
    fun s hs => by
      rcases horb s hs with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
  have hmap : ∀ s ∈ T, (J ⊔ J.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom ≤
      J ⊔ J.map (MulAut.conj t).toMonoidHom := fun s hs => by
    rw [Subgroup.map_sup, map_conj_map_conj]
    exact sup_le (hle s (T_le cfg hs)) (hle _ (M₁.mul_mem (T_le cfg hs) (T_le cfg ht)))
  exact fun s hs => SecB.mem_normalizer_of_map_le (hmap s hs) (hmap s⁻¹ (T.inv_mem hs))

theorem conjClosure_K_le (cfg : B0KConfig G T L I H K M₁ J n m) {t : G}
    (horb : ∀ s ∈ M₁, J.map (MulAut.conj s).toMonoidHom = J ∨
      J.map (MulAut.conj s).toMonoidHom = J.map (MulAut.conj t).toMonoidHom) :
    conjClosure K T ≤ J ⊔ J.map (MulAut.conj t).toMonoidHom := by
  refine conjClosure_le fun s hs k hk => ?_
  have hmem : s * k * s⁻¹ ∈ J.map (MulAut.conj s).toMonoidHom := ⟨k, cfg.hKJ hk, rfl⟩
  rcases horb s (T_le cfg hs) with h | h <;> rw [h] at hmem
  · exact Subgroup.mem_sup_left hmem
  · exact Subgroup.mem_sup_right hmem

theorem commutator_le_pCoreOf (h37 : Vol2Native.A37ForSQTKCat)
    (cfg : B0KConfig G T L I H K M₁ J n m) {J' : Subgroup G} (hJ' : J' ∈ cComp M₁)
    (hne : J' ≠ J) : ⁅J, J'⁆ ≤ pCoreOf 2 M₁ := by
  have hbar : modO2Image M₁ J ≠ modO2Image M₁ J' := fun h =>
    hne ((modO2Image_injOn M₁ cfg.hJ hJ' h).symm)
  have hc := h37 _ (sqtkHypCat_bar cfg) _ (Jbar_mem_cComp cfg) _ (modO2Image_mem_cComp hJ') hbar
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haM : a ∈ M₁ := J_le cfg ha
  have hbM : b ∈ M₁ := le_of_mem_cComp hJ' hb
  have hmem : ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨a, haM⟩,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨b, hbM⟩⁆ ∈ ⁅modO2Image M₁ J, modO2Image M₁ J'⁆ :=
    Subgroup.commutator_mem_commutator ⟨⟨a, haM⟩, ha, rfl⟩ ⟨⟨b, hbM⟩, hb, rfl⟩
  rw [hc, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
