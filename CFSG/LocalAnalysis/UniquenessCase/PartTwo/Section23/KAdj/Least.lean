module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

theorem least_invariant {G : Type*} [Group G] [Finite G] {Fam : Set (Subgroup G)}
    {Pα : Subgroup G} (hle : ∀ P ∈ Fam, Pα ≤ P) (σ : G ≃* G)
    (hσ : Pα.map σ.toMonoidHom ∈ Fam) : Pα.map σ.toMonoidHom = Pα := by
  refine (Subgroup.eq_of_le_of_card_ge (hle _ hσ) ?_).symm
  rw [Subgroup.card_map_of_injective σ.injective]

theorem minimal_good_eq_of_least {G : Type*} [Group G] {Good : Subgroup G → Prop}
    {Pα P : Subgroup G} (hgood : Good Pα) (hle : ∀ Q, Good Q → Pα ≤ Q)
    (hmin : Minimal Good P) : P = Pα :=
  (minimal_iff_eq hgood hle).1 hmin

theorem map_conj_eq_iff_map_normalizerMonoidHom_eq {G : Type*} [Group G] (H : Subgroup G) {t : G}
    (ht : t ∈ Subgroup.normalizer (H : Set G)) (P : Subgroup ↥H) :
    (P.map H.subtype).map (MulAut.conj t).toMonoidHom = P.map H.subtype ↔
      P.map (H.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom = P := by
  have hcomm : H.subtype.comp (H.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype := by
    ext h
    simp [MulAut.conj_apply]
  have key : (P.map (H.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom).map H.subtype =
      (P.map H.subtype).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomm]
  rw [← key]
  exact ⟨fun h => Subgroup.map_injective H.subtype_injective h, fun h => by rw [h]⟩

theorem map_conj_map_sylow_eq {G : Type*} [Group G] {p : ℕ} (H : Subgroup G) (S : Sylow p ↥H)
    (T : Subgroup G) (hTH : T ≤ Subgroup.normalizer (H : Set G)) (hT : IsPGroup p ↥T)
    (hST : (S : Subgroup ↥H).map H.subtype ≤ T) {t : G} (ht : t ∈ T) :
    ((S : Subgroup ↥H).map H.subtype).map (MulAut.conj t).toMonoidHom =
      (S : Subgroup ↥H).map H.subtype := by
  have key : ∀ {s : G}, s ∈ T →
      ((S : Subgroup ↥H).map H.subtype).map (MulAut.conj s).toMonoidHom ≤
        (S : Subgroup ↥H).map H.subtype := by
    intro s hs
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxH : s * (x : G) * s⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.1 (hTH hs) (x : G)).1 x.2
    have hxT : s * (x : G) * s⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem hs (hST ⟨x, hx, rfl⟩)) (T.inv_mem hs)
    have hQp : IsPGroup p (T.comap H.subtype) := hT.comap_subtype (K := H)
    have hSQ : (S : Subgroup ↥H) ≤ T.comap H.subtype := fun y hy => hST ⟨y, hy, rfl⟩
    have hQS : T.comap H.subtype = (S : Subgroup ↥H) := S.is_maximal' hQp hSQ
    have hmem : (⟨s * (x : G) * s⁻¹, hxH⟩ : ↥H) ∈ T.comap H.subtype := hxT
    rw [hQS] at hmem
    exact ⟨_, hmem, by simp [MulAut.conj_apply]⟩
  refine le_antisymm (key ht) ?_
  intro y hy
  exact ⟨(MulAut.conj t⁻¹).toMonoidHom y,
    key (T.inv_mem ht) ⟨y, hy, rfl⟩,
    by simp [MulAut.conj_apply, mul_assoc]⟩

theorem map_conj_eq_of_least_parabolic {G : Type} [Group G] (H : Subgroup G) [Finite ↥H]
    (S : Sylow 2 ↥H) (Pℓ : Subgroup ↥H) (T : Subgroup G)
    (hTH : T ≤ Subgroup.normalizer (H : Set G)) (hT : IsPGroup 2 ↥T)
    (hST : (S : Subgroup ↥H).map H.subtype ≤ T)
    (hPℓ : ∀ t ∈ T, (Pℓ.map H.subtype).map (MulAut.conj t).toMonoidHom = Pℓ.map H.subtype)
    {Pα : Subgroup ↥H} (hpar : IsParabolicTwo ↥H Pα) (hSP : (S : Subgroup ↥H) ≤ Pα)
    (hnot : ¬ Pα ≤ Pℓ)
    (hle : ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P → (S : Subgroup ↥H) ≤ P → ¬ P ≤ Pℓ → Pα ≤ P) :
    ∀ t ∈ T, (Pα.map H.subtype).map (MulAut.conj t).toMonoidHom = Pα.map H.subtype := by
  intro t ht
  rw [map_conj_eq_iff_map_normalizerMonoidHom_eq H (hTH ht) Pα]
  set σ : ↥H ≃* ↥H := H.normalizerMonoidHom ⟨t, hTH ht⟩
  have hSσ : (S : Subgroup ↥H).map σ.toMonoidHom = (S : Subgroup ↥H) :=
    (map_conj_eq_iff_map_normalizerMonoidHom_eq H (hTH ht) S).1
      (map_conj_map_sylow_eq H S T hTH hT hST ht)
  have hPσ : Pℓ.map σ.toMonoidHom = Pℓ :=
    (map_conj_eq_iff_map_normalizerMonoidHom_eq H (hTH ht) Pℓ).1 (hPℓ t ht)
  refine least_invariant
    (Fam := {P : Subgroup ↥H | IsParabolicTwo ↥H P ∧ (S : Subgroup ↥H) ≤ P ∧ ¬ P ≤ Pℓ})
    (fun P hP => hle P hP.1 hP.2.1 hP.2.2) σ
    ⟨IsParabolicTwo.map hpar σ.toMonoidHom σ.surjective, ?_, ?_⟩
  · calc (S : Subgroup ↥H) = (S : Subgroup ↥H).map σ.toMonoidHom := hSσ.symm
      _ ≤ Pα.map σ.toMonoidHom := Subgroup.map_mono hSP
  · intro hle'
    apply hnot
    rw [← hPσ] at hle'
    exact (Subgroup.map_le_map_iff_of_injective σ.injective).1 hle'

theorem minimal_good_eq_of_least_parabolic {G : Type} [Group G] (H : Subgroup G) [Finite ↥H]
    (S : Sylow 2 ↥H) (Pℓ : Subgroup ↥H) (T : Subgroup G)
    (hTH : T ≤ Subgroup.normalizer (H : Set G)) (hT : IsPGroup 2 ↥T)
    (hST : (S : Subgroup ↥H).map H.subtype ≤ T)
    (hPℓ : ∀ t ∈ T, (Pℓ.map H.subtype).map (MulAut.conj t).toMonoidHom = Pℓ.map H.subtype)
    {Pα : Subgroup ↥H} (hpar : IsParabolicTwo ↥H Pα) (hSP : (S : Subgroup ↥H) ≤ Pα)
    (hnot : ¬ Pα ≤ Pℓ)
    (hle : ∀ P : Subgroup ↥H, IsParabolicTwo ↥H P → (S : Subgroup ↥H) ≤ P → ¬ P ≤ Pℓ → Pα ≤ P)
    {P : Subgroup ↥H}
    (hmin : Minimal (fun Q : Subgroup ↥H => IsParabolicTwo ↥H Q ∧ (S : Subgroup ↥H) ≤ Q ∧
      (∀ t ∈ T, (Q.map H.subtype).map (MulAut.conj t).toMonoidHom = Q.map H.subtype) ∧
      ¬ Q ≤ Pℓ) P) :
    P = Pα := by
  refine minimal_good_eq_of_least
    ⟨hpar, hSP,
      map_conj_eq_of_least_parabolic H S Pℓ T hTH hT hST hPℓ hpar hSP hnot hle, hnot⟩
    (fun Q hQ => hle Q hQ.1 hQ.2.1 hQ.2.2.2) hmin

theorem map_conj_stabilizer_fixedPoint_eq {W : Type} [CommGroup W] (H : Subgroup (MulAut W))
    (S : Sylow 2 ↥H) (Tstar : Subgroup (MulAut W))
    (hTH : Tstar ≤ Subgroup.normalizer (H : Set (MulAut W))) (hT : IsPGroup 2 ↥Tstar)
    (hST : (S : Subgroup ↥H).map H.subtype ≤ Tstar) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    let ℓ : Subgroup W := CFSG.fixedPointSubgroup ↥S W
    let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
    ∀ t ∈ Tstar, (Pℓ.map H.subtype).map (MulAut.conj t).toMonoidHom = Pℓ.map H.subtype := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  intro ℓ Pℓ t ht
  have key : ∀ {s : MulAut W}, s ∈ Tstar → ∀ w ∈ ℓ, s w ∈ ℓ := by
    intro s hs w hw
    have hw' : ∀ x : ↥S, ((x : ↥H) : MulAut W) w = w := hw
    show ∀ x : ↥S, ((x : ↥H) : MulAut W) (s w) = s w
    intro x
    have hconj := map_conj_map_sylow_eq H S Tstar hTH hT hST (Tstar.inv_mem hs)
    have hmem : (MulAut.conj s⁻¹).toMonoidHom ((x : ↥H) : MulAut W) ∈
        (S : Subgroup ↥H).map H.subtype := by
      rw [← hconj]
      exact ⟨_, ⟨(x : ↥H), x.2, rfl⟩, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := hmem
    have h3 : H.subtype y w = w := hw' ⟨y, hy⟩
    rw [hyeq] at h3
    have h4 : s⁻¹ (((x : ↥H) : MulAut W) (s w)) = w := by
      simpa [MulAut.conj_apply] using h3
    calc ((x : ↥H) : MulAut W) (s w)
        = s (s⁻¹ (((x : ↥H) : MulAut W) (s w))) := by simp
      _ = s w := by rw [h4]
  have hℓ : ℓ.map t.toMonoidHom = ℓ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact key ht w hw
    · intro w hw
      exact ⟨t⁻¹ w, key (Tstar.inv_mem ht) w hw, by simp [MulAut.apply_inv_self]⟩
  have hstab := map_subtype_stabilizer_conj_normalizer t (hTH ht) ℓ
  rw [hℓ] at hstab
  exact hstab

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
