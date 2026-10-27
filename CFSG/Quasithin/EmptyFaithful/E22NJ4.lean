module

public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.EmptyFaithful.A38c8J4
public import CFSG.Sporadic.J4.QT2LocZMain
public import CFSG.Sporadic.J4.QT2LocCntMain

public section

namespace CFSG.Quasithin

namespace E2P

open CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

namespace J4Two

theorem P0_le_centralizer :
    P0 ≤ Subgroup.centralizer ({eta uJ 11 1131} : Set J) := by
  have hZ := Zc_eq j4Facts.mat j4Facts 1 (by norm_num)
  have hmem : eta uJ 11 1131 ∈ Zc 1 := by
    rw [hZ]
    have hm : ucsMasks.getD 1 [] = [0, 1131] := rfl
    exact ⟨1131, by rw [hm]; simp, rfl⟩
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := hmem.2 x hx
  have h1 : eta uJ 11 1131 * x * (eta uJ 11 1131)⁻¹ * x⁻¹ = 1 := h
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

theorem exists_two_max_P0 :
    ∃ M₁ M₂ : Subgroup J, IsCoatom M₁ ∧ IsCoatom M₂ ∧ M₁ ≠ M₂ ∧ P0 ≤ M₁ ∧ P0 ≤ M₂ := by
  have hCne : Subgroup.centralizer ({eta uJ 11 1131} : Set J) ≠ ⊤ := by
    intro h
    have hc := card_centralizer_eta_1131
    rw [h, Subgroup.card_top, card_J j4Facts] at hc
    norm_num at hc
  obtain ⟨M₂, hM₂, hCM⟩ := (eq_top_or_exists_le_coatom _).resolve_left hCne
  obtain ⟨g, hg, hgH⟩ := centralizer_z0_not_le_Hj
  have hgC : g ∈ Subgroup.centralizer ({eta uJ 11 1131} : Set J) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hg
  have hP0 : P0 ≤ M₂ := le_trans P0_le_centralizer hCM
  refine ⟨Hj, M₂, isCoatom_Hj j4Facts, hM₂, ?_, P0_le_Hj, hP0⟩
  intro h
  exact hgH (h ▸ hCM hgC)

theorem isMaxSubgroupIn_top_iff {G : Type} [Group G] {N : Subgroup G} :
    IsMaxSubgroupIn ⊤ N ↔ IsCoatom N :=
  ⟨fun h => ⟨lt_top_iff_ne_top.mp h.1, fun b hb => h.2 b hb le_top⟩,
    fun h => ⟨lt_top_iff_ne_top.mpr h.1, fun K hK _ => h.2 K hK⟩⟩

@[expose] def TwoMaxSylow (G : Type) [Group G] : Prop :=
  ∀ S : Subgroup G, IsPGroup 2 S → ¬ 2 ∣ S.index →
    ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ M₁ ≠ M₂ ∧ S ≤ M₁ ∧ S ≤ M₂

theorem twoMaxSylow_of_mulEquiv {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')
    (h : TwoMaxSylow G') : TwoMaxSylow G := by
  intro S hS2 hSi
  have hS2' : IsPGroup 2 (S.map (φ : G →* G')) :=
    hS2.of_equiv (Subgroup.equivMapOfInjective S (φ : G →* G') φ.injective)
  have hSi' : ¬ 2 ∣ (S.map (φ : G →* G')).index := by
    rwa [Subgroup.index_map_equiv S φ]
  obtain ⟨M₁, M₂, h₁, h₂, hne, hS₁, hS₂⟩ := h _ hS2' hSi'
  have hcomp : ((φ.symm : G' →* G)).comp (φ : G →* G') = MonoidHom.id G := by
    ext x
    simp
  refine ⟨M₁.map (φ.symm : G' →* G), M₂.map (φ.symm : G' →* G), ?_, ?_, ?_, ?_, ?_⟩
  · exact (φ.symm.mapSubgroup.isCoatom_iff M₁).mpr h₁
  · exact (φ.symm.mapSubgroup.isCoatom_iff M₂).mpr h₂
  · intro h
    exact hne (φ.symm.mapSubgroup.injective h)
  · have := Subgroup.map_mono (f := (φ.symm : G' →* G)) hS₁
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at this
  · have := Subgroup.map_mono (f := (φ.symm : G' →* G)) hS₂
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at this

theorem twoMaxSylow_of_sylow {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index)
    (h : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ M₁ ≠ M₂ ∧ P ≤ M₁ ∧ P ≤ M₂) :
    TwoMaxSylow G := by
  intro S hS2 hSi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hP2.toSylow hPi) (hS2.toSylow hSi)
  have hgS : P.map (MulAut.conj g).toMonoidHom = S := by
    have h1 := congrArg (fun Q : Sylow 2 G => (Q : Subgroup G)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    exact h1
  obtain ⟨M₁, M₂, h₁, h₂, hne, hP₁, hP₂⟩ := h
  refine ⟨M₁.map (MulAut.conj g).toMonoidHom, M₂.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact ((MulAut.conj g).mapSubgroup.isCoatom_iff M₁).mpr h₁
  · exact ((MulAut.conj g).mapSubgroup.isCoatom_iff M₂).mpr h₂
  · intro h
    exact hne ((MulAut.conj g).mapSubgroup.injective h)
  · rw [← hgS]
    exact Subgroup.map_mono hP₁
  · rw [← hgS]
    exact Subgroup.map_mono hP₂

theorem P0_sylow :
    IsPGroup 2 P0 ∧ ¬ 2 ∣ P0.index := by
  have hc := card_P0 j4Facts.mat j4Facts
  refine ⟨IsPGroup.of_card hc, ?_⟩
  have h := Subgroup.card_mul_index P0
  rw [hc, card_J j4Facts] at h
  intro h2
  obtain ⟨k, hk⟩ := h2
  rw [hk] at h
  omega

theorem twoMaxSylow_J :
    TwoMaxSylow J :=
  twoMaxSylow_of_sylow P0_sylow.1 P0_sylow.2 exists_two_max_P0

theorem twoMaxSylow_carrier :
    TwoMaxSylow (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
  @twoMaxSylow_of_mulEquiv (CFSG.Blueprint.NativeSporadic.Carrier .J4) J _ _
    (seedEquiv j4Facts.mat) twoMaxSylow_J

end J4Two

theorem asc86bSporadic_holds :
    Asc86bSporadic := by
  intro H _ _ K T hKn hK hC hT hKT
  have : K.Normal := hKn
  have hodd := A38c8.odd_card_outer_of_isSporadic_j4 hK
  have hTK : T ≤ K := by
    intro t ht
    obtain ⟨a, ha⟩ := hT.2.1 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨n, hn, hconj⟩ := A38c8.exists_inner_of_odd_outer hodd hta
    have hc : n⁻¹ * t ∈ Subgroup.centralizer (K : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hconj x hx
      calc x * (n⁻¹ * t) = n⁻¹ * (n * x * n⁻¹) * t := by group
        _ = n⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
        _ = (n⁻¹ * t) * x := by group
    rw [hC, Subgroup.mem_bot] at hc
    have htn : t = n := by
      have := congrArg (n * ·) hc
      simpa using this
    exact htn ▸ hn
  have hKtop : K = ⊤ := by simpa [sup_eq_left.mpr hTK] using hKT
  obtain ⟨e⟩ := hK
  have h1 : J4Two.TwoMaxSylow ↥K := J4Two.twoMaxSylow_of_mulEquiv e J4Two.twoMaxSylow_carrier
  have h2 : J4Two.TwoMaxSylow H :=
    J4Two.twoMaxSylow_of_mulEquiv (((MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv).symm) h1
  have hTi : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
  obtain ⟨M₁, M₂, h₁, h₂, hne, hT₁, hT₂⟩ := h2 T hT.2.1 hTi
  exact ⟨M₁, M₂, J4Two.isMaxSubgroupIn_top_iff.mpr h₁, J4Two.isMaxSubgroupIn_top_iff.mpr h₂, hne,
    hT₁, hT₂⟩

end E2P

end CFSG.Quasithin
