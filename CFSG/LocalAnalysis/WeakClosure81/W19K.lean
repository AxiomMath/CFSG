module

public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Four

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem exists_isE (c : MinCex193 D V₀ V p X) {A : Subgroup G} (hAT : A ≤ D.T)
    (hAab : IsElemAbelian 2 A) (hXA : ¬ ⁅X, A⁆ ≤ pCoreOf 2 (X ⊔ D.T)) :
    ∃ K : Subgroup G, E1.IsE 1 (X ⊔ D.T) D.T A K := by
  classical
  haveI hp : Fact p.Prime := ⟨c.hyp.prime⟩
  haveI h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := X ⊔ D.T
  have hH : H = X ⊔ D.T := rfl
  have hXH : X ≤ H := by rw [hH]; exact le_sup_left
  have hTH : D.T ≤ H := by rw [hH]; exact le_sup_right
  have hAH : A ≤ H := hAT.trans hTH
  have hHcore : pCoreOf 2 H ≤ H := c.hyp.pCoreOf_le_T.trans hTH
  set Y : Subgroup ↥H := CFSG.pCore 2 ↥H with hY
  haveI : Y.Normal := CFSG.pCore_normal
  let π : ↥H →* ↥H ⧸ Y := QuotientGroup.mk' Y
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hπker : π.ker = Y := QuotientGroup.ker_mk' Y
  set T' : Subgroup ↥H := D.T.subgroupOf H with hT'
  set A' : Subgroup ↥H := A.subgroupOf H with hA'
  set X' : Subgroup ↥H := X.subgroupOf H with hX'
  have hT'syl : IsSylowIn 2 T' ⊤ := by
    have hTHsyl : IsSylowIn 2 D.T H := by rw [hH]; exact c.hyp.isSylowIn_T
    have := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := D.T) (K := H) (H := H)
      hTH le_rfl).mpr hTHsyl
    rwa [Subgroup.subgroupOf_self] at this
  have hA'T' : A' ≤ T' := by
    intro a ha
    have ha' : a ∈ A.subgroupOf H := by rwa [← hA']
    exact hAT (Subgroup.mem_subgroupOf.mp ha')
  have hAab' : IsElemAbelian 2 A' := by
    rw [hA']
    exact CFSG.Open.IsElemAbelian.subgroupOf hAab H
  have hX'p : IsPGroup p X' := by
    rw [hX']
    exact c.hyp.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
  let Xb : Subgroup (↥H ⧸ Y) := X'.map π
  let Abar : Subgroup (↥H ⧸ Y) := A'.map π
  have hYmap : Y.map π = ⊥ := by
    change Y.map (QuotientGroup.mk' Y) = ⊥
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hXYnormal : (X' ⊔ Y).Normal := by
    have hle : X ⊔ pCoreOf 2 H ≤ H := sup_le hXH hHcore
    have hN : ((X ⊔ pCoreOf 2 H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (by
        rw [hH]
        exact c.le_normalizer_sup_pCoreOf)
    have hsub : (X ⊔ pCoreOf 2 H).subgroupOf H = X' ⊔ Y := by
      have hmap : X ⊔ pCoreOf 2 H = (X' ⊔ Y).map H.subtype := by
        rw [hX', hY, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXH]
        rfl
      rw [hmap]
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective (X' ⊔ Y)
    rwa [hsub] at hN
  have hXb_eq : Xb = (X' ⊔ Y).map π := by
    rw [Subgroup.map_sup, hYmap, sup_bot_eq]
  have hXbNormal : Xb.Normal := hXb_eq ▸ hXYnormal.map π hπs
  have hXbP : IsPGroup p Xb := hX'p.map π
  have hAbarT : Abar ≤ T'.map π := Subgroup.map_mono hA'T'
  have hAbarab : IsElemAbelian 2 Abar := CFSG.Open.IsElemAbelian.map hAab' π
  have hTt : IsSylowIn 2 (T'.map π) ⊤ := E1.isSylowIn_two_map_top hπs hT'syl
  have hcomm_ne : ⁅Xb, Abar⁆ ≠ ⊥ := by
    intro hbot
    apply hXA
    have h1 : ⁅X', A'⁆ ≤ Y := by
      have hmap : (⁅X', A'⁆).map π = ⊥ := by
        rw [Subgroup.map_commutator]
        exact hbot
      have hle := hmap
      rw [Subgroup.map_eq_bot_iff] at hle
      rwa [hπker] at hle
    have h2 : (⁅X', A'⁆).map H.subtype ≤ Y.map H.subtype := Subgroup.map_mono h1
    have h3 : (⁅X', A'⁆).map H.subtype = ⁅X, A⁆ := by
      rw [Subgroup.map_commutator, hX', hA',
        Subgroup.map_subgroupOf_eq_of_le hXH, Subgroup.map_subgroupOf_eq_of_le hAH]
    have h4 : Y.map H.subtype = pCoreOf 2 H := by rw [hY]; rfl
    rwa [h3, h4] at h2
  let S : Set (Subgroup (↥H ⧸ Y)) :=
    {K | E1.IsE 1 ⊤ (T'.map π) (A'.map π) K ∧
      E1.EOne ↥K ((A'.map π).subgroupOf K) ∧
      Nat.card (E1.barO2 ↥K ((A'.map π).subgroupOf K)) ≤ 2 ^ 1}
  haveI : Xb.Normal := hXbNormal
  have hle : ⁅Xb, Abar⁆ ≤ ⨆ K ∈ S, twoResidual K :=
    E1.comm_le_iSup_twoResidual (G := ↥H ⧸ Y) c.hyp.prime c.hyp.odd hTt hAbarT hAbarab hXbP
  have hSne : S.Nonempty := by
    by_contra hne
    have hbot : (⨆ K ∈ S, twoResidual K) = ⊥ := by
      rw [iSup₂_eq_bot]
      intro K hK
      exact (hne ⟨K, hK⟩).elim
    exact hcomm_ne (le_bot_iff.mp (hbot ▸ hle))
  obtain ⟨Ktilde, hKtilde⟩ := hSne
  have hKIsE : E1.IsE 1 ⊤ (T'.map π) (A'.map π) Ktilde := by
    have hKtilde' : E1.IsE 1 ⊤ (T'.map π) (A'.map π) Ktilde ∧
        E1.EOne ↥Ktilde ((A'.map π).subgroupOf Ktilde) ∧
        Nat.card (E1.barO2 ↥Ktilde ((A'.map π).subgroupOf Ktilde)) ≤ 2 ^ 1 := by
      simpa only [S, Set.mem_setOf_eq] using hKtilde
    exact hKtilde'.1
  obtain ⟨J, hJ, -⟩ :=
    E1.ten_seven (G := ↥H) (Y := Y) hT'syl hA'T' hAab' hKIsE
  refine ⟨J.map H.subtype, ?_⟩
  have hJ' : E1.IsE 1 H (T'.map H.subtype) (A'.map H.subtype) (J.map H.subtype) :=
    (E1.isE_map_subtype H (i := 1) (T' := T') (A' := A') (K' := J)).mpr hJ
  rw [hT', hA', Subgroup.map_subgroupOf_eq_of_le hTH,
    Subgroup.map_subgroupOf_eq_of_le hAH] at hJ'
  change E1.IsE 1 H D.T A (J.map H.subtype)
  exact hJ'

theorem exists_conf196 (c : MinCex193 D V₀ V p X) {g : G} (hg : conjSubgroup V g ≤ D.T)
    (hXA : ¬ ⁅X, conjSubgroup V g⁆ ≤ pCoreOf 2 (X ⊔ D.T)) :
    ∃ K : Subgroup G, Conf196 D V X g K := by
  obtain ⟨K, hK⟩ := c.exists_isE hg (E3.isElemAbelian_conjSubgroup c.setting.isElemAbelian g) hXA
  exact ⟨K, ⟨hg, hK⟩⟩

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
