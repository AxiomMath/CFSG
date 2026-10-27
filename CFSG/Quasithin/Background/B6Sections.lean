module

public import CFSG.Quasithin.Background.B6Maschke
public import CFSG.Quasithin.Background.B6Struct
public import CFSG.Quasithin.Background.B6Aut
public import CFSG.GroupTheory.SolvableHallNodes
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

variable {G : Type*} [Group G]

namespace B6

section Surj

variable {X Y : Type*} [Group X] [Group Y] {φ : X →* Y}

theorem isMaxSubgroupIn_top_iff {U : Subgroup X} : IsMaxSubgroupIn ⊤ U ↔ IsCoatom U := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨lt_top_iff_ne_top.mp h1, fun b hb => h2 b hb le_top⟩
  · rintro ⟨h1, h2⟩
    exact ⟨lt_top_iff_ne_top.mpr h1, fun b hb _ => h2 b hb⟩

theorem comap_map_eq_of_ker_le {U : Subgroup X} (hU : φ.ker ≤ U) : (U.map φ).comap φ = U := by
  rw [Subgroup.comap_map_eq, sup_eq_left.mpr hU]

theorem isCoatom_map_of_surjective (hφ : Function.Surjective φ) {U : Subgroup X}
    (hU : φ.ker ≤ U) (hc : IsCoatom U) : IsCoatom (U.map φ) := by
  have h1 : (U.map φ).comap φ = U := comap_map_eq_of_ker_le hU
  refine ⟨?_, fun V hV => ?_⟩
  · intro htop
    apply hc.1
    rw [← h1, htop, Subgroup.comap_top]
  · have hlt : U < V.comap φ := by
      rw [← h1]
      exact (Subgroup.comap_lt_comap_of_surjective hφ).mpr hV
    have := hc.2 _ hlt
    rw [← Subgroup.map_comap_eq_self_of_surjective hφ V, this, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hφ]

theorem kerIn_map_top (hφ : Function.Surjective φ) {M : Subgroup X} (hM : φ.ker ≤ M) :
    kerIn (M.map φ) ⊤ = (kerIn M ⊤).map φ := by
  have hnorm : (⊤ : Subgroup X) ≤ Subgroup.normalizer (φ.ker : Set X) :=
    (Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker φ)).ge
  have hker : φ.ker ≤ kerIn M ⊤ := le_kerIn_of_le_normalizer hM hnorm
  have hcm : (M.map φ).comap φ = M := comap_map_eq_of_ker_le hM
  ext y
  obtain ⟨x, rfl⟩ := hφ y
  have hJ : φ x ∈ (kerIn M ⊤).map φ ↔ x ∈ kerIn M ⊤ := by
    rw [← Subgroup.mem_comap, comap_map_eq_of_ker_le hker]
  rw [hJ]
  constructor
  · intro hx c _
    have := hx (φ c) (Subgroup.mem_top _)
    rw [← map_mul, ← map_inv, ← map_mul] at this
    rw [← hcm]
    exact this
  · intro hx b _
    obtain ⟨c, rfl⟩ := hφ b
    refine ⟨c * x * c⁻¹, hx c (Subgroup.mem_top _), ?_⟩
    simp

theorem twoResidual_map_top [Finite X] (hφ : Function.Surjective φ) :
    (twoResidual (⊤ : Subgroup X)).map φ = twoResidual (⊤ : Subgroup Y) := by
  have : Finite Y := Finite.of_surjective φ hφ
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine twoResidual_le_of_isTwoQuotient le_top ?_ ?_
    · have hn : (twoResidual (⊤ : Subgroup Y)).Normal :=
        Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
      exact (Subgroup.normalizer_eq_top_iff.mpr (hn.comap φ)).ge
    · intro x _
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup Y) (φ x) (Subgroup.mem_top _)
      exact ⟨k, by simpa using hk⟩
  · refine twoResidual_le_of_isTwoQuotient le_top ?_ ?_
    · have hn : (twoResidual (⊤ : Subgroup X)).Normal :=
        Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
      exact (Subgroup.normalizer_eq_top_iff.mpr (hn.map φ hφ)).ge
    · intro y _
      obtain ⟨x, rfl⟩ := hφ y
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup X) x (Subgroup.mem_top _)
      exact ⟨k, ⟨x ^ 2 ^ k, hk, by simp⟩⟩

theorem isSylowTwoOf_map_top (hφ : Function.Surjective φ) [Finite X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map φ) ⊤ := by
  refine ⟨le_top, hT.2.1.map φ, ?_⟩
  have h1 : (T.map φ).index ∣ T.index := Subgroup.index_map_dvd T hφ
  have e1 : ((T.map φ).subgroupOf ⊤).index = (T.map φ).index :=
    Subgroup.relIndex_top_right (T.map φ)
  have e2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  rw [e1]
  intro hd
  apply hT.2.2
  rw [e2]
  exact hd.trans h1

end Surj

end B6

theorem MinParabolic.map_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X]
    {φ : X →* Y} {T M : Subgroup X} (h : MinParabolic (⊤ : Subgroup X) T M)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ M) :
    MinParabolic (⊤ : Subgroup Y) (T.map φ) (M.map φ) := by
  have : Finite Y := Finite.of_surjective φ hφ
  refine ⟨isSylowTwoOf_map_top hφ h.isSylow, ?_, ?_⟩
  · intro hnorm
    have hN : (T.map φ).Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)
    have hC : ((T.map φ).comap φ).Normal := hN.comap φ
    have hTC : T ≤ (T.map φ).comap φ := Subgroup.le_comap_map φ T
    have hCM : (T.map φ).comap φ ≤ M := by
      rw [Subgroup.comap_map_eq]
      exact sup_le h.le hker
    have hCn : (⊤ : Subgroup X) ≤ Subgroup.normalizer (((T.map φ).comap φ : Subgroup X) : Set X) :=
      (Subgroup.normalizer_eq_top_iff.mpr hC).ge
    have hfr := frattini_two le_top hCn (isSylowTwoOf_mono h.isSylow hTC le_top)
    have hHM : (⊤ : Subgroup X) ≤ M := hfr.trans (sup_le hCM h.inf_normalizer_le)
    exact absurd (lt_of_le_of_lt hHM h.maximal.1) (lt_irrefl _)
  · rw [isUniqueMaxOver_iff]
    refine ⟨isMaxSubgroupIn_top_iff.mpr (isCoatom_map_of_surjective hφ hker
      (isMaxSubgroupIn_top_iff.mp h.maximal)), Subgroup.map_mono h.le, fun N hN hTN => ?_⟩
    have hNc := isMaxSubgroupIn_top_iff.mp hN
    have hcN : IsCoatom (N.comap φ) := Subgroup.isCoatom_comap_of_surjective hφ hNc
    have hTle : T ≤ N.comap φ := Subgroup.map_le_iff_le_comap.mp hTN
    have := h.eq_of_maximal (isMaxSubgroupIn_top_iff.mpr hcN) hTle
    rw [← Subgroup.map_comap_eq_self_of_surjective hφ N, this]

namespace B6

theorem isMaxSubgroupIn_top_subgroupOf {H N : Subgroup G} (h : IsMaxSubgroupIn H N) :
    IsMaxSubgroupIn (⊤ : Subgroup H) (N.subgroupOf H) := by
  have hNH : N ≤ H := h.1.le
  refine ⟨lt_top_iff_ne_top.mpr fun htop => ?_, fun K' hK' _ => ?_⟩
  · exact absurd (Subgroup.subgroupOf_eq_top.mp htop) (not_le_of_gt h.1)
  · have hmap : N < K'.map H.subtype := by
      have := (Subgroup.map_lt_map_iff_of_injective H.subtype_injective).mpr hK'
      rwa [Subgroup.map_subgroupOf_eq_of_le hNH] at this
    have hK : K'.map H.subtype = H := h.2 _ hmap (by
      rintro _ ⟨x, -, rfl⟩
      exact x.2)
    have h1 : K' = (K'.map H.subtype).comap H.subtype :=
      (Subgroup.comap_map_eq_self_of_injective H.subtype_injective K').symm
    rw [h1, hK]
    exact Subgroup.subgroupOf_self H

theorem isMaxSubgroupIn_map_subtype {H : Subgroup G} {N' : Subgroup H}
    (h : IsMaxSubgroupIn (⊤ : Subgroup H) N') : IsMaxSubgroupIn H (N'.map H.subtype) := by
  refine ⟨?_, fun K hK hKH => ?_⟩
  · refine lt_of_le_of_ne (by rintro _ ⟨x, -, rfl⟩; exact x.2) fun heq => ?_
    have : N' = ⊤ := by
      have h1 : N' = (N'.map H.subtype).comap H.subtype :=
        (Subgroup.comap_map_eq_self_of_injective H.subtype_injective N').symm
      rw [h1, heq]
      exact Subgroup.subgroupOf_self H
    exact absurd this (ne_of_lt h.1)
  · have hlt : N' < K.subgroupOf H := by
      have h1 := (Subgroup.map_lt_map_iff_of_injective H.subtype_injective
        (H := N') (K := K.subgroupOf H))
      rw [Subgroup.map_subgroupOf_eq_of_le hKH] at h1
      exact h1.mp hK
    have := h.2 _ hlt le_top
    have h2 : K = (K.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hKH).symm
    rw [h2, this, Subgroup.map_top, Subgroup.range_subtype]

end B6

theorem MinParabolic.subgroupOf {H T M : Subgroup G} (h : MinParabolic H T M) :
    MinParabolic (⊤ : Subgroup H) (T.subgroupOf H) (M.subgroupOf H) := by
  have hTH : T ≤ H := h.isSylow.1
  have hTM : T ≤ M := h.le
  refine ⟨⟨le_top, ?_, ?_⟩, ?_, ?_⟩
  · exact h.isSylow.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTH).injective
  · have e : ((T.subgroupOf H).subgroupOf ⊤).index = (T.subgroupOf H).index :=
      Subgroup.relIndex_top_right (T.subgroupOf H)
    rw [e]
    exact h.isSylow.2.2
  · intro hn
    apply h.not_normal
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have key := Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_top (⟨x, hx⟩ : H)))
    constructor
    · intro hz
      have := (key ⟨z, hTH hz⟩).mp hz
      exact this
    · intro hz
      have hzH : z ∈ H := by
        have hxz : x * z * x⁻¹ ∈ H := hTH hz
        have := H.mul_mem (H.mul_mem (H.inv_mem hx) hxz) hx
        simpa [mul_assoc] using this
      exact (key ⟨z, hzH⟩).mpr hz
  · rw [isUniqueMaxOver_iff]
    refine ⟨isMaxSubgroupIn_top_subgroupOf h.maximal, Subgroup.subgroupOf_mono H hTM,
      fun N' hN' hTN' => ?_⟩
    have hmax := isMaxSubgroupIn_map_subtype hN'
    have hTN : T ≤ N'.map H.subtype := by
      intro t ht
      exact ⟨⟨t, hTH ht⟩, hTN' ht, rfl⟩
    have := h.eq_of_maximal hmax hTN
    rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective N', this]
    rfl

theorem minParabolic_exists_iff [Finite G] {S H : Subgroup G} :
    (∃ M, MinParabolic H S M) ↔
      IsSylowTwoOf S H ∧ ¬ H ≤ Subgroup.normalizer (S : Set G) ∧
        ∃ K : Subgroup G, S ≤ K ∧ K < H ∧ ∀ X : Subgroup G, S ≤ X → X < H → X ≤ K := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨h.isSylow, h.not_normal, M, h.le, h.maximal.1, fun X hSX hXH => h.le_of_lt hSX hXH⟩
  · rintro ⟨hS, hnorm, K, hSK, hKH, hK⟩
    have hmax : IsMaxSubgroupIn H K := by
      refine ⟨hKH, fun X hKX hXH => ?_⟩
      by_contra hne
      exact absurd (hK X (hSK.trans hKX.le) (lt_of_le_of_ne hXH hne)) (not_le_of_gt hKX)
    refine ⟨K, hS, hnorm, isUniqueMaxOver_iff.mpr ⟨hmax, hSK, fun N hN hSN => ?_⟩⟩
    have hNK : N ≤ K := hK N hSN hN.1
    by_contra hne
    have hlt : N < K := lt_of_le_of_ne hNK hne
    exact absurd (hN.2 K hlt hKH.le) (ne_of_lt hKH)

namespace B6

theorem kerIn_subgroupOf_top (M H : Subgroup G) :
    kerIn (M.subgroupOf H) ⊤ = (kerIn M H).subgroupOf H := by
  ext x
  simp only [mem_kerIn, Subgroup.mem_subgroupOf, Subgroup.mem_top, forall_const, Subtype.forall]
  constructor
  · intro hx b hb
    exact hx b hb
  · intro hx b hb
    exact hx b hb

theorem twoResidual_top_eq_subgroupOf [Finite G] (H : Subgroup G) :
    twoResidual (⊤ : Subgroup H) = (twoResidual H).subgroupOf H := by
  apply le_antisymm
  · refine twoResidual_le_of_isTwoQuotient le_top ?_ ?_
    · refine (Subgroup.normalizer_eq_top_iff.mpr ?_).ge
      refine ⟨fun a ha b => ?_⟩
      have := Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H b.2) a
      exact this.mp ha
    · intro y _
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H y y.2
      exact ⟨k, hk⟩
  · intro y hy
    have hn : (twoResidual (⊤ : Subgroup H)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
    have hle : twoResidual H ≤ (twoResidual (⊤ : Subgroup H)).map H.subtype := by
      refine twoResidual_le_of_isTwoQuotient ?_ ?_ ?_
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      · intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · rintro ⟨n, hnN, rfl⟩
          exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, hn.conj_mem n hnN ⟨g, hg⟩, rfl⟩
        · rintro ⟨n, hnN, hz⟩
          have hmem := hn.conj_mem n hnN (⟨g, hg⟩ : H)⁻¹
          rw [inv_inv] at hmem
          refine ⟨_, hmem, ?_⟩
          have : (n : G) = g * z * g⁻¹ := hz
          simp [this, mul_assoc]
      · intro x hx
        obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup H) ⟨x, hx⟩ (Subgroup.mem_top _)
        exact ⟨k, ⟨_, hk, rfl⟩⟩
    obtain ⟨n, hnN, hny⟩ := hle hy
    have : n = y := Subtype.ext hny
    rw [← this]
    exact hnN

end B6

namespace B6

theorem exists_conj_le_of_odd_relIndex [Finite G] {H T Y : Subgroup G} (hT : IsSylowTwoOf T H)
    (hYH : Y ≤ H) (hodd : ¬ 2 ∣ Y.relIndex H) : ∃ g ∈ H, conjSub g T ≤ Y := by
  obtain ⟨S, hS, -⟩ := exists_isSylowTwoOf_ge (X := (⊥ : Subgroup G)) (J := Y)
    (fun x => ⟨0, Subtype.ext (by simpa using Subgroup.mem_bot.mp x.2)⟩) bot_le
  have hSH : IsSylowTwoOf S H := by
    refine ⟨hS.1.trans hYH, hS.2.1, fun hd => ?_⟩
    have h1 : S.relIndex Y * Y.relIndex H = S.relIndex H :=
      Subgroup.relIndex_mul_relIndex S Y H hS.1 hYH
    have hd' : 2 ∣ S.relIndex Y * Y.relIndex H := h1 ▸ hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd' with h2 | h2
    · exact hS.2.2 h2
    · exact hodd h2
  obtain ⟨g, hg, hgS⟩ := isSylowTwoOf_exists_conj hSH hT
  refine ⟨g⁻¹, H.inv_mem hg, ?_⟩
  rw [hgS, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  exact hS.1

theorem pCoreOf_top (r : ℕ) (X : Type*) [Group X] :
    pCoreOf r (⊤ : Subgroup X) = CFSG.Open.pCore r X := by
  unfold pCoreOf
  have := CFSG.LieType.BorelTits.map_pCore_mulEquiv r (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
  exact this

instance instNormalPCore (p : ℕ) (X : Type*) [Group X] : (CFSG.Open.pCore p X).Normal :=
  CFSG.LieType.BorelTits.pCore_normal p

end B6

theorem MinParabolic.eq_conjSub_of_maximal [Finite G] {H T M N : Subgroup G}
    (h : MinParabolic H T M) {g : G} (hg : g ∈ H) (hN : IsMaxSubgroupIn H N)
    (hTN : conjSub g T ≤ N) : N = conjSub g M := by
  have hH : conjSub g⁻¹ H = H := conjSub_eq_self (Subgroup.le_normalizer (H.inv_mem hg))
  have hN' : IsMaxSubgroupIn H (conjSub g⁻¹ N) := by
    have := (isMaxSubgroupIn_conjSub (g := g⁻¹)).mpr hN
    rwa [hH] at this
  have hT' : T ≤ conjSub g⁻¹ N := by
    have := (conjSub g⁻¹).le_iff_le.mpr hTN
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  have := h.eq_of_maximal hN' hT'
  rw [← this, ← conjSub_mul, mul_inv_cancel, conjSub_one]

namespace MinParabolic

variable {X : Type*} [Group X] [Finite X] {T M : Subgroup X}

instance instNormalKerIn (M : Subgroup X) : (kerIn M ⊤).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_kerIn M ⊤))

theorem pCore_le_M (h : MinParabolic (⊤ : Subgroup X) T M) : CFSG.Open.pCore 2 X ≤ M := by
  rw [← pCoreOf_top]
  exact (pCoreOf_two_le_of_isSylowTwoOf h.isSylow).trans h.le

theorem map_kerIn_eq_frattini (h : MinParabolic (⊤ : Subgroup X) T M) :
    (kerIn M ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) =
      frattini (X ⧸ CFSG.Open.pCore 2 X) := by
  set φ := QuotientGroup.mk' (CFSG.Open.pCore 2 X) with hφdef
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker ≤ M := by
    rw [hφdef, QuotientGroup.ker_mk']
    exact h.pCore_le_M
  have hMc : IsCoatom M := isMaxSubgroupIn_top_iff.mp h.maximal
  have hMbar : IsCoatom (M.map φ) := isCoatom_map_of_surjective hφ hker hMc
  apply le_antisymm
  ·
    unfold frattini Order.radical
    refine le_iInf₂ fun K' hK' => ?_
    rw [Subgroup.map_le_iff_le_comap]
    set Y := K'.comap φ with hY
    have hYc : IsCoatom Y := Subgroup.isCoatom_comap_of_surjective hφ hK'
    by_contra hJY
    have hsup : Y ⊔ kerIn M ⊤ = ⊤ := by
      refine hYc.2 _ (lt_of_le_of_ne le_sup_left fun heq => hJY ?_)
      exact heq ▸ le_sup_right
    have hYn : Y ≤ Subgroup.normalizer ((kerIn M ⊤ : Subgroup X) : Set X) :=
      (le_normalizer_kerIn M ⊤).trans' le_top
    have hidx : (Y ⊓ kerIn M ⊤).relIndex (kerIn M ⊤) = Y.relIndex ⊤ := by
      have := relIndex_inf_eq_relIndex_sup hYn
      rwa [hsup] at this
    have hQY : pCoreOf 2 (⊤ : Subgroup X) ≤ Y ⊓ kerIn M ⊤ := by
      refine le_inf ?_ (by
        rw [pCoreOf_top]
        exact h.pCoreOf_le_kerIn |>.trans' (le_of_eq (pCoreOf_top 2 X).symm))
      rw [pCoreOf_top, hY]
      intro x hx
      rw [Subgroup.mem_comap]
      have : φ x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [this]
      exact K'.one_mem
    have hodd : ¬ 2 ∣ Y.relIndex ⊤ := by
      rw [← hidx]
      intro hd
      exact h.isSylowTwoOf_pCoreOf_kerIn.2.2
        (hd.trans (Subgroup.relIndex_dvd_of_le_left _ hQY))
    obtain ⟨g, -, hg⟩ := exists_conj_le_of_odd_relIndex h.isSylow le_top hodd
    have hYM := h.eq_conjSub_of_maximal (Subgroup.mem_top g) (isMaxSubgroupIn_top_iff.mpr hYc) hg
    apply hJY
    rw [hYM]
    have hJg : conjSub g (kerIn M ⊤) = kerIn M ⊤ :=
      conjSub_eq_self (le_normalizer_kerIn M ⊤ (Subgroup.mem_top g))
    calc kerIn M ⊤ = conjSub g (kerIn M ⊤) := hJg.symm
      _ ≤ conjSub g M := (conjSub g).le_iff_le.mpr kerIn_le
  ·
    rw [← kerIn_map_top hφ hker]
    refine le_kerIn_of_le_normalizer (frattini_le_coatom hMbar) ?_
    exact (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge

theorem map_kerIn_subgroupOf_eq_frattini {H T M : Subgroup G} [Finite G]
    (h : MinParabolic H T M) :
    ((kerIn M H).subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 H)) =
      frattini (H ⧸ CFSG.Open.pCore 2 H) := by
  have := h.subgroupOf.map_kerIn_eq_frattini
  rwa [B6.kerIn_subgroupOf_top] at this

end MinParabolic

namespace B6

theorem isPGroup_of_pow_mem {Y : Type*} [Group Y] {p : ℕ} {N P : Subgroup Y} (hN : IsPGroup p N)
    (h : ∀ x ∈ P, ∃ k : ℕ, x ^ p ^ k ∈ N) : IsPGroup p P := by
  intro x
  obtain ⟨a, ha⟩ := h x x.2
  obtain ⟨b, hb⟩ := hN ⟨x ^ p ^ a, ha⟩
  refine ⟨a + b, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val hb
  simpa [pow_add, pow_mul] using this

theorem mem_of_pow_mem_of_coprime {Y : Type*} [Group Y] {K : Subgroup Y} {x : Y} {k : ℕ}
    (hk : x ^ k ∈ K) (hcop : Nat.Coprime (orderOf x) k) : x ∈ K := by
  have h1 : (Nat.gcd (orderOf x) k : ℤ) =
      orderOf x * Nat.gcdA (orderOf x) k + k * Nat.gcdB (orderOf x) k := Nat.gcd_eq_gcd_ab _ _
  rw [hcop] at h1
  have h2 : x = (x ^ (orderOf x)) ^ (Nat.gcdA (orderOf x) k) *
      (x ^ k) ^ (Nat.gcdB (orderOf x) k) := by
    rw [← zpow_natCast x (orderOf x), ← zpow_natCast x k, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (orderOf x : ℤ) * Nat.gcdA (orderOf x) k + k * Nat.gcdB (orderOf x) k = 1 := by
      rw [← h1]; rfl
    rw [this, zpow_one]
  rw [h2, pow_orderOf_eq_one, one_zpow, one_mul]
  exact K.zpow_mem hk _

theorem le_twoResidual_of_odd {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y}
    (hN : Odd (Nat.card N)) : N ≤ twoResidual (⊤ : Subgroup Y) := by
  intro x hx
  obtain ⟨b, hb⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup Y) x (Subgroup.mem_top x)
  refine mem_of_pow_mem_of_coprime hb ?_
  have hdvd : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : N)
    simpa using this
  exact Nat.Coprime.pow_right b ((Odd.coprime_two_right (hN.of_dvd_nat hdvd)))

end B6

namespace MinParabolic

variable {Z : Type*} [Group Z] [Finite Z] {T M : Subgroup Z}

theorem twoResidual_ne_bot (h : MinParabolic (⊤ : Subgroup Z) T M) :
    twoResidual (⊤ : Subgroup Z) ≠ ⊥ := fun hK =>
  h.not_twoResidual_le_kerIn (hK ▸ bot_le)

theorem twoResidual_minimal_normal (h : MinParabolic (⊤ : Subgroup Z) T M)
    (hJ : kerIn M ⊤ = ⊥) {N : Subgroup Z} (hN : N.Normal) (hNK : N ≤ twoResidual ⊤) :
    N = ⊥ ∨ N = twoResidual ⊤ := by
  rcases h.le_kerIn_or_twoResidual_le le_top (Subgroup.normalizer_eq_top_iff.mpr hN).ge with
    hle | hle
  · left
    rw [hJ] at hle
    exact le_bot_iff.mp hle
  · right
    exact le_antisymm hNK hle

theorem not_isPGroup_top (h : MinParabolic (⊤ : Subgroup Z) T M) :
    ¬ IsPGroup 2 (⊤ : Subgroup Z) := by
  intro hp
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow_of_isPGroup hp T
  have hodd : ¬ 2 ∣ T.relIndex ⊤ := h.isSylow.2.2
  have hn0 : n = 0 := by
    by_contra hne
    exact hodd (hn ▸ dvd_pow_self 2 hne)
  rw [hn0, pow_zero] at hn
  apply h.not_normal
  have := Subgroup.relIndex_eq_one.mp hn
  exact this.trans Subgroup.le_normalizer

theorem twoResidual_isPGroup_of_solvable (h : MinParabolic (⊤ : Subgroup Z) T M)
    (hJ : kerIn M ⊤ = ⊥) (hsolv : Group.IsSolvable Z) {p : ℕ}
    (hZ : ∀ q : ℕ, q.Prime → q ∣ Nat.card Z → q = 2 ∨ q = p) :
    IsPGroup p (twoResidual (⊤ : Subgroup Z)) ∧
      ∀ x ∈ twoResidual (⊤ : Subgroup Z), ∀ y ∈ twoResidual (⊤ : Subgroup Z), x * y = y * x := by
  have hKn : (twoResidual (⊤ : Subgroup Z)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  obtain ⟨r, S, hr, hSK, hSimple, hconj, hSnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hKn h.twoResidual_ne_bot
      (fun N hN hNK => h.twoResidual_minimal_normal hJ hN hNK)
  have hSsolv : ∀ i, Group.IsSolvable (S i) := fun i => inferInstance
  have hScomm : ∀ i, ∀ a b : S i, a * b = b * a := fun i => by
    have := hSimple i
    exact (IsSimpleGroup.comm_iff_isSolvable).mpr (hSsolv i)
  have hSprime : ∀ i, (Nat.card (S i)).Prime := fun i => by
    have := hSimple i
    let : CommGroup (S i) := { (inferInstance : Group (S i)) with mul_comm := hScomm i }
    exact IsSimpleGroup.prime_card
  let i₀ : Fin r := ⟨0, hr⟩
  have hcard : ∀ i, Nat.card (S i) = Nat.card (S i₀) := fun i => by
    obtain ⟨g, hg⟩ := hconj i₀ i
    rw [hg]
    exact card_conjSub (S i₀) g⁻¹
  have hKcard : Nat.card (twoResidual (⊤ : Subgroup Z)) = Nat.card (S i₀) ^ r := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_pi]
    simp [hcard]
  have hq := hSprime i₀
  have hqK : Nat.card (S i₀) ∣ Nat.card (twoResidual (⊤ : Subgroup Z)) := by
    rw [hKcard]
    exact dvd_pow_self _ (by omega)
  have hqZ : Nat.card (S i₀) ∣ Nat.card Z :=
    hqK.trans (Subgroup.card_subgroup_dvd_card _)
  have hKp : IsPGroup (Nat.card (S i₀)) (twoResidual (⊤ : Subgroup Z)) := by
    have := Fact.mk hq
    exact IsPGroup.of_card hKcard
  have hqp : Nat.card (S i₀) = p := by
    rcases hZ _ hq hqZ with h2 | h2
    · exfalso
      rw [h2] at hKp
      apply h.not_isPGroup_top
      exact isPGroup_of_pow_mem hKp fun x _ => twoResidual_isTwoQuotient ⊤ x (Subgroup.mem_top x)
    · exact h2
  rw [hqp] at hKp
  refine ⟨hKp, fun x hx y hy => ?_⟩
  have h1 : e.symm ⟨x, hx⟩ * e.symm ⟨y, hy⟩ = e.symm ⟨y, hy⟩ * e.symm ⟨x, hx⟩ := by
    funext i
    exact hScomm i _ _
  have h2 := congrArg e h1
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  exact congrArg Subtype.val h2

theorem pCore_eq_twoResidual {p : ℕ} (hpp : p.Prime)
    (hp2 : p ≠ 2) (hK : IsPGroup p (twoResidual (⊤ : Subgroup Z))) :
    CFSG.Open.pCore p Z = twoResidual (⊤ : Subgroup Z) := by
  have hKn : (twoResidual (⊤ : Subgroup Z)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have : Fact p.Prime := ⟨hpp⟩
  apply le_antisymm
  · refine le_twoResidual_of_odd ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCore_isPGroup (G := Z) p)
    rw [hn]
    exact (hpp.odd_of_ne_two hp2).pow
  · exact CFSG.LieType.BorelTits.le_pCore p hKn hK

theorem eq_bot_or_eq_twoResidual_of_normalizes (h : MinParabolic (⊤ : Subgroup Z) T M)
    (hJ : kerIn M ⊤ = ⊥)
    (hcomm : ∀ x ∈ twoResidual (⊤ : Subgroup Z), ∀ y ∈ twoResidual (⊤ : Subgroup Z), x * y = y * x)
    {S : Subgroup Z} (hSK : S ≤ twoResidual ⊤) (hTS : T ≤ Subgroup.normalizer (S : Set Z)) :
    S = ⊥ ∨ S = twoResidual ⊤ := by
  have hKn : (twoResidual (⊤ : Subgroup Z)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hKS : twoResidual (⊤ : Subgroup Z) ≤ Subgroup.normalizer (S : Set Z) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := hcomm k hk x (hSK hx)
      have e : k * x * k⁻¹ = x := by rw [h1]; group
      rw [e]
      exact hx
    · intro hx
      have hxK : x ∈ twoResidual (⊤ : Subgroup Z) := by
        have := hKn.conj_mem _ (hSK hx) k⁻¹
        simpa [mul_assoc] using this
      have h1 := hcomm k hk x hxK
      have e : k * x * k⁻¹ = x := by rw [h1]; group
      rwa [e] at hx
  have hn : (S : Subgroup Z).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    calc (⊤ : Subgroup Z) = T ⊔ twoResidual ⊤ := (sup_twoResidual_eq h.isSylow).symm
      _ ≤ _ := sup_le hTS hKS
  exact h.twoResidual_minimal_normal hJ hn hSK

end MinParabolic

namespace MinParabolic

variable {X : Type*} [Group X] [Finite X] {T M : Subgroup X}

theorem exists_hall_of_solvable (h : MinParabolic (⊤ : Subgroup X) T M) (hsolv : Group.IsSolvable X)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrX : r ∣ Nat.card X) :
    ∃ Hr : Subgroup X, T ≤ Hr ∧ Hr ≠ ⊤ ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Hr.index → ℓ = r := by
  let π : Set Nat.Primes := {ℓ | ℓ.val ≠ r}
  have hTπ : CFSG.IsPiSubgroup π T := by
    intro ℓ hℓ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.isSylow.2.1
    have : ℓ.val ∣ 2 ^ n := hn ▸ hℓ
    have h2 : ℓ.val = 2 := (Nat.prime_dvd_prime_iff_eq ℓ.property Nat.prime_two).mp
      (ℓ.property.dvd_of_dvd_pow this)
    show ℓ.val ≠ r
    rw [h2]
    exact fun h' => hr2 h'.symm
  obtain ⟨Hr, hHall, hTH⟩ := CFSG.SolvableHall.solvable_hall_containment hsolv π T hTπ
  refine ⟨Hr, hTH, ?_, fun ℓ hℓ hdvd => ?_⟩
  · intro htop
    have hdvd : (⟨r, hr⟩ : Nat.Primes).val ∣ Nat.card Hr := by
      rw [htop, Subgroup.card_top]
      exact hrX
    have := hHall.p_in_pi_of_p_dvd_card ⟨r, hr⟩ hdvd
    exact this rfl
  · have := hHall.p_in_pi_of_p_dvd_index ⟨ℓ, hℓ⟩ hdvd
    exact not_not.mp this

theorem exists_odd_prime_of_solvable (h : MinParabolic (⊤ : Subgroup X) T M)
    (hsolv : Group.IsSolvable X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p := by
  by_cases hex : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card X
  · obtain ⟨p, hp, hp2, hpX⟩ := hex
    refine ⟨p, hp, hp2, fun q hq hqX => ?_⟩
    by_cases hq2 : q = 2
    · exact Or.inl hq2
    · right
      by_contra hqp
      obtain ⟨Hp, hTp, hHp, hidxp⟩ := h.exists_hall_of_solvable hsolv hp hp2 hpX
      obtain ⟨Hq, hTq, hHq, hidxq⟩ := h.exists_hall_of_solvable hsolv hq hq2 hqX
      have hHpM : Hp ≤ M := h.le_of_lt hTp (lt_top_iff_ne_top.mpr hHp)
      have hHqM : Hq ≤ M := h.le_of_lt hTq (lt_top_iff_ne_top.mpr hHq)
      have hdp : M.index ∣ Hp.index := Subgroup.index_dvd_of_le hHpM
      have hdq : M.index ∣ Hq.index := Subgroup.index_dvd_of_le hHqM
      have hMidx : M.index = 1 := by
        by_contra hne
        obtain ⟨ℓ, hℓ, hℓM⟩ := Nat.exists_prime_and_dvd hne
        exact hqp ((hidxq ℓ hℓ (hℓM.trans hdq)).symm.trans (hidxp ℓ hℓ (hℓM.trans hdp)))
      exact absurd (Subgroup.index_eq_one.mp hMidx) (ne_of_lt h.maximal.1)
  · exfalso
    have hX : Nat.card X ≠ 0 := Nat.card_pos.ne'
    have hpow : Nat.card X = 2 ^ (Nat.card X).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hX fun {d} hd hdX => by
        by_contra hd2
        exact hex ⟨d, hd, hd2, hdX⟩
    apply h.not_isPGroup_top
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := (Nat.card X).primeFactorsList.length) ?_
    rw [Subgroup.card_top]
    exact hpow

end MinParabolic

namespace MinParabolic

variable {Y : Type*} [Group Y] [Finite Y] {T M : Subgroup Y}

theorem card_kerIn_odd (h : MinParabolic (⊤ : Subgroup Y) T M) (hO : CFSG.Open.pCore 2 Y = ⊥) :
    ¬ 2 ∣ Nat.card (kerIn M ⊤) := by
  have h5 := h.isSylowTwoOf_pCoreOf_kerIn
  rw [pCoreOf_top, hO] at h5
  have := h5.2.2
  rwa [Subgroup.bot_subgroupOf, Subgroup.index_bot] at this

theorem isPGroup_kerIn (h : MinParabolic (⊤ : Subgroup Y) T M) (hO : CFSG.Open.pCore 2 Y = ⊥)
    {p : ℕ} (hpp : p.Prime) (hZ : ∀ q : ℕ, q.Prime → q ∣ Nat.card Y → q = 2 ∨ q = p) :
    IsPGroup p (kerIn M ⊤) := by
  have hodd := h.card_kerIn_odd hO
  have hJ0 : Nat.card (kerIn M ⊤) ≠ 0 := Nat.card_pos.ne'
  have hpow : Nat.card (kerIn M ⊤) = p ^ (Nat.card (kerIn M ⊤)).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hJ0 (fun {d} hd hdJ => by
      rcases hZ d hd (hdJ.trans (Subgroup.card_subgroup_dvd_card _)) with h2 | h2
      · exact absurd (h2 ▸ hdJ) hodd
      · exact h2)
  have := Fact.mk hpp
  exact IsPGroup.of_card hpow

end MinParabolic

namespace MinParabolic

variable {Y : Type*} [Group Y] [Finite Y] {T M : Subgroup Y}

theorem isPGroup_twoResidual_of_pCore_eq_bot (h : MinParabolic (⊤ : Subgroup Y) T M)
    (hO : CFSG.Open.pCore 2 Y = ⊥) (hsolv : Group.IsSolvable Y) {p : ℕ} (hpp : p.Prime)
    (hZ : ∀ q : ℕ, q.Prime → q ∣ Nat.card Y → q = 2 ∨ q = p) :
    IsPGroup p (twoResidual (⊤ : Subgroup Y)) := by
  set J := kerIn M ⊤ with hJdef
  set φ := QuotientGroup.mk' J with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker ≤ M := by
    rw [hφ, QuotientGroup.ker_mk']
    exact kerIn_le
  have hmp := h.map_of_surjective hsurj hker
  have hJ' : kerIn (M.map φ) ⊤ = ⊥ := by
    rw [kerIn_map_top hsurj hker]
    exact QuotientGroup.map_mk'_self J
  have hZ' : ∀ q : ℕ, q.Prime → q ∣ Nat.card (Y ⧸ J) → q = 2 ∨ q = p := fun q hq hqZ =>
    hZ q hq (hqZ.trans (Subgroup.index_dvd_card J))
  have hK' := (hmp.twoResidual_isPGroup_of_solvable hJ' inferInstance hZ').1
  rw [← twoResidual_map_top hsurj] at hK'
  have hJp := h.isPGroup_kerIn hO hpp hZ
  refine isPGroup_of_pow_mem hJp fun x hx => ?_
  obtain ⟨a, ha⟩ := hK' ⟨φ x, Subgroup.mem_map_of_mem φ hx⟩
  refine ⟨a, ?_⟩
  have : (φ x) ^ p ^ a = 1 := congrArg Subtype.val ha
  rw [← map_pow] at this
  rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact this

end MinParabolic

namespace MinParabolic

variable {Y : Type*} [Group Y] [Finite Y] {T M : Subgroup Y}

open scoped commutatorElement in
theorem kerIn_eq_frattini_twoResidual (h : MinParabolic (⊤ : Subgroup Y) T M)
    (hO : CFSG.Open.pCore 2 Y = ⊥) (hsolv : Group.IsSolvable Y) {p : ℕ} (hpp : p.Prime)
    (hp2 : p ≠ 2) (hZ : ∀ q : ℕ, q.Prime → q ∣ Nat.card Y → q = 2 ∨ q = p) :
    kerIn M ⊤ = (frattini (twoResidual (⊤ : Subgroup Y))).map
      (twoResidual (⊤ : Subgroup Y)).subtype := by
  set K := twoResidual (⊤ : Subgroup Y) with hKdef
  set J := kerIn M ⊤ with hJdef
  set Φ := (frattini K).map K.subtype with hΦdef
  have hKn : K.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hKp : IsPGroup p K := h.isPGroup_twoResidual_of_pCore_eq_bot hO hsolv hpp hZ
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (IsPGroup p K) := ⟨hKp⟩
  have hΦn : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (Φ : Set Y) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := K) (frattini K)
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn] at h1
    exact h1
  have hJK : J ≤ K := by
    refine le_twoResidual_of_odd ?_
    exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact h.card_kerIn_odd hO)
  have hΦK : Φ ≤ K := Subgroup.map_subtype_le _
  have hΦJ : Φ ≤ J := by
    rcases h.le_kerIn_or_twoResidual_le le_top hΦn with hle | hle
    · exact hle
    · exfalso
      have hfr : frattini K = ⊤ := by
        refine top_unique ?_
        intro x _
        have hx : (x : Y) ∈ K := x.2
        have := hle hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp this
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      have hbot : (⊥ : Subgroup K) = ⊤ := frattini_nongenerating (by rw [hfr]; simp)
      apply h.twoResidual_ne_bot
      rw [← hKdef, eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : K) ∈ (⊥ : Subgroup K) := by rw [hbot]; exact Subgroup.mem_top _
      have h1 : (⟨x, hx⟩ : K) = 1 := Subgroup.mem_bot.mp this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  apply le_antisymm _ hΦJ
  have hpow : ∀ x ∈ K, x ^ p ∈ Φ := fun x hx => by
    have := pth_power_mem_frattini_of_isPGroup (p := p) (⟨x, hx⟩ : K)
    exact Subgroup.mem_map.mpr ⟨_, this, rfl⟩
  have hcomm : ⁅K, K⁆ ≤ Φ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : ⁅(⟨a, ha⟩ : K), (⟨b, hb⟩ : K)⁆ ∈ frattini K :=
      commutator_le_frattini_of_isPGroup (p := p)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
  have hTn : ∀ X : Subgroup Y, X.Normal → T ≤ Subgroup.normalizer (X : Set Y) :=
    fun X hX => le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hX).ge
  obtain ⟨W', hΦW', hW'K, hTW', hsup, hinf⟩ :=
    B6.exists_isCompl_of_coprime_section hp2 hΦJ hJK hpow hcomm
      (hTn K hKn) (le_top.trans hΦn) (hTn J inferInstance) h.isSylow.2.1
  have hW'norm : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (W' : Set Y) := by
    have hKW : K ≤ Subgroup.normalizer (W' : Set Y) := by
      rw [Subgroup.le_normalizer_iff_commutator_le_left]
      exact (Subgroup.commutator_mono hW'K le_rfl).trans (hcomm.trans hΦW')
    calc (⊤ : Subgroup Y) = T ⊔ K := (sup_twoResidual_eq h.isSylow).symm
      _ ≤ _ := sup_le hTW' hKW
  have hW'n : W'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hW'norm)
  rcases h.le_kerIn_or_twoResidual_le le_top hW'norm with hle | hle
  · exfalso
    apply h.not_twoResidual_le_kerIn
    rw [← hKdef, ← hsup]
    exact sup_le le_rfl hle
  · have hW'eq : W' = K := le_antisymm hW'K hle
    rw [hW'eq, inf_eq_left.mpr hJK] at hinf
    exact hinf.le

end MinParabolic

@[expose] def upperTwo {X : Type*} [Group X] (N : Subgroup X) [N.Normal] : Subgroup X :=
  (CFSG.Open.pCore 2 (X ⧸ N)).comap (QuotientGroup.mk' N)

section UpperSeries

variable (X : Type*) [Group X]

@[expose] def O2p (p : ℕ) : Subgroup X :=
  (CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 X))

instance instNormalO2p (p : ℕ) : (O2p X p).Normal := by
  unfold O2p
  infer_instance

@[expose] def O2p2 (p : ℕ) : Subgroup X := upperTwo (O2p X p)

end UpperSeries

namespace B6

variable {X : Type*} [Group X] [Finite X]

theorem pCore_quotient_pCore : CFSG.Open.pCore 2 (X ⧸ CFSG.Open.pCore 2 X) = ⊥ := by
  set N := CFSG.Open.pCore 2 X with hN
  set φ := QuotientGroup.mk' N with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  set P := CFSG.Open.pCore 2 (X ⧸ N) with hP
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hPp : IsPGroup 2 P := CFSG.LieType.BorelTits.pCore_isPGroup (G := X ⧸ N) 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2
  have hP'p : IsPGroup 2 (P.comap φ) := by
    refine isPGroup_of_pow_mem hNp fun x hx => ?_
    obtain ⟨k, hk⟩ := hPp ⟨φ x, Subgroup.mem_comap.mp hx⟩
    refine ⟨k, ?_⟩
    have : (φ x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at this
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  have hle : P.comap φ ≤ N := CFSG.LieType.BorelTits.le_pCore 2 (hPn.comap φ) hP'p
  rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective hsurj P]
  calc (P.comap φ).map φ ≤ N.map φ := Subgroup.map_mono hle
    _ = ⊥ := QuotientGroup.map_mk'_self N

theorem upperTwo_eq_top_iff (N : Subgroup X) [N.Normal] :
    upperTwo N = ⊤ ↔ ∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
  constructor
  · intro h x
    have hx : x ∈ upperTwo N := by rw [h]; exact Subgroup.mem_top x
    have hx' := Subgroup.mem_comap.mp hx
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := X ⧸ N) 2 ⟨_, hx'⟩
    refine ⟨k, ?_⟩
    have : (QuotientGroup.mk' N x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · intro h
    have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective _
    have hp : IsPGroup 2 (⊤ : Subgroup (X ⧸ N)) := by
      intro q
      obtain ⟨x, hx⟩ := hsurj q.1
      obtain ⟨k, hk⟩ := h x
      refine ⟨k, ?_⟩
      apply Subtype.ext
      show (q.1) ^ 2 ^ k = 1
      rw [← hx, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    have hle : (⊤ : Subgroup (X ⧸ N)) ≤ CFSG.Open.pCore 2 (X ⧸ N) :=
      CFSG.LieType.BorelTits.le_pCore 2 inferInstance hp
    exact top_unique fun x _ => Subgroup.mem_comap.mpr (hle (Subgroup.mem_top _))

end B6

namespace MinParabolic

variable {X : Type*} [Group X] [Finite X] {T M : Subgroup X}

theorem solvable_structure (h : MinParabolic (⊤ : Subgroup X) T M) (hsolv : Group.IsSolvable X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ O2p2 X p = ⊤ ∧
      (kerIn M ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) =
        (frattini (CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X))).map
          (CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X)).subtype ∧
      CFSG.Open.pCore p (X ⧸ kerIn M ⊤) ≠ ⊥ ∧
      ∀ S : Subgroup (X ⧸ kerIn M ⊤), S ≤ CFSG.Open.pCore p (X ⧸ kerIn M ⊤) →
        T.map (QuotientGroup.mk' (kerIn M ⊤)) ≤ Subgroup.normalizer (S : Set (X ⧸ kerIn M ⊤)) →
        S = ⊥ ∨ S = CFSG.Open.pCore p (X ⧸ kerIn M ⊤) := by
  obtain ⟨p, hpp, hp2, hZ⟩ := h.exists_odd_prime_of_solvable hsolv
  refine ⟨p, hpp, hp2, ?_⟩
  set φ₂ := QuotientGroup.mk' (CFSG.Open.pCore 2 X) with hφ₂
  have hsurj₂ : Function.Surjective φ₂ := QuotientGroup.mk'_surjective _
  have hker₂ : φ₂.ker ≤ M := by
    rw [hφ₂, QuotientGroup.ker_mk']
    exact h.pCore_le_M
  have hmpY := h.map_of_surjective hsurj₂ hker₂
  have hOY : CFSG.Open.pCore 2 (X ⧸ CFSG.Open.pCore 2 X) = ⊥ := B6.pCore_quotient_pCore
  have hZY : ∀ q : ℕ, q.Prime → q ∣ Nat.card (X ⧸ CFSG.Open.pCore 2 X) → q = 2 ∨ q = p :=
    fun q hq hqY => hZ q hq (hqY.trans (Subgroup.index_dvd_card _))
  have hKpY := hmpY.isPGroup_twoResidual_of_pCore_eq_bot hOY inferInstance hpp hZY
  have hpcY := pCore_eq_twoResidual hpp hp2 hKpY
  have hfrY := hmpY.kerIn_eq_frattini_twoResidual hOY inferInstance hpp hp2 hZY
  refine ⟨?_, ?_, ?_⟩
  ·
    refine (B6.upperTwo_eq_top_iff (O2p X p)).mpr fun x => ?_
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X))
      (φ₂ x) (Subgroup.mem_top _)
    refine ⟨k, ?_⟩
    rw [← hpcY] at hk
    exact Subgroup.mem_comap.mpr (by rw [map_pow]; exact hk)
  ·
    rw [hpcY, ← hfrY, kerIn_map_top hsurj₂ hker₂]
  ·
    set J := kerIn M ⊤ with hJ
    set φ := QuotientGroup.mk' J with hφ
    have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
    have hker : φ.ker ≤ M := by
      rw [hφ, QuotientGroup.ker_mk']
      exact kerIn_le
    have hmp := h.map_of_surjective hsurj hker
    have hJ' : kerIn (M.map φ) ⊤ = ⊥ := by
      rw [kerIn_map_top hsurj hker]
      exact QuotientGroup.map_mk'_self J
    have hZ' : ∀ q : ℕ, q.Prime → q ∣ Nat.card (X ⧸ J) → q = 2 ∨ q = p := fun q hq hqZ =>
      hZ q hq (hqZ.trans (Subgroup.index_dvd_card J))
    obtain ⟨hKp, hKc⟩ := hmp.twoResidual_isPGroup_of_solvable hJ' inferInstance hZ'
    have hpc := pCore_eq_twoResidual hpp hp2 hKp
    refine ⟨?_, fun S hS hTS => ?_⟩
    · rw [hpc]
      exact hmp.twoResidual_ne_bot
    · rw [hpc] at hS ⊢
      exact hmp.eq_bot_or_eq_twoResidual_of_normalizes hJ' hKc hS hTS

end MinParabolic

namespace MinParabolic

variable {Y : Type*} [Group Y] [Finite Y] {T M : Subgroup Y}

theorem le_conjSub_of_lt {G : Type*} [Group G] [Finite G] {H T M X : Subgroup G}
    (h : MinParabolic H T M) {g : G} (hg : g ∈ H) (hTX : conjSub g T ≤ X) (hXH : X < H) :
    X ≤ conjSub g M := by
  obtain ⟨N, hN, hXN⟩ := exists_isMaxSubgroupIn hXH
  have := h.eq_conjSub_of_maximal hg hN (hTX.trans hXN)
  rw [← this]
  exact hXN

theorem isNilpotent_kerIn (h : MinParabolic (⊤ : Subgroup Y) T M)
    (hO : CFSG.Open.pCore 2 Y = ⊥) : Group.IsNilpotent (kerIn M ⊤) := by
  set J := kerIn M ⊤ with hJdef
  have hJn : J.Normal := inferInstance
  have hodd := h.card_kerIn_odd hO
  refine ((Group.isNilpotent_of_finite_tfae (G := J)).out 4 1).mp ?_
  intro r hr P
  have : Fact r.Prime := hr
  set R : Subgroup Y := (P : Subgroup J).map J.subtype with hR
  have hfr : Subgroup.normalizer (R : Set Y) ⊔ J = ⊤ := Sylow.normalizer_sup_eq_top P
  have hN'J : Subgroup.normalizer (R : Set Y) ≤ Subgroup.normalizer (J : Set Y) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hJn).ge
  have hidx := relIndex_inf_eq_relIndex_sup hN'J
  rw [hfr] at hidx
  have hoddN : ¬ 2 ∣ (Subgroup.normalizer (R : Set Y)).relIndex ⊤ := by
    rw [← hidx]
    exact fun hd => hodd (hd.trans (Subgroup.relIndex_dvd_card _ _))
  obtain ⟨g, -, hg⟩ := exists_conj_le_of_odd_relIndex h.isSylow le_top hoddN
  have hRn : R.Normal := by
    by_contra hnot
    have hlt : Subgroup.normalizer (R : Set Y) < ⊤ := by
      refine lt_of_le_of_ne le_top fun heq => hnot ?_
      exact Subgroup.normalizer_eq_top_iff.mp heq
    have hle := h.le_conjSub_of_lt (Subgroup.mem_top g) hg hlt
    have hJg : J ≤ conjSub g M := by
      have h1 : conjSub g J = J := conjSub_eq_self (le_normalizer_kerIn M ⊤ (Subgroup.mem_top g))
      rw [← h1]
      exact (conjSub g).le_iff_le.mpr kerIn_le
    have htop : conjSub g M = ⊤ := top_unique (hfr ▸ sup_le hle hJg)
    have : M = ⊤ := by
      have := congrArg (conjSub g⁻¹) htop
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, map_top] at this
    exact absurd this (ne_of_lt h.maximal.1)
  have hRJ : R.subgroupOf J = (P : Subgroup J) :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  have := hRn.subgroupOf J
  rwa [hRJ] at this

end MinParabolic

namespace B6

theorem isSolvable_of_twoResidual {Y : Type*} [Group Y] [Finite Y]
    (hK : Group.IsSolvable (twoResidual (⊤ : Subgroup Y))) : Group.IsSolvable Y := by
  have hKn : (twoResidual (⊤ : Subgroup Y)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hp : IsPGroup 2 (Y ⧸ twoResidual (⊤ : Subgroup Y)) := fun q => by
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup Y) y (Subgroup.mem_top y)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  have : Group.IsNilpotent (Y ⧸ twoResidual (⊤ : Subgroup Y)) := hp.isNilpotent
  exact Group.isSolvable_of_ker_le_range (twoResidual (⊤ : Subgroup Y)).subtype
    (QuotientGroup.mk' (twoResidual (⊤ : Subgroup Y)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_of_quotient_pCore {X : Type*} [Group X] [Finite X]
    (h : Group.IsSolvable (X ⧸ CFSG.Open.pCore 2 X)) : Group.IsSolvable X := by
  have hN : IsPGroup 2 (CFSG.Open.pCore 2 X) := CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2
  have : Group.IsNilpotent (CFSG.Open.pCore 2 X) := hN.isNilpotent
  exact Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 X).subtype
    (QuotientGroup.mk' (CFSG.Open.pCore 2 X))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end B6

namespace MinParabolic

variable {Y : Type*} [Group Y] [Finite Y] {T M : Subgroup Y}

theorem fittingSubgroup_eq_kerIn (h : MinParabolic (⊤ : Subgroup Y) T M)
    (hO : CFSG.Open.pCore 2 Y = ⊥) (hns : ¬ Group.IsSolvable Y) :
    CFSG.fittingSubgroup Y = kerIn M ⊤ := by
  apply le_antisymm
  · rcases h.le_kerIn_or_twoResidual_le le_top
        (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (CFSG.fittingSubgroup Y).Normal)).ge
      with hle | hle
    · exact hle
    · exfalso
      apply hns
      refine B6.isSolvable_of_twoResidual ?_
      have hFnil : Group.IsNilpotent (CFSG.fittingSubgroup Y) := inferInstance
      have hKnil : Group.IsNilpotent (twoResidual (⊤ : Subgroup Y)) :=
        Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)
      infer_instance
  · exact le_sSup ⟨inferInstance, h.isNilpotent_kerIn hO⟩

end MinParabolic

section UpperSeries3

variable (X : Type*) [Group X]

@[expose] def O2F : Subgroup X :=
  (CFSG.fittingSubgroup (X ⧸ CFSG.Open.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 X))

@[expose] def O2Fstar : Subgroup X :=
  (CFSG.generalizedFitting (X ⧸ CFSG.Open.pCore 2 X)).comap
    (QuotientGroup.mk' (CFSG.Open.pCore 2 X))

@[expose] def O2E : Subgroup X :=
  (CFSG.layer (X ⧸ CFSG.Open.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 X))

instance instNormalO2E : (O2E X).Normal := by
  unfold O2E
  have : (CFSG.layer (X ⧸ CFSG.Open.pCore 2 X)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  infer_instance

@[expose] def O2E2 : Subgroup X := upperTwo (O2E X)

end UpperSeries3

namespace B6

variable {X : Type*} [Group X] [Finite X]

theorem perfect_le_twoResidual {P : Subgroup X} [Group.IsPerfect P] :
    P ≤ twoResidual (⊤ : Subgroup X) := by
  have hKn : (twoResidual (⊤ : Subgroup X)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hp : IsPGroup 2 (X ⧸ twoResidual (⊤ : Subgroup X)) := fun q => by
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup X) y (Subgroup.mem_top y)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  have : Group.IsNilpotent (X ⧸ twoResidual (⊤ : Subgroup X)) := hp.isNilpotent
  have hperf : Group.IsPerfect (P.map (QuotientGroup.mk' (twoResidual (⊤ : Subgroup X)))) :=
    Group.IsPerfect.map _
  have hbot : P.map (QuotientGroup.mk' (twoResidual (⊤ : Subgroup X))) = ⊥ := by
    by_contra hne
    have : Nontrivial (P.map (QuotientGroup.mk' (twoResidual (⊤ : Subgroup X)))) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable
      (↥(P.map (QuotientGroup.mk' (twoResidual (⊤ : Subgroup X))))) inferInstance
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem layer_le_twoResidual : CFSG.layer X ≤ twoResidual (⊤ : Subgroup X) :=
  sSup_le fun C hC => by
    have : Group.IsPerfect C := hC.1.1
    exact perfect_le_twoResidual

end B6

namespace MinParabolic

variable {X : Type*} [Group X] [Finite X] {T M : Subgroup X}

theorem pCore_le_kerIn (h : MinParabolic (⊤ : Subgroup X) T M) :
    CFSG.Open.pCore 2 X ≤ kerIn M ⊤ := by
  rw [← pCoreOf_top]
  exact h.pCoreOf_le_kerIn

end MinParabolic

namespace B6

theorem isSolvable_of_map {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) (N : Subgroup X)
    (hN : φ.ker ≤ N) [Group.IsSolvable (N.map φ)] [Group.IsSolvable φ.ker] :
    Group.IsSolvable N := by
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hN) (φ.subgroupMap N) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : φ x = 1 := congrArg Subtype.val hx
  refine ⟨⟨x, h1⟩, ?_⟩
  apply Subtype.ext
  rfl

end B6

namespace MinParabolic

variable {X : Type*} [Group X] [Finite X] {T M : Subgroup X}

theorem isSolvable_kerIn (h : MinParabolic (⊤ : Subgroup X) T M) :
    Group.IsSolvable (kerIn M ⊤) := by
  set φ₂ := QuotientGroup.mk' (CFSG.Open.pCore 2 X) with hφ₂
  have hsurj₂ : Function.Surjective φ₂ := QuotientGroup.mk'_surjective _
  have hker₂ : φ₂.ker ≤ M := by
    rw [hφ₂, QuotientGroup.ker_mk']
    exact h.pCore_le_M
  have hmpY := h.map_of_surjective hsurj₂ hker₂
  have hOY : CFSG.Open.pCore 2 (X ⧸ CFSG.Open.pCore 2 X) = ⊥ := B6.pCore_quotient_pCore
  have hnil := hmpY.isNilpotent_kerIn hOY
  rw [kerIn_map_top hsurj₂ hker₂] at hnil
  have h1 : Group.IsSolvable ((kerIn M ⊤).map φ₂) := by
    have := hnil
    infer_instance
  have h2 : IsPGroup 2 φ₂.ker := by
    rw [hφ₂, QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2
  have : Group.IsNilpotent φ₂.ker := h2.isNilpotent
  exact B6.isSolvable_of_map φ₂ _ (by
    rw [hφ₂, QuotientGroup.ker_mk']; exact h.pCore_le_kerIn)

theorem kerIn_eq_O2F (h : MinParabolic (⊤ : Subgroup X) T M) (hns : ¬ Group.IsSolvable X) :
    kerIn M ⊤ = O2F X := by
  set φ₂ := QuotientGroup.mk' (CFSG.Open.pCore 2 X) with hφ₂
  have hsurj₂ : Function.Surjective φ₂ := QuotientGroup.mk'_surjective _
  have hker₂ : φ₂.ker ≤ M := by
    rw [hφ₂, QuotientGroup.ker_mk']
    exact h.pCore_le_M
  have hmpY := h.map_of_surjective hsurj₂ hker₂
  have hOY : CFSG.Open.pCore 2 (X ⧸ CFSG.Open.pCore 2 X) = ⊥ := B6.pCore_quotient_pCore
  have hnsY : ¬ Group.IsSolvable (X ⧸ CFSG.Open.pCore 2 X) := fun hs =>
    hns (B6.isSolvable_of_quotient_pCore hs)
  have hF := hmpY.fittingSubgroup_eq_kerIn hOY hnsY
  rw [kerIn_map_top hsurj₂ hker₂] at hF
  unfold O2F
  rw [hF, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr h.pCore_le_kerIn]

theorem O2F_dichotomy (h : MinParabolic (⊤ : Subgroup X) T M) (hns : ¬ Group.IsSolvable X) :
    (kerIn M ⊤ = O2F X ∧ O2F X = O2Fstar X) ∨
      (kerIn M ⊤ = CFSG.solvableRadical X ∧ O2E2 X = ⊤) := by
  set φ₂ := QuotientGroup.mk' (CFSG.Open.pCore 2 X) with hφ₂
  have hsurj₂ : Function.Surjective φ₂ := QuotientGroup.mk'_surjective _
  have hker₂ : φ₂.ker ≤ M := by
    rw [hφ₂, QuotientGroup.ker_mk']
    exact h.pCore_le_M
  have hmpY := h.map_of_surjective hsurj₂ hker₂
  have hOY : CFSG.Open.pCore 2 (X ⧸ CFSG.Open.pCore 2 X) = ⊥ := B6.pCore_quotient_pCore
  have hnsY : ¬ Group.IsSolvable (X ⧸ CFSG.Open.pCore 2 X) := fun hs =>
    hns (B6.isSolvable_of_quotient_pCore hs)
  have hF := hmpY.fittingSubgroup_eq_kerIn hOY hnsY
  rw [kerIn_map_top hsurj₂ hker₂] at hF
  have h3a := h.kerIn_eq_O2F hns
  by_cases hE : CFSG.layer (X ⧸ CFSG.Open.pCore 2 X) ≤
      CFSG.fittingSubgroup (X ⧸ CFSG.Open.pCore 2 X)
  · left
    refine ⟨h3a, ?_⟩
    unfold O2F O2Fstar; simp only [CFSG.generalizedFitting.eq_sup]
    rw [sup_eq_left.mpr hE]
  · right
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      ·
        have hsolvJ : Group.IsSolvable (kerIn M ⊤) := h.isSolvable_kerIn
        exact le_sSup ⟨inferInstance, hsolvJ⟩
      · refine sSup_le fun N hN => ?_
        obtain ⟨hNn, hNs⟩ := hN
        rcases h.le_kerIn_or_twoResidual_le le_top
          (Subgroup.normalizer_eq_top_iff.mpr hNn).ge with hle | hle
        · exact hle
        · exfalso
          apply hns
          have := hNs
          exact B6.isSolvable_of_twoResidual
            (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
    · refine (B6.upperTwo_eq_top_iff (O2E X)).mpr fun x => ?_
      have hEn : (CFSG.layer (X ⧸ CFSG.Open.pCore 2 X)).Normal := by
        have : (CFSG.layer (X ⧸ CFSG.Open.pCore 2 X)).Characteristic :=
          CFSG.LocalCores.layer_characteristic
        infer_instance
      have hKE : twoResidual (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X)) ≤
          CFSG.layer (X ⧸ CFSG.Open.pCore 2 X) := by
        rcases hmpY.le_kerIn_or_twoResidual_le le_top
            (Subgroup.normalizer_eq_top_iff.mpr hEn).ge with hle | hle
        · exfalso
          apply hE
          rw [hF, ← kerIn_map_top hsurj₂ hker₂]
          exact hle
        · exact hle
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient
        (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X)) (φ₂ x) (Subgroup.mem_top _)
      refine ⟨k, Subgroup.mem_comap.mpr ?_⟩
      rw [map_pow]
      exact hKE hk

end MinParabolic

namespace MinParabolic

theorem eq_twoResidual_sup [Finite G] {H T M : Subgroup G} (h : MinParabolic H T M) :
    H = twoResidual H ⊔ T := by
  rw [sup_comm]
  exact (sup_twoResidual_eq h.isSylow).symm

end MinParabolic

namespace MinParabolic

variable {X : Type*} [Group X] [Finite X] {T M : Subgroup X}

theorem nonsolvable_structure (h : MinParabolic (⊤ : Subgroup X) T M)
    (hns : ¬ Group.IsSolvable X) :
    ∃ L : Subgroup (X ⧸ kerIn M ⊤), IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      L ≤ (twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)) ∧
      (twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)) =
        ⨆ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)), conjSub t L ∧
      sSupIndep {S : Subgroup (X ⧸ kerIn M ⊤) |
        ∃ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)), S = conjSub t L} ∧
      (∀ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)),
        ((conjSub t L).subgroupOf
          ((twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)))).Normal) ∧
      autOn ⊤ L ∈ uFamHat (autOn ⊤ L) (autOn (T.map (QuotientGroup.mk' (kerIn M ⊤))) L) ∧
      IsUniqueMaxOver (autOn ⊤ L) (autOn (T.map (QuotientGroup.mk' (kerIn M ⊤))) L)
        (autOn (M.map (QuotientGroup.mk' (kerIn M ⊤))) L) := by
  set J := kerIn M ⊤ with hJ
  set φ := QuotientGroup.mk' J with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker ≤ M := by
    rw [hφ, QuotientGroup.ker_mk']
    exact kerIn_le
  have hmp := h.map_of_surjective hsurj hker
  have hJ' : kerIn (M.map φ) ⊤ = ⊥ := by
    rw [kerIn_map_top hsurj hker]
    exact QuotientGroup.map_mk'_self J
  have hnsZ : ¬ Group.IsSolvable (X ⧸ J) := fun hs => by
    have := h.isSolvable_kerIn
    exact hns (Group.isSolvable_of_ker_le_range J.subtype φ
      (by rw [hφ, QuotientGroup.ker_mk', Subgroup.range_subtype]))
  obtain ⟨L, hL, hLn, hLK, hgen, hind, hnorm⟩ :=
    exists_simple_factor hmp hJ' hnsZ
  have hK := twoResidual_map_top (φ := φ) hsurj
  have hL2 : Even (Nat.card L) := by
    by_contra hodd
    have hsolv : Group.IsSolvable L := CFSG.FeitThompson.isSolvable_of_odd_natCard L (Nat.not_even_iff_odd.mp hodd)
    exact hLn (IsMulCommutative.of_comm ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv))
  obtain ⟨hA1, hA2⟩ := aut_clause hmp hL hLn hL2 hLK hgen hind hnorm
  rw [hK]
  exact ⟨L, hL, hLn, hLK, hgen, hind, hnorm, hA1, hA2⟩

end MinParabolic

end CFSG.Quasithin
