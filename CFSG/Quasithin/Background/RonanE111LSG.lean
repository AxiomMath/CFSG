module

public import CFSG.Quasithin.Background.RonanE111Lift

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G]

theorem ronanE111_isElemAbelian_subgroupOf {p : ℕ} {A : Subgroup G} (h : IsElemAbelian p A)
    (K : Subgroup G) : IsElemAbelian p (A.subgroupOf K) := by
  have := h.1
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have hc := congrArg Subtype.val (mul_comm'
      (⟨((x : K) : G), Subgroup.mem_subgroupOf.mp x.2⟩ : ↥A)
      ⟨((y : K) : G), Subgroup.mem_subgroupOf.mp y.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using hc
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h.2 _ (Subgroup.mem_subgroupOf.mp hx)

theorem SemisimpleMod.subgroupOf {T D Y : Subgroup G} {𝒟 : Set (Subgroup G)} {K : Subgroup G}
    (h : SemisimpleMod T D Y 𝒟) (hTK : T ≤ K) (hDK : D ≤ K) (hYK : Y ≤ K) :
    SemisimpleMod (T.subgroupOf K) (D.subgroupOf K) (Y.subgroupOf K)
      ((fun S : Subgroup G => S.subgroupOf K) '' 𝒟) := by
  have hmemK : ∀ S ∈ 𝒟, S ≤ K := fun S hS => (h.le_D S hS).trans hDK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    exact Subgroup.subgroupOf_mono K (h.Y_le S hS)
  · rintro _ ⟨S, hS, rfl⟩
    exact Subgroup.subgroupOf_mono K (h.le_D S hS)
  · rintro _ ⟨S, hS, rfl⟩ M hYM hMS hMn
    have hMbS : M.map K.subtype ≤ S := by
      calc M.map K.subtype ≤ (S.subgroupOf K).map K.subtype := Subgroup.map_mono hMS
        _ = S := Subgroup.map_subgroupOf_eq_of_le (hmemK S hS)
    have hYMb : Y ≤ M.map K.subtype := by
      intro y hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hYK hy⟩, hYM (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
    have hconj : ∀ s ∈ S, ∀ m ∈ M.map K.subtype, s * m * s⁻¹ ∈ M.map K.subtype := by
      intro s hs m hm
      obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.mp hm
      have hsK : s ∈ K := hmemK S hS hs
      have hs' : (⟨s, hsK⟩ : ↥K) ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.mpr hs
      have hc := hMn.conj_mem ⟨m', hMS hm'⟩ (Subgroup.mem_subgroupOf.mpr hm') ⟨⟨s, hsK⟩, hs'⟩
      exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mp hc, rfl⟩
    have hMbnorm : ((M.map K.subtype).subgroupOf S).Normal :=
      normal_subgroupOf_of_conj hMbS hconj
    rcases h.simple S hS (M.map K.subtype) hYMb hMbS hMbnorm with e | e
    · left
      calc M = (M.map K.subtype).subgroupOf K :=
            (Subgroup.comap_map_eq_self_of_injective K.subtype_injective M).symm
        _ = Y.subgroupOf K := by rw [e]
    · right
      calc M = (M.map K.subtype).subgroupOf K :=
            (Subgroup.comap_map_eq_self_of_injective K.subtype_injective M).symm
        _ = S.subgroupOf K := by rw [e]
  · rintro _ ⟨S, hS, rfl⟩ hc
    apply h.nonab S hS
    have h1 : (⁅S.subgroupOf K, S.subgroupOf K⁆).map K.subtype ≤
        (Y.subgroupOf K).map K.subtype := Subgroup.map_mono hc
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hmemK S hS),
      Subgroup.map_subgroupOf_eq_of_le hYK] at h1
    exact h1
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩ hne
    have hSS : S ≠ S' := fun e => hne (by rw [e])
    rw [← Subgroup.map_subtype_le_map_subtype, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le (hmemK S hS), Subgroup.map_subgroupOf_eq_of_le (hmemK S' hS'),
      Subgroup.map_subgroupOf_eq_of_le hYK]
    exact h.comm S hS S' hS' hSS
  · rw [← sSup_eq_iSup, E111R.sSup_image_subgroupOf hmemK, sSup_eq_iSup, h.gen]
  · rintro _ ⟨S, hS, rfl⟩ t ht
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    exact ⟨A1b.conjSub (t : G) S, h.conj S hS (t : G) htT,
      (E111R.conjSub_subgroupOf t (hmemK S hS)).symm⟩
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩
    obtain ⟨t, ht, hts⟩ := h.trans S hS S' hS'
    have htK : t ∈ K := hTK ht
    refine ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.mpr ht, ?_⟩
    rw [E111R.conjSub_subgroupOf ⟨t, htK⟩ (hmemK S hS)]
    exact congrArg (fun X : Subgroup G => X.subgroupOf K) hts

theorem lift_semisimple_sub [Finite G] {n : ℕ} (hn : 1 ≤ n) {T T₀ N Y A : Subgroup G}
    {𝒟 : Set (Subgroup G)}
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hAab : IsElemAbelian 2 A)
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t)
    (hT₀N : T₀ ≤ Subgroup.normalizer (N : Set G)) (hT₀Y : T₀ ≤ Subgroup.normalizer (Y : Set G))
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) (hYN : Y ≤ N) (hperf : ⁅N, N⁆ = N)
    (hYs : Group.IsSolvable ↥Y) (hSM : SemisimpleMod T₀ N Y 𝒟)
    (hSyl : IsSylowIn 2 (T ⊓ (N ⊔ T₀)) (N ⊔ T₀)) (hτ : E1.tauOf ⊤ T A ≤ T₀)
    (hmove : ∃ S ∈ 𝒟, ∃ a ∈ A, ∃ s ∈ S, a * s * a⁻¹ * s⁻¹ ∉ Y)
    (hrank : ∀ S ∈ 𝒟, (∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S, a * s * a⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (S : Set G), (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
        B.relIndex (A ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n) :
    N ≤ T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K := by
  set K : Subgroup G := N ⊔ T₀ with hKdef
  have hNK : N ≤ K := le_sup_left
  have hT₀K : T₀ ≤ K := le_sup_right
  have hYK : Y ≤ K := hYN.trans hNK
  have hAK : A ≤ K := hAT₀.trans hT₀K
  have hAT : A ≤ T := hAT₀.trans hT₀T
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hT₀N
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := sup_le hNY hT₀Y
  haveI hNn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  haveI hYn : (Y.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hKY
  have hmemK : ∀ S ∈ 𝒟, S ≤ K := fun S hS => (hSM.le_D S hS).trans hNK
  have hSylK : IsSylowIn 2 ((T ⊓ K).subgroupOf K) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ K ≤ K), Subgroup.map_top,
      Subgroup.range_subtype]
    exact hSyl
  have hT₀T' : T₀.subgroupOf K ≤ (T ⊓ K).subgroupOf K :=
    Subgroup.subgroupOf_mono K (le_inf hT₀T hT₀K)
  have hAT₀' : A.subgroupOf K ≤ T₀.subgroupOf K := Subgroup.subgroupOf_mono K hAT₀
  have hAab' : IsElemAbelian 2 (A.subgroupOf K) := ronanE111_isElemAbelian_subgroupOf hAab K
  have hT₀A' : ∀ t ∈ T₀.subgroupOf K, ∀ a ∈ A.subgroupOf K, t * a = a * t := fun t ht a ha =>
    Subtype.ext (hT₀A _ (Subgroup.mem_subgroupOf.mp ht) _ (Subgroup.mem_subgroupOf.mp ha))
  have hDperf : ⁅N.subgroupOf K, N.subgroupOf K⁆ = N.subgroupOf K := by
    rw [E111R.commutator_subgroupOf hNK hNK, hperf]
  have hDT₀' : N.subgroupOf K ⊔ T₀.subgroupOf K = ⊤ := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hNK,
      Subgroup.map_subgroupOf_eq_of_le hT₀K, Subgroup.map_top, Subgroup.range_subtype, hKdef]
  have hYsK : Group.IsSolvable ↥(Y.subgroupOf K) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYK).symm.surjective
  have hSMK := hSM.subgroupOf hT₀K hNK hYK
  have hmove' : ∃ S ∈ (fun S : Subgroup G => S.subgroupOf K) '' 𝒟,
      ¬ A.subgroupOf K ≤ Cmod S (Y.subgroupOf K) := by
    obtain ⟨S, hS, a, ha, s, hs, hnot⟩ := hmove
    refine ⟨S.subgroupOf K, ⟨S, hS, rfl⟩, fun hle => hnot ?_⟩
    have hmem := hle (Subgroup.mem_subgroupOf.mpr ha : (⟨a, hAK ha⟩ : ↥K) ∈ A.subgroupOf K)
    rw [mem_Cmod_iff] at hmem
    have key := Subgroup.mem_subgroupOf.mp (hmem ⟨s, hmemK S hS hs⟩
      (Subgroup.mem_subgroupOf.mpr hs))
    simpa using key
  have hrank' : ∀ S' ∈ (fun S : Subgroup G => S.subgroupOf K) '' 𝒟,
      ¬ A.subgroupOf K ⊓ Subgroup.normalizer (S' : Set ↥K) ≤ Cmod S' (Y.subgroupOf K) →
      (A.subgroupOf K ⊓ Subgroup.normalizer (S' : Set ↥K) ⊓ Cmod S' (Y.subgroupOf K)).relIndex
        (A.subgroupOf K ⊓ Subgroup.normalizer (S' : Set ↥K)) ≤ 2 ^ n := by
    rintro _ ⟨S, hS, rfl⟩ hnot
    have hSK : S ⊓ K = S := inf_eq_left.mpr (hmemK S hS)
    have hex : ∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S, a * s * a⁻¹ * s⁻¹ ∉ Y := by
      by_contra hc
      push Not at hc
      apply hnot
      intro x hx
      obtain ⟨hxA, hxN⟩ := Subgroup.mem_inf.mp hx
      have hxG : (x : G) ∈ A ⊓ Subgroup.normalizer (S : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxA, ?_⟩
        have h1 := (E111R.mem_normalizer_subgroupOf_iff (D := S)).mp hxN
        rwa [hSK] at h1
      rw [mem_Cmod_iff]
      intro s hs
      have key := hc (x : G) hxG (s : G) (Subgroup.mem_subgroupOf.mp hs)
      exact Subgroup.mem_subgroupOf.mpr (by simpa using key)
    obtain ⟨B, hBsub, hBcent, hBidx⟩ := hrank S hS hex
    have hM : A.subgroupOf K ⊓ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) =
        (A ⊓ Subgroup.normalizer (S : Set G)).subgroupOf K := by
      ext k
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, E111R.mem_normalizer_subgroupOf_iff, hSK]
    have hBK : B.subgroupOf K ≤
        A.subgroupOf K ⊓ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
      rw [hM]
      exact Subgroup.subgroupOf_mono K hBsub
    have hBC : B.subgroupOf K ≤ Cmod (S.subgroupOf K) (Y.subgroupOf K) := by
      intro k hk
      rw [mem_Cmod_iff]
      intro s hs
      have hkB : (k : G) ∈ B := Subgroup.mem_subgroupOf.mp hk
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hBcent (k : G) hkB (s : G) hsS)
    have hne : (B.subgroupOf K).relIndex
        (A.subgroupOf K ⊓ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K)) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    calc (A.subgroupOf K ⊓ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊓
          Cmod (S.subgroupOf K) (Y.subgroupOf K)).relIndex
          (A.subgroupOf K ⊓ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K))
        ≤ (B.subgroupOf K).relIndex
          (A.subgroupOf K ⊓ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K)) :=
          Subgroup.relIndex_le_of_le_left (le_inf hBK hBC) hne
      _ = (B.subgroupOf K).relIndex ((A ⊓ Subgroup.normalizer (S : Set G)).subgroupOf K) := by
          rw [hM]
      _ = B.relIndex (A ⊓ Subgroup.normalizer (S : Set G)) :=
          Subgroup.relIndex_subgroupOf
            ((inf_le_left : A ⊓ Subgroup.normalizer (S : Set G) ≤ A).trans hAK)
      _ ≤ 2 ^ n := hBidx
  have hLift := lift_semisimple (Q := ↥K) hn hSylK hT₀T' hAT₀' hAab' hT₀A' hDperf hDT₀' hYsK
    hSMK hmove' hrank'
  have hmem : ∀ K' : Subgroup ↥K, E1.IsE n ⊤ ((T ⊓ K).subgroupOf K) (A.subgroupOf K) K' →
      E1.IsE n ⊤ T A (K'.map K.subtype) := by
    intro K' hK'
    have h1 : E1.IsE n K (((T ⊓ K).subgroupOf K).map K.subtype) ((A.subgroupOf K).map K.subtype)
        (K'.map K.subtype) := (E1.isE_map_subtype K).mpr hK'
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ K ≤ K),
      Subgroup.map_subgroupOf_eq_of_le hAK] at h1
    exact E1.eight_two hT hAT hAab le_top (hτ.trans (le_inf hT₀T hT₀K)) hSyl h1
  have hfin : (N.subgroupOf K).map K.subtype ≤
      T ⊔ ⨆ X ∈ {X : Subgroup G | E1.IsE n ⊤ T A X}, X := by
    refine (Subgroup.map_mono hLift).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ K ≤ K)]
    simp only [Subgroup.map_iSup]
    exact sup_le_sup inf_le_left (iSup_le fun K' => iSup_le fun hK' =>
      le_iSup₂_of_le (K'.map K.subtype) (hmem K' hK') le_rfl)
  rw [Subgroup.map_subgroupOf_eq_of_le hNK] at hfin
  exact hfin

end CFSG.Quasithin.RonanE111
