module

public import CFSG.Quasithin.EmptyFaithful.S146yCom
public import CFSG.Quasithin.EmptyFaithful.S146F22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section U3

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.false_of_le_normalizer (S : Setting146 G T M) {K T₀ : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hL : KbarIsL3Two K ∨ KbarIsA6 K) (hsimple : IsSimpleGroup (KBar K))
    (hT₀T : T₀ ≤ T) (hP : T ⊓ K ≤ T₀) (hn : K ≤ Subgroup.normalizer (T₀ : Set G)) : False := by
  have hcard := S.card_kbarImage hK hL
  have hDn : ((T ⊓ K).subgroupOf K).Normal := by
    refine ⟨fun d hd g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    have hd' : (d : G) ∈ T₀ := hP hd
    have h1 : (g : G) * d * (g : G)⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp (hn g.2) d).mp hd'
    exact ⟨hT₀T h1, K.mul_mem (K.mul_mem g.2 d.2) (K.inv_mem g.2)⟩
  have hDbar : (kbarImage K T).Normal :=
    Subgroup.Normal.map hDn (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hcardK : Nat.card (KBar K) = 168 ∨ Nat.card (KBar K) = 360 := by
    rcases hL with h | h
    · left
      obtain ⟨e⟩ := KbarIsL3Two.nonempty h
      rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field]
      simp [Fin.prod_univ_succ]
    · right
      obtain ⟨e⟩ := KbarIsA6.nonempty h
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
  have := hsimple
  have := hDbar
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (kbarImage K T) with h | h
  · rw [h, Subgroup.card_bot] at hcard
    omega
  · rw [h, Subgroup.card_top] at hcard
    omega

theorem Setting146.conj_mem_inf_of_normalizes (S : Setting146 G T M) (hB : HypB146 T M)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hK₂ : K₂ ∈ cComp (mcOf T)) (hne : K₂ ≠ K₁)
    (hN : K₂ ≤ Subgroup.normalizer (K₁ : Set G)) :
    ∀ k₂ ∈ K₂, ∀ d ∈ T ⊓ K₁, k₂ * d * k₂⁻¹ ∈ T ⊓ K₁ := by
  intro k₂ hk₂ d hd
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hcomm : ⁅K₂, K₁⁆ ≤ pCoreOf 2 (mcOf T) :=
    (cComp_ne_commutator_le_solvRad hK₂ hK₁ hne).trans (solvRad_le_pCoreOf_of_oddCore (hB _ hG))
  have h3 : K₁ ⊓ pCoreOf 2 (mcOf T) ≤ pCoreOf 2 K₁ := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 (mcOf T)).to_le inf_le_right)
    intro k hk
    exact F7.mem_normalizer_inf (Subgroup.le_normalizer hk)
      (le_normalizer_pCoreOf 2 (mcOf T) (hK₁G hk))
  have hOT : pCoreOf 2 K₁ ≤ T ⊓ K₁ := S.pCoreOf_le_inf hK₁
  have hcm : k₂ * d * k₂⁻¹ * d⁻¹ ∈ T ⊓ K₁ := by
    refine hOT (h3 ⟨?_, hcomm ?_⟩)
    · have h1 : k₂ * (d : G) * k₂⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp (hN hk₂) _).mp hd.2
      exact K₁.mul_mem h1 (K₁.inv_mem hd.2)
    · exact Subgroup.commutator_mem_commutator hk₂ hd.2
  have e : k₂ * d * k₂⁻¹ = (k₂ * d * k₂⁻¹ * d⁻¹) * d := by group
  rw [e]
  exact (T ⊓ K₁).mul_mem hcm hd

theorem Setting146.mem_T_of_prod_normalizes (S : Setting146 G T M) (hB : HypB146 T M)
    {K₁ K₂ T₀ : Subgroup G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hK₂ : K₂ ∈ cComp (mcOf T)) (hne : K₂ ≠ K₁)
    (hL₁ : KbarIsL3Two K₁) (hN : K₂ ≤ Subgroup.normalizer (K₁ : Set G)) (hT₀T : T₀ ≤ T)
    (hP₁ : T ⊓ K₁ ≤ T₀) {k₁ k₂ : G} (hk₁ : k₁ ∈ K₁) (hk₂ : k₂ ∈ K₂)
    (hn : ∀ x ∈ T₀, (k₁ * k₂) * x * (k₁ * k₂)⁻¹ ∈ T₀) : k₁ ∈ T := by
  refine S.mem_of_normalizes hK₁ hL₁ hk₁ (fun d hd => ?_)
  have hd' : k₂⁻¹ * d * k₂ ∈ T ⊓ K₁ := by
    have := S.conj_mem_inf_of_normalizes hB hK₁ hK₂ hne hN k₂⁻¹ (K₂.inv_mem hk₂) d hd
    simpa using this
  have h1 := hn _ (hP₁ hd')
  have e : (k₁ * k₂) * (k₂⁻¹ * d * k₂) * (k₁ * k₂)⁻¹ = k₁ * d * k₁⁻¹ := by group
  rw [e] at h1
  exact hT₀T h1

theorem Setting146.normalizer_of_pair (S : Setting146 G T M) {K Kt : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hKt : Kt ∈ cComp (mcOf T)) (hne : Kt ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kt) :
    Kt ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ Subgroup.normalizer (Kt : Set G) := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hinj : ∀ (x : G) (A B : Subgroup G), conjSub x A = conjSub x B → A = B := fun x A B h =>
    Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective h
  constructor
  · intro x hx
    have hxH : x ∈ mcOf T := le_of_mem_cComp hKt hx
    rcases hcomps _ (map_conj_mem_cComp hK hxH) with h | h
    · exact mem_normalizer_of_conjSub_eq h
    · exfalso
      have h2 : conjSub x Kt = Kt := conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hx)
      exact hne (hinj x _ _ (h.trans h2.symm)).symm
  · intro x hx
    have hxH : x ∈ mcOf T := le_of_mem_cComp hK hx
    rcases hcomps _ (map_conj_mem_cComp hKt hxH) with h | h
    · exfalso
      have h2 : conjSub x K = K := conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hx)
      exact hne (hinj x _ _ (h.trans h2.symm))
    · exact mem_normalizer_of_conjSub_eq h

omit [Finite G] in
theorem le_centralizer_U₁_of_ne {K Kp U₁ U₂ : Subgroup G} {s : G}
    (hdec : IsDecompUK T M K U₁ U₂ s) (c22 : Conc14622 T M K) (hKp : Kp ∈ cComp (mcOf T))
    (hKpK : Kp ≠ K) : Kp ≤ Subgroup.centralizer (U₁ : Set G) := by
  have hUK : ⁅uOfL22 T M, K⁆ ≤ Subgroup.centralizer (Kp : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (c22.2 Kp hKp hKpK)
  have hZ : Zz ≤ Subgroup.centralizer (Kp : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun k hk => S146T.comm_Z (le_of_mem_cComp hKp hk) hz
  have hsup : ⁅uOfL22 T M, K⁆ ⊔ Zz ≤ Subgroup.centralizer (Kp : Set G) := sup_le hUK hZ
  intro k hk
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hx' : x ∈ ⁅uOfL22 T M, K⁆ ⊔ Zz := by
    rw [hdec.sup]
    exact Subgroup.mem_sup_left hx
  exact (Subgroup.mem_centralizer_iff.mp (hsup hx') k hk).symm

theorem input14624U3_of_A6 (hA6 : U1A6Res) : Input14624U3 := by
  intro G _ _ T M S hB K U₁ U₂ s u hctx
  have hctx' := hctx
  obtain ⟨c19, _c20, c23, hK, c21, c22, hdec, hch⟩ := hctx'
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have h2 : (tZero T u).relIndex T = 2 :=
    (input14624U1_of_A6 hA6 G T M S hB K U₁ U₂ s u hctx).2
  have hT₀T : tZero T u ≤ T := fun x hx => hx.1
  have hTn : ∀ t ∈ T, ∀ x ∈ tZero T u, t * x * t⁻¹ ∈ tZero T u := by
    have hnorm : ((tZero T u).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
    intro t ht x hx
    exact hnorm.conj_mem ⟨x, hT₀T hx⟩ hx ⟨t, ht⟩
  have hTN : T ≤ Subgroup.normalizer (tZero T u : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hTn t ht x, fun hx => ?_⟩
    have := hTn t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hmul := exists_mul_of_perfectCore hTH c23
  have hsimple : IsSimpleGroup (KBar K) := (c19 (mcOf T) hG).2 K hK
  apply le_antisymm
  · intro h hh
    obtain ⟨hhN, hhH⟩ := hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hmul h hhH
    have haN : a ∈ Subgroup.normalizer (tZero T u : Set G) := by
      have := (Subgroup.normalizer (tZero T u : Set G)).mul_mem hhN
        ((Subgroup.normalizer (tZero T u : Set G)).inv_mem (hTN hb))
      simpa using this
    have hn : ∀ x ∈ tZero T u, a * x * a⁻¹ ∈ tZero T u := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp haN x).mp hx
    suffices haT : a ∈ T from T.mul_mem haT hb
    have hKU₁ := S.le_normalizer_U₁_of_decomp hK hdec
    rcases c21 with ⟨hper, hL⟩ | ⟨hc2, hL3⟩ | ⟨Kp, hKp, hKpK, hHK, hHKp, hper, hL3, hL3p⟩
    ·
      have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
        rw [← hper]
        exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
      obtain ⟨hN⟩ : Nonempty (T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u) := by
        rcases hch with ⟨-, -, -, hN⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
        · exact ⟨hN⟩
        · exact absurd (hKn (hTH ht)) htn
      have hP₁ : T ⊓ K ≤ tZero T u := fun x hx => hN ⟨hx.1, hKU₁ hx.2⟩
      have haK : a ∈ K := hper ▸ ha
      have hB' : T ≤ Subgroup.normalizer (tZero T u : Set G) ⊓ mcOf T := le_inf hTN hTH
      rcases S.inf_le_or_le hK hdec.mem.1 hdec.mem.2 hdec.dynkin hB' with hle | hle
      · exact hle ⟨haK, ⟨haN, perfectCore_le _ ha⟩⟩
      · exact (S.false_of_le_normalizer hK hL hsimple hT₀T hP₁ (hle.trans inf_le_left)).elim
    ·
      obtain ⟨t, ht, htn, hper⟩ := hc2
      obtain ⟨hN⟩ : Nonempty (T ⊓ Subgroup.normalizer (K : Set G) ≤ tZero T u) := by
        rcases hch with ⟨hnc2, -⟩ | ⟨-, -, -, hN⟩
        · exact absurd ⟨t, ht, htn, hper⟩ hnc2
        · exact ⟨hN⟩
      set Kt := conjSub t K with hKt_def
      have hKt : Kt ∈ cComp (mcOf T) := map_conj_mem_cComp hK (hTH ht)
      have hKtK : Kt ≠ K := fun h => htn (A38.map_conj_eq_iff.mp h)
      have hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kt := fun L hL =>
        cComp_eq_of_le_sup hL hK hKt
          (hper ▸ le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL))
      obtain ⟨hKtN, -⟩ := S.normalizer_of_pair hK hKt hKtK hcomps
      have hP₁ : T ⊓ K ≤ tZero T u := fun x hx => hN ⟨hx.1, Subgroup.le_normalizer hx.2⟩
      have haKK : a ∈ K ⊔ Kt := hper ▸ ha
      have hprod := Subgroup.coe_mul_of_right_le_normalizer_left K Kt hKtN
      have haKK' : a ∈ ((K ⊔ Kt : Subgroup G) : Set G) := haKK
      rw [hprod] at haKK'
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Set.mem_mul.mp haKK'
      have hk₁T : k₁ ∈ T :=
        S.mem_T_of_prod_normalizes hB hK hKt hKtK hL3 hKtN hT₀T hP₁ hk₁ hk₂ hn
      have hn₂ : ∀ x ∈ tZero T u, k₂ * x * k₂⁻¹ ∈ tZero T u := by
        intro x hx
        have h1 := hTn k₁⁻¹ (T.inv_mem hk₁T) _ (hn x hx)
        have e : k₁⁻¹ * (k₁ * k₂ * x * (k₁ * k₂)⁻¹) * k₁⁻¹⁻¹ = k₂ * x * k₂⁻¹ := by group
        rwa [e] at h1
      have hk' : t⁻¹ * k₂ * t ∈ K := by
        have := mem_conjSub.mp hk₂
        exact this
      have hn' : ∀ x ∈ tZero T u, (t⁻¹ * k₂ * t) * x * (t⁻¹ * k₂ * t)⁻¹ ∈ tZero T u := by
        intro x hx
        have h1 := hTn t⁻¹ (T.inv_mem ht) _ (hn₂ _ (hTn t ht x hx))
        have e : t⁻¹ * (k₂ * (t * x * t⁻¹) * k₂⁻¹) * t⁻¹⁻¹ =
            (t⁻¹ * k₂ * t) * x * (t⁻¹ * k₂ * t)⁻¹ := by group
        rw [e] at h1
        exact h1
      have hk'T : t⁻¹ * k₂ * t ∈ T :=
        S.mem_of_normalizes hK hL3 hk' (fun d hd => hT₀T (hn' d (hP₁ hd)))
      have hk₂T : k₂ ∈ T := by
        have := T.mul_mem (T.mul_mem ht hk'T) (T.inv_mem ht)
        simpa [mul_assoc] using this
      exact T.mul_mem hk₁T hk₂T
    ·
      obtain ⟨hN⟩ : Nonempty (T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u) := by
        rcases hch with ⟨-, -, -, hN⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
        · exact ⟨hN⟩
        · exact absurd (hHK (hTH ht)) htn
      have hP₁ : T ⊓ K ≤ tZero T u := fun x hx => hN ⟨hx.1, hKU₁ hx.2⟩
      have hKpU : Kp ≤ Subgroup.normalizer (U₁ : Set G) :=
        (le_centralizer_U₁_of_ne hdec c22 hKp hKpK).trans (Subgroup.centralizer_le_normalizer _)
      have hP₂ : T ⊓ Kp ≤ tZero T u := fun x hx => hN ⟨hx.1, hKpU hx.2⟩
      have hKpN : Kp ≤ Subgroup.normalizer (K : Set G) := fun x hx => hHK (le_of_mem_cComp hKp hx)
      have haKK : a ∈ K ⊔ Kp := hper ▸ ha
      have hprod := Subgroup.coe_mul_of_right_le_normalizer_left K Kp hKpN
      have haKK' : a ∈ ((K ⊔ Kp : Subgroup G) : Set G) := haKK
      rw [hprod] at haKK'
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Set.mem_mul.mp haKK'
      have hk₁T : k₁ ∈ T :=
        S.mem_T_of_prod_normalizes hB hK hKp hKpK hL3 hKpN hT₀T hP₁ hk₁ hk₂ hn
      have hn₂ : ∀ x ∈ tZero T u, k₂ * x * k₂⁻¹ ∈ tZero T u := by
        intro x hx
        have h1 := hTn k₁⁻¹ (T.inv_mem hk₁T) _ (hn x hx)
        have e : k₁⁻¹ * (k₁ * k₂ * x * (k₁ * k₂)⁻¹) * k₁⁻¹⁻¹ = k₂ * x * k₂⁻¹ := by group
        rwa [e] at h1
      have hk₂T : k₂ ∈ T :=
        S.mem_of_normalizes hKp hL3p hk₂ (fun d hd => hT₀T (hn₂ d (hP₂ hd)))
      exact T.mul_mem hk₁T hk₂T
  · exact le_inf hTN hTH

end U3

end CFSG.Quasithin
