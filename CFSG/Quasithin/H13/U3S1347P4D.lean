module

public import CFSG.Quasithin.H13.U3S1347P4C
public import CFSG.Quasithin.H13.U3S1347N
public import CFSG.Quasithin.H13.U3S1348K

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem eq_top_of_not_le_pCore' {K : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) {N : Subgroup ↥K} [N.Normal]
    (hnot : ¬ N ≤ CFSG.pCore 2 ↥K) : N = ⊤ := by
  let Nbar : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
  have : Nbar.Normal := Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Nbar with h | h
  · exfalso
    apply hnot
    intro x hx
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈ Nbar := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  · have hall : ∀ x : ↥K, ∃ n ∈ N, ∃ p ∈ CFSG.pCore 2 ↥K, x = n * p := by
      intro x
      have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈ Nbar := by rw [h]; trivial
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, n⁻¹ * x, ?_, by simp⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnx
      exact QuotientGroup.eq.1 hnx
    have hpg : IsPGroup 2 (↥K ⧸ N) := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨n, hn, p, hp, rfl⟩ := hall x
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨p, hp⟩
        refine ⟨k, ?_⟩
        have hp1 : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hn1 : (QuotientGroup.mk n : ↥K ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
        rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hp1]
        rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hperf
    have hperfQ : Group.IsPerfect (↥K ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hsub : Subsingleton (↥K ⧸ N) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isNilpotent _ hpg.isNilpotent
    rw [eq_top_iff]
    intro x _
    exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)

theorem comm_le_of_simple {K Q V : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hKQ : K ≤ normalizer (Q : Set G))
    (hKV : K ≤ normalizer (V : Set G)) {c : G} (hcK : c ∈ K) (hcO : c ∉ pCoreOf 2 K)
    (hc : ∀ q ∈ Q, c * q * c⁻¹ * q⁻¹ ∈ V) : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ V := by
  have hconj : ∀ g ∈ K, ∀ k : G, (∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ V) →
      ∀ q ∈ Q, (g * k * g⁻¹) * q * (g * k * g⁻¹)⁻¹ * q⁻¹ ∈ V := by
    intro g hg k hk q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (mem_normalizer_iff.1 (hKQ (inv_mem hg)) q).1 hq
      simpa using this
    have h1 := (mem_normalizer_iff.1 (hKV hg) _).1 (hk _ hq')
    have e : g * (k * (g⁻¹ * q * g) * k⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ =
        (g * k * g⁻¹) * q * (g * k * g⁻¹)⁻¹ * q⁻¹ := by group
    rwa [e] at h1
  let N : Subgroup ↥K :=
    { carrier := {k | ∀ q ∈ Q, (k : G) * q * (k : G)⁻¹ * q⁻¹ ∈ V}
      one_mem' := fun q _ => by simp
      mul_mem' := fun {a b} ha hb q hq => by
        have h1 := (mem_normalizer_iff.1 (hKV a.2) _).1 (hb q hq)
        have e : (a : G) * ((b : G) * q * (b : G)⁻¹ * q⁻¹) * (a : G)⁻¹ *
            ((a : G) * q * (a : G)⁻¹ * q⁻¹) =
              ((a * b : ↥K) : G) * q * ((a * b : ↥K) : G)⁻¹ * q⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
        rw [← e]
        exact mul_mem h1 (ha q hq)
      inv_mem' := fun {a} ha q hq => by
        have hq' : (a : G)⁻¹ * q * a ∈ Q := by
          have := (mem_normalizer_iff.1 (hKQ (inv_mem a.2)) q).1 hq
          simpa using this
        have h1 := inv_mem (ha _ hq')
        have e : ((a : G) * ((a : G)⁻¹ * q * a) * (a : G)⁻¹ * ((a : G)⁻¹ * q * a)⁻¹)⁻¹ =
            ((a⁻¹ : ↥K) : G) * q * ((a⁻¹ : ↥K) : G)⁻¹ * q⁻¹ := by
          simp only [Subgroup.coe_inv]
          group
        rw [← e]
        exact h1 }
  have hN : N.Normal := ⟨fun k hk g q hq => by
    have := hconj g g.2 k hk q hq
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this⟩
  have hcN : (⟨c, hcK⟩ : ↥K) ∈ N := hc
  have hnot : ¬ N ≤ CFSG.pCore 2 ↥K := by
    intro hle
    apply hcO
    have h1 := hle hcN
    rw [← pCoreOf_subgroupOf_eq_pCore, mem_subgroupOf] at h1
    exact h1
  have htop := eq_top_of_not_le_pCore' hperf hs hnot
  intro k hk q hq
  have hkN : (⟨k, hk⟩ : ↥K) ∈ N := by rw [htop]; trivial
  exact hkN q hq

theorem s1347_four_II (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) (hB : H13.IsA6Block L)
    (hII : ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 (L ⊔ T)) A → IsMaxElemAbelian T A)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (hH₀M : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G))
    (hJ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G)) {K₀ : Subgroup G} (hKH : K₀ ≤ H₁ ⊔ H₂)
    (hsup : H₁ ⊔ H₂ = K₀ ⊔ T) (hperf : ⁅K₀, K₀⁆ = K₀)
    (hs : IsSimpleGroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) (hK₂ : oTwoRes H₂ ≤ K₀)
    (hK₂L : oTwoRes H₂ = l2Of S) {c : G} (hcL2 : c ∈ l2Of S)
    (hcN : c ∈ normalizer (V : Set G)) (hcρ : S.frame.ρ ⟨c, hcN⟩ = c2perm) (hc3 : c ^ 3 = 1)
    (h16 : 16 ≤ (centralizer ({c} : Set G)).relIndex (v0Of T H₁ H₂)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V₀ := v0Of T H₁ H₂ with hV₀
  set O := pCoreOf 2 (L ⊔ T) with hOdef
  set Q₀ := pCoreOf 2 (H₁ ⊔ H₂) with hQ₀def
  have hred := s1347_reduced S hH₀
  have hV₀e : IsElemAbelian 2 V₀ := hred.2.2.1
  have hV₀N : H₁ ⊔ H₂ ≤ normalizer (V₀ : Set G) := hred.2.1
  have hV₀T : V₀ ≤ T := s1347_V0_le_T S hH₀
  have hTH : T ≤ H₁ ⊔ H₂ := hH₀.1
  have hQ₀ : T ⊓ centralizer (V₀ : Set G) = Q₀ := s1347_T_inf_centralizer S h hH₀
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hTH
  have hQ₀T : Q₀ ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have hJQ : thompsonJ T ≤ Q₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hJT.trans hTH) hJ
      (S.h13.sylow.1.to_le hJT)
  have hAQ : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ Q₀ := fun A hA =>
    (B6.le_thompsonJ hA).trans hJQ
  have hVA : ∀ A : Subgroup G, IsMaxElemAbelian T A → V₀ ≤ A := by
    intro A hA
    refine le_of_isMaxElemAbelian hA hV₀T hV₀e.2 fun v hv => ?_
    refine mem_centralizer_iff.2 fun a ha => ?_
    have h1 := (hQ₀.symm ▸ hAQ A hA ha : a ∈ T ⊓ centralizer (V₀ : Set G))
    exact ((mem_centralizer_iff.1 h1.2) v hv).symm
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian O
  have hV₀O : V₀ ≤ O := (hVA A₀ (hII A₀ hA₀)).trans hA₀.1
  have hzV : S.zV ∈ V₀ := by
    refine s1347_Z_le_V0 (subset_closure
      ⟨⟨S.V_le_T S.zV_mem_V, mem_centralizer_iff.2 fun t ht => ?_⟩, S.zV_sq⟩)
    have h1 := S.conj_zV ⟨t, S.frame.T_le ht⟩
    calc t * S.zV = t * S.zV * t⁻¹ * t := by group
      _ = S.zV * t := by rw [h1]
  have hcH₂ : c ∈ H₂ := by rw [← hK₂L] at hcL2; exact oTwoRes_le _ hcL2
  have hcH : c ∈ H₁ ⊔ H₂ := mem_sup_right hcH₂
  obtain ⟨hVV₀, hcomm⟩ := s1347_four_count S he hB (hTH.trans hV₀N) hV₀O hzV hcL2 hcN hcρ hc3
    (hV₀N hcH) h16
  have hQ₀O : Q₀ ≤ O := by
    rw [← hQ₀, hOdef, ← s134_cT S]
    exact inf_le_inf_left T (centralizer_le (SetLike.coe_subset_coe.2 hVV₀))
  have hcK : c ∈ K₀ := by rw [← hK₂L] at hcL2; exact hK₂ hcL2
  have hcO : c ∉ pCoreOf 2 K₀ := by
    intro hc
    have hc1 : c = 1 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 K₀)) ⟨c, hc⟩
      have hk' : orderOf c = 2 ^ k := (Subgroup.orderOf_coe ⟨c, hc⟩).trans hk
      have hco : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
      have hk0 : k = 0 := by
        by_contra hk0
        have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans (hk' ▸ hco)
        omega
      exact orderOf_eq_one_iff.1 (by rw [hk', hk0, pow_zero])
    have h1 : S.frame.ρ ⟨c, hcN⟩ = 1 := by
      rw [show (⟨c, hcN⟩ : ↥(normalizer (V : Set G))) = 1 from Subtype.ext hc1, map_one]
    rw [hcρ] at h1
    exact c2perm_props.2.2.1 h1
  have hKQ₀ : K₀ ≤ normalizer (Q₀ : Set G) := hKH.trans (le_normalizer_pCoreOf 2 _)
  have hKcomm := comm_le_of_simple hperf hs hKQ₀ (hKH.trans hV₀N) hcK hcO
    fun q hq => hcomm q (hQ₀O hq)
  have hKA : ∀ A : Subgroup G, IsMaxElemAbelian T A → K₀ ≤ normalizer (A : Set G) := by
    intro A hA
    have hmem : ∀ k ∈ K₀, ∀ a ∈ A, k * a * k⁻¹ ∈ A := by
      intro k hk a ha
      have h1 := hKcomm k hk a (hAQ A hA ha)
      have e : k * a * k⁻¹ = (k * a * k⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact mul_mem (hVA A hA h1) ha
    intro k hk
    exact B6.mem_normalizer_of_forall_mem (hmem k hk) fun a ha => by
      have := hmem k⁻¹ (inv_mem hk) a ha
      simpa using this
  have hKJ : K₀ ≤ normalizer (thompsonJ O : Set G) := by
    have key : ∀ g ∈ K₀, B6.conjSub g (thompsonJ O) ≤ thompsonJ O := by
      intro g hg
      unfold thompsonJ
      simp only [OrderIso.map_iSup]
      refine iSup₂_le fun A hA => ?_
      rw [B6.conjSub_eq_self (hKA A (hII A hA) hg)]
      exact le_iSup₂_of_le A hA le_rfl
    intro g hg
    exact B6.mem_normalizer_of_conjSub_le (key g hg) (key g⁻¹ (inv_mem hg))
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 _
  have hVO : V ≤ O := by
    rw [hOdef, ← s134_cT S]
    exact le_inf S.V_le_T fun v hv => mem_centralizer_iff.2 fun w hw =>
      (B6.isElemAbelian_iff.1 (s134_elemAbelian_V S)).1 w hw v hv
  have hJ1 : thompsonJ O ≠ ⊥ :=
    S1414.thompsonJ_ne_bot hO2 fun hb => S.irr.2.1 (le_bot_iff.1 (hb ▸ hVO))
  have hLTJ : L ⊔ T ≤ normalizer (thompsonJ O : Set G) :=
    (le_normalizer_pCoreOf 2 (L ⊔ T)).trans (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _)
  have hJM := s134_normalizer_le_M S hJ1 (hO2.to_le (B6.thompsonJ_le O)) hLTJ
  exact hH₀M (hsup.le.trans (sup_le (hKJ.trans hJM) S.T_le_NL))

end CFSG.Quasithin.H13.U3
