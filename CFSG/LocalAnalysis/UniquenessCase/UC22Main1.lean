module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22main1_pCoreOf_le (K : Subgroup G) : pCoreOf 2 K ≤ K :=
  Subgroup.map_subtype_le _

theorem uc22main1_isPGroup_pCoreOf (K : Subgroup G) : IsPGroup 2 (pCoreOf 2 K) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype

theorem uc22main1_le_pCoreOf {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 P)
    (hn : ∀ k ∈ K, ∀ x ∈ P, k * x * k⁻¹ ∈ P) : P ≤ pCoreOf 2 K := by
  have hN : (P.subgroupOf K).Normal := ⟨fun x hx k => hn (k : G) k.2 x hx⟩
  have hQ : IsPGroup 2 (P.subgroupOf K) := hP.comap_subtype
  have hle : P.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hN, hQ⟩
  intro x hx
  exact ⟨⟨x, hPK hx⟩, hle hx, rfl⟩

theorem uc22main1_conj_mem_pCoreOf_self {K : Subgroup G} {k x : G} (hk : k ∈ K)
    (hx : x ∈ pCoreOf 2 K) : k * x * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem y hy ⟨k, hk⟩, rfl⟩

theorem uc22main1_conj_mem_pCoreOf {N K : Subgroup G}
    (hnorm : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K) {n x : G} (hn : n ∈ N)
    (hx : x ∈ pCoreOf 2 K) : n * x * n⁻¹ ∈ pCoreOf 2 K := by
  have hPK : (pCoreOf 2 K).map (MulAut.conj n).toMonoidHom ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hnorm n hn y (uc22main1_pCoreOf_le K hy)
  have hP2 : IsPGroup 2 ((pCoreOf 2 K).map (MulAut.conj n).toMonoidHom) :=
    (uc22main1_isPGroup_pCoreOf K).map _
  have hPn : ∀ k ∈ K, ∀ y ∈ (pCoreOf 2 K).map (MulAut.conj n).toMonoidHom,
      k * y * k⁻¹ ∈ (pCoreOf 2 K).map (MulAut.conj n).toMonoidHom := by
    rintro k hk _ ⟨y, hy, rfl⟩
    have hk' : n⁻¹ * k * n ∈ K := by simpa using hnorm n⁻¹ (N.inv_mem hn) k hk
    refine ⟨(n⁻¹ * k * n) * y * (n⁻¹ * k * n)⁻¹,
      uc22main1_conj_mem_pCoreOf_self hk' hy, ?_⟩
    simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    group
  exact uc22main1_le_pCoreOf hPK hP2 hPn ⟨x, hx, rfl⟩

theorem uc22main1_no_odd_prime_elt {N K : Subgroup G} (hKN : K ≤ N)
    (hnorm : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K)
    (hN : N ⊓ centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N)
    {x : G} (hxK : x ∈ K) (hxc : x ∈ centralizer (pCoreOf 2 K : Set G))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hxq : orderOf x = q) : False := by
  have hxq1 : x ^ q = 1 := hxq ▸ pow_orderOf_eq_one x
  have hcomm : ∀ r ∈ pCoreOf 2 N, x * r = r * x := by
    intro r hr
    have hcR : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 N :=
      (pCoreOf 2 N).mul_mem (uc22main1_conj_mem_pCoreOf_self (hKN hxK) hr)
        ((pCoreOf 2 N).inv_mem hr)
    have hcK : x * r * x⁻¹ * r⁻¹ ∈ K := by
      have e : x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) := by group
      rw [e]
      exact K.mul_mem hxK (hnorm r (uc22main1_pCoreOf_le N hr) x⁻¹ (K.inv_mem hxK))
    have hcQ : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 K := by
      refine uc22main1_le_pCoreOf (K := K) (P := K ⊓ pCoreOf 2 N) inf_le_left
        ((uc22main1_isPGroup_pCoreOf N).to_le inf_le_right) ?_ ⟨hcK, hcR⟩
      intro k hk y hy
      exact ⟨K.mul_mem (K.mul_mem hk hy.1) (K.inv_mem hk),
        uc22main1_conj_mem_pCoreOf_self (hKN hk) hy.2⟩
    generalize hc : x * r * x⁻¹ * r⁻¹ = c at hcR hcQ
    have hxr : x * r * x⁻¹ = c * r := by rw [← hc]; group
    have hcx : c * x = x * c := mem_centralizer_iff.1 hxc c hcQ
    have hxcx : x * c * x⁻¹ = c := by rw [← hcx, mul_inv_cancel_right]
    have hpow : ∀ k : ℕ, x ^ k * r * (x ^ k)⁻¹ = c ^ k * r := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc x ^ (k + 1) * r * (x ^ (k + 1))⁻¹ = x * (x ^ k * r * (x ^ k)⁻¹) * x⁻¹ := by group
          _ = x * (c ^ k * r) * x⁻¹ := by rw [ih]
          _ = (x * c ^ k * x⁻¹) * (x * r * x⁻¹) := by group
          _ = (x * c * x⁻¹) ^ k * (c * r) := by rw [conj_pow, hxr]
          _ = c ^ (k + 1) * r := by rw [hxcx]; group
    have hcq : c ^ q = 1 := by
      have h := hpow q
      rw [hxq1] at h
      simpa using h.symm
    obtain ⟨j, hj⟩ := uc22main1_isPGroup_pCoreOf N ⟨c, hcR⟩
    have hcj : c ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hcop : Nat.gcd q (2 ^ j) = 1 :=
      Nat.Coprime.pow_right j ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
    have hc1 : c = 1 := by
      have := pow_gcd_eq_one.2 ⟨hcq, hcj⟩
      rwa [hcop, pow_one] at this
    subst hc1
    have h1 : x * r * x⁻¹ = r := by simpa using hxr
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hxR : x ∈ pCoreOf 2 N :=
    hN ⟨hKN hxK, mem_centralizer_iff.2 fun r hr => (hcomm r hr).symm⟩
  obtain ⟨j, hj⟩ := uc22main1_isPGroup_pCoreOf N ⟨x, hxR⟩
  have hxj : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hdvd : q ∣ 2 ^ j := hxq ▸ orderOf_dvd_of_pow_eq_one hxj
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))

theorem uc22main1_cent_pCoreOf_le {N K : Subgroup G} (hKN : K ≤ N)
    (hnorm : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K)
    (hN : N ⊓ centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N) :
    K ⊓ centralizer (pCoreOf 2 K : Set G) ≤ pCoreOf 2 K := by
  have hX2 : IsPGroup 2 ↥(K ⊓ centralizer (pCoreOf 2 K : Set G)) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro q hq hqd
    by_contra hq2
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hqd
    exact uc22main1_no_odd_prime_elt hKN hnorm hN y.2.1 y.2.2 hq hq2
      ((Subgroup.orderOf_coe y).trans hy)
  refine uc22main1_le_pCoreOf inf_le_left hX2 ?_
  intro k hk x hx
  rw [Subgroup.mem_inf] at hx ⊢
  refine ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk), ?_⟩
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : k⁻¹ * y * k ∈ pCoreOf 2 K := by
    simpa using uc22main1_conj_mem_pCoreOf_self (K.inv_mem hk) hy
  have h := mem_centralizer_iff.1 hx.2 _ hy'
  calc y * (k * x * k⁻¹) = k * ((k⁻¹ * y * k) * x) * k⁻¹ := by group
    _ = k * (x * (k⁻¹ * y * k)) * k⁻¹ := by rw [h]
    _ = (k * x * k⁻¹) * y := by group

theorem uc22main1_conj_mem_centralizer {Z : Subgroup G} {n k : G}
    (hn : n ∈ normalizer (Z : Set G)) (hk : k ∈ centralizer (Z : Set G)) :
    n * k * n⁻¹ ∈ centralizer (Z : Set G) := by
  rw [mem_centralizer_iff] at hk ⊢
  intro z hz
  have hz' : n⁻¹ * z * n ∈ Z := (mem_normalizer_iff''.1 hn z).1 hz
  have h := hk _ hz'
  calc z * (n * k * n⁻¹) = n * ((n⁻¹ * z * n) * k) * n⁻¹ := by group
    _ = n * (k * (n⁻¹ * z * n)) * n⁻¹ := by rw [h]
    _ = (n * k * n⁻¹) * z := by group

theorem uc22main1_T_ne_bot (D : Data G) : D.T ≠ ⊥ := by
  obtain ⟨P, hP1, hP2, hPM⟩ := D.maxLocal.1
  have hPle : P ≤ D.M := hPM ▸ Subgroup.le_normalizer
  intro hT
  exact hP1 (D.sylowM.eq_of_le (hT ▸ bot_le) hPle hP2 |>.trans hT)

theorem uc22main1_Z_ne_bot (D : Data G) : D.Z ≠ ⊥ :=
  CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot D.sylowM.isPGroup
    (uc22main1_T_ne_bot D)

theorem uc22main1_Z_le_T (D : Data G) : D.Z ≤ D.T :=
  CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le D.T

theorem uc22main1_Z_le_U (D : Data G) : D.Z ≤ D.U := by
  intro z hz
  refine Subgroup.mem_iSup_of_mem (1 : D.M) ?_
  exact ⟨z, hz, by simp⟩

theorem uc22main1_T_le_centralizer (D : Data G) : D.T ≤ centralizer (D.Z : Set G) := by
  intro t ht
  rw [mem_centralizer_iff]
  intro z hz
  exact ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hz).2.1 t ht).symm

theorem uc22main1_centralizer_mem_hSet (D : Data G) (hC : ¬ centralizer (D.Z : Set G) ≤ D.M) :
    centralizer (D.Z : Set G) ∈ hSet D.T D.M := by
  refine ⟨uc22main1_T_le_centralizer D, hC, ?_⟩
  have hloc : IsTwoLocal (normalizer (D.Z : Set G)) :=
    ⟨D.Z, uc22main1_Z_ne_bot D,
      D.sylowM.isPGroup.to_le (uc22main1_Z_le_T D), rfl⟩
  exact uc22main1_cent_pCoreOf_le (centralizer_le_normalizer _)
    (fun _ hn _ hk => uc22main1_conj_mem_centralizer hn hk)
    (D.standing.charTwo _ hloc)

theorem uc22main1_exists_irr (D : Data G) :
    ∃ V : Subgroup G, V ≤ D.U ∧ V ≠ ⊥ ∧ D.M ≤ normalizer (V : Set G) ∧ IrrOn D.M V := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  haveI : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  have hU : D.U ≠ ⊥ := fun h =>
    uc22main1_Z_ne_bot D (le_bot_iff.1 (h ▸ uc22main1_Z_le_U D))
  obtain ⟨V, hV⟩ := exists_minimal_of_wellFoundedLT
    (fun W : Subgroup G => W ≤ D.U ∧ W ≠ ⊥ ∧ D.M ≤ normalizer (W : Set G))
    ⟨D.U, le_rfl, hU, le_normalizer_uCore D.M D.T⟩
  obtain ⟨hVU, hVne, hVM⟩ := hV.1
  refine ⟨V, hVU, hVne, hVM, fun W hWV hWM => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · exact Or.inr (le_antisymm hWV (hV.2 ⟨hWV.trans hVU, hW, hWM⟩ hWV))

theorem uc22main1_calLOf_nonempty (D : Data G) (h20_4 : S20_4 D) (h1930 : H1930 D)
    {H : Subgroup G} (hH : H ∈ hSet D.T D.M) : (calLOf D.T D.M H).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h := h20_4 h1930 H hH
  rw [hne, iSup_emptyset, Subgroup.coe_bot] at h
  apply hH.2.1
  intro a ha
  have ha' : a ∈ ({1} : Set G) * ((H ⊓ D.M : Subgroup G) : Set G) := by
    rw [h]; exact ha
  obtain ⟨u, hu, b, hb, rfl⟩ := Set.mem_mul.1 ha'
  rw [Set.mem_singleton_iff] at hu
  subst hu
  rw [one_mul]
  exact hb.2

theorem uc22main1_nParam (D : Data G) (h20_10 : S20_10 D) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calLLow D.T D.M) : ∃ n, NParam L n := by
  rcases h20_10 h1930 L hL with ⟨n, hn⟩ | ⟨L₁, L₂, h₁, h₂, hL12, hne, -, n, hn⟩ | ⟨n, hn, -⟩
  · refine ⟨n, Or.inl ?_⟩
    rcases hn with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact ⟨n, Or.inr ⟨L₁, L₂, h₁, h₂, hL12, hne, hn⟩⟩
  · refine ⟨n, Or.inl ?_⟩
    rcases hn with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem uc22main1_ctx21 (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D) (h20_10 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) : ∃ c : Ctx21 D Ch, c.L0 ≤ L := by
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  haveI : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  obtain ⟨L0, hle, hmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ calL D.T D.M) L hL
  have hL0 : L0 ∈ calLLow D.T D.M := hmin
  obtain ⟨n, hn⟩ := uc22main1_nParam D h20_10 h1930 hL0
  obtain ⟨B0, hch, hB0, hpi, hα, hBM⟩ := hCh L0 hL0 n hn
  exact ⟨⟨L0, B0, B0, n, hL0, hn, hB0, hpi, hα, hBM, hch, hB0, le_rfl⟩, hle⟩

theorem uc22_isTI_of_steps (D : Data G) (Ch : Choice2011 G)
    (hne : (hSet D.T D.M).Nonempty) (h1930 : H1930 D)
    (h20_4 : S20_4 D) (h20_10 : S20_10 D)
    (hCh : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M)
    (h22_2 : S22_2 D Ch) (hend : S22_end D Ch) :
    CFSG.CGT.Timmesfeld75.IsTI D.U := by
  by_contra hU
  obtain ⟨H, hH⟩ := hne
  obtain ⟨L, hL⟩ := uc22main1_calLOf_nonempty D h20_4 h1930 hH
  obtain ⟨c, -⟩ := uc22main1_ctx21 D Ch h1930 h20_10 hCh hL.1
  have hC : ¬ centralizer (D.Z : Set G) ≤ D.M := h22_2 h1930 ⟨c, hU⟩
  obtain ⟨L', hL'⟩ := uc22main1_calLOf_nonempty D h20_4 h1930
    (uc22main1_centralizer_mem_hSet D hC)
  obtain ⟨c', hc'⟩ := uc22main1_ctx21 D Ch h1930 h20_10 hCh hL'.1
  obtain ⟨V, hVU, hVne, hVM, hVirr⟩ := uc22main1_exists_irr D
  exact hend h1930
    { toCtx22 := ⟨c', hU⟩, hC := hC, L := L', hL := hL', hLge := hc', V := V, hVU := hVU,
      hVne := hVne, hVM := hVM, hVirr := hVirr }

end CFSG.LocalAnalysis.UniquenessCase.UC22
