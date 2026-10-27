module

public import CFSG.Quasithin.H13.L32A726d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_three_pow_mem_726 {Q : Subgroup G} {g : G} (hcop : ¬ 3 ∣ orderOf g) {k : ℕ}
    (hk : g ^ 3 ^ k ∈ Q) : g ∈ Q := by
  have h : Nat.Coprime (3 ^ k) (orderOf g) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcop)
  exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime h)

omit [Finite G] in
theorem mem_normalizer_conjClosure_726 {Z M : Subgroup G} {g : G}
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) (hgM : g ∈ Subgroup.normalizer (M : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure Z M : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (Z : Set G) →
      g ∈ Subgroup.normalizer (M : Set G) → ∀ y ∈ conjClosure Z M,
        g * y * g⁻¹ ∈ conjClosure Z M := by
    intro g hgZ hgM y hy
    have hle : conjClosure Z M ≤ (conjClosure Z M).comap (MulAut.conj g).toMonoidHom := by
      refine conjClosure_le fun h hh z hz => ?_
      rw [Subgroup.mem_comap]
      show g * (h * z * h⁻¹) * g⁻¹ ∈ conjClosure Z M
      have h1 : g * h * g⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hgM h).mp hh
      have h2 : g * z * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hgZ z).mp hz
      have h3 := mem_conjClosure h1 h2
      rwa [show g * h * g⁻¹ * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ by
        group] at h3
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hgZ hgM y, fun hy => ?_⟩
  have h := key g⁻¹ (inv_mem hgZ) (inv_mem hgM) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h

open scoped Pointwise in
theorem exists_conj_of_isSylowOf_726 {p : ℕ} [Fact p.Prime] {S S' I : Subgroup G}
    (hS : IsSylowOf p S I) (hS' : IsSylowOf p S' I) :
    ∃ i ∈ I, ∀ x : G, x ∈ S' ↔ i⁻¹ * x * i ∈ S := by
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨Q', rfl⟩ := hS'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥I) Q Q'
  have hg' : MulAut.conj g • (Q : Subgroup I) = (Q' : Subgroup I) := by
    rw [← Sylow.coe_subgroup_smul (g := g), hg]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← hg', Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    refine Subgroup.mem_map.mpr ⟨s, hs, ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
      Subgroup.coe_inv]
    group
  · intro hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hx
    have hs' : (s : G) = (g : G)⁻¹ * x * g := hsx
    have hx : x = (g : G) * (s : G) * (g : G)⁻¹ := by
      rw [hs']
      group
    have hxI : x ∈ I := by
      rw [hx]
      exact I.mul_mem (I.mul_mem g.2 s.2) (I.inv_mem g.2)
    refine Subgroup.mem_map.mpr ⟨⟨x, hxI⟩, ?_, rfl⟩
    rw [← hg', Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨s, hs, Subtype.ext ?_⟩
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hx.symm

theorem le_sup_normalizer_of_isSylowOf_726 {p : ℕ} [Fact p.Prime] {I G0 S : Subgroup G}
    (hIG0 : I ≤ G0) (hG0I : G0 ≤ Subgroup.normalizer (I : Set G)) (hS : IsSylowOf p S I) :
    G0 ≤ I ⊔ (G0 ⊓ Subgroup.normalizer (S : Set G)) := by
  intro g hg
  have hS' : IsSylowOf p (conjByElt g S) I := by
    refine isSylowOf_of_card ?_ ?_
    · intro y hy
      rw [mem_conjByElt] at hy
      have h1 : g * (g⁻¹ * y * g) * g⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (hG0I hg) _).mp (hS.le hy)
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1
    · rw [conjByElt, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hS.card_eq
  obtain ⟨i, hiI, hi⟩ := exists_conj_of_isSylowOf_726 hS hS'
  have hn : i⁻¹ * g ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have h1 := hi (g * s * g⁻¹)
    rw [mem_conjByElt, show g⁻¹ * (g * s * g⁻¹) * g = s by group] at h1
    rw [h1, show i⁻¹ * g * s * (i⁻¹ * g)⁻¹ = i⁻¹ * (g * s * g⁻¹) * i by group]
  have hG : i⁻¹ * g ∈ G0 := G0.mul_mem (G0.inv_mem (hIG0 hiI)) hg
  have h := Subgroup.mul_mem_sup hiI (Subgroup.mem_inf.mpr ⟨hG, hn⟩ :
    i⁻¹ * g ∈ G0 ⊓ Subgroup.normalizer (S : Set G))
  rwa [mul_inv_cancel_left] at h

section Ctx

variable {T L V H D : Subgroup G}

theorem pRank_three_le_726 (hc : Ctx726 G T L V H D) {X : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥) :
    CFSG.Open.pRank 3 X ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := (isSQTKCat_of_pCoreOf_ne_bot_726 hc hX).1
  have h' := CFSG.SectionRank.isStronglyQuasithin_iff.mp h 3 Nat.prime_three (by norm_num)
  rwa [pRank_top_subtype] at h'

theorem normalizer_x_le_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) {G0 : Subgroup G}
    (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) {x : G} (hxL : x ∈ L32A.l1 T L V)
    (hx3 : orderOf x = 3) (hPQ : pCoreOf 2 (L32A.l1 T L V) ≤ pCoreOf 2 G0) :
    G0 ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ H := by
  have hQ0H : pCoreOf 2 G0 ≤ H :=
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_td_g0_726 hc hdD hdV htT htd hHdG0 hG0)).trans
      (inf_le_left.trans (t_le_h_726 hc))
  have hl1eq : L32A.l1 T L V = conjClosure (Subgroup.zpowers x) (pCoreOf 2 G0) := by
    apply le_antisymm
    · exact (l1_le_conjClosure_726 hc hxL hx3).trans (conjClosure_mono le_rfl hPQ)
    · exact conjClosure_le fun q hq z hz =>
        (Subgroup.mem_normalizer_iff.mp (hc.l1_normal (hQ0H hq)) z).mp
          ((Subgroup.zpowers_le.mpr hxL) hz)
  intro g hg
  apply normalizer_l1_le_726 hc
  rw [hl1eq]
  exact mem_normalizer_conjClosure_726 hg.2 (le_normalizer_pCoreOf 2 G0 hg.1)

theorem le_pCoreOf_of_pow_three_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hd2 : d * d = 1) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t)
    {G0 : Subgroup G} (hHdG0 : H ⊓ Subgroup.centralizer ({d} : Set G) ≤ G0)
    (hG0 : G0 ≤ Subgroup.centralizer ({d} : Set G)) (hG0H : ¬ G0 ≤ H) {I : Subgroup G}
    (hIG0 : I ≤ G0) (hG0I : G0 ≤ Subgroup.normalizer (I : Set G))
    (hI3 : ∀ g ∈ I, ∃ k : ℕ, g ^ 3 ^ k ∈ pCoreOf 2 G0) : I ≤ pCoreOf 2 G0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hIQ
  obtain ⟨g, hgI, hgQ⟩ : ∃ g ∈ I, g ∉ pCoreOf 2 G0 := by
    by_contra h
    push Not at h
    exact hIQ h
  obtain ⟨x, Y, E₁, E₂, hX⟩ := exists_xData_726 hc
  have hKG0 : oTwoUpper H ≤ G0 := (k_le_hd_726 hc hdD).trans hHdG0
  have hYG0 : Y ≤ G0 := hX.y_le.trans hKG0
  have hr := pRank_three_le_726 hc (pCoreOf_g0_ne_bot_726 hc hdD hdV hd2 hHdG0 hG0)
  have hTd := isSylowTwoOf_td_g0_726 hc hdD hdV htT htd hHdG0 hG0
  have h3I : 3 ∣ Nat.card I := by
    by_contra h3
    obtain ⟨k, hk⟩ := hI3 g hgI
    refine hgQ (mem_of_pow_three_pow_mem_726 (fun h => h3 ?_) hk)
    have h1 := orderOf_dvd_natCard (⟨g, hgI⟩ : ↥I)
    rw [Subgroup.orderOf_mk] at h1
    exact h.trans h1
  obtain ⟨W, -, -, hWI, hxWI, -⟩ := iLemma_726 hr hYG0 hX.y_pgroup hX.e₁_le hX.e₂_le
    hX.e₁_elem hX.e₂_elem hX.e₁_card hX.e₂_card hX.x_order hX.inf_le hIG0 (hYG0.trans hG0I) h3I
  have hxI : x ∈ I := hxWI.2
  have hL1I : L32A.l1 T L V ≤ I := (l1_le_conjClosure_726 hc hX.x_mem hX.x_order).trans
    (conjClosure_le fun p hp z hz =>
      (Subgroup.mem_normalizer_iff.mp (hG0I (hKG0 (l1_le_k_726 hc (pCoreOf_le 2 _ hp)))) z).mp
        ((Subgroup.zpowers_le.mpr hxI) hz))
  have hPQ : pCoreOf 2 (L32A.l1 T L V) ≤ pCoreOf 2 G0 := by
    intro p hp
    obtain ⟨k, hk⟩ := hI3 p (hL1I (pCoreOf_le 2 _ hp))
    refine mem_of_pow_three_pow_mem_726 ?_ hk
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (L32A.l1 T L V)) ⟨p, hp⟩
    have hm' : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three
      (h3.trans (orderOf_dvd_of_pow_eq_one hm'))) (by norm_num)
  have hNx := normalizer_x_le_726 hc hdD hdV htT htd hHdG0 hG0 hX.x_mem hX.x_order hPQ
  have h23 : ∀ q : ℕ, q.Prime → q ∣ Nat.card G0 → q = 2 ∨ q = 3 := by
    intro q hq hqd
    have : Fact q.Prime := ⟨hq⟩
    set N0 := G0 ⊓ Subgroup.normalizer ((W ⊓ I : Subgroup G) : Set G) with hN0
    have hfr : G0 ≤ I ⊔ N0 := le_sup_normalizer_of_isSylowOf_726 hIG0 hG0I hWI
    have hG0eq : N0 ⊔ I = G0 := le_antisymm (sup_le inf_le_left hIG0) (by rwa [sup_comm])
    have hidx : I.relIndex G0 = I.relIndex N0 := by
      rw [← hG0eq]
      exact A4.relIndex_sup_eq_of_le_normalizer' (inf_le_left.trans hG0I)
    have hcard : Nat.card G0 = I.relIndex G0 * Nat.card I := by
      have h := Subgroup.relIndex_mul_card I G0
      rw [inf_eq_left.mpr hIG0] at h
      exact h.symm
    have hIq : q ∣ Nat.card I → q = 2 ∨ q = 3 := by
      intro hqI
      obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' q hqI
      obtain ⟨k, hk⟩ := hI3 i i.2
      by_cases hq3 : q = 3
      · exact Or.inr hq3
      left
      have hcop : (orderOf (i : G)).Coprime (3 ^ k) := by
        rw [Subgroup.orderOf_coe, hi]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_three).mpr hq3)
      have hord : orderOf ((i : G) ^ 3 ^ k) = q := by
        rw [hcop.orderOf_pow, Subgroup.orderOf_coe, hi]
      obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 G0) ⟨_, hk⟩
      have hm' : ((i : G) ^ 3 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hqd' : q ∣ 2 ^ m := hord ▸ orderOf_dvd_of_pow_eq_one hm'
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqd')
    have hN0q : q ∣ Nat.card N0 → q = 2 ∨ q = 3 := by
      intro hqN
      obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' q hqN
      have hnN : (n : G) ∈ Subgroup.normalizer ((W ⊓ I : Subgroup G) : Set G) := n.2.2
      set a := (W ⊓ I).normalizerMonoidHom ⟨n, hnN⟩ with ha
      have hao : orderOf a ∣ q := by
        have h1 := orderOf_map_dvd (W ⊓ I).normalizerMonoidHom
          (⟨n, hnN⟩ : Subgroup.normalizer ((W ⊓ I : Subgroup G) : Set G))
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hn] at h1
        exact h1
      rcases (Nat.dvd_prime hq).mp hao with h1 | hq'
      ·
        have hker : (⟨n, hnN⟩ : Subgroup.normalizer ((W ⊓ I : Subgroup G) : Set G)) ∈
            (W ⊓ I).normalizerMonoidHom.ker := orderOf_eq_one_iff.mp h1
        rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
        have hnx : (n : G) * x = x * n :=
          ((Subgroup.mem_centralizer_iff.mp hker) x hxWI).symm
        have hnH : (n : G) ∈ H := hNx ⟨n.2.1, centralizer_le_normalizer_zpowers_726 x
          (Subgroup.mem_centralizer_singleton_iff.mpr hnx)⟩
        have hqH : q ∣ Nat.card H := by
          have h2 := orderOf_dvd_natCard (⟨n, hnH⟩ : ↥H)
          rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hn] at h2
        exact hc.two_three q hq hqH
      · have hqA : q ∣ Nat.card (MulAut ↥(W ⊓ I)) := hq' ▸ orderOf_dvd_natCard a
        have hWIp : IsPGroup 3 ↥(W ⊓ I) := hWI.isPGroup
        have hWIr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(W ⊓ I)) ≤ 2 := by
          rw [pRank_top_subtype]
          exact (CFSG.SectionRank.pRank_mono (by norm_num) (hWI.le.trans hIG0)).trans hr
        exact prime_dvd_card_aut_of_three hWIp hWIr hq hqA
    rw [hcard] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · rw [hidx] at h
      exact hN0q (h.trans (Subgroup.relIndex_dvd_card I N0))
    · exact hIq h
  have h3G0 : 3 ∣ Nat.card G0 := by
    have h1 := Subgroup.card_dvd_of_le hYG0
    rw [hX.y_card] at h1
    exact (show 3 ∣ 27 by norm_num).trans h1
  obtain ⟨W', -, -, hW'G0, -, hxc⟩ := iLemma_726 hr hYG0 hX.y_pgroup hX.e₁_le hX.e₂_le
    hX.e₁_elem hX.e₂_elem hX.e₁_card hX.e₂_card hX.x_order hX.inf_le le_rfl
    (hYG0.trans Subgroup.le_normalizer) h3G0
  have hSH : W' ⊓ G0 ≤ H := fun w hw => hNx ⟨hw.2, centralizer_le_normalizer_zpowers_726 x
    (Subgroup.mem_centralizer_singleton_iff.mpr (hxc w hw.1).symm)⟩
  have hTdH : T ⊓ Subgroup.centralizer ({d} : Set G) ≤ H := inf_le_left.trans (t_le_h_726 hc)
  set M := (W' ⊓ G0) ⊔ (T ⊓ Subgroup.centralizer ({d} : Set G)) with hM
  have hMG0 : M ≤ G0 := sup_le inf_le_right hTd.1
  have hidx1 : M.relIndex G0 = 1 := by
    have h₁ : M.relIndex G0 ∣ (W' ⊓ G0).relIndex G0 :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ M G0 le_sup_left hMG0)
    have h₂ : M.relIndex G0 ∣ (T ⊓ Subgroup.centralizer ({d} : Set G)).relIndex G0 :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ M G0 le_sup_right hMG0)
    have h3 : ¬ 3 ∣ (W' ⊓ G0).relIndex G0 := (isSylowOf_iff.mp hW'G0).2.2
    have h2 : ¬ 2 ∣ (T ⊓ Subgroup.centralizer ({d} : Set G)).relIndex G0 := hTd.2.2
    by_contra hne
    obtain ⟨r, hr', hrd⟩ := Nat.exists_prime_and_dvd hne
    rcases h23 r hr' (hrd.trans (Subgroup.relIndex_dvd_card M G0)) with rfl | rfl
    · exact h2 (hrd.trans h₂)
    · exact h3 (hrd.trans h₁)
  exact hG0H ((Subgroup.relIndex_eq_one.mp hidx1).trans (sup_le hSH hTdH))

end Ctx

end CFSG.Quasithin.H13.L32A
