module

public import CFSG.Walter.W67.Transport
public import CFSG.Walter.W67.W1GW

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem le_pPrimeCore_of_map_normal {W : Subgroup G} (hW : Odd (Nat.card W))
    (hn : (W.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 G))).Normal) : W ≤ CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 G
  set π := QuotientGroup.mk' O
  have hO : Odd (Nat.card O) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    rwa [Nat.coprime_two_left] at this
  set V := (W.map π).comap π
  have hWV : W ≤ V := Subgroup.le_comap_map π W
  have hVn : V.Normal := hn.comap π
  have hVcard : Nat.card V = Nat.card (W.map π) * Nat.card O := by
    have h1 := card_eq_card_map_mul_card_inf_ker π V
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
      QuotientGroup.ker_mk', inf_eq_right.mpr] at h1
    · exact h1
    · intro x hx
      change π x ∈ W.map π
      have : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [this]
      exact Subgroup.one_mem _
  have hVodd : Odd (Nat.card V) := by
    rw [hVcard]
    exact Odd.mul (Odd.of_dvd_nat hW (Subgroup.card_map_dvd W π)) hO
  have hVO : V ≤ O := le_sSup ⟨hVn, Nat.coprime_two_left.mpr hVodd⟩
  exact hWV.trans hVO

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem conj_mem_KE
    {x y : G} (hx : x ∈ h.H) (hy : y ∈ h.K ⊔ fr.E) : x * y * x⁻¹ ∈ h.K ⊔ fr.E := by
  rw [← fr.isInternalDirectProduct_H.1] at hx
  have hKEN : h.K ⊔ fr.E ≤ Subgroup.normalizer
      ((Subgroup.zpowers h.J : Subgroup G) : Set G) := by
    intro z hz
    rw [JT.normalizer_zpowers_of_orderOf_eq_two h.orderOf_J]
    exact sup_le h.K_le_H fr.E_le_H hz
  obtain ⟨j, hj, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer hKEN).mp hx
  have hjz : j * (z * y * z⁻¹) * j⁻¹ = z * y * z⁻¹ := by
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
    · group
    · have := h.commute_J (sup_le h.K_le_H fr.E_le_H
        ((h.K ⊔ fr.E).mul_mem ((h.K ⊔ fr.E).mul_mem hz hy) ((h.K ⊔ fr.E).inv_mem hz)))
      rw [← this, mul_inv_cancel_right]
  rw [show j * z * y * (j * z)⁻¹ = j * (z * y * z⁻¹) * j⁻¹ by group, hjz]
  exact (h.K ⊔ fr.E).mul_mem ((h.K ⊔ fr.E).mul_mem hz hy) ((h.K ⊔ fr.E).inv_mem hz)

end Frame

theorem case1_of_sup : ∀ (G : Type) [Group G] [Finite G] (h : Hyp G), h.H ⊔ CFSG.pPrimeCore 2 G = ⊤ → Case1 h := by
  intro G _ _ h hHO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨fr⟩ := Frame.nonempty G h
  set O := CFSG.pPrimeCore 2 G
  set π := QuotientGroup.mk' O
  have hO : Odd (Nat.card O) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    rwa [Nat.coprime_two_left] at this
  have hHtop : h.H.map π = ⊤ := by
    have := congrArg (Subgroup.map π) hHO
    rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O),
      show O.map π = ⊥ by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'], sup_bot_eq]
      at this
  have hsurj : ∀ y : G ⧸ O, ∃ x ∈ h.H, π x = y := fun y => by
    have : y ∈ h.H.map π := hHtop ▸ Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, hx, rfl⟩
  have hKO : h.K ⊓ O = ⊥ := h.K_inf_eq_bot_of_odd O hO
  have hHO_F : h.H ⊓ O ≤ h.F := by
    rintro x ⟨hxH, hxO⟩
    refine fr.mem_F_of_odd ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      (Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard _ hxO))
    have h1 : k * x * k⁻¹ * x⁻¹ ∈ h.K ⊓ O := by
      refine ⟨?_, ?_⟩
      · have : k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
        rw [this]
        exact h.K.mul_mem hk (h.conj_mem_K hxH (h.K.inv_mem hk))
      · exact O.mul_mem (CFSG.pPrimeCore_normal.conj_mem x hxO k) (O.inv_mem hxO)
    rw [hKO, Subgroup.mem_bot] at h1
    calc k * x = (k * x * k⁻¹ * x⁻¹) * x * k := by group
      _ = x * k := by rw [h1, one_mul]
  have hFO : h.F ≤ O := by
    refine le_pPrimeCore_of_map_normal h.odd_card_F ⟨fun y hy z => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hsurj z
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨x * w * x⁻¹, fr.conj_mem_F hx hw, by rw [map_mul, map_mul, map_inv]⟩
  set M := (h.K ⊔ fr.E).map π
  have hJKE : h.J ∉ h.K ⊔ fr.E := fun hJ =>
    h.J_ne_one (Subgroup.disjoint_def.mp fr.isInternalDirectProduct_H.2.1
      (Subgroup.mem_zpowers h.J) hJ)
  have hJM : (π h.J) ∉ M := by
    rintro ⟨y, hy, hyJ⟩
    have hyJ' : y⁻¹ * h.J ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (π y)⁻¹ * π h.J = 1
      rw [hyJ, inv_mul_cancel]
    have hyH : y ∈ h.H := sup_le h.K_le_H fr.E_le_H hy
    have hF : y⁻¹ * h.J ∈ h.F :=
      hHO_F ⟨h.H.mul_mem (h.H.inv_mem hyH) h.J_mem_H, hyJ'⟩
    apply hJKE
    have : h.J = y * (y⁻¹ * h.J) := by group
    rw [this]
    exact (h.K ⊔ fr.E).mul_mem hy (Subgroup.mem_sup_right (fr.F_le_E hF))
  have hMC : M ≤ Subgroup.centralizer ({π h.J} : Set (G ⧸ O)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      h.commute_J (sup_le h.K_le_H fr.E_le_H hy)]
  have hsup : Subgroup.zpowers (π h.J) ⊔ M = ⊤ := by
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup, fr.isInternalDirectProduct_H.1, hHtop]
  have hMn : M.Normal := by
    refine ⟨fun y hy z => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hsurj z
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨x * w * x⁻¹, fr.conj_mem_KE hx hw, by rw [map_mul, map_mul, map_inv]⟩
  refine ⟨hHO, ⟨M, hMn, hJM, hMC, hsup, ?_⟩, h.mod_eight⟩
  set K₀ := h.K.map π
  have hK₀M : K₀ ≤ M := Subgroup.map_mono le_sup_left
  refine ⟨K₀, hK₀M, ?_, ?_, ⟨(mapQuotientEquiv O hKO).symm.trans h.iso⟩⟩
  · rw [Subgroup.normal_subgroupOf_iff hK₀M]
    rintro _ _ ⟨k, hk, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨y * k * y⁻¹, h.conj_mem_K (sup_le h.K_le_H fr.E_le_H hy) hk,
      by rw [map_mul, map_mul, map_inv]⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨y, hy, rfl⟩, hyC⟩
    have hyH : y ∈ h.H := sup_le h.K_le_H fr.E_le_H hy
    have hyCK : y ∈ h.CK := by
      refine ⟨hyH, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have hc := Subgroup.mem_centralizer_iff.mp hyC (π k) ⟨k, hk, rfl⟩
      have h1 : k * y * k⁻¹ * y⁻¹ ∈ h.K ⊓ O := by
        refine ⟨?_, ?_⟩
        · have : k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) := by group
          rw [this]
          exact h.K.mul_mem hk (h.conj_mem_K hyH (h.K.inv_mem hk))
        · show k * y * k⁻¹ * y⁻¹ ∈ O
          rw [← QuotientGroup.eq_one_iff]
          change π k * π y * (π k)⁻¹ * (π y)⁻¹ = 1
          rw [hc]
          group
      rw [hKO, Subgroup.mem_bot] at h1
      calc k * y = (k * y * k⁻¹ * y⁻¹) * y * k := by group
        _ = y * k := by rw [h1, one_mul]
    have hyF : y ∈ h.F := by
      rw [← fr.isInternalDirectProduct_CK.1.1] at hyCK
      have hFN : h.F ≤ Subgroup.normalizer ((Subgroup.zpowers h.J : Subgroup G) : Set G) := by
        intro z hz
        rw [JT.normalizer_zpowers_of_orderOf_eq_two h.orderOf_J]
        exact h.F_le_H hz
      obtain ⟨j, hj, f, hf, rfl⟩ := (mem_sup_iff_of_le_normalizer hFN).mp hyCK
      rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
      · rwa [one_mul]
      · exfalso
        apply hJKE
        have : h.J = (h.J * f) * f⁻¹ := by group
        rw [this]
        exact (h.K ⊔ fr.E).mul_mem hy (Subgroup.mem_sup_right (fr.F_le_E (h.F.inv_mem hf)))
    exact (QuotientGroup.eq_one_iff y).mpr (hFO hyF)

theorem mem_of_odd_index {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Odd N.index) {y : Y} {k : ℕ} (hy : orderOf y = 2 ^ k) : y ∈ N := by
  have h1 : orderOf (QuotientGroup.mk y : Y ⧸ N) ∣ 2 ^ k :=
    hy ▸ orderOf_map_dvd (QuotientGroup.mk' N) y
  have h2 : orderOf (QuotientGroup.mk y : Y ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) N.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  have := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at this

theorem le_of_odd_index {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Odd N.index) {W : Subgroup Y} (hW : IsPGroup 2 W) : W ≤ N := by
  intro y hy
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hW ⟨y, hy⟩
  rw [Subgroup.orderOf_mk] at hk
  exact mem_of_odd_index hN hk

theorem Hyp.H_eq_top_of_index_two
    {X : Type} [Group X] [Finite X] (h : Hyp X)
    (hO : CFSG.pPrimeCore 2 X = ⊥) {X₀ : Subgroup X} [hX₀n : X₀.Normal] (hX₀ : X₀.index = 2) :
    h.H = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨fr⟩ := Frame.nonempty X h
  have hKX₀ : h.K ≤ X₀ := PSL2Sub.le_of_normal_index_two h.iso h.odd_p h.f_pos h.mod_eight hX₀
  have hTX₀ : fr.T ≤ X₀ := fr.T_le_K.trans hKX₀
  have hJX₀ : h.J ∉ X₀ := by
    intro hJ
    have hSX₀ : (fr.S : Subgroup X) ≤ X₀ := by
      rw [← fr.zpowers_J_sup_T]
      exact sup_le ((Subgroup.zpowers_le).mpr hJ) hTX₀
    have := Subgroup.index_dvd_of_le hSX₀
    rw [hX₀] at this
    exact fr.S.not_dvd_index this
  have hcases : ∀ x : X, x ∈ X₀ ∨ x * h.J ∈ X₀ := by
    intro x
    by_cases hx : x ∈ X₀
    · exact Or.inl hx
    · right
      rw [Subgroup.mul_mem_iff_of_index_two hX₀]
      exact iff_of_false hx hJX₀
  have hcardX : Nat.card X = 2 * Nat.card X₀ := by
    have := X₀.card_mul_index
    rw [hX₀] at this
    rw [← this, mul_comm]
  have h2X₀ : ∀ W : Subgroup X, W ≤ X₀ → IsPGroup 2 W → Nat.card W ∣ 4 := by
    intro W hWX₀ hW
    obtain ⟨S', hS'⟩ := hW.exists_le_sylow
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW
    have h8 : Nat.card (S' : Subgroup X) = 8 := h.card_sylow S'
    have hk3 : k ≤ 3 := by
      have := Subgroup.card_le_of_le hS'
      rw [hk, h8] at this
      by_contra hk3
      push Not at hk3
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      omega
    have hdvd : 2 ^ k ∣ Nat.card X₀ := by
      rw [← hk, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX₀).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have hX₀2 : ¬ 8 ∣ Nat.card X₀ := by
      intro h8'
      have : 16 ∣ Nat.card X := by
        rw [hcardX]
        exact Nat.mul_dvd_mul_left 2 h8'
      obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 2 (n := 4)
        (by norm_num; exact this)
      have := h.card_le_eight (IsPGroup.of_card hQ)
      rw [hQ] at this
      norm_num at this
    rw [hk]
    interval_cases k
    · norm_num
    · norm_num
    · norm_num
    · exact absurd hdvd hX₀2
  have hO₀ : CFSG.pPrimeCore 2 X₀ = ⊥ := by
    have hodd : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 X₀).map X₀.subtype)) := by
      rw [Subgroup.card_map_of_injective X₀.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hle : (CFSG.pPrimeCore 2 X₀).map X₀.subtype ≤ CFSG.pPrimeCore 2 X :=
      le_sSup ⟨inferInstance, hodd⟩
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ X₀.subtype_injective] at hle
    exact hle
  set T₀ := fr.T.subgroupOf X₀ with hT₀def
  have eT₀ : T₀ ≃* fr.T := Subgroup.subgroupOfEquivOfLe hTX₀
  have hT₀2 : IsPGroup 2 T₀ := fr.isPGroup_T.of_equiv eT₀.symm
  have hT₀idx : ¬ 2 ∣ T₀.index := by
    rintro ⟨k, hk⟩
    have hc := T₀.card_mul_index
    rw [Nat.card_congr eT₀.toEquiv, fr.card_T, hk] at hc
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := X₀) 2 (n := 3)
      (by rw [← hc]; exact ⟨k, by ring⟩)
    have := h2X₀ (Q.map X₀.subtype) (Subgroup.map_subtype_le Q) ((IsPGroup.of_card hQ).map _)
    rw [Subgroup.card_map_of_injective X₀.subtype_injective, hQ] at this
    norm_num at this
  set PT : Sylow 2 X₀ := hT₀2.toSylow hT₀idx
  have hPT : (PT : Subgroup X₀) = T₀ := hT₀2.toSylow_coe hT₀idx
  have hT₀V : IsKleinFour T₀ :=
    ⟨by rw [Nat.card_congr eT₀.toEquiv, fr.card_T],
      by rw [Monoid.exponent_eq_of_mulEquiv eT₀, fr.isKleinFour_T.exponent_two]⟩
  have hKlein : ∀ P : Sylow 2 X₀, IsKleinFour (P : Subgroup X₀) := by
    intro P
    have eP := (Sylow.equiv P PT).trans (MulEquiv.subgroupCongr hPT)
    exact ⟨by rw [Nat.card_congr eP.toEquiv, hT₀V.card_four],
      by rw [Monoid.exponent_eq_of_mulEquiv eP, hT₀V.exponent_two]⟩
  have hKcard := PSL2Sub.card_eq h.iso h.odd_p h.f_pos
  have hq3 : 3 ≤ h.p ^ h.f := by
    have hp3 : 3 ≤ h.p := by
      have := (Fact.out : h.p.Prime).two_le
      rcases h.odd_p with ⟨k, hk⟩
      omega
    exact hp3.trans (Nat.le_self_pow h.f_pos.ne' h.p)
  have hK12 : 12 ≤ Nat.card h.K := by
    rw [hKcard]
    have : 3 * (3 ^ 2 - 1) ≤ h.p ^ h.f * ((h.p ^ h.f) ^ 2 - 1) :=
      Nat.mul_le_mul hq3 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq3 2) 1)
    omega
  by_cases hTn : T₀.Normal
  ·
    have hPTn : (PT : Subgroup X₀).Normal := hPT ▸ hTn
    have : (PT : Subgroup X₀).Characteristic := Sylow.characteristic_of_normal PT hPTn
    have hTnX : fr.T.Normal := by
      have hmap : (PT : Subgroup X₀).map X₀.subtype = fr.T := by
        rw [hPT, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTX₀]
      rw [← hmap]
      infer_instance
    set Y := X₀ ⊓ Subgroup.centralizer (fr.T : Set X) with hYdef
    have hTY : fr.T ≤ Y := le_inf hTX₀ (fun t ht => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      fr.comm_of_mem_S (fr.T_le_S hs) (fr.T_le_S ht))
    have hTYidx : ¬ 2 ∣ (fr.T.subgroupOf Y).index := by
      rintro ⟨k, hk⟩
      have hc := (fr.T.subgroupOf Y).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv, fr.card_T, hk] at hc
      obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := Y) 2 (n := 3)
        (by rw [← hc]; exact ⟨k, by ring⟩)
      have := h2X₀ (Q.map Y.subtype) ((Subgroup.map_subtype_le Q).trans inf_le_left)
        ((IsPGroup.of_card hQ).map _)
      rw [Subgroup.card_map_of_injective Y.subtype_injective, hQ] at this
      norm_num at this
    have hTc : fr.T ≤ Subgroup.centralizer (Y : Set X) := fun t ht =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp hy.2 t ht).symm
    obtain ⟨⟨hsup, -, -⟩, hoddY⟩ := isInternalDirectProduct_oddPart hTY fr.isPGroup_T hTYidx hTc
    have hOY : oddPart Y = ⊥ := by
      have hn : (oddPart Y).Normal := by
        refine ⟨fun y hy g => hoddY _ ⟨hX₀n.conj_mem y (oddPart_le Y hy).1 g,
          Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩ (by
            rw [orderOf_conj_mul]
            exact odd_orderOf_of_mem_oddPart hy)⟩
        have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ fr.T := hTnX.conj_mem t ht g⁻¹
        have hc := Subgroup.mem_centralizer_iff.mp (oddPart_le Y hy).2 _ ht'
        calc t * (g * y * g⁻¹) = g * ((g⁻¹ * t * g⁻¹⁻¹) * y) * g⁻¹ := by group
          _ = g * (y * (g⁻¹ * t * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
          _ = g * y * g⁻¹ * t := by group
      have : oddPart Y ≤ CFSG.pPrimeCore 2 X := le_sSup ⟨hn, coprime_card_oddPart Y⟩
      rw [hO] at this
      exact le_bot_iff.mp this
    have hYT : Y = fr.T := by rw [← hsup, hOY, sup_bot_eq]
    have hX₀N : X₀ ≤ Subgroup.normalizer (fr.T : Set X) := fun x _ =>
      JT.mem_normalizer_of_conj_mem fun t ht => hTnX.conj_mem t ht x
    let := JT.conjAct X₀ fr.T hX₀N
    let φ : X₀ →* MulAut fr.T := MulDistribMulAction.toMulAut X₀ fr.T
    have hker : φ.ker = fr.T.subgroupOf X₀ := by
      ext n
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have hmem : (n : X) ∈ fr.T ↔ (n : X) ∈ Y := by rw [hYT]
      rw [hmem]
      constructor
      · intro hn
        refine ⟨n.2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
        have := congrArg Subtype.val (DFunLike.congr_fun hn ⟨t, ht⟩)
        change (n : X) * t * (n : X)⁻¹ = t at this
        calc t * n = ((n : X) * t * (n : X)⁻¹) * n := by rw [this]
          _ = n * t := by group
      · rintro ⟨-, hnC⟩
        ext t
        change (n : X) * t * (n : X)⁻¹ = t
        rw [← Subgroup.mem_centralizer_iff.mp hnC t t.2, mul_inv_cancel_right]
    have hcard : Nat.card X₀ = 4 * Nat.card φ.range := by
      have h1 := φ.ker.card_mul_index
      rw [Subgroup.index_ker, hker, Nat.card_congr eT₀.toEquiv, fr.card_T] at h1
      exact h1.symm
    have hdvd6 : Nat.card φ.range ∣ 6 := by
      have := fr.isKleinFour_T
      rw [← JT.PSL2Facts.card_mulAut_of_isKleinFour fr.T]
      exact Subgroup.card_subgroup_dvd_card _
    have hodd : ¬ 2 ∣ Nat.card φ.range := by
      rintro ⟨k, hk⟩
      obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := X₀) 2 (n := 3)
        (by rw [hcard, hk]; exact ⟨k, by ring⟩)
      have := h2X₀ (Q.map X₀.subtype) (Subgroup.map_subtype_le Q) ((IsPGroup.of_card hQ).map _)
      rw [Subgroup.card_map_of_injective X₀.subtype_injective, hQ] at this
      norm_num at this
    have hKle : Nat.card h.K ≤ Nat.card X₀ := Subgroup.card_le_of_le hKX₀
    have h3 : Nat.card φ.range = 3 := by
      have hpos : 0 < Nat.card φ.range := Nat.card_pos
      have hle : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
      interval_cases hc : Nat.card φ.range <;> omega
    have hKX₀eq : h.K = X₀ :=
      Subgroup.eq_of_le_of_card_ge hKX₀ (by rw [hcard, h3]; omega)
    rw [eq_top_iff]
    intro x _
    rcases hcases x with hx | hx
    · rw [← hKX₀eq] at hx
      exact h.K_le_H hx
    · rw [← hKX₀eq] at hx
      have : x = (x * h.J) * h.J⁻¹ := by group
      rw [this]
      exact h.H.mul_mem (h.K_le_H hx) (h.H.inv_mem h.J_mem_H)
  ·
    have hX₀not2 : ¬ IsPGroup 2 X₀ := by
      intro h2
      have h4 := h2X₀ X₀ le_rfl h2
      have hTX₀eq : fr.T = X₀ := Subgroup.eq_of_le_of_card_ge hTX₀ (by
        rw [fr.card_T]
        exact Nat.le_of_dvd (by norm_num) h4)
      apply hTn
      have : T₀ = ⊤ := by
        rw [hT₀def, hTX₀eq]
        exact Subgroup.subgroupOf_self X₀
      rw [this]
      exact Subgroup.normal_top
    obtain ⟨L, hLn, hLi, p', f', hfact, hp'odd, hf', ⟨eL⟩⟩ :=
      exists_psl2_of_kleinFour hO₀ hKlein hX₀not2
    set G₁ := L.map X₀.subtype with hG₁def
    let eG : G₁ ≃* PSL(2, GaloisField p' f') :=
      (L.equivMapOfInjective _ X₀.subtype_injective).symm.trans eL
    have hG₁X₀ : G₁ ≤ X₀ := Subgroup.map_subtype_le L
    have hG₁n : ∀ x ∈ X₀, ∀ y ∈ G₁, x * y * x⁻¹ ∈ G₁ := by
      rintro x hx _ ⟨y, hy, rfl⟩
      exact ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, hLn.conj_mem y hy _, rfl⟩
    have hTG₁ : fr.T ≤ G₁ := by
      intro t ht
      have : (⟨t, hTX₀ ht⟩ : X₀) ∈ L := le_of_odd_index hLi hT₀2 (by
        rw [hT₀def, Subgroup.mem_subgroupOf]
        exact ht)
      exact ⟨_, this, rfl⟩
    have h8' : p' ^ f' % 8 = 3 ∨ p' ^ f' % 8 = 5 :=
      PSL2Sub.mod_eight eG hp'odd hf' fun _ _ hP => h.isMulCommutative_of_isPGroup hP
    have hr3 : 3 < p' ^ f' := by
      by_contra hr3
      have hp'3 : 3 ≤ p' := by
        have := (Fact.out : p'.Prime).two_le
        rcases hp'odd with ⟨k, hk⟩
        omega
      have hr : p' ^ f' = 3 := by
        have : 3 ≤ p' ^ f' := hp'3.trans (Nat.le_self_pow hf'.ne' p')
        omega
      apply hTn
      have h12 : Nat.card G₁ = 12 := by
        rw [PSL2Sub.card_eq eG hp'odd hf', hr]
        norm_num
      have hN12 := PSL2Sub.card_inf_normalizer eG hp'odd hf' h8' hTG₁ fr.isKleinFour_T
      have hG₁N : G₁ ≤ Subgroup.normalizer (fr.T : Set X) := by
        have := Subgroup.eq_of_le_of_card_ge (inf_le_left : G₁ ⊓ Subgroup.normalizer
          (fr.T : Set X) ≤ G₁) (by rw [hN12, h12])
        rw [← this]
        exact inf_le_right
      refine ⟨fun t ht x => ?_⟩
      rw [hT₀def, Subgroup.mem_subgroupOf] at ht ⊢
      set T' := fr.T.map (MulAut.conj (x : X)).toMonoidHom
      have hT'G₁ : T' ≤ G₁ := by
        rintro _ ⟨s, hs, rfl⟩
        exact hG₁n x x.2 s (hTG₁ hs)
      have hT' : Nat.card T' = 4 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj (x : X)).injective, fr.card_T]
      obtain ⟨g, hgG₁, hg⟩ := PSL2Sub.exists_conj_of_card_four eG hp'odd hf' h8' hTG₁ hT'G₁
        fr.card_T hT'
      have h1 := hg ((x : X) * t * (x : X)⁻¹) ⟨t, ht, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hG₁N hgG₁)) _).mp h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [show g⁻¹ * (g * ((x : X) * t * (x : X)⁻¹) * g⁻¹) * g⁻¹⁻¹ =
        (x : X) * t * (x : X)⁻¹ by group] at h2
    have hsimple : IsSimpleGroup G₁ := by
      have : IsSimpleGroup PSL(2, GaloisField p' f') :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
          rw [GaloisField.card _ _ hf'.ne']
          omega)
      exact eG.isSimpleGroup
    have hJN : ∀ y ∈ G₁, h.J * y * h.J⁻¹ ∈ G₁ := by
      set G₁' := G₁.map (MulAut.conj h.J).toMonoidHom
      have hG₁'X₀ : G₁' ≤ X₀ := by
        rintro _ ⟨y, hy, rfl⟩
        exact hX₀n.conj_mem y (hG₁X₀ hy) h.J
      have hG₁'n : (G₁'.subgroupOf X₀).Normal := by
        rw [Subgroup.normal_subgroupOf_iff hG₁'X₀]
        rintro _ x ⟨y, hy, rfl⟩ hx
        have hx' : h.J⁻¹ * x * h.J⁻¹⁻¹ ∈ X₀ := hX₀n.conj_mem x hx h.J⁻¹
        refine ⟨(h.J⁻¹ * x * h.J⁻¹⁻¹) * y * (h.J⁻¹ * x * h.J⁻¹⁻¹)⁻¹, hG₁n _ hx' y hy, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have hcardG₁' : Nat.card G₁' = Nat.card G₁ :=
        Subgroup.card_map_of_injective (MulAut.conj h.J).injective
      have hG₁'i : Odd (G₁'.subgroupOf X₀).index := by
        have h1 := (G₁'.subgroupOf X₀).card_mul_index
        have h2 := L.card_mul_index
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG₁'X₀).toEquiv, hcardG₁',
          hG₁def, Subgroup.card_map_of_injective X₀.subtype_injective] at h1
        rw [← h2] at h1
        rwa [Nat.eq_of_mul_eq_mul_left Nat.card_pos h1]
      have hTG₁' : fr.T ≤ G₁' := by
        intro t ht
        have : (⟨t, hTX₀ ht⟩ : X₀) ∈ G₁'.subgroupOf X₀ :=
          le_of_odd_index hG₁'i hT₀2 (by rw [hT₀def, Subgroup.mem_subgroupOf]; exact ht)
        exact this
      have hint : ((G₁ ⊓ G₁').subgroupOf G₁).Normal := by
        rw [Subgroup.normal_subgroupOf_iff inf_le_left]
        intro a b ha hb
        exact ⟨G₁.mul_mem (G₁.mul_mem hb ha.1) (G₁.inv_mem hb),
          hG₁'n.conj_mem ⟨a, hG₁'X₀ ha.2⟩ ha.2 ⟨b, hG₁X₀ hb⟩⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((G₁ ⊓ G₁').subgroupOf G₁) with hb | ht
      · exfalso
        obtain ⟨t, htT, ht1⟩ : ∃ t ∈ fr.T, t ≠ 1 := by
          by_contra hcon
          push Not at hcon
          have : fr.T = ⊥ := eq_bot_iff.mpr fun x hx => hcon x hx
          have h4 : Nat.card fr.T = 4 := fr.card_T
          rw [this, Subgroup.card_bot] at h4
          omega
        have : (⟨t, hTG₁ htT⟩ : G₁) ∈ (G₁ ⊓ G₁').subgroupOf G₁ :=
          Subgroup.mem_subgroupOf.mpr ⟨hTG₁ htT, hTG₁' htT⟩
        rw [hb, Subgroup.mem_bot] at this
        exact ht1 (congrArg Subtype.val this)
      · have hle : G₁ ≤ G₁' := fun y hy => by
          have : (⟨y, hy⟩ : G₁) ∈ (G₁ ⊓ G₁').subgroupOf G₁ := ht ▸ Subgroup.mem_top _
          exact (Subgroup.mem_subgroupOf.mp this).2
        have heq : G₁ = G₁' := Subgroup.eq_of_le_of_card_ge hle hcardG₁'.le
        intro y hy
        rw [heq]
        exact ⟨y, hy, rfl⟩
    have hG₁nX : G₁.Normal := by
      refine ⟨fun y hy g => ?_⟩
      rcases hcases g with hg | hg
      · exact hG₁n g hg y hy
      · have h1 := hG₁n (g * h.J) hg (h.J⁻¹ * y * h.J⁻¹⁻¹) (by
          rw [h.J_inv]
          exact hJN y hy)
        rwa [show g * h.J * (h.J⁻¹ * y * h.J⁻¹⁻¹) * (g * h.J)⁻¹ = g * y * g⁻¹ by group] at h1
    set CG := Subgroup.centralizer (G₁ : Set X) with hCGdef
    have hCGn : CG.Normal := by
      refine ⟨fun c hc g => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ G₁ := hG₁nX.conj_mem y hy g⁻¹
      have := Subgroup.mem_centralizer_iff.mp hc _ hy'
      calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
        _ = g * c * g⁻¹ * y := by group
    have hY₁ : X₀ ⊓ CG = ⊥ := by
      have hY₁n : (X₀ ⊓ CG).Normal := Subgroup.normal_inf_normal X₀ CG
      have hY₁G₁ : X₀ ⊓ CG ⊓ G₁ = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨⟨-, hxC⟩, hxG⟩
        exact PSL2Sub.eq_one_of_commute eG hxG fun k hk =>
          (Subgroup.mem_centralizer_iff.mp hxC k hk).symm
      have hodd : Nat.Coprime 2 (Nat.card (X₀ ⊓ CG : Subgroup X)) := by
        rw [Nat.coprime_two_left, Nat.odd_iff]
        by_contra h2
        obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (X₀ ⊓ CG : Subgroup X)) 2
          (Nat.dvd_of_mod_eq_zero (by omega))
        have hu2 : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe, hu]
        set U := Subgroup.zpowers (u : X)
        have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, hu2, pow_one])
        have hc : ∀ x ∈ U, ∀ y ∈ fr.T, x * y = y * x := by
          intro x hx y hy
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          have := (Subgroup.mem_centralizer_iff.mp u.2.2 y (hTG₁ hy)).symm
          exact (Commute.zpow_left this n).eq
        have hd : U ⊓ fr.T = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.1
          have hmem : (u : X) ^ n ∈ X₀ ⊓ CG ⊓ G₁ :=
            ⟨Subgroup.zpow_mem _ u.2 n, hTG₁ hx.2⟩
          rw [hY₁G₁] at hmem
          exact hmem
        have hUN : U ≤ Subgroup.normalizer (fr.T : Set X) := fun x hx =>
          JT.mem_normalizer_of_conj_mem fun t ht => by
            rw [hc x hx t ht, mul_inv_cancel_right]
            exact ht
        have h2' : IsPGroup 2 (fr.T ⊔ U : Subgroup X) :=
          IsPGroup.to_sup_of_normal_left' fr.isPGroup_T hU2 hUN
        obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute U fr.T hc
        rw [hd, Subgroup.card_bot, mul_one, Nat.card_zpowers, hu2, fr.card_T] at hcard
        have hle : fr.T ⊔ U ≤ X₀ := sup_le hTX₀ ((Subgroup.zpowers_le).mpr u.2.1)
        have := h2X₀ _ hle h2'
        rw [sup_comm, hcard] at this
        norm_num at this
      have := le_sSup (s := {K : Subgroup X | K.Normal ∧ Nat.Coprime 2 (Nat.card K)})
        ⟨hY₁n, hodd⟩
      rw [← CFSG.pPrimeCore, hO] at this
      exact le_bot_iff.mp this
    have hCG2 : Nat.card CG ≤ 2 := by
      have h1 := card_eq_card_map_mul_card_inf_ker (QuotientGroup.mk' X₀) CG
      rw [QuotientGroup.ker_mk', inf_comm, hY₁, Subgroup.card_bot, mul_one] at h1
      rw [h1]
      calc Nat.card (CG.map (QuotientGroup.mk' X₀)) ≤ Nat.card (X ⧸ X₀) :=
            Subgroup.card_le_card_group _
        _ = 2 := hX₀
    by_cases hCGb : CG = ⊥
    ·
      exfalso
      have hJNG : h.J ∈ Subgroup.normalizer (G₁ : Set X) :=
        JT.mem_normalizer_of_conj_mem fun y hy => hJN y hy
      obtain ⟨e', P₀, hT'⟩ := PSL2Sub.exists_coords eG hp'odd hf' h8' hTG₁ fr.card_T
      set F := GaloisField p' f'
      set ι0 := psl2Map (algebraMap (ZMod p') F)
      set V₀ := (P₀ : Subgroup PSL(2, ZMod p')).map ι0
      have hp8 : p' ^ 1 % 8 = 3 ∨ p' ^ 1 % 8 = 5 := by
        rw [pow_one, ← pow_mod_eight_of_odd hp'odd (odd_of_pow_mod_eight hp'odd h8')]
        exact h8'
      have hZ : Nat.card (ZMod p') = p' ^ 1 := by rw [Nat.card_zmod, pow_one]
      have hV₀ : IsKleinFour V₀ := isKleinFour_map_of_injective _
        (psl2_sylow_two_isKleinFour (ZMod p') hZ hp'odd one_pos hp8 P₀) _ (psl2Map_injective _)
      have hV₀fix : ∀ τ : F ≃+* F, ∀ v ∈ V₀, psl2FieldAut _ τ v = v := by
        rintro τ _ ⟨x, -, rfl⟩
        exact psl2FieldAut_psl2Map_zmod τ x
      set α := PSL2Sub.conjHom e' ⟨h.J, hJNG⟩
      have hα2 : α ^ 2 = 1 := by
        rw [← map_pow]
        have : (⟨h.J, hJNG⟩ : Subgroup.normalizer (G₁ : Set X)) ^ 2 = 1 :=
          Subtype.ext (by rw [Subgroup.coe_pow, pow_two, h.J_mul_J]; rfl)
        rw [this, map_one]
      have hαV : ∀ v ∈ V₀, α v = v := by
        intro v hv
        apply PSL2Sub.emb_injective e'
        rw [PSL2Sub.emb_conjHom]
        have hvT : psl2Emb e' v ∈ fr.T := by
          rw [hT']
          exact ⟨v, hv, rfl⟩
        change h.J * psl2Emb e' v * h.J⁻¹ = psl2Emb e' v
        rw [fr.comm_of_mem_S fr.J_mem (fr.T_le_S hvT), mul_inv_cancel_right]
      obtain ⟨g0, hg0V, hg0⟩ := eq_conj_of_sq_eq_one hp'odd hf' h8' hr3 hV₀ hV₀fix α hα2 hαV
      set x₀ := psl2Emb e' g0
      have hx₀T : x₀ ∈ fr.T := by
        rw [hT']
        exact ⟨g0, hg0V, rfl⟩
      have hmem : x₀⁻¹ * h.J ∈ CG := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨y', rfl⟩ := PSL2Sub.exists_emb_eq e' hy
        have h1 := (PSL2Sub.conjHom_eq_iff e' _ _).mp hg0 y'
        change h.J * psl2Emb e' y' * h.J⁻¹ = psl2Emb e' (MulAut.conj g0 y') at h1
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
        change h.J * psl2Emb e' y' * h.J⁻¹ = x₀ * psl2Emb e' y' * x₀⁻¹ at h1
        calc psl2Emb e' y' * (x₀⁻¹ * h.J) = x₀⁻¹ * (x₀ * psl2Emb e' y' * x₀⁻¹) * h.J := by group
          _ = x₀⁻¹ * (h.J * psl2Emb e' y' * h.J⁻¹) * h.J := by rw [h1]
          _ = x₀⁻¹ * h.J * psl2Emb e' y' := by group
      rw [hCGb, Subgroup.mem_bot] at hmem
      have hJx₀ : h.J = x₀ := by
        have := congrArg (x₀ * ·) hmem
        simpa using this
      exact h.J_not_mem_K (hJx₀ ▸ fr.T_le_K hx₀T)
    ·
      obtain ⟨⟨z, hzC⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCGb
      have hz1 : z ≠ 1 := fun h1 => hz1' (Subtype.ext h1)
      have huniq : ∀ w ∈ CG, w ≠ 1 → w = z := by
        intro w hw hw1
        by_contra hwz
        have hsub : ({1, z, w} : Set X) ⊆ CG := by
          intro x hx
          rcases hx with rfl | rfl | rfl
          · exact CG.one_mem
          · exact hzC
          · exact hw
        have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_insert_of_notMem (by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨fun h => hz1 h.symm, fun h => hw1 h.symm⟩),
          Set.ncard_pair (Ne.symm hwz)] at h3
        rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h3
        omega
      have hzZ : ∀ g : X, g * z = z * g := by
        intro g
        have hgz : g * z * g⁻¹ ∈ CG := hCGn.conj_mem z hzC g
        have hgz1 : g * z * g⁻¹ ≠ 1 := by
          intro h1
          apply hz1
          have := congrArg (fun w => g⁻¹ * w * g) h1
          simpa [mul_assoc] using this
        have := huniq _ hgz hgz1
        calc g * z = (g * z * g⁻¹) * g := by group
          _ = z * g := by rw [this]
      have hzH : z ∈ h.H := h.mem_H_iff.mpr (hzZ h.J).symm
      have hzCK : z ∈ h.CK := ⟨hzH, Subgroup.mem_centralizer_iff.mpr fun k _ => hzZ k⟩
      have hz2 : z * z = 1 := by
        have hzz : z * z ∈ CG := CG.mul_mem hzC hzC
        by_contra hzz1
        have := huniq _ hzz hzz1
        have : z = 1 := by
          calc z = z * z * z⁻¹ := by group
            _ = z * z⁻¹ := by rw [this]
            _ = 1 := mul_inv_cancel z
        exact hz1 this
      have hzJ : z = h.J := by
        rw [← fr.isInternalDirectProduct_CK.1.1] at hzCK
        have hFN : h.F ≤ Subgroup.normalizer
            ((Subgroup.zpowers h.J : Subgroup X) : Set X) := by
          intro y hy
          rw [JT.normalizer_zpowers_of_orderOf_eq_two h.orderOf_J]
          exact h.F_le_H hy
        obtain ⟨j, hj, f₁, hf₁, hjf⟩ := (mem_sup_iff_of_le_normalizer hFN).mp hzCK
        have hf₁odd := odd_orderOf_of_mem_oddPart hf₁
        rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
        · exfalso
          rw [one_mul] at hjf
          rw [← hjf] at hz2
          have : orderOf f₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
          rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
          · rw [orderOf_eq_one_iff] at h1
            exact hz1 (hjf.symm.trans h1)
          · rw [h1] at hf₁odd
            exact absurd hf₁odd (by decide)
        ·
          have hf₁ : f₁ = h.J⁻¹ * z := by rw [← hjf]; group
          have hJz : h.J⁻¹ * z = z * h.J⁻¹ := hzZ h.J⁻¹
          have h2 : f₁ * f₁ = 1 := by
            rw [hf₁]
            calc h.J⁻¹ * z * (h.J⁻¹ * z) = h.J⁻¹ * (z * h.J⁻¹) * z := by group
              _ = h.J⁻¹ * (h.J⁻¹ * z) * z := by rw [hJz]
              _ = (h.J⁻¹ * h.J⁻¹) * (z * z) := by group
              _ = 1 := by rw [hz2, h.J_inv, h.J_mul_J, one_mul]
          have : orderOf f₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
          rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
          · rw [orderOf_eq_one_iff] at h1
            rw [h1, mul_one] at hjf
            exact hjf.symm
          · rw [h1] at hf₁odd
            exact absurd hf₁odd (by decide)
      rw [eq_top_iff]
      intro g _
      rw [h.mem_H_iff, ← hzJ]
      exact hzZ g

theorem prop_2_3 :
    ∀ (G : Type) [Group G] [Finite G] (h : Hyp G), (∃ N : Subgroup G, N.Normal ∧ N.index = 2) →
      h.H ⊔ CFSG.pPrimeCore 2 G = ⊤ := by
  intro G _ _ h ⟨N, hNn, hN2⟩
  set O := CFSG.pPrimeCore 2 G
  set π := QuotientGroup.mk' O
  have hO : Odd (Nat.card O) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := G)
    rwa [Nat.coprime_two_left] at this
  have hON : O ≤ N := fun x hx =>
    mem_of_index_two_of_odd hN2 (Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard _ hx))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have : (N.map π).Normal := hNn.map π hπ
  have hN2' : (N.map π).index = 2 := by
    rw [Subgroup.index_map_eq _ hπ (by rw [QuotientGroup.ker_mk']; exact hON), hN2]
  have htop := (h.quotient O hO).H_eq_top_of_index_two pPrimeCore_quotient_eq_bot hN2'
  rw [eq_top_iff]
  intro g _
  have hg : π g ∈ (h.quotient O hO).H := htop ▸ Subgroup.mem_top _
  rw [Hyp.mem_H_iff, Hyp.quotient_J] at hg
  obtain ⟨c, hc, hcg⟩ := Suzuki.exists_commute_mk_eq O hO h.J_mul_J hg
  have hcO : c⁻¹ * g ∈ O := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcg]
    exact inv_mul_cancel _
  have : g = c * (c⁻¹ * g) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left (h.mem_H_iff.mpr hc)) (Subgroup.mem_sup_right hcO)

end CFSG.Walter.W67
