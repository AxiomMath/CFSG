module

public import CFSG.Quasithin.H13.U3S1348B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin B2F
open scoped Pointwise

section Block

variable {W : Type} [CommGroup W] [Finite W] {J : Subgroup (MulAut W)}
  {𝓗 : Finset (Subgroup (MulAut W))}

theorem block_two_transvections (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    {L : Subgroup (MulAut W)} (hL : L ∈ 𝓗) :
    ∃ t₁ ∈ transvectionsIn L, ∃ t₂ ∈ transvectionsIn L, t₁ ≠ t₂ := by
  by_contra h
  push Not at h
  have h6 := hb.card_eq L hL
  rcases (transvectionsIn L).eq_empty_or_nonempty with he | ⟨t, ht⟩
  · have := hb.closure_eq L hL
    rw [he, Subgroup.closure_empty] at this
    rw [← this, card_bot] at h6
    omega
  · have hle : L ≤ zpowers t := by
      rw [← hb.closure_eq L hL, closure_le]
      intro t' ht'
      rw [h t' ht' t ht]
      exact mem_zpowers t
    have hc := card_le_of_le hle
    rw [h6, Nat.card_zpowers] at hc
    obtain ⟨ht1, w, htw⟩ := ht.2
    have hsq : t * t = 1 := B1.tv_sq hW htw ht1
    have h2 : orderOf t ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hsq)
    omega

theorem block_eq_one_of_commute (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    {L : Subgroup (MulAut W)} (hL : L ∈ 𝓗) {d t : MulAut W} (hdL : d ∈ L) (htL : t ∈ L)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hdt : d * t = t * d) (hd : ∃ m, Odd m ∧ d ^ m = 1) :
    d = 1 := by
  by_contra hd1
  have h6 := hb.card_eq L hL
  obtain ⟨m, hm, hdm⟩ := hd
  have ho6 : orderOf d ∣ 6 := by
    have := orderOf_dvd_natCard (⟨d, hdL⟩ : ↥L)
    rwa [Subgroup.orderOf_mk, h6] at this
  have hoodd : Odd (orderOf d) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hdm)
  have ho3 : orderOf d = 3 := by
    have hpos : 0 < orderOf d := Nat.pos_of_dvd_of_pos ho6 (by norm_num)
    have hle : orderOf d ≤ 6 := Nat.le_of_dvd (by norm_num) ho6
    interval_cases h : orderOf d
    · exact absurd (orderOf_eq_one_iff.1 h) hd1
    · exact absurd hoodd (by decide)
    · rfl
    · exact absurd ho6 (by decide)
    · exact absurd ho6 (by decide)
    · exact absurd hoodd (by decide)
  have hot : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hdto : orderOf (d * t) = 6 := by
    rw [(Commute.orderOf_mul_eq_mul_orderOf_of_coprime hdt (by rw [ho3, hot]; norm_num)), ho3,
      hot]
  have hzL : zpowers (d * t) ≤ L := zpowers_le.2 (mul_mem hdL htL)
  have hzeq : zpowers (d * t) = L := eq_of_le_of_card_ge hzL (by rw [h6, Nat.card_zpowers, hdto])
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb'
    rw [← hzeq] at ha hb'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb'
    exact (Commute.zpow_zpow_self (d * t) i j).eq
  obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := block_two_transvections hW hb hL
  obtain ⟨ht₁1, w₁, hw₁⟩ := ht₁.2
  obtain ⟨ht₂1, w₂, hw₂⟩ := ht₂.2
  exact IsTransvectionBlocks.not_commuting_involutions h6 ht₁.1 ht₂.1
    (by rw [pow_two]; exact B1.tv_sq hW hw₁ ht₁1) (by rw [pow_two]; exact B1.tv_sq hW hw₂ ht₂1)
    ht₁1 ht₂1 hne (hcomm t₁ ht₁.1 t₂ ht₂.1)

end Block

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}
  {H R : Subgroup G} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

namespace BlocksR

theorem conjAut_mem (B : BlocksR (hV := hV) H R 𝓗 I) {g : MulAut (IntMod V hV)}
    (hg : g ∈ autI hV H) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    B1.conjAut g L ∈ I := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hN' : B1.conjAut g (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, L := by
    rw [← B.eq, conjAut_autI_conjClosure hg]
  exact B.hb.conjAut_mem hW B.sub hg hN' hL

omit [Finite G] in
theorem thompsonJ_le (B : BlocksR (hV := hV) H R 𝓗 I) :
    autI hV (thompsonJ R) ≤ ⨆ L ∈ I, L := by
  rw [← B.eq]
  exact autI_mono hV (le_conjClosure _ H)

open scoped Classical in
theorem le_of_inf_eq_bot (B : BlocksR (hV := hV) H R 𝓗 I) (hred : IsTwoReducedIn H V)
    (hsolv : Group.IsSolvable ↥H) (hVR : V ≤ R) (hRH : R ≤ H)
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I)
    (h0 : autI hV (thompsonJ R) ⊓ L = ⊥) :
    autI hV (thompsonJ R) ≤ ⨆ K ∈ I.erase L, K := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hHN : H ≤ normalizer (V : Set G) := hred.2.1
  have hRN : R ≤ normalizer (V : Set G) := hRH.trans hHN
  have hsolvX := isSolvable_autI hV hHN hsolv
  have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 => eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
  have hJI := B.thompsonJ_le
  conv_lhs => rw [autI_thompsonJ hV hRN]
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAR => ?_
  have hAJ : A ≤ autI hV (thompsonJ R) := by
    rw [autI_thompsonJ hV hRN]
    exact le_iSup₂_of_le A hA (le_iSup_of_le hAR le_rfl)
  have hoff : IsFFStarOffender (autI hV H) A :=
    isFFStarOffender_mono (autI_mono hV hRH) (offenderImages_isFFStarOffender hV hVR hRN hA)
  obtain ⟨a, ha, -, hAeq⟩ := (B.hb.offender_iff hW hsolvX hO2 A).1 hoff
  rw [hAeq]
  refine iSup₂_le fun K hK => ?_
  have haK : a K ≤ K := by
    rcases ha K hK with h | h
    · rw [h]; exact bot_le
    · exact h.1
  have haA : a K ≤ A := hAeq ▸ le_iSup₂_of_le
    (f := fun (K' : Subgroup (MulAut (IntMod V hV))) (_ : K' ∈ 𝓗) => a K') K hK le_rfl
  by_cases hKL : K = L
  · subst hKL
    have hbot : a K ≤ ⊥ := by
      rw [← h0]
      exact le_inf (haA.trans hAJ) haK
    rw [le_bot_iff.1 hbot]
    exact bot_le
  by_cases hKI : K ∈ I
  · exact haK.trans (le_iSup₂_of_le (f := fun (K' : Subgroup (MulAut (IntMod V hV)))
      (_ : K' ∈ I.erase L) => K') K (Finset.mem_erase.2 ⟨hKL, hKI⟩) le_rfl)
  · have hle : (⨆ L' ∈ I, L') ≤ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ K), H' :=
      iSup₂_le fun K' hK' =>
        le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut (IntMod V hV))) (_ : H' ∈ 𝓗) =>
          ⨆ (_ : H' ≠ K), H') K' (B.sub hK')
          (le_iSup (fun _ : K' ≠ K => K') (fun h => hKI (h ▸ hK')))
    have : a K = ⊥ := by
      rw [← le_bot_iff, ← B.hb.inf_biSup_ne_eq_bot hK]
      exact le_inf haK (((haA.trans hAJ).trans hJI).trans hle)
    rw [this]
    exact bot_le

omit [Finite G] in
theorem inf_eq_bot (B : BlocksR (hV := hV) H R 𝓗 I) {L L' : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) (hL' : L' ∈ I) (hne : L ≠ L') : L ⊓ L' = ⊥ := by
  rw [← le_bot_iff, ← B.hb.inf_biSup_ne_eq_bot (B.sub hL)]
  exact inf_le_inf_left L (le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut (IntMod V hV)))
    (_ : H' ∈ 𝓗) => ⨆ (_ : H' ≠ L), H') L' (B.sub hL') (le_iSup (fun _ : L' ≠ L => L')
      (Ne.symm hne)))

omit [Finite G] in
theorem eq_pair_of_card_le_two {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I)
    (hcard : I.card ≤ 2) : I = {L} ∨ ∃ L' ∈ I, L' ≠ L ∧ ∀ K ∈ I, K = L ∨ K = L' := by
  classical
  rcases Finset.eq_singleton_or_nontrivial hL with h | h
  · exact Or.inl h
  · right
    obtain ⟨L', hL', hne⟩ := h.exists_ne L
    refine ⟨L', hL', hne, fun K hK => ?_⟩
    by_contra hK'
    push Not at hK'
    have hsub : ({L, L', K} : Finset _) ⊆ I := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hL
      · exact hL'
      · exact hK
    have h3 : ({L, L', K} : Finset _).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hne, Ne.symm hK'.1]),
        Finset.card_pair (Ne.symm hK'.2)]
    have := Finset.card_le_card hsub
    omega

theorem inf_ne_bot (B : BlocksR (hV := hV) H R 𝓗 I) (hred : IsTwoReducedIn H V)
    (hsolv : Group.IsSolvable ↥H) (hVR : V ≤ R) (hRH : R ≤ H)
    (hJ : ¬ thompsonJ R ≤ centralizer (V : Set G)) {T : Subgroup G} (hTsyl : IsSylowTwoOf T H)
    (hTR : T ≤ normalizer (R : Set G)) (hcard : I.card ≤ 2)
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    autI hV (thompsonJ R) ⊓ L ≠ ⊥ := by
  classical
  intro h0
  have hHN : H ≤ normalizer (V : Set G) := hred.2.1
  have hRN : R ≤ normalizer (V : Set G) := hRH.trans hHN
  have hJN : thompsonJ R ≤ normalizer (V : Set G) :=
    (iSup₂_le fun _ hA => hA.1 : thompsonJ R ≤ R).trans hRN
  set J' := autI hV (thompsonJ R) with hJ'
  have hJne : J' ≠ ⊥ := fun h => hJ ((autI_eq_bot_iff hV hJN).1 h)
  have hle := B.le_of_inf_eq_bot hred hsolv hVR hRH hL h0
  rcases eq_pair_of_card_le_two hL hcard with hI | ⟨L', hL', hne, hI⟩
  · apply hJne
    rw [← le_bot_iff]
    refine hle.trans (iSup₂_le fun K hK => ?_)
    rw [hI] at hK
    simp at hK
  have hJL' : J' ≤ L' := by
    refine hle.trans (iSup₂_le fun K hK => ?_)
    obtain ⟨hKL, hKI⟩ := Finset.mem_erase.1 hK
    rcases hI K hKI with h | h
    · exact absurd h hKL
    · exact h.le
  have hLL' : L ⊓ L' = ⊥ := B.inf_eq_bot hL hL' (Ne.symm hne)
  set X := autI hV H with hX
  have hTX : autI hV T ≤ X := autI_mono hV hTsyl.1
  have hTfix : ∀ t ∈ autI hV T, B1.conjAut t L' = L' := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 ht
    have hJy : B1.conjAut (convI hV y) J' = J' := by
      rw [conjAut_eq_map, hJ', autI_cjSub hV y.2,
        cjSub_eq_of_mem_normalizer (normalizer_le_normalizer_thompsonJ R (hTR hy))]
    rcases hI _ (B.conjAut_mem (hTX ((mem_autI hV).2 ⟨y, hy, rfl⟩)) hL') with h | h
    · exfalso
      apply hJne
      rw [← le_bot_iff, ← hLL']
      refine le_inf ?_ hJL'
      rw [← h, ← hJy]
      exact B1.conjAut_le_iff.2 hJL'
    · exact h
  obtain ⟨g, hgX, hg⟩ : ∃ g ∈ X, B1.conjAut g L' = L := by
    by_contra hcon
    push Not at hcon
    have hfix : ∀ g ∈ X, B1.conjAut g L' = L' := fun g hg => by
      rcases hI _ (B.conjAut_mem hg hL') with h | h
      · exact absurd h (hcon g hg)
      · exact h
    have hle' : autI hV (conjClosure (thompsonJ R) H) ≤ L' := by
      rw [← ffJP_offenderImagesIn hVR hRH hHN hJ]
      refine iSup_le fun A => iSup_le fun hA => iSup_le fun _ => ?_
      obtain ⟨h, hh, A', hA', rfl⟩ := hA
      rw [autI_cjSub_eq hV (hHN hh), ← hfix _ (convI_mem_autI hV hh (hHN hh))]
      refine B1.conjAut_le_iff.2 (le_trans ?_ hJL')
      rw [hJ', autI_thompsonJ hV hRN]
      exact le_iSup₂_of_le (autI hV A') ⟨A', hA', rfl⟩
        (le_iSup_of_le (autI_mono hV hA'.1.1) le_rfl)
    have hLle : L ≤ L' := (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV)))
      (_ : K ∈ I) => K) L hL le_rfl).trans (B.eq ▸ hle')
    have h6 := B.hb.card_eq L (B.sub hL)
    rw [inf_eq_left.2 hLle] at hLL'
    rw [hLL', card_bot] at h6
    omega
  set N₁ := X ⊓ normalizer ((L' : Subgroup (MulAut (IntMod V hV))) :
    Set (MulAut (IntMod V hV))) with hN₁
  have hmemN : ∀ b ∈ X, b ∈ N₁ ↔ B1.conjAut b L' = L' := by
    intro b hb
    rw [conjAut_eq_map]
    constructor
    · rintro ⟨-, h⟩
      exact mem_normalizer_iff_map_conj_eq.mp h
    · intro h
      exact ⟨hb, mem_normalizer_iff_map_conj_eq.mpr h⟩
  have hidx : (N₁.subgroupOf X).index = 2 := by
    refine index_eq_two_iff.2 ⟨⟨g, hgX⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul, hmemN _ (X.mul_mem b.2 hgX), hmemN _ b.2]
    have e : B1.conjAut ((b : MulAut (IntMod V hV)) * g) L' = B1.conjAut b L := by
      rw [← hg, conjAut_eq_map, conjAut_eq_map, conjAut_eq_map, map_map]
      rfl
    rw [e]
    have hbL := hI _ (B.conjAut_mem b.2 hL)
    have hbL' := hI _ (B.conjAut_mem b.2 hL')
    have hinj : B1.conjAut b L ≠ B1.conjAut b L' := fun h =>
      hne (le_antisymm (B1.conjAut_le_iff.1 h.ge) (B1.conjAut_le_iff.1 h.le))
    rcases hbL with h1 | h1 <;> rcases hbL' with h2 | h2
    · exact absurd (h1.trans h2.symm) hinj
    · rw [h1, h2]
      exact Or.inr ⟨rfl, fun h => hne h.symm⟩
    · rw [h1, h2]
      exact Or.inl ⟨rfl, fun h => hne h.symm⟩
    · exact absurd (h1.trans h2.symm) hinj
  have hsylX := isSylowTwoOf_autI hV hHN hTsyl
  have hTN : autI hV T ≤ N₁ := fun t ht => (hmemN t (hTX ht)).2 (hTfix t ht)
  have hm := relIndex_mul_relIndex (autI hV T) N₁ X hTN inf_le_left
  have hidx' : N₁.relIndex X = 2 := hidx
  rw [hidx'] at hm
  exact hsylX.2.2 (show 2 ∣ (autI hV T).relIndex X from hm ▸ dvd_mul_left 2 _)

theorem eq_one_of_normalizes (B : BlocksR (hV := hV) H R 𝓗 I) (hcard : I.card ≤ 2)
    (hR2 : IsPGroup 2 R) (hRN : R ≤ normalizer (V : Set G))
    (hmeet : ∀ L ∈ I, autI hV (thompsonJ R) ⊓ L ≠ ⊥) {d : MulAut (IntMod V hV)}
    (hdI : d ∈ ⨆ L ∈ I, L) (hd : ∃ m, Odd m ∧ d ^ m = 1)
    (hdN : d ∈ normalizer ((autI hV (thompsonJ R) : Subgroup (MulAut (IntMod V hV))) :
      Set (MulAut (IntMod V hV)))) : d = 1 := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  set J' := autI hV (thompsonJ R) with hJ'
  have hJ2 : IsPGroup 2 J' := isPGroup_autI hV (hR2.to_le (iSup₂_le fun _ hA => hA.1))
    ((iSup₂_le fun _ hA => hA.1 : thompsonJ R ≤ R).trans hRN)
  have hinv : ∀ L ∈ I, ∃ t ∈ J' ⊓ L, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ x ∈ J' ⊓ L, x = 1 ∨ x = t := by
    intro L hL
    have h6 := B.hb.card_eq L (B.sub hL)
    have hS2 : IsPGroup 2 ↥(J' ⊓ L) := hJ2.to_le inf_le_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
    have hdvd : Nat.card ↥(J' ⊓ L) ∣ 6 := h6 ▸ card_dvd_of_le inf_le_right
    have hcard2 : Nat.card ↥(J' ⊓ L) = 2 := by
      rw [hk] at hdvd ⊢
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact hmeet L hL (card_eq_one.1 hk)
      have hk1 : k ≤ 1 := by
        by_contra h
        have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans hdvd
        norm_num at this
      obtain rfl : k = 1 := by omega
      rfl
    obtain ⟨⟨t, ht⟩, ht1⟩ := (ne_bot_iff_exists_ne_one).1 (hmeet L hL)
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hto : orderOf t = 2 := by
      have h1 := orderOf_dvd_natCard (⟨t, ht⟩ : ↥(J' ⊓ L))
      rw [Subgroup.orderOf_mk, hcard2] at h1
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) ht1'
      · exact h
    have ht2 : t ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one t
    have hSeq : J' ⊓ L = zpowers t := (eq_of_le_of_card_ge (zpowers_le.2 ht)
      (by rw [hcard2, Nat.card_zpowers, hto])).symm
    refine ⟨t, ht, ht1', ht2, fun x hx => ?_⟩
    rw [hSeq] at hx
    exact IsTransvectionBlocks.eq_one_or_eq_of_sq_eq_one ht2 hx
  have hkey : ∀ L ∈ I, ∀ d' ∈ L, (∃ m, Odd m ∧ d' ^ m = 1) →
      (∀ x ∈ L, d * x * d⁻¹ = d' * x * d'⁻¹) → d' = 1 := by
    intro L hL d' hd'L hd'o hconj
    obtain ⟨t, ht, ht1, ht2, hS⟩ := hinv L hL
    have hmem : d' * t * d'⁻¹ ∈ J' ⊓ L := by
      refine mem_inf.2 ⟨?_, L.mul_mem (L.mul_mem hd'L ht.2) (L.inv_mem hd'L)⟩
      rw [← hconj t ht.2]
      exact (mem_normalizer_iff.1 hdN t).1 ht.1
    have hne1 : d' * t * d'⁻¹ ≠ 1 := fun h => ht1 (by
      have : t = d'⁻¹ * (d' * t * d'⁻¹) * d' := by group
      rw [this, h]
      group)
    rcases hS _ hmem with h | h
    · exact absurd h hne1
    · refine block_eq_one_of_commute hW B.hb (B.sub hL) hd'L ht.2 ht2 ht1 ?_ hd'o
      calc d' * t = d' * t * d'⁻¹ * d' := by group
        _ = t * d' := by rw [h]
  rcases I.eq_empty_or_nonempty with hI0 | ⟨L₁, hL₁⟩
  · rw [hI0] at hdI
    simpa using hdI
  rcases eq_pair_of_card_le_two hL₁ hcard with hI | ⟨L₂, hL₂, hne, hI⟩
  ·
    have hdL : d ∈ L₁ := by
      rw [hI] at hdI
      simpa using hdI
    exact hkey L₁ hL₁ d hdL hd fun x _ => rfl
  ·
    have hIeq : I = {L₁, L₂} := by
      ext K
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun hK => (hI K hK).elim Or.inl Or.inr, fun hK => hK.elim (· ▸ hL₁) (· ▸ hL₂)⟩
    have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a :=
      B.hb.comm L₁ (B.sub hL₁) L₂ (B.sub hL₂) (Ne.symm hne)
    have hinf : L₁ ⊓ L₂ = ⊥ := B.inf_eq_bot hL₁ hL₂ (Ne.symm hne)
    have hdsup : d ∈ L₁ ⊔ L₂ := by
      rw [hIeq, Finset.iSup_insert, Finset.iSup_singleton] at hdI
      exact hdI
    have hN₂ : L₂ ≤ normalizer ((L₁ : Subgroup (MulAut (IntMod V hV))) :
        Set (MulAut (IntMod V hV))) :=
      fun b hb => centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left L₁ L₂ hN₂
    have hd' : d ∈ (L₁ : Set (MulAut (IntMod V hV))) * (L₂ : Set (MulAut (IntMod V hV))) := by
      rw [← hmul]
      exact hdsup
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Set.mem_mul.mp hd'
    obtain ⟨m, hm, hdm⟩ := hd
    have hd12 : d₁ ^ m * d₂ ^ m = 1 := by
      rw [← (Commute.mul_pow (hcomm d₁ hd₁ d₂ hd₂) m)]
      exact hdm
    have hd1m : d₁ ^ m = 1 := by
      have h1 : d₁ ^ m ∈ L₁ ⊓ L₂ := mem_inf.2 ⟨L₁.pow_mem hd₁ m, by
        rw [eq_inv_of_mul_eq_one_left hd12]
        exact L₂.inv_mem (L₂.pow_mem hd₂ m)⟩
      rw [hinf, mem_bot] at h1
      exact h1
    have hd2m : d₂ ^ m = 1 := by rw [hd1m, one_mul] at hd12; exact hd12
    have e1 := hkey L₁ hL₁ d₁ hd₁ ⟨m, hm, hd1m⟩ fun x hx => by
      have := hcomm x hx d₂ hd₂
      calc d₁ * d₂ * x * (d₁ * d₂)⁻¹ = d₁ * (d₂ * x) * d₂⁻¹ * d₁⁻¹ := by group
        _ = d₁ * x * d₁⁻¹ := by rw [← this]; group
    have e2 := hkey L₂ hL₂ d₂ hd₂ ⟨m, hm, hd2m⟩ fun x hx => by
      have := hcomm d₁ hd₁ x hx
      calc d₁ * d₂ * x * (d₁ * d₂)⁻¹ = d₁ * d₂ * x * d₂⁻¹ * d₁⁻¹ := by group
        _ = d₂ * x * d₂⁻¹ * (d₁ * d₁⁻¹) := by
          rw [show d₁ * d₂ * x * d₂⁻¹ * d₁⁻¹ = d₁ * (d₂ * x * d₂⁻¹) * d₁⁻¹ by group]
          have h' := hcomm d₁ hd₁ (d₂ * x * d₂⁻¹) (mul_mem (mul_mem hd₂ hx) (inv_mem hd₂))
          rw [h']
          group
        _ = d₂ * x * d₂⁻¹ := by group
    rw [e1, e2, one_mul]

end BlocksR

end CFSG.Quasithin.H13.U3
