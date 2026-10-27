module

public import CFSG.Quasithin.Background.B2FactorizationBaumann

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

theorem isSylowTwoOf_cjSub {T H : Subgroup G} (g : G) (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf (cjSub g T) (cjSub g H) := by
  refine ⟨cjSub_mono hT.1, ?_, ?_⟩
  · exact hT.2.1.of_equiv
      (T.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  · have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) T H
      (MulAut.conj g).injective
    exact fun h2 => hT.2.2 (by
      show 2 ∣ T.relIndex H
      rw [← h]
      exact h2)

theorem exists_two_part_odd_part [Finite G] (c : G) :
    ∃ a b : G, c = b * a ∧ a ∈ Subgroup.zpowers c ∧ b ∈ Subgroup.zpowers c ∧
      (∃ k : ℕ, a ^ 2 ^ k = 1) ∧ Odd (orderOf b) := by
  obtain ⟨s, t, ht, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcop : Nat.Coprime (2 ^ s) t := (Nat.coprime_two_left.2 ht).pow_left s
  obtain ⟨e, he0, he1⟩ := Nat.chineseRemainder hcop 0 1
  obtain ⟨u, hu⟩ := (Nat.modEq_zero_iff_dvd).1 he0
  obtain ⟨w, hw⟩ := Nat.modEq_iff_dvd.1 he1
  refine ⟨c ^ ((1 : ℤ) - e), c ^ e, ?_, Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _,
    Subgroup.pow_mem _ (Subgroup.mem_zpowers c) e, ⟨s, ?_⟩, ?_⟩
  · rw [← zpow_natCast, ← zpow_add]
    simp
  · have hexp : ((1 : ℤ) - e) * ((2 ^ s : ℕ) : ℤ) = (orderOf c : ℤ) * w := by
      have h : (1 : ℤ) - e = t * w := by exact_mod_cast hw
      rw [h, hm]
      push_cast
      ring
    rw [← zpow_natCast, ← zpow_mul, hexp, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h1 : (c ^ e) ^ t = 1 := by
      rw [← pow_mul, hu, show 2 ^ s * u * t = orderOf c * u by rw [hm]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat ht (orderOf_dvd_of_pow_eq_one h1)

theorem mem_normalizer_of_normal {V : Subgroup G} (hVN : V.Normal) :
    ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) := fun g => by
  rw [Subgroup.normalizer_eq_top_iff.2 hVN]
  exact Subgroup.mem_top g

theorem isPGroup_zpowers [Finite G] {a : G} {k : ℕ} (h : a ^ 2 ^ k = 1) : IsPGroup 2 (Subgroup.zpowers a) := by
  have h1 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact IsPGroup.iff_card.2 ⟨j, by rw [Nat.card_zpowers, hj]⟩

theorem isMaxElemAbelian_of_pRank_eq [Finite G] {D S R : Subgroup G} (hD : IsMaxElemAbelian R D)
    (hDS : D ≤ S) (h : Open.pRank 2 S = Open.pRank 2 R) : IsMaxElemAbelian S D := by
  have h1 := (isMaxElemAbelian_iff_corank_zero.1 hD).2.2
  exact isMaxElemAbelian_iff_corank_zero.2 ⟨hDS, hD.2.1, by rw [h]; exact h1⟩

section Pre

variable {V : Subgroup G} (hV : IsElemAbelian 2 V) (hVN : V.Normal)

@[expose] noncomputable def starPre (M : Subgroup G) (Y : Subgroup (MulAut (IntMod V hV))) :
    Subgroup G :=
  M ⊓ Y.comap (starHom hV (mem_normalizer_of_normal hVN))

theorem mem_starPre {M : Subgroup G} {Y : Subgroup (MulAut (IntMod V hV))} {g : G} :
    g ∈ starPre hV hVN M Y ↔ g ∈ M ∧ starHom hV (mem_normalizer_of_normal hVN) g ∈ Y := Iff.rfl

variable [Finite G]

theorem isSylowTwoOf_starPre {L R : Subgroup G} (hR : IsPGroup 2 R)
    (hQsyl : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((L ⊔ R) ⊓ Subgroup.centralizer (V : Set G))) :
    IsSylowTwoOf R (starPre hV hVN (L ⊔ R) (autI hV R)) := by
  have hN := mem_normalizer_of_normal hVN
  have hRY : R ≤ starPre hV hVN (L ⊔ R) (autI hV R) := fun x hx =>
    ⟨Subgroup.mem_sup_right hx, (mem_autI_iff hV hN).2 ⟨x, hx, rfl⟩⟩
  have hYC : starPre hV hVN (L ⊔ R) (autI hV R) ⊓ Subgroup.centralizer (V : Set G) =
      (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, mem_starPre]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rw [(starHom_eq_one_iff hV hN x).2 h3]
      exact (autI hV R).one_mem
  have hYA : autI hV (starPre hV hVN (L ⊔ R) (autI hV R)) = autI hV R := by
    refine le_antisymm (fun φ hφ => ?_) (autI_mono hV hRY)
    obtain ⟨g, hg, rfl⟩ := (mem_autI_iff hV hN).1 hφ
    exact hg.2
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := fun x _ => hN x
  have hRpg : IsPGroup 2 (autI hV R) :=
    (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm).map (convI hV)
  refine isSylowTwoOf_of_isSylowTwoOf_autI hV (fun x _ => hN x) hRY hR ?_ ?_
  · rw [hYC]
    exact hQsyl
  · rw [hYA]
    exact ⟨le_rfl, hRpg, by simp⟩

include hVN in
theorem exists_mem_L_cjSub_le {L R U : Subgroup G} (hLn : L.Normal) (hR : IsPGroup 2 R)
    (hQsyl : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((L ⊔ R) ⊓ Subgroup.centralizer (V : Set G)))
    (hU2 : IsPGroup 2 U) (hUM : U ≤ L ⊔ R) (hU : autI hV U ≤ autI hV R) :
    ∃ l ∈ L, cjSub l U ≤ R := by
  have hN := mem_normalizer_of_normal hVN
  have hUY : U ≤ starPre hV hVN (L ⊔ R) (autI hV R) := fun x hx =>
    ⟨hUM hx, hU ((mem_autI_iff hV hN).2 ⟨x, hx, rfl⟩)⟩
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf (isSylowTwoOf_starPre hV hVN hR hQsyl)
    hUY hU2
  have hU' : U ≤ cjSub h⁻¹ R := by
    have := cjSub_mono (g := h⁻¹) hle
    rwa [cjSub_inv_cjSub] at this
  obtain ⟨l, hl, r, hr, hlr⟩ := Subgroup.mem_sup_of_normal_left.1 (inv_mem hh.1 : h⁻¹ ∈ L ⊔ R)
  rw [← hlr, cjSub_mul, cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hr)] at hU'
  refine ⟨l⁻¹, L.inv_mem hl, ?_⟩
  have := cjSub_mono (g := l⁻¹) hU'
  rwa [cjSub_inv_cjSub] at this

end Pre

section Claim

variable [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V) (hVN : V.Normal)

include hVN in
theorem le_I_of_offender {L R I Rj : Subgroup G} {Y : Subgroup (MulAut (IntMod V hV))}
    (hLodd : ∀ x : G, Odd (orderOf x) → x ∈ L)
    (hdec : ∀ l ∈ L, ∃ i ∈ I, ∃ o ∈ pCoreOf 2 L, l = i * o) (hR : IsPGroup 2 R)
    (hOQ : pCoreOf 2 L ≤ R ⊓ Subgroup.centralizer (V : Set G))
    (hLRN : L ⊔ R ≤ Subgroup.normalizer
      ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hQsyl : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((L ⊔ R) ⊓ Subgroup.centralizer (V : Set G)))
    (hRjSyl : IsSylowTwoOf Rj (starPre hV hVN (L ⊔ R) Y))
    (hYj : Y = autI hV (thompsonJ Rj)) (hrk : Open.pRank 2 Rj = Open.pRank 2 R)
    (hXI : thompsonJ Rj ≤ I) {D : Subgroup G} (hD : IsMaxElemAbelian R D) {g : G} (hg : g ∈ L)
    (hDg : autI hV D ≤ B1.conjAut (starHom hV (mem_normalizer_of_normal hVN) g) Y) : D ≤ I := by
  have hN := mem_normalizer_of_normal hVN
  have hgLR : g ∈ L ⊔ R := Subgroup.mem_sup_left hg
  have hQY : R ⊓ Subgroup.centralizer (V : Set G) ≤ starPre hV hVN (L ⊔ R) Y := fun q hq =>
    (mem_starPre hV hVN).2 ⟨Subgroup.mem_sup_right hq.1, by
      rw [(starHom_eq_one_iff hV hN q).2 hq.2]
      exact Y.one_mem⟩
  have hQRj : R ⊓ Subgroup.centralizer (V : Set G) ≤ Rj := by
    obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hRjSyl hQY (hR.to_le inf_le_left)
    rwa [cjSub_eq_of_mem_normalizer (hLRN hh.1)] at hle
  have hT : IsSylowTwoOf (cjSub g Rj) (cjSub g (starPre hV hVN (L ⊔ R) Y)) :=
    isSylowTwoOf_cjSub g hRjSyl
  have hDZ : D ≤ cjSub g (starPre hV hVN (L ⊔ R) Y) := by
    intro x hx
    rw [mem_cjSub]
    refine (mem_starPre hV hVN).2 ⟨(L ⊔ R).mul_mem ((L ⊔ R).mul_mem ((L ⊔ R).inv_mem hgLR)
      (Subgroup.mem_sup_right (hD.1 hx))) hgLR, ?_⟩
    have h1 : starHom hV hN x ∈ autI hV D := (mem_autI_iff hV hN).2 ⟨x, hx, rfl⟩
    have h2 := B1.mem_conjAut.1 (hDg h1)
    rw [map_mul, map_mul, map_inv]
    exact h2
  obtain ⟨z, hz, hzD⟩ := exists_conj_le_of_isSylowTwoOf hT hDZ (hR.to_le hD.1)
  have hDw : D ≤ cjSub z⁻¹ (cjSub g Rj) := by
    have := cjSub_mono (g := z⁻¹) hzD
    rwa [cjSub_inv_cjSub] at this
  have hwZ' : g⁻¹ * z⁻¹ * g ∈ starPre hV hVN (L ⊔ R) Y :=
    mem_cjSub.1 ((cjSub g (starPre hV hVN (L ⊔ R) Y)).inv_mem hz)
  have hYle : Y ≤ autI hV Rj := by
    rw [hYj]
    exact autI_mono hV (thompsonJ_le_self Rj)
  obtain ⟨t', ht', ht'eq⟩ := (mem_autI_iff hV hN).1 (hYle ((mem_starPre hV hVN).1 hwZ').2)
  have htT : g * t' * g⁻¹ ∈ cjSub g Rj := by
    rw [mem_cjSub]
    simpa [mul_assoc] using ht'
  have hstar_t : starHom hV hN (g * t' * g⁻¹) = starHom hV hN z⁻¹ := by
    have h := ht'eq
    simp only [map_mul, map_inv] at h ⊢
    rw [h]
    group
  have hcC : z⁻¹ * (g * t' * g⁻¹)⁻¹ ∈ (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hw : z⁻¹ ∈ L ⊔ R := by
        have := (L ⊔ R).mul_mem ((L ⊔ R).mul_mem hgLR ((mem_starPre hV hVN).1 hwZ').1)
          ((L ⊔ R).inv_mem hgLR)
        simpa [mul_assoc] using this
      have ht : g * t' * g⁻¹ ∈ L ⊔ R :=
        (L ⊔ R).mul_mem ((L ⊔ R).mul_mem hgLR ((mem_starPre hV hVN).1 (hRjSyl.1 ht')).1)
          ((L ⊔ R).inv_mem hgLR)
      exact (L ⊔ R).mul_mem hw ((L ⊔ R).inv_mem ht)
    · rw [← starHom_eq_one_iff hV hN, map_mul, map_inv (starHom hV hN) (g * t' * g⁻¹), hstar_t,
        mul_inv_cancel]
  obtain ⟨c, hcC', hzc⟩ : ∃ c ∈ (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G),
      z⁻¹ = c * (g * t' * g⁻¹) := ⟨_, hcC, by group⟩
  have hDc : D ≤ cjSub c (cjSub g Rj) := by
    have : cjSub z⁻¹ (cjSub g Rj) = cjSub c (cjSub g Rj) := by
      rw [hzc, cjSub_mul, cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer htT)]
    rwa [this] at hDw
  obtain ⟨a, b, hcab, haz, hbz, ⟨k, hak⟩, hbodd⟩ := exists_two_part_odd_part c
  have haC : a ∈ (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) := Subgroup.zpowers_le.2 hcC' haz
  have haQ : a ∈ R ⊓ Subgroup.centralizer (V : Set G) := by
    obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hQsyl (Subgroup.zpowers_le.2 haC)
      (isPGroup_zpowers hak)
    have h2 : Subgroup.zpowers a ≤ cjSub h⁻¹ (R ⊓ Subgroup.centralizer (V : Set G)) := by
      have := cjSub_mono (g := h⁻¹) hle
      rwa [cjSub_inv_cjSub] at this
    rw [cjSub_eq_of_mem_normalizer (hLRN ((L ⊔ R).inv_mem hh.1))] at h2
    exact h2 (Subgroup.mem_zpowers a)
  have haT : a ∈ cjSub g Rj := by
    have hQg : cjSub g (R ⊓ Subgroup.centralizer (V : Set G)) =
        R ⊓ Subgroup.centralizer (V : Set G) := cjSub_eq_of_mem_normalizer (hLRN hgLR)
    have h2 : R ⊓ Subgroup.centralizer (V : Set G) ≤ cjSub g Rj :=
      calc R ⊓ Subgroup.centralizer (V : Set G) = cjSub g (R ⊓ Subgroup.centralizer (V : Set G)) :=
            hQg.symm
        _ ≤ cjSub g Rj := cjSub_mono hQRj
    exact h2 haQ
  have hDb : D ≤ cjSub (b * g) Rj := by
    have h1 : cjSub c (cjSub g Rj) = cjSub b (cjSub g Rj) := by
      rw [hcab, cjSub_mul, cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer haT)]
    rw [h1, ← cjSub_mul] at hDc
    exact hDc
  have hDmax : IsMaxElemAbelian (cjSub (b * g) Rj) D :=
    isMaxElemAbelian_of_pRank_eq hD hDb (by rw [pRank_cjSub, hrk])
  have hDJ : D ≤ cjSub (b * g) (thompsonJ Rj) := by
    have h1 : D ≤ thompsonJ (cjSub (b * g) Rj) := le_iSup₂_of_le D hDmax le_rfl
    have h2 : cjSub (b * g) (thompsonJ Rj) = thompsonJ (cjSub (b * g) Rj) :=
      thompsonJ_map_mulEquiv (MulAut.conj (b * g)) Rj
    rwa [← h2] at h1
  obtain ⟨i, hi, o, ho, hio⟩ := hdec (b * g) (L.mul_mem (hLodd b hbodd) hg)
  have hoN : o ∈ Subgroup.normalizer (thompsonJ Rj : Set G) :=
    R_le_normalizer_thompsonJ Rj (hQRj (hOQ ho))
  have hfin : cjSub (b * g) (thompsonJ Rj) ≤ I := by
    rw [hio, cjSub_mul, cjSub_eq_of_mem_normalizer hoN]
    calc cjSub i (thompsonJ Rj) ≤ cjSub i I := cjSub_mono hXI
      _ = I := cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hi)
  exact hDJ.trans hfin

end Claim

section Assembly

variable [Finite G]

omit [Finite G] in
theorem thompsonJ_thompsonJ (S : Subgroup G) : thompsonJ (thompsonJ S) = thompsonJ S := by
  refine le_antisymm (thompsonJ_le_self _) (iSup_le fun A => iSup_le fun hA => ?_)
  have hA' : IsMaxElemAbelian (thompsonJ S) A :=
    ⟨le_iSup₂_of_le A hA le_rfl, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans (thompsonJ_le_self S))
      hBe⟩
  exact le_iSup₂_of_le A hA' le_rfl

theorem pRank_eq_of_isMaxElemAbelian {S H A : Subgroup G} (hA : IsMaxElemAbelian S A) (hAH : A ≤ H)
    (hHS : H ≤ S) : Open.pRank 2 H = Open.pRank 2 S := by
  have hA' : IsMaxElemAbelian H A :=
    ⟨hAH, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans hHS) hBe⟩
  have h1 := (isMaxElemAbelian_iff_corank_zero.1 hA).2.2
  have h2 := (isMaxElemAbelian_iff_corank_zero.1 hA').2.2
  exact Nat.pow_right_injective le_rfl (h2.symm.trans h1)

theorem pRank_thompsonJ (H : Subgroup G) : Open.pRank 2 (thompsonJ H) = Open.pRank 2 H := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian H
  exact pRank_eq_of_isMaxElemAbelian hA (le_iSup₂_of_le A hA le_rfl) (thompsonJ_le_self H)

theorem eq_bot_of_le_oTwoPhi {L : Subgroup G} (hL : L = pResidualOf 2 (⊤ : Subgroup G))
    (h : L ≤ oTwoPhi L) : L = ⊥ := by
  have h1 := exists_mul_of_le_sup_oTwoPhi (K := ⊥) bot_le (by rw [bot_sup_eq]; exact h)
  have h2 : L ≤ pCoreOf 2 L := by
    intro l hl
    obtain ⟨k, hk, o, ho, rfl⟩ := h1 l hl
    rw [Subgroup.mem_bot.1 hk, one_mul]
    exact ho
  have hLp : IsPGroup 2 L := (pCoreOf_isPGroup 2 L).to_le h2
  rw [eq_bot_iff, hL, pResidualOf_top_eq_closure_odd, Subgroup.closure_le]
  intro x hx
  have hxL : x ∈ L := by
    rw [hL]
    exact mem_pResidualOf_top_of_odd hx
  obtain ⟨k, hk⟩ := hLp ⟨x, hxL⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) := ((Nat.coprime_two_left.2 hx).pow_left k).symm
  have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [SetLike.mem_coe, Subgroup.mem_bot]
  exact orderOf_eq_one_iff.1 this

end Assembly

section Assembly2

variable [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V) (hVN : V.Normal)

theorem inf_centralizer_le_of_isSylow_starPre {L R Rj : Subgroup G}
    {Y : Subgroup (MulAut (IntMod V hV))} (hR : IsPGroup 2 R)
    (hLRN : L ⊔ R ≤ Subgroup.normalizer
      ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hRjSyl : IsSylowTwoOf Rj (starPre hV hVN (L ⊔ R) Y)) :
    R ⊓ Subgroup.centralizer (V : Set G) ≤ Rj := by
  have hN := mem_normalizer_of_normal hVN
  have hQY : R ⊓ Subgroup.centralizer (V : Set G) ≤ starPre hV hVN (L ⊔ R) Y := fun q hq =>
    (mem_starPre hV hVN).2 ⟨Subgroup.mem_sup_right hq.1, by
      rw [(starHom_eq_one_iff hV hN q).2 hq.2]
      exact Y.one_mem⟩
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hRjSyl hQY (hR.to_le inf_le_left)
  rwa [cjSub_eq_of_mem_normalizer (hLRN ((mem_starPre hV hVN).1 hh).1)] at hle

omit [Finite G] in
theorem le_iSup_preI (hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G)) {A : Subgroup G}
    {ι : Type*} [Nonempty ι] (Ai : ι → Subgroup (MulAut (IntMod V hV)))
    (hle : ∀ k, Ai k ≤ autI hV A) (heq : autI hV A = ⨆ k, Ai k) :
    A ≤ ⨆ k, preI hV A (fun x _ => hN x) (Ai k) := by
  set P := ⨆ k, preI hV A (fun x _ => hN x) (Ai k) with hP
  have hPA : P ≤ A := iSup_le fun k => preI_le hV
  have hAP : autI hV P = autI hV A := by
    rw [hP, autI_iSup hV _ (fun k x _ => hN x), heq]
    exact iSup_congr fun k => autI_preI hV (hle k)
  intro a ha
  have h1 : starHom hV hN a ∈ autI hV P := hAP ▸ (mem_autI_iff hV hN).2 ⟨a, ha, rfl⟩
  obtain ⟨p, hp, hpa⟩ := (mem_autI_iff hV hN).1 h1
  have hc : a * p⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    rw [← starHom_eq_one_iff hV hN, map_mul, map_inv, ← hpa, mul_inv_cancel]
  have hmem : a * p⁻¹ ∈ A ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.mem_inf.2 ⟨A.mul_mem ha (A.inv_mem (hPA hp)), hc⟩
  have hk : a * p⁻¹ ∈ P := by
    obtain ⟨k⟩ := ‹Nonempty ι›
    exact le_iSup (fun k => preI hV A (fun x _ => hN x) (Ai k)) k (inf_centralizer_le_preI hV hmem)
  have := P.mul_mem hk hp
  simpa using this

end Assembly2

end B2F

open B2F in
theorem B2_19 [Finite G] {V L R : Subgroup G} (hV : IsElemAbelian 2 V) (hVN : V.Normal)
    (hL : L = pResidualOf 2 (⊤ : Subgroup G)) (hR : IsPGroup 2 R) (hVR : V ≤ R)
    (hA₁ : pCoreOf 2 L ≤ R ⊓ Subgroup.centralizer (V : Set G))
    (hA₂ : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((L ⊔ R) ⊓ Subgroup.centralizer (V : Set G)))
    (hA₃ : L ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hB : L ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoPhi L)
    (hC : ∀ B, ¬ IsStrongFFStarOffender (autI hV R) B)
    (hDE : ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V hV))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI hV L, B1.conjAut g (Y i) ≤ autI hV R) ∧
      (∀ i, IsSylowTwoOf (Rs i) (starPre hV hVN (L ⊔ R) (Y i))) ∧
      (∀ i, Y i = autI hV (thompsonJ (Rs i))) ∧ (∀ i, Open.pRank 2 (Rs i) = Open.pRank 2 R) ∧
      autI hV L ≤ ⨆ i, Y i ∧ ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI hV L)) ∧
      ∀ A, IsFFStarOffender (autI hV R) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V hV))), A = ⨆ k, Ai k ∧
          ∀ k, IsFFStarOffender (autI hV R) (Ai k) ∧ ∃ j : Fin n, ∃ g ∈ autI hV L,
            Ai k ≤ B1.conjAut g (Y j) ∧ B1.conjAut g (Y j) ≤ autI hV R) :
    pCoreOf 2 L ≤ baum R ∧
      omegaOneCenterOf (thompsonJ R) =
        (omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G)) ⊔
          (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) ∧
      IsSylowTwoOf (baum R ⊓ Subgroup.centralizer (V : Set G))
        ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) ∧
      (IsSylowTwoOf (autI hV (baum R)) (autI hV L ⊔ autI hV (baum R)) →
        IsSylowTwoOf (baum R) (L ⊔ baum R)) := by
  have hN := mem_normalizer_of_normal hVN
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := fun g _ => hN g
  by_cases hLbot : L = ⊥
  · subst hLbot
    have hcen : Subgroup.centralizer (((⊥ : Subgroup G) : Subgroup G) : Set G) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_iff]
    have hS : IsPGroup 2 (baum R) := hR.to_le inf_le_left
    refine ⟨(pCoreOf_le 2 _).trans bot_le, ?_, ?_, ?_⟩
    · rw [hcen, inf_top_eq]
      exact (sup_eq_left.2 (inf_centralizer_thompsonJ_le hV hVR)).symm
    · rw [bot_sup_eq]
      exact ⟨le_rfl, hR.to_le (inf_le_left.trans inf_le_left), by simp⟩
    · intro _
      rw [bot_sup_eq]
      exact ⟨le_rfl, hS, by simp⟩
  · obtain ⟨n, Y, Rs, hconj, hsyl, hYJ, hrk, hLY, hsum, hE⟩ := hDE
    have hLn : L.Normal := by
      rw [hL]
      exact normal_pResidualOf_top
    have hLodd : ∀ x : G, Odd (orderOf x) → x ∈ L := fun x hx => by
      rw [hL]
      exact mem_pResidualOf_top_of_odd hx
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso
        subst h0
        apply hLbot
        refine eq_bot_of_le_oTwoPhi hL ?_
        have h1 : autI hV L = ⊥ := by
          have h2 := hLY
          rw [iSup_of_empty] at h2
          exact le_bot_iff.1 h2
        have h2 : L ≤ Subgroup.centralizer (V : Set G) :=
          (autI_eq_bot_iff hV (fun x _ => hN x)).1 h1
        exact fun x hx => hB (Subgroup.mem_inf.2 ⟨hx, h2 hx⟩)
      · exact h0
    obtain ⟨X, hXdef⟩ : ∃ X : Fin n → Subgroup G, ∀ i, X i = thompsonJ (Rs i) :=
      ⟨fun i => thompsonJ (Rs i), fun i => rfl⟩
    have hYX : ∀ i, Y i = autI hV (X i) := fun i => by rw [hXdef]; exact hYJ i
    have hXJ : ∀ i, X i = thompsonJ (X i) := fun i => by
      rw [hXdef]
      exact (thompsonJ_thompsonJ _).symm
    have hXrank : ∀ i, Open.pRank 2 (X i) = Open.pRank 2 R := fun i => by
      rw [hXdef, pRank_thompsonJ, hrk]
    have hLX : autI hV L ≤ ⨆ i, autI hV (X i) :=
      hLY.trans (iSup_mono fun i => (hYX i).le)
    have hsum' : ∑ i, rkIdx (fixV (autI hV (X i))) ≤ rkIdx (fixV (autI hV L)) := by
      have h : ∀ i, autI hV (X i) = Y i := fun i => (hYX i).symm
      simp only [h]
      exact hsum
    have hXR : ∀ i, X i ≤ Rs i := fun i => by
      rw [hXdef]
      exact thompsonJ_le_self _
    have hXconj : ∀ i, ∃ l ∈ L, cjSub l (X i) ≤ R := by
      intro i
      obtain ⟨g', hg', hle⟩ := hconj i
      obtain ⟨g, hgL, rfl⟩ := (mem_autI_iff hV hN).1 hg'
      have hRsY : Rs i ≤ starPre hV hVN (L ⊔ R) (Y i) := (hsyl i).1
      have hU2 : IsPGroup 2 (cjSub g (X i)) :=
        ((isSylowTwoOf_cjSub g (hsyl i)).2.1).to_le (cjSub_mono (hXR i))
      have hUM : cjSub g (X i) ≤ L ⊔ R :=
        cjSub_le (Subgroup.le_normalizer (Subgroup.mem_sup_left hgL)) fun x hx =>
          ((mem_starPre hV hVN).1 (hRsY (hXR i hx))).1
      have hU : autI hV (cjSub g (X i)) ≤ autI hV R := by
        intro φ hφ
        obtain ⟨u, hu, rfl⟩ := (mem_autI_iff hV hN).1 hφ
        apply hle
        rw [B1.mem_conjAut]
        have h1 : starHom hV hN (g⁻¹ * u * g) ∈ Y i := by
          rw [hYX i]
          exact (mem_autI_iff hV hN).2 ⟨_, mem_cjSub.1 hu, rfl⟩
        simpa only [map_mul, map_inv] using h1
      obtain ⟨l, hl, hlR⟩ := exists_mem_L_cjSub_le hV hVN hLn hR hA₂ hU2 hUM hU
      exact ⟨l * g, L.mul_mem hl hgL, by rw [cjSub_mul]; exact hlR⟩
    obtain ⟨I, hI⟩ : ∃ I : Subgroup G, I = ⨆ i, X i := ⟨_, rfl⟩
    have hXI : ∀ i, X i ≤ I := fun i => hI ▸ le_iSup X i
    have hLI₀ : autI hV L ≤ autI hV I := by
      rw [hI, autI_iSup hV X (fun i x _ => hN x)]
      exact hLX
    have hdec := L_decomp hV hN hL hB hLI₀
    have hRQ : R ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hRN)
    have hLRN : L ⊔ R ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := sup_le hA₃ hRQ
    have hfacts := alpha_facts hV hVR hRN hC
    have hJQ : ∀ D, IsMaxElemAbelian (R ⊓ Subgroup.centralizer (V : Set G)) D → D ≤ I := by
      intro D hD
      have hDR : IsMaxElemAbelian R D := hfacts.1 D hD
      have hQRs := inf_centralizer_le_of_isSylow_starPre hV hVN hR hLRN (hsyl ⟨0, hn⟩)
      have hDmax : IsMaxElemAbelian (Rs ⟨0, hn⟩) D :=
        isMaxElemAbelian_of_pRank_eq hDR (hD.1.trans hQRs) (hrk _)
      have : D ≤ X ⟨0, hn⟩ := by
        rw [hXdef]
        exact le_iSup₂_of_le D hDmax le_rfl
      exact this.trans (hXI _)
    have hJI : thompsonJ R ≤ I := by
      refine iSup_le fun A => iSup_le fun hA => ?_
      by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
      · refine hJQ A ⟨le_inf hA.1 hAC, hA.2.1, fun B hB' hBe => hA.2.2 B (hB'.trans inf_le_left) hBe⟩
      · have hAoff : IsFFOffender R V A := ⟨hA, hAC⟩
        have hAstar := offenderImages_isFFStarOffender hV hVR hRN
          (⟨A, hAoff, rfl⟩ : autI hV A ∈ offenderImages hV R)
        obtain ⟨r, Ai, hAeq, hAk⟩ := hE _ hAstar
        have hAN : A ≤ Subgroup.normalizer (V : Set G) := fun x _ => hN x
        have hnot : ¬ IsStrongFFOffender hV R A := fun h => hC _ h.2
        have hV2 : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
        have hle : ∀ k, Ai k ≤ autI hV A := fun k => hAeq ▸ le_iSup Ai k
        have hD : ∀ k, ∃ D, IsMaxElemAbelian R D ∧ preI hV A hAN (Ai k) ≤ D ∧
            autI hV D = Ai k := by
          intro k
          have hff := B2_8_ffLe hV hVR hRN hAoff hnot (hAk k).1.2.1 (hle k)
            (B1_4_1 hV2 (hAk k).1)
          obtain ⟨hDmax, hDeq⟩ := (offender_core hV hVR hRN hA (hle k)).2 hff.2.2.2
          exact ⟨_, hDmax, le_sup_left, hDeq⟩
        have hDI : ∀ k, ∀ D, IsMaxElemAbelian R D → autI hV D = Ai k → D ≤ I := by
          intro k D hD hDk
          obtain ⟨-, j, g', hg', hAij, -⟩ := hAk k
          obtain ⟨l, hl, rfl⟩ := (mem_autI_iff hV hN).1 hg'
          have hXIj : thompsonJ (Rs j) ≤ I := by
            rw [← hXdef j]
            exact hXI j
          exact le_I_of_offender hV hVN hLodd hdec hR hA₁ hLRN hA₂ (hsyl j) (hYJ j) (hrk j)
            hXIj hD hl (hDk ▸ hAij)
        have hne : Nonempty (Fin r) := by
          by_contra hne
          rw [not_nonempty_iff] at hne
          apply hAstar.2.1
          rw [hAeq, iSup_of_empty]
        refine (le_iSup_preI hV hN Ai hle hAeq).trans (iSup_le fun k => ?_)
        obtain ⟨D, hDmax, hBD, hDeq⟩ := hD k
        exact hBD.trans (hDI k D hDmax hDeq)
    obtain ⟨h1, h2, h3⟩ := B2_18 hV hVN hL hR hVR hA₁ hA₃ hB hC
      ⟨n, X, hXconj, hXJ, hXrank, hLX, hsum', by rw [← hI]; exact hJI⟩
    obtain ⟨h3a, h3b⟩ := h3 hA₂
    exact ⟨h1, h2, h3a, h3b⟩

end CFSG.Quasithin
