module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveJ4
public import CFSG.Quasithin.Vol2.Ch12Sec5KGJ4Lat

public section

namespace CFSG.Quasithin.H13.J4Cover

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam
open CFSG.QuasithinUnique

private theorem exists_order_five_map
    (hF : J4Facts) {X : Subgroup J} (hXM : X ≤ M3) (h5 : 5 ∣ Nat.card X) :
    ∃ g : ↥M3, (g : J) ∈ X ∧ orderOf g = 5 ∧ V0.normalizerMonoidHom g = 1 ∧
      orderOf (CFSG.Quasithin.J4Fam.rho3 hF g) = 5 ∧
      CFSG.Quasithin.J4Fam.rho3 hF g ∈ alternatingGroup (Fin 5) := by
  have hM := hF.mat
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨x, hxX⟩, hx5⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 h5
  have hxo : orderOf x = 5 := by rw [← Subgroup.orderOf_mk x hxX]; exact hx5
  let g : ↥M3 := ⟨x, hXM hxX⟩
  have hgo : orderOf g = 5 := by rw [Subgroup.orderOf_mk, hxo]
  have hα : V0.normalizerMonoidHom g = 1 := by
    have h1 := orderOf_map_dvd V0.normalizerMonoidHom g
    rw [hgo] at h1
    have h2 := orderOf_dvd_natCard (V0.normalizerMonoidHom g)
    rw [CFSG.Quasithin.J4Rad.card_mulAut_V0 hM] at h2
    have h3 : orderOf (V0.normalizerMonoidHom g) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
      · exact h
      · rw [h] at h2
        norm_num at h2
    exact orderOf_eq_one_iff.mp h3
  have hρg : orderOf (CFSG.Quasithin.J4Fam.rho3 hF g) = 5 := by
    have h1 := orderOf_map_dvd (CFSG.Quasithin.J4Fam.rho3 hF) g
    rw [hgo] at h1
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
    · exfalso
      have hmem : g ∈ ((CFSG.Quasithin.J4Fam.rho3 hF).ker ⊓
          V0.normalizerMonoidHom.ker : Subgroup ↥M3) :=
        ⟨MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h), MonoidHom.mem_ker.mpr hα⟩
      obtain ⟨k, hk⟩ := CFSG.Quasithin.J4Fam.isPGroup_ker_rho3_alpha3 hF ⟨g, hmem⟩
      have h2 : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hgo] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
        (Nat.prime_five.dvd_of_dvd_pow h3)
      omega
    · exact h
  have hρgA : CFSG.Quasithin.J4Fam.rho3 hF g ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h0 : CFSG.Quasithin.J4Fam.rho3 hF g ^ 5 = 1 := by
      have := pow_orderOf_eq_one (CFSG.Quasithin.J4Fam.rho3 hF g)
      rwa [hρg] at this
    have h1 : Equiv.Perm.sign (CFSG.Quasithin.J4Fam.rho3 hF g) ^ 5 = 1 := by
      rw [← map_pow, h0, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (CFSG.Quasithin.J4Fam.rho3 hF g)) with h | h
    · exact h
    · rw [h] at h1
      exact absurd h1 (by decide)
  exact ⟨g, hxX, hgo, hα, hρg, hρgA⟩

private theorem alt5_le_map_rho
    (hF : J4Facts) {X : Subgroup J} (hP : P0 ≤ X) (hXM : X ≤ M3)
    (h5 : 5 ∣ Nat.card X) :
    alternatingGroup (Fin 5) ≤ (X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) := by
  have hM := hF.mat
  have hPM3 : P0 ≤ M3 := hP.trans hXM
  obtain ⟨g, hgX, -, -, hρg, hρgA⟩ := exists_order_five_map hF hXM h5
  have hA5I : alternatingGroup (Fin 5) ≤ (CFSG.Quasithin.J4Fam.rho3 hF).range := by
    have h1 := CFSG.Quasithin.H13.FiveNorm.J4F.alt5_le_of_sixty_dvd
      (CFSG.Quasithin.J4Fam.sixty_dvd_card_rho3 hF)
    exact h1.trans (by
      rw [MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _)
  have hP0M : IsSylowTwoOf (P0.subgroupOf M3) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf
      (CFSG.Quasithin.A4.isSylowTwoOf_mono isSylowTwoOf_P0 hPM3 le_top)
  have hPbI : IsSylowTwoOf
      ((P0.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF))
      (CFSG.Quasithin.J4Fam.rho3 hF).range := by
    have h1 := CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hP0M
      (CFSG.Quasithin.J4Fam.rho3 hF).rangeRestrict
      (CFSG.Quasithin.J4Fam.rho3 hF).rangeRestrict_surjective
    have h2 : (P0.subgroupOf M3).map
        (CFSG.Quasithin.J4Fam.rho3 hF).rangeRestrict =
        ((P0.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF)).subgroupOf
          (CFSG.Quasithin.J4Fam.rho3 hF).range := by
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨m, hm, hmx⟩
        exact ⟨m, hm, congrArg Subtype.val hmx⟩
      · rintro ⟨m, hm, hmx⟩
        exact ⟨m, hm, Subtype.ext hmx⟩
    rw [h2] at h1
    refine ⟨Subgroup.map_le_range _ _, hP0M.2.1.map _, ?_⟩
    have h3 : ((((P0.subgroupOf M3).map
        (CFSG.Quasithin.J4Fam.rho3 hF)).subgroupOf
          (CFSG.Quasithin.J4Fam.rho3 hF).range).subgroupOf ⊤).index =
        (((P0.subgroupOf M3).map
          (CFSG.Quasithin.J4Fam.rho3 hF)).subgroupOf
            (CFSG.Quasithin.J4Fam.rho3 hF).range).index :=
      Subgroup.relIndex_top_right _
    have h4 := h1.2.2
    rwa [h3] at h4
  have hA5n : (CFSG.Quasithin.J4Fam.rho3 hF).range ≤
      Subgroup.normalizer ((alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) :
        Set (Equiv.Perm (Fin 5))) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hPbA : Nat.card ↥((P0.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
      alternatingGroup (Fin 5)) = 4 := by
    have h1 := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hPbI hA5I hA5n
    have h2 := CFSG.Quasithin.H13.FiveNorm.card_eq_of_isSylowTwoOf_top
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf h1)
      (k := 2) (m := 15)
      (by rw [CFSG.Quasithin.H13.FiveNorm.J4F.card_alt5]; norm_num) (by decide)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h2
  have hPbR : (P0.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
      alternatingGroup (Fin 5) ≤
      (X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
        alternatingGroup (Fin 5) :=
    inf_le_inf_right _ (Subgroup.map_mono (Subgroup.subgroupOf_mono M3 hP))
  have hgR : CFSG.Quasithin.J4Fam.rho3 hF g ∈
      (X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
        alternatingGroup (Fin 5) :=
    ⟨⟨g, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩, hρgA⟩
  set n := Nat.card ↥((X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
    alternatingGroup (Fin 5)) with hn
  have h4 : 4 ∣ n := by
    have := Subgroup.card_dvd_of_le hPbR
    rwa [hPbA] at this
  have h5' : 5 ∣ n := by
    have := Subgroup.orderOf_dvd_natCard _ hgR
    rwa [hρg] at this
  have h60 : n ∣ 60 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_right : (X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
        alternatingGroup (Fin 5) ≤ alternatingGroup (Fin 5))
    rwa [CFSG.Quasithin.H13.FiveNorm.J4F.card_alt5] at this
  obtain ⟨c, hc⟩ : ∃ c, n = 20 * c :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h5'
  have hc3 : c ∣ 3 := by
    have h : 20 * c ∣ 20 * 3 := by
      rw [show (20 : ℕ) * 3 = 60 by norm_num]
      rwa [hc] at h60
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (Nat.dvd_prime Nat.prime_three).mp hc3 with hc1 | hc3'
  · exfalso
    have hn20 : n = 20 := by rw [hc, hc1, mul_one]
    have hidx : (((X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
        alternatingGroup (Fin 5)).subgroupOf (alternatingGroup (Fin 5))).index = 3 := by
      have h := Subgroup.card_mul_index
        (((X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
          alternatingGroup (Fin 5)).subgroupOf (alternatingGroup (Fin 5)))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
        ← hn, CFSG.Quasithin.H13.FiveNorm.J4F.card_alt5, hn20] at h
      omega
    exact CFSG.Quasithin.H13.FiveNorm.J4F.index_ne_three_of_isSimpleGroup
      (by rw [CFSG.Quasithin.H13.FiveNorm.J4F.card_alt5]; norm_num) _ hidx
  · have hn60 : n = 60 := by rw [hc, hc3']
    have hidx1 : (((X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
        alternatingGroup (Fin 5)).subgroupOf (alternatingGroup (Fin 5))).index = 1 := by
      have h := Subgroup.card_mul_index
        (((X.subgroupOf M3).map (CFSG.Quasithin.J4Fam.rho3 hF) ⊓
          alternatingGroup (Fin 5)).subgroupOf (alternatingGroup (Fin 5)))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
        ← hn, CFSG.Quasithin.H13.FiveNorm.J4F.card_alt5, hn60] at h
      omega
    rw [Subgroup.inf_subgroupOf_right] at hidx1
    exact Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hidx1)

private theorem three_dvd_card_ker
    (hF : J4Facts) {X : Subgroup J} (hP : P0 ≤ X) (hXM : X ≤ M3)
    (h5 : 5 ∣ Nat.card X) :
    3 ∣ Nat.card ↥((V0.normalizerMonoidHom.comp (X.subgroupOf M3).subtype).ker) := by
  have hM := hF.mat
  obtain ⟨g, hgX, -, hαg, hρg, hρgA⟩ := exists_order_five_map hF hXM h5
  have hA5le := alt5_le_map_rho hF hP hXM h5
  let Xm : Subgroup ↥M3 := X.subgroupOf M3
  let α : ↥M3 →* MulAut ↥V0 := V0.normalizerMonoidHom
  let ρ : ↥M3 →* Equiv.Perm (Fin 5) := CFSG.Quasithin.J4Fam.rho3 hF
  let fX : ↥Xm →* MulAut ↥V0 := α.comp Xm.subtype
  let ρX : ↥Xm →* Equiv.Perm (Fin 5) := ρ.comp Xm.subtype
  let K : Subgroup ↥Xm := fX.ker
  let R : Subgroup (Equiv.Perm (Fin 5)) := K.map ρX
  let Alt : Subgroup (Equiv.Perm (Fin 5)) := alternatingGroup (Fin 5)
  have hA5map : Alt ≤ Xm.map ρ := hA5le
  have hKnormal : K.Normal := MonoidHom.normal_ker fX
  have hRnorm : ∀ n ∈ Xm.map ρ, ∀ r ∈ R, n * r * n⁻¹ ∈ R := by
    intro n hn r hr
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨k, hk, rfl⟩ := hr
    let y' : ↥Xm := ⟨y, hy⟩
    refine ⟨y' * k * y'⁻¹, hKnormal.conj_mem k hk y', ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  let S : Subgroup (Equiv.Perm (Fin 5)) := R ⊓ Alt
  have hSn : (S.subgroupOf Alt).Normal := by
    refine ⟨fun x hx a => ?_⟩
    have hx' : (x : Equiv.Perm (Fin 5)) ∈ S := Subgroup.mem_subgroupOf.mp hx
    have hconj : (a : Equiv.Perm (Fin 5)) * (x : Equiv.Perm (Fin 5)) *
        (a : Equiv.Perm (Fin 5))⁻¹ ∈ R :=
      hRnorm _ (hA5map a.2) _ hx'.1
    exact Subgroup.mem_subgroupOf.mpr
      ⟨hconj, Alt.mul_mem (Alt.mul_mem a.2 hx'.2) (Alt.inv_mem a.2)⟩
  have hgK : (⟨g, Subgroup.mem_subgroupOf.mpr hgX⟩ : ↥Xm) ∈ K := by
    show fX ⟨g, Subgroup.mem_subgroupOf.mpr hgX⟩ = 1
    simpa [fX, α] using hαg
  have hgR : ρ g ∈ R := ⟨⟨g, Subgroup.mem_subgroupOf.mpr hgX⟩, hgK, rfl⟩
  have hgS : ρ g ∈ S := ⟨hgR, hρgA⟩
  have hne : S.subgroupOf Alt ≠ ⊥ := by
    intro hbot
    have hmem : (⟨ρ g, hρgA⟩ : ↥Alt) ∈ S.subgroupOf Alt :=
      Subgroup.mem_subgroupOf.mpr hgS
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : ρ g = 1 := congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hρg
    omega
  haveI : IsSimpleGroup ↥Alt := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf Alt) with h | h
  · exact absurd h hne
  · have hA5S : Alt ≤ S := Subgroup.subgroupOf_eq_top.mp h
    have h3R : 3 ∣ Nat.card ↥R := by
      have h60 : 60 ∣ Nat.card ↥R := by
        rw [← CFSG.Quasithin.H13.FiveNorm.J4F.card_alt5]
        exact Subgroup.card_dvd_of_le (hA5S.trans inf_le_left)
      exact (by norm_num : 3 ∣ 60).trans h60
    exact h3R.trans (Subgroup.card_map_dvd K ρX)

private theorem card_map_P0_eq_eight
    (hF : J4Facts) (hPM3 : P0 ≤ M3) :
    Nat.card ↥((P0.subgroupOf M3).map V0.normalizerMonoidHom) = 8 := by
  have hM := hF.mat
  let Pm : Subgroup ↥M3 := P0.subgroupOf M3
  let α : ↥M3 →* MulAut ↥V0 := V0.normalizerMonoidHom
  let f : ↥Pm →* MulAut ↥V0 := α.comp Pm.subtype
  have hPm2 : IsPGroup 2 Pm :=
    CFSG.Quasithin.A4.isPGroup_subgroupOf_of_le hPM3 isSylowTwoOf_P0.2.1
  have hf2 : IsPGroup 2 ↥f.ker := hPm2.to_subgroup f.ker
  obtain ⟨n, hn⟩ := hf2.exists_card_eq
  have hker_le : (f.ker).map Pm.subtype ≤ CFSG.Quasithin.J4Fam.Dm := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : Pm.subtype y ∈ α.ker := MonoidHom.mem_ker.mpr hy
    have hker : α.ker = CFSG.Quasithin.J4Fam.Dm := V0.normalizerMonoidHom_ker
    rwa [hker] at hy'
  have hndvd : 2 ^ n ∣ 3932160 := by
    rw [← hn]
    have h1 : Nat.card ↥f.ker ∣ Nat.card ↥(CFSG.Quasithin.J4Fam.Dm) := by
      rw [← Subgroup.card_map_of_injective (f := Pm.subtype) Pm.subtype_injective]
      exact Subgroup.card_dvd_of_le hker_le
    rwa [CFSG.Quasithin.J4Fam.card_Dm hF] at h1
  have hn18 : n ≤ 18 := by
    have hcop : Nat.Coprime (2 ^ n) 15 :=
      (Nat.coprime_two_left.mpr (by decide : Odd 15)).pow_left n
    have h15 : 2 ^ n ∣ 2 ^ 18 := by
      apply hcop.dvd_of_dvd_mul_right
      rw [show (3932160 : ℕ) = 2 ^ 18 * 15 by norm_num] at hndvd
      exact hndvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h15
  have hrange2 : IsPGroup 2 ↥(Pm.map α) := hPm2.map α
  obtain ⟨k, hk⟩ := hrange2.exists_card_eq
  have hrange_eq : f.range = Pm.map α := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hPmcard : Nat.card ↥Pm = 2 ^ 21 := by
    change Nat.card ↥(P0.subgroupOf M3) = 2 ^ 21
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM3).toEquiv,
      CFSG.Sporadic.J4.QT.card_P0 hM hF]
  have hk' : Nat.card ↥f.range = 2 ^ k := by rw [hrange_eq, hk]
  have hiso := Subgroup.card_ker_mul_card_range f
  rw [hPmcard, hn, hk', ← pow_add] at hiso
  have hnk : n + k = 21 := Nat.pow_right_injective (le_refl 2) hiso
  have hk_dvd : 2 ^ k ∣ 168 := by
    have h1 : Nat.card ↥(Pm.map α) ∣ Nat.card (MulAut ↥V0) :=
      Subgroup.card_subgroup_dvd_card (Pm.map α)
    rw [hk, CFSG.Quasithin.J4Rad.card_mulAut_V0 hM] at h1
    exact h1
  have hcop21 : Nat.Coprime (2 ^ k) 21 :=
    (Nat.coprime_two_left.mpr (by decide : Odd 21)).pow_left k
  have hk8 : 2 ^ k ∣ 8 := by
    apply hcop21.dvd_of_dvd_mul_right
    rw [show (168 : ℕ) = 8 * 21 by norm_num] at hk_dvd
    exact hk_dvd
  have hk3 : k ≤ 3 := by
    have h : 2 ^ k ∣ 2 ^ 3 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hk8
      exact hk8
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h
  have hk_eq : k = 3 := by omega
  rw [hk, hk_eq]
  norm_num

private theorem map_eq_map_P0
    (hF : J4Facts) {X : Subgroup J} (hP : P0 ≤ X) (hXM : X ≤ M3)
    (h5 : 5 ∣ Nat.card X) (h9 : ¬ 9 ∣ Nat.card X) :
    (X.subgroupOf M3).map V0.normalizerMonoidHom =
      (P0.subgroupOf M3).map V0.normalizerMonoidHom := by
  have hM := hF.mat
  have hPM3 : P0 ≤ M3 := hP.trans hXM
  let Xm : Subgroup ↥M3 := X.subgroupOf M3
  let Pm : Subgroup ↥M3 := P0.subgroupOf M3
  let α : ↥M3 →* MulAut ↥V0 := V0.normalizerMonoidHom
  have hle : Pm.map α ≤ Xm.map α :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M3 hP)
  have hcardP : Nat.card ↥(Pm.map α) = 8 := card_map_P0_eq_eight hF hPM3
  have h8 : 8 ∣ Nat.card ↥(Xm.map α) := by
    rw [← hcardP]
    exact Subgroup.card_dvd_of_le hle
  have h168 : Nat.card ↥(Xm.map α) ∣ 168 := by
    have h1 := Subgroup.card_subgroup_dvd_card (Xm.map α)
    rwa [CFSG.Quasithin.J4Rad.card_mulAut_V0 hM] at h1
  have h3 : ¬ 3 ∣ Nat.card ↥(Xm.map α) := by
    let fX : ↥Xm →* MulAut ↥V0 := α.comp Xm.subtype
    have h3K : 3 ∣ Nat.card ↥fX.ker := three_dvd_card_ker hF hP hXM h5
    have hrange : fX.range = Xm.map α := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    have hcard := Subgroup.card_ker_mul_card_range fX
    rw [hrange] at hcard
    have hXmcard : Nat.card ↥Xm = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
    intro h3map
    apply h9
    rw [← hXmcard, ← hcard]
    exact mul_dvd_mul h3K h3map
  have h56 : Nat.card ↥(Xm.map α) ≠ 56 := by
    intro h56
    haveI : IsSimpleGroup (MulAut ↥V0) :=
      CFSG.Quasithin.J4Fam.isSimpleGroup_mulAut_of_subgroup_eight V0
        (CFSG.Quasithin.J4Rad.V0_comm hM) (CFSG.Quasithin.J4Rad.V0_sq hM)
        (CFSG.Quasithin.J4Rad.card_V0 hM)
    have hidx : (Xm.map α).index = 3 := by
      have h := Subgroup.card_mul_index (Xm.map α)
      rw [CFSG.Quasithin.J4Rad.card_mulAut_V0 hM, h56] at h
      omega
    exact CFSG.Quasithin.H13.FiveNorm.J4F.index_ne_three_of_isSimpleGroup
      (by rw [CFSG.Quasithin.J4Rad.card_mulAut_V0 hM]; norm_num) (Xm.map α) hidx
  have hcardX : Nat.card ↥(Xm.map α) = 8 := by
    obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥(Xm.map α) = 8 * k := h8
    have hk21 : k ∣ 21 := by
      have h : 8 * k ∣ 8 * 21 := by
        rw [hk, show (168 : ℕ) = 8 * 21 by norm_num] at h168
        exact h168
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    have hk3 : ¬ 3 ∣ k := by
      intro h3k
      apply h3
      rw [hk]
      exact dvd_mul_of_dvd_right h3k 8
    have hk7 : k ≠ 7 := by
      intro hk7
      apply h56
      rw [hk, hk7]
    have hk1 : k = 1 := by
      have hmem : k ∈ (Nat.divisors 21).filter (fun k => ¬ 3 ∣ k ∧ k ≠ 7) := by
        rw [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨hk21, by norm_num⟩, hk3, hk7⟩
      have hset : (Nat.divisors 21).filter (fun k => ¬ 3 ∣ k ∧ k ≠ 7) = {1} := by
        decide
      rw [hset] at hmem
      simpa using hmem
    rw [hk, hk1]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hcardX])).symm

private theorem le_centralizer_of_le_M3
    (hF : J4Facts) {X : Subgroup J} (hP : P0 ≤ X) (hXM : X ≤ M3)
    (h5 : 5 ∣ Nat.card X) (h9 : ¬ 9 ∣ Nat.card X) :
    X ≤ Subgroup.centralizer ({z0} : Set J) := by
  have hM := hF.mat
  let Xm : Subgroup ↥M3 := X.subgroupOf M3
  let α : ↥M3 →* MulAut ↥V0 := V0.normalizerMonoidHom
  have hmap : Xm.map α = (P0.subgroupOf M3).map α := map_eq_map_P0 hF hP hXM h5 h9
  intro x hx
  have hxmap : α ⟨x, hXM hx⟩ ∈ Xm.map α :=
    Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.mpr hx)
  rw [hmap] at hxmap
  obtain ⟨p, hp, hpx⟩ := hxmap
  have hp0 : (p : J) ∈ P0 := Subgroup.mem_subgroupOf.mp hp
  have hz0V0 : z0 ∈ V0 := Subgroup.subset_closure (by
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inr rfl))
  have hconj : x * z0 * x⁻¹ = z0 := by
    have h1 : α ⟨x, hXM hx⟩ ⟨z0, hz0V0⟩ = α p ⟨z0, hz0V0⟩ := by rw [hpx]
    have h2 := congrArg (fun v : ↥V0 => (v : J)) h1
    rw [V0.normalizerMonoidHom_apply_apply_coe,
      V0.normalizerMonoidHom_apply_apply_coe] at h2
    calc x * z0 * x⁻¹ = ((⟨x, hXM hx⟩ : ↥M3) : J) * z0 * ((⟨x, hXM hx⟩ : ↥M3) : J)⁻¹ :=
        rfl
      _ = (p : J) * z0 * (p : J)⁻¹ := h2
      _ = z0 := CFSG.Quasithin.J4Ov.P0_conj_z0 hM p hp0
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc x * z0 = (x * z0 * x⁻¹) * x := by group
    _ = z0 * x := by rw [hconj]

theorem le_centralizer_of_five
    {X : Subgroup J} (hP : P0 ≤ X) (h5 : 5 ∣ Nat.card X) (h9 : ¬ 9 ∣ Nat.card X) :
    X ≤ Subgroup.centralizer ({z0} : Set J) := by
  have hF : J4Facts := j4Facts
  rcases CFSG.Quasithin.H13.S125KG.J4.over_P0 hP with htop | hHj | hM3 | hM2
  · exfalso
    apply h9
    rw [htop, Subgroup.card_top, card_J hF]
    norm_num
  · rcases CFSG.Quasithin.H13.KGT3J4.card_of_le_Hj hP hHj with htop | ⟨j, hj, hcard⟩
    · exfalso
      apply h9
      rw [htop, card_Hj hF]
      norm_num
    · exfalso
      have h5' : 5 ∣ CFSG.Quasithin.A312M24.memIdx[j]! * 2 ^ 10 := by
        have h := h5
        rw [hcard] at h
        refine Nat.Coprime.dvd_of_dvd_mul_right (by decide : Nat.Coprime 5 (2 ^ 11)) ?_
        rw [show (2 : ℕ) ^ 21 = 2 ^ 10 * 2 ^ 11 by norm_num, ← mul_assoc] at h
        exact h
      rcases CFSG.Quasithin.A312M24.idx_5 j hj h5' with rfl | rfl
      · apply h9
        rw [hcard]
        norm_num [CFSG.Quasithin.A312M24.memIdx]
      · apply h9
        rw [hcard]
        norm_num [CFSG.Quasithin.A312M24.memIdx]
  · exact le_centralizer_of_le_M3 hF hP hM3 h5 h9
  · rw [hM2]

end CFSG.Quasithin.H13.J4Cover
