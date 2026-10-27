module

public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Quasithin.Vol2.Ch11SecE3LieL2Up
public import CFSG.Quasithin.Background.HL3NineModel
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Vol2.Ch8Sec2L825D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

section L825F

theorem not_isSz_of_even_82 {X : Type} [Group X] {k : ℕ} (hk : Even k) : ¬ IsSz k X := by
  rintro ⟨-, a, -, K, _, _, hf, -⟩
  obtain ⟨j, hj⟩ := hk
  omega

theorem eq_one_of_odd_cent_sylow_82 {X : Type} [Group X] [Finite X] {k : ℕ} (hk : 2 ≤ k)
    (hX : IsPSL 2 2 k X) {S : Subgroup X} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) {x s : X}
    (hxN : x ∈ Subgroup.normalizer (S : Set X)) (hxo : Odd (orderOf x)) (hs : s ∈ S)
    (hs1 : s ≠ 1) (hxs : x * s * x⁻¹ = s) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField X 2 2 k hX
  set S' := S.map e.toMonoidHom with hS'
  have hS'p : IsPGroup 2 ↥S' := hS.2.1.map e.toMonoidHom
  have hS'i : ¬ 2 ∣ S'.index := by
    have h1 : S'.index = S.index := Subgroup.index_map_equiv S e
    rw [h1, ← Subgroup.relIndex_top_right]
    exact hS.2.2
  obtain ⟨D, -, -, -, hUDN, hreg⟩ :=
    CFSG.Walter.psl2_even_normalizer_sylow_two hk (hS'p.toSylow hS'i)
  obtain ⟨hUel, -⟩ := CFSG.Walter.psl2_even_sylow_two hk (hS'p.toSylow hS'i)
  have hUDN' : S' ⊔ D = Subgroup.normalizer (S' : Set _) := hUDN
  have hDN : D ≤ Subgroup.normalizer (S' : Set _) := hUDN' ▸ le_sup_right
  have hcomm : IsMulCommutative ↥S' := hUel.toIsMulCommutative
  have hNS : (Subgroup.normalizer (S : Set X)).map e.toMonoidHom =
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup _) : Set _) :=
    Subgroup.map_equiv_normalizer_eq S e
  have hx' : e x ∈ ((S' ⊔ D : Subgroup _) : Set _) := by
    rw [hUDN', ← hNS]
    exact ⟨x, hxN, rfl⟩
  rw [Subgroup.coe_mul_of_right_le_normalizer_left S' D hDN] at hx'
  obtain ⟨u, hu, d, hd, hud⟩ := Set.mem_mul.mp hx'
  have hs' : e s ∈ S' := ⟨s, hs, rfl⟩
  have hs'1 : e s ≠ 1 := fun h => hs1 (e.injective (h.trans (map_one e).symm))
  have hxs' : e x * e s * (e x)⁻¹ = e s := by rw [← map_mul, ← map_inv, ← map_mul, hxs]
  rw [← hud] at hxs'
  have hus : u⁻¹ * e s * u = e s := by
    have h1 : (⟨u, hu⟩ : ↥S') * ⟨e s, hs'⟩ = ⟨e s, hs'⟩ * ⟨u, hu⟩ := hcomm.is_comm.comm _ _
    have h2 : u * e s = e s * u := congrArg Subtype.val h1
    rw [mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
  have hds : d * e s * d⁻¹ = e s := by
    calc d * e s * d⁻¹ = u⁻¹ * ((u * d) * e s * (u * d)⁻¹) * u := by group
      _ = u⁻¹ * e s * u := by rw [hxs']
      _ = e s := hus
  obtain ⟨d₀, -, huniq⟩ := hreg (e s) hs' hs'1 (e s) hs' hs'1
  have hd1 : (⟨d, hd⟩ : ↥D) = 1 := by
    rw [huniq ⟨d, hd⟩ hds, huniq 1 (by simp)]
  have hd1' : d = 1 := congrArg Subtype.val hd1
  rw [hd1', mul_one] at hud
  obtain ⟨m, hm⟩ := hS'p ⟨u, hu⟩
  have hm' : (e x) ^ 2 ^ m = 1 := by
    rw [← hud]
    exact congrArg Subtype.val hm
  have hxo' : Odd (orderOf (e x)) := by
    have h := orderOf_injective e.toMonoidHom e.injective x
    change orderOf (e x) = orderOf x at h
    rwa [h]
  have hex : e x = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hm')
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rwa [h0, pow_zero, orderOf_eq_one_iff] at hj
    · rw [hj] at hxo'
      exact absurd ((Nat.even_pow' hpos.ne').mpr even_two) (Nat.not_even_iff_odd.mpr hxo')
  exact e.injective (hex.trans (map_one e).symm)

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_cent_cartan_82 {T M I V X : Subgroup G} {k : ℕ} (hk : 2 ≤ k)
    (hI : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I))
    (hSyl : QuasithinUnique.IsSylowTwoOf (T ⊓ I) I)
    (hB : E2.star (M ⊓ I) I (M ⊓ I) =
      Subgroup.normalizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (hVT : E2.star (M ⊓ I) I V ≤ E2.star (M ⊓ I) I (T ⊓ I))
    (hV1 : E2.star (M ⊓ I) I V ≠ ⊥)
    (hXMI : X ≤ M ⊓ I) (hXK : X ⊓ kerIn (M ⊓ I) I = ⊥) (hXodd : Odd (Nat.card ↥X))
    {x : G} (hx : x ∈ X) (hxV : x ∈ Subgroup.centralizer (V : Set G)) : x = 1 := by
  set π := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hπ
  have hxI : x ∈ I := (hXMI hx).2
  have hxN : π ⟨x, hxI⟩ ∈ Subgroup.normalizer
      (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) := by
    rw [← hB]
    exact ⟨⟨x, hxI⟩, hXMI hx, rfl⟩
  have hxo : Odd (orderOf (π ⟨x, hxI⟩)) := by
    refine Odd.of_dvd_nat hXodd ((orderOf_map_dvd π _).trans ?_)
    have h1 : orderOf (⟨x, hxI⟩ : ↥I) = orderOf (⟨x, hx⟩ : ↥X) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    rw [h1]
    exact orderOf_dvd_natCard _
  obtain ⟨⟨s, hsV⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨v, hvV, rfl⟩ := hsV
  have hxs : π ⟨x, hxI⟩ * π v * (π ⟨x, hxI⟩)⁻¹ = π v := by
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    have hv : (v : G) ∈ V := hvV
    show x * (v : G) * x⁻¹ = v
    rw [(Subgroup.mem_centralizer_iff.mp hxV v hv).symm, mul_inv_cancel_right]
  have h1 := eq_one_of_odd_cent_sylow_82 hk hI (isSylowTwoOf_star_82 hSyl) hxN hxo
    (hVT ⟨v, hvV, rfl⟩) hs1' hxs
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have : x ∈ X ⊓ kerIn (M ⊓ I) I := ⟨hx, h1⟩
  rw [hXK, Subgroup.mem_bot] at this
  exact this

theorem generalizedFitting_eq_top_82 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] :
    CFSG.generalizedFitting Y = ⊤ := by
  have hN : (CFSG.generalizedFitting Y).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Y)).2
  rcases hN.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    have h1 := CFSG.centralizer_generalizedFitting_le Y
    rw [h] at h1
    have hyc : y ∈ Subgroup.centralizer ((⊥ : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hm
      rw [hm, one_mul, mul_one]
    exact hy (Subgroup.mem_bot.mp (h1 hyc))
  · exact h

theorem nParam_eq_of_isPSL_82 {Y : Type} [Group Y] [Finite Y] {k : ℕ} (hY : IsPSL 2 2 k Y)
    {S : Subgroup Y} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    E1.nParam (⊤ : Subgroup Y) = k := by
  have hs : IsSimpleGroup Y := (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 2 k hY).2
  have hF : CFSG.generalizedFitting Y = ⊤ := generalizedFitting_eq_top_82
  have hL : IsPSL 2 2 k ↥(CFSG.generalizedFitting Y) := by
    rw [hF]
    exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv Subgroup.topEquiv hY
  have hFs : IsSimpleGroup ↥(CFSG.generalizedFitting Y) := by
    rw [hF]
    exact Subgroup.topEquiv.isSimpleGroup
  have hT : quasithinIsSylowTwo S := by
    refine ⟨hS.2.1, ?_⟩
    have h2 := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h2
  exact Vol2.Ch11.SecE3.nParam_eq_of_isPSL22 hL hFs hT (by rw [hF]; exact top_sup_eq _)

theorem card_of_binaryNineTensor_82 {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {n : ℕ}
    (hn : 1 ≤ n) (hL : BinaryNineTensor L ⊤ ⊥ n) : Nat.card W = 2 ^ (9 * n) := by
  obtain ⟨K, _, _, _, hK, hreal⟩ := hL
  have hK' : Nat.card K = (2 ^ n) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨e, -⟩ := CFSG.Quasithin.H.L3Nine.exists_model hK' hreal
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Quasithin.H.L3Nine.card_HMod hn hK'

end L825F

end CFSG.Quasithin.H13
