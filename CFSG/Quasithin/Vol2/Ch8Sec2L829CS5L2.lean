module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Sub
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5L2T
public import CFSG.LargeExtraspecial.Bender
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups

theorem rankOneSyl_top_of_isPSL_two_cs5 {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (hG : IsPSL 2 2 n G) {S : Subgroup G} (hS : IsSylowTwoOf S ⊤) :
    RankOneSyl (⊤ : Subgroup G) S (2 ^ n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField G 2 2 n hG
  have hfin : Finite PSL(2, GaloisField 2 n) := Finite.of_equiv G e.toEquiv
  have hB : fusionBenderBorel G (2 ^ n) 1 :=
    (bender_psl2_borel_full n hn).map_mulEquiv e.symm
  obtain ⟨P, hPS⟩ := exists_sylow_of_isSylowTwoOf_top_cs5 hS
  obtain ⟨hSE, -, hzexp, hZcard, hQcard⟩ := hB P
  subst hPS
  have hQcard' : Nat.card ↥(P : Subgroup G) = 2 ^ n := by simpa using hQcard
  have hZtop : Subgroup.center ↥(P : Subgroup G) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hZcard, hQcard'])
  haveI : NeZero n := ⟨by omega⟩
  have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hsimple : IsSimpleGroup G :=
    e.isSimpleGroup_congr.mpr
      (CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable
        (by rw [hFcard]; calc 4 = 2 ^ 2 := by norm_num
                              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)).1
  refine ⟨hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g _ hgN
    have hodd := hSE.2.2 g⁻¹ (fun h => hgN (by simpa using Subgroup.inv_mem _ h))
    rw [inv_inv] at hodd
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxg⟩ := hx
    have hxM : x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
      ⟨Subgroup.le_normalizer hxS, ⟨g⁻¹ * x * g, Subgroup.le_normalizer (B6.mem_conjSub.mp hxg),
        by simp [mul_assoc]⟩⟩
    have hd := Subgroup.orderOf_dvd_natCard _ hxM
    obtain ⟨k, hk⟩ := exists_two_pow_eq_one_of_mem_cs5 hS.2.1 hxS
    have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hodd' : Odd (orderOf x) := hodd.of_dvd_nat hd
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
      Nat.Coprime.pow_right _ hodd'.coprime_two_right
    have := Nat.Coprime.eq_one_of_dvd hcop h2
    exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp this)
  ·
    have h1 : (⊤ ⊓ Subgroup.normalizer ((P : Subgroup G) : Set G)).relIndex ⊤ =
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).index := by
      rw [top_inf_eq, Subgroup.relIndex_top_right]
    have hidx : Nat.card (Sylow 2 G) = (Subgroup.normalizer ((P : Subgroup G) : Set G)).index :=
      Sylow.card_eq_index_normalizer P
    rw [h1, ← hidx, CFSG.LargeExtraspecial.Bender.card_sylow_of_psl2 G 2 n hG, hQcard']
  ·
    intro N hN hnorm
    haveI : N.Normal := ⟨fun n hn g => hnorm g (Subgroup.mem_top g) n hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      apply hSE.1
      rw [eq_top_iff]
      intro x _
      exact (hN (h ▸ Subgroup.mem_top x)).2
  ·
    unfold centerSub
    rw [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective]
    simpa using hZcard
  ·
    intro z hz
    unfold centerSub at hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have := hzexp x hx
    have h2 : (x : G) * x = 1 := by
      have := congrArg Subtype.val this
      simpa [pow_two] using this
    exact h2
  ·
    intro z hz hz1 z' hz' hz'1
    have hzS := centerSub_le_cs5 _ hz
    have hz'S := centerSub_le_cs5 _ hz'
    let P' : Sylow 2 PSL(2, GaloisField 2 n) := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hP' : (P' : Subgroup PSL(2, GaloisField 2 n)) = (P : Subgroup G).map e.toMonoidHom :=
      Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
    obtain ⟨b', hb', hbz⟩ := psl2_sylow_transitive_cs5 (by omega) hFcard P' (z := e z) (z' := e z')
      (by rw [hP']; exact ⟨z, hzS, rfl⟩) (by simpa using hz1)
      (by rw [hP']; exact ⟨z', hz'S, rfl⟩) (by simpa using hz'1)
    refine ⟨e.symm b', ⟨Subgroup.mem_top _, ?_⟩, ?_⟩
    · rw [hP'] at hb'
      refine Subgroup.mem_normalizer_iff.mpr ?_
      intro y
      have h := (Subgroup.mem_normalizer_iff.mp hb') (e y)
      rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h
      simpa [map_mul] using h
    · apply e.injective
      simpa using hbz
  ·
    intro x hx _
    refine mem_centerSub_cs5.mpr ⟨hx, fun s hs => ?_⟩
    have := Subgroup.mem_center_iff.mp (hZtop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥(P : Subgroup G)))
      ⟨s, hs⟩
    exact congrArg Subtype.val this
  · calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn


theorem rankOneSyl_of_isPSL_two_cs5 {Y : Type} [Group Y] [Finite Y] {X S : Subgroup Y} {n : ℕ}
    (hn : 2 ≤ n) (hX : IsPSL 2 2 n ↥X) (hS : IsSylowTwoOf S X) :
    RankOneSyl X S (2 ^ n) :=
  RankOneSyl.of_subgroup_cs5 hS.1
    (rankOneSyl_top_of_isPSL_two_cs5 hn hX ((isSylowTwoOf_top_iff_cs5 hS.1).mpr hS))

end CFSG.Quasithin.H13
