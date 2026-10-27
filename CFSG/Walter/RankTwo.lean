module

public import CFSG.Walter.Defs
public import CFSG.Assembly.Defs
import CFSG.Walter.AStar.Basic
import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes
import CFSG.Dihedral.GorensteinWalter
import CFSG.Walter.TwoRank

public section

namespace CFSG.Walter

open scoped MatrixGroups

theorem twoRank_eq_assembly (G : Type*) [Group G] [Finite G] :
    CFSG.Open.twoRank G = CFSG.Assembly.twoRank G := rfl

theorem sylow_isKleinFour_of_twoRank_eq_two
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : CFSG.Assembly.twoRank G = 2) (S : Sylow 2 G)
    (hS : IsMulCommutative (S : Subgroup G)) : IsKleinFour (S : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Sg := (S : Subgroup G) with hSg
  have hcomm : ∀ a b : Sg, a * b = b * a := fun a b => hS.is_comm.comm a b
  have hSp : IsPGroup 2 Sg := S.isPGroup'
  have hrankS : RankTwoShapes.TwoRankLeTwo Sg := by
    intro E hE hexp
    have hmap : Nat.card (E.map Sg.subtype) = Nat.card E :=
      Subgroup.card_map_of_injective Sg.subtype_injective
    rw [← hmap]
    apply RankTwoShapes.elementary_card_le_four_of_twoRank hrank
    · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      obtain ⟨ea, hea, hea'⟩ := a.2
      obtain ⟨eb, heb, heb'⟩ := b.2
      have hc := congrArg (fun x : E => ((x : Sg) : G)) (hE.is_comm.comm ⟨ea, hea⟩ ⟨eb, heb⟩)
      simp only [Subgroup.coe_mul] at hc
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hea', ← heb']
      exact hc
    · rintro _ ⟨e, he, rfl⟩
      have h := congrArg Subtype.val (hexp e he)
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
  obtain ⟨E₀, -, hE₀card⟩ := RankTwoShapes.exists_elementary_four_of_twoRank hrank
  have h2G : 2 ∣ Nat.card G := by
    have := E₀.card_subgroup_dvd_card
    rw [hE₀card] at this
    exact dvd_trans (by norm_num : 2 ∣ 4) this
  have hSne : Sg ≠ ⊥ := S.ne_bot_of_dvd_card h2G
  have : Nontrivial Sg := (Subgroup.nontrivial_iff_ne_bot Sg).mpr hSne
  have h2S : 2 ∣ Nat.card Sg := by
    rcases hSp.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card).ne'
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Sg) 2 h2S
  have hzZ : z ∈ Subgroup.center Sg := Subgroup.mem_center_iff.mpr fun y => hcomm y z
  obtain ⟨g, hgS, hgz⟩ :=
    RankTwoShapes.simple_central_sylow_involution_movement hnonab S z hzZ hz
  obtain ⟨n, hnN, hn⟩ := Sylow.conj_eq_normalizer_conj_of_mem S (z : G) g z.2 hgS
  set NQ := Subgroup.normalizer (Sg : Set G) with hNQ
  set φ : NQ →* MulAut Sg := Sg.normalizerMonoidHom with hφ
  set A : Subgroup (MulAut Sg) := φ.range with hA
  set P₀ : Subgroup NQ := (Sg ⊓ NQ).subgroupOf NQ with hP₀
  have hP₀p : IsPGroup 2 P₀ :=
    (S.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hP₀idx : ¬ 2 ∣ P₀.index := by
    have hle : Sg ≤ NQ := Subgroup.le_normalizer
    have hidx : P₀.index ∣ Sg.index := by
      have h1 : P₀ = Sg.subgroupOf NQ := by
        rw [hP₀, inf_eq_left.mpr hle]
      rw [h1]
      exact Subgroup.relIndex_dvd_index_of_le hle
    exact fun h => S.not_dvd_index (h.trans hidx)
  set P₀s : Sylow 2 NQ := hP₀p.toSylow hP₀idx with hP₀s
  set B : Sylow 2 A := P₀s.mapSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    with hBdef
  have hB : ∀ b ∈ (B : Subgroup A), ((b : A) : MulAut Sg) z = z := by
    intro b hb
    rw [hBdef, Sylow.coe_mapSurjective] at hb
    obtain ⟨m, hm, rfl⟩ := hb
    have hm' : m ∈ P₀ := by
      have h1 : m ∈ ((hP₀p.toSylow hP₀idx : Sylow 2 NQ) : Subgroup NQ) := hm
      rwa [IsPGroup.toSylow_coe] at h1
    have hmS : (m : G) ∈ Sg := (Subgroup.mem_subgroupOf.mp hm').1
    apply Subtype.ext
    change (m : G) * (z : G) * (m : G)⁻¹ = z
    have := congrArg Subtype.val (hcomm ⟨(m : G), hmS⟩ z)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
    rw [this, mul_inv_cancel_right]
  have hmove : ∃ a ∈ A, a z ≠ z := by
    refine ⟨φ ⟨n⁻¹, NQ.inv_mem hnN⟩, ⟨_, rfl⟩, ?_⟩
    intro h
    apply hgz
    have h' := congrArg Subtype.val h
    change n⁻¹ * (z : G) * n⁻¹⁻¹ = z at h'
    rw [inv_inv] at h'
    rw [hn, h']
  obtain ⟨-, -, α, hαA, hα3, -, hαfpf⟩ :=
    RankTwoShapes.central_involution_three_automorphism hSp hrankS A B hzZ hz hB hmove
  have hα3' : α ^ 3 = 1 := by rw [← hα3]; exact pow_orderOf_eq_one α
  obtain ⟨x, hxmax⟩ := Finite.exists_max (fun y : Sg => orderOf y)
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hSp) x
  have he1 : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    have h2 := hxmax z
    rw [hz, he, he0, pow_zero] at h2
    omega
  obtain ⟨-, -, ⟨eA⟩, -, -, -, htop⟩ :=
    RankTwoShapes.three_automorphism_homocyclic_subgroup hSp hrankS α hα3' hαfpf x hxmax he he1
  have eS : Sg ≃* Multiplicative (ZMod (2 ^ e)) × Multiplicative (ZMod (2 ^ e)) :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr (htop hcomm)).symm.trans eA)
  have he' : e = 1 := RankTwoShapes.homocyclic_sylow_simple_exponent_two hnonab S e he1 ⟨eS⟩
  subst he'
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr eS.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]
    norm_num
  · apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro s
      apply eS.injective
      rw [map_pow, map_one]
      exact RankTwoShapes.sq_eq_one_of_klein _
    · rw [← hz]
      exact Monoid.order_dvd_exponent z

theorem mod_eight_of_psl2_two_part {q : ℕ} (hq : Odd q) (hq1 : 1 < q)
    (h : (q * (q ^ 2 - 1) / 2).factorization 2 = 2) : q % 8 = 3 ∨ q % 8 = 5 := by
  have two_dvd_of (m : ℕ) (hm : m ≠ 0) (h1 : m.factorization 2 = 1) : 2 ∣ m ∧ ¬ 4 ∣ m := by
    refine ⟨?_, fun h4 => ?_⟩
    · have := (Nat.prime_two.pow_dvd_iff_le_factorization hm (k := 1)).mpr (by omega)
      simpa using this
    · have := (Nat.prime_two.pow_dvd_iff_le_factorization hm (k := 2)).mp (by simpa using h4)
      omega
  have hq3 : 3 ≤ q := by
    obtain ⟨k, hk⟩ := hq
    omega
  rcases Nat.even_or_odd ((q - 1) / 2) with heven | hodd
  · rw [GorensteinWalter.psl2_order_two_factorization_split hq hq1 heven] at h
    obtain ⟨h2, h4⟩ := two_dvd_of ((q - 1) / 2) (by omega) (by omega)
    obtain ⟨k, hk⟩ := hq
    omega
  · rw [GorensteinWalter.psl2_order_two_factorization_nonsplit hq hq1 hodd] at h
    obtain ⟨h2, h4⟩ := two_dvd_of ((q + 1) / 2) (by omega) (by omega)
    obtain ⟨k, hk⟩ := hq
    omega

theorem isTypeL2_of_twoRank_le_two
    (L : Type) [Group L] [Finite L] [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (hab : HasAbelianSylowTwo L)
    (hrank : CFSG.Open.twoRank L ≤ 2) : IsTypeL2 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven := even_card_of_isSimpleGroup hnonab
  have h2 : CFSG.Assembly.twoRank L = 2 :=
    le_antisymm hrank (CFSG.Walter.two_le_twoRank L hnonab heven)
  obtain ⟨S⟩ : Nonempty (Sylow 2 L) := inferInstance
  have hK := sylow_isKleinFour_of_twoRank_eq_two hnonab h2 S (hab S)
  have hS4 : Nat.card (S : Subgroup L) = 4 := hK.card_four
  have hfac : (Nat.card L).factorization 2 = 2 := by
    have h := S.card_eq_multiplicity
    rw [hS4] at h
    exact (Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num : 4 = 2 ^ 2)))
  have hcard0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  obtain ⟨eD⟩ : Nonempty ((S : Subgroup L) ≃* DihedralGroup 2) := by
    let := Fintype.ofFinite (S : Subgroup L)
    obtain ⟨e₀⟩ : Nonempty ((S : Subgroup L) ≃ DihedralGroup 2) := by
      refine Fintype.card_eq.mp ?_
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hS4, IsKleinFour.card_four]
    let e₁ := e₀.trans (Equiv.swap (e₀ 1) 1)
    exact ⟨IsKleinFour.mulEquiv e₁ (Equiv.swap_apply_left _ _)⟩
  rcases GorensteinWalter.gorenstein_walter L hnonab S ⟨2, ⟨eD⟩⟩ with ⟨⟨e7⟩⟩ |
      ⟨p, k, hp, hpodd, hpk, ⟨e⟩⟩
  · exfalso
    have h7 : Nat.card L = 2520 := by
      rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have h8 : 2 ^ 3 ∣ Nat.card L := by rw [h7]; norm_num
    have := (Nat.prime_two.pow_dvd_iff_le_factorization hcard0).mp h8
    omega
  · right
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hpk
    have hqcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp.out, hpodd, Nat.one_le_iff_ne_zero.mpr hk0, hqcard⟩
    have hLcard : Nat.card L = p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula _ hodd, hqcard]
    have hqodd : Odd (p ^ k) := hpodd.pow
    have hmod := mod_eight_of_psl2_two_part hqodd (by omega) (hLcard ▸ hfac)
    exact ⟨p, k, hp, hpodd, Nat.pos_of_ne_zero hk0, hpk, hmod, ⟨e⟩⟩

end CFSG.Walter
