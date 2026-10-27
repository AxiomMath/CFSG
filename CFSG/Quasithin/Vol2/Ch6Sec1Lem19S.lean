module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19D
public import CFSG.Quasithin.Vol2.Ch5Sec1BorelTorus
public import CFSG.Quasithin.Background.G64Linear
public import CFSG.Quasithin.EmptyFaithful.S146S3
public import CFSG.Quasithin.Vol2.Ch6Sec1GreenBook

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace L619

omit [Finite G] in
theorem conjSub_le_normalizer_of_mem {X Y : Subgroup G} {g : G}
    (hX : X ≤ Subgroup.normalizer (Y : Set G)) (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    conjSub g X ≤ Subgroup.normalizer (Y : Set G) := by
  have := conjSub_le_normalizer (g := g) hX
  rwa [conjSub_eq_of_mem_normalizer' hg] at this

omit [Finite G] in
theorem isPGroup_inf_of_card {X D I : Subgroup G} (hXI : X ≤ Subgroup.normalizer (I : Set G))
    (hDX : D ≤ X) (hD3 : Nat.card D = 3) (hDI : D ⊓ I = ⊥) {a : ℕ}
    (hX : Nat.card X = 3 * 2 ^ a) : IsPGroup 2 ↥(X ⊓ I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := X ⊓ I with hN
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hXI hx⟩
  have hDN : D ≤ Subgroup.normalizer (N : Set G) := hDX.trans hXN
  have h1 : N.relIndex (D ⊔ N) = N.relIndex D := A4.relIndex_sup_eq_of_le_normalizer' hDN
  have h2 : N.relIndex D = 3 := by
    have h := Subgroup.relIndex_mul_card N D
    have hND : N ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [← hDI]
      exact ⟨hx.2, hx.1.2⟩
    rw [hND, Subgroup.card_bot, mul_one, hD3] at h
    exact h
  have h3 : N.relIndex (D ⊔ N) * Nat.card ↥(N ⊓ (D ⊔ N)) = Nat.card ↥(D ⊔ N) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr (le_sup_right : N ≤ D ⊔ N), h1, h2] at h3
  have h4 : Nat.card ↥(D ⊔ N) ∣ Nat.card X := Subgroup.card_dvd_of_le (sup_le hDX inf_le_left)
  rw [← h3, hX] at h4
  have h5 : Nat.card N ∣ 2 ^ a := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h5
  exact IsPGroup.of_card hb

theorem le_normalizer_of_card {X D I S : Subgroup G} (hXI : X ≤ Subgroup.normalizer (I : Set G))
    (hDX : D ≤ X) (hD3 : Nat.card D = 3) (hDI : D ⊓ I = ⊥) {a : ℕ}
    (hX : Nat.card X = 3 * 2 ^ a) (hSX : S ≤ X) (hS : IsSylowTwoOf S I) :
    X ≤ Subgroup.normalizer (S : Set G) := by
  have heq : X ⊓ I = S := G64.IsSylowTwoOf.eq_of_le hS (le_inf hSX hS.1) inf_le_right
    (isPGroup_inf_of_card hXI hDX hD3 hDI hX)
  rw [← heq]
  exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, hXI hx⟩

theorem nonempty_oTwoQuot_conjSub {P : Subgroup G} (g : G)
    (h : Nonempty (oTwoQuot ↥P ≃* Equiv.Perm (Fin 3))) :
    Nonempty (oTwoQuot ↥(conjSub g P) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h
  let c : ↥(conjSub g P) ≃* ↥P :=
    (P.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  let ψ : ↥(conjSub g P) →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥P)).comp c.toMonoidHom)
  refine nonempty_quot_perm3_of_surjective ψ ?_ ?_
  · intro σ
    obtain ⟨q, rfl⟩ := e.surjective σ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨c.symm x, by simp [ψ]⟩
  · have hker : ψ.ker = (CFSG.Open.pCore 2 ↥P).comap c.toMonoidHom := by
      ext x
      simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_comap]
    rw [hker]
    exact (CFSG.LieType.BorelTits.pCore_isPGroup 2).comap_of_injective _ c.injective

end L619

namespace Hyp5_0_1

theorem card_sup_borelL (h : Hyp5_0_1 G T M L n) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    ∃ a : ℕ, Nat.card ↥(T ⊔ borelL T L) = Nat.card D * 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTB : T ≤ Subgroup.normalizer (borelL T L : Set G) := by
    intro t ht
    have htTL : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, h.T_le_normalizer ht⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.T_le_normalizer ht, F1.mem_normalizer_normalizer htTL⟩
  have h1 : (borelL T L).relIndex (T ⊔ borelL T L) = (borelL T L).relIndex T :=
    A4.relIndex_sup_eq_of_le_normalizer' hTB
  have h2 : (borelL T L).relIndex (T ⊔ borelL T L) * Nat.card ↥(borelL T L ⊓ (T ⊔ borelL T L)) =
      Nat.card ↥(T ⊔ borelL T L) := Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr (le_sup_right : borelL T L ≤ T ⊔ borelL T L), h1] at h2
  obtain ⟨k, hk⟩ := hD.2.2
  have h3 : D.relIndex (borelL T L) * Nat.card ↥(D ⊓ borelL T L) = Nat.card ↥(borelL T L) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr hD.1, hk] at h3
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp h.sylow.1
  have h4 : (borelL T L).relIndex T ∣ 2 ^ m := by
    rw [← hm]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  refine ⟨j + k, ?_⟩
  rw [← h2, hj, ← h3, pow_add]
  ring

end Hyp5_0_1

structure Dat619 (T M L V H : Subgroup G) (n : ℕ) (y z : G) (T' D' : Subgroup G) : Prop where
  cfg : Cfg619 T L V H n y
  z619 : Z619 T L V H y z
  isY : IsY619 T L V z (ch619I T L V ⊔ T')
  sylow : quasithinIsSylowTwo T'
  T'_le : T' ≤ Subgroup.normalizer (ch6ZS T L V : Set G)
  sylow_S' : IsSylowTwoOf (T' ⊓ ch619I T L V) (ch619I T L V)
  D'_le_L : D' ≤ L
  card_D' : Nat.card D' = 3
  D'_le_ZS : D' ≤ Subgroup.normalizer (ch6ZS T L V : Set G)
  D'_inf : D' ⊓ ch619I T L V = ⊥
  D'_le_S' : D' ≤ Subgroup.normalizer ((T' ⊓ ch619I T L V : Subgroup G) : Set G)
  rank : CFSG.Open.pRank 3 (Subgroup.normalizer (ch6ZS T L V : Set G)) ≤ 2

namespace Dat619

variable {z : G} {T' D' : Subgroup G} (hd : Dat619 T M L V H n y z T' D')
include hd

theorem D'_le_I : D' ≤ Subgroup.normalizer (ch619I T L V : Set G) :=
  L619.normalizer_I_of hd.D'_le_ZS

theorem T'_le_I : T' ≤ Subgroup.normalizer (ch619I T L V : Set G) :=
  L619.normalizer_I_of hd.T'_le

theorem rank_I : CFSG.Open.pRank 3 (ch619I T L V) ≤ 2 :=
  (CFSG.SectionRank.pRank_mono (by norm_num) (Subgroup.centralizer_le_normalizer _)).trans hd.rank

theorem pow_three_eq_one {d : G} (hdD : d ∈ D') : d ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥D') (x := ⟨d, hdD⟩)
  rw [hd.card_D'] at h
  simpa using congrArg Subtype.val h

end Dat619

namespace Hyp6116

theorem exists_dat619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (h6112 : Stmt6_1_12) (h : Hyp6116 G T M L V n)
    (hH : IsInHS T M L V H) (hHs : IsHStar T M H)
    (hodd : Odd (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V)) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    ∃ y z d : G, d ∈ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) ∧
      Dat619 T M L V H n y z (conjSub d⁻¹ T) (conjSub d⁻¹ D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, c⟩ := h.exists_cfg619 h331 h432 h615 h6110 h6112 hH hHs hodd
  obtain ⟨z, hz1, -, hzZ, hcomm⟩ := c.exists_z h
  have hz : Z619 T L V H y z := ⟨hz1, hzZ, hcomm⟩
  obtain ⟨d, hd, hTz⟩ := h.toHyp611Nat.exists_conjSub_T_le_centralizer hz.mem_ZS hz1
  have hY := isY619_sup h.toHyp611Nat hz.mem_ZS hd hTz
  have hdZ : d⁻¹ ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := Subgroup.inv_mem _ hd.2
  have hdL : d⁻¹ ∈ L := Subgroup.inv_mem _ hd.1
  set I := ch619I T L V with hI
  set T' := conjSub d⁻¹ T with hT'
  set D' := conjSub d⁻¹ D with hD'
  have hT'syl : quasithinIsSylowTwo T' :=
    ⟨h.sylow.1.map _, by
      rw [hT']
      unfold conjSub
      rw [show (MulAut.conj d⁻¹).toMonoidHom = ((MulAut.conj d⁻¹ : G ≃* G) : G →* G) from rfl,
        Subgroup.index_map_equiv]
      exact h.sylow.2⟩
  have hTZ : T' ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    L619.conjSub_le_normalizer_of_mem h.T_le_normalizer_ZS hdZ
  have hTI : T' ≤ Subgroup.normalizer (I : Set G) := L619.normalizer_I_of hTZ
  have hBZ : borelL T L ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    h.toHyp611Nat.borelL_le_normalizer_ZS
  have hDZ : D' ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    L619.conjSub_le_normalizer_of_mem (hD.1.trans hBZ) hdZ
  have hDL : D' ≤ L := by
    have := conjSub_mono d⁻¹ (hD.1.trans inf_le_left)
    rwa [conjSub_eq_of_mem_normalizer' (Subgroup.le_normalizer hdL)] at this
  have hn : n = 2 := c.n_eq
  have hcD : Nat.card D = 3 := by
    rw [(h.toHyp5_0_1.isCyclic_card_of_isHall l2TorusFact hD).2, hn]
    norm_num
  have hcD' : Nat.card D' = 3 := by rw [hD', card_conjSub', hcD]
  have hDI : D' ⊓ I = ⊥ :=
    h.toHyp611Nat.inf_centralizer_ZS_eq_bot hDL (by rw [hcD']; exact ⟨1, rfl⟩)
  have hsylN : IsSylowTwoOf T' (Subgroup.normalizer (ch6ZS T L V : Set G)) :=
    E6.isSylowIn_of_le ⟨le_top, hT'syl.1, by rw [Subgroup.relIndex_top_right]; exact hT'syl.2⟩
      hTZ le_top
  have hS' : IsSylowTwoOf (T' ⊓ I) I :=
    A4.isSylowTwoOf_inf_normal hsylN (Subgroup.centralizer_le_normalizer _)
      (L619.normalizer_I_of le_rfl)
  obtain ⟨a, ha⟩ := h.toHyp5_0_1.card_sup_borelL hD
  set X := conjSub d⁻¹ (T ⊔ borelL T L) with hX
  have hXI : X ≤ Subgroup.normalizer (I : Set G) :=
    L619.normalizer_I_of (L619.conjSub_le_normalizer_of_mem
      (sup_le h.T_le_normalizer_ZS hBZ) hdZ)
  have hDX : D' ≤ X := conjSub_mono _ (hD.1.trans le_sup_right)
  have hcX : Nat.card X = 3 * 2 ^ a := by rw [hX, card_conjSub', ha, hcD]
  have hSX : T' ⊓ I ≤ X := inf_le_left.trans (conjSub_mono _ le_sup_left)
  have hDS : D' ≤ Subgroup.normalizer ((T' ⊓ I : Subgroup G) : Set G) :=
    hDX.trans (L619.le_normalizer_of_card hXI hDX hcD' hDI hcX hSX hS')
  have hO : pCoreOf 2 (Subgroup.normalizer (ch6ZS T L V : Set G)) ≠ ⊥ := by
    intro h0
    apply h.toHyp611Nat.ZS_ne_bot
    rw [eq_bot_iff, ← h0]
    have hZel : IsElemAbelian 2 (ch6ZS T L V) :=
      B2F.isElemAbelian_mono inf_le_left h.toHyp611.isElemAbelian
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (B2F.isPGroup_of_isElemAbelian hZel)
  have hrank : CFSG.Open.pRank 3 (Subgroup.normalizer (ch6ZS T L V : Set G)) ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot h.qtke hO Nat.prime_three (by norm_num)
  exact ⟨y, z, d, hd, c, hz, hY, hT'syl, hTZ, hS', hDL, hcD', hDZ, hDI, hDS, hrank⟩

end Hyp6116

namespace Hyp611Nat

theorem parabolic_of_conj (h : Hyp611Nat G T M L V n) {d : G}
    (hd : d ∈ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)) {D P₁' : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hP₁I : P₁' ≤ ch619I T L V)
    (hTP : conjSub d⁻¹ T ≤ Subgroup.normalizer (P₁' : Set G))
    (hDP : conjSub d⁻¹ D ≤ Subgroup.normalizer (P₁' : Set G)) (hM : ¬ P₁' ≤ M)
    (hsyl : IsSylowTwoOf (conjSub d⁻¹ T ⊓ P₁') P₁')
    (hS3 : Nonempty (oTwoQuot ↥P₁' ≃* Equiv.Perm (Fin 3))) :
    ∃ P₁ : Subgroup G, P₁ ≤ Subgroup.normalizer (ch6ZS T L V : Set G) ∧
      T ≤ Subgroup.normalizer (P₁ : Set G) ∧ borelL T L ≤ Subgroup.normalizer (P₁ : Set G) ∧
      ¬ P₁ ≤ M ∧ IsSylowTwoOf (T ⊓ P₁) P₁ ∧ Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)) := by
  refine ⟨conjSub d P₁', ?_, ?_, ?_, ?_, ?_, L619.nonempty_oTwoQuot_conjSub d hS3⟩
  · exact L619.conjSub_le_normalizer_of_mem (hP₁I.trans (Subgroup.centralizer_le_normalizer _))
      hd.2
  · have := conjSub_le_normalizer (g := d) hTP
    rwa [conjSub_inv_conjSub] at this
  · rw [← h.toHyp5_0_1.borelL_eq_sup hD]
    refine sup_le ?_ (inf_le_left.trans ?_)
    · have := conjSub_le_normalizer (g := d) hDP
      rwa [conjSub_inv_conjSub] at this
    · have := conjSub_le_normalizer (g := d) hTP
      rwa [conjSub_inv_conjSub] at this
  · intro hle
    apply hM
    have := conjSub_mono d⁻¹ hle
    rwa [conjSub_conjSub_inv, conjSub_eq_of_mem_normalizer'
      (Subgroup.le_normalizer (Subgroup.inv_mem _ (h.L_le hd.1)))] at this
  · have := F7.isSylowTwoOf_conj hsyl d
    rwa [conjSub_inf, conjSub_inv_conjSub] at this

end Hyp611Nat

end CFSG.Quasithin.H13
