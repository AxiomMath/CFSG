module

public import CFSG.CGT.Timmesfeld75.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W10FourNine
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Cent
import CFSG.RankThree.PartTwo.Sec8.Hering611SPsl2Cent
import CFSG.Adapters.StatedClassicalOrders
import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.Blueprint (LieModel)

private theorem r1fo_psl2 {X : Type} [Group X] {p f : ℕ} (h : LieModel X .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (X ≃* CFSG.GorensteinWalter.PSL2 F) := by
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := h.statedClassicalModel (by decide)
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨φ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

private theorem r1fo_three_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    3 ≤ p ^ f := by
  have := hp.two_le
  exact le_trans (by omega) (Nat.le_self_pow (by omega) p)

private theorem r1fo_l2_large {X : Type} [Group X] {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 2 ≤ f) (hF : Nat.card F = p ^ f)
    (φ : X ≃* CFSG.GorensteinWalter.PSL2 F) : 360 < Nat.card X := by
  rw [Nat.card_congr φ.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F
    ⟨p, f, hp, hp.odd_of_ne_two (by omega), by omega, hF⟩, hF]
  have h1 : 25 ≤ p ^ f :=
    le_trans (Nat.pow_le_pow_left hp5 2) (Nat.pow_le_pow_right (by omega) hf)
  have h2 : 625 ≤ (p ^ f) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h1 2)
  have h3 : 25 * 624 ≤ p ^ f * ((p ^ f) ^ 2 - 1) := Nat.mul_le_mul h1 (by omega)
  generalize p ^ f * ((p ^ f) ^ 2 - 1) = N at h3 ⊢
  omega

private theorem r1fo_l3_large {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (h : LieModel X .PSL 3 p f) : 360 < Nat.card X := by
  have hc := h.statedClassicalModel (by decide)
  obtain ⟨hp, hf1, -⟩ := hc.1
  have hq := r1fo_three_le hp hp2 hf1
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hc,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have hg : 0 < Nat.gcd 3 (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd 3 (p ^ f - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h27 : 27 ≤ (p ^ f) ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 3)
  have h9 : 9 ≤ (p ^ f) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  have hN : 27 * (8 * 26) ≤ (p ^ f) ^ (3 * (3 - 1) / 2) * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) :=
    Nat.mul_le_mul h27 (Nat.mul_le_mul (by omega) (by omega))
  refine (Nat.le_div_iff_mul_le hg).mpr (le_trans ?_ hN)
  generalize Nat.gcd 3 (p ^ f - 1) = g at hg hg3 ⊢
  omega

private theorem r1fo_u3_large {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (h : LieModel X .PSU 3 p f) : 360 < Nat.card X := by
  have hc := h.statedClassicalModel (by decide)
  obtain ⟨hp, hf1, -⟩ := hc.1
  have hq := r1fo_three_le hp hp2 hf1
  have key := CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three hc
  have hg3 : Nat.gcd 3 (p ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h27 : 27 ≤ (p ^ f) ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 3)
  have h9 : 9 ≤ (p ^ f) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  have hN : 27 * (8 * 28) ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
    Nat.mul_le_mul h27 (Nat.mul_le_mul (by omega) (by omega))
  by_contra hle
  have hle' : Nat.card X * Nat.gcd 3 (p ^ f + 1) ≤ 360 * 3 :=
    Nat.mul_le_mul (by omega) hg3
  generalize Nat.card X * Nat.gcd 3 (p ^ f + 1) = A at key hle'
  generalize (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) = B at key hN
  omega

private theorem r1fo_isElemAbelian_subgroupOf {Y : Type} [Group Y] {V : Subgroup Y}
    (hV2 : CFSG.Open.IsElemAbelian 2 V) (H : Subgroup Y) :
    CFSG.Open.IsElemAbelian 2 (V.subgroupOf H) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · exact congrArg (fun z : ↥V => (z : Y)) (isMulCommutative_iff.mp hV2.1 ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)
  · simpa using hV2.2 (x : Y) hx

private theorem r1fo_faithful {Y : Type} [Group Y] {K V H : Subgroup Y} (hKH : K ≤ H)
    (hVf : V ⊓ centralizer (K : Set Y) = ⊥) :
    V.subgroupOf H ⊓ centralizer (K.subgroupOf H : Set ↥H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxY : (x : Y) ∈ V ⊓ centralizer (K : Set Y) := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 ⟨k, hKH hk⟩ hk)
  rw [hVf] at hxY
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxY))

private theorem r1fo_l2_three {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {e : Y}
    {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 3 ^ f) (hf : f ≠ 0)
    (φ : ↥K ≃* CFSG.GorensteinWalter.PSL2 F) (he : orderOf e = 3) (heK : e ∈ K) :
    f ≤ CFSG.Open.pRank 3 K := by
  have hx : orderOf (φ ⟨e, heK⟩) = 3 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, he]
  have hx1 : φ ⟨e, heK⟩ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  have hx3 : φ ⟨e, heK⟩ ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one _
  obtain ⟨hab, hcard⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Hering611.centralizer_psl2_of_pow_three hf hF hx1 hx3
  let C := centralizer ({φ ⟨e, heK⟩} : Set (CFSG.GorensteinWalter.PSL2 F))
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num)
    (fun a b => isMulCommutative_iff.mp hab.1 a b)
    (fun a => Subtype.ext (by simpa using hab.2 a a.2))
    hcard (K.subtype.comp (φ.symm.toMonoidHom.comp C.subtype)) ?_ ?_
  · exact K.subtype_injective.comp (φ.symm.injective.comp C.subtype_injective)
  · rintro _ ⟨a, rfl⟩
    exact (φ.symm a).2

private theorem r1fo_even_of_l2 {Y : Type} [Group Y] [Finite Y] {K V : Subgroup Y} {e : Y}
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hF : Nat.card F = p ^ f) (φ : ↥K ≃* CFSG.GorensteinWalter.PSL2 F)
    (hV2 : CFSG.Open.IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V)
    (hVN : V ≤ normalizer (K : Set Y)) (hVf : V ⊓ centralizer (K : Set Y) = ⊥)
    (he : orderOf e = 3) (heK : e ∈ K) (hVe : V ≤ centralizer ({e} : Set Y)) : Even f := by
  let ρ : ↥V →* MulAut (CFSG.GorensteinWalter.PSL2 F) :=
    (MulAut.congr φ).toMonoidHom.comp ((CFSG.Quasithin.conjAct K).comp (Subgroup.inclusion hVN))
  have hρ : Function.Injective ρ := by
    refine (injective_iff_map_eq_one ρ).mpr fun v hv => ?_
    have h1 : CFSG.Quasithin.conjAct K (Subgroup.inclusion hVN v) = 1 :=
      (MulAut.congr φ).injective (by rw [map_one]; exact hv)
    have h2 : (v : Y) ∈ V ⊓ centralizer (K : Set Y) :=
      Subgroup.mem_inf.mpr ⟨v.2, (CFSG.Quasithin.AutOn.conjAct_eq_one_iff _).mp h1⟩
    rw [hVf] at h2
    exact Subtype.ext (Subgroup.mem_bot.mp h2)
  have hcard : Nat.card ρ.range = Nat.card V :=
    (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm
  have hE2 : ∀ α ∈ ρ.range, α * α = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [← map_mul, show v * v = 1 from Subtype.ext (by simpa [pow_two] using hV2.2 v v.2),
      map_one]
  have hEx : ∀ α ∈ ρ.range, α (φ ⟨e, heK⟩) = φ ⟨e, heK⟩ := by
    rintro _ ⟨v, rfl⟩
    have hfix : CFSG.Quasithin.conjAct K (Subgroup.inclusion hVN v) ⟨e, heK⟩ = ⟨e, heK⟩ := by
      apply Subtype.ext
      rw [CFSG.Quasithin.AutOn.coe_conjAct_apply]
      have hc : (v : Y) * e = e * v := Subgroup.mem_centralizer_singleton_iff.mp (hVe v.2)
      show (v : Y) * e * (v : Y)⁻¹ = e
      rw [hc, mul_inv_cancel_right]
    change φ (CFSG.Quasithin.conjAct K (Subgroup.inclusion hVN v) (φ.symm (φ ⟨e, heK⟩))) = _
    rw [MulEquiv.symm_apply_apply, hfix]
  have hx : orderOf (φ ⟨e, heK⟩) = 3 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, he]
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F = p := ringChar.eq F p
  obtain ⟨hle, h4⟩ := CFSG.RankThree.PartTwo.Sec20.card_le_four_of_forall_apply_eq
    (by rw [hchar]; exact hp2) (by rw [hchar]; exact hp3) hx ρ.range hE2 hEx
  obtain ⟨-, σ, hσ1, hσ2⟩ := h4 (by omega)
  exact CFSG.RankThree.PartTwo.Sec20.even_of_ringEquiv hp hF hσ1 hσ2

section W10


private theorem r1fo_card_w10 {Y : Type} [Group Y] [Finite Y] {K V : Subgroup Y}
    (hKs : IsSimpleGroup ↥K) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hchev : CFSG.LocalAnalysis.UniquenessCase.UC22.IsChev ↥K q)
    (hV2 : CFSG.Open.IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V)
    (hVN : V ≤ normalizer (K : Set Y)) (hVf : V ⊓ centralizer (K : Set Y) = ⊥)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) : Nat.card K ≤ 360 := by
  have hKH : K ≤ K ⊔ V := le_sup_left
  have hVH : V ≤ K ⊔ V := le_sup_right
  let eK : ↥(K.subgroupOf (K ⊔ V)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have hnorm : (K.subgroupOf (K ⊔ V)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (sup_le Subgroup.le_normalizer hVN)
  have : IsSimpleGroup ↥K := hKs
  have hchev' : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsChev ↥(K.subgroupOf (K ⊔ V)) q := by
    obtain ⟨t, n, f, hadm, hmod⟩ := hchev
    exact ⟨q, hq, hq2, t, n, f, hadm, hmod.of_mulEquiv eK.symm⟩
  have hcardV : 4 ≤ Nat.card (V.subgroupOf (K ⊔ V)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
  have htop : K.subgroupOf (K ⊔ V) ⊔ V.subgroupOf (K ⊔ V) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKH hVH, Subgroup.subgroupOf_self]
  have h := w10_4_9_holds ↥(K ⊔ V) (K.subgroupOf (K ⊔ V)) (V.subgroupOf (K ⊔ V)) hnorm
    eK.isSimpleGroup hchev' (r1fo_isElemAbelian_subgroupOf hV2 _) hcardV (r1fo_faithful hKH hVf)
    htop (hTI.subgroupOf _)
  rw [Nat.card_congr eK.toEquiv] at h
  omega

theorem false_of_odd_char_of_rankOne {Y : Type} [Group Y] [Finite Y] (K V : Subgroup Y) (e : Y)
    (hKs : IsSimpleGroup ↥K)
    (hshape : (∃ p f : ℕ, p ≠ 2 ∧ LieModel ↥K .PSL 2 p f) ∨
      (∃ p f : ℕ, p ≠ 2 ∧ p ^ f % 3 = 2 ∧ LieModel ↥K .PSL 3 p f) ∨
      (∃ p f : ℕ, p ≠ 2 ∧ p ^ f % 3 = 1 ∧ LieModel ↥K .PSU 3 p f))
    (h3 : CFSG.Open.pRank 3 K ≤ 1) (hV2 : CFSG.Open.IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V)
    (hVN : V ≤ normalizer (K : Set Y)) (hVf : V ⊓ centralizer (K : Set Y) = ⊥)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (he : orderOf e = 3) (heK : e ∈ K)
    (hVe : V ≤ centralizer ({e} : Set Y)) : False := by
  have hw : ∀ {t n p f}, p ≠ 2 → LieModel ↥K t n p f → Nat.card K ≤ 360 := fun hp2 hL =>
    r1fo_card_w10 hKs hL.admissible.1 hp2 ⟨_, _, _, hL.admissible, hL⟩ hV2 hV4 hVN hVf hTI
  rcases hshape with ⟨p, f, hp2, hL⟩ | ⟨p, f, hp2, -, hL⟩ | ⟨p, f, hp2, -, hL⟩
  · obtain ⟨hp, hf1, -, -, h23⟩ := hL.admissible
    obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := r1fo_psl2 hL
    by_cases hp3 : p = 3
    · subst hp3
      have hf : f ≠ 1 := by
        rintro rfl
        exact h23 rfl
      have := r1fo_l2_three hF (by omega) φ he heK
      omega
    · rcases Nat.even_or_odd f with hfe | hfo
      · obtain ⟨r, hr⟩ := hfe
        have := r1fo_l2_large hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3) (by omega) hF φ
        have := hw hp2 hL
        omega
      · exact Nat.not_even_iff_odd.mpr hfo
          (r1fo_even_of_l2 hp hp2 hp3 hF φ hV2 hV4 hVN hVf he heK hVe)
  · have := r1fo_l3_large hp2 hL
    have := hw hp2 hL
    omega
  · have := r1fo_u3_large hp2 hL
    have := hw hp2 hL
    omega

end W10

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
