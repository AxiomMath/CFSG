module

public import CFSG.Quasithin.H13.KGFactL33
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Quasithin.Vol2.Ch11SecBL2OPSL
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open CFSG.GorensteinWalter
open scoped MatrixGroups

namespace ConfL2

theorem ne_two_of_fermat_or_mersenne {p : ℕ} (h : IsFermatOrMersennePrime p) : p ≠ 2 := by
  rintro rfl
  rcases h.2 with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · have : 1 ≤ 2 ^ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ 2 ^ k = 1 := by omega
    have h0 : 2 ^ k = 0 := by
      rcases Nat.pow_eq_one.mp h2 with h | h
      · omega
      · exact h
    exact absurd h0 (by positivity)
  · have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

theorem mod_eight_of_fermat_or_mersenne {p : ℕ} (h : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  rcases h.2 with ⟨k, rfl⟩ | ⟨k, hk2, rfl⟩
  · left
    have hk : 2 ≤ k := by
      by_contra hk
      interval_cases k <;> norm_num at hp7
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ k = j + 3 := ⟨2 ^ k - 3, by omega⟩
    rw [hj, pow_add]
    omega
  · right
    have hk : 3 ≤ k := by
      by_contra hk
      interval_cases k
      norm_num at hp7
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    rw [pow_add]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega

section Action

variable {p : ℕ} {G : Type} [Group G] (K : Subgroup G) (e : ↥K ≃* PSL2 (ZMod p))

@[expose] noncomputable def actHom :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (PSL2 (ZMod p)) where
  toFun c := (e.symm.trans (KGL33.conjK K c c.2)).trans e
  map_one' := by
    ext x
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.one_apply]
    conv_rhs => rw [← e.apply_symm_apply x]
    congr 1
    apply Subtype.ext
    rw [KGL33.conjK_apply]
    simp
  map_mul' m n := by
    ext x
    rw [MulAut.mul_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    simp only [KGL33.conjK_apply, Subgroup.coe_mul]
    group

theorem actHom_apply (c : ↥(Subgroup.normalizer (K : Set G))) (y : ↥K) :
    actHom K e c (e y) = e (KGL33.conjK K c c.2 y) := by
  show e (KGL33.conjK K c c.2 (e.symm (e y))) = e (KGL33.conjK K c c.2 y)
  rw [MulEquiv.symm_apply_apply]

theorem mem_centralizer_of_actHom_eq_one {c : ↥(Subgroup.normalizer (K : Set G))}
    (h : actHom K e c = 1) : (c : G) ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := actHom_apply K e c ⟨x, hx⟩
  rw [h, MulAut.one_apply] at h1
  have h2 := congrArg Subtype.val (e.injective h1)
  rw [KGL33.conjK_apply] at h2
  calc x * c = (c * x * (c : G)⁻¹) * c := by rw [← h2]
    _ = c * x := by group

theorem actHom_eq_one_of_mem_centralizer {c : ↥(Subgroup.normalizer (K : Set G))}
    (h : (c : G) ∈ Subgroup.centralizer (K : Set G)) : actHom K e c = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [actHom_apply, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [KGL33.conjK_apply, ← Subgroup.mem_centralizer_iff.mp h y y.2]
  group

end Action

section Aut

variable {p : ℕ} [Fact p.Prime]

theorem exists_pgl2_eq (hK : IsOddPrimePower (Nat.card (ZMod p)))
    (hcard : 3 < Nat.card (ZMod p)) (γ : MulAut (PSL2 (ZMod p))) :
    ∃ g : PGL2 (ZMod p), γ = pgl2InnerAutPSL2 (ZMod p) hK hcard g := by
  have hKcard : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod p) hKcard hK hcard γ
  have hr : x.right = 1 := Subsingleton.elim _ _
  rw [← SemidirectProduct.inl_left_mul_inr_right x, hr, map_one, mul_one,
    pGammaL2ToMulAutPSL2_inl] at hx
  exact ⟨x.left, hx.symm⟩

theorem exists_mem_kleinFour
    (hK : IsOddPrimePower (Nat.card (ZMod p)))
    (hcard : 3 < Nat.card (ZMod p)) {V : Subgroup (PSL2 (ZMod p))} (hV : IsKleinFour V)
    (γ : MulAut (PSL2 (ZMod p))) (hγ : ∀ t ∈ V, γ t = t) : ∃ v ∈ V, γ = MulAut.conj v := by
  obtain ⟨g, rfl⟩ := exists_pgl2_eq hK hcard γ
  let toPGL : PSL2 (ZMod p) →* PGL2 (ZMod p) := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP' : IsKleinFour (V.map toPGL) := isKleinFour_map_of_injective V hV toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (PGL2 (ZMod p))) :
      Set (PGL2 (ZMod p))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 := hγ v hv
    have h2 := toPGL_pgl2InnerAutPSL2_apply (ZMod p) hK hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self (ZMod p) hK _ hVP'] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  refine ⟨g0, hg0V, ?_⟩
  rw [← hg0]
  exact pgl2InnerAutPSL2_toPGL (ZMod p) hK hcard g0

theorem sq_mem_range_toPGL {K : Type*} [Field K] [Fintype K] [DecidableEq K] (g : PGL2 K) :
    g ^ 2 ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  CFSG.GorensteinWalter.pgl2_sq_mem_psl2Range g

theorem exists_conj_of_odd (hK : IsOddPrimePower (Nat.card (ZMod p)))
    (hcard : 3 < Nat.card (ZMod p)) (γ : MulAut (PSL2 (ZMod p))) (hγ : Odd (orderOf γ)) :
    ∃ k : PSL2 (ZMod p), γ = MulAut.conj k := by
  obtain ⟨g, rfl⟩ := exists_pgl2_eq hK hcard γ
  obtain ⟨r, hr⟩ := hγ
  have h1 : pgl2InnerAutPSL2 (ZMod p) hK hcard ((g ^ (r + 1)) ^ 2) =
      pgl2InnerAutPSL2 (ZMod p) hK hcard g := by
    rw [← pow_mul, map_pow, show (r + 1) * 2 = orderOf (pgl2InnerAutPSL2 (ZMod p) hK hcard g) + 1
      by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  obtain ⟨k, hk⟩ := sq_mem_range_toPGL (g ^ (r + 1))
  refine ⟨k, ?_⟩
  rw [← h1, ← hk]
  exact pgl2InnerAutPSL2_toPGL (ZMod p) hK hcard k


end Aut

theorem eq_of_card_eq_two {H : Type*} [Group H] [Finite H] (h : Nat.card H = 2) {x y : H}
    (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  classical
  have : Fintype H := Fintype.ofFinite H
  by_contra hxy
  have h3 : ({1, x, y} : Finset H).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, x, y, hx.symm, hy.symm, hxy, rfl⟩
  have h4 := Finset.card_le_univ ({1, x, y} : Finset H)
  rw [h3, ← Nat.card_eq_fintype_card, h] at h4
  omega

end ConfL2

open KGL33 ConfL2 in
theorem factConfL2_holds :
    FactConfL2 := by
  intro G _ _ K X Q a z l p hqs hFM hm hconf
  obtain ⟨hKX, hXN, hQ, haQ, hzQ, -, -, haC, hzC, ha1, hz1, haz, -, hlN, hlodd, hla, hlz⟩ :=
    hconf
  have hp : p.Prime := hFM.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := ne_two_of_fermat_or_mersenne hFM
  have hp5 : 5 ≤ p := by
    obtain ⟨F, _, _, _, -, hF, -, h5⟩ := K1.psl2_model_data hp2 hm
    rwa [hF, pow_one] at h5
  obtain ⟨e⟩ := Vol2Native.A312L.equiv_psl2_zmod_of_model hm
  have hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, by rw [Nat.card_zmod, pow_one]⟩
  have hcard : 3 < Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  have hsimp : IsSimpleGroup (PSL2 (ZMod p)) := Vol2.Ch11.SecB.isSimpleGroup_psl2 hp5
  have hnab : ∃ x y : PSL2 (ZMod p), x * y ≠ y * x := by
    obtain ⟨-, -, a', b', hab⟩ := hqs
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b'
    refine ⟨e a', e b', fun h => hab ?_⟩
    rw [← map_mul, ← map_mul] at h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e.injective h]
  have hZ : ∀ x : PSL2 (ZMod p), (∀ y, x * y = y * x) → x = 1 := by
    intro x hx
    have hxZ : x ∈ Subgroup.center (PSL2 (ZMod p)) :=
      Subgroup.mem_center_iff.mpr fun y => (hx y).symm
    rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2 (ZMod p))) with h | h
    · rw [h] at hxZ
      exact hxZ
    · exfalso
      obtain ⟨x', y', hxy⟩ := hnab
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x') y').symm
  have hZK : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → x = 1 := by
    intro x hx
    apply e.injective
    rw [map_one]
    refine hZ _ fun y => ?_
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx y]
  have hconj : Function.Injective (MulAut.conj : PSL2 (ZMod p) →* MulAut (PSL2 (ZMod p))) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => hZ x fun y => ?_
    have := congrArg (fun f : MulAut (PSL2 (ZMod p)) => f y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  obtain ⟨PK, hPKQ⟩ := exists_sylow_le hKX hXN hQ
  have fixP : ∀ c ∈ Q, (∀ t ∈ Q, c * t * c⁻¹ * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) →
      ∀ t ∈ (PK : Subgroup ↥K), c * (t : G) * c⁻¹ = t := by
    intro c hcQ hc t ht
    have hcN : c ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 hcQ)
    have h1 := hc t (hPKQ t ht)
    have h2 : c * (t : G) * c⁻¹ * (t : G)⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.1 hcN t).1 t.2) (K.inv_mem t.2)
    have h3 : (⟨_, h2⟩ : ↥K) = 1 := hZK _ fun y => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 h1 y y.2).symm
    have h4 : c * (t : G) * c⁻¹ * (t : G)⁻¹ = 1 := congrArg Subtype.val h3
    calc c * (t : G) * c⁻¹ = (c * (t : G) * c⁻¹ * (t : G)⁻¹) * t := by group
      _ = t := by rw [h4, one_mul]
  obtain ⟨P, hP⟩ : ∃ P : Sylow 2 (PSL2 (ZMod p)),
      (P : Subgroup (PSL2 (ZMod p))) = (PK : Subgroup ↥K).map e.toMonoidHom :=
    ⟨PK.mapSurjective (f := e.toMonoidHom) e.surjective, Sylow.coe_mapSurjective _ _⟩
  have hmemP : ∀ t ∈ (P : Subgroup (PSL2 (ZMod p))), ∃ t' ∈ (PK : Subgroup ↥K), e t' = t := by
    intro t ht
    rw [hP] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    exact ⟨t', ht', rfl⟩
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 haQ)
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 hzQ)
  have fixAct : ∀ c ∈ Q, (∀ t ∈ Q, c * t * c⁻¹ * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) →
      ∀ hcN : c ∈ Subgroup.normalizer (K : Set G),
      ∀ t ∈ (P : Subgroup (PSL2 (ZMod p))), actHom K e ⟨c, hcN⟩ t = t := by
    intro c hcQ hc hcN t ht
    obtain ⟨t', ht', rfl⟩ := hmemP t ht
    rw [actHom_apply]
    congr 1
    exact Subtype.ext (fixP c hcQ hc t' ht')
  obtain ⟨m, hm1, ⟨eP⟩⟩ := psl2_odd_hasDihedralSylowTwo_model (ZMod p) hK P
  obtain ⟨V, hVP, hV⟩ :=
    exists_kleinFour_le_of_dihedral_subgroup_mulEquiv (P : Subgroup (PSL2 (ZMod p))) hm1 eP
  obtain ⟨va, hvaV, hγa⟩ := exists_mem_kleinFour hK hcard hV (actHom K e ⟨a, haN⟩)
    fun t ht => fixAct a haQ haC haN t (hVP ht)
  obtain ⟨vz, hvzV, hγz⟩ := exists_mem_kleinFour hK hcard hV (actHom K e ⟨z, hzN⟩)
    fun t ht => fixAct z hzQ hzC hzN t (hVP ht)
  have hcentP : ∀ c ∈ Q, (∀ t ∈ Q, c * t * c⁻¹ * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) →
      ∀ hcN : c ∈ Subgroup.normalizer (K : Set G), ∀ v : PSL2 (ZMod p),
      actHom K e ⟨c, hcN⟩ = MulAut.conj v →
      ∀ t ∈ (P : Subgroup (PSL2 (ZMod p))), v * t = t * v := by
    intro c hcQ hc hcN v hv t ht
    have h1 := fixAct c hcQ hc hcN t ht
    rw [hv, MulAut.conj_apply] at h1
    calc v * t = v * t * v⁻¹ * v := by group
      _ = t * v := by rw [h1]
  have hva1 : va ≠ 1 := by
    rintro rfl
    rw [map_one] at hγa
    exact ha1 (mem_centralizer_of_actHom_eq_one K e hγa)
  have hvz1 : vz ≠ 1 := by
    rintro rfl
    rw [map_one] at hγz
    exact hz1 (mem_centralizer_of_actHom_eq_one K e hγz)
  have hvaz : va ≠ vz := by
    intro h
    have hN : a * z⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ haN (Subgroup.inv_mem _ hzN)
    have he : (⟨a * z⁻¹, hN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨a, haN⟩ * (⟨z, hzN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := rfl
    have h1 : actHom K e ⟨a * z⁻¹, hN⟩ = 1 := by
      rw [he, map_mul, map_inv, hγa, hγz, h, mul_inv_cancel]
    exact haz (mem_centralizer_of_actHom_eq_one K e h1)
  have hord2 : ∀ v ∈ V, v ≠ 1 → orderOf v = 2 := by
    intro v hv hv1
    have h2 : orderOf (⟨v, hv⟩ : ↥V) ∣ 2 := by
      have h := Monoid.order_dvd_exponent (⟨v, hv⟩ : ↥V)
      rwa [hV.exponent_two] at h
    rw [Subgroup.orderOf_mk] at h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hv1
    · exact h
  have hCva := CFSG.Walter.psl2_centralizer_involution (ZMod p) (p := p) (f := 1)
    (by rw [Nat.card_zmod, pow_one]) (hp.odd_of_ne_two hp2) one_pos (hord2 va hvaV hva1)
  rcases Nat.lt_or_ge p 7 with hp7 | hp7
  ·
    have hp5' : p = 5 := by
      rcases (show p = 5 ∨ p = 6 by omega) with h | h
      · exact h
      · exact absurd (h ▸ hp) (by norm_num)
    let lam := actHom K e ⟨l, hlN⟩
    have hlamodd : Odd (orderOf lam) := by
      refine hlodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
      have h1 : (⟨l, hlN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf l = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one])
      show (actHom K e ⟨l, hlN⟩) ^ orderOf l = 1
      rw [← map_pow, h1, map_one]
    obtain ⟨k, hk⟩ := exists_conj_of_odd hK hcard lam hlamodd
    have hcomm : k * va = va * k := by
      have hN : l * a * l⁻¹ * a⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN haN)
          (Subgroup.inv_mem _ hlN)) (Subgroup.inv_mem _ haN)
      have h1 : actHom K e ⟨_, hN⟩ = 1 := actHom_eq_one_of_mem_centralizer K e hla
      have he : (⟨_, hN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          ⟨l, hlN⟩ * ⟨a, haN⟩ * (⟨l, hlN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ *
            (⟨a, haN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := rfl
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      change lam * _ * lam⁻¹ * _ = 1 at h1
      rw [hk, hγa, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h1
      have h3 : k * va * k⁻¹ * va⁻¹ = 1 := hconj (h1.trans (map_one _).symm)
      calc k * va = (k * va * k⁻¹ * va⁻¹) * va * k := by group
        _ = va * k := by rw [h3, one_mul]
    have hkC : k ∈ Subgroup.centralizer ({va} : Set (PSL2 (ZMod p))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have hk4 : orderOf k ∣ 4 := by
      have h1 := orderOf_dvd_natCard
        (⟨k, hkC⟩ : ↥(Subgroup.centralizer ({va} : Set (PSL2 (ZMod p)))))
      rw [Subgroup.orderOf_mk, (hCva.1 (by rw [pow_one]; omega)).1] at h1
      have h4 : p ^ 1 - 1 = 4 := by rw [pow_one]; omega
      rwa [h4] at h1
    have hkodd : Odd (orderOf k) := by
      rw [← orderOf_injective MulAut.conj hconj k, ← hk]
      exact hlamodd
    have hk1 : k = 1 := by
      rw [← orderOf_eq_one_iff]
      have h := Nat.le_of_dvd (by norm_num) hk4
      have h0 : 0 < orderOf k := hkodd.pos
      interval_cases h1 : orderOf k
      · rfl
      · exact absurd hkodd (by decide)
      · exact absurd hk4 (by decide)
      · exact absurd hkodd (by decide)
    have hlam1 : lam = 1 := by rw [hk, hk1, map_one]
    have hN : l * z * l⁻¹ * z⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hzN)
        (Subgroup.inv_mem _ hlN)) (Subgroup.inv_mem _ hzN)
    have he : (⟨_, hN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨l, hlN⟩ * ⟨z, hzN⟩ * (⟨l, hlN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ *
          (⟨z, hzN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := rfl
    have h1 : actHom K e ⟨_, hN⟩ = 1 := by
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv]
      change lam * _ * lam⁻¹ * _ = 1
      rw [hlam1, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact hlz (mem_centralizer_of_actHom_eq_one K e h1)
  ·
    have h8 := mod_eight_of_fermat_or_mersenne hFM hp7
    have h8C : 8 ∣ Nat.card (Subgroup.centralizer ({va} : Set (PSL2 (ZMod p)))) := by
      rcases h8 with h | h
      · rw [(hCva.1 (by rw [pow_one]; omega)).1, pow_one]
        omega
      · rw [(hCva.2 (by rw [pow_one]; omega)).1, pow_one]
        omega
    have h8P : 2 ^ 3 ∣ Nat.card (P : Subgroup (PSL2 (ZMod p))) :=
      P.pow_dvd_card_of_pow_dvd_card (h8C.trans (Subgroup.card_subgroup_dvd_card _))
    have hPcard : Nat.card (P : Subgroup (PSL2 (ZMod p))) = 2 * 2 ^ m := by
      rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
    have hm4 : 4 ≤ 2 ^ m := by
      rw [hPcard] at h8P
      have h4 : 4 ∣ 2 ^ m := by omega
      exact Nat.le_of_dvd (by positivity) h4
    have hcen : Nat.card (Subgroup.center (P : Subgroup (PSL2 (ZMod p)))) = 2 := by
      rw [Nat.card_congr (Subgroup.centerCongr eP).toEquiv]
      exact CFSG.Walter.card_center_dihedralGroup hm4
        (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have hmemZ : ∀ v (hv : v ∈ V), (∀ t ∈ (P : Subgroup (PSL2 (ZMod p))), v * t = t * v) →
        (⟨v, hVP hv⟩ : ↥(P : Subgroup (PSL2 (ZMod p)))) ∈
          Subgroup.center ↥(P : Subgroup (PSL2 (ZMod p))) := by
      intro v hv hvc
      rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext (hvc t t.2).symm
    have hZa := hmemZ va hvaV (hcentP a haQ haC haN va hγa)
    have hZz := hmemZ vz hvzV (hcentP z hzQ hzC hzN vz hγz)
    have hne : ∀ v (hv : v ∈ V)
        (hc : (⟨v, hVP hv⟩ : ↥(P : Subgroup (PSL2 (ZMod p)))) ∈
          Subgroup.center ↥(P : Subgroup (PSL2 (ZMod p)))), v ≠ 1 →
        (⟨⟨v, hVP hv⟩, hc⟩ : ↥(Subgroup.center ↥(P : Subgroup (PSL2 (ZMod p))))) ≠ 1 := by
      intro v hv hc hv1 h
      exact hv1 (congrArg
        (fun x : ↥(Subgroup.center ↥(P : Subgroup (PSL2 (ZMod p)))) => (x.1.1 : PSL2 (ZMod p))) h)
    have := eq_of_card_eq_two hcen (x := ⟨_, hZa⟩) (y := ⟨_, hZz⟩)
      (hne va hvaV hZa hva1) (hne vz hvzV hZz hvz1)
    exact hvaz (congrArg
      (fun x : ↥(Subgroup.center ↥(P : Subgroup (PSL2 (ZMod p)))) => (x.1.1 : PSL2 (ZMod p))) this)

end CFSG.Quasithin.H13.A5
