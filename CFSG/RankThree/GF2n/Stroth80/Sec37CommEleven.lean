module

public import CFSG.RankThree.GF2n.Stroth80.Sec37CommStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tim37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem orderOf_four_zmod_eleven : orderOf ((4 : ℕ) : ZMod 11) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem charP_two_of_card_eq_four {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) :
    CharP F 2 := by
  haveI := Fintype.ofFinite F
  obtain ⟨p, hp, n, hpp, hcard⟩ := FiniteField.card' F
  have h4 : p ^ (n : ℕ) = 4 := by rw [← hcard, ← Nat.card_eq_fintype_card, hF]
  have hdvd : p ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
    exact dvd_pow_self p n.ne_zero
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd)
  rw [hp2] at hp
  exact hp

theorem eq_one_of_pow_eleven_eq_one {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : Nat.card F = 4) (hV : Module.finrank F V = 6)
    (B : LinearMap.BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate) {T : V ≃ₗ[F] V}
    (hiso : ∀ x y, B (T x) (T y) = B x y) (hT : T ^ 11 = 1) : T = 1 := by
  by_contra hne
  haveI := charP_two_of_card_eq_four hF
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hord : orderOf T = 11 := orderOf_eq_prime hT hne
  have hodd : Odd (orderOf ((Nat.card F : ℕ) : ZMod 11)) := by
    rw [hF, orderOf_four_zmod_eleven]
    decide
  have h := two_mul_orderOf_le_finrank_of_isometry B hB hnd hiso (p := 11) (by norm_num)
    (by norm_num) hord hne hodd
  rw [hF, orderOf_four_zmod_eleven, hV] at h
  omega

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Lgen_LB_le_H0 (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ H0 M Z := by
  unfold Lgen
  refine iSup₂_le fun m hm x hx => ?_
  refine Subgroup.mem_inf.mpr ⟨conj_le_M hc.LB_le_M hm hx, ?_⟩
  rw [← hc.LB_conj hm] at hx
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact (mul_inv_eq_iff_eq_mul.mp ((hc.conj_of_mem hm).LB_centralizes_Z hx z hz)).symm

end

theorem eleven37 : Eleven37Statement := by
  intro G _ _ M Q Z B _ hc hw hZ h11
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨k, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, -, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp h
  have hK : Nat.card (GaloisField 2 k) = 4 := h.card.trans hZ
  have hdim : Module.finrank (GaloisField 2 k) M₀.E = 6 := by
    rw [h.finrank_E hw (by rw [hK]; norm_num)]
  have hnd : M₀.B.Nondegenerate :=
    ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
      rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 11 h11
  obtain ⟨y, hyS, hyx⟩ := Subgroup.mem_map.mp x.2
  have hyH : (y : G) ∈ H0 M Z := Lgen_LB_le_H0 hc hyS
  have hx11 : (x : ↥M ⧸ Q.subgroupOf M) ^ 11 = 1 := by
    have := congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
    simpa using this
  have hx1 : (x : ↥M ⧸ Q.subgroupOf M) ≠ 1 := by
    intro h1
    have h2 : x = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hx
    norm_num at hx
  have hy11 : (y : G) ^ 11 ∈ Q := by
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (y ^ 11) = 1 := by
      rw [map_pow, hyx]
      exact hx11
    have h2 := (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (y ^ 11)).mp h1
    simpa using Subgroup.mem_subgroupOf.mp h2
  have hyQ : (y : G) ∉ Q := by
    intro hyQ
    apply hx1
    rw [← hyx]
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) y).mpr
      (Subgroup.mem_subgroupOf.mpr hyQ)
  set g : ↥(H0 M Z) := ⟨(y : G), hyH⟩ with hg
  have hT11 : φ g ^ 11 = 1 := by
    rw [← map_pow]
    exact (hφker _).mpr (by simpa [hg] using hy11)
  have hT1 : φ g ≠ 1 := fun h1 => hyQ ((hφker g).mp h1)
  have hiso : ∀ e f, M₀.B (φ g e) (φ g f) = M₀.B e f := by
    intro e f
    have h1 := M₀.Qf_add (φ g e) (φ g f)
    have h2 := M₀.Qf_add e f
    rw [← map_add, hφQ g, hφQ g e, hφQ g f] at h1
    linear_combination h2 - h1
  exact hT1 (eq_one_of_pow_eleven_eq_one hK hdim M₀.B (fun e => M₀.alt e) hnd hiso hT11)

end CFSG.RankThree.GF2n.Stroth80.Tim37
