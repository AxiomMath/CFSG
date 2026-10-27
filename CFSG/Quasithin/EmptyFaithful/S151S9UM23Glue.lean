module

public import CFSG.Quasithin.EmptyFaithful.S151S9UDef
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23E2
public import Certificates.Certificate4170
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Quasithin.A312M23 CFSG.Quasithin.A312Words
open scoped Pointwise

theorem index_eq_one_or_two_of_half_le {m : ℕ} (hm : 2 ≤ m)
    {H : Subgroup (Equiv.Perm (Fin m))} (h : m.factorial / 2 ≤ Nat.card H) :
    H.index = 1 ∨ H.index = 2 := by
  have hcard : Nat.card H * H.index = m.factorial := by
    rw [Subgroup.card_mul_index, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  obtain ⟨q, hq⟩ : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) hm
  have hpos := Nat.factorial_pos m
  have hq2 : m.factorial / 2 = q := by omega
  rw [hq2] at h
  have hidx : 0 < H.index := Nat.pos_of_ne_zero (by
    intro h0
    rw [h0] at hcard
    omega)
  by_contra hne
  have h3 : 3 ≤ H.index := by omega
  have := Nat.mul_le_mul_left (Nat.card H) h3
  omega

theorem card_eq_half_or_full_of_half_le {m : ℕ} (hm : 2 ≤ m)
    {H : Subgroup (Equiv.Perm (Fin m))} (h : m.factorial / 2 ≤ Nat.card H) :
    Nat.card H = m.factorial / 2 ∨ Nat.card H = m.factorial := by
  have hcard : Nat.card H * H.index = m.factorial := by
    rw [Subgroup.card_mul_index, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  obtain ⟨q, hq⟩ : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) hm
  have hq2 : m.factorial / 2 = q := by omega
  rcases index_eq_one_or_two_of_half_le hm h with h1 | h2
  · right
    rw [h1] at hcard
    omega
  · left
    rw [h2] at hcard
    omega

theorem alternatingGroup_le_of_half_le {m : ℕ} (hm : 2 ≤ m)
    {H : Subgroup (Equiv.Perm (Fin m))} (h : m.factorial / 2 ≤ Nat.card H) :
    alternatingGroup (Fin m) ≤ H := by
  rcases index_eq_one_or_two_of_half_le hm h with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact le_top
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    have h3 : σ ^ 3 = 1 := by
      have := pow_orderOf_eq_one σ
      rwa [(show σ.IsThreeCycle from hσ).orderOf] at this
    have hσ4 : σ = (σ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    rw [SetLike.mem_coe, hσ4]
    exact Subgroup.sq_mem_of_index_two h2 _

theorem actionDataG_of_perm_hom {X : Type} [Group X] [Finite X] {m k : ℕ} (hm : 5 ≤ m)
    (φ : X →* Equiv.Perm (Fin m)) (hcard : Nat.card X = 2 ^ k * (m.factorial / 2))
    (hrange : m.factorial / 2 ≤ Nat.card φ.range) : ActionDataG X := by
  have halt : alternatingGroup (Fin m) ≤ φ.range :=
    alternatingGroup_le_of_half_le (by omega) hrange
  let ψ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin m) := φ.comp (⊤ : Subgroup X).subtype
  have hψr : ψ.range = φ.range := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  have hk := Subgroup.card_ker_mul_card_range ψ
  rw [hψr, Subgroup.card_top, hcard] at hk
  have hq : 0 < m.factorial / 2 := by
    have : 2 ≤ m.factorial := (Nat.self_le_factorial m).trans' (by omega)
    omega
  have hdvd : Nat.card ψ.ker ∣ 2 ^ k := by
    rcases card_eq_half_or_full_of_half_le (by omega) hrange with h1 | h2
    · rw [h1] at hk
      exact dvd_of_eq (Nat.eq_of_mul_eq_mul_right hq hk)
    · obtain ⟨q, hq2⟩ : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have hqq : m.factorial / 2 = q := by omega
      rw [h2, hqq, hq2] at hk
      have hk' : (Nat.card ψ.ker * 2) * q = 2 ^ k * q := by rw [← hk]; ring
      have hqpos : 0 < q := by omega
      exact Dvd.intro 2 (Nat.eq_of_mul_eq_mul_right hqpos hk')
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨⊤, m, ψ, Subgroup.normal_top, ⟨0, by simp⟩, hm, IsPGroup.of_card ha, ?_⟩
  rw [hψr]
  exact halt

theorem actionData_of_e2Facts {G : Type} [Group G] [Finite G] {α : Type} [MulAction G α]
    {Y : Subgroup G} {k m r : ℕ} {tr : Bool} (hF : E2Facts α Y k m r false tr)
    (hcard : Nat.card Y = 2 ^ k * r) (hm : 5 ≤ m) (hr : r = m.factorial / 2) : ActionData Y := by
  classical
  obtain ⟨ol, t, hdata, -, -, pt, hpt, hYp, -, -, -, -, -, -, -, hE, -⟩ := hF
  let φ := CFSG.Quasithin.A312M23.actHom Y pt hpt hYp
  have hle : Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)} ≤ φ.range := by
    rw [Subgroup.closure_le]
    intro e he
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
    have hgY := hdata.mem g hg
    exact ⟨⟨g, hgY⟩, (rhoFn_of_mem hgY).symm⟩
  have hrange : m.factorial / 2 ≤ Nat.card φ.range := by
    rw [← hr, ← hE]
    exact Subgroup.card_le_of_le hle
  exact actionDataG_of_perm_hom (X := ↥Y) hm φ (by rw [hcard, hr]) hrange

end CFSG.Quasithin.S151S9U
