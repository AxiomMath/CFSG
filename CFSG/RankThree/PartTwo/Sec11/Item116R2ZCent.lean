module

public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.OutThreeCore

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem centralizer_zpowers_eq_centralizer_singleton {G : Type*} [Group G] (g : G) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem map_mk_centralizer_eq {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {d : X} (hd3 : d ^ 3 = 1) :
    (Subgroup.centralizer ({d} : Set X)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer ({(QuotientGroup.mk d : X ⧸ N)} : Set (X ⧸ N)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 (Subgroup.zpowers d) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hd3
  have hcen := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 N hN
    (Subgroup.zpowers d) hA
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq_centralizer_singleton,
    centralizer_zpowers_eq_centralizer_singleton] at hcen
  exact hcen

theorem mem_sylow_centralizer_of_pow_three {X : Type} [Group X] [Finite X] {d : X} (hd3 : d ^ 3 = 1)
    (P : Subgroup X) (hPle : P ≤ Subgroup.centralizer ({d} : Set X))
    (hPcard : Nat.card P = 3 ^ (Nat.card (Subgroup.centralizer ({d} : Set X))).factorization 3) :
    d ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdC0 : d ∈ Subgroup.centralizer ({d} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set C : Subgroup X := Subgroup.centralizer ({d} : Set X) with hCdef
  set dC : C := ⟨d, hdC0⟩ with hdCdef
  have hdC3 : dC ^ 3 = 1 := Subtype.ext hd3
  have hcomm : ∀ g : C, g * dC = dC * g := by
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  haveI hnorm : (Subgroup.zpowers dC).Normal := by
    apply Subgroup.normal_of_le_center
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    exact hcomm
  have hP : IsPGroup 3 (Subgroup.zpowers dC) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hdC3
  have hcard : Nat.card (P.subgroupOf C) = 3 ^ (Nat.card C).factorization 3 := by
    rw [← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv
  have hS : (Sylow.ofCard (P.subgroupOf C) hcard : Subgroup C) = P.subgroupOf C :=
    Sylow.coe_ofCard _ _
  have hdS : dC ∈ P.subgroupOf C := by
    rw [← hS]
    exact IsPGroup.le_sylow_of_normal hP (Sylow.ofCard (P.subgroupOf C) hcard)
      (Subgroup.mem_zpowers dC)
  exact Subgroup.mem_subgroupOf.mp hdS

theorem exists_sylow_of_invariant_subgroup_three {X : Type} [Group X] [Finite X] (φ : MulAut X)
    (hφ3 : φ ^ 3 = 1) (C : Subgroup X) (hC : ∀ x ∈ C, φ x ∈ C) :
    ∃ P : Subgroup X, P ≤ C ∧ Nat.card P = 3 ^ (Nat.card C).factorization 3 ∧
      ∀ x ∈ P, φ x ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ∀ y : X, φ (φ (φ y)) = y := by
    intro y
    have h := congrArg (fun f : MulAut X => f y) hφ3
    simpa [pow_three'] using h
  have hsymm : ∀ x : X, φ.symm x = φ (φ x) := by
    intro x
    have h := h3 (φ.symm x)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hC' : ∀ x ∈ C, φ.symm x ∈ C := by
    intro x hx
    rw [hsymm]
    exact hC _ (hC _ hx)
  let φC : MulAut C :=
    { toFun := fun x => ⟨φ x.1, hC x.1 x.2⟩
      invFun := fun x => ⟨φ.symm x.1, hC' x.1 x.2⟩
      left_inv := fun x => Subtype.ext (MulEquiv.symm_apply_apply φ x.1)
      right_inv := fun x => Subtype.ext (MulEquiv.apply_symm_apply φ x.1)
      map_mul' := fun x y => Subtype.ext (map_mul φ x.1 y.1) }
  have hφC_apply : ∀ x : C, ((φC x : C) : X) = φ (x : X) := fun x => rfl
  have hiter : ∀ (n : ℕ) (x : C), (((φC ^ n) x : C) : X) = (φ ^ n) (x : X) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; simp only [pow_succ, MulAut.mul_apply, ih, hφC_apply]
  have hφC3 : φC ^ 3 = 1 := by
    refine MulEquiv.ext (fun x => Subtype.ext ?_)
    simp only [hiter, hφ3, MulAut.one_apply]
  obtain ⟨Q, hQ⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.exists_sylow_map_eq_of_pow_eq_one
      (p := 3) (n := 1) φC (by simpa using hφC3)
  refine ⟨(Q : Subgroup C).map C.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact (Subgroup.card_subtype C (Q : Subgroup C)).trans (Sylow.card_eq_multiplicity Q)
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨φC q, hQ q hq, rfl⟩

theorem exists_invariant_sylow_centralizer {X : Type} [Group X] [Finite X] (φ : MulAut X)
    (hφ3 : φ ^ 3 = 1) {d : X} (hφd : φ d = d) :
    ∃ P : Subgroup X, P ≤ Subgroup.centralizer ({d} : Set X) ∧
      Nat.card P = 3 ^ (Nat.card (Subgroup.centralizer ({d} : Set X))).factorization 3 ∧
      ∀ x ∈ P, φ x ∈ P := by
  refine exists_sylow_of_invariant_subgroup_three φ hφ3 (Subgroup.centralizer ({d} : Set X)) ?_
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have h := congrArg (⇑φ) hx
  rwa [map_mul, map_mul, hφd] at h

theorem card_map_mk_mul_card_inf_of_normal {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (H : Subgroup X) :
    Nat.card (H.map (QuotientGroup.mk' N)) * Nat.card ↥(H ⊓ N) = Nat.card H := by
  let ψ : H →* X ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hker : ψ.ker.map H.subtype = H ⊓ N := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (QuotientGroup.eq_one_iff (N := N) (y : X)).mp (MonoidHom.mem_ker.mp hy)⟩
    · rintro ⟨hxH, hxN⟩
      exact ⟨⟨x, hxH⟩, MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff (N := N) x).mpr hxN), rfl⟩
  have hrange : ψ.range = H.map (QuotientGroup.mk' N) := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h2 : Nat.card ψ.ker = Nat.card ↥(H ⊓ N) := by
    rw [← hker, Subgroup.card_map_of_injective H.subtype_injective]
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [hrange, h2] at h1
  rw [Nat.mul_comm]
  exact h1

theorem card_map_mk_sylow {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {d : X} (hd3 : d ^ 3 = 1) (P : Subgroup X)
    (hPle : P ≤ Subgroup.centralizer ({d} : Set X))
    (hPcard : Nat.card P = 3 ^ (Nat.card (Subgroup.centralizer ({d} : Set X))).factorization 3) :
    Nat.card (P.map (QuotientGroup.mk' N)) =
        3 ^ (Nat.card (Subgroup.centralizer ({(QuotientGroup.mk d : X ⧸ N)} : Set (X ⧸ N)))).factorization 3 ∧
      P ⊓ N = ⊥ := by
  have hcop : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN
  have hPdvd : Nat.card ↥(P ⊓ N) ∣
      3 ^ (Nat.card (Subgroup.centralizer ({d} : Set X))).factorization 3 := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le (_root_.inf_le_left : P ⊓ N ≤ P)
  have hPN1 : Nat.card ↥(P ⊓ N) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left hPdvd (Nat.Coprime.pow_left _ hcop))
      (Subgroup.card_dvd_of_le (_root_.inf_le_right : P ⊓ N ≤ N))
  have hPbot : P ⊓ N = ⊥ := Subgroup.card_eq_one.mp hPN1
  have hPimg : Nat.card (P.map (QuotientGroup.mk' N)) = Nat.card P := by
    have h := card_map_mk_mul_card_inf_of_normal N P
    rw [hPN1, Nat.mul_one] at h
    exact h
  have hCN : Nat.card ↥(Subgroup.centralizer ({d} : Set X) ⊓ N) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le (_root_.inf_le_right : Subgroup.centralizer ({d} : Set X) ⊓ N ≤ N)
  have hbz : (Nat.card ↥(Subgroup.centralizer ({d} : Set X) ⊓ N)).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => hN (dvd_trans h hCN))
  have hCimg := card_map_mk_mul_card_inf_of_normal N (Subgroup.centralizer ({d} : Set X))
  rw [map_mk_centralizer_eq N hN hd3] at hCimg
  have ha : Nat.card (Subgroup.centralizer ({(QuotientGroup.mk d : X ⧸ N)} : Set (X ⧸ N))) ≠ 0 :=
    Nat.card_pos.ne'
  have hb : Nat.card ↥(Subgroup.centralizer ({d} : Set X) ⊓ N) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card (Subgroup.centralizer ({d} : Set X))).factorization 3 =
      (Nat.card (Subgroup.centralizer ({(QuotientGroup.mk d : X ⧸ N)} : Set (X ⧸ N)))).factorization 3 +
        (Nat.card ↥(Subgroup.centralizer ({d} : Set X) ⊓ N)).factorization 3 := by
    rw [← hCimg, Nat.factorization_mul ha hb, Finsupp.add_apply]
  refine ⟨?_, hPbot⟩
  rw [hPimg, hPcard, hfac, hbz, Nat.add_zero]

end CFSG.RankThree.PartTwo.Sec11
