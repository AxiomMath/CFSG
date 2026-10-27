module

public import CFSG.RankThree.PartOne.K133B.Plane
public import CFSG.RankThree.PartOne.K133B.Five
public import CFSG.RankThree.PartOne.Q1327S.Arith
public import CFSG.RankThree.PartOne.S12.Sec127

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem prime_five_or_eleven_le {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) :
    p = 5 ∨ 11 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h5', h11'⟩ := hcon
  interval_cases p
  · exact h5' rfl
  · exact absurd hp (by decide)
  · exact h7 rfl
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)

variable {G : Type} [Group G] [Finite G] {p g : ℕ} {E : Subgroup G} {e : G} {I P : Subgroup G}

theorem dvd_card_center_of_mem (hp : p.Prime) {e : G} {I : Subgroup G} (he1 : e ≠ 1)
    (hep : e ^ p = 1) (hcent : ∀ n ∈ I, e * n = n * e) (heI : e ∈ I) :
    p ∣ Nat.card (Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I)) := by
  set θ := aschbacherSolvableCore p ↥I with hθ
  let e' : ↥I := ⟨e, heI⟩
  have hcent' : QuotientGroup.mk (s := θ) e' ∈ Subgroup.center (↥I ⧸ θ) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcent n n.2).symm
  have he'1 : e' ≠ 1 := fun h1 => he1 (congrArg Subtype.val h1)
  have he'p : e' ^ p = 1 := Subtype.ext hep
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf e' = p := orderOf_eq_prime he'p he'1
  have hmk1 : QuotientGroup.mk (s := θ) e' ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    exact not_dvd_card_theta hp (hord ▸ Subgroup.orderOf_dvd_natCard θ h1)
  have hmkp : (QuotientGroup.mk (s := θ) e') ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, he'p]
    rfl
  have hmkord : orderOf (QuotientGroup.mk (s := θ) e') = p := orderOf_eq_prime hmkp hmk1
  have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center (↥I ⧸ θ)) hcent'
  rwa [hmkord] at h1

theorem e_not_mem (hp : p.Prime) (PD : PlaneData p g E e I P)
    (hZ : Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I) = ⊥) : e ∉ I := by
  intro heI
  have h := dvd_card_center_of_mem hp PD.e_ne PD.e_pow PD.e_cent heI
  rw [hZ, Subgroup.card_bot] at h
  exact hp.one_lt.ne' (Nat.dvd_one.1 h)

theorem inf_le_P (hp : p.Prime) (hE : IsElementaryAbelian p ↥E) (PD : PlaneData p g E e I P)
    (heI : e ∉ I) : E ⊓ I ≤ P := by
  intro y hy
  have hy' : y ∈ Subgroup.zpowers e ⊔ P := by rw [← PD.E_eq]; exact hy.1
  have hcomm : ∀ k ∈ Subgroup.zpowers e, ∀ l ∈ P, k * l = l * k := by
    intro k hk l hl
    have hkE : k ∈ E := by rw [PD.E_eq]; exact Subgroup.mem_sup_left hk
    have hlE : l ∈ E := PD.P_le_E hl
    exact congrArg (fun z : ↥E => (z : G)) (hE.is_comm.comm ⟨k, hkE⟩ ⟨l, hlE⟩)
  obtain ⟨a, ha, z, hz, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hcomm hy'
  have haI : a ∈ I := by
    have := I.mul_mem hy.2 (I.inv_mem (PD.P_le_I hz))
    simpa using this
  have hzv : Nat.card ↥(Subgroup.zpowers e) = p := by
    rw [Nat.card_zpowers]
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime PD.e_pow PD.e_ne
  have hbot : Subgroup.zpowers e ⊓ I = ⊥ := by
    have hd' : Nat.card ↥(Subgroup.zpowers e ⊓ I) ∣ p :=
      hzv ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hd' with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply heI
      have e2 : Subgroup.zpowers e ⊓ I = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hzv])
      have : e ∈ Subgroup.zpowers e ⊓ I := by rw [e2]; exact Subgroup.mem_zpowers e
      exact this.2
  have ha1 : a = 1 := by
    have : a ∈ Subgroup.zpowers e ⊓ I := ⟨ha, haI⟩
    rw [hbot] at this
    exact this
  rw [ha1, one_mul]
  exact hz

theorem fixes_and_stable (hE : IsElementaryAbelian p ↥E) (hp : p.Prime)
    (PD : PlaneData p g E e I P) (heI : e ∉ I) {k : G} (hkI : k ∈ I)
    (hk : k ∈ Subgroup.normalizer (E : Set G)) {PE : Subgroup E} {v : E} (hv : (v : G) = e)
    (hPE : PE.map E.subtype = P) :
    conjAut E k hk v = v ∧ ∀ x ∈ PE, conjAut E k hk x ∈ PE := by
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    rw [Equivariance.coe_conjAut hk v, hv]
    rw [← PD.e_cent k hkI]
    group
  · intro x hx
    have hxP : (x : G) ∈ P := by
      rw [← hPE]
      exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    have hxI : (x : G) ∈ I := PD.P_le_I hxP
    have hI' : (conjAut E k hk x : G) ∈ I := by
      rw [Equivariance.coe_conjAut hk x]
      exact I.mul_mem (I.mul_mem hkI hxI) (I.inv_mem hkI)
    have hP' : (conjAut E k hk x : G) ∈ P := inf_le_P hp hE PD heI ⟨(conjAut E k hk x).2, hI'⟩
    rw [← hPE] at hP'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hP'
    have : y = conjAut E k hk x := Subtype.ext hyx
    rw [← this]
    exact hy

theorem not_dvd_card_torusImage (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElementaryAbelian p ↥E)
    (hcard : Nat.card E = p ^ 3) (hnt : ¬ torusHasTransvection p E)
    (PD : PlaneData p g E e I P) (heI : e ∉ I) : ¬ p ∣ Nat.card ↥(torusImage E I) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype ↥(torusImage E I) := Fintype.ofFinite _
  obtain ⟨φ0, hφ0⟩ := exists_prime_orderOf_dvd_card (G := ↥(torusImage E I)) p
    (by rwa [← Nat.card_eq_fintype_card])
  have hφp : (φ0 : MulAut E) ^ p = 1 := by
    have h1 : φ0 ^ p = 1 := hφ0 ▸ pow_orderOf_eq_one φ0
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hφ1 : (φ0 : MulAut E) ≠ 1 := by
    intro h1
    have : φ0 = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hφ0
    exact hp.one_lt.ne hφ0
  obtain ⟨k, hkI, hk, hkφ⟩ := Sec12Three.mem_torusImage_iff.1 φ0.2
  obtain ⟨PE, v, hv, hPE, hPEcard, hvPE, hEtop⟩ := PD.E_plane
  obtain ⟨hφv, hPEs⟩ := fixes_and_stable hE hp PD heI hkI hk hv hPE
  have hkφ' : conjAut E k hk = (φ0 : MulAut E) := hkφ
  rw [hkφ'] at hφv hPEs
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 hE
  have hT := isAutTransvection_of_decomp hd hcard hφ1 hφp hφv hPEcard hPEs hvPE hEtop
  exact hnt ⟨(φ0 : MulAut E), Sec127.torusImage_le_torusWeyl E I φ0.2, hT⟩

theorem oddDatum_of_planeData (hInsp : Row8U3Inspection) (hOdd : Row8OddInspection)
    (hp : p.Prime) (hE : IsElementaryAbelian p ↥E) (hcard : Nat.card E = p ^ 3)
    (hnt : ¬ torusHasTransvection p E) (PD : PlaneData p g E e I P) :
    OddOrderOneOrThree ↥(torusImage E I) := by
  have hp5 := PD.conf.five_le
  have hp2 : p ≠ 2 := by omega
  set Q := ↥I ⧸ aschbacherSolvableCore p ↥I with hQ
  set Ē : Subgroup Q := (P.subgroupOf I).map (QuotientGroup.mk' (aschbacherSolvableCore p ↥I))
    with hĒ
  have hZ : Subgroup.center Q = ⊥ := (hInsp Q p g Ē trivial PD.conf).1
  have heI : e ∉ I := e_not_mem hp PD hZ
  obtain ⟨ψ⟩ := torusImage_equiv hp PD.e_cent PD.e_pow PD.e_ne heI PD.P_le_I PD.P_elem PD.E_eq
  have hnd := not_dvd_card_torusImage hp hp2 hE hcard hnt PD heI
  have hnd' : ¬ p ∣ Nat.card ↥(torusImage Ē ⊤) := by rwa [← Nat.card_congr ψ.toEquiv]
  have hp7 : p ≠ 7 := Q1327S.ne_seven_of_dvd_two_pow_add_one PD.conf.p_dvd
  have hcases : p = 5 ∨ 11 ≤ p := prime_five_or_eleven_le hp hp5 hp7
  have hconcl : Row8OddConcl p Q Ē := by
    rcases hcases with h5 | h11
    · subst h5
      exact row8OddConcl_five PD.conf
    · exact hOdd Q p g Ē h11 hZ trivial PD.conf
  exact OddOrderOneOrThree.of_mulEquiv ψ.symm (hconcl hnd')

end CFSG.RankThree.PartOne.K133B
