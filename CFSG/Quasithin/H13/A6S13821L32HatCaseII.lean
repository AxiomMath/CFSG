module

public import CFSG.Quasithin.H13.A6S13821L32HatPi
public import CFSG.Quasithin.H13.A6S13821L32HatL0
public import CFSG.Quasithin.H13.A6S13821L32HatSL3

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open Equiv

namespace L32HatStep

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem eq_one_of_pow_three_pow_two {A : Type*} [Group A] {x : A} {k : ℕ} (h3 : x ^ 3 = 1)
    (h2 : x ^ 2 ^ k = 1) : x = 1 := by
  have d3 := orderOf_dvd_of_pow_eq_one h3
  have d2 := orderOf_dvd_of_pow_eq_one h2
  have hg : orderOf x ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd d3 d2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by decide))] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

theorem caseII_false {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz) (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hXK : S.X13820 ≤ K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have P := S.plusData_X13820
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
  obtain ⟨π, hπ, hker, hD⟩ := exists_pi_sl3 hK hKn hTsylH hP'
  have hL0K : l0 L ≤ K := S.l0_le_of_hat h139 h37 h38 hhat hH hK hKn hP
  have hXgen : S.X13820 ≤ oTwoUpper S.X13820 := P.eq.le
  have hL0gen : l0 L ≤ oTwoUpper (l0 L) := S.oTwoUpper_l0.symm.le
  have hXL1 : S.X13820 ≤ S.L1 := P.le_L1
  have hL0L1 : l0 L ≤ S.L1 := S.l0_le_L1
  set Xs : Subgroup SL3.S := (S.X13820.subgroupOf K).map π with hXsdef
  set Ls : Subgroup SL3.S := ((l0 L).subgroupOf K).map π with hLsdef
  have hXs_le : Xs ≤ oTwoUpper Xs := image_le_oTwoUpper hXK hXgen
  have hLs_le : Ls ≤ oTwoUpper Ls := image_le_oTwoUpper hL0K hL0gen
  have hTX : ∀ t ∈ T, ∀ z ∈ S.X13820, t * z * t⁻¹ ∈ S.X13820 := fun t ht z hz =>
    (Subgroup.mem_normalizer_iff.mp (P.T_le ht) z).mp hz
  have hTl0 : ∀ t ∈ T, ∀ z ∈ l0 L, t * z * t⁻¹ ∈ l0 L := fun t ht z hz =>
    (Subgroup.mem_normalizer_iff.mp (S.frame.T_le.trans S.normalizer_le_l0 ht) z).mp hz
  have hPXs : SL3.P0 ≤ Subgroup.normalizer (Xs : Set SL3.S) :=
    P0_le_normalizer_image hD hXK hTX
  have hPLs : SL3.P0 ≤ Subgroup.normalizer (Ls : Set SL3.S) :=
    P0_le_normalizer_image hD hL0K hTl0
  set Q : Subgroup SL3.S := ((S.L1 ⊔ T).subgroupOf K).map π with hQdef
  have hXQ : Xs ≤ Q := Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_sup_left (hXL1 (Subgroup.mem_subgroupOf.mp hx)))
  have hLQ : Ls ≤ Q := Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_sup_left (hL0L1 (Subgroup.mem_subgroupOf.mp hx)))
  have hPQ : SL3.P0 ≤ Q := by
    rw [← hD]
    exact Subgroup.map_mono fun t ht => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp ht))
  have hW : (Xs ⊔ Ls) ⊔ SL3.P0 ≤ Q := sup_le (sup_le hXQ hLQ) hPQ
  have hWc := SL3.overgroups_SL3 ((Xs ⊔ Ls) ⊔ SL3.P0) le_sup_right
  have hτC : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ∈ S14.C3 := by decide
  have hτ3 : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ^ 3 = 1 := by decide
  have hτ1 : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ≠ 1 := by decide
  obtain ⟨x₀N, hx₀X, hρx₀⟩ := P.three _ hτC
  have hx₀K : (x₀N : G) ∈ K := hXK hx₀X
  have hx₀O : (x₀N : G) ∉ pCoreOf 2 K := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨(x₀N : G), h⟩
    have hk' : (x₀N : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hk'' : x₀N ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    have hτ2 : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ^ 2 ^ k = 1 := by
      rw [← hρx₀, ← map_pow, hk'', map_one]
    exact hτ1 (eq_one_of_pow_three_pow_two hτ3 hτ2)
  have hπx₀ : π ⟨(x₀N : G), hx₀K⟩ ≠ 1 := fun h => hx₀O ((hker _).mp h)
  have hXs_ne : Xs ≠ ⊥ := by
    intro h
    apply hπx₀
    have hmem : π ⟨(x₀N : G), hx₀K⟩ ∈ Xs :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx₀X)
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := l0_decomp hhat
  have hc1 : c ≠ 1 := fun h1 => hcO (h1 ▸ Subgroup.one_mem _)
  have hcK : c ∈ K := hL0K hcl0
  have hcOK : c ∉ pCoreOf 2 K := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨c, h⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hc1 (eq_one_of_pow_three_pow_two hc3 hk')
  have hπc : π ⟨c, hcK⟩ ≠ 1 := fun h => hcOK ((hker _).mp h)
  have hLs_ne : Ls ≠ ⊥ := by
    intro h
    apply hπc
    have hmem : π ⟨c, hcK⟩ ∈ Ls := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hcl0)
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  have hρcontra : Xs = Ls → False := by
    intro hXL
    have hmem : π ⟨(x₀N : G), hx₀K⟩ ∈ Ls :=
      hXL ▸ Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx₀X)
    obtain ⟨l, hl, hπl⟩ := Subgroup.mem_map.mp hmem
    have hpo : π (l⁻¹ * ⟨(x₀N : G), hx₀K⟩) = 1 := by
      rw [map_mul, map_inv, hπl, inv_mul_cancel]
    have hoO : ((l⁻¹ * ⟨(x₀N : G), hx₀K⟩ : ↥K) : G) ∈ pCoreOf 2 K := (hker _).mp hpo
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨_, hoO⟩
    have hk' : ((l⁻¹ * ⟨(x₀N : G), hx₀K⟩ : ↥K) : G) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hl0 : (l : G) ∈ l0 L := Subgroup.mem_subgroupOf.mp hl
    have hlC : (l : G) ∈ Subgroup.centralizer (V : Set G) :=
      S.o2Z_le_centralizer (oTwoRes_le _ hl0)
    have hlN : (l : G) ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.centralizer_le_normalizer _ hlC
    set lN : ↥(Subgroup.normalizer (V : Set G)) := ⟨(l : G), hlN⟩ with hlNdef
    have hρl : S.frame.ρ lN = 1 := (S.rho_eq_one_iff lN).mpr hlC
    set oN : ↥(Subgroup.normalizer (V : Set G)) := lN⁻¹ * x₀N with hoNdef
    have hoNG : (oN : G) = ((l⁻¹ * ⟨(x₀N : G), hx₀K⟩ : ↥K) : G) := by
      simp [oN, lN]
    have hpowN : oN ^ 2 ^ k = 1 := Subtype.ext (by
      simpa [hoNG] using hk')
    have hτ2 : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ^ 2 ^ k = 1 := by
      rw [← hρx₀]
      have hx : x₀N = lN * oN := by simp [oN]
      rw [hx, map_mul, hρl, one_mul, ← map_pow, hpowN, map_one]
    exact hτ1 (eq_one_of_pow_three_pow_two hτ3 hτ2)
  rcases hWc with hW0 | hW1 | hW2 | hWt
  ·
    obtain ⟨y, hyX, hy1, hyo⟩ := L32HatSL3.exists_odd_ne_one hXs_le hXs_ne
    have hyP : y ∈ SL3.P0 := by
      have : Xs ≤ SL3.P0 := by
        rw [← hW0]
        exact le_sup_left.trans le_sup_left
      exact this hyX
    have hyX1 : SL3.InX1 y := (inf_le_left : SL3.P0 ≤ SL3.X1) hyP
    have hyX2 : SL3.InX2 y := (inf_le_right : SL3.P0 ≤ SL3.X2) hyP
    have hy3 : y ^ 3 = 1 := L32HatSL3.pow_three_eq_one_of_odd (L32HatSL3.X1_pow_24 y hyX1) hyo
    have hyT : y ∈ L32HatSL3.T3X1 := by
      simp only [L32HatSL3.T3X1, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hyX1, hy3, hy1⟩
    exact L32HatSL3.T3X1_not_InX2 y hyT hyX2
  ·
    have hXsX1 : Xs ≤ SL3.X1 := by
      have : Xs ≤ (Xs ⊔ Ls) ⊔ SL3.P0 := le_sup_left.trans le_sup_left
      rw [hW1] at this
      exact this
    have hLsX1 : Ls ≤ SL3.X1 := by
      have : Ls ≤ (Xs ⊔ Ls) ⊔ SL3.P0 := le_sup_right.trans le_sup_left
      rw [hW1] at this
      exact this
    exact hρcontra ((L32HatSL3.fA4_X1 hXsX1 hPXs hXs_le hXs_ne).trans
      (L32HatSL3.fA4_X1 hLsX1 hPLs hLs_le hLs_ne).symm)
  ·
    have hXsX2 : Xs ≤ SL3.X2 := by
      have : Xs ≤ (Xs ⊔ Ls) ⊔ SL3.P0 := le_sup_left.trans le_sup_left
      rw [hW2] at this
      exact this
    have hLsX2 : Ls ≤ SL3.X2 := by
      have : Ls ≤ (Xs ⊔ Ls) ⊔ SL3.P0 := le_sup_right.trans le_sup_left
      rw [hW2] at this
      exact this
    exact hρcontra ((L32HatSL3.fA4_X2 hXsX2 hPXs hXs_le hXs_ne).trans
      (L32HatSL3.fA4_X2 hLsX2 hPLs hLs_le hLs_ne).symm)
  ·
    have hQtop : Q = ⊤ := eq_top_iff.mpr (hWt ▸ hW)
    have hKle : K ≤ (K ⊓ (S.L1 ⊔ T)) ⊔ pCoreOf 2 K := by
      intro k hk
      have hπk : π ⟨k, hk⟩ ∈ Q := by
        rw [hQtop]
        exact Subgroup.mem_top _
      obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp hπk
      have h1 : π (a⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hak, inv_mul_cancel]
      have h2 : ((a⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := (hker _).mp h1
      have haK : (a : G) ∈ K ⊓ (S.L1 ⊔ T) := ⟨a.2, Subgroup.mem_subgroupOf.mp ha⟩
      have e : (k : G) = (a : G) * ((a⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
      rw [e]
      exact Subgroup.mul_mem_sup haK h2
    have hsolv : Group.IsSolvable ↥((K ⊓ (S.L1 ⊔ T)) ⊔ pCoreOf 2 K) := by
      haveI := S.isSolvable_L1T h1334 hS
      haveI hNsolv : Group.IsSolvable ↥(pCoreOf 2 K) := by
        haveI := IsPGroup.isNilpotent (pCoreOf_isPGroup 2 K)
        infer_instance
      haveI hTsolv : Group.IsSolvable ↥(K ⊓ (S.L1 ⊔ T)) :=
        Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : K ⊓ (S.L1 ⊔ T) ≤ S.L1 ⊔ T)).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe (inf_le_right : K ⊓ (S.L1 ⊔ T) ≤ S.L1 ⊔ T)).surjective
      have hTN : K ⊓ (S.L1 ⊔ T) ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
        inf_le_left.trans ((Subgroup.le_normalizer).trans
          (normalizer_le_normalizer_pCoreOf 2 K))
      rw [sup_comm]
      exact CFSG.Quasithin.C126.isSolvable_sup_of_le_normalizer' hTN ‹_› hTsolv
    have hKs : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKle)
        (Subgroup.inclusion_injective hKle)
    exact not_isSolvable_of_mem_cComp hK hKs

end L32HatStep

end CFSG.Quasithin.H13.A6
