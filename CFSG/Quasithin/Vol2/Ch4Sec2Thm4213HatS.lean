module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatT
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatChk

public section

namespace CFSG.Quasithin.H13.Ch4.HatS

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Quasithin.H13.Ch4.HatChk CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.A4
open CFSG.QuasithinUnique

variable {n : ℕ}

theorem closure_le_of_gens {M : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    {rA : Array ℕ} (hrA : Rep n rA r) {gs : Array (Array ℕ)}
    (hval : ∀ k < gs.size, validA n gs[k]! = true)
    (hM : ∀ k < gs.size, permOfArr n gs[k]! ∈ M)
    (hcm : ∀ k < gs.size, cmA n gs[k]! rA = true) :
    Subgroup.closure (permsA n gs) ≤
      M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n))) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  show permOfArr n gs[k]! ∈ _
  refine Subgroup.mem_inf.mpr ⟨hM k hk, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (cmA_iff (rep_of_validA (hval k hk)) hrA).1 (hcm k hk)

theorem closure_conj_le {M : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    {gs : Array (Array ℕ)} {cA : Array ℕ} (hvc : validA n cA = true)
    (hc : permOfArr n cA ∈ M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n))))
    (hval : ∀ k < gs.size, validA n gs[k]! = true)
    (hle : Subgroup.closure (permsA n gs) ≤
      M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n)))) :
    Subgroup.closure (permsA n (gs.map (conjA n cA))) ≤
      M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n))) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk1 : k < gs.size := by simpa using hk
  show permOfArr n (gs.map (conjA n cA))[k]! ∈ _
  rw [map_getElem! _ _ hk1, permOfArr_eq_of_rep (rep_conjA hvc (rep_of_validA (hval k hk1)))]
  have hg := hle (Subgroup.subset_closure (mem_permsA hk1))
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hg) (Subgroup.inv_mem _ hc)

theorem isSylowTwoOf_of_card {X : Type} [Group X] {P C : Subgroup X} (hPC : P ≤ C) {a m : ℕ}
    (hP : Nat.card P = 2 ^ a) (hC : Nat.card C = 2 ^ a * m) (hm : ¬ 2 ∣ m) :
    IsSylowTwoOf P C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hPC, IsPGroup.of_card hP, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P C
  rw [inf_eq_left.mpr hPC, hP, hC, mul_comm (2 ^ a) m] at h1
  have h2 : P.relIndex C = m := Nat.eq_of_mul_eq_mul_right (pow_pos two_pos a) h1
  change ¬ 2 ∣ P.relIndex C
  rw [h2]
  exact hm

theorem pCoreOf_le_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {P C : Subgroup X}
    (hP : IsSylowTwoOf P C) : pCoreOf 2 C ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : ((pCoreOf 2 C).subgroupOf C).Normal := by
    have h1 : (pCoreOf 2 C).subgroupOf C = CFSG.Open.pCore 2 ↥C :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    rw [h1]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  exact le_of_normal_of_isSylowTwoOf hP (pCoreOf_le 2 C) hQn (pCoreOf_isPGroup 2 C)

theorem hatCoreAt_of_coverOK {M : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    {gs₁ gs₂ : Array (Array ℕ)} {ps : List ℕ} {c₁ c₂ : ArrCert} {cls : Array ℕ} {a m : ℕ}
    (hps : ∀ q ∈ ps, q < n)
    (hC : Nat.card ↥(M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n)))) = 2 ^ a * m)
    (hm : ¬ 2 ∣ m)
    (hP₁ : Subgroup.closure (permsA n gs₁) ≤
      M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n))))
    (hP₂ : Subgroup.closure (permsA n gs₂) ≤
      M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n))))
    (h₁ : enumOK n gs₁ ps c₁ = true) (hc₁ : c₁.pts.size = 2 ^ a)
    (h₂ : enumOK n gs₂ ps c₂ = true) (hc₂ : c₂.pts.size = 2 ^ a)
    (hcov : coverOK n 63 ps c₁ c₂ cls = true) :
    HatCoreAt (Equiv.Perm (Fin n)) M r := by
  intro t U S _ _ _ hUc hU _ _ _ _ _ _ _ _ _ _ _ hle
  have hsyl₁ := isSylowTwoOf_of_card hP₁ ((enumOK_spec hps h₁).2.1.trans hc₁) hC hm
  have hsyl₂ := isSylowTwoOf_of_card hP₂ ((enumOK_spec hps h₂).2.1.trans hc₂) hC hm
  have h63 := card_le_of_coverOK hps h₁ h₂ hcov (hle.trans (pCoreOf_le_of_isSylowTwoOf hsyl₁))
    (hle.trans (pCoreOf_le_of_isSylowTwoOf hsyl₂)) hUc
  omega

theorem hatCoreAt_conj {X : Type} [Group X] [Finite X] {M : Subgroup X} {r c : X} (hc : c ∈ M)
    (hr : HatCoreAt X M r) : HatCoreAt X M (c * r * c⁻¹) := by
  intro t U S hUM hSM htM hUc hU hS2 hS hUS hzU hzS hz2 hz1 htS htU htz hzt
  have hzM : c * r * c⁻¹ ∈ M := hUM hzU
  refine T4213N.not_le_pCoreOf_of_hatCore (MulAut.conj (⟨c, hc⟩ : ↥M)⁻¹) hUM hSM hzM htM ?_
    hUc hU hS2 hS hUS hzU hzS hz2 hz1 htS htU htz hzt
  have e : ((MulAut.conj (⟨c, hc⟩ : ↥M)⁻¹ ⟨c * r * c⁻¹, hzM⟩ : ↥M) : X) = r := by
    rw [MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  rw [e]
  exact hr

end CFSG.Quasithin.H13.Ch4.HatS
