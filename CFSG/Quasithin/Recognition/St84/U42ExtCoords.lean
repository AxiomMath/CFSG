module

public import CFSG.Quasithin.Recognition.St84.U42ExtFrame

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.GH74.QTGen4.U42
  CFSG.Quasithin.H13.A5 CFSG.Quasithin.A5Model CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

variable {G : Type} [Group G]

theorem dsuce_main [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S) (hS : ¬ S ≤ L1)
    (hs3 : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hb6 : F112B6Loc L2 L1)
    (hE1 : pCoreOf 2 L1 = dsQ L1 L2 S) (hEZ : dsQ L1 L2 S = dsZi L1 S)
    (hE16 : Nat.card ↥(pCoreOf 2 L1) = 16)
    (hQ2 : pCoreOf 2 L2 = dsQ L2 L1 S) (hQ2c : Nat.card ↥(pCoreOf 2 L2) = 32)
    (hQQ : dsQ L1 L2 S ⊔ dsQ L2 L1 S = S ⊓ L1) (hnotZ : ¬ dsZi L1 S ≤ dsQ L2 L1 S)
    (h5 : Nonempty (oTwoQuot ↥(L1 ⊔ bigB L1 L2 S) ≃* Equiv.Perm (Fin 5)))
    (h33 : Nonempty (oTwoQuot ↥(L2 ⊔ bigB L2 L1 S) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hsylS : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S))
    (hsylS2 : IsSylowTwoOf S (L2 ⊔ bigB L2 L1 S)) :
    ∃ e : ↥(L1 ⊔ bigB L1 L2 S) ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))),
      (∀ m : ↥(L1 ⊔ bigB L1 L2 S), (m : G) ∈ L2 ⊔ bigB L1 L2 S ↔ ((e m : Mof _) : Mc) ∈ Bhc) ∧
      (∀ m : ↥(L1 ⊔ bigB L1 L2 S), (m : G) ∈ S ↔ ((e m : Mof _) : Mc) ∈ Thc) ∧
      (∀ m : ↥(L1 ⊔ bigB L1 L2 S), (m : G) ∈ pCoreOf 2 L2 ↔ ((e m : Mof _) : Mc) ∈ U0) ∧
      PairCore (L2 ⊔ bigB L1 L2 S) ((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)) S (pCoreOf 2 L2) ∧
      pCoreOf 2 L2 ≤ ⁅(L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S),
        (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)⁆ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let B : Subgroup G := bigB L1 L2 S
  have hBB : bigB L2 L1 S = B := by rw [bigB_comm L1 L2 S]
  have hP2alt : P2 = L2 ⊔ bigB L2 L1 S := by rw [hBB]
  have hQ2P : pCoreOf 2 L2 = pCoreOf 2 P2 := by
    rw [hQ2]
    show pCoreOf 2 (L2 ⊔ bigB L2 L1 S) = pCoreOf 2 P2
    rw [← hP2alt]
  have hEleP1 : pCoreOf 2 L1 ≤ L1 ⊔ bigB L1 L2 S :=
    (dsucp_pCoreOf_le L1).trans le_sup_left
  have hSleB : S ≤ B := le_sup_right
  have hBleP1 : B ≤ P1 := le_sup_right
  have hBleP2 : B ≤ P2 := le_sup_right
  have hSleP1 : S ≤ P1 := hSleB.trans hBleP1
  have hSleP2 : S ≤ P2 := hSleB.trans hBleP2
  have hinf : P1 ⊓ P2 = B := by
    show (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S
    exact CFSG.Quasithin.F1.parabolic_inf_parabolic h
  have hfr : U42ExtFrame L1 L2 S := u42ExtFrame_of_local h hS hb6 hE1 hE16 h5 hsylS
  obtain ⟨C, hCV, hCtop, hCS, hCB, ⟨A, hAV, hAVtop⟩, hcardS⟩ := hfr
  obtain ⟨e0, heV0, heρ0⟩ := C.equiv_of_complement A hAV hAVtop
  let e : ↥P1 ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
    e0.trans (MulEquiv.subgroupCongr (congrArg Mof hCtop))
  have heρ : ∀ m : ↥P1, ((e m : Mof _) : Mc).right = C.ρ m := fun m => heρ0 m
  have heV : ∀ v : ↥C.V, ((e (v : ↥P1) : Mof _) : Mc) =
      SemidirectProduct.inl (C.ψ v) := fun v => heV0 v
  have hT : ∀ m : ↥P1, (m : G) ∈ S ↔ ((e m : Mof _) : Mc) ∈ Thc := by
    intro m
    have h1 : ((e m : Mof _) : Mc) ∈ Thc ↔ InD (C.ρ m) := by
      rw [show ((e m : Mof _) : Mc) ∈ Thc ↔ InD ((e m : Mof _) : Mc).right from Iff.rfl,
        heρ m]
    exact (hCS m).trans h1.symm
  have hB2 : ∀ m : ↥P1, (m : G) ∈ P2 ↔ ((e m : Mof _) : Mc) ∈ Bhc := by
    intro m
    have hmem : (m : G) ∈ P2 ↔ (m : G) ∈ B := by
      constructor
      · intro hm
        have h' : (m : G) ∈ P1 ⊓ P2 := ⟨m.2, hm⟩
        rwa [hinf] at h'
      · intro hb
        exact hBleP2 hb
    have hBhc : ((e m : Mof _) : Mc) ∈ Bhc ↔ (C.ρ m) 4 = 4 := by
      rw [show ((e m : Mof _) : Mc) ∈ Bhc ↔ ((e m : Mof _) : Mc).right 4 = 4 from Iff.rfl,
        heρ m]
    exact hmem.trans ((hCB m).trans hBhc.symm)
  have hUleS : pCoreOf 2 L2 ≤ S := by
    calc pCoreOf 2 L2 = dsQ L2 L1 S := hQ2
      _ ≤ dsQ L1 L2 S ⊔ dsQ L2 L1 S := le_sup_right
      _ = S ⊓ L1 := hQQ
      _ ≤ S := inf_le_left
  have hUleP1 : pCoreOf 2 L2 ≤ P1 := hUleS.trans hSleP1
  let ψe : ↥P1 →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  let X : Subgroup Mc := ((pCoreOf 2 L2).subgroupOf P1).map ψe
  have hXmem : ∀ x : Mc, x ∈ X ↔ ∃ m : ↥P1, (m : G) ∈ pCoreOf 2 L2 ∧
      ((e m : Mof _) : Mc) = x := by
    intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
  have hXle : X ≤ Thc := by
    rintro x ⟨m, hm, rfl⟩
    exact (hT m).mp (hUleS (Subgroup.mem_subgroupOf.mp hm))
  have hXcard : Nat.card X = 32 := by
    rw [Subgroup.card_map_of_injective]
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleP1).toEquiv, hQ2c]
    · exact Subtype.val_injective.comp e.injective
  have hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    obtain ⟨q, hq, rfl⟩ := (hXmem x).mp hx
    have hbM : b ∈ Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
      mem_Mof.mpr (Subgroup.mem_top b)
    obtain ⟨mb, hmb⟩ := e.surjective ⟨b, hbM⟩
    have hmbB : (mb : G) ∈ B := by
      apply (hCB mb).mpr
      have h4 : ((e mb : Mof _) : Mc).right 4 = 4 := by
        rw [show ((e mb : Mof _) : Mc) = b from congrArg Subtype.val hmb]
        exact hb.2
      rw [← heρ mb]
      exact h4
    have hnorm : P2 ≤ Subgroup.normalizer ((pCoreOf 2 L2 : Subgroup G) : Set G) := by
      rw [hQ2P]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2
    have hconj : (mb * q * mb⁻¹ : ↥P1) ∈ (pCoreOf 2 L2).subgroupOf P1 := by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hnorm (hBleP2 hmbB)) (q : G)).mp
        (Subgroup.mem_subgroupOf.mp hq)
    refine ⟨mb * q * mb⁻¹, hconj, ?_⟩
    show ((e (mb * q * mb⁻¹) : Mof _) : Mc) = b * ((e q : Mof _) : Mc) * b⁻¹
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show ((e mb : Mof _) : Mc) = b from congrArg Subtype.val hmb]
  have hnotE : ¬ pCoreOf 2 L1 ≤ pCoreOf 2 L2 := by
    intro hle
    apply hnotZ
    rw [← hEZ, ← hE1, ← hQ2]
    exact hle
  have hXV : ¬ Wc ≤ X := by
    intro hW
    apply hnotE
    intro y hy
    have hyP1 : y ∈ P1 := hEleP1 hy
    let m : ↥P1 := ⟨y, hyP1⟩
    have hmV : m ∈ C.V := by
      rw [hCV]
      exact Subgroup.mem_subgroupOf.mpr hy
    have hWmem : ((e m : Mof _) : Mc) ∈ Wc := by
      rw [heV ⟨m, hmV⟩]
      exact MonoidHom.mem_range.mpr ⟨C.ψ ⟨m, hmV⟩, rfl⟩
    obtain ⟨m', hm', heq⟩ := (hXmem _).mp (hW hWmem)
    have hmm' : m' = m := e.injective (Subtype.ext heq)
    have hyEq : (m' : G) = y := by rw [hmm']
    rwa [hyEq] at hm'
  have hX_eq : X = U0 := U0_unique hXle hXcard hXB hXV
  have hU : ∀ m : ↥P1, (m : G) ∈ pCoreOf 2 L2 ↔ ((e m : Mof _) : Mc) ∈ U0 := by
    intro m
    have h1 : ((e m : Mof _) : Mc) ∈ X ↔ (m : G) ∈ pCoreOf 2 L2 := by
      rw [hXmem]
      constructor
      · rintro ⟨m', hm', heq⟩
        have hmm' : m' = m := e.injective (Subtype.ext heq)
        rwa [hmm'] at hm'
      · intro hm
        exact ⟨m, hm, rfl⟩
    rw [← hX_eq]
    exact h1.symm
  have hcardP2 : Nat.card ↥P2 = 1152 := by
    have hpc : Nat.card ↥(CFSG.pCore 2 ↥P2) = 32 := by
      have hmap := Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥P2) (f := P2.subtype)
        (Subgroup.subtype_injective P2)
      rw [← hmap]
      show Nat.card ↥(pCoreOf 2 P2) = 32
      rw [← hQ2P]
      exact hQ2c
    have h36 : Nat.card (oTwoQuot ↥P2) = 36 := by
      rw [show P2 = L2 ⊔ bigB L2 L1 S from hP2alt]
      obtain ⟨ee⟩ := h33
      rw [Nat.card_congr ee.toEquiv, Nat.card_prod, Nat.card_perm]
      have h3 : Nat.card (Fin 3) = 3 := by simp
      rw [h3]
      norm_num
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥P2)
    rw [show Nat.card (↥P2 ⧸ CFSG.pCore 2 ↥P2) = 36 from h36, hpc] at hmul
    rw [hmul]
  have hodd : ¬ 2 ∣ (S.subgroupOf P2).index := by
    have hmul := Subgroup.card_mul_index (S.subgroupOf P2)
    have hSc : Nat.card ↥(S.subgroupOf P2) = Nat.card ↥S := by
      rw [hP2alt]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsylS2.1).toEquiv
    rw [hSc, hcardS, hcardP2] at hmul
    have hidx : (S.subgroupOf P2).index = 9 := by omega
    rw [hidx]
    norm_num
  have hcharP2 : CharTwo P2 := by
    have heq : P2 = L2 ⊔ S ⊔ borelOf L1 S := by
      show L2 ⊔ bigB L1 L2 S = L2 ⊔ S ⊔ borelOf L1 S
      rw [← CFSG.Quasithin.F1.parabolic_eq L2 L1 S, bigB_comm L1 L2 S]
    rw [heq]
    exact h.hyp.h2.charTwo
  have hPairCore : PairCore P2 (P2 ⊓ P1) S (pCoreOf 2 L2) := by
    refine ⟨hUleS, le_inf hSleP2 hSleP1, inf_le_left, ?_, h.hyp.h2.pgroup, hodd, ?_, ?_⟩
    · intro x hx u hu
      have hu' : u ∈ pCoreOf 2 P2 := by rw [← hQ2P]; exact hu
      have hmem := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2 hx) u).mp hu'
      rwa [hQ2P]
    · intro x hx hc
      have hcen : x ∈ Subgroup.centralizer ((pCoreOf 2 P2 : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (hc u (by rw [hQ2P]; exact hu)).symm
      have hx' := hcharP2 (Subgroup.mem_inf.mpr ⟨hx, hcen⟩)
      rwa [← hQ2P] at hx'
    · rw [hcardP2, hcardS]
  have hinf' : P2 ⊓ P1 = B := by rw [inf_comm]; exact hinf
  have hBmap : (B.subgroupOf P1).map ψe = Bhc := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact (hB2 b).mp (hBleP2 (Subgroup.mem_subgroupOf.mp hb))
    · intro y hy
      have hyM : y ∈ Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
        mem_Mof.mpr (Subgroup.mem_top y)
      obtain ⟨m, hm⟩ := e.surjective ⟨y, hyM⟩
      have hmP2 : (m : G) ∈ P2 := (hB2 m).mpr (by rw [hm]; exact hy)
      refine ⟨m, Subgroup.mem_subgroupOf.mpr ?_, congrArg Subtype.val hm⟩
      have h' : (m : G) ∈ P1 ⊓ P2 := ⟨m.2, hmP2⟩
      rwa [hinf] at h'
  have hcomm : pCoreOf 2 L2 ≤ ⁅P2 ⊓ P1, P2 ⊓ P1⁆ := by
    intro q hq
    have hqS : q ∈ S := hUleS hq
    have hqP1 : q ∈ P1 := hSleP1 hqS
    let m : ↥P1 := ⟨q, hqP1⟩
    have hmemU0 : ((e m : Mof _) : Mc) ∈ U0 := (hU m).mp hq
    have hc : ((e m : Mof _) : Mc) ∈
        (⁅B.subgroupOf P1, B.subgroupOf P1⁆ : Subgroup ↥P1).map ψe := by
      rw [Subgroup.map_commutator, hBmap]
      exact U0_le_comm_Bhc hmemU0
    obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.mp hc
    have hxm' : x = m := e.injective (Subtype.ext hxm)
    have hmB : m ∈ ⁅B.subgroupOf P1, B.subgroupOf P1⁆ := hxm' ▸ hx
    have hmap : (⁅B.subgroupOf P1, B.subgroupOf P1⁆ : Subgroup ↥P1).map P1.subtype =
        ⁅B, B⁆ := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBleP1]
    have hqB : q ∈ ⁅B, B⁆ := by
      have h : q ∈ (⁅B.subgroupOf P1, B.subgroupOf P1⁆ : Subgroup ↥P1).map P1.subtype :=
        Subgroup.mem_map.mpr ⟨m, hmB, rfl⟩
      rwa [hmap] at h
    rwa [hinf']
  exact ⟨e, hB2, hT, hU, hPairCore, hcomm⟩




end CFSG.Quasithin.F112R.St84
