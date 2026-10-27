module

public import CFSG.Quasithin.EmptyFaithful.S153G26

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBd

theorem isQuasisimple_of_surjective_ker_le_center {N S : Type*} [Group N] [Group S]
    (f : N →* S) (hf : Function.Surjective f) (hperf : Group.IsPerfect N)
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a)
    (hker : f.ker ≤ Subgroup.center N) : CFSG.IsQuasisimple N := by
  let e : N ⧸ f.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective f hf
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient f.ker hker hperf ?_ ?_
  · exact (MulEquiv.isSimpleGroup_congr e).mpr hS
  · obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this

theorem commutator_eq_bot_of_solvable_normal {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    (hA : CFSG.IsQuasisimple ↥A) (hBA : B ≤ A) (hBn : A ≤ Subgroup.normalizer (B : Set Γ))
    (hBs : Group.IsSolvable ↥B) : ⁅A, B⁆ = ⊥ := by
  have hn : (B.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).mpr hBn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hA hn with htop | hcen
  · exfalso
    have hAle : A ≤ B := Subgroup.subgroupOf_eq_top.mp htop
    have := hBs
    exact S153D.not_isSolvable_of_isQuasisimple hA
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAle))
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    have h1 : (⟨b, hBA hb⟩ : ↥A) ∈ Subgroup.center ↥A := hcen (Subgroup.mem_subgroupOf.mpr hb)
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨a, ha⟩
    exact (congrArg Subtype.val h2).symm

theorem card_Yp_sup_eq {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G}
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) :
    ∃ k : ℕ, Nat.card ↥(Yp ⊔ Sgp153 T V₁) = 2 ^ k * 6 := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := hF.s3
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (Yp ⊔ Sgp153 T V₁)).exists_card_eq
  refine ⟨k, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (↥(Yp ⊔ Sgp153 T V₁) ⧸ φ.ker) = 6 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have h3 : Nat.card φ.ker = 2 ^ k := by
    rw [hφk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 _)).toEquiv]
    exact hk
  rw [h1, h2, h3]
  ring

theorem not_nine_dvd_card_Yp {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G}
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) : ¬ 9 ∣ Nat.card Yp := by
  obtain ⟨k, hk⟩ := card_Yp_sup_eq hF
  have hcardYp : Nat.card Yp ∣ 2 ^ k * 6 := hk ▸ Subgroup.card_dvd_of_le le_sup_left
  intro h9
  have h1 : 3 * 3 ∣ 3 * 2 ^ (k + 1) := by
    have := h9.trans hcardYp
    rw [pow_succ]
    convert this using 1
    ring
  have h2 : 3 ∣ 2 ^ (k + 1) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem mem_of_orderOf_three_pow {G : Type*} [Group G] [Finite G] {N H : Subgroup G}
    (hNH : N ≤ H) (hn : H ≤ Subgroup.normalizer (N : Set G)) (h3 : 3 ∣ Nat.card N)
    (h9 : ¬ 9 ∣ Nat.card H) {x : G} (hx : x ∈ H) (hj : ∃ j : ℕ, orderOf x = 3 ^ j) : x ∈ N := by
  obtain ⟨j, hj⟩ := hj
  have hNn : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hn
  have hQ : ¬ 3 ∣ Nat.card (↥H ⧸ N.subgroupOf H) := by
    intro hQ3
    apply h9
    have e := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
    have e2 : Nat.card (N.subgroupOf H) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
    rw [e, e2]
    exact Nat.mul_dvd_mul hQ3 h3
  have hord : orderOf (QuotientGroup.mk ⟨x, hx⟩ : ↥H ⧸ N.subgroupOf H) ∣ 3 ^ j := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : ↥H) ^ 3 ^ j = 1 := Subtype.ext (by rw [← hj]; simp)
    rw [this, QuotientGroup.mk_one]
  have hord2 : orderOf (QuotientGroup.mk ⟨x, hx⟩ : ↥H ⧸ N.subgroupOf H) ∣
      Nat.card (↥H ⧸ N.subgroupOf H) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ j) (Nat.card (↥H ⧸ N.subgroupOf H)) :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ)
  have h1 : orderOf (QuotientGroup.mk ⟨x, hx⟩ : ↥H ⧸ N.subgroupOf H) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord hord2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact (Subgroup.mem_subgroupOf.mp h1)

theorem isPGroup_two_inf {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G}
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) {C : Subgroup G}
    (hYU : Yp ≤ Subgroup.normalizer (UI153 T I : Set G))
    (hYC : Yp ≤ Subgroup.normalizer (C : Set G))
    (hCU : C ≤ Subgroup.centralizer (UI153 T I : Set G)) :
    IsPGroup 2 ↥(C ⊓ Yp) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := card_Yp_sup_eq hF
  have hcardYp : Nat.card Yp ∣ 2 ^ k * 6 := hk ▸ Subgroup.card_dvd_of_le le_sup_left
  have h9 : ¬ 9 ∣ Nat.card Yp := not_nine_dvd_card_Yp hF
  have hAY : C ⊓ Yp ≤ Yp := inf_le_right
  have hcardA : Nat.card ↥(C ⊓ Yp) ∣ 2 ^ k * 6 := (Subgroup.card_dvd_of_le hAY).trans hcardYp
  by_cases h3 : 3 ∣ Nat.card ↥(C ⊓ Yp)
  · exfalso
    have hn : Yp ≤ Subgroup.normalizer ((C ⊓ Yp : Subgroup G) : Set G) := fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hYC hy, Subgroup.le_normalizer hy⟩
    have hall : ∀ x : G, x ∈ Yp → (∃ j : ℕ, orderOf x = 3 ^ j) → x ∈ C := fun x hx hj =>
      (mem_of_orderOf_three_pow hAY hn h3 h9 hx hj).1
    have hmem : ∀ x : G, x ∈ M ⊓ I → (∃ j : ℕ, orderOf x = 3 ^ j) → x ∈ Yp := fun x hx hj => by
      rw [hF.yp_eq]
      exact Subgroup.subset_closure ⟨hx, hj⟩
    have hYle : Yp ≤ C := by
      rw [hF.yp_eq]
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      exact hall x (hmem x hx.1 hx.2) hx.2
    apply hF.star_ne
    exact (autOn_eq_bot_iff hYU).mpr (hYle.trans hCU)
  · have hcop : Nat.Coprime (Nat.card ↥(C ⊓ Yp)) 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have hdvd : Nat.card ↥(C ⊓ Yp) ∣ 2 ^ (k + 1) := by
      have : Nat.card ↥(C ⊓ Yp) ∣ 2 ^ (k + 1) * 3 := by
        rw [pow_succ]
        convert hcardA using 1
        ring
      exact hcop.dvd_of_dvd_mul_right this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card hj

theorem commutator_solvRad_le {G : Type} [Group G] [Finite G] {U L I : Subgroup G}
    (hLI : L ∈ cComp I) (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hLq : CFSG.IsQuasisimple ↥(autOn L U)) :
    ⁅L, solvRad L⁆ ≤ L ⊓ Subgroup.centralizer (U : Set G) := by
  have hRL : solvRad L ≤ L := solvRad_le L
  have hLR : L ≤ Subgroup.normalizer (solvRad L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRL).mp (solvRad_normal L)
  have hRU : solvRad L ≤ Subgroup.normalizer (U : Set G) := hRL.trans hLU
  have hcomm : ⁅autOn L U, autOn (solvRad L) U⁆ = ⊥ :=
    commutator_eq_bot_of_solvable_normal hLq (autOn_le_autOn _ hRL)
      (autOn_le_normalizer_autOn hLU hRU hLR) (S153D.isSolvable_autOn hRU (solvRad_isSolvable L))
  have h0 : autOn ⁅L, solvRad L⁆ U = ⊥ := by
    rw [S153D.autOn_commutator hLU hRU]
    exact hcomm
  have hle : ⁅L, solvRad L⁆ ≤ L := by
    refine (Subgroup.commutator_mono le_rfl hRL).trans ?_
    rw [perfect_of_mem_cComp hLI]
  exact le_inf hle ((autOn_eq_bot_iff (hle.trans hLU)).mp h0)

theorem input26Quasisimple_of_a3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    Input26Quasisimple := by
  intro G _ _ T Mc M V₁ V₂ Yp I t c hF L hLc hLn hLq _hB
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF3 : Facts153 T M V₁ Yp I := hF.toFacts153
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLle.trans hUN
  have hYI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hYU : Yp ≤ Subgroup.normalizer (UI153 T I : Set G) := hYI.trans hUN
  have hYL : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 c.hyp c.inH hLI
  have hLY : ⁅L, Yp⁆ = L :=
    S153D.comm_eq_of_quasisimple' h37 h38 c.hyp c.inH hF3 hLc hLn hLq
  set C : Subgroup G := L ⊓ Subgroup.centralizer (UI153 T I : Set G) with hC
  have hCL : C ≤ L := inf_le_left
  have hCU : C ≤ Subgroup.centralizer (UI153 T I : Set G) := inf_le_right
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hl, B2F.le_normalizer_centralizer hLU hl⟩
  have hYC : Yp ≤ Subgroup.normalizer (C : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hYL hy, B2F.le_normalizer_centralizer hYU hy⟩
  have hCM : C ≤ M ⊓ I := fun x hx => hF3.cent_le ⟨hLle hx.1, hx.2⟩
  have hCYn : C ≤ Subgroup.normalizer (Yp : Set G) := by
    intro x hx
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by
      rw [hF3.norm_eq]
      exact hCM hx
    exact this.2
  have hA2 : IsPGroup 2 ↥(C ⊓ Yp) := isPGroup_two_inf hF hYU hYC hCU
  have hCn : C ≤ Subgroup.normalizer ((C ⊓ Yp : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hCYn hx⟩
  have hAC : C ⊓ Yp ≤ pCoreOf 2 C := le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hA2
  have hOCL : pCoreOf 2 C ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans hCL)
      (fun l hl => normalizer_le_normalizer_pCoreOf 2 C (hLC hl)) (pCoreOf_isPGroup 2 C)
  have hCY : ⁅C, Yp⁆ ≤ pCoreOf 2 L := by
    refine le_trans ?_ (hAC.trans hOCL)
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨?_, ?_⟩
    · have h2 : y * x⁻¹ * y⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hYC hy) x⁻¹).mp (C.inv_mem hx)
      rw [commutatorElement_def]
      simpa [mul_assoc] using C.mul_mem hx h2
    · have h1 : x * y * x⁻¹ ∈ Yp := (Subgroup.mem_normalizer_iff.mp (hCYn hx) y).mp hy
      rw [commutatorElement_def]
      exact Yp.mul_mem h1 (Yp.inv_mem hy)
  have hNL : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  have hNY : Yp ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hYL.trans (normalizer_le_normalizer_pCoreOf 2 L)
  have hLCN : ⁅L, C⁆ ≤ pCoreOf 2 L := by
    have h1 : ⁅⁅Yp, C⁆, L⁆ ≤ pCoreOf 2 L := by
      refine (Subgroup.commutator_mono ?_ le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hNL)
      rw [Subgroup.commutator_comm]
      exact hCY
    have h2 : ⁅⁅C, L⁆, Yp⁆ ≤ pCoreOf 2 L :=
      (Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_left.mp hLC)
        le_rfl).trans hCY
    have := S153D.commutator_commutator_le_of_rotate (A := L) (B := Yp) (C := C) hNL hNY
      (hCL.trans hNL) h1 h2
    rwa [hLY] at this
  have hRL : solvRad L ≤ L := solvRad_le L
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hLRC : ⁅L, solvRad L⁆ ≤ C := commutator_solvRad_le hLI hLU hLq
  have hLRN : ⁅L, solvRad L⁆ ≤ pCoreOf 2 L := by
    have hCLN : ⁅C, L⁆ ≤ pCoreOf 2 L := by
      rw [Subgroup.commutator_comm]
      exact hLCN
    have h1 : ⁅⁅L, solvRad L⁆, L⁆ ≤ pCoreOf 2 L :=
      (Subgroup.commutator_mono hLRC le_rfl).trans hCLN
    have h2 : ⁅⁅solvRad L, L⁆, L⁆ ≤ pCoreOf 2 L := by
      rw [Subgroup.commutator_comm (solvRad L) L]
      exact h1
    have := S153D.commutator_commutator_le_of_rotate (A := L) (B := L) (C := solvRad L) hNL hNL
      (hRL.trans hNL) h1 h2
    rwa [hLperf] at this
  have hnorm₂ : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hN₂R : CFSG.pCore 2 ↥L ≤ (solvRad L).subgroupOf L := by
    intro x hx
    have hxO : (x : G) ∈ pCoreOf 2 L := (S153D.mem_pCore_iff x).mp hx
    have hOnorm : ((pCoreOf 2 L).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 L)).mpr hNL
    have hsub : IsSubnormal (pCoreOf 2 L) L := A4.subnormal_of_normal (pCoreOf_le 2 L) hOnorm
    have hsolv : Group.IsSolvable ↥(pCoreOf 2 L) := by
      have : Group.IsNilpotent ↥(pCoreOf 2 L) := (pCoreOf_isPGroup 2 L).isNilpotent
      infer_instance
    exact le_solvRad_of_subnormal hsub hsolv hxO
  let f : (↥L ⧸ CFSG.pCore 2 ↥L) →* (↥L ⧸ (solvRad L).subgroupOf L) :=
    QuotientGroup.map (CFSG.pCore 2 ↥L) ((solvRad L).subgroupOf L) (MonoidHom.id ↥L)
      (by rw [Subgroup.comap_id]; exact hN₂R)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hker : f.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro q hq
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hlR : (l : G) ∈ solvRad L := by
      have h1 : (QuotientGroup.mk l : ↥L ⧸ (solvRad L).subgroupOf L) = 1 := hq
      rw [QuotientGroup.eq_one_iff] at h1
      exact h1
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective q'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hc : ⁅(l : G)⁻¹, (l' : G)⁻¹⁆ ∈ pCoreOf 2 L := by
      refine hLRN ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ((solvRad L).inv_mem hlR) (L.inv_mem l'.2)
    refine (S153D.mem_pCore_iff _).mpr ?_
    have e : ((((l' * l)⁻¹ * (l * l') : ↥L)) : G) = ⁅(l : G)⁻¹, (l' : G)⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact hc
  have hperfL : Group.IsPerfect ↥L := S153D.isPerfect_of_commutator_eq hLperf
  have hperfQ : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨⟨hsimple, hnc⟩, -⟩ := (cComp_structure hLI).2
  exact SBd.isQuasisimple_of_surjective_ker_le_center f hfs hperfQ hsimple hnc hker

end SBd

end CFSG.Quasithin
