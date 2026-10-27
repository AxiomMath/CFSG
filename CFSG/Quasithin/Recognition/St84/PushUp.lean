module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18A5
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannS3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannA5
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRMain
public import CFSG.Quasithin.Recognition.St84.Basic
public import CFSG.Dihedral.Glauberman.DicksonMaxB
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Br
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2
public import CFSG.Quasithin.Background.C58Push
public import CFSG.GroupTheory.FiniteAmalgamEmbedding
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Push

theorem odd_order_mem_of_normal_ne_bot_alt5 {N : Subgroup ↥(alternatingGroup (Fin 5))}
    (hN : N.Normal) (hne : N ≠ ⊥) {x : ↥(alternatingGroup (Fin 5))} (_hx : Odd (orderOf x)) :
    x ∈ N := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
  · exact absurd h hne
  · rw [h]; exact Subgroup.mem_top x

theorem odd_order_mem_of_normal_ne_bot_perm3 {N : Subgroup (Equiv.Perm (Fin 3))} (hN : N.Normal)
    (hne : N ≠ ⊥) {x : Equiv.Perm (Fin 3)} (hx : Odd (orderOf x)) : x ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcases : ∀ σ : Equiv.Perm (Fin 3),
      σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 1 2 ∨
        σ = Equiv.swap 0 2 * Equiv.swap 0 1 ∨ σ = (Equiv.swap 0 2 * Equiv.swap 0 1) ^ 2 := by
    intro σ; revert σ; decide
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (Subgroup.ext fun y => ⟨fun hy => by rw [Subgroup.mem_bot, h y hy],
      fun hy => by rw [Subgroup.mem_bot] at hy; rw [hy]; exact N.one_mem⟩)
  have hcyc : Equiv.swap 0 2 * Equiv.swap 0 1 ∈ N := by
    rcases hcases n with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hn1
    · obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 3),
          τ * Equiv.swap 0 1 * τ⁻¹ = Equiv.swap 0 2 := by decide
      exact N.mul_mem (by rw [← hτ]; exact hN.conj_mem _ hnN τ) hnN
    · obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 3),
          τ * Equiv.swap 0 2 * τ⁻¹ = Equiv.swap 0 1 := by decide
      exact N.mul_mem hnN (by rw [← hτ]; exact hN.conj_mem _ hnN τ)
    · obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 3),
          τ * Equiv.swap 1 2 * τ⁻¹ = Equiv.swap 0 1 := by decide
      obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 3),
          σ * Equiv.swap 1 2 * σ⁻¹ = Equiv.swap 0 2 := by decide
      exact N.mul_mem (by rw [← hσ]; exact hN.conj_mem _ hnN σ)
        (by rw [← hτ]; exact hN.conj_mem _ hnN τ)
    · exact hnN
    · have h : (Equiv.swap 0 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)) =
          (((Equiv.swap 0 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3))) ^ 2) ^ 2 := by decide
      rw [h]; exact N.mul_mem hnN hnN
  rcases hcases x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact N.one_mem
  · exfalso
    have h : orderOf (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) = 2 := by
      refine orderOf_eq_prime ?_ ?_ <;> decide
    rw [h] at hx
    obtain ⟨k, hk⟩ := hx
    omega
  · exfalso
    have h : orderOf (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) = 2 := by
      refine orderOf_eq_prime ?_ ?_ <;> decide
    rw [h] at hx
    obtain ⟨k, hk⟩ := hx
    omega
  · exfalso
    have h : orderOf (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) = 2 := by
      refine orderOf_eq_prime ?_ ?_ <;> decide
    rw [h] at hx
    obtain ⟨k, hk⟩ := hx
    omega
  · exact hcyc
  · exact N.mul_mem hcyc hcyc

section Group

variable {G : Type} [Group G]

@[expose] noncomputable def pushZ (X P : Subgroup G) : Subgroup G :=
  conjClosure (omegaOneCenterOf P) X

variable {X P A : Subgroup G} {n : ℕ}

theorem le_centralizer_omegaOneCenterOf (P : Subgroup G) :
    P ≤ Subgroup.centralizer (omegaOneCenterOf P : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  exact (B2F.omegaOneCenter_le_inf_centralizer P).trans inf_le_right

theorem le_normalizer_pushZ (X P : Subgroup G) :
    X ≤ Subgroup.normalizer (pushZ X P : Set G) :=
  le_normalizer_conjClosure _ _

section Finite

variable [Finite G]

theorem pushZ_le_centerOf_pCoreOf (hchar : CharTwo X) (hP : IsSylowTwoOf P X) :
    pushZ X P ≤ centerOf (pCoreOf 2 X) ∧ IsElemAbelian 2 (pushZ X P) :=
  conjClosure_le_centerOf_pCoreOf_of_sylowIn hP.1 hP.2.1 hP.2.2 hchar le_rfl

theorem pushZ_le_pCoreOf (hchar : CharTwo X) (hP : IsSylowTwoOf P X) :
    pushZ X P ≤ pCoreOf 2 X :=
  (pushZ_le_centerOf_pCoreOf hchar hP).1.trans fun _ hx => hx.1

theorem isSylowTwoOf_ne_bot (hn : n = 1 ∨ n = 2) (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) : P ≠ ⊥ := by
  intro hbot
  have hXodd : ¬ 2 ∣ Nat.card X := by
    have h := hP.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
    exact h
  have hq2 : ∃ q : OTwoQuot X, orderOf q = 2 := by
    rcases hn with rfl | rfl
    · obtain ⟨e⟩ := hquot
      refine ⟨(e.trans permThreeEquivPSL.symm).symm (Equiv.swap 0 1), ?_⟩
      rw [← MulEquiv.orderOf_eq (e.trans permThreeEquivPSL.symm),
        MulEquiv.apply_symm_apply]
      refine orderOf_eq_prime ?_ ?_ <;> decide
    · obtain ⟨e⟩ := hquot
      obtain ⟨e2⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
      refine ⟨(e.trans e2).symm ⟨Equiv.swap 0 1 * Equiv.swap 2 3, ?_⟩, ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup]; decide
      · rw [← MulEquiv.orderOf_eq (e.trans e2), MulEquiv.apply_symm_apply]
        refine orderOf_eq_prime ?_ ?_
        · apply Subtype.ext
          decide
        · intro h
          have h' := congrArg Subtype.val h
          revert h'
          decide
  obtain ⟨q, hq⟩ := hq2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥X) q
  have h2 : 2 ∣ orderOf x := by
    rw [← hq]
    exact orderOf_map_dvd (QuotientGroup.mk' (pCore 2 ↥X)) x
  exact hXodd (h2.trans (orderOf_dvd_natCard x))

theorem pushZ_ne_bot (hn : n = 1 ∨ n = 2) (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) : pushZ X P ≠ ⊥ := by
  intro hbot
  have hle : omegaOneCenterOf P ≤ pushZ X P := le_conjClosure _ _
  rw [hbot] at hle
  exact CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hP.2.1
    (isSylowTwoOf_ne_bot hn hquot hP) (le_bot_iff.mp hle)

theorem map_mulEquiv_ne_bot {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    {K : Subgroup H} (h : K ≠ ⊥) : K.map e.toMonoidHom ≠ ⊥ := fun h0 =>
  h (Subgroup.map_injective e.injective (by rw [h0, Subgroup.map_bot]))

theorem pushZ_centralizer_eq (hn : n = 1 ∨ n = 2) (hchar : CharTwo X)
    (hquot : IsL2Quot n (oTwoQuot ↥X)) (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X) :
    X ⊓ Subgroup.centralizer (pushZ X P : Set G) = pCoreOf 2 X := by
  have hPne : P ≠ ⊥ := isSylowTwoOf_ne_bot hn hquot hP
  set K : Subgroup G := X ⊓ Subgroup.centralizer (pushZ X P : Set G) with hKdef
  have hKleX : K ≤ X := hKdef ▸ inf_le_left
  have hOle : pCoreOf 2 X ≤ K := by
    rw [hKdef]
    refine le_inf ?_ ?_
    · rintro x ⟨y, -, rfl⟩; exact y.2
    exact fun o ho => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      ((Subgroup.mem_centralizer_iff.mp ((pushZ_le_centerOf_pCoreOf hchar hP).1 hz).2) o ho).symm
  refine le_antisymm ?_ hOle
  by_contra hcon
  have hKnorm : X ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKdef]
    exact A1a.le_normalizer_inf Subgroup.le_normalizer
      (A1a.le_normalizer_centralizer (le_normalizer_pushZ X P))
  have hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleX).mpr hKnorm
  let π : ↥X →* OTwoQuot X := QuotientGroup.mk' (pCore 2 ↥X)
  let QK : Subgroup (OTwoQuot X) := (K.subgroupOf X).map π
  have hQKn : QK.Normal := hKn.map π (QuotientGroup.mk'_surjective _)
  have hcore_le : pCore 2 ↥X ≤ K.subgroupOf X := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hOle ⟨y, hy, rfl⟩)
  have hpre : ∀ y : ↥X, π y ∈ QK ↔ y ∈ K.subgroupOf X := by
    intro y
    constructor
    · rintro ⟨k, hk, hkπ⟩
      have h1 : k⁻¹ * y ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkπ]
        simp
      have h2 : k⁻¹ * y ∈ pCore 2 ↥X := by
        rwa [QuotientGroup.ker_mk'] at h1
      have h3 := hcore_le h2
      simpa using (K.subgroupOf X).mul_mem hk h3
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hQKne : QK ≠ ⊥ := by
    intro h0
    apply hcon
    intro x hx
    have hxK' : (⟨x, hKleX hx⟩ : ↥X) ∈ K.subgroupOf X := hx
    have h1 : π ⟨x, hKleX hx⟩ ∈ QK := Subgroup.mem_map_of_mem π hxK'
    rw [h0, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hKleX hx⟩ : ↥X) ∈ pCore 2 ↥X := by
      rw [← QuotientGroup.ker_mk' (pCore 2 ↥X), MonoidHom.mem_ker]
      exact h1
    exact ⟨⟨x, hKleX hx⟩, h2, rfl⟩
  have hodd : ∀ y : ↥X, Odd (orderOf y) → y ∈ K.subgroupOf X := by
    intro y hy
    rw [← hpre y]
    have hkey : ∀ z : OTwoQuot X, Odd (orderOf z) → z ∈ QK := by
      intro z hz
      rcases hn with rfl | rfl
      · obtain ⟨e⟩ := hquot
        let E : OTwoQuot X ≃* Equiv.Perm (Fin 3) := e.trans permThreeEquivPSL.symm
        have hz' : Odd (orderOf (E z)) := by rwa [MulEquiv.orderOf_eq]
        have hmem : E z ∈ QK.map E.toMonoidHom :=
          odd_order_mem_of_normal_ne_bot_perm3 (hQKn.map E.toMonoidHom E.surjective)
            (map_mulEquiv_ne_bot E hQKne) hz'
        simpa using Subgroup.mem_map_equiv.mp hmem
      · obtain ⟨e⟩ := hquot
        obtain ⟨e2⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
        let E : OTwoQuot X ≃* ↥(alternatingGroup (Fin 5)) := e.trans e2
        have hz' : Odd (orderOf (E z)) := by rwa [MulEquiv.orderOf_eq]
        have hmem : E z ∈ QK.map E.toMonoidHom :=
          odd_order_mem_of_normal_ne_bot_alt5 (hQKn.map E.toMonoidHom E.surjective)
            (map_mulEquiv_ne_bot E hQKne) hz'
        simpa using Subgroup.mem_map_equiv.mp hmem
    exact hkey (π y) (Odd.of_dvd_nat hy (orderOf_map_dvd π y))
  have hXcent : X ≤ Subgroup.centralizer (omegaOneCenterOf P : Set G) := by
    have hO : pResidualOf 2 X ≤ Subgroup.centralizer (omegaOneCenterOf P : Set G) := by
      rw [← CFSG.Quasithin.oTwoUpper_eq_pResidualOf]
      refine (Subgroup.closure_le _).mpr ?_
      rintro z ⟨hzX, hzo⟩
      have hzK : z ∈ K := hodd ⟨z, hzX⟩ (by rwa [Subgroup.orderOf_mk])
      exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
        Subgroup.mem_centralizer_iff.mp hzK.2 w (le_conjClosure _ _ hw)
    rw [← pResidualOf_sup_eq_of_sylow hP]
    exact sup_le hO (le_centralizer_omegaOneCenterOf P)
  exact hnc (omegaOneCenterOf P) (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le P)
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hP.2.1 hPne)
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf P)
    (hXcent.trans (Subgroup.centralizer_le_normalizer _))

theorem pushHyp_pushZ (hn : n = 1 ∨ n = 2) (hchar : CharTwo X) (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X) : PushHyp X P (pushZ X P) where
  sylow := hP
  normal := le_normalizer_pushZ X P
  elemAbelian := (pushZ_le_centerOf_pCoreOf hchar hP).2
  le_core := pushZ_le_pCoreOf hchar hP
  cent_eq := pushZ_centralizer_eq hn hchar hquot hP hnc

theorem not_thompsonJ_le_pCoreOf (hn : n = 1 ∨ n = 2) (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X) : ¬ thompsonJ P ≤ pCoreOf 2 X := by
  intro hJ
  have hPne : P ≠ ⊥ := isSylowTwoOf_ne_bot hn hquot hP
  have hle : pCoreOf 2 X ≤ P := pCoreOf_le_of_isSylowTwoOf hP
  have heq : thompsonJ (pCoreOf 2 X) = thompsonJ P :=
    CFSG.QuasithinUnique.GammaExtra.thompsonJ_eq_of_le hJ hle
  have hN : X ≤ Subgroup.normalizer (thompsonJ P : Set G) := by
    rw [← heq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans
      (normalizer_le_normalizer_thompsonJ (pCoreOf 2 X))
  exact hnc (thompsonJ P) (CFSG.Quasithin.B6.thompsonJ_le P)
    (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hP.2.1 hPne)
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ P) hN

theorem baumannC_pushZ (hn : n = 1 ∨ n = 2) (hchar : CharTwo X) (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X) : BaumannC X (pushZ X P) := by
  have h := pushHyp_pushZ hn hchar hquot hP hnc
  have hJ := not_thompsonJ_le_pCoreOf hn hquot hP hnc
  rcases hn with rfl | rfl
  · obtain ⟨e⟩ := hquot
    exact baumannS3_holds G X P (pushZ X P) h ⟨e.trans permThreeEquivPSL.symm⟩ hnc
  · obtain ⟨e⟩ := hquot
    obtain ⟨e2⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
    have he : Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))) := ⟨e.trans e2⟩
    exact baumannA5_holds G X P (pushZ X P) h he
      (hss18A5_holds G X P (pushZ X P) h he hJ) hnc

theorem le_normalizer_conjJoinOf_pushZ (hPX : P ≤ X)
    (hA : A ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ Subgroup.normalizer (conjJoinOf A (pushZ X P) : Set G) := by
  have hpoint : ∀ a : A, P ≤ Subgroup.normalizer (cj (a : G) (pushZ X P) : Set G) := by
    intro a p hp
    have hmem : (a : G)⁻¹ * p * (a : G) ∈ Subgroup.normalizer (pushZ X P : Set G) :=
      le_normalizer_pushZ X P
        (hPX (by simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hA a.2)) p).mp hp))
    have hm : p * (a : G) = (a : G) * ((a : G)⁻¹ * p * (a : G)) := by group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change cj p (cj (a : G) (pushZ X P)) = cj (a : G) (pushZ X P)
    rw [CFSG.Quasithin.F53Push.cj_cj p (a : G) (pushZ X P), hm,
      ← CFSG.Quasithin.F53Push.cj_cj (a : G) ((a : G)⁻¹ * p * (a : G)) (pushZ X P),
      cj_eq_of_mem_normalizer hmem]
  have hjoin : conjJoinOf A (pushZ X P) = ⨆ a : A, cj (a : G) (pushZ X P) := by
    rw [conjJoinOf]
    exact iSup_subtype'
  rw [hjoin]
  exact (le_iInf hpoint).trans (Subgroup.iInf_normalizer_le_normalizer_iSup _)

theorem conjJoinOf_pushZ_le (hn : n = 1 ∨ n = 2) (hchar : CharTwo X)
    (hquot : IsL2Quot n (oTwoQuot ↥X)) (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X)
    (hA : A ≤ Subgroup.normalizer (P : Set G)) (hAo : Odd (Nat.card A)) :
    conjJoinOf A (pushZ X P) ≤ pCoreOf 2 X ∧
      X ≤ Subgroup.normalizer (conjJoinOf A (pushZ X P) : Set G) := by
  have h := pushHyp_pushZ hn hchar hquot hP hnc
  have hB := baumannC_pushZ hn hchar hquot hP hnc
  have hJ := not_thompsonJ_le_pCoreOf hn hquot hP hnc
  have hPnorm := le_normalizer_conjJoinOf_pushZ hP.1 hA
  have hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ A).relIndex A) := by
    refine Odd.of_dvd_nat hAo ⟨Nat.card ↥((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ A) ⊓ A), ?_⟩
    exact (Subgroup.relIndex_mul_card (Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ A) A).symm
  have hle : conjJoinOf A (pushZ X P) ≤ pCoreOf 2 X := by
    rcases hn with h1 | h2
    · have hq : IsL2Quot 1 (oTwoQuot ↥X) := h1 ▸ hquot
      obtain ⟨e⟩ := hq
      exact (cor42_s3 h ⟨e.trans permThreeEquivPSL.symm⟩ hnc hB hA hodd).2.1
    · have hq : IsL2Quot 2 (oTwoQuot ↥X) := h2 ▸ hquot
      obtain ⟨e⟩ := hq
      obtain ⟨e2⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
      have he : Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))) := ⟨e.trans e2⟩
      exact (cor42_a5 h he (hss18A5_holds G X P (pushZ X P) h he hJ) hB hA hodd).2.1
  refine ⟨hle, ?_⟩
  rcases hn with h1 | h2
  · have hq : IsL2Quot 1 (oTwoQuot ↥X) := h1 ▸ hquot
    obtain ⟨e⟩ := hq
    exact (cor42_s3 h ⟨e.trans permThreeEquivPSL.symm⟩ hnc hB hA hodd).2.2 hPnorm
  · have hq : IsL2Quot 2 (oTwoQuot ↥X) := h2 ▸ hquot
    obtain ⟨e⟩ := hq
    obtain ⟨e2⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
    have he : Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))) := ⟨e.trans e2⟩
    exact (cor42_a5 h he (hss18A5_holds G X P (pushZ X P) h he hJ) hB hA hodd).2.2 hPnorm

theorem noCharNormal_map_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    {S T : Subgroup Y} (h : NoCharNormal S T) :
    NoCharNormal (S.map e.toMonoidHom) (T.map e.toMonoidHom) := by
  intro C' hC'S' hC'ne hC'char hT'N'
  have hSe : (S.map e.toMonoidHom).comap e.toMonoidHom = S :=
    Subgroup.comap_map_eq_self_of_injective e.injective S
  have hC'e : (C'.comap e.toMonoidHom).map e.toMonoidHom = C' :=
    Subgroup.map_comap_eq_self (by simp)
  have hCS : C'.comap e.toMonoidHom ≤ S := by
    intro c hc
    rw [← hSe]
    exact hC'S' hc
  have hCne : C'.comap e.toMonoidHom ≠ ⊥ := by
    intro h0
    apply hC'ne
    rw [← hC'e, h0, Subgroup.map_bot]
  have hchar : ((C'.comap e.toMonoidHom).subgroupOf S).Characteristic := by
    let eS : ↥S ≃* ↥(S.map e.toMonoidHom) := S.equivMapOfInjective e.toMonoidHom e.injective
    have hmap2 : (C'.subgroupOf (S.map e.toMonoidHom)).map eS.symm.toMonoidHom =
        (C'.comap e.toMonoidHom).subgroupOf S := by
      ext s
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      rfl
    rw [← hmap2]
    exact CFSG.Quasithin.C58.characteristic_map_mulEquiv hC'char eS.symm
  have hN : T ≤ Subgroup.normalizer ((C'.comap e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht c hc
    have h1 : e t ∈ T.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom ht
    have h2 : e c ∈ C' := hc
    have h3 := (Subgroup.le_normalizer_iff.mp hT'N') (e t) h1 (e c) h2
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact h3
  exact h (C'.comap e.toMonoidHom) hCS hCne hchar hN

theorem noCharNormal_of_subgroupOf {Y : Type*} [Group Y] {S T : Subgroup Y} (hTS : T ≤ S)
    (h : NoCharNormal (T.subgroupOf S) (⊤ : Subgroup ↥S)) : NoCharNormal T S := by
  intro C hCT hCne hCchar hSN
  let C₀ : Subgroup ↥S := C.subgroupOf S
  have hCTS : C ≤ S := hCT.trans hTS
  have hC₀T : C₀ ≤ T.subgroupOf S := fun c hc => Subgroup.mem_subgroupOf.mpr (hCT hc)
  have hC₀ne : C₀ ≠ ⊥ := by
    intro h0
    apply hCne
    have heq : C = C₀.map S.subtype := (Subgroup.map_subgroupOf_eq_of_le hCTS).symm
    rw [heq, h0, Subgroup.map_bot]
  have hchar : (C₀.subgroupOf (T.subgroupOf S)).Characteristic := by
    let e : ↥(T.subgroupOf S) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTS
    have hmap : (C₀.subgroupOf (T.subgroupOf S)).map e.toMonoidHom = C.subgroupOf T := by
      ext p
      constructor
      · rintro ⟨c, hc, hcp⟩
        have hcY : ((c : ↥S) : Y) ∈ C := hc
        have h5 : ((e.toMonoidHom c : ↥T) : Y) = (p : Y) := by rw [hcp]
        have h6 : ((e.toMonoidHom c : ↥T) : Y) = ((c : ↥S) : Y) := rfl
        show (p : Y) ∈ C
        rw [← h5, h6]
        exact hcY
      · intro hp
        have hpY : (p : Y) ∈ C := hp
        refine ⟨⟨⟨(p : Y), hTS p.2⟩, p.2⟩, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hpY)
        · exact Subtype.ext rfl
    have hmap2 : (C.subgroupOf T).map e.symm.toMonoidHom =
        C₀.subgroupOf (T.subgroupOf S) := by
      rw [← hmap, Subgroup.map_map]
      simp
    rw [← hmap2]
    exact CFSG.Quasithin.C58.characteristic_map_mulEquiv hCchar e.symm
  have hnorm : (⊤ : Subgroup ↥S) ≤ Subgroup.normalizer ((C₀ : Subgroup ↥S) : Set ↥S) := by
    rw [Subgroup.le_normalizer_iff]
    intro x _ c hc
    have hcC : (c : Y) ∈ C := hc
    have hxS : (x : Y) ∈ S := x.2
    have hconj := (Subgroup.le_normalizer_iff.mp hSN) (x : Y) hxS (c : Y) hcC
    exact hconj
  exact h C₀ hC₀T hC₀ne hchar hnorm

theorem finite_sup_of_le_normalizer {G : Type*} [Group G] {X P A : Subgroup G} [Finite X]
    [Finite A] (hPX : P ≤ X) (hA : A ≤ Subgroup.normalizer (P : Set G)) : Finite ↥(P ⊔ A) := by
  haveI : Finite ↥P := Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
  refine Finite.of_surjective
    (fun pa : ↥P × ↥A => (⟨(pa.1 : G) * (pa.2 : G), Subgroup.mul_mem_sup pa.1.2 pa.2.2⟩ :
      ↥(P ⊔ A))) ?_
  rintro ⟨x, hx⟩
  obtain ⟨p, hp, a, ha, rfl⟩ := mem_sup_of_le_normalizer hA hx
  exact ⟨(⟨p, hp⟩, ⟨a, ha⟩), Subtype.ext rfl⟩

end Finite

end Group

@[expose] def PushUpFacts (n : ℕ) : Prop :=
  ∀ (F : Type) [Group F] [Finite F] (X P A : Subgroup F), CharTwo X →
    IsL2Quot n (oTwoQuot ↥X) → IsSylowTwoOf P X → NoCharNormal P X →
    A ≤ Subgroup.normalizer (P : Set F) → Odd (Nat.card A) →
    pushZ X P ≠ ⊥ ∧ conjJoinOf A (pushZ X P) ≤ pCoreOf 2 X ∧
      X ≤ Subgroup.normalizer (conjJoinOf A (pushZ X P) : Set F)

theorem pushUpFacts_of_eq_one_or_two {n : ℕ} (hn : n = 1 ∨ n = 2) : PushUpFacts n :=
  fun _ _ _ _ _ _ hchar hquot hP hnc hA hAo =>
    ⟨pushZ_ne_bot hn hquot hP, conjJoinOf_pushZ_le hn hchar hquot hP hnc hA hAo⟩

section Arbitrary

variable {G : Type} [Group G] {X P A : Subgroup G} [Finite X] [Finite A] {n : ℕ}

theorem map_conj_subgroupOf_map {Y F : Type*} [Group Y] [Group F] {B : Subgroup Y}
    (φ : ↥B →* F) (hφ : Function.Injective φ) {S : Subgroup Y} (hSB : S ≤ B)
    (a : Y) (ha : a ∈ B) :
    ((S.map (MulAut.conj a).toMonoidHom).subgroupOf B).map φ =
      ((S.subgroupOf B).map φ).map (MulAut.conj (φ ⟨a, ha⟩)).toMonoidHom := by
  have h1 : (S.map (MulAut.conj a).toMonoidHom).subgroupOf B =
      (S.subgroupOf B).map (MulAut.conj (⟨a, ha⟩ : ↥B)).toMonoidHom := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwy⟩
      exact ⟨⟨w, hSB hw⟩, hw, Subtype.ext hwy⟩
    · rintro ⟨w, hw, hwy⟩
      exact ⟨(w : Y), hw, congrArg Subtype.val hwy⟩
  rw [h1, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext w
  show φ ((⟨a, ha⟩ : ↥B) * w * (⟨a, ha⟩ : ↥B)⁻¹) = φ ⟨a, ha⟩ * φ w * (φ ⟨a, ha⟩)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem pushUp_odd_of_pushUpFacts (hF : PushUpFacts n) (hchar : CharTwo X)
    (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X)
    (hA : A ≤ Subgroup.normalizer (P : Set G)) (hAo : Odd (Nat.card A)) :
    ∃ Z : Subgroup G, Z ≠ ⊥ ∧ Z ≤ pCoreOf 2 X ∧
      (⨆ a ∈ A, Z.map (MulAut.conj a).toMonoidHom) ≤ pCoreOf 2 X ∧
      X ≤ Subgroup.normalizer ((⨆ a ∈ A, Z.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) := by
  classical
  have hPX : P ≤ X := hP.1
  have hPcoreP : pCoreOf 2 X ≤ P := pCoreOf_le_of_isSylowTwoOf hP
  haveI hfinPA : Finite ↥(P ⊔ A) :=
    finite_sup_of_le_normalizer (X := X) (P := P) (A := A) hPX hA
  obtain ⟨F, instF, finF, f, g, hf, hg, hagree⟩ :=
    CFSG.GroupTheory.exists_finite_amalgam_embedding
      (Subgroup.inclusion hPX) (Subgroup.inclusion (le_sup_left : P ≤ P ⊔ A))
      (Subgroup.inclusion_injective hPX)
      (Subgroup.inclusion_injective (le_sup_left : P ≤ P ⊔ A))
  letI : Group F := instF
  letI : Finite F := finF
  let X' : Subgroup F := (⊤ : Subgroup ↥X).map f
  let P' : Subgroup F := (P.subgroupOf X).map f
  let P₂ : Subgroup F := (P.subgroupOf (P ⊔ A)).map g
  let A' : Subgroup F := (A.subgroupOf (P ⊔ A)).map g
  let eX : ↥X ≃* ↥X' := (Subgroup.topEquiv (G := ↥X)).symm.trans
    (Subgroup.equivMapOfInjective (⊤ : Subgroup ↥X) f hf)
  have heX : ∀ x : ↥X, (eX x : F) = f x := fun _ => rfl
  have hfg : ∀ (p : G) (hp : p ∈ P), f ⟨p, hPX hp⟩ = g ⟨p, (le_sup_left : P ≤ P ⊔ A) hp⟩ := by
    intro p hp
    have h3 := congrArg (fun φ : ↥P →* F => φ ⟨p, hp⟩) hagree
    simp only [MonoidHom.comp_apply] at h3
    have h4 : (Subgroup.inclusion hPX ⟨p, hp⟩ : ↥X) = ⟨p, hPX hp⟩ := Subtype.ext rfl
    have h5 : (Subgroup.inclusion (le_sup_left : P ≤ P ⊔ A) ⟨p, hp⟩ : ↥(P ⊔ A)) =
        ⟨p, (le_sup_left : P ≤ P ⊔ A) hp⟩ := Subtype.ext rfl
    rw [h4, h5] at h3
    exact h3
  have hP'le : P' ≤ X' := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨p, Subgroup.mem_top p, rfl⟩
  have hP'P₂ : P' = P₂ := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpP : (p : G) ∈ P := hp
      exact ⟨⟨(p : G), (le_sup_left : P ≤ P ⊔ A) hpP⟩, Subgroup.mem_subgroupOf.mpr hpP,
        (hfg (p : G) hpP).symm⟩
    · rintro ⟨q, hq, rfl⟩
      have hqP : (q : G) ∈ P := hq
      exact ⟨⟨(q : G), hPX hqP⟩, Subgroup.mem_subgroupOf.mpr hqP, hfg (q : G) hqP⟩
  have hP'eX : (P.subgroupOf X).map eX.toMonoidHom = P'.subgroupOf X' := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, (heX p).symm⟩
    · rintro ⟨p, hp, hfp⟩
      exact ⟨p, hp, Subtype.ext (by show (eX p : F) = (y : F); rw [heX p]; exact hfp)⟩
  have hchar' : CharTwo X' := CFSG.Quasithin.Rk2.charTwo_of_equiv eX hchar
  have hquot' : IsL2Quot n (oTwoQuot ↥X') := by
    obtain ⟨e⟩ := hquot
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr eX).symm.trans e⟩
  have hP' : IsSylowTwoOf P' X' := by
    have h1 : IsSylowTwoOf (P.subgroupOf X) ⊤ := by
      rw [CFSG.Quasithin.A312.isSylowTwoOf_top_iff_map X (P.subgroupOf X),
        Subgroup.map_subgroupOf_eq_of_le hPX]
      exact hP
    have h2 : IsSylowTwoOf ((P.subgroupOf X).map eX.toMonoidHom) ⊤ :=
      CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_map_mulEquiv eX h1
    rw [hP'eX] at h2
    have h3 := (CFSG.Quasithin.A312.isSylowTwoOf_top_iff_map X' (P'.subgroupOf X')).mp h2
    rwa [Subgroup.map_subgroupOf_eq_of_le hP'le] at h3
  have hnc' : NoCharNormal P' X' := by
    refine noCharNormal_of_subgroupOf hP'le ?_
    rw [← hP'eX]
    have h := noCharNormal_map_mulEquiv eX (noCharNormal_subgroupOf hPX hnc)
    rwa [Subgroup.map_top_of_surjective _ eX.surjective] at h
  have hA'le : A' ≤ Subgroup.normalizer (P' : Set F) := by
    rw [hP'P₂]
    rw [Subgroup.le_normalizer_iff]
    intro a' ha' p hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hp
    have hconj : (q : G) * (r : G) * (q : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hA hq) (r : G)).mp hr
    refine Subgroup.mem_map.mpr ⟨⟨_, (le_sup_left : P ≤ P ⊔ A) hconj⟩,
      Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
    have heq : (⟨(q : G) * (r : G) * (q : G)⁻¹, (le_sup_left : P ≤ P ⊔ A) hconj⟩ :
        ↥(P ⊔ A)) = q * r * q⁻¹ := Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_inv]
  have hA'o : Odd (Nat.card A') := by
    have hcard : Nat.card ↥A' = Nat.card ↥A := by
      rw [show Nat.card ↥A' = Nat.card ↥(A.subgroupOf (P ⊔ A)) from
        Subgroup.card_map_of_injective hg,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ P ⊔ A)).toEquiv]
    rwa [hcard]
  obtain ⟨hZFne, hWFle₀, hWFN₀⟩ := hF F X' P' A' hchar' hquot' hP' hnc' hA'le hA'o
  have hpCore_eq : pCoreOf 2 X' = (CFSG.Open.pCore 2 ↥X).map f := by
    rw [show X' = (⊤ : Subgroup ↥X).map f from rfl,
      CFSG.Quasithin.H13.U3.GC137.S2.pCoreOf_map_injective f hf,
      CFSG.Quasithin.F53Push.pCoreOf_top_eq ↥X]
  have hpCore_g : pCoreOf 2 X' = ((pCoreOf 2 X).subgroupOf (P ⊔ A)).map g := by
    rw [hpCore_eq, ← CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf 2 X]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxP : (x : G) ∈ P := hPcoreP (Subgroup.mem_subgroupOf.mp hx)
      exact ⟨⟨(x : G), (le_sup_left : P ≤ P ⊔ A) hxP⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), (hfg (x : G) hxP).symm⟩
    · rintro ⟨p, hp, rfl⟩
      have hpP : (p : G) ∈ P := hPcoreP (Subgroup.mem_subgroupOf.mp hp)
      exact ⟨⟨(p : G), hPX hpP⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hp),
        hfg (p : G) hpP⟩
  set WF : Subgroup F := conjJoinOf A' (pushZ X' P') with hWFdef
  have hWFle : WF ≤ pCoreOf 2 X' := hWFle₀
  have hWFN : X' ≤ Subgroup.normalizer (WF : Set F) := hWFN₀
  have hWFAN : A' ≤ Subgroup.normalizer (WF : Set F) :=
    CFSG.Quasithin.F53Push.le_normalizer_conjJoin A' (pushZ X' P')
  have hWFne : WF ≠ ⊥ := by
    intro h0
    refine hZFne (le_bot_iff.mp ?_)
    rw [hWFdef] at h0
    calc pushZ X' P' ≤ conjJoinOf A' (pushZ X' P') :=
          CFSG.Quasithin.F53Push.le_conjJoin
      _ = ⊥ := h0
  have hP'range : P' ≤ g.range := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨⟨(p : G), (le_sup_left : P ≤ P ⊔ A) hp⟩, (hfg (p : G) hp).symm⟩
  have hWFP₂ : WF ≤ P₂ := hWFle.trans (by
    rw [hpCore_g]
    exact Subgroup.map_mono (fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hPcoreP (Subgroup.mem_subgroupOf.mp hx))))
  have hWFrange : WF ≤ g.range := by
    have h1 := hWFP₂
    rw [← hP'P₂] at h1
    exact h1.trans hP'range
  set Z : Subgroup G := (WF.comap g).map (P ⊔ A).subtype with hZdef
  have hZsub : Z.subgroupOf (P ⊔ A) = WF.comap g :=
    Subgroup.comap_map_eq_self_of_injective (P ⊔ A).subtype_injective _
  have hZmap : (Z.subgroupOf (P ⊔ A)).map g = WF := by
    rw [hZsub]
    exact Subgroup.map_comap_eq_self hWFrange
  have hZmem : ∀ (z : G) (hz : z ∈ P ⊔ A), z ∈ Z ↔ g ⟨z, hz⟩ ∈ WF := by
    intro z hz
    have h1 : z ∈ Z ↔ g ⟨z, hz⟩ ∈ (Z.subgroupOf (P ⊔ A)).map g := by
      rw [Subgroup.mem_map_iff_mem hg]
      exact Iff.rfl
    rw [h1, hZmap]
  have hZlePA : Z ≤ P ⊔ A := by
    rintro z ⟨y, -, rfl⟩
    exact y.2
  have hZleP : Z ≤ P := by
    have h2 : WF.comap g ≤ P.subgroupOf (P ⊔ A) := by
      have h3 : WF.comap g ≤ P₂.comap g := Subgroup.comap_mono hWFP₂
      rwa [Subgroup.comap_map_eq_self_of_injective hg] at h3
    calc Z = (WF.comap g).map (P ⊔ A).subtype := rfl
      _ ≤ (P.subgroupOf (P ⊔ A)).map (P ⊔ A).subtype := Subgroup.map_mono h2
      _ = P := Subgroup.map_subgroupOf_eq_of_le (le_sup_left : P ≤ P ⊔ A)
  have hZleX : Z ≤ X := hZleP.trans hPX
  have hZXmap : (Z.subgroupOf X).map f = WF := by
    rw [← hZmap]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxP : (x : G) ∈ P := hZleP hx
      exact ⟨⟨(x : G), (le_sup_left : P ≤ P ⊔ A) hxP⟩, hx, (hfg (x : G) hxP).symm⟩
    · rintro ⟨p, hp, rfl⟩
      have hpP : (p : G) ∈ P := hZleP hp
      exact ⟨⟨(p : G), hPX hpP⟩, hp, hfg (p : G) hpP⟩
  have hZA : ∀ a ∈ A, Z.map (MulAut.conj a).toMonoidHom = Z := by
    intro a ha
    have haPA : a ∈ P ⊔ A := (le_sup_right : A ≤ P ⊔ A) ha
    have hga : g ⟨a, haPA⟩ ∈ A' := ⟨⟨a, haPA⟩, ha, rfl⟩
    have hN : g ⟨a, haPA⟩ ∈ Subgroup.normalizer (WF : Set F) := hWFAN hga
    have hZaPA : Z.map (MulAut.conj a).toMonoidHom ≤ P ⊔ A := by
      rw [Subgroup.map_le_iff_le_comap]
      intro z hz
      rw [Subgroup.mem_comap]
      change a * z * a⁻¹ ∈ P ⊔ A
      exact (P ⊔ A).mul_mem ((P ⊔ A).mul_mem haPA (hZlePA hz)) ((P ⊔ A).inv_mem haPA)
    have hkey : ((Z.map (MulAut.conj a).toMonoidHom).subgroupOf (P ⊔ A)).map g =
        (Z.subgroupOf (P ⊔ A)).map g := by
      rw [map_conj_subgroupOf_map g hg hZlePA a haPA, hZmap]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
    have hsub := Subgroup.map_injective hg hkey
    have hfin := congrArg (fun K : Subgroup ↥(P ⊔ A) => K.map (P ⊔ A).subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hZaPA, Subgroup.map_subgroupOf_eq_of_le hZlePA] at hfin
  have hZcore : Z ≤ pCoreOf 2 X := by
    intro z hz
    have hzP : z ∈ P := hZleP hz
    have hzPA : z ∈ P ⊔ A := (le_sup_left : P ≤ P ⊔ A) hzP
    have h1 : g ⟨z, hzPA⟩ ∈ pCoreOf 2 X' := hWFle ((hZmem z hzPA).mp hz)
    rw [hpCore_g] at h1
    have h2 : (⟨z, hzPA⟩ : ↥(P ⊔ A)) ∈ (pCoreOf 2 X).subgroupOf (P ⊔ A) :=
      (Subgroup.mem_map_iff_mem hg).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hZX : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z := by
    intro x hx
    have hZXle : Z.map (MulAut.conj x).toMonoidHom ≤ X := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
      exact hPX (hPcoreP ((Subgroup.le_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)) x hx z (hZcore hz)))
    have hN : f ⟨x, hx⟩ ∈ Subgroup.normalizer (WF : Set F) := by
      have h4 : (eX ⟨x, hx⟩ : F) ∈ Subgroup.normalizer (WF : Set F) :=
        hWFN (eX ⟨x, hx⟩).2
      rwa [heX] at h4
    have hkey : ((Z.map (MulAut.conj x).toMonoidHom).subgroupOf X).map f =
        (Z.subgroupOf X).map f := by
      rw [map_conj_subgroupOf_map f hf hZleX x hx, hZXmap]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
    have hsub := Subgroup.map_injective hf hkey
    have hfin := congrArg (fun K : Subgroup ↥X => K.map X.subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hZXle, Subgroup.map_subgroupOf_eq_of_le hZleX] at hfin
  have hJoin : (⨆ a ∈ A, Z.map (MulAut.conj a).toMonoidHom) = Z := by
    refine le_antisymm (iSup₂_le fun a ha => (hZA a ha).le) ?_
    have h1 : Z.map (MulAut.conj (1 : G)).toMonoidHom = Z := by
      ext z
      simp
    calc Z = Z.map (MulAut.conj (1 : G)).toMonoidHom := h1.symm
      _ ≤ ⨆ a ∈ A, Z.map (MulAut.conj a).toMonoidHom :=
          le_iSup₂ (f := fun a (_ : a ∈ A) => Z.map (MulAut.conj a).toMonoidHom) 1 A.one_mem
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro h0
    have hmapbot : (Z.subgroupOf (P ⊔ A)).map g = ⊥ := by
      rw [h0, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    rw [hZmap] at hmapbot
    exact hWFne hmapbot
  · exact hZcore
  · rw [hJoin]
    exact hZcore
  · rw [hJoin]
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hZX x hx

end Arbitrary

section LemmaR

variable {G : Type} [Group G] {V : Type*} [MulAction G V] {Γ : SimpleGraph V}

theorem lemmaR_of_faithful_of_pushUpFacts (hconn : Γ.Connected)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfaith : ∀ g : G, (∀ v : V, g • v = v) → g = 1) (hnbr : ∀ v : V, ∃ w, Γ.Adj v w)
    {α β : V} (hαβ : Γ.Adj α β) (hfinα : Finite ↥(MulAction.stabilizer G α))
    (hfinβ : Finite ↥(MulAction.stabilizer G β)) {W T : Subgroup G} {n : ℕ}
    (hF : PushUpFacts n) (hWβ : W ≤ MulAction.stabilizer G β)
    (hWtr : ∀ a b : V, Γ.Adj β a → Γ.Adj β b → ∃ w ∈ W, w • a = b)
    (hchar : CharTwo W) (hquot : IsL2Quot n (oTwoQuot ↥W))
    (hT : IsSylowTwoOf T W) (hTα : T ≤ MulAction.stabilizer G α) (hnc : NoCharNormal T W)
    {x : G} (hxα : x ∈ MulAction.stabilizer G α) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxo : Odd (orderOf x))
    (hxtr : ∀ a b : V, Γ.Adj α a → Γ.Adj α b → ∃ k : ℤ, x ^ k • a = b) : False := by
  classical
  haveI hstabβ : Finite ↥(MulAction.stabilizer G β) := hfinβ
  haveI hstabα : Finite ↥(MulAction.stabilizer G α) := hfinα
  haveI hWfin : Finite ↥W :=
    Finite.of_injective (Subgroup.inclusion hWβ) (Subgroup.inclusion_injective hWβ)
  let A : Subgroup G := Subgroup.zpowers x
  have hxA : x ∈ A := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  haveI hAfin : Finite ↥A := by
    have hAle : A ≤ MulAction.stabilizer G α := by
      rw [show A = Subgroup.zpowers x from rfl]
      exact Subgroup.zpowers_le.mpr hxα
    exact Finite.of_injective (Subgroup.inclusion hAle) (Subgroup.inclusion_injective hAle)
  have hAo : Odd (Nat.card ↥A) := by
    rw [show Nat.card ↥A = orderOf x from Nat.card_zpowers x]
    exact hxo
  have hA : A ≤ Subgroup.normalizer (T : Set G) := by
    rw [show A = Subgroup.zpowers x from rfl]
    exact Subgroup.zpowers_le.mpr hxT
  obtain ⟨Z, hZne, hZle, hYle, hYN⟩ :=
    pushUp_odd_of_pushUpFacts (X := W) (P := T) (A := A) hF hchar hquot hT hnc hA hAo
  set Y : Subgroup G := ⨆ a ∈ A, Z.map (MulAut.conj a).toMonoidHom with hYdef
  have hZY : Z ≤ Y := by
    have h1 : Z.map (MulAut.conj (1 : G)).toMonoidHom = Z := by ext z; simp
    rw [hYdef]
    calc Z = Z.map (MulAut.conj (1 : G)).toMonoidHom := h1.symm
      _ ≤ ⨆ a ∈ A, Z.map (MulAut.conj a).toMonoidHom :=
          le_iSup₂ (f := fun a (_ : a ∈ A) => Z.map (MulAut.conj a).toMonoidHom) 1 A.one_mem
  have hYne : Y ≠ ⊥ := fun h0 => hZne (le_bot_iff.mp (h0 ▸ hZY))
  have hYle' : Y ≤ pCoreOf 2 W := hYle
  have hYleT : Y ≤ T := hYle'.trans (pCoreOf_le_of_isSylowTwoOf hT)
  have hYstabs : Y ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β :=
    le_inf (hYleT.trans hTα) (hYleT.trans (hT.1.trans hWβ))
  have hYN' : W ≤ Subgroup.normalizer (Y : Set G) := hYN
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map (MulAut.conj x).toMonoidHom Y = Y
    have hY1 : Y = ⨆ b : A, Subgroup.map (MulAut.conj (b : G)).toMonoidHom Z := by
      rw [hYdef]
      exact iSup_subtype'
    have hstep : ∀ b : A, Subgroup.map (MulAut.conj x).toMonoidHom
          (Subgroup.map (MulAut.conj (b : G)).toMonoidHom Z) =
          Subgroup.map (MulAut.conj (x * (b : G))).toMonoidHom Z := by
      intro b
      rw [Subgroup.map_map]
      congr 1
      ext z
      show x * ((b : G) * z * (b : G)⁻¹) * x⁻¹ = (x * (b : G)) * z * (x * (b : G))⁻¹
      group
    rw [hY1, Subgroup.map_iSup]
    refine le_antisymm (iSup_le fun b => ?_) (iSup_le fun b => ?_)
    · rw [hstep b]
      exact le_iSup (fun c : A => Subgroup.map (MulAut.conj (c : G)).toMonoidHom Z)
        ⟨x * (b : G), A.mul_mem hxA b.2⟩
    · have hxb : x * (x⁻¹ * (b : G)) = (b : G) := by group
      calc Subgroup.map (MulAut.conj (b : G)).toMonoidHom Z
          = Subgroup.map (MulAut.conj (x * (x⁻¹ * (b : G)))).toMonoidHom Z := by rw [hxb]
        _ = Subgroup.map (MulAut.conj x).toMonoidHom
              (Subgroup.map (MulAut.conj ((⟨x⁻¹ * (b : G),
                A.mul_mem (A.inv_mem hxA) b.2⟩ : A) : G)).toMonoidHom Z) :=
            (hstep ⟨x⁻¹ * (b : G), A.mul_mem (A.inv_mem hxA) b.2⟩).symm
        _ ≤ ⨆ c : A, Subgroup.map (MulAut.conj x).toMonoidHom
              (Subgroup.map (MulAut.conj (c : G)).toMonoidHom Z) :=
            le_iSup (fun c : A => Subgroup.map (MulAut.conj x).toMonoidHom
              (Subgroup.map (MulAut.conj (c : G)).toMonoidHom Z))
              ⟨x⁻¹ * (b : G), A.mul_mem (A.inv_mem hxA) b.2⟩
  have hβ : ∀ a b : V, Γ.Adj β a → Γ.Adj β b →
      ∃ g ∈ Subgroup.normalizer (Y : Set G) ⊓ MulAction.stabilizer G β, g • a = b := by
    intro a b ha hb
    obtain ⟨w, hw, hwab⟩ := hWtr a b ha hb
    exact ⟨w, ⟨hYN' hw, hWβ hw⟩, hwab⟩
  have hαtr : ∀ a b : V, Γ.Adj α a → Γ.Adj α b →
      ∃ g ∈ Subgroup.normalizer (Y : Set G) ⊓ MulAction.stabilizer G α, g • a = b := by
    intro a b ha hb
    obtain ⟨k, hk⟩ := hxtr a b ha hb
    refine ⟨x ^ k, ⟨?_, ?_⟩, hk⟩
    · exact Subgroup.zpowers_le.mpr hxY (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    · exact Subgroup.zpowers_le.mpr hxα (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have hbot : Y = ⊥ :=
    eq_bot_of_normalizer_trans_of_faithful hconn hadj hfaith hnbr hαβ hYstabs hαtr hβ
  exact hYne hbot

theorem lemmaR_of_faithful (hconn : Γ.Connected)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfaith : ∀ g : G, (∀ v : V, g • v = v) → g = 1) (hnbr : ∀ v : V, ∃ w, Γ.Adj v w)
    {α β : V} (hαβ : Γ.Adj α β) (hfinα : Finite ↥(MulAction.stabilizer G α))
    (hfinβ : Finite ↥(MulAction.stabilizer G β)) {W T : Subgroup G} {n : ℕ}
    (hn : n = 1 ∨ n = 2) (hWβ : W ≤ MulAction.stabilizer G β)
    (hWtr : ∀ a b : V, Γ.Adj β a → Γ.Adj β b → ∃ w ∈ W, w • a = b)
    (hchar : CharTwo W) (hquot : IsL2Quot n (oTwoQuot ↥W))
    (hT : IsSylowTwoOf T W) (hTα : T ≤ MulAction.stabilizer G α) (hnc : NoCharNormal T W)
    {x : G} (hxα : x ∈ MulAction.stabilizer G α) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxo : Odd (orderOf x))
    (hxtr : ∀ a b : V, Γ.Adj α a → Γ.Adj α b → ∃ k : ℤ, x ^ k • a = b) : False :=
  lemmaR_of_faithful_of_pushUpFacts hconn hadj hfaith hnbr hαβ hfinα hfinβ
    (pushUpFacts_of_eq_one_or_two hn) hWβ hWtr hchar hquot hT hTα hnc hxα hxT hxo hxtr

theorem lemmaR_of_pushUpFacts (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) {W T : Subgroup G}
    {n : ℕ} (hF : PushUpFacts n) (hWβ : W ≤ MulAction.stabilizer G β)
    (hWtr : ∀ a b : V, Γ.Adj β a → Γ.Adj β b → ∃ w ∈ W, w • a = b)
    (hchar : CharTwo W) (hquot : IsL2Quot n (oTwoQuot ↥W))
    (hT : IsSylowTwoOf T W) (hTα : T ≤ MulAction.stabilizer G α) (hnc : NoCharNormal T W)
    {x : G} (hxα : x ∈ MulAction.stabilizer G α) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxo : Odd (orderOf x))
    (hxtr : ∀ a b : V, Γ.Adj α a → Γ.Adj α b → ∃ k : ℤ, x ^ k • a = b) : False :=
  lemmaR_of_faithful_of_pushUpFacts h.isTree.connected h.adj_smul h.faithful h.exists_adj hαβ
    (h.finite_stab α) (h.finite_stab β) hF hWβ hWtr hchar hquot hT hTα hnc hxα hxT hxo hxtr

theorem lemmaR (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) {W T : Subgroup G} {n : ℕ}
    (hn : n = 1 ∨ n = 2) (hWβ : W ≤ MulAction.stabilizer G β)
    (hWtr : ∀ a b : V, Γ.Adj β a → Γ.Adj β b → ∃ w ∈ W, w • a = b)
    (hchar : CharTwo W) (hquot : IsL2Quot n (oTwoQuot ↥W))
    (hT : IsSylowTwoOf T W) (hTα : T ≤ MulAction.stabilizer G α) (hnc : NoCharNormal T W)
    {x : G} (hxα : x ∈ MulAction.stabilizer G α) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxo : Odd (orderOf x))
    (hxtr : ∀ a b : V, Γ.Adj α a → Γ.Adj α b → ∃ k : ℤ, x ^ k • a = b) : False :=
  lemmaR_of_faithful h.isTree.connected h.adj_smul h.faithful h.exists_adj hαβ
    (h.finite_stab α) (h.finite_stab β) hn hWβ hWtr hchar hquot hT hTα hnc hxα hxT hxo hxtr

end LemmaR

end CFSG.Quasithin.St84
