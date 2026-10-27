module

public import CFSG.Quasithin.H13.NQS134HatInputs
public import CFSG.Quasithin.H13.NQS13410H
public import CFSG.Quasithin.H13.U3S13227P

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] def Stmt13_2_2_8Hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), A6.Setting134 G T L V →
    A6.IsHatA6 L →
      thompsonJ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = thompsonJ (pCoreOf 2 (L ⊔ T)) ∧
        baum (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = baum (pCoreOf 2 (L ⊔ T))

theorem k4x_even : ∀ σ ∈ U3.K4xList, Perm.sign σ = 1 → σ ∈ U3.K4List := by decide +kernel

@[expose] noncomputable def rhoL (S : A6.Setting134 G T L V) :
    ↥L →* ↥(alternatingGroup (Fin 6)) :=
  (S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le)).codRestrict _ fun l =>
    (S.frame.image_L _).1 ⟨Subgroup.inclusion S.frame.L_le l, l.2, rfl⟩

theorem rhoL_apply (S : A6.Setting134 G T L V) (l : ↥L) :
    (rhoL S l : Perm (Fin 6)) = S.frame.ρ ⟨l, S.frame.L_le l.2⟩ := rfl

@[expose] noncomputable def rhoQ (S : A6.Setting134 G T L V) :
    (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(alternatingGroup (Fin 6)) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥L) (rhoL S) fun x hx => by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [rhoL_apply, Subgroup.coe_one]
    exact (U3.s134_rho_eq_one_iff S _).2 (U3.s134_pCoreOf_L_le S ((A6.mem_pCore_iff x).1 hx))

theorem rhoQ_mk (S : A6.Setting134 G T L V) (l : ↥L) :
    rhoQ S (l : ↥L ⧸ CFSG.pCore 2 ↥L) = rhoL S l := rfl

theorem rhoQ_surjective (S : A6.Setting134 G T L V) : Function.Surjective (rhoQ S) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
  refine ⟨((⟨g, hgL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L), Subtype.ext ?_⟩
  rw [rhoQ_mk, rhoL_apply]
  exact hg

theorem rhoQ_ker (S : A6.Setting134 G T L V) :
    (rhoQ S).ker = center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | _ l =>
    rw [MonoidHom.mem_ker, rhoQ_mk]
    constructor
    · intro h
      have hC : (l : G) ∈ centralizer (V : Set G) := by
        refine (U3.s134_rho_eq_one_iff S ⟨l, S.frame.L_le l.2⟩).1 ?_
        rw [← rhoL_apply, h, Subgroup.coe_one]
      exact U3.s134_hat_mk_mem_center S hC
    · intro h
      have hZ : (l : G) ∈ A6.o2Z L := ⟨l, h, rfl⟩
      apply Subtype.ext
      rw [rhoL_apply, Subgroup.coe_one]
      exact (U3.s134_rho_eq_one_iff S _).2 (U3.s134_o2Z_le_centralizer S hZ)

@[expose] noncomputable def hatEquiv
    (S : A6.Setting134 G T L V) :
    (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(alternatingGroup (Fin 6)) :=
  (QuotientGroup.quotientMulEquivOfEq (rhoQ_ker S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (rhoQ S) (rhoQ_surjective S))

theorem hatEquiv_mk (S : A6.Setting134 G T L V) (l : ↥L) :
    (hatEquiv S (((l : ↥L ⧸ CFSG.pCore 2 ↥L) :
        (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L))) : Perm (Fin 6)) =
      S.frame.ρ ⟨l, S.frame.L_le l.2⟩ := rfl

omit [Finite G] in
@[expose] noncomputable def conjQuot (r : ↥(normalizer (L : Set G))) :
    MulAut (↥L ⧸ CFSG.pCore 2 ↥L) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) (conjAct L r)
    (Subgroup.characteristic_iff_map_eq.mp inferInstance (conjAct L r))

omit [Finite G] in
theorem conjQuot_mk (r : ↥(normalizer (L : Set G))) (l : ↥L) :
    conjQuot r (l : ↥L ⧸ CFSG.pCore 2 ↥L) = ((conjAct L r l : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) :=
  QuotientGroup.congr_mk _ _ _ _ l

theorem rho_sign_of_mem_R (hInv : HatA6OddInverts)
    (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) (r : ↥(normalizer (V : Set G)))
    (hr : (r : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) : Perm.sign (S.frame.ρ r) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hs
  have hs' : Perm.sign (S.frame.ρ r) = -1 := (Int.units_eq_one_or _).resolve_left hs
  have hrT : (r : G) ∈ T := s134_R_le_T S hr
  have hrL : (r : G) ∈ normalizer (L : Set G) := S.T_le_NL hrT
  set X := ↥L ⧸ CFSG.pCore 2 ↥L with hX
  set α := conjQuot (⟨r, hrL⟩ : ↥(normalizer (L : Set G))) with hα
  have hcompat : ∀ x : X, ((hatEquiv S (α x : X ⧸ center X) : Perm (Fin 6))) =
      S.frame.ρ r * (hatEquiv S (x : X ⧸ center X) : Perm (Fin 6)) * (S.frame.ρ r)⁻¹ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | _ l =>
      rw [hα, conjQuot_mk, hatEquiv_mk, hatEquiv_mk]
      have e : (⟨((conjAct L ⟨r, hrL⟩ l : ↥L) : G), S.frame.L_le (conjAct L ⟨r, hrL⟩ l).2⟩ :
          ↥(normalizer (V : Set G))) = r * ⟨l, S.frame.L_le l.2⟩ * r⁻¹ :=
        Subtype.ext (A5.conjAct_val L ⟨r, hrL⟩ l)
      rw [e, map_mul, map_mul, map_inv]
  have hinv := hInv X hhat.1 hhat.2.1 (hatEquiv S) α (S.frame.ρ r) hs' hcompat
  obtain ⟨c, hcL0, hc3, hcO, -⟩ := A6.exists_l0_c hhat.2.1
  have hcL1 : c ∈ L₁Of L (fsuV1 T V) := U3.s134_l0_le_L1 S hcL0
  have hcZ : c ∈ A6.o2Z L := oTwoRes_le _ hcL0
  obtain ⟨c', hc'Z, hc'c⟩ := hcZ
  have hc'c' : (c' : G) = c := hc'c
  rw [← hc'c'] at hcL1 hc3 hcO
  have hc'Z' : (c' : X) ∈ center X := hc'Z
  have h1 : α (c' : X) = (c' : X)⁻¹ := hinv _ hc'Z'
  have hcR : (c' : G) ∈ normalizer (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _ (mem_sup_left hcL1)
  have hcomm : (r : G) * c' * (r : G)⁻¹ * (c' : G)⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have h2 : (c' : G) * (r : G)⁻¹ * (c' : G)⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
      (mem_normalizer_iff.mp hcR _).mp (inv_mem hr)
    have e : (r : G) * c' * (r : G)⁻¹ * (c' : G)⁻¹ =
        (r : G) * ((c' : G) * (r : G)⁻¹ * (c' : G)⁻¹) := by group
    rw [e]
    exact mul_mem hr h2
  obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨_, hcomm⟩
  have hk' : ((r : G) * c' * (r : G)⁻¹ * (c' : G)⁻¹) ^ 2 ^ k = 1 := by
    have h2 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  set d : ↥L := conjAct L ⟨r, hrL⟩ c' * c'⁻¹ with hd
  have hdG : (d : G) = (r : G) * c' * (r : G)⁻¹ * (c' : G)⁻¹ := by
    rw [hd, Subgroup.coe_mul, A5.conjAct_val, Subgroup.coe_inv]
  have hd2 : d ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hdG, hk', Subgroup.coe_one])
  have hdX : (d : X) = (c' : X)⁻¹ * (c' : X)⁻¹ := by
    rw [hd, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← conjQuot_mk, ← hα, h1]
  have hc3' : (c' : X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : c' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hc3, Subgroup.coe_one])
    rw [this, QuotientGroup.mk_one]
  have hcX : (c' : X)⁻¹ * (c' : X)⁻¹ = (c' : X) := by
    calc (c' : X)⁻¹ * (c' : X)⁻¹ = (c' : X)⁻¹ * (c' : X)⁻¹ * (c' : X) ^ 3 := by
          rw [hc3', mul_one]
      _ = (c' : X) := by group
  have hc2 : (c' : X) ^ 2 ^ k = 1 := by
    rw [← hcX, ← hdX, ← QuotientGroup.mk_pow, hd2, QuotientGroup.mk_one]
  have hc1 : (c' : X) = 1 := by
    have h2 : orderOf (c' : X) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc2
    have h3 : orderOf (c' : X) ∣ 3 := orderOf_dvd_of_pow_eq_one hc3'
    have h4 : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h4 h2 h3)
  exact hcO ((A6.mem_pCore_iff c').1 ((QuotientGroup.eq_one_iff _).1 hc1))

theorem rho_mem_K4_of_mem_R (hInv : HatA6OddInverts)
    (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) (r : ↥(normalizer (V : Set G)))
    (hr : (r : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) : S.frame.ρ r ∈ U3.K4List := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := U3.s134Plus_l1plus S hhat
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := s134_R_le_T S
  have hle : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ pCoreOf 2 (l1plus T L V ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRT.trans le_sup_right)
      ((sup_le_sup_right P.le_L1 T).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hR1 : (r : G) ∈ U3.r1Of T L V := P.pCoreOf_eq_r1Of ▸ hle hr
  have hK := ((U3.s134_mem_r1Of_iff S).1 hR1).2 r.2
  exact k4x_even _ (U3.mem_K4xsub.1 hK) (rho_sign_of_mem_R hInv S hhat r hr)

theorem stmt13_2_2_8Hat_of (hInv : HatA6OddInverts) :
    Stmt13_2_2_8Hat := by
  intro G _ _ T L V S hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hRdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hRT : R ≤ T := s134_R_le_T S
  have hQ : T ⊓ centralizer (V : Set G) = Q := U3.s134_cT S
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := (oTwoRes_le _).trans inf_le_left
  have hQR : Q ≤ R := by
    have hQT : Q ≤ T := hQ ▸ inf_le_left
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      ((sup_le_sup_right hL1L T).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hVab := U3.s134_elemAbelian_V S
  have hVQ : V ≤ Q := by
    rw [← hQ]
    exact le_inf S.V_le_T fun v hv => mem_centralizer_iff.2 fun w hw =>
      congrArg Subtype.val (hVab.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  have hVR : V ≤ R := hVQ.trans hQR
  have hJ : thompsonJ R ≤ R ⊓ centralizer (V : Set G) := by
    refine iSup₂_le fun A hA => le_inf hA.1 ?_
    by_contra hAC
    have hAN : A ≤ normalizer (V : Set G) := hA.1.trans (hRT.trans S.frame.T_le)
    have hle := card_le_relIndex_mul_card hVab hVR hA
    have hlt := U3.s134_relIndex_mul_card_lt S hAN
      (fun a ha => rho_mem_K4_of_mem_R hInv S hhat a (hA.1 ha)) hAC
    rw [S.card_V] at hle
    omega
  have hRC : R ⊓ centralizer (V : Set G) = Q := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQR (hQ ▸ inf_le_right))
    rw [← hQ]
    exact mem_inf.2 ⟨hRT (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩
  refine ⟨(B6.thompsonJ_eq_of_le (S := R) (R := Q) (hJ.trans hRC.le) hQR).symm, ?_⟩
  rw [baum_eq_baum_centralizer hVab hVR hJ, hRC]

end CFSG.Quasithin.H13.NQS134
