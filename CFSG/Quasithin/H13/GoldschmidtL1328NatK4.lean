module

public import CFSG.Quasithin.H13.GoldschmidtL1328NatCount
public import CFSG.Quasithin.H13.NQS134Hat8
public import CFSG.Quasithin.H13.KGFactHatA6

public section

namespace CFSG.Quasithin.H13.A6

namespace L1328

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.NQS134 (conjQuot conjQuot_mk)

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

@[expose] noncomputable def rhoAlt : ↥L →* ↥(alternatingGroup (Fin 6)) :=
  (S.frame.ρ.comp (Subgroup.inclusion S.frame.L_le)).codRestrict _ fun l =>
    (S.frame.image_L _).1 ⟨Subgroup.inclusion S.frame.L_le l, l.2, rfl⟩

theorem rhoAlt_apply (l : ↥L) :
    (rhoAlt S l : Perm (Fin 6)) = S.frame.ρ ⟨l, S.frame.L_le l.2⟩ := rfl

@[expose] noncomputable def rhoAltQ :
    (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(alternatingGroup (Fin 6)) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥L) (rhoAlt S) fun x hx => by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [rhoAlt_apply, Subgroup.coe_one]
    exact (S.rho_eq_one_iff _).2 (S.pCoreOf_L_le_centralizer ((mem_pCore_iff x).1 hx))

theorem rhoAltQ_mk (l : ↥L) :
    rhoAltQ S (l : ↥L ⧸ CFSG.pCore 2 ↥L) = rhoAlt S l := rfl

theorem rhoAltQ_surjective : Function.Surjective (rhoAltQ S) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L σ).2 hσ
  refine ⟨((⟨g, hgL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L), Subtype.ext ?_⟩
  rw [rhoAltQ_mk, rhoAlt_apply]
  exact hg

theorem rhoAltQ_ker :
    (rhoAltQ S).ker = center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | _ l =>
    rw [MonoidHom.mem_ker, rhoAltQ_mk]
    constructor
    · intro h
      have hC : (l : G) ∈ centralizer (V : Set G) := by
        refine (S.rho_eq_one_iff ⟨l, S.frame.L_le l.2⟩).1 ?_
        rw [← rhoAlt_apply, h, Subgroup.coe_one]
      exact S.hat_mk_mem_center hC
    · intro h
      have hZ : (l : G) ∈ o2Z L := ⟨l, h, rfl⟩
      apply Subtype.ext
      rw [rhoAlt_apply, Subgroup.coe_one]
      exact (S.rho_eq_one_iff _).2 (S.o2Z_le_centralizer hZ)

@[expose] noncomputable def hatEquiv :
    (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(alternatingGroup (Fin 6)) :=
  (QuotientGroup.quotientMulEquivOfEq (rhoAltQ_ker S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (rhoAltQ S) (rhoAltQ_surjective S))

theorem hatEquiv_mk (l : ↥L) :
    (hatEquiv S (((l : ↥L ⧸ CFSG.pCore 2 ↥L) :
        (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L))) : Perm (Fin 6)) =
      S.frame.ρ ⟨l, S.frame.L_le l.2⟩ := rfl

theorem R_le_T : pCoreOf 2 (S.L1 ⊔ T) ≤ T :=
  pCoreOf_le_of_sylow S.h13.sylow le_sup_right

theorem rho_sign_of_mem_R (hhat : IsHatA6 L)
    (r : ↥(normalizer (V : Set G))) (hr : (r : G) ∈ pCoreOf 2 (S.L1 ⊔ T)) :
    Perm.sign (S.frame.ρ r) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hs
  have hs' : Perm.sign (S.frame.ρ r) = -1 := (Int.units_eq_one_or _).resolve_left hs
  have hrT : (r : G) ∈ T := R_le_T S hr
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
  have hinv := KGHatA6.hatA6OddInverts_holds X hhat.1 hhat.2.1 (hatEquiv S) α (S.frame.ρ r) hs'
    hcompat
  obtain ⟨c, hcL0, hc3, hcO, -⟩ := exists_l0_c hhat.2.1
  have hcL1 : c ∈ S.L1 := S.l0_le_L1 hcL0
  have hcZ : c ∈ o2Z L := oTwoRes_le _ hcL0
  obtain ⟨c', hc'Z, hc'c⟩ := hcZ
  have hc'c' : (c' : G) = c := hc'c
  rw [← hc'c'] at hcL1 hc3 hcO
  have hc'Z' : (c' : X) ∈ center X := hc'Z
  have h1 : α (c' : X) = (c' : X)⁻¹ := hinv _ hc'Z'
  have hcR : (c' : G) ∈ normalizer (pCoreOf 2 (S.L1 ⊔ T) : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _ (mem_sup_left hcL1)
  have hcomm : (r : G) * c' * (r : G)⁻¹ * (c' : G)⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) := by
    have h2 : (c' : G) * (r : G)⁻¹ * (c' : G)⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) :=
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
  exact hcO ((mem_pCore_iff c').1 ((QuotientGroup.eq_one_iff _).1 hc1))


theorem pCoreOf_rho_mem_E8 {Lp : Subgroup G}
    (P : S14.PlusData S Lp) {x : G} (hx : x ∈ pCoreOf 2 (Lp ⊔ T))
    (hxN : x ∈ normalizer (V : Set G)) : S.frame.ρ ⟨x, hxN⟩ ∈ S14.E8 := by
  classical
  have hP2T : pCoreOf 2 (Lp ⊔ T) ≤ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right
  set H' : Subgroup G := (S14.E8sub.comap S.frame.ρ).map (normalizer (V : Set G)).subtype
    with hH'
  have hmemH' : ∀ y : G, y ∈ H' ↔
      ∃ hy : y ∈ normalizer (V : Set G), S.frame.ρ ⟨y, hy⟩ ∈ S14.E8 := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hy, hE⟩
      exact ⟨⟨y, hy⟩, hE, rfl⟩
  have hYle : H' ⊓ T ≤ pCoreOf 2 (Lp ⊔ T) := fun y hy =>
    P.Ypre_le_pCoreOf
      (S14.mem_Ypre.2 ⟨(le_sup_right : T ≤ Lp ⊔ T) hy.2, (hmemH' y).1 hy.1⟩)
  have hidx : H'.relIndex T ≤ 2 := by
    refine S14.relIndex_le_two_of fun a ha b hb haH hbH => ?_
    have haN : a ∈ normalizer (V : Set G) := S.frame.T_le ha
    have hbN : b ∈ normalizer (V : Set G) := S.frame.T_le hb
    have haE : S.frame.ρ ⟨a, haN⟩ ∉ S14.E8 := fun h => haH ((hmemH' a).2 ⟨haN, h⟩)
    have hbE : S.frame.ρ ⟨b, hbN⟩ ∉ S14.E8 := fun h => hbH ((hmemH' b).2 ⟨hbN, h⟩)
    have h1 := S14.e8_index _ _ (S.frame.T_D ⟨a, haN⟩ ha) (S.frame.T_D ⟨b, hbN⟩ hb) haE hbE
    have habN : a⁻¹ * b ∈ normalizer (V : Set G) :=
      mul_mem (inv_mem haN) hbN
    refine (hmemH' _).2 ⟨habN, ?_⟩
    have e : (⟨a⁻¹ * b, habN⟩ : ↥(normalizer (V : Set G))) = ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩ := rfl
    rw [e, map_mul, map_inv]
    exact h1
  have h2 := Subgroup.relIndex_mul_relIndex (H' ⊓ T) (pCoreOf 2 (Lp ⊔ T)) T hYle hP2T
  rw [P.index2_eq, Subgroup.inf_relIndex_right] at h2
  have h3 : (H' ⊓ T).relIndex (pCoreOf 2 (Lp ⊔ T)) = 1 := by
    have h4 : (H' ⊓ T).relIndex (pCoreOf 2 (Lp ⊔ T)) * 2 ≤ 2 := by omega
    have h5 : (H' ⊓ T).relIndex (pCoreOf 2 (Lp ⊔ T)) ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hle : pCoreOf 2 (Lp ⊔ T) ≤ H' ⊓ T := Subgroup.relIndex_eq_one.1 h3
  exact ((hmemH' x).1 (hle hx).1).choose_spec

theorem rho_mem_K4_of_mem_R (hhat : IsHatA6 L)
    (r : ↥(normalizer (V : Set G))) (hr : (r : G) ∈ pCoreOf 2 (S.L1 ⊔ T)) :
    S.frame.ρ r ∈ K4L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P : S14.PlusData S (l1plus T L V) := S14.plusData_l1plus S (S.hatL1Plus hhat)
  have hRT : pCoreOf 2 (S.L1 ⊔ T) ≤ T := R_le_T S
  have hle : pCoreOf 2 (S.L1 ⊔ T) ≤ pCoreOf 2 (l1plus T L V ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRT.trans le_sup_right)
      ((sup_le_sup_right P.le_L1 T).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hE := pCoreOf_rho_mem_E8 S P (hle hr) r.2
  exact e8_even_K4 _ hE (rho_sign_of_mem_R S hhat r hr)

end L1328

end CFSG.Quasithin.H13.A6
