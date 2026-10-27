module

public import CFSG.Quasithin.Background.E1Sec7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCentralCoverAtCenterPrimes
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.H13.NParamLiftS5

public section

namespace CFSG.Quasithin.E1.ThinA5

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1.LiftS5

theorem exists_mulEquiv_alt_of_isPSL {X : Type} [Group X]
    (h : IsPSL 2 2 2 X) : Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, F, iF, iFin, hF, ⟨e⟩⟩ := h
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inl (by rw [hF]; norm_num))
  exact ⟨e.trans e5⟩

section Cover

variable {G : Type} [Group G] [Finite G] {H K : Subgroup G}

theorem pCoreOf_le_pCoreOf (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 K ≤ pCoreOf 2 H := by
  have hchar : (CFSG.Open.pCore 2 ↥K).Characteristic := by
    infer_instance
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (CFSG.Open.pCore 2 ↥K))

theorem mem_pCore_of_mem_pCoreOf (hKH : K ≤ H) (k : ↥K) (hk : (k : G) ∈ pCoreOf 2 H) :
    k ∈ CFSG.pCore 2 ↥K := by
  have hn : ((pCoreOf 2 H ⊓ K).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hg)) x
    constructor
    · rintro ⟨hxQ, hxK⟩
      exact ⟨h1.mp hxQ, K.mul_mem (K.mul_mem hg hxK) (K.inv_mem hg)⟩
    · rintro ⟨hxQ, hxK⟩
      refine ⟨h1.mpr hxQ, ?_⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hg) hxK) hg
      simpa [mul_assoc] using this
  have hp : IsPGroup 2 ↥((pCoreOf 2 H ⊓ K).subgroupOf K) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left |>.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : pCoreOf 2 H ⊓ K ≤ K)).symm
  exact CFSG.LieType.BorelTits.le_pCore 2 hn hp (show k ∈ (pCoreOf 2 H ⊓ K).subgroupOf K from
    ⟨hk, k.2⟩)

@[expose] noncomputable def toStar {M' : Subgroup G} (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M' H K) :=
  ((QuotientGroup.mk' ((kerIn M' H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (E2.star M' H K) (fun k => ⟨⟨k.1, hKH k.2⟩, k.2, rfl⟩)

omit [Finite G] in
theorem toStar_apply {M' : Subgroup G} (hKH : K ≤ H) (k : ↥K) :
    ((toStar (M' := M') hKH k : ↥(E2.star M' H K)) : E2.StarQuot M' H) =
      QuotientGroup.mk' ((kerIn M' H).subgroupOf H) ⟨k.1, hKH k.2⟩ := rfl

omit [Finite G] in
theorem toStar_surjective {M' : Subgroup G} (hKH : K ≤ H) :
    Function.Surjective (toStar (M' := M') hKH) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩

omit [Finite G] in
theorem toStar_eq_one_iff {M' : Subgroup G} (hKH : K ≤ H) (k : ↥K) :
    toStar (M' := M') hKH k = 1 ↔ (k : G) ∈ kerIn M' H := by
  rw [← Subtype.coe_inj, toStar_apply, Subgroup.coe_one, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem odd_card_center_quot_pCore {X : Type*} [Group X] [Finite X] :
    Odd (Nat.card ↥(Subgroup.center (X ⧸ CFSG.pCore 2 X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center (X ⧸ CFSG.pCore 2 X)) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.mp hodd
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center (X ⧸ CFSG.pCore 2 X))) 2 h2
  set w : X ⧸ CFSG.pCore 2 X := (z : X ⧸ CFSG.pCore 2 X) with hw
  have hwo : orderOf w = 2 := by
    rw [hw, Subgroup.orderOf_coe]
    exact hz
  have hwc : w ∈ Subgroup.center (X ⧸ CFSG.pCore 2 X) := z.2
  have hN : (Subgroup.zpowers w).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcomm : Commute g w := Subgroup.mem_center_iff.mp hwc g
    rw [(hcomm.zpow_right m).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers w m
  have hp : IsPGroup 2 ↥(Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwo]; norm_num)
  have hle := CFSG.LieType.BorelTits.le_pCore 2 hN hp
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
  have hw1 : w = 1 := by
    have : w ∈ (⊥ : Subgroup (X ⧸ CFSG.pCore 2 X)) := hle (Subgroup.mem_zpowers w)
    exact Subgroup.mem_bot.mp this
  rw [hw1, orderOf_one] at hwo
  omega

omit [Finite G] in
theorem isCyclic_of_card_dvd_sixty {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y ∣ 60)
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (S : Sylow r Y) : IsCyclic ↥(S : Subgroup Y) := by
  have h1 : Nat.card ↥(S : Subgroup Y) ∣ 60 := (Subgroup.card_subgroup_dvd_card _).trans hY
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 S.isPGroup'
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h2 : r ^ 2 ∣ 60 := (pow_dvd_pow r (by omega)).trans (hk ▸ h1)
    have h3 : r ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) h2
    have h4 : r ≤ 7 := by nlinarith
    have hp := hr.out
    interval_cases r <;> first | omega | (norm_num at hp)
  interval_cases k
  · have : Nat.card ↥(S : Subgroup Y) = 1 := by simpa using hk
    have hs : Subsingleton ↥(S : Subgroup Y) := (Nat.card_eq_one_iff_unique.mp this).1
    exact isCyclic_of_subsingleton
  · have : Nat.card ↥(S : Subgroup Y) = r := by simpa using hk
    exact isCyclic_of_prime_card this

theorem exists_quot_equiv_alt {M' : Subgroup G} (hKc : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hker : ∀ x : G, x ∈ kerIn M' H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hPSL : IsPSL 2 2 2 ↥(E2.star M' H K)) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨eS⟩ := exists_mulEquiv_alt_of_isPSL hPSL
  set O := CFSG.pCore 2 ↥K with hO
  set f := toStar (M' := M') hKH with hf
  have hOQ : ∀ k ∈ O, (k : G) ∈ pCoreOf 2 H := by
    intro k hk
    refine pCoreOf_le_pCoreOf hKH hKn ?_
    exact ⟨k, by assumption, rfl⟩
  have hQJ : ∀ x ∈ pCoreOf 2 H, x ∈ kerIn M' H := by
    intro x hx
    rw [hker]
    refine ⟨Subgroup.mem_sup_right hx, fun y hy => ?_⟩
    have hyH : y ∈ H := (sup_le hKH (CFSG.LieType.BorelTits.pCoreOf_le 2 H)) hy
    have := commutator_mem_pCoreOf hx hyH
    simpa [commutatorElement_def] using this
  have hOle : O ≤ f.ker := fun k hk => (toStar_eq_one_iff hKH k).2 (hQJ _ (hOQ k hk))
  set fb := QuotientGroup.lift O f hOle with hfb
  have hfbs : Function.Surjective fb := by
    intro y
    obtain ⟨k, rfl⟩ := toStar_surjective hKH y
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hker_le : fb.ker ≤ Subgroup.center (↥K ⧸ O) := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H k =>
      have hk1 : f k = 1 := hx
      have hkJ : (k : G) ∈ kerIn M' H := (toStar_eq_one_iff hKH k).1 hk1
      rw [Subgroup.mem_center_iff]
      intro w
      induction w using QuotientGroup.induction_on with
      | H k' =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hxJ : ((k : G)⁻¹) ∈ kerIn M' H := (kerIn M' H).inv_mem hkJ
        have hy : ((k' : G)⁻¹) ∈ K ⊔ pCoreOf 2 H := Subgroup.mem_sup_left (K.inv_mem k'.2)
        have hc := ((hker _).1 hxJ).2 _ hy
        refine mem_pCore_of_mem_pCoreOf hKH _ ?_
        simpa [mul_assoc] using hc
  have hperf : commutator (↥K ⧸ O) = ⊤ := by
    have hK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKc)
    have : Group.IsPerfect (↥K ⧸ O) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective O)
    exact Group.isPerfect_def.mp this
  have hcard : Nat.card ((↥K ⧸ O) ⧸ Subgroup.center (↥K ⧸ O)) ∣ 60 := by
    have h1 : (Subgroup.center (↥K ⧸ O)).index ∣ fb.ker.index := Subgroup.index_dvd_of_le hker_le
    have h2 : fb.ker.index = Nat.card fb.range := Subgroup.index_ker fb
    have h3 : Nat.card fb.range = 60 := by
      rw [MonoidHom.range_eq_top.mpr hfbs, Subgroup.card_top, Nat.card_congr eS.toEquiv,
        nat_card_alternatingGroup, Nat.card_fin]
      rfl
    rw [← Subgroup.index_eq_card]
    exact (h1.trans (h2 ▸ h3 ▸ dvd_rfl))
  have hZ : Subgroup.center (↥K ⧸ O) = ⊥ :=
    CFSG.GorensteinWalter.oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes hperf _ rfl
      odd_card_center_quot_pCore fun r _ _ hr2 S => isCyclic_of_card_dvd_sixty hcard hr2 S
  have hinj : Function.Injective fb := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hZ ▸ hker_le)
  exact ⟨(MulEquiv.ofBijective fb ⟨hinj, hfbs⟩).trans eS⟩

end Cover

end CFSG.Quasithin.E1.ThinA5
