module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G2
public import CFSG.Quasithin.Vol2.Ch10SecV1N

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

namespace RCtx

variable {T L I R H : Subgroup G} (c : RCtx T L I R H)
include c

theorem false_of_c27 (hC27 : C27NoL2pJ1)
    (hK : LocalSQTK G) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {t : G} (ht : t ∈ T) {X K : Subgroup G}
    (hX : X = L ∨ X = CFSG.conjugate L t) (hKc : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : X < K) (hch : CharTwo K)
    (hq : CFSG.IsQuasisimple (ModO2 K))
    (htype : (∃ p : ℕ, p.Prime ∧ IsPSL 2 p 1 ↥(modO2Image H K) ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5)) ∨ (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 2 ↥(modO2Image H K)) ∨
      IsSporadic .J1 ↥(modO2Image H K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 (fsuL0 T L ⊔ T) with hQdef
  have hC23 := c.hypC23Cat hK h331 h37 h38
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := (c.pcore.trans c.R_le).trans hKn
  have hKM : ¬ K ≤ fsuM T L ⊓ H := fun h =>
    SecB.not_le_fsuM c.hyp ht hX hKc hXK (h.trans inf_le_left)
  exact hC27 G H Q (fsuM T L ⊓ H) K hC23 hKc hq hch hKM hQK _ (modO2_mulEquiv hKc) htype

theorem false_of_shape21 (hK : LocalSQTK G) (h36 : Vol2Native.A36CoreForSQTKCat)
    (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {t : G} (ht : t ∈ T) {X K : Subgroup G} (hX : X = L ∨ X = CFSG.conjugate L t)
    (hKc : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : X < K)
    (hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image H K))
    (h21 : modO2Image H K = modO2Image H X ⊔
      (CFSG.oddCore ↥(modO2Image H K)).map (modO2Image H K).subtype) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.hyp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  set Kb := modO2Image H K with hKb
  obtain ⟨hcase, hcommon, -⟩ := Vol2Native.lemma_1_2_1_four_core hK h36 c.two hKc
  have h3 : ¬ 3 ∣ Nat.card (CFSG.fittingSubgroup ↥Kb) := by
    rcases hcase with hc | ⟨p, hp, hp3, -, ⟨e⟩, -⟩ | ⟨-, -, -, hprimes⟩
    · exact absurd hc.1 hnq
    · intro h
      rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
        Nat.card_fin] at h
      have h3p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    · intro h
      have := (hprimes 3 Nat.prime_three h).1
      omega
  rw [← hcommon.1] at h21
  set Fb := (CFSG.fittingSubgroup ↥Kb).map Kb.subtype with hFb
  have hKbN : (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      Subgroup.normalizer (Kb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    have h1 := SecB.modO2Image_le_normalizer' (H := H) (A := H) (B := K) hKn
    have h2 : modO2Image H H = ⊤ := by
      rw [modO2Image, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rwa [h2] at h1
  have hFn : Fb.Normal := by
    refine ⟨fun f hf g => ?_⟩
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Kb) (CFSG.fittingSubgroup ↥Kb) (hKbN (Subgroup.mem_top g))
    exact (Subgroup.mem_normalizer_iff.mp h1 f).mp hf
  have hFnil : Group.IsNilpotent ↥Fb :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ Kb.subtype_injective)
  have hFF : Fb ≤ CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) := le_sSup ⟨hFn, hFnil⟩
  have hFc : ¬ 3 ∣ Nat.card Fb := by
    rw [hFb, Subgroup.card_map_of_injective Kb.subtype_injective]
    exact h3
  apply SecB.not_le_fsuM hyp ht hX hKc hXK
  intro k hk
  have hkb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨k, hKH hk⟩ : ↥H) ∈ Kb :=
    Subgroup.mem_map_of_mem _ (show (⟨k, hKH hk⟩ : ↥H) ∈ K.subgroupOf H from hk)
  rw [h21] at hkb
  obtain ⟨xb, hxb, fb, hfb, hxf⟩ := Subgroup.mem_sup_of_normal_right.mp hkb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hxb
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) fb
  have hfY : (f : G) ∈ oTwoFIn H := C2Six.mem_oTwoFIn_iff.mpr (hFF hfb)
  have hcop : (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
      (⟨(f : G), C2Six.oTwoFIn_le hfY⟩ : ↥H))).Coprime 3 := by
    have hd : orderOf (⟨_, hfb⟩ : ↥Fb) ∣ Nat.card Fb := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      fun h3' => hFc (h3'.trans ?_)))
    exact hd
  have hfM := c.mem_fsuM_of_coprime_three hK h331 h37 h38 hfY hcop
  have hxM : (x : G) ∈ fsuM T L := by
    have hxX : (x : G) ∈ X := hx
    rcases hX with rfl | rfl
    · exact ((SecA.le_fsuL0 T X).trans (SecA.fsuL0_le_fsuM T X)) hxX
    · exact ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_fsuM T L)) hxX
  rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxf
  have hO : ((x * f)⁻¹ * ⟨k, hKH hk⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by
    exact hxf
  have hoM : (((x * f)⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) ∈ fsuM T L := c.pCoreOf_le_fsuM ⟨_, hO, rfl⟩
  have hk' : k = (x : G) * (f : G) * (((x * f)⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) := by
    simp [mul_assoc]
  rw [hk']
  exact (fsuM T L).mul_mem ((fsuM T L).mul_mem hxM hfM) hoM

end RCtx

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
