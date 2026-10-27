module

public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.Background.C126Split
public import CFSG.Quasithin.H13.A6S13813d

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

theorem mem_oTwoRes_of_odd {G : Type} [Group G] {X : Subgroup G} {x : G} (hx : x ∈ X) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) : x ∈ oTwoRes X :=
  Subgroup.subset_closure ⟨hx, m, hm, hxm⟩

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1T_le_G1 (hS : S.Hyp138) : S.L1 ⊔ T ≤ S.G1 :=
  (hS.hF S.G1 hS.hG1).toHypF91.L₁T_le_H

theorem isSolvable_L1T (h1334 : Stmt13_3_4) (hS : S.Hyp138) : Group.IsSolvable ↥(S.L1 ⊔ T) := by
  have h23 := (h1334 G T L V S.h13 S.irr).2.2
  refine A5.isSolvable_of_isTwoThreeGroup (h23 _ le_sup_right ?_)
  refine lt_of_le_of_ne (sup_le_sup_right S.L1_le_L T) fun h => ?_
  have hL : L ≤ S.G1 := le_sup_left.trans (h.symm ▸ S.L1T_le_G1 hS)
  apply S.z_ne_one
  have hz : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨S.z_mem_V, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hL hl)
  rw [S.zv] at hz
  exact hz

theorem isTwoThreeGroup_oTwoRes_solvRad (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) :
    IsTwoThreeGroup (oTwoRes (solvRad H)) := by
  set M := Subgroup.normalizer (L : Set G) with hM
  set R := solvRad H with hR
  set Y := oTwoRes R with hY
  have hLT : S.L1 ⊔ T ≤ H := hH.1.1
  have hHR : H ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H)
  have hRM : R ≤ M := by
    have hsol : Group.IsSolvable ↥(R ⊔ (S.L1 ⊔ T)) :=
      C126.isSolvable_sup_of_le_normalizer' (hLT.trans hHR) (solvRad_isSolvable H)
        (S.isSolvable_L1T h1334 hS)
    have hle : R ⊔ (S.L1 ⊔ T) ≤ S.G1 := sup_le ((solvRad_le H).trans hH.2.1) (hLT.trans hH.2.1)
    exact le_sup_left.trans (h13 G T L V S hS _ le_sup_right hle hsol)
  have hYR : Y ≤ R := oTwoRes_le _
  have hYH : Y ≤ H := hYR.trans (solvRad_le H)
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := A5.le_normalizer_oTwoRes_of_le_normalizer hHR
  have hYY : oTwoRes Y = Y := by
    refine le_antisymm (oTwoRes_le _) ?_
    rw [hY, oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hy, m, hm, hym⟩, m, hm, hym⟩
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
    rw [S.zv, Subgroup.mem_bot] at h1
    exact S.z_ne_one h1
  have hYz : Y ≤ M ⊓ Subgroup.centralizer ({S.z} : Set G) :=
    le_inf (hYR.trans hRM) (hYH.trans hH.2.1)
  have hInH : InH T H := ⟨le_sup_right.trans hLT, hH.1.2⟩
  have hL1 : IsTwoThreeGroup S.L1 := by
    have h23 := (h1334 G T L V S.h13 S.irr).2.2
    have hLT23 : IsTwoThreeGroup (S.L1 ⊔ T) := by
      refine h23 _ le_sup_right (lt_of_le_of_ne (sup_le_sup_right S.L1_le_L T) fun h => ?_)
      have hL : L ≤ S.G1 := le_sup_left.trans (h.symm ▸ S.L1T_le_G1 hS)
      apply hzL
      exact Subgroup.mem_centralizer_iff.2 fun l hl =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hL hl))
    intro p hp hpd
    exact hLT23 p hp (hpd.trans (Subgroup.card_dvd_of_le le_sup_left))
  rcases h139 G T L V H Y S.z S.h13 S.irr S.a6 hInH hH.2.2 hYY hYH hHY hz hzL hYz with
    h | ⟨-, hA6, hhat⟩
  · intro p hp hpd
    rw [h, Subgroup.card_bot] at hpd
    exact absurd (Nat.le_of_dvd one_pos hpd) (by have := hp.two_le; omega)
  · by_cases hh : IsHatA6 L
    · rw [hhat hh]
      intro p hp hpd
      exact hL1 p hp (hpd.trans (Subgroup.card_dvd_of_le S.l1plus_le_L1))
    · rw [hA6 (S.nonempty_alt6_of_not_hat hh)]
      exact hL1

theorem isQuasisimple_modO2 (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.h13.simple
  have hloc : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  obtain ⟨hcases, -, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_1_four_core hloc h36 hH.1.2 hK
  obtain ⟨e⟩ := modO2_mulEquiv hK
  rcases hcases with hc | h34
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hc.1
  exfalso
  set X := ↥(modO2Image H K) with hXdef
  obtain ⟨p, hp, hp3, x, hx, hxo⟩ : ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ∃ x ∈ CFSG.fittingSubgroup X, orderOf x = p := by
    rcases h34 with ⟨p, hp, hp3, -, ⟨eF⟩, -⟩ | ⟨hFF, -, -, hprimes⟩
    · have : Fact p.Prime := ⟨hp⟩
      have hdvd : p ∣ Nat.card ↥(CFSG.fittingSubgroup X) := by
        rw [Nat.card_congr eF.toEquiv, Nat.card_eq_fintype_card]
        simp [ZMod.card]
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.fittingSubgroup X)) p hdvd
      exact ⟨p, hp, hp3, y, y.2, by rw [← hy, Subgroup.orderOf_coe]⟩
    ·
      have hne : CFSG.fittingSubgroup X ≠ ⊥ := by
        intro hbot
        have hC := CFSG.centralizer_generalizedFitting_le X
        rw [hFF, hbot] at hC
        have hX1 : ∀ y : X, y = 1 := fun y => by
          have : y ∈ Subgroup.centralizer ((⊥ : Subgroup X) : Set X) := by
            rw [Subgroup.mem_centralizer_iff]
            intro h hh
            rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
            rw [hh, one_mul, mul_one]
          exact Subgroup.mem_bot.mp (hC this)
        apply ne_bot_of_mem_cComp (modO2Image_mem_cComp hK)
        rw [eq_bot_iff]
        intro y hy
        have := hX1 ⟨y, hy⟩
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
        (fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1))
      have : Fact p.Prime := ⟨hp⟩
      have hp3 : 3 < p := by
        have h2 := hp.two_le
        rcases (hprimes p hp hpd).1 with h | h | h <;> omega
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.fittingSubgroup X)) p hpd
      exact ⟨p, hp, hp3, y, y.2, by rw [← hy, Subgroup.orderOf_coe]⟩
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set F' : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := (CFSG.fittingSubgroup X).map (modO2Image H K).subtype
    with hF'
  set FH : Subgroup ↥H := F'.comap π ⊓ K.subgroupOf H with hFH
  set Fh : Subgroup G := FH.map H.subtype with hFh
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hFhK : Fh ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.1 hy.2
  obtain ⟨hnil, hnorm, -⟩ := (CFSG.LocalCores.fitting_nilpotent (G := X))
  have hFsol : Group.IsSolvable ↥Fh := by
    have hF'sol : Group.IsSolvable ↥F' := by
      have : Group.IsSolvable ↥(CFSG.fittingSubgroup X) := by
        have := hnil
        infer_instance
      exact Group.isSolvable_of_surjective (f := ((CFSG.fittingSubgroup X).equivMapOfInjective _
        (modO2Image H K).subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    let g : ↥FH →* ↥F' := (π.comp FH.subtype).codRestrict F' fun y => y.2.1
    have hker : Group.IsSolvable ↥g.ker := by
      have h2 : IsPGroup 2 ↥g.ker := by
        intro y
        have hy : π (y : ↥FH) = 1 := by
          have := congrArg Subtype.val (MonoidHom.mem_ker.mp y.2)
          exact this
        have hyQ : ((y : ↥FH) : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).1 hy
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hyQ⟩
        exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
      have := h2.isNilpotent
      infer_instance
    have hFH : Group.IsSolvable ↥FH :=
      Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])
    exact Group.isSolvable_of_surjective
      (f := (FH.equivMapOfInjective _ H.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hFhn : (Fh.subgroupOf K).Normal := by
    refine ⟨fun y hy k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    obtain ⟨y', hy', hy'e⟩ := hy
    have hkH : (k : G) ∈ H := hKH k.2
    refine ⟨⟨k, hkH⟩ * y' * ⟨k, hkH⟩⁻¹, ⟨?_, ?_⟩, ?_⟩
    · show π (⟨k, hkH⟩ * y' * ⟨k, hkH⟩⁻¹) ∈ F'
      have hk' : π ⟨k, hkH⟩ ∈ modO2Image H K := ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
      obtain ⟨f, hf, hfe⟩ := hy'.1
      rw [map_mul, map_mul, map_inv, ← hfe]
      refine ⟨⟨π ⟨k, hkH⟩, hk'⟩ * f * ⟨π ⟨k, hkH⟩, hk'⟩⁻¹, hnorm.conj_mem f hf _, rfl⟩
    · show _ ∈ K.subgroupOf H
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact K.mul_mem (K.mul_mem k.2 (Subgroup.mem_subgroupOf.1 hy'.2)) (K.inv_mem k.2)
    · simp [← hy'e]
  have hFhR : Fh ≤ solvRad H :=
    (le_solvRad hFhK hFhn hFsol).trans (solvRad_le_solvRad_of_subnormal (subnormal_of_mem_cComp hK))
  obtain ⟨⟨hk, hkH⟩, hkK, hke⟩ := (x : ↥(modO2Image H K)).2
  have hhF : hk ∈ Fh := ⟨⟨hk, hkH⟩, ⟨⟨x, hx, hke.symm ▸ rfl⟩, hkK⟩, rfl⟩
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (⟨hk, hkH⟩ : ↥H)).ne'
  set h' : ↥H := (⟨hk, hkH⟩ : ↥H) ^ (2 ^ a) with hh'
  have hh'm : h' ^ m = 1 := by rw [hh', ← pow_mul, ← hn, pow_orderOf_eq_one]
  have hY := S.isTwoThreeGroup_oTwoRes_solvRad h139 h1334 h13 hS hH
  have hh'Y : (h' : G) ∈ oTwoRes (solvRad H) :=
    mem_oTwoRes_of_odd (by rw [hh', Subgroup.coe_pow]; exact (solvRad H).pow_mem (hFhR hhF) _) hm
      (by rw [← Subgroup.coe_pow, hh'm, Subgroup.coe_one])
  have hπx : π (⟨hk, hkH⟩ : ↥H) = ((x : X) : ↥H ⧸ CFSG.pCore 2 ↥H) := hke
  have hord : orderOf (π h') = p := by
    rw [hh', map_pow, hπx]
    have hxo' : orderOf ((x : X) : ↥H ⧸ CFSG.pCore 2 ↥H) = p := by
      rw [Subgroup.orderOf_coe, hxo]
    rw [Nat.Coprime.orderOf_pow, hxo']
    rw [hxo']
    exact Nat.Coprime.pow_right a ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
  have hdvd : p ∣ Nat.card ↥(oTwoRes (solvRad H)) := by
    have h1 : orderOf (π h') ∣ orderOf h' := orderOf_map_dvd π h'
    have h2 : orderOf (⟨(h' : G), hh'Y⟩ : ↥(oTwoRes (solvRad H))) ∣
        Nat.card ↥(oTwoRes (solvRad H)) := orderOf_dvd_natCard _
    have h3 : orderOf (⟨(h' : G), hh'Y⟩ : ↥(oTwoRes (solvRad H))) = orderOf h' := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    rw [← hord]
    exact h1.trans (h3 ▸ h2)
  rcases hY p hp hdvd with h | h <;> omega

end Setting4

end CFSG.Quasithin.H13.A6

