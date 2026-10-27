module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Bar
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Lift
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42E49
public import CFSG.Quasithin.H13.NQBlockCommonResidual

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem center_eq_bot_of_simple_perfect {Q : Type*} [Group Q] [IsSimpleGroup Q]
    [hp : Group.IsPerfect Q] : Subgroup.center Q = ⊥ := by
  refine center_eq_bot_of_isSimpleGroup ?_
  by_contra hc
  push Not at hc
  have htop : commutator Q = ⊤ := Group.IsPerfect.commutator_eq_top
  have hbot : commutator Q = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hc y x
  obtain ⟨a, b, hab⟩ := exists_pair_ne Q
  apply hab
  have ha : a ∈ (⊥ : Subgroup Q) := by rw [← hbot, htop]; exact Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup Q) := by rw [← hbot, htop]; exact Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_pCore_bar {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh) {b : G}
    (hbX : b ∈ X) (hbK : ∀ x ∈ K, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 K)
    (x : ↥(modO2Image X K)) :
    ∃ y ∈ CFSG.pCore 2 ↥(modO2Image X K),
      (y : O2Q X) = QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hbX⟩ * x *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hbX⟩)⁻¹ * (x : O2Q X)⁻¹ := by
  obtain ⟨k, rfl⟩ := barMap_surjective l.le_X x
  have hkK : ((k : G)) ∈ K := k.2
  have hmem := hbK k hkK
  have hmemK : b * k * b⁻¹ * (k : G)⁻¹ ∈ K := by
    obtain ⟨w, -, hw⟩ := hmem
    rw [← hw]
    exact w.2
  refine ⟨barMap l.le_X ⟨b * k * b⁻¹ * (k : G)⁻¹, hmemK⟩,
    NQBlock.map_pCore_le_of_surjective _ (barMap_surjective l.le_X) ⟨⟨_, hmemK⟩, ?_, rfl⟩, ?_⟩
  · obtain ⟨w, hw, hwv⟩ := hmem
    have hw' : w = ⟨b * k * b⁻¹ * (k : G)⁻¹, hmemK⟩ := Subtype.ext hwv
    rw [← hw'] at *
    exact hw
  · show QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b * k * b⁻¹ * (k : G)⁻¹, _⟩ = _
    rw [show (⟨b * k * b⁻¹ * (k : G)⁻¹, l.le_X hmemK⟩ : ↥X) =
      ⟨b, hbX⟩ * ⟨k, l.le_X k.2⟩ * ⟨b, hbX⟩⁻¹ * ⟨k, l.le_X k.2⟩⁻¹ from rfl]
    simp only [map_mul, map_inv]
    rfl

theorem three_le_pRank_of_seven
    {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
    (hXN : X ≤ Subgroup.normalizer (Kh : Set G)) (hD4 : Is3D4 2 1 ↥(modO2Image X Kh))
    (hL8 : LieModel (O2Q K) .PSL 2 2 3) {b : G} (hbX : b ∈ X) (hb1 : b ≠ 1) (hb7 : b ^ 7 = 1)
    (hbN : b ∈ Subgroup.normalizer (K : Set G))
    (hbK : ∀ x ∈ K, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 K) : 3 ≤ CFSG.Open.pRank 7 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (O2Q K) := isSimpleGroup_of_lieModel_PSL2 hL8
  obtain ⟨hSperf, hUS, hKbY, -, hKSne, hUKS, hne⟩ := bar_facts l hsimple
  set Y := modO2Image X Kh with hY
  set Kb := modO2Image X K with hKb
  have : IsSimpleGroup ↥Y := isSimpleGroup_of_perfect hD4
  have hZ := center_eq_bot hD4
  set mb : O2Q X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hbX⟩ with hmb
  have hmbY : mb ∈ Subgroup.normalizer (Y : Set (O2Q X)) := o2Map_mem_normalizer (hXN hbX)
  have hmbK : mb ∈ Subgroup.normalizer (Kb : Set (O2Q X)) := o2Map_mem_normalizer hbN
  have hmb7 : mb ^ 7 = 1 := by
    rw [hmb, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (by
      rw [show (⟨b, hbX⟩ : ↥X) ^ 7 = 1 from Subtype.ext hb7]
      exact one_mem _)
  set α := Y.normalizerMonoidHom ⟨mb, hmbY⟩ with hα
  have hαapp : ∀ y : ↥Y, ((α y : ↥Y) : O2Q X) = mb * y * mb⁻¹ := fun y => rfl
  have hα7 : α ^ 7 = 1 := by
    rw [hα, ← map_pow, show (⟨mb, hmbY⟩ : ↥(Subgroup.normalizer (Y : Set (O2Q X)))) ^ 7 = 1 from
      Subtype.ext hmb7, map_one]
  obtain ⟨c, hc⟩ := exists_conj_of_pow_seven hD4 α hα7
  have hcapp : ∀ y : ↥Y, ((c * y * c⁻¹ : ↥Y) : O2Q X) = mb * y * mb⁻¹ := fun y => by
    rw [← hαapp, hc]
    rfl
  have hc7 : c ^ 7 = 1 := by
    have h1 : c ^ 7 ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 : MulAut.conj (c ^ 7) y = y := by rw [map_pow, ← hc, hα7]; rfl
      rw [MulAut.conj_apply] at h2
      calc y * c ^ 7 = c ^ 7 * y * (c ^ 7)⁻¹ * c ^ 7 := by rw [h2]
        _ = c ^ 7 * y := by group
    rwa [hZ, Subgroup.mem_bot] at h1
  set KS := Kb.subgroupOf Y with hKS
  have hcN : c ∈ Subgroup.normalizer (KS : Set ↥Y) := by
    refine mem_normalizer_of_conj_mem' fun x hx => ?_
    show ((c * x * c⁻¹ : ↥Y) : O2Q X) ∈ Kb
    rw [hcapp]
    exact (Subgroup.mem_normalizer_iff.mp hmbK _).mp hx
  have hKSt : KS ≠ ⊤ := fun h => hne (by rw [h, top_sup_eq])
  have h7 : 7 ∣ Nat.card ↥KS := by
    obtain ⟨eB⟩ := l.bar_equiv
    have h1 := (card_of_lieModel_PSL2 hL8).1
    rw [Nat.card_congr eB.toEquiv] at h1
    have h2 : Nat.card (ModO2 Kb) ∣ Nat.card ↥KS := by
      rw [hKS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKbY).toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    rw [h1] at h2
    exact (by norm_num : 7 ∣ 2 ^ 3 * (4 ^ 3 - 1)).trans h2
  have hcKS : c ∈ KS := mem_of_mem_normalizer hD4 hUS hUKS hKSne hKSt h7 hc7 hcN
  have hc1 : c = 1 := by
    obtain ⟨eB⟩ := l.bar_equiv
    have : IsSimpleGroup (ModO2 Kb) := eB.symm.isSimpleGroup
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr l.perfect
    have : Group.IsPerfect ↥Kb := Group.IsPerfect.ofSurjective (barMap_surjective l.le_X)
    have : Group.IsPerfect (ModO2 Kb) := Group.IsPerfect.ofSurjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Kb))
    have hcK : (⟨(c : O2Q X), hcKS⟩ : ↥Kb) = 1 := by
      refine eq_one_of_commutator_mem center_eq_bot_of_simple_perfect ?_ fun x => ?_
      · exact Subtype.ext (by simpa using congrArg Subtype.val hc7)
      · obtain ⟨y, hy, hyv⟩ := commutator_mem_pCore_bar l hbX hbK x
        convert hy using 1
        apply Subtype.ext
        rw [hyv]
        have h1 := hcapp ⟨x, hKbY x.2⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
        rw [h1]
    exact Subtype.ext (by simpa using congrArg Subtype.val hcK)
  have hmbc : ∀ y ∈ Y, mb * y = y * mb := by
    intro y hy
    have h1 := hcapp ⟨y, hy⟩
    rw [hc1, one_mul, inv_one, mul_one] at h1
    calc mb * y = mb * y * mb⁻¹ * mb := by group
      _ = y * mb := by rw [← h1]
  have hmbY' : mb ∉ Y := by
    intro hmem
    have h1 : (⟨mb, hmem⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hmbc y y.2).symm
    rw [hZ, Subgroup.mem_bot] at h1
    have h2 : mb = 1 := congrArg Subtype.val h1
    rw [hmb, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, h2⟩
    have h3 : b ^ 2 ^ m = 1 := by
      simpa using congrArg (fun z : ↥(CFSG.pCore 2 ↥X) => ((z : ↥X) : G)) hm
    have h4 : orderOf b ∣ Nat.gcd (2 ^ m) 7 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hb7)
    rw [Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 7)] at h4
    exact hb1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4))
  obtain ⟨E, hE, hE49⟩ := exists_elemAbelian_49 hD4
  obtain ⟨hF, hF3⟩ := elemAbelian_sup_zpowers (Y := Y) (E := E.map Y.subtype)
    (fun _ ⟨y, _, hy⟩ => hy ▸ y.2) (CFSG.SectionRank.isElemAbelian_map hE _)
    (by rw [Subgroup.card_map_of_injective Y.subtype_injective, hE49]) hmb7 hmbY' hmbc
  exact three_le_pRank_of_quotient hF hF3

end CFSG.Quasithin.H13.D42
