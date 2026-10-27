module

public import CFSG.Quasithin.H13.A6S1525
public import CFSG.Quasithin.H13.A5S1521e
public import CFSG.Quasithin.H13.A6S1512

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def FactCentRows1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L → A5.Rows1321Final G L A →
      ∀ v : MulAut V, A5.Cond1321 G L v → rkIdx (fixV (Subgroup.zpowers v)) = 2 →
        ¬ 9 ∣ Nat.card ↥(L ⊓ Subgroup.centralizer {v})

theorem nine_dvd_card_of_central {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q} {a b : Q}
    (haY : a ∈ Y) (hbY : b ∈ Y) (haZ : a ∈ Subgroup.center Q) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hb3 : b ^ 3 = 1) (hba : b ∉ Subgroup.zpowers a) : 9 ∣ Nat.card Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : (Subgroup.zpowers a).Normal :=
    ⟨fun n hn g => by
      have hnZ : n ∈ Subgroup.center Q := Subgroup.zpowers_le.mpr haZ hn
      rw [Subgroup.mem_center_iff.mp hnZ g, mul_inv_cancel_right]
      exact hn⟩
  have hNY : Subgroup.zpowers a ≤ Y := Subgroup.zpowers_le.mpr haY
  set s : Subgroup ↥Y := (Subgroup.zpowers a).subgroupOf Y with hs
  have : s.Normal := Subgroup.normal_subgroupOf
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup s
  have hs3 : Nat.card s = 3 := by
    rw [hs, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime ha3 ha1]
  set β : ↥Y ⧸ s := QuotientGroup.mk ⟨b, hbY⟩ with hβ
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← QuotientGroup.mk_pow]
    have : (⟨b, hbY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, QuotientGroup.mk_one]
  have hβ1 : β ≠ 1 := by
    rw [hβ, Ne, QuotientGroup.eq_one_iff, hs, Subgroup.mem_subgroupOf]
    exact hba
  have h3 : 3 ∣ Nat.card (↥Y ⧸ s) := by
    rw [← orderOf_eq_prime hβ3 hβ1]
    exact orderOf_dvd_natCard β
  rw [hcard, hs3]
  exact Nat.mul_dvd_mul_right h3 3

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_L1_c012_hat (hhat : IsHatA6 L) :
    ∃ t : ↥(Subgroup.normalizer (V : Set G)), (t : G) ∈ S.L1 ∧ (t : G) ^ 3 = 1 ∧
      S.frame.ρ t ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hs, h4, h5, h3⟩, -⟩ := three_cycles
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_of_three hs h4 h5 h3
  obtain ⟨b, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ (2 ^ b), ?_, ?_, ?_⟩
  · simpa using S.L1.pow_mem hgL1 (2 ^ b)
  ·
    have hodd : ((g : G) ^ (2 ^ b)) ^ m = 1 := by
      have h : (g ^ (2 ^ b)) ^ m = 1 := by rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
      simpa using congrArg Subtype.val h
    have hc := S.cube_mem_pCoreOf_L1_hat hhat (S.L1.pow_mem hgL1 (2 ^ b))
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, hc⟩
    have hk' : (((g : G) ^ (2 ^ b)) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : (((g : G) ^ (2 ^ b)) ^ 3) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hodd, one_pow]
    have h2 : orderOf (((g : G) ^ (2 ^ b)) ^ 3) ∣ Nat.gcd (2 ^ k) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm')
    rw [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_left.mpr hm).pow_left k), Nat.dvd_one,
      orderOf_eq_one_iff] at h2
    simpa using h2
  ·
    rw [map_pow, hg]
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [orderOf_eq_prime h3 (by decide : (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) ≠ 1)] at h1
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
    omega

theorem nine_dvd_card_L1_hat (hhat : IsHatA6 L) :
    9 ∣ Nat.card S.L1 := by
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := exists_l0_c hhat.2.1
  have hcL1 : c ∈ S.L1 := S.l0_le_L1 hcl0
  have hcL : c ∈ L := S.L1_le_L hcL1
  have hcV : c ∈ Subgroup.centralizer (V : Set G) := S.o2Z_le_centralizer (oTwoRes_le _ hcl0)
  obtain ⟨t, htL1, ht3, htρ⟩ := S.exists_L1_c012_hat hhat
  have htL : (t : G) ∈ L := S.L1_le_L htL1
  set π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _ with hπ
  set Y : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := (S.L1.subgroupOf L).map π with hY
  have hmemY : ∀ x (hx : x ∈ S.L1), π ⟨x, S.L1_le_L hx⟩ ∈ Y := fun x hx =>
    ⟨⟨x, S.L1_le_L hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hπ1 : ∀ y : ↥L, π y = 1 ↔ (y : G) ∈ pCoreOf 2 L := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff]
  have h9 : 9 ∣ Nat.card Y := by
    refine nine_dvd_card_of_central (hmemY c hcL1) (hmemY _ htL1) ?_ ?_ ?_ ?_ ?_
    · exact S.mk_mem_center (y := ⟨c, hcL⟩) hcV
    · rw [← map_pow]
      have : (⟨c, hcL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
      rw [this, map_one]
    · rw [Ne, hπ1]
      exact hcO
    · rw [← map_pow]
      have : (⟨(t : G), htL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using ht3)
      rw [this, map_one]
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply htρ
      have h1 : π (⟨(t : G), htL⟩ * (⟨c, hcL⟩ ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
      rw [hπ1] at h1
      have h2 : (((⟨c, hcL⟩ : ↥L) ^ k : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) := by
        have : (((⟨c, hcL⟩ : ↥L) ^ k : ↥L) : G) = c ^ k := by simp
        rw [this]
        exact Subgroup.zpow_mem _ hcV k
      have h3 : (t : G) ∈ Subgroup.centralizer (V : Set G) := by
        have e : (t : G) = ((⟨(t : G), htL⟩ * (⟨c, hcL⟩ ^ k)⁻¹ : ↥L) : G) *
            (((⟨c, hcL⟩ : ↥L) ^ k : ↥L) : G) := by simp
        rw [e]
        exact Subgroup.mul_mem _ (S.pCoreOf_L_le_centralizer h1) h2
      exact (S.rho_eq_one_iff t).2 h3
  calc 9 ∣ Nat.card Y := h9
    _ ∣ Nat.card (S.L1.subgroupOf L) := Subgroup.card_map_dvd _ _
    _ = Nat.card S.L1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.L1_le_L).toEquiv

theorem nine_dvd_card_imQ_L1_hat (hhat : IsHatA6 L)
    {H : Subgroup G} (hL1H : S.L1 ≤ H) : 9 ∣ Nat.card (imQ H S.L1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup ↥H := S.L1.subgroupOf H with hX
  set g : ↥X →* A5.Hstar H := (A5.piQ H).comp X.subtype with hg
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  have h2 : Nat.card (↥X ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have h3 : g.range = imQ H S.L1 := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : IsPGroup 2 g.ker := by
    rintro ⟨x, hx⟩
    have hx1 : g x = 1 := MonoidHom.mem_ker.mp hx
    have hx2 : A5.piQ H (x : ↥H) = 1 := hx1
    have hxQ : ((x : ↥H) : G) ∈ pCoreOf 2 H := (A5.piQ_eq_one_iff _).mp hx2
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, hxQ⟩
    refine ⟨k, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  have h9 : 9 ∣ Nat.card X := by
    rw [hX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL1H).toEquiv]
    exact S.nine_dvd_card_L1_hat hhat
  rw [h1, h2, h3, hn] at h9
  exact (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_right h9

end Setting4

theorem input13521Four_of_cent
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h38 : A38ForSQTK)
    (hF : A5.Facts1321) (hR : A5.FactRankRows1321) (hA7 : A5.FactA7Grp1321)
    (hL3 : A5.FactL3Grp1321) (hO : A5.FactOutRows1321) (hC : FactCentRows1321) :
    Input13521Four := by
  intro G _ _ T L V S hNS hna hhat
  have hG1 := S.G1_mem_Hz_of_nonabelian hna
  have hVG1 : V ≤ S.G1 := (S.toA5Sit hNS h13315 h1356two hG1 hna).V_le_H
  obtain ⟨v, hv, hvQ⟩ : ∃ v ∈ V, v ∉ pCoreOf 2 S.G1 :=
    Set.not_subset.mp (S.toA5Sit hNS h13315 h1356two hG1 hna).not_V_le
  obtain ⟨K, hK, hKb⟩ := (S.toA5Sit hNS h13315 h1356two hG1 hna).exists_component
    VolI.stmtF956i (S.toA5SitY_L0 hNS h13315 h1356two hG1 hna hhat)
    (S.lemma13_5_19_two_l0 hhat hVG1) hv hvQ
  set P := (S.toA5Sit hNS h13315 h1356two hG1 hna).toHyp1321 VolI.stmtF956i hv hvQ K hK hKb
    with hP
  set QL := (S.toA5Sit hNS h13315 h1356two hG1 hna).toHypL1 VolI.stmtF956i h38 hv hvQ K hK hKb
    (fun _ hl => S.cube_mem_pCoreOf_L1_hat hhat hl) with hQL
  obtain ⟨-, hLK, U1, U2, h1, h2, -, -, -, -, hB4, hcond, hinj, -, -, hrk, A, hA⟩ :=
    A5.lemma_13_5_21_main P
      ((S.toA5Sit hNS h13315 h1356two hG1 hna).toHypY VolI.stmtF956i h38 hv hvQ K hK hKb
        (S.toA5SitY_L0 hNS h13315 h1356two hG1 hna hhat) (S.lemma13_5_19_two_l0 hhat hVG1))
      QL hF hR hA7 hL3 hO
  refine hC _ (A5.Hyp1321.chiefSec_sq P U1 U2) _ _ A hB4 hA _ hcond hrk ?_
  set ψ := A5.secAct P.ρ _ h1 h2 with hψ
  set f : ↥P.K →* MulAut (A5.ChiefSec U1 U2) :=
    ψ.comp (Subgroup.inclusion le_sup_left : ↥P.K →* ↥(P.K ⊔ Subgroup.zpowers P.b)) with hf
  have hle : (QL.L.subgroupOf P.K).map f ≤
      (P.K.subgroupOf (P.K ⊔ Subgroup.zpowers P.b)).map ψ ⊓
        Subgroup.centralizer {ψ ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩} := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨Subgroup.inclusion le_sup_left k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hkb : (Subgroup.inclusion le_sup_left k : ↥(P.K ⊔ Subgroup.zpowers P.b)) *
        ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩ =
        ⟨P.b, Subgroup.mem_sup_right (Subgroup.mem_zpowers P.b)⟩ *
          Subgroup.inclusion le_sup_left k :=
      Subtype.ext (QL.comm _ (Subgroup.mem_subgroupOf.mp hk))
    rw [hf, MonoidHom.comp_apply, ← map_mul, hkb, map_mul]
  have hcard : Nat.card ((QL.L.subgroupOf P.K).map f) = Nat.card QL.L := by
    rw [Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv
  have h9 : 9 ∣ Nat.card QL.L :=
    S.nine_dvd_card_imQ_L1_hat hhat (H := S.G1) (le_sup_left.trans hG1.1.1)
  rw [← hcard] at h9
  exact h9.trans (Subgroup.card_dvd_of_le hle)

end CFSG.Quasithin.H13.A6
