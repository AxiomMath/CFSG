module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

theorem ctl_eq_bot_of_yNormal
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (hY : Lem12225YNormal) {G : Type} [Group G]
    [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  have hY4 := hY G T L V H P U I h n p hH hNE hC hn3
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨hc1, -, hc2, -, -, -, -, -, -, -, -, -, -⟩ := hstar
  obtain ⟨hHs, -, hn, hVn, -, -, hp, hp2, hP, -, hhH, hhM, hI, -, hUd, hUi, hUe, hD, -,
    hidx, ⟨hcommV, htv⟩, hUO, -, -, hHU, hHI, hIP, -, hIM, -⟩ := hC
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  have hNVM : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    Lem20.normalizer_le_of_hyp1223 (stmt12_2_6_of h1222 h323) hH
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have : IsMulCommutative ↥V := hcommV
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact Subtype.ext (hVe.2 v v.2)
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU hhH
  have hPh : (P : Subgroup G) = Subgroup.zpowers h := hP
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hTI := h1216 G S L V hH hNE
  set A := CFSG.conjugate V h with hAdef
  have hVA : V ⊓ A = ⊥ := by
    rcases hTI h with h1 | h1
    · exfalso
      apply hhM
      refine hNVM (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
      rw [← BlueprintB2.mem_conjugate_iff, h1]
    · exact h1
  have hBase : I62.Base V A := ⟨hVe, isElemAbelian_conjugate' hVe h,
    conjugate_one V ▸ isTISetIn_conjugate hTI 1, isTISetIn_conjugate hTI h, hVA⟩
  have hUN : U ≤ Subgroup.normalizer (V : Set G) := hUT.trans hTV
  have htiU : ASInputs.tiU V A ≠ V := by
    intro htU
    have hVNA : V ≤ Subgroup.normalizer (A : Set G) := htU ▸ inf_le_right
    have hI2 : IsPGroup 2 I := by
      rw [hI]
      exact IsPGroup.to_sup_of_normal_right' (B2F.isPGroup_of_isElemAbelian hVe)
        (B2F.isPGroup_of_isElemAbelian (isElemAbelian_conjugate' hVe h)) hVNA
    obtain ⟨_, ⟨eD⟩⟩ := hD
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf I)
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at hcard
    obtain ⟨k, hk⟩ := hI2.exists_card_eq
    have hpd : p ∣ 2 ^ k := by
      rw [← hk, hcard]
      exact Dvd.dvd.mul_right (dvd_mul_left p 2) _
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd))
  have hCUV : U ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    rintro u ⟨hu, huV⟩
    have hUAC : U ⊓ A ≤ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun a ha => hUab a ha.1 b hb.1
    have hu' : u ∈ (U ⊓ V) ⊔ (U ⊓ A) := hUd ▸ hu
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_centralizer hUAC hu'
    have hbV : b ∈ Subgroup.centralizer (V : Set G) := by
      have ha' : a⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.mpr fun v hv => hVab v hv a ha.2)
      have := Subgroup.mul_mem _ ha' huV
      simpa using this
    by_cases hb1 : b = 1
    · rw [hb1, mul_one]
      exact ha.2
    · exfalso
      have hbB : b ∈ ASInputs.tiB V A := ⟨hb.2, hUN hb.1⟩
      have h1 := hBase.inf_centralizer_eq' hbB hb1
      apply htiU
      rw [← h1]
      refine le_antisymm inf_le_left fun v hv => ⟨hv, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hbV v hv)
  have hhI : h ∈ I := by rw [hIP]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hPh ▸
    Subgroup.mem_zpowers h))
  have hUI : U ≤ I := by rw [hIP]; exact le_sup_right.trans le_sup_left
  have hCIU : (S : Subgroup G) ⊓ Subgroup.centralizer (I : Set G) ≤
      Subgroup.centralizer (U : Set G) := inf_le_right.trans (Subgroup.centralizer_le hUI)
  have hgR : ∀ g ∈ Subgroup.normalizer (U : Set G), g ∈ I →
      ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G),
        g * x * g⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := by
    intro g hgU hgI x hx
    rw [hc1] at hx ⊢
    obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup_centralizer hCIU hx
    have hcg : g * c * g⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc.2 g hgI, mul_inv_cancel_right]
    rw [show g * (u * c) * g⁻¹ = (g * u * g⁻¹) * (g * c * g⁻¹) by group, hcg]
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp hgU u).mp hu) hc
  have hSR : (S : Subgroup G) ≤ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, B6.le_normalizer_centralizer hHU (hTH ht)⟩
  have hhR : h ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hgR h hhU hhI x, fun hx => ?_⟩
    have := hgR h⁻¹ (Subgroup.inv_mem _ hhU) (I.inv_mem hhI) _ hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
  have hIR : I ≤ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
    rw [hIP]
    exact sup_le (sup_le (hPh ▸ (Subgroup.zpowers_le).mpr hhR) (hUT.trans hSR))
      (hVT.trans hSR)
  have hA2 : ((U ⊓ V).subgroupOf V).index = 2 := hidx
  have hW3 : 3 ≤ Nat.card ↥((U ⊓ V).subgroupOf V) := by
    have h1 := Subgroup.card_mul_index ((U ⊓ V).subgroupOf V)
    rw [hA2, hVn] at h1
    rcases hn with rfl | rfl | rfl
    · exact absurd rfl hn3
    · rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at h1
      omega
    · rw [show (2 : ℕ) ^ 5 = 32 by norm_num] at h1
      omega
  have hgY : ∀ g, ∀ hg : g ∈ L, Odd (orderOf g) →
      (∀ x : ↥V, A4.actionOn V L hLV ⟨g, hg⟩ x * x⁻¹ ∈ (U ⊓ V).subgroupOf V) →
        g ∈ oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) := by
    intro g hg hodd hgW
    refine Subgroup.subset_closure ⟨⟨hg, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩, hodd⟩
    have hW : ∀ y (hy : y ∈ V), (g * y * g⁻¹ ∈ U ⊓ V ↔ y ∈ U ⊓ V) := fun y hy => by
      have h1 := (Subgroup.mul_mem_iff_of_index_two hA2).mp (hgW ⟨y, hy⟩)
      rw [inv_mem_iff] at h1
      exact h1
    constructor
    · intro hx
      exact (hW x hx.2).mpr hx
    · intro hx
      have hxV : x ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hg)) _).mp hx.2
        rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
      exact (hW x hxV).mp hx
  have hCUY : ∀ u ∈ U, u ∈ Subgroup.centralizer
      ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
        Set G) → u = 1 := by
    intro u hu huY
    by_contra hu1
    have hfix : ∀ d : ↥V, d ∈ (U ⊓ V).subgroupOf V → d ≠ 1 →
        (∀ g, ∀ hg : g ∈ L, Odd (orderOf g) →
          (∀ x : ↥V, A4.actionOn V L hLV ⟨g, hg⟩ x * x⁻¹ ∈ (U ⊓ V).subgroupOf V) →
            g * (d : G) * g⁻¹ = d) → False := fun d hd hd1 hall => by
      obtain ⟨g, hg, hodd, hgW, hgd⟩ := exists_odd_moves hLV hV2' htop hW3 hd hd1
      exact hgd (hall g hg hodd hgW)
    by_cases huV : u ∈ V
    · refine hfix ⟨u, huV⟩ (Subgroup.mem_subgroupOf.mpr ⟨hu, huV⟩)
        (fun h1 => hu1 (congrArg Subtype.val h1)) fun g hg hodd hgW => ?_
      have := Subgroup.mem_centralizer_iff.mp huY g (hgY g hg hodd hgW)
      show g * u * g⁻¹ = u
      rw [this, mul_inv_cancel_right]
    · have huCV : u ∉ Subgroup.centralizer (V : Set G) := fun h1 => huV (hCUV ⟨hu, h1⟩)
      obtain ⟨v₀, hv₀, hv₀u⟩ : ∃ v₀ ∈ V, u * v₀ * u⁻¹ * v₀⁻¹ ≠ 1 := by
        by_contra hno
        push Not at hno
        exact huCV (Subgroup.mem_centralizer_iff.mpr fun v hv => by
          have := hno v hv
          calc v * u = (u * v * u⁻¹ * v⁻¹)⁻¹ * u * v := by group
            _ = u * v := by rw [this, inv_one, one_mul])
      have hdU : u * v₀ * u⁻¹ * v₀⁻¹ ∈ U := by
        rw [show u * v₀ * u⁻¹ * v₀⁻¹ = u * (v₀ * u⁻¹ * v₀⁻¹) by group]
        exact U.mul_mem hu ((Subgroup.mem_normalizer_iff.mp (hHU (hTH (hVT hv₀))) _).mp
          (U.inv_mem hu))
      have hdV : u * v₀ * u⁻¹ * v₀⁻¹ ∈ V :=
        V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUN hu) v₀).mp hv₀) (V.inv_mem hv₀)
      refine hfix ⟨_, hdV⟩ (Subgroup.mem_subgroupOf.mpr ⟨hdU, hdV⟩)
        (fun h1 => hv₀u (congrArg Subtype.val h1)) fun g hg hodd hgW => ?_
      have hgu := Subgroup.mem_centralizer_iff.mp huY g (hgY g hg hodd hgW)
      have hw := hgW ⟨v₀, hv₀⟩
      set w := (A4.actionOn V L hLV ⟨g, hg⟩ ⟨v₀, hv₀⟩ * (⟨v₀, hv₀⟩ : ↥V)⁻¹ : ↥V) with hwdef
      have hwG : g * v₀ * g⁻¹ = (w : G) * v₀ := by
        rw [hwdef]
        simp [A4.actionOn_apply_coe]
      have hwu : (w : G) * u = u * w := hUab _ (Subgroup.mem_subgroupOf.mp hw).1 u hu
      have hgu' : g * u * g⁻¹ = u := by rw [hgu, mul_inv_cancel_right]
      show g * (u * v₀ * u⁻¹ * v₀⁻¹) * g⁻¹ = u * v₀ * u⁻¹ * v₀⁻¹
      calc g * (u * v₀ * u⁻¹ * v₀⁻¹) * g⁻¹ =
          (g * u * g⁻¹) * (g * v₀ * g⁻¹) * (g * u * g⁻¹)⁻¹ * (g * v₀ * g⁻¹)⁻¹ := by group
        _ = u * ((w : G) * v₀) * u⁻¹ * ((w : G) * v₀)⁻¹ := by rw [hgu', hwG]
        _ = (u * w) * v₀ * u⁻¹ * v₀⁻¹ * (w : G)⁻¹ := by group
        _ = (w * u) * v₀ * u⁻¹ * v₀⁻¹ * (w : G)⁻¹ := by rw [hwu]
        _ = w * (u * v₀ * u⁻¹ * v₀⁻¹) * (w : G)⁻¹ := by group
        _ = u * v₀ * u⁻¹ * v₀⁻¹ := by
          rw [hVab _ (Subgroup.mem_subgroupOf.mp hw).2 _ hdV, mul_inv_cancel_right]
  have hCLR : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) ≤
      (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := hc2 ▸ le_sup_right
  have hYL : oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) ≤ L :=
    (oTwoUpper_le _).trans inf_le_left
  have hCeq : (S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) =
      ((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer
        ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
          Set G) := by
    apply le_antisymm
    · exact fun c hc => ⟨hCLR hc, Subgroup.centralizer_le hYL hc.2⟩
    · rintro x ⟨hxR, hxY⟩
      rw [hc2] at hxR
      obtain ⟨u, hu, c, hc, rfl⟩ :=
        exists_mul_of_mem_sup_centralizer (hCLR.trans inf_le_right) hxR
      have hcY := Subgroup.centralizer_le hYL hc.2
      have huY : u ∈ Subgroup.centralizer
          ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) :
            Subgroup G) : Set G) := by
        have := Subgroup.mul_mem _ hxY (Subgroup.inv_mem _ hcY)
        simpa using this
      rw [hCUY u hu huY, one_mul]
      exact hc
  by_contra hne
  have hT₀2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G)) :=
    S.isPGroup'.to_le inf_le_left
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (⟨_, hne, hT₀2, rfl⟩ : IsTwoLocal
    (Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)))
  have hLN : L ≤ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hTN : (S : Subgroup G) ≤ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, B6.le_normalizer_centralizer hH.normalizes ht⟩
  have hIN : I ≤ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun x hx => by
      rw [hCeq]
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hIR hx, B6.le_normalizer_centralizer le_rfl (hY4 (hIR hx))⟩
  have heq := ((h331 G S hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal
    hH.quasisimple).1.2.2 M' hM' ((sup_le hLN hTN).trans hle)
  rw [hH.conjClosure_eq] at heq
  exact hIM (hIN.trans (hle.trans heq.le))

end Lem25

end CFSG.Quasithin.H13
