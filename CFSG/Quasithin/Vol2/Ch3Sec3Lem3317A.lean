module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.Alternating.Multipliers.Small
public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316B
public import CFSG.Quasithin.H13.A7Nat1233Mod
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316A

public section

namespace CFSG.Quasithin.H13.L3317

open CFSG.RankThree.PerfectCover
open CFSG.Open (pCoreOf)

theorem card_ker_dvd_hopfMultiplier {S E : Type} [Group S] [Group E] [Finite S] [Finite E]
    [Group.IsPerfect E] (q : E →* S) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) : Nat.card q.ker ∣ Nat.card (hopfMultiplier S) := by
  have hS : Group.IsPerfect S := Group.IsPerfect.ofSurjective hq
  have := finite_hopfMultiplier hS
  rw [← map_hopfMultiplier_hopfLift q hq hker]
  exact Subgroup.card_map_dvd (H := hopfMultiplier S) (hopfLift q hq hker)

theorem injective_of_odd_of_hopf {S E : Type} [Group S] [Group E] [Finite S] [Finite E]
    [Group.IsPerfect E] (h2 : Nat.card (hopfMultiplier S) = 2) (q : E →* S)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card q.ker)) : Function.Injective q := by
  have hd := card_ker_dvd_hopfMultiplier q hq hker
  rw [h2] at hd
  have h1 : Nat.card q.ker = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem card_hopfMultiplier_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') :
    Nat.card (hopfMultiplier S) = Nat.card (hopfMultiplier S') := by
  rw [← Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv,
    ← Nat.card_congr (hopfMultiplierEquivGriess S').toEquiv,
    Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv]

theorem card_hopfMultiplier_alt5 :
    Nat.card (hopfMultiplier (alternatingGroup (Fin 5))) = 2 :=
  (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2

theorem card_hopfMultiplier_psl32 :
    Nat.card (hopfMultiplier (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 1))) =
      2 := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_three_two_hopfMultiplier
  rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]


section Kernel

variable {G : Type} [Group G] [Finite G]

theorem ker_eq_pCore_of_hopf {L V Y : Subgroup G} (hYL : Y ≤ L) (hY : ⁅Y, Y⁆ = Y)
    (hcen : ∀ x ∈ L, x ∈ Subgroup.centralizer (V : Set G) → ∀ y ∈ L,
      x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (h2 : Nat.card (hopfMultiplier S) = 2) (f : ↥Y →* S) (hf : Function.Surjective f)
    (hfk : ∀ y : ↥Y, f y = 1 ↔ (y : G) ∈ Subgroup.centralizer (V : Set G)) :
    f.ker = CFSG.pCore 2 ↥Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 ↥Y with hPdef
  have hPk : P ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    have hN : (P.map f).Normal := CFSG.pCore_normal.map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map f) with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 (P.map f) := CFSG.pCore_isPGroup.map f
      rw [h] at hp
      have hS2 : IsPGroup 2 S := hp.of_equiv Subgroup.topEquiv
      have : Group.IsNilpotent S := hS2.isNilpotent
      exact CFSG.Quasithin.H13.InspA312.false_of_isSolvable_of_simple hnc inferInstance
  have hYp : Group.IsPerfect ↥Y := (Subgroup.isPerfect_iff).2 hY
  set q : (↥Y ⧸ P) →* S := QuotientGroup.lift P f hPk with hq
  have hqs : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective _ _ hf hPk
  have hcomm : ∀ x y : ↥Y, f x = 1 → x * y * x⁻¹ * y⁻¹ ∈ P := by
    intro x y hx
    have hxV := (hfk x).1 hx
    have hc := hcen x (hYL x.2) hxV y (hYL y.2)
    have hYN : Y ≤ Subgroup.normalizer (pCoreOf 2 L ⊓ Y : Set G) := by
      intro k hk
      exact CFSG.Quasithin.A4.mem_normalizer_inf
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hYL hk)) (Subgroup.le_normalizer hk)
    have hcY : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 Y :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hYN
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left)
        ⟨hc, Y.mul_mem (Y.mul_mem (Y.mul_mem x.2 y.2) (Y.inv_mem x.2)) (Y.inv_mem y.2)⟩
    rw [CFSG.Quasithin.H13.A7.pCoreOf_eq_map_cfsgPCore] at hcY
    obtain ⟨w, hw, hweq⟩ := hcY
    have hw' : w = x * y * x⁻¹ * y⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hweq)
    rw [hw'] at hw
    exact hw
  have hker : q.ker ≤ Subgroup.center (↥Y ⧸ P) := by
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    have hx1 : f x = 1 := ha
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have h1 : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : ↥Y ⧸ P) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcomm x y hx1)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    calc (QuotientGroup.mk y : ↥Y ⧸ P) * QuotientGroup.mk x
        = ((QuotientGroup.mk x * QuotientGroup.mk y * (QuotientGroup.mk x)⁻¹ *
            (QuotientGroup.mk y)⁻¹)⁻¹ * (QuotientGroup.mk x * QuotientGroup.mk y)) := by group
      _ = QuotientGroup.mk x * QuotientGroup.mk y := by rw [h1, inv_one, one_mul]
  have hodd : Odd (Nat.card q.ker) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2d
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := q.ker) 2 h2d
    have ha' : orderOf (a : ↥Y ⧸ P) = 2 := by rwa [Subgroup.orderOf_coe]
    have hZ : Subgroup.zpowers (a : ↥Y ⧸ P) ≤ Subgroup.center (↥Y ⧸ P) :=
      (Subgroup.zpowers_le).2 (hker a.2)
    have hle : Subgroup.zpowers (a : ↥Y ⧸ P) ≤ CFSG.pCore 2 (↥Y ⧸ P) :=
      le_sSup ⟨Subgroup.normal_of_le_center hZ,
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha', pow_one])⟩
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
    have h1 : (a : ↥Y ⧸ P) = 1 := by
      have := hle (Subgroup.mem_zpowers (a : ↥Y ⧸ P))
      rwa [Subgroup.mem_bot] at this
    rw [h1, orderOf_one] at ha'
    exact absurd ha' (by decide)
  have hinj := injective_of_odd_of_hopf h2 q hqs hker hodd
  refine le_antisymm (fun x hx => ?_) hPk
  have h1 : q (QuotientGroup.mk x) = q 1 := by
    rw [map_one]
    exact hx
  exact (QuotientGroup.eq_one_iff x).1 (hinj h1)

end Kernel


section Action

variable {G : Type} [Group G]

@[expose] noncomputable def actL (L V : Subgroup G) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥L →* ↥(autOn L V) :=
  (CFSG.Quasithin.A4.actionOn V L hLV).codRestrict (autOn L V) fun l =>
    (CFSG.Quasithin.A4.mem_autOn_iff hLV).2 ⟨l, rfl⟩

theorem actL_surjective {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (actL L V hLV) := by
  rintro ⟨a, ha⟩
  obtain ⟨l, rfl⟩ := (CFSG.Quasithin.A4.mem_autOn_iff hLV).1 ha
  exact ⟨l, rfl⟩

theorem actL_eq_one_iff {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (l : ↥L) : actL L V hLV l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← CFSG.Quasithin.A4.actionOn_eq_one_iff hLV l]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem actL_ker {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    (actL L V hLV).ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
  ext l
  rw [MonoidHom.mem_ker, actL_eq_one_iff, Subgroup.mem_subgroupOf]

@[expose] noncomputable def actA7 {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (e : ↥(autOn L V) ≃* alternatingGroup (Fin 7)) : ↥L →* alternatingGroup (Fin 7) :=
  e.toMonoidHom.comp (actL L V hLV)

theorem actA7_surjective {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (e : ↥(autOn L V) ≃* alternatingGroup (Fin 7)) : Function.Surjective (actA7 hLV e) :=
  e.surjective.comp (actL_surjective hLV)

theorem actA7_ker {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (e : ↥(autOn L V) ≃* alternatingGroup (Fin 7)) :
    (actA7 hLV e).ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
  rw [← actL_ker hLV]
  ext l
  simp only [actA7, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, MulEquiv.map_eq_one_iff]

end Action


section Cases

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem le_normalizer_vPlus (h : Hyp331 G T M L D) :
    L ≤ Subgroup.normalizer (vPlus L T : Set G) :=
  le_sup_left.trans (Hyp331.vPlus_reduced h.toSetup331).2.2.2.1

theorem alt7_cases (h8 : Stmt3_3_8) (h10 : Stmt3_3_10) (h14 : Stmt3_3_14)
    (h : Hyp331 G T M L D) (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      AlternatingNatural (autOn L (vPlus L T)) (commVPlus L T L) ⊥ 7 ∨
        Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 4 := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hc7 : Nat.card ↥(autOn L (vPlus L T)) = 2520 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H.A7.card_A7]
  obtain ⟨hab, hc⟩ := h8 G T M L D h
  refine ⟨hab, ?_⟩
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    obtain ⟨t, ht, htN, -⟩ := h1
    exact absurd (hTL ht) htN
  ·
    obtain ⟨n, -, hn, -⟩ := h2
    exact absurd hn ((h10 G T M L D h).2.1 n)
  ·
    rcases h3 with ⟨⟨e5⟩, -⟩ | ⟨-, hnat⟩
    · rw [hML] at e5
      have := Nat.card_congr e5.toEquiv
      rw [hc7, card_alt_five] at this
      norm_num at this
    · rw [hML] at hnat
      exact Or.inl hnat
  ·
    exfalso
    rcases h4 with ⟨n, K, _, _, hK, ⟨eK⟩, -⟩ | ⟨n, K, _, _, hn, hK, ⟨eK⟩, -⟩ | ⟨⟨e6⟩, -⟩ |
      ⟨n, K, _, _, hK, ⟨eK⟩, -⟩
    · rw [hML] at eK
      have hcK := Nat.card_congr eK.toEquiv
      rw [hc7, L3316.card_sl3 hK] at hcK
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          norm_num at h1
        · norm_num at hcK
      · have := L3316.sl3_ge hn
        omega
    · rw [hML] at eK
      have hcK := Nat.card_congr eK.toEquiv
      rw [hc7, L3316.card_sp4 hK] at hcK
      have := L3316.sp4_ge hn
      omega
    · rw [hML] at e6
      have := Nat.card_congr e6.toEquiv
      rw [hc7, card_alt_six] at this
      norm_num at this
    · rw [hML] at eK
      have hcK := Nat.card_congr eK.toEquiv
      rw [hc7] at hcK
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          norm_num at h1
        · have hd : Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ ∣ Nat.card ↥(quasithinG2 K) :=
            Subgroup.card_dvd_of_le (Subgroup.commutator_le.2 fun a ha b hb => by
              rw [commutatorElement_def]
              exact (quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
                ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb))
          rw [← hcK, L3316.card_g2 le_rfl hK] at hd
          norm_num at hd
      · rw [Obs3324.commutator_quasithinG2_eq hn hK, L3316.card_g2 (by omega) hK] at hcK
        have := L3316.g2_ge hn
        omega
  ·
    obtain ⟨-, hc4⟩ := h5
    rw [hML] at hc4
    exact Or.inr hc4
  ·
    exfalso
    obtain ⟨-, hZ, -⟩ := h6
    rw [hML] at hZ
    have : IsSimpleGroup ↥(autOn L (vPlus L T)) := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(autOn L (vPlus L T)))
      with hb | ht
    · rw [hb, Subgroup.card_bot] at hZ
      norm_num at hZ
    · apply CFSG.Quasithin.H.A7.not_comm_A7
      intro σ τ
      have hσ := (Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top (e.symm σ)) (e.symm τ))
      apply e.symm.injective
      rw [map_mul, map_mul, hσ]
  ·
    exfalso
    obtain ⟨n, hn, ⟨eS⟩, -⟩ := h7
    rw [hML] at eS
    have hcS := Nat.card_congr eS.toEquiv
    rw [hc7] at hcS
    rcases hn with rfl | rfl
    · rw [CFSG.QuasithinUnique.Bridge.card_sl4] at hcS
      norm_num at hcS
    · rw [CFSG.QuasithinUnique.Bridge.card_sl5] at hcS
      norm_num at hcS

theorem mem_lFamilyOf_of_hopf (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) {Y : Subgroup G} (hYL : Y ≤ L)
    (hY : ⁅Y, Y⁆ = Y) (hTY : T ≤ Subgroup.normalizer (Y : Set G)) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (h2 : Nat.card (hopfMultiplier S) = 2) (f : ↥Y →* S) (hf : Function.Surjective f)
    (hfk : ∀ y : ↥Y, f y = 1 ↔ (y : G) ∈ Subgroup.centralizer (vPlus L T : Set G)) :
    Y ∈ lFamilyOf L T ∧ Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* S) := by
  have hLV := le_normalizer_vPlus h
  have hcen : ∀ x ∈ L, x ∈ Subgroup.centralizer (vPlus L T : Set G) → ∀ y ∈ L,
      x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L := fun x hx hxV y hy =>
    CFSG.Quasithin.H13.A7.commutator_mem_pCoreOf_of_ker h.Lq (actA7_surjective hLV e)
      (actA7_ker hLV e) hx hxV hy
  have hk := ker_eq_pCore_of_hopf hYL hY hcen hnc h2 f hf hfk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨L3316.mem_lFamilyOf_of_hom h.sylow h.toSetup331.pCoreOf_ne_bot hYL hY hTY f hf
    (hk ▸ CFSG.pCore_isPGroup), ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

end Cases

section CommV

variable {G : Type} [Group G]

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

@[expose] noncomputable def autOnEquiv {L V W : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hC : L ⊓ Subgroup.centralizer (W : Set G) = L ⊓ Subgroup.centralizer (V : Set G)) :
    ↥(autOn L W) ≃* ↥(autOn L V) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (actL_surjective hLW)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (by
      rw [actL_ker, actL_ker]
      ext l
      simp only [Subgroup.mem_subgroupOf]
      constructor
      · intro hl
        exact ((Subgroup.ext_iff.1 hC (l : G)).1 ⟨l.2, hl⟩).2
      · intro hl
        exact ((Subgroup.ext_iff.1 hC (l : G)).2 ⟨l.2, hl⟩).2)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (actL_surjective hLV)))

theorem autOnEquiv_actL {L V W : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hC : L ⊓ Subgroup.centralizer (W : Set G) = L ⊓ Subgroup.centralizer (V : Set G))
    (l : ↥L) : autOnEquiv hLV hLW hC (actL L W hLW l) = actL L V hLV l := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ (actL_surjective hLW)).symm
      (actL L W hLW l) = (QuotientGroup.mk l : ↥L ⧸ (actL L W hLW).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [autOnEquiv, MulEquiv.trans_apply, h1]
  rfl

variable [Finite G] {T M L D : Subgroup G}

theorem commV_le_vPlus (h : Hyp331 G T M L D) : ⁅vPlus L T, L⁆ ≤ vPlus L T :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 (le_normalizer_vPlus h)

theorem le_normalizer_commV (h : Hyp331 G T M L D) :
    L ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun _ hl =>
  mem_normalizer_commutator (le_normalizer_vPlus h hl) (Subgroup.le_normalizer hl)

omit [Finite G] in
theorem T_le_normalizer_commV (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun _ ht =>
  mem_normalizer_commutator (Hyp331.le_normalizer_vPlus L T ht) (hTL ht)

theorem inf_centralizer_commV (h : Hyp331 G T M L D) (hML : mPlus L T = L) :
    L ⊓ Subgroup.centralizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer (vPlus L T : Set G) := by
  refine le_antisymm (fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, ?_⟩)
    (inf_le_inf_left _ (Subgroup.centralizer_le (commV_le_vPlus h)))
  replace hx := Subgroup.mem_inf.1 hx
  have hdec := h.vPlus_decomp.2
  rw [hML] at hdec
  have hle : vPlus L T ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hdec]
    refine sup_le (fun w hw => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx.2) w hw
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.1 hz.2) x hx.1).symm
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hv)

end CommV

end CFSG.Quasithin.H13.L3317
