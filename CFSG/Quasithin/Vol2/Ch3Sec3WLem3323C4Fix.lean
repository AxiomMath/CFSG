module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C4Fix
public import CFSG.Quasithin.Vol2.Ch3Sec3WCase4Fix3323P
public import CFSG.Quasithin.Background.C134Case4FixM
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4FixCore
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C23
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324Ctx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace C4Fix3323

variable {G : Type} [Group G]

theorem card_Q_ge_of_case4CorrW [Finite G] {T R L : Subgroup G}
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (h4 : CFSG.Quasithin.C134Case4Min (L ⊔ T) R L) :
    8 < Nat.card ↥(c134Q (L ⊔ T) L) := by
  obtain ⟨⟨n, F, _, _, α, hFc, hα, hZQ, hCU, hU, -, hCne⟩, -⟩ := h4
  set Q := c134Q (L ⊔ T) L with hQ
  set C := c134CQ (L ⊔ T) L with hC
  set U := ⁅centerOf Q, L⁆ with hUdef
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα)
  obtain ⟨-, -, β, hβs, hβk, -⟩ := hU
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hU8 : Nat.card ↥U = 8 := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have hCZ : C ≤ centerOf Q := hZQ ▸ le_sup_left
  have hUZ : U ≤ centerOf Q := hZQ ▸ le_sup_right
  have hCN : C ≤ Subgroup.normalizer (U : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (hCZ ha).2 b (hUZ hb).1))
  have hprod := C45.card_sup_mul_card_inf hCN
  rw [hCU, Subgroup.card_bot, mul_one, hU8] at hprod
  have hC2 : 1 < Nat.card ↥C := (Subgroup.one_lt_card_iff_ne_bot C).mpr hCne
  have hle : Nat.card ↥(C ⊔ U) ≤ Nat.card ↥Q :=
    Subgroup.card_le_of_le ((sup_le hCZ hUZ).trans inf_le_left)
  omega

variable [Finite G] {T M L D : Subgroup G}

theorem not_isC134Case4CorrW
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14)
    (h20 : Stmt3_3_20) (hC34 : CFSG.Quasithin.C134L32CorrM)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂) :
    ¬ CFSG.Quasithin.C134Case4Min (L ⊔ T) T L := by
  intro hi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi0 := hi
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hsylT : IsSylowTwoOf T (L ⊔ T) := h.toSetup331.isSylowTwoOf
  obtain ⟨hQO, -, hLQ, hTQ⟩ := C23.qData hTL
  set Q := c134Q (L ⊔ T) L with hQ
  set Z := quasithinOmegaOneCenter T with hZdef
  have hOq : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQq : Q ≤ qL L T := hQO.trans hOq
  have hqT : qL L T ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylT
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) :=
    (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_right
  obtain ⟨c, hcCQ, hc1, hcZ⟩ :=
    CFSG.Quasithin.C134Case4Fix.exists_memW hi hT2 le_sup_right hTL (hQq.trans hqT)
  have hc2 : c ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hcZ
  have hNc : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ M := by
    refine h.toSetup331.normalizer_le h38 h39 (Subgroup.zpowers_ne_bot.mpr hc1) ?_ ?_
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hc2 hc1, pow_one]
    · refine sup_le (fun l hl => C45.mem_normalizer_zpowers ?_)
        (fun t ht => C45.mem_normalizer_zpowers ?_)
      · exact Subgroup.mem_centralizer_iff.mp hcCQ.2 l hl
      · exact Subgroup.mem_centralizer_iff.mp (hZC hcZ) t ht
  have hCZM : Subgroup.centralizer (Z : Set G) ≤ M := fun x hx =>
    hNc (C45.mem_normalizer_zpowers (Subgroup.mem_centralizer_iff.mp hx c hcZ).symm)
  set U := ⁅centerOf Q, L⁆ with hUdef
  obtain ⟨⟨n, F, _, _, α, hFc, hα, -, -, hU, -, -⟩, -⟩ := hi
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα)
  obtain ⟨hLU, -, β, hβs, hβk, hβe⟩ := hU
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hTU : T ≤ Subgroup.normalizer (U : Set G) := fun t ht =>
    SBd5.mem_normalizer_commutator_of (C23.mem_normalizer_centerOf (hTQ ht)) (hTL ht)
  have hinner : ∀ t ∈ T, ∃ l ∈ L, ∃ c ∈ qL L T, t = l * c := fun t ht =>
    Mod3323.exists_eq_mul_of_natural hTL hT2 hα₂ hF hα (by norm_num) hLU β hβs hβi hβe ht (hTU ht)
  set H := L ⊓ Subgroup.centralizer (Z : Set G) ⊔ T with hH
  set R := pCoreOf 2 H with hR
  have hTH : T ≤ H := le_sup_right
  have hHLT : H ≤ L ⊔ T := sup_le_sup_right inf_le_left T
  have hsylH : IsSylowTwoOf T H := ⟨hTH, hsylT.2.1, fun h2 =>
    hsylT.2.2 (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T H (L ⊔ T) hTH hHLT)))⟩
  have hRT : R ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylH
  have hqR : qL L T ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hqT.trans hTH) (fun x hx =>
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (hHLT hx))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hset : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T hTL
  have hset' : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (R : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hset] at hx
      obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨l', hl', c', hc', rfl⟩ := hinner t ht
      exact Set.mem_mul.mpr ⟨l * l', L.mul_mem hl hl', c', hqR hc', by group⟩
    · rintro _ ⟨l, hl, r, hr, rfl⟩
      exact Subgroup.mul_mem_sup hl (hRT hr)
  have hr2 := CFSG.Quasithin.S1567.isRankTwoLie2Derived_of_modO2 α₂ hα₂.1 hα₂.2
  have hcomp := h.toSetup331.mem_cComp
  have hMST : IsMSPair (L ⊔ T) T := h.isMSPair h38 h39 hr2 hTL
  have hDR : ¬ D ≤ Subgroup.normalizer (R : Set G) := by
    by_cases hMS3 : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
        ¬ L ⊔ T ≤ Subgroup.normalizer (C : Set G)
    · exfalso
      have hMSR : IsMSPair (L ⊔ T) R :=
        ⟨⟨hMST.1.1, hMST.1.2.1, L, hcomp, hset', hr2⟩,
          Or.inl ⟨H, MS3323.lt_sup h h38 h39 hTL, MS3323.not_two_dvd_relIndex h, rfl⟩, hMS3⟩
      obtain ⟨i, hi2⟩ := hC34 G (L ⊔ T) R L hMSR hcomp hset'
        ⟨ZMod 2, inferInstance, inferInstance, α₂, by simp, hα₂⟩
      have hRZ : R = pCoreOf 2 ((L ⊔ T) ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set G)) := by
        rw [MS3323.inf_centralizer_eq hTL]
      match i, hi2 with
      | 0, hi2 => exact hi2.elim
      | 1, hi2 =>
        have h8 := card_Q_of_case1 (R := R) hα₂ hi2
        have h32 := card_Q_ge_of_case4CorrW hα₂ hi0
        omega
      | 2, hi2 => exact hi2.2 T hsylT hRT hRZ
      | 3, hi2 => exact hi2.2 T hsylT hRT hRZ
      | 4, hi2 => exact hi2.2 T hsylT hRT hRZ
      | 5, hi2 => exact MS3323.false_of_le_center h h38 h39 hTL (hi2.2 T hsylT hRT).1
      | n + 6, hi2 => exact hi2.elim
    · push Not at hMS3
      obtain ⟨C, hCR, hC1, hchar, hLTC⟩ := hMS3
      intro hDR
      have hCLT : C ≤ L ⊔ T := hCR.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hHLT)
      exact h.not_le_normalizer h38 h39 hC1 hCLT hLTC
        (hDR.trans (Hyp331.normalizer_le_normalizer_of_characteristic hCR hchar))
  obtain ⟨z₀, ⟨hz₀Z, hz₀VL⟩, hz₀1⟩ := Ctx3324.exists_z₀ h h38 h39 hTL
  have hVL := Ctx3324.vL_le h
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) :=
    (le_conjClosure L T).trans (le_normalizer_conjClosure _ _)
  have hVab : ∀ x ∈ vPlus L T, ∀ y ∈ vPlus L T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Hyp331.vPlus_reduced h.toSetup331).2.1.1.is_comm.comm
      (⟨x, hx⟩ : ↥(vPlus L T)) ⟨y, hy⟩)
  have hVLZQ : ⁅vPlus L T, L⁆ ≤ centerOf Q := fun x hx =>
    ⟨(hVL hx).1, Subgroup.centralizer_le hQq (hVL hx).2⟩
  have hVLU : ⁅vPlus L T, L⁆ ≤ U := by
    rw [← SBd5.commutator_commutator_eq_self h.Lmax.1.2.1.2.1 hLV hVab]
    exact Subgroup.commutator_mono hVLZQ le_rfl
  have hz₀U : z₀ ∈ U := hVLU hz₀VL
  set α₃ := Ctx3324.alpha3 hF α with hα₃
  have hα₃s : Function.Surjective α₃ := Ctx3324.alpha3_surjective hF hα.1
  have hα₃k : ∀ ℓ : ↥L, α₃ ℓ = 1 → (ℓ : G) ∈ pCoreOf 2 L := Ctx3324.mem_of_alpha3 hF hα
  set γW : ↥U →* Multiplicative L3.Vec :=
    (Sec3323.coord (F := ZMod 2) (0 : Fin 1)).comp ((Ctx3324.z2Coords hF 1).comp β) with hγW
  have hγWi : Function.Injective γW := by
    intro u u' huu
    have h0 : Multiplicative.toAdd ((Ctx3324.z2Coords hF 1).comp β u) 0 =
        Multiplicative.toAdd ((Ctx3324.z2Coords hF 1).comp β u') 0 :=
      congrArg Multiplicative.toAdd huu
    have h1 : (Ctx3324.z2Coords hF 1).comp β u = (Ctx3324.z2Coords hF 1).comp β u' :=
      Multiplicative.toAdd.injective (funext fun i => by fin_cases i; exact h0)
    exact hβi (Ctx3324.z2Coords_injective hF 1 h1)
  have hγWs : Function.Surjective γW := by
    intro y
    obtain ⟨x, hx⟩ := Ctx3324.z2Coords_surjective hF 1
      (Multiplicative.ofAdd fun _ => Multiplicative.toAdd y)
    obtain ⟨u, rfl⟩ := hβs x
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (Ctx3324.z2Coords hF 1 (β u)) 0 = Multiplicative.toAdd y
    rw [hx]
    rfl
  set βW : ↥U ≃* Multiplicative L3.Vec := MulEquiv.ofBijective γW ⟨hγWi, hγWs⟩ with hβW
  have hβWe : ∀ (ℓ : ↥L) (u v : ↥U), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (βW v) = L3.act (α₃ ℓ) (Multiplicative.toAdd (βW u)) :=
    fun ℓ u v huv => Ctx3324.z2_equiv hF β hβe ℓ u v huv 0
  have hLVL : L ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun ℓ hℓ =>
    Main3324.mem_normalizer_comm (hLV hℓ) (Subgroup.le_normalizer hℓ)
  have hUVL : U ≤ ⁅vPlus L T, L⁆ :=
    Ctx3324.le_of_conj_z₀ βW α₃ hLU hα₃s hβWe hz₀U hz₀1 hz₀VL hLVL
  have hqU : qL L T ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUVL.trans fun x hx => (hVL hx).2)
  have hUZQ : U ≤ centerOf Q := Subgroup.le_normalizer_iff_commutator_le_left.mp fun l hl =>
    C23.mem_normalizer_centerOf (hLQ hl)
  have hUq : U ≤ qL L T := hUZQ.trans (inf_le_left.trans hQq)
  have hcz : ∀ {u : G}, u ∈ Z → ∀ t ∈ T, t * u * t⁻¹ = u := fun hu t ht => by
    have := Subgroup.mem_centralizer_iff.mp (hZC hu) t ht
    rw [this]
    group
  set I := (T.subgroupOf L).map α₃ with hI
  have hI2 : IsPGroup 2 I := (hT2.comap_of_injective L.subtype L.subtype_injective).map α₃
  have hIodd : ¬ 2 ∣ I.index := by
    have h1 := Subgroup.index_map_dvd (T.subgroupOf L) hα₃s
    have h2 : T.relIndex L ∣ T.index :=
      (C45.relIndex_eq hTL) ▸ Subgroup.relIndex_dvd_index_of_le le_sup_right
    exact fun h3 => hTidx ((h3.trans h1).trans h2)
  obtain ⟨e, he⟩ := Mod3323.exists_fix hI2 hIodd
  have hfixI : ∀ {u : ↥U}, (u : G) ∈ Z →
      Multiplicative.toAdd (βW u) = 0 ∨ Multiplicative.toAdd (βW u) = e := by
    intro u hu
    apply he
    rintro _ ⟨t, ht, rfl⟩
    exact (hβWe t u u (hcz hu _ ht).symm).symm
  have hz₀e : Multiplicative.toAdd (βW ⟨z₀, hz₀U⟩) = e := by
    rcases hfixI (u := ⟨z₀, hz₀U⟩) hz₀Z with h0 | h1
    · exfalso
      apply hz₀1
      have h2 : βW ⟨z₀, hz₀U⟩ = βW 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h0
      exact congrArg Subtype.val (βW.injective h2)
    · exact h1
  have hZ : ∀ y (hy : y ∈ L), L3.act (α₃ ⟨y, hy⟩) (Multiplicative.toAdd (βW ⟨z₀, hz₀U⟩)) =
      Multiplicative.toAdd (βW ⟨z₀, hz₀U⟩) → y ∈ Subgroup.centralizer (Z : Set G) := by
    intro y hy hfix
    have hfe : L3.act (α₃ ⟨y, hy⟩) e = e := by
      rw [← hz₀e]
      exact hfix
    refine Ctx3324.centZ h hTL hy fun u hu => ?_
    have huU : u ∈ U := hVLU hu.2
    have hyu : y * u * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hLU hy) u).mp huU
    have h1 : (⟨_, hyu⟩ : ↥U) = ⟨u, huU⟩ := βW.injective (Multiplicative.toAdd.injective (by
      rw [hβWe ⟨y, hy⟩ ⟨u, huU⟩ ⟨_, hyu⟩ rfl]
      rcases hfixI (u := ⟨u, huU⟩) hu.1 with h0 | h1
      · rw [h0, L3.act_zero]
      · rw [h1, hfe]))
    exact congrArg Subtype.val h1
  obtain ⟨-, X, hXX, hTX, hS3, hXTe, hXL, hXZ, -⟩ :=
    Ctx3324.xStructU h hTL hLU hTU hUq hqU βW α₃ hα₃s hα₃k hβWe hz₀U hz₀Z hz₀1 hZ
  have hD' : ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) := by
    rw [hXTe]
    exact hDR
  obtain ⟨-, ⟨p, hp, hp24, hpsl⟩, -⟩ := h20 G T M L D X h hXX hTX hS3 hD'
  have hp2 : p ≠ 2 := by rintro rfl; omega
  set Y := conjClosure X D with hY
  have hXnot : ¬ X ≤ pCoreOf 2 (Y ⊔ T) := by
    intro hXP
    have hYT : IsSylowTwoOf T (Y ⊔ T) := ⟨le_sup_right, hT2, fun h2 =>
      hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
    have hXT2 : IsPGroup 2 ↥(X ⊔ T) :=
      hT2.to_le (sup_le (hXP.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hYT)) le_rfl)
    obtain ⟨eS⟩ := hS3
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hXT2.to_quotient (CFSG.pCore 2 ↥(X ⊔ T)))
    rw [Nat.card_congr eS.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by decide : 3 ∣ Nat.factorial 3)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by decide)
  have hYZ : Y ≤ Subgroup.centralizer (Z : Set G) := conjClosure_le fun d hd x hx => by
    have hdZ : d ∈ Subgroup.normalizer (Z : Set G) :=
      Hyp331.normalizer_le_normalizer_of_characteristic hZT
        (CFSG.QuasithinUnique.L246C127.characteristic_omegaOneCenter T) (h.DN hd)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : d⁻¹ * z * d⁻¹⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdZ) z).mp hz
    have hxz := Subgroup.mem_centralizer_iff.mp (hXZ hx) _ hz'
    calc z * (d * x * d⁻¹) = d * ((d⁻¹ * z * d⁻¹⁻¹) * x) * d⁻¹ := by group
      _ = d * (x * (d⁻¹ * z * d⁻¹⁻¹)) * d⁻¹ := by rw [hxz]
      _ = d * x * d⁻¹ * z := by group
  have hYTL : Y ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    (sup_le (hYZ.trans hCZM) h.TM).trans hML
  have hdvd := Case4Fix.prime_dvd_card_quot hp hp2 hpsl hYTL hXL
    ((le_conjClosure X D).trans le_sup_left) hXnot
  have h168 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    rw [← hα₂.2, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α₂ hα₂.1).toEquiv,
      ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
        (ZMod 2)).toEquiv]
  rw [h168] at hdvd
  exact Case4Fix.not_dvd_card_sl (by norm_num) (by norm_num) hp hp24 hdvd

theorem notCase4Corr3323_holdsW
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14) (h20 : Stmt3_3_20)
    (hC34 : CFSG.Quasithin.C134L32CorrM) : Ch3Sec3.NotCase4Corr3323W :=
  fun _ _ _ _ _ _ _ h hTL _ hα₂ => not_isC134Case4CorrW h h38 h39 h14 h20 hC34 hTL hα₂


end C4Fix3323

end CFSG.Quasithin.H13
