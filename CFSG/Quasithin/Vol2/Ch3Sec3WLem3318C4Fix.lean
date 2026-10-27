module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318C4Fix
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3323C4Fix
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4FixX

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.X3324
open scoped commutatorElement IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T M L D : Subgroup G} {n k : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)}
  {Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)}

theorem not_case4CorrW
    (hD : Data G T M L D n k α Φ) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h14 : Stmt3_3_14) (h15 : Step3_3_15R) (h20 : Stmt3_3_20) (hC34 : CFSG.Quasithin.C134L32CorrM)
    (hMS : IsMSPair (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T) T)
    (hcomp : liftCore α (flagStabilizer n (ZMod 2) {3}) ∈
      cComp (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T))
    {α₂ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})) →* ↥(StatedSL 3 (ZMod 2))}
    (hα₂ : IsModO2Surj (liftCore α (flagStabilizer n (ZMod 2) {3})) α₂)
    (h4 : CFSG.Quasithin.C134Case4Min
      (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T) T
      (liftCore α (flagStabilizer n (ZMod 2) {3}))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hD.hyp
  set Y := liftCore α (flagStabilizer n (ZMod 2) {3}) with hY
  set Z := quasithinOmegaOneCenter T with hZdef
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hD.le_normalizer_Y {3}
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hsylT : IsSylowTwoOf T (Y ⊔ T) := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right
  have hYL : Y ≤ L := liftCore_le α _
  obtain ⟨-, hML⟩ := h14 G T M L D h
  obtain ⟨-, -, hYQ, hTQ⟩ := C23.qData hTY
  set Q := c134Q (Y ⊔ T) Y with hQ
  have hQT : Q ≤ T :=
    MSY.c134Q_le_pCoreOf.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylT)
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) :=
    (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_right
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hZ₀L : Z ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine le_sup_left.trans (hD.sup_eq.le.trans (sup_le (sup_le ?_ ?_) ?_))
    · exact hD.le_centralizer.trans (Subgroup.centralizer_le inf_le_left)
    · rw [← Subgroup.le_centralizer_iff]
      exact inf_le_right
    · exact hTZ.trans (Subgroup.centralizer_le inf_le_left)
  have hYZ : ¬ Y ≤ Subgroup.centralizer (Z : Set G) := by
    intro hYZ
    have hZL : Z ≤ Subgroup.centralizer (L : Set G) :=
      fun z hz => hZ₀L ⟨hz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hYZ hy) z hz).symm⟩
    refine MS3323.false_of_le_center h h38 h39 hD.TL ?_
    rw [omegaOneCenterOf_eq]
    refine le_inf (hZT.trans le_sup_right) ?_
    rw [← Subgroup.le_centralizer_iff]
    exact sup_le (fun l hl => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZL hz) l hl).symm) hTZ
  have h4' := h4
  obtain ⟨c, hcCQ, hc1, hcZ⟩ :=
    CFSG.Quasithin.C134Case4Fix.exists_memW h4 hT2 le_sup_right hTY hQT
  have hcL : c ∈ Subgroup.centralizer (L : Set G) := hZ₀L ⟨hcZ, hcCQ.2⟩
  have hc2 : c ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hcZ
  have hNc : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ M := by
    refine h.toSetup331.normalizer_le h38 h39 (Subgroup.zpowers_ne_bot.mpr hc1) ?_ ?_
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hc2 hc1, pow_one]
    · refine sup_le (fun l hl => C45.mem_normalizer_zpowers ?_)
        (fun t ht => C45.mem_normalizer_zpowers ?_)
      · exact Subgroup.mem_centralizer_iff.mp hcL l hl
      · exact Subgroup.mem_centralizer_iff.mp (hZC hcZ) t ht
  have hCZM : Subgroup.centralizer (Z : Set G) ≤ M := fun x hx =>
    hNc (C45.mem_normalizer_zpowers (Subgroup.mem_centralizer_iff.mp hx c hcZ).symm)
  set U := ⁅centerOf Q, Y⁆ with hUdef
  obtain ⟨⟨nF, F, _, _, α', hFc, hα', -, -, hU, -, -⟩, -⟩ := h4
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα')
  obtain ⟨hYU, -, β, hβs, hβk, hβe⟩ := hU
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hβe' : ∀ (a : ↥Y) (u v : ↥U), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        ((α' a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u) i) :=
    fun a u v huv i => by simpa [moduleAct] using hβe a u v huv i
  have hTU : T ≤ Subgroup.normalizer (U : Set G) := fun t ht =>
    SBd5.mem_normalizer_commutator_of (C23.mem_normalizer_centerOf (hTQ ht)) (hTY ht)
  have hU8 : Nat.card ↥U = 8 := by
    rw [Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩), Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := F), hF]
    simp
  have hUZQ : U ≤ centerOf Q := Subgroup.le_normalizer_iff_commutator_le_left.mp fun y hy =>
    C23.mem_normalizer_centerOf (hYQ hy)
  have hUT : U ≤ T := hUZQ.trans (inf_le_left.trans hQT)
  have hW₃U : W₃ Φ ≤ U :=
    hD.W₃_le_commutator_self.trans (Subgroup.commutator_mono hD.W₃_le_centerOf le_rfl)
  have hk : k = 1 := by
    have h1 := Subgroup.card_le_of_le hW₃U
    rw [hD.card_W₃, hU8] at h1
    have hk1 := hD.k1
    by_contra hne
    have h2 : 8 ^ 2 ≤ 8 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hW₃eq : W₃ Φ = U :=
    Subgroup.eq_of_le_of_card_ge hW₃U (by rw [hD.card_W₃, hU8, hk, pow_one])
  have hZVU : ∀ u ∈ Z ⊓ ⁅vPlus L T, L⁆, u ∈ U := by
    rintro u ⟨huZ, huVL⟩
    obtain ⟨c', rfl⟩ := hD.exists_eq huVL
    have hcT : ∀ t ∈ T ⊓ L, t * (Φ c' : G) * t⁻¹ = (Φ c' : G) := fun t ht => by
      have := Subgroup.mem_centralizer_iff.mp (hZC huZ) t ht.1
      rw [this]
      group
    obtain ⟨x, hx⟩ := exists_ext3 (n := n) (k := k) (by have := hD.n4; omega)
      (c := c') (fun i a ha => hD.coord_eq_zero hcT i a (by omega))
    rw [← hW₃eq]
    refine ⟨x, ?_⟩
    show ((Φ (ext3 n k x)) : G) = (Φ c' : G)
    rw [hx]
  have hU1 : U ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hU8
    omega
  obtain ⟨⟨z₁, hz₁U, hz₁C⟩, hz₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (CFSG.Quasithin.C134Case4Fix.inf_centralizer_ne_bot hT2 hUT hTU hU1)
  have hz₁1' : z₁ ≠ 1 := fun e => hz₁1 (Subtype.ext e)
  set α₃ := Ctx3324.alpha3 hF α' with hα₃
  have hα₃s : Function.Surjective α₃ := Ctx3324.alpha3_surjective hF hα'.1
  have hα₃k : ∀ y : ↥Y, α₃ y = 1 → (y : G) ∈ pCoreOf 2 Y := Ctx3324.mem_of_alpha3 hF hα'
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
  have hβWe : ∀ (ℓ : ↥Y) (u v : ↥U), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (βW v) = L3.act (α₃ ℓ) (Multiplicative.toAdd (βW u)) :=
    fun ℓ u v huv => Ctx3324.z2_equiv hF β hβe ℓ u v huv 0
  have hz₁Z : z₁ ∈ Z := by
    have hz₁2 : z₁ ^ 2 = 1 := by
      have := eq_of_toAdd_beta βW (u := ⟨z₁, hz₁U⟩ * ⟨z₁, hz₁U⟩) (u' := 1)
        (by rw [toAdd_beta_mul, toAdd_beta_one, vec_add_self])
      rw [pow_two]
      exact congrArg Subtype.val this
    exact Subgroup.subset_closure ⟨⟨hUT hz₁U, hz₁C⟩, hz₁2⟩
  have hZU2 : Nat.card ↥(Z ⊓ U) ≤ 2 :=
    MSY.card_le_two hsylT hTY hF hα' β hβi hβe' inf_le_right (inf_le_left.trans hZC)
  have hZU : ∀ u ∈ Z ⊓ U, u = 1 ∨ u = z₁ := by
    intro u hu
    by_contra hcon
    push Not at hcon
    classical
    have : Fintype ↥(Z ⊓ U) := Fintype.ofFinite _
    have h3 : (({1, ⟨z₁, hz₁Z, hz₁U⟩, ⟨u, hu⟩} : Finset ↥(Z ⊓ U))).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro e
        exact hcon.2 (congrArg Subtype.val e).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun e => hz₁1' (congrArg Subtype.val e).symm, fun e => hcon.1
          (congrArg Subtype.val e).symm⟩
    have h4c := Finset.card_le_univ (({1, ⟨z₁, hz₁Z, hz₁U⟩, ⟨u, hu⟩} : Finset ↥(Z ⊓ U)))
    rw [h3, ← Nat.card_eq_fintype_card] at h4c
    omega
  have hZ : ∀ y (hy : y ∈ Y), L3.act (α₃ ⟨y, hy⟩) (Multiplicative.toAdd (βW ⟨z₁, hz₁U⟩)) =
      Multiplicative.toAdd (βW ⟨z₁, hz₁U⟩) → y ∈ Subgroup.centralizer (Z : Set G) := by
    intro y hy hfix
    refine Ctx3324.centZ h hD.TL (hYL hy) fun u hu => ?_
    rcases hZU u ⟨hu.1, hZVU u hu⟩ with rfl | rfl
    · group
    · have hyz : y * u * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hYU hy) u).mp hz₁U
      have h1 : (⟨_, hyz⟩ : ↥U) = ⟨u, hz₁U⟩ := βW.injective (Multiplicative.toAdd.injective (by
        rw [hβWe ⟨y, hy⟩ ⟨u, hz₁U⟩ ⟨_, hyz⟩ rfl]
        exact hfix))
      exact congrArg Subtype.val h1
  obtain ⟨X, hXX, hTX, hS3, hXTe, hXY, hXZ⟩ :=
    Case4Fix.exists_X hT2 hTidx hTY hYU hTU βW α₃ hα₃s hα₃k hβWe hz₁U hz₁Z hz₁1' hZ
  set H := Y ⊓ Subgroup.centralizer (Z : Set G) ⊔ T with hH
  set R := pCoreOf 2 H with hR
  have hTH : T ≤ H := le_sup_right
  have hHYT : H ≤ Y ⊔ T := sup_le_sup_right inf_le_left T
  have hsylH : IsSylowTwoOf T H := ⟨hTH, hsylT.2.1, fun h2 =>
    hsylT.2.2 (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T H (Y ⊔ T) hTH hHYT)))⟩
  have hRT : R ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylH
  have hqR : pCoreOf 2 (Y ⊔ T) ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylT).trans hTH) (fun x hx =>
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T) (hHYT hx))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hinner : ∀ t ∈ T, ∃ y ∈ Y, ∃ c ∈ qL Y T, t = y * c := fun t ht =>
    Mod3323.exists_eq_mul_of_natural hTY hT2 hα₂ hF hα' (by norm_num) hYU β hβs hβi hβe ht
      (hTU ht)
  have hset : ((Y ⊔ T : Subgroup G) : Set G) = (Y : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY
  have hset' : ((Y ⊔ T : Subgroup G) : Set G) = (Y : Set G) * (R : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hset] at hx
      obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨y', hy', c', hc', rfl⟩ := hinner t ht
      exact Set.mem_mul.mpr ⟨y * y', Y.mul_mem hy hy', c', hqR hc', by group⟩
    · rintro _ ⟨y, hy, r, hr, rfl⟩
      exact Subgroup.mul_mem_sup hy (hRT hr)
  have hr2 := CFSG.Quasithin.S1567.isRankTwoLie2Derived_of_modO2 _ hα₂.1 hα₂.2
  have hHZ : H ≤ Subgroup.centralizer (Z : Set G) := sup_le inf_le_right hTZ
  have hlt : H < Y ⊔ T := by
    refine lt_of_le_of_ne hHYT fun heq => hYZ fun y hy => hHZ ?_
    rw [heq]
    exact Subgroup.mem_sup_left hy
  have hodd : ¬ 2 ∣ H.relIndex (Y ⊔ T) := fun h2 =>
    hsylT.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left _ hTH))
  have hDR : ¬ D ≤ Subgroup.normalizer (R : Set G) := by
    by_cases hMS3 : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
        ¬ Y ⊔ T ≤ Subgroup.normalizer (C : Set G)
    · exfalso
      have hMSR : IsMSPair (Y ⊔ T) R :=
        ⟨⟨hMS.1.1, hMS.1.2.1, Y, hcomp, hset', hr2⟩, Or.inl ⟨H, hlt, hodd, rfl⟩, hMS3⟩
      obtain ⟨i, hi2⟩ := hC34 G (Y ⊔ T) R Y hMSR hcomp hset'
        ⟨ZMod 2, inferInstance, inferInstance, _, by simp, hα₂⟩
      have hRZ : R = pCoreOf 2 ((Y ⊔ T) ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set G)) := by
        rw [MS3323.inf_centralizer_eq hTY]
      match i, hi2 with
      | 0, hi2 => exact hi2.elim
      | 1, hi2 =>
        have h8 := C4Fix3323.card_Q_of_case1 (R := R) hα₂ hi2
        have h32 := C4Fix3323.card_Q_ge_of_case4CorrW hα₂ h4'
        omega
      | 2, hi2 => exact hi2.2 T hsylT hRT hRZ
      | 3, hi2 => exact hi2.2 T hsylT hRT hRZ
      | 4, hi2 => exact hi2.2 T hsylT hRT hRZ
      | 5, hi2 =>
        have hZc := (hi2.2 T hsylT hRT).1
        rw [omegaOneCenterOf_eq] at hZc
        exact hYZ fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz =>
          (Subgroup.mem_centralizer_iff.mp (hZc hz).2 y (Subgroup.mem_sup_left hy)).symm
      | n + 6, hi2 => exact hi2.elim
    · push Not at hMS3
      obtain ⟨C, hCR, hC1, hchar, hYTC⟩ := hMS3
      intro hDR
      have hDC := hDR.trans (Hyp331.normalizer_le_normalizer_of_characteristic hCR hchar)
      apply hD.false_of_pCoreOf_ne_bot h15
      have hC2 : IsPGroup 2 ↥C :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hCR
      have hCle : C ≤ pCoreOf 2 (Y ⊔ T ⊔ D) :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((hCR.trans (hRT.trans le_sup_right)).trans le_sup_left)
          (sup_le hYTC hDC) hC2
      intro hb
      rw [hb, le_bot_iff] at hCle
      exact hC1 hCle
  have hD' : ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) := by
    rw [hXTe]
    exact hDR
  obtain ⟨-, ⟨p, hp, hp24, hpsl⟩, -⟩ := h20 G T M L D X h hXX hTX hS3 hD'
  have hp2 : p ≠ 2 := by rintro rfl; omega
  set Yd := conjClosure X D with hYd
  have hXnot : ¬ X ≤ pCoreOf 2 (Yd ⊔ T) := by
    intro hXP
    have hYT : IsSylowTwoOf T (Yd ⊔ T) := ⟨le_sup_right, hT2, fun h2 =>
      hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
    have hXT2 : IsPGroup 2 ↥(X ⊔ T) :=
      hT2.to_le (sup_le (hXP.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hYT)) le_rfl)
    obtain ⟨eS⟩ := hS3
    obtain ⟨k', hk'⟩ := (IsPGroup.iff_card).mp (hXT2.to_quotient (CFSG.pCore 2 ↥(X ⊔ T)))
    rw [Nat.card_congr eS.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      at hk'
    have h3 : 3 ∣ 2 ^ k' := hk' ▸ (by decide : 3 ∣ Nat.factorial 3)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by decide)
  have hYdZ : Yd ≤ Subgroup.centralizer (Z : Set G) := conjClosure_le fun d hd x hx => by
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
  have hYTL : Yd ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    (sup_le (hYdZ.trans hCZM) h.TM).trans hML
  have hdvd := Case4Fix.prime_dvd_card_quot hp hp2 hpsl hYTL (hXY.trans hYL)
    ((le_conjClosure X D).trans le_sup_left) hXnot
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
      Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [← hD.ker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hD.surj).toEquiv]
  rw [hcard] at hdvd
  exact Case4Fix.not_dvd_card_sl (by have := hD.n4; omega) hD.n5 hp hp24 hdvd


end Data

end CFSG.Quasithin.H13.L3318
