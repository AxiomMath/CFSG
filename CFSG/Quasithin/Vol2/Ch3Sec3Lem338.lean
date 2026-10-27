module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3310
public import CFSG.Quasithin.Vol2.Ch3Sec3Sec
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.H13.LinearOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative Pointwise commutatorElement

namespace Ch3Sec3

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem eq_one_of_two_of_commute {X K : Subgroup Ω}
    (hXK : X ≤ Subgroup.normalizer (K : Set Ω)) (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K)
    (hO : pCoreOf 2 X = ⊥) {x : Ω} (hx : x ∈ X) (hc : ∀ k ∈ K, k * x = x * k) {e : ℕ}
    (hxe : x ^ 2 ^ e = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := X ⊓ Subgroup.centralizer (K : Set Ω) with hC
  set Z := C ⊓ K with hZ
  have hCX : C ≤ X := inf_le_left
  have hXC : X ≤ Subgroup.normalizer (C : Set Ω) := fun y hy =>
    mem_normalizer_inf (Subgroup.le_normalizer hy)
      (B2F.normalizer_le_normalizer_centralizer K (hXK hy))
  have hxC : x ∈ C := ⟨hx, Subgroup.mem_centralizer_iff.mpr fun k hk => hc k hk⟩
  have hx2 : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨e, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxe, one_zpow]
  obtain ⟨S, hS, hxS⟩ := A4.exists_isSylowTwoOf_ge
    ((Subgroup.zpowers_le).mpr hxC) hx2
  have hZC : Z ≤ C := inf_le_left
  have hCZ : C ≤ Subgroup.normalizer (Z : Set Ω) := fun y hy =>
    mem_normalizer_inf (Subgroup.le_normalizer hy) (hXK (hCX hy))
  have h2C : ∀ c ∈ C, ∃ e : ℕ, c ^ 2 ^ e ∈ Z := fun c hc => by
    obtain ⟨e, he⟩ := h2 c (hCX hc)
    exact ⟨e, C.pow_mem hc _, he⟩
  have hCZS := le_sup_of_two_pow hZC hCZ h2C hS
  have hZS : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z := fun z hz s hs =>
    Subgroup.mem_centralizer_iff.mp (hS.1 hs).2 z hz.2
  have hSn : C ≤ Subgroup.normalizer (S : Set Ω) := by
    intro c hc
    have hc' : c ∈ (Z : Set Ω) * (S : Set Ω) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z S
        (le_normalizer_of_commute fun s hs z hz => (hZS z hz s hs).symm)]
      exact hCZS hc
    obtain ⟨z, hz, s, hs, rfl⟩ := hc'
    exact Subgroup.mul_mem _
      (le_normalizer_of_commute (fun s hs z hz => (hZS z hz s hs).symm) hz)
      (Subgroup.le_normalizer hs)
  have hSO : S ≤ pCoreOf 2 C := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hS.1 hSn hS.2.1
  have hOC : pCoreOf 2 C ≤ pCoreOf 2 X :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 C X hCX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hXC)
  have := (hSO.trans (hOC.trans hO.le)) (hxS (Subgroup.mem_zpowers x))
  exact Subgroup.mem_bot.mp this

omit [Finite Ω] in
theorem commutator_eq_self_of_isPerfect {Q : Subgroup Ω} (h : Group.IsPerfect ↥Q) :
    ⁅Q, Q⁆ = Q := by
  have h1 := Group.isPerfect_def.mp h
  rw [commutator_def] at h1
  calc ⁅Q, Q⁆ = (⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ : Subgroup ↥Q).map Q.subtype := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (⊤ : Subgroup ↥Q).map Q.subtype := by rw [h1]
    _ = Q := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_eq_of_two {X K A : Subgroup Ω}
    (hXK : X ≤ Subgroup.normalizer (K : Set Ω)) (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K)
    (hO : pCoreOf 2 X = ⊥) (hq : CFSG.IsQuasisimple ↥K) (hAX : A ≤ X) (hA : A ≠ ⊥)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) : ⁅K, A⁆ = K := by
  have hKA : ⁅K, A⁆ ≤ K := commutator_le_left_of_le_normalizer (hAX.trans hXK)
  have hn : (⁅K, A⁆.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).mpr
      (Subgroup.normalizer_commutator_ge_left K A)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      (B1Red.isQuasisimple_to_open hq) (⁅K, A⁆.subgroupOf K) with hc | ht
  · exfalso
    have hperf : ⁅K, K⁆ = K := commutator_eq_self_of_isPerfect hq.1
    have h1 : ⁅⁅K, A⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hyK : y ∈ K := hKA hy
      have hyc := Subgroup.mem_center_iff.mp (hc (Subgroup.mem_subgroupOf.mpr hy :
        (⟨y, hyK⟩ : ↥K) ∈ ⁅K, A⁆.subgroupOf K)) ⟨k, hk⟩
      exact congrArg Subtype.val hyc
    have h2' : ⁅⁅A, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm A K]; exact h1
    have h3 : ⁅⁅K, K⁆, A⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2'
    rw [hperf] at h3
    obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
    apply ha1
    refine Subtype.ext (eq_one_of_two_of_commute hXK h2 hO (hAX haA) (fun k hk => ?_)
      (e := 1) (by simpa using hA2 _ haA))
    have := Subgroup.commutator_mem_commutator hk haA
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · apply le_antisymm hKA
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ ⁅K, A⁆.subgroupOf K := ht ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end Ch3Sec3

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

namespace Hyp331

omit [Finite G] in
theorem mPlus_eq_of_le (hTL : T ≤ Subgroup.normalizer (L : Set G)) : mPlus L T = L :=
  le_antisymm (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl)
    (le_conjClosure L T)

theorem one_lt_of_lieModel {X : Type} [Group X] {n : ℕ} (hL : LieModel X .PSL 2 2 n) :
    1 < n := by
  rcases hL with ⟨-, ⟨-, hf, -, hne, -⟩, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rcases Nat.lt_or_ge 1 n with h1 | h1
    · exact h1
    · exfalso
      apply hne
      have : n = 1 := le_antisymm h1 hf
      rw [this, pow_one]
  all_goals exact absurd h0 (by norm_num)

theorem one_le_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    1 ≤ n := by
  have hK1 : 1 < Nat.card F := Finite.one_lt_card
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rw [hF, pow_zero] at hK1
    omega
  · exact h

theorem lemma_3_3_8_of_le
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h51 : AsB51) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      Case3_3_8_one T L ∨
      (∃ n : ℕ, 1 < n ∧ LieModel ↥(autOn (mPlus L T) (vPlus L T)) .PSL 2 2 n ∧
        BinaryNaturalSL (autOn (mPlus L T) (vPlus L T)) (tildeComm L T (mPlus L T))
          (cvPlus L T) 2 n) ∨
      ((Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 5)) ∧
          AlternatingNatural (autOn (mPlus L T) (vPlus L T)) (commVPlus L T (mPlus L T)) ⊥ 5) ∨
        (Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 7)) ∧
          AlternatingNatural (autOn (mPlus L T) (vPlus L T)) (commVPlus L T (mPlus L T)) ⊥ 7)) ∨
      Case3_3_8_four T L ∨
      (Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 7)) ∧
        Nat.card ↥⁅vPlus L T, mPlus L T⁆ = 2 ^ 4) ∨
      (Group.IsPerfect ↥(autOn (mPlus L T) (vPlus L T)) ∧
        Nat.card (Subgroup.center ↥(autOn (mPlus L T) (vPlus L T))) = 3 ∧
        Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ⧸
          Subgroup.center ↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 6)) ∧
        Nat.card ↥⁅vPlus L T, mPlus L T⁆ = 2 ^ 6) ∨
      (∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
        B51Part1 (ffJ (autOn (mPlus L T ⊔ T) (vPlus L T))) (autOn (mPlus L T) (vPlus L T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMp := mPlus_eq_of_le hTL
  obtain ⟨hVc, hFF⟩ := h.isFFModule h38 h39
  refine ⟨hVc, ?_⟩
  set V := vPlus L T with hVdef
  set Mp := mPlus L T with hMpdef
  have hred := vPlus_reduced h.toSetup331
  have hHV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  have hO2 : pCoreOf 2 (autOn (L ⊔ T) V) = ⊥ :=
    CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred.2.2
  have hMH : Mp ≤ L ⊔ T := by
    rw [hMpdef, ← conjClosure_sup_eq]
    exact le_sup_left
  have hHM : L ⊔ T ≤ Subgroup.normalizer (Mp : Set G) := sup_le_normalizer_conjClosure L T
  have hMV : Mp ≤ Subgroup.normalizer (V : Set G) := hMH.trans hHV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hred.2.1.2 v v.2)
  have hMpT : Mp ⊔ T = L ⊔ T := conjClosure_sup_eq L T
  rw [hMpT]
  obtain ⟨hKX, hXK, h2X, -⟩ := h.autOn_data
  set K := autOn Mp V with hKdef
  set X := autOn (L ⊔ T) V with hXdef
  have hOK : pCoreOf 2 K = ⊥ := le_bot_iff.mp (hO2 ▸
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K X hKX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK))
  have hKL : K = autOn L V := by rw [hKdef, hMp]
  have hLV' : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hHV
  have hq : CFSG.IsQuasisimple ↥K := by
    rw [hKL]
    rw [hKL] at hOK
    exact InternalSec.isQuasisimple_autOn hLV' h.Lq hOK (h.not_L_le_centralizer h38 h39)
  have hS : SQTKGroup ↥K := sqtkGroup_autOn
    (sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian h.toSetup331.pCoreOf_ne_bot)
    hMH hMV hq
  obtain ⟨A, hA⟩ := ((B1_4_5 hV2 X).out 1 2).1 hFF
  have hKA : ⁅K, A⁆ = K := Ch3Sec3.commutator_eq_of_two hXK h2X hO2 hq hA.1 hA.2.1
    fun a ha => hA.2.2.1.2 a ha
  have h2' : ∀ y ∈ L ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ Mp ⊔ Subgroup.centralizer (V : Set G) := by
    intro y hy
    rw [← hMpT] at hy
    obtain ⟨e, he⟩ := InternalSec.two_of_sup h.sylow.1 (le_normalizer_conjClosure_right L T) y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩
  obtain ⟨hB51, -⟩ := InternalSec.b51Hyp_ffJ_autOn hHV hMH hHM h2' hO2 hq hS hA hKA
  obtain ⟨hP1, hP2, -, -, -, -⟩ := h51 ↥V hV2 _ _ hB51
  have hcomm : commV K = commVPlus L T Mp := by
    apply Subgroup.map_injective V.subtype_injective
    rw [map_commV_autOn hMV, Subgroup.map_subgroupOf_eq_of_le
      (commutator_le_left_of_le_normalizer hMV)]
  have hfix : fixV K = cvPlus L T := fixV_autOn hMV
  have hCinv : ∀ k : ↥K, ∀ c ∈ fixV K, (k : MulAut ↥V) c ∈ fixV K := by
    intro k c hc
    rw [(mem_fixV.mp hc) k k.2]
    exact hc
  have htrans : ∀ {D : FFModel}, D.Realizes K (commV K) (fixV K ⊓ commV K) →
      D.Realizes K (tildeComm L T Mp) (cvPlus L T) := by
    intro D hD
    rw [inf_comm] at hD
    have := realizes_sup_of_inf hCinv hD
    rwa [hcomm, hfix] at this
  have hcard : Nat.card ↥⁅V, Mp⁆ = Nat.card ↥(commV K) := by
    have := Subgroup.card_map_of_injective (K := commV K) (f := V.subtype) V.subtype_injective
    rw [map_commV_autOn hMV] at this
    exact this
  have hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hperf : Group.IsPerfect ↥K := hq.1
  have t2 : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = 2 ^ n →
      (FFModel.nat (StatedSL 2 F)).Realizes K (commV K) (fixV K ⊓ commV K) →
      ∃ n : ℕ, 1 < n ∧ LieModel ↥K .PSL 2 2 n ∧
        BinaryNaturalSL K (tildeComm L T Mp) (cvPlus L T) 2 n := by
    intro F _ _ n hF hR
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (FFModel.nat_faithful _) hR
    have hL := lieModel_psl_two_of_mulEquiv hperf hF e
    exact ⟨n, one_lt_of_lieModel hL, hL, F, inferInstance, inferInstance, hF, htrans hR⟩
  have t4a : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = 2 ^ n →
      (FFModel.nat (StatedSL 3 F)).Realizes K (commV K) (fixV K ⊓ commV K) →
      Case3_3_8_four T L := by
    intro F _ _ n hF hR
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (FFModel.nat_faithful _) hR
    exact Or.inl ⟨n, F, inferInstance, inferInstance, hF, ⟨e⟩,
      Or.inl ⟨F, inferInstance, inferInstance, hF, htrans hR⟩⟩
  have t4b : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = 2 ^ n →
      (FFModel.nat (StatedSp 2 F)).Realizes K (commV K) (fixV K ⊓ commV K) →
      Case3_3_8_four T L := by
    intro F _ _ n hF hR
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (FFModel.nat_faithful _) hR
    have h1 : 1 < n := by
      rcases Nat.lt_or_ge 1 n with h1 | h1
      · exact h1
      · exfalso
        have hn1 : n = 1 := le_antisymm h1 (one_le_of_card hF)
        rw [hn1, pow_one] at hF
        exact not_isPerfect_statedSp_two hF (Group.IsPerfect.ofSurjective
          (f := e.toMonoidHom) e.surjective)
    exact Or.inr (Or.inl ⟨n, F, inferInstance, inferInstance, h1, hF, ⟨e⟩,
      F, inferInstance, inferInstance, hF, htrans hR⟩)
  have t4c : (FFModel.altDn 6).Realizes K (commV K) (fixV K ⊓ commV K) →
      Case3_3_8_four T L := by
    intro hR
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful_of_five_le (by norm_num)) hR
    exact Or.inr (Or.inr (Or.inl ⟨⟨e⟩, htrans hR⟩))
  have t4d : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = 2 ^ n →
      (FFModel.zornQ (quasithinG2 F)).Realizes K (commV K) (fixV K ⊓ commV K) →
      Case3_3_8_four T L := by
    intro F _ _ n hF hR
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (zornQ_faithful le_rfl) hR
    have hG : ⁅quasithinG2 F, quasithinG2 F⁆ = quasithinG2 F :=
      Ch3Sec3.commutator_eq_self_of_isPerfect (Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom) e.surjective)
    refine Or.inr (Or.inr (Or.inr ⟨n, F, inferInstance, inferInstance, hF,
      ⟨e.trans (MulEquiv.subgroupCongr hG.symm)⟩, F, inferInstance, inferInstance, hF, ?_⟩))
    rw [hG]
    exact htrans hR
  have t4d' : ∀ {F : Type} [Field F] [Finite F], Nat.card F = 2 ^ 1 →
      (FFModel.zornQ ⁅quasithinG2 F, quasithinG2 F⁆).Realizes K (commV K) (fixV K ⊓ commV K) →
      Case3_3_8_four T L := by
    intro F _ _ hF hR
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (zornQ_faithful (commutator_self_le _)) hR
    exact Or.inr (Or.inr (Or.inr ⟨1, F, inferInstance, inferInstance, hF, ⟨e⟩,
      F, inferInstance, inferInstance, hF, htrans hR⟩))
  have t7 : ∀ n : ℕ, (n = 4 ∨ n = 5) → Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
        B51Part1 (ffJ X) K := fun n hn he => ⟨n, hn, he, hP1⟩
  have t7nat : ∀ n : ℕ, (n = 4 ∨ n = 5) → ∀ {U Z : Subgroup ↥V} {F : Type} [Field F] [Finite F],
      Nat.card F = 2 ^ 1 → (FFModel.nat (StatedSL n F)).Realizes K U Z →
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    intro n hn U Z F _ _ hF hR
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (FFModel.nat_faithful _) hR
    rw [pow_one] at hF
    exact ⟨e.trans (statedSLEquivZModTwo hF)⟩
  have t7ext : ∀ n : ℕ, 3 ≤ n → ∀ {U Z : Subgroup ↥V},
      (FFModel.extSq (ZMod 2) n).Realizes K U Z →
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    intro n hn U Z hR
    obtain ⟨π, hπ⟩ := hR
    have hinj := injective_of_statedSL_zmodTwo (K := ZMod 2) (by simp) hn hπ.1
    exact ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm.trans
      (statedSLEquivZModTwo (by simp))⟩
  have t7inj : ∀ n : ℕ, ∀ {U : Subgroup ↥V} {π : ↥(StatedSL n (ZMod 2)) →* ↥K},
      (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia K U ⊥ π →
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    intro n U π hπ
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    exact ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm.trans (statedSLEquivZModTwo (by simp))⟩
  by_cases hZ : fixV K ⊓ commV K = ⊥
  ·
    obtain ⟨-, hcases⟩ := hP1
    rcases hcases with ⟨-, hpair, -⟩ | hii | ⟨n, hiii⟩ | hiv
    ·
      rcases hpair with ⟨n, F, _, _, hF, hR⟩ | ⟨n, F, _, _, hF, hR⟩ | ⟨n, F, _, _, hF, hR⟩ |
        ⟨n, F, _, _, hF, hR⟩ | ⟨F, _, _, hF, hR⟩ | hR | hR | hR | ⟨α, hR⟩ | hR |
        ⟨F, _, _, hF, hR⟩ | ⟨F, _, _, hF, hR⟩ | hR | hR
      · exact Or.inr (Or.inl (t2 hF hR))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (t4a hF hR))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (t4b hF hR))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (t4d hF hR))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (t4d' hF hR))))
      · rw [hZ] at hR
        obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful_of_five_le le_rfl) hR
        refine Or.inr (Or.inr (Or.inl (Or.inl ⟨⟨e⟩, ?_⟩)))
        rw [← hcomm]
        exact hR
      · exact Or.inr (Or.inr (Or.inr (Or.inl (t4c hR))))
      · rw [hZ] at hR
        obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful_of_five_le (by norm_num)) hR
        refine Or.inr (Or.inr (Or.inl (Or.inr ⟨⟨e⟩, ?_⟩)))
        rw [← hcomm]
        exact hR
      · rw [hZ] at hR
        obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (a7Four_faithful α) hR
        obtain ⟨π, hπ⟩ := hR
        have hc := G64.RealizesVia.card_eq hπ
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨e⟩, ?_⟩))))
        rw [hcard, hc, Subgroup.card_bot, mul_one]
        show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
          (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 2 ^ 4
        rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
          Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
          Nat.card_fin]
      · obtain ⟨F, _, _, Γ₀, hF4, -, hhat, -, hR'⟩ := hR
        rw [hZ] at hR'
        obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (FFModel.nat_faithful Γ₀) hR'
        obtain ⟨hp, hz, hq'⟩ := isHat_parts_of_mulEquiv e hhat
        obtain ⟨π, hπ⟩ := hR'
        have hc := card_eq_of_realizesVia_nat hπ
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hz, hq', ?_⟩)))))
        rw [hcard, hc, Subgroup.card_bot, mul_one, Nat.card_fun, hF4, Nat.card_fin]
        norm_num
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (t7 4 (Or.inl rfl) (t7nat 4 (Or.inl rfl) hF hR)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (t7 5 (Or.inr rfl) (t7nat 5 (Or.inr rfl) hF hR)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (t7 4 (Or.inl rfl) (t7ext 4 (by norm_num) hR)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (t7 5 (Or.inr rfl) (t7ext 5 (by norm_num) hR)))))))
    ·
      obtain ⟨-, n, F, _, _, hF, I, π, hind, hsup, hreal, -, -⟩ := hii
      have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) (hreal 0)
      have hDS : DirectSumOfCopies K (commV K) ⊥ (FFModel.nat (StatedSL 3 F)) 2 :=
        ⟨I, π, fun _ => bot_le, fun i => by rw [bot_sup_eq]; exact (hind i).eq_bot,
          by rw [bot_sup_eq, hsup], hreal⟩
      have hDS' := directSumOfCopies_sup hCinv (by rw [inf_comm]; exact hZ) hDS
      rw [hcomm, hfix] at hDS'
      exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨n, F, inferInstance, inferInstance, hF,
        ⟨(MulEquiv.ofBijective π ⟨hinj, (hreal 0).1⟩).symm⟩, Or.inr hDS'⟩))))
    ·
      obtain ⟨-, hn, π, U₁, U₂, -, hR₁, -⟩ := hiii
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (t7 n hn (t7inj n hR₁)))))))
    ·
      obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (t7 n hn (t7inj n (hreal ⟨0, hk1⟩))))))))
  ·
    have hnd : ¬ IsIntDirect (commV K) (fixV K) ⊤ := hP2.1.mpr (Or.inl hZ)
    obtain ⟨-, hlist⟩ := hP2.2 hnd
    rcases hlist with ⟨n, F, _, _, hF, hR⟩ | ⟨n, F, _, _, hF, hR⟩ | ⟨n, F, _, _, hF, hR⟩ | hR |
      hR | ⟨F, _, _, hF, hR⟩ | ⟨F, _, _, hF, hR⟩
    · exact Or.inr (Or.inl (t2 hF hR))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (t4b hF hR))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (t4d hF hR))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (t4c hR))))
    · obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful_of_five_le (by norm_num)) hR
      obtain ⟨e'⟩ := nonempty_mulEquiv_alternating_eight_sl_four
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (t7 4 (Or.inl rfl) ⟨e.trans e'⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (t4d' hF hR))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (t4a hF hR))))

end Hyp331

theorem stmt3_3_8_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51)
    (h8one : Stmt3_3_8One) : Stmt3_3_8 := by
  intro G _ _ T M L D h
  by_cases hTL : T ≤ Subgroup.normalizer (L : Set G)
  · exact h.lemma_3_3_8_of_le h38 h39 h51 hTL
  · obtain ⟨hc, h1⟩ := h8one G T M L D h hTL
    exact ⟨hc, Or.inl h1⟩

end CFSG.Quasithin.H13
