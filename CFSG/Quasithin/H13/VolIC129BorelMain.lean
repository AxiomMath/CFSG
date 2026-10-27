module

public import CFSG.Quasithin.H13.VolIC129Borel
public import CFSG.Quasithin.H13.VolIC113
public import CFSG.Quasithin.Background.C129NativeSet
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Sub
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_sup_of_inf {R K : Subgroup G} (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (h : IsSylowTwoOf (R ⊓ K) K) :
    IsSylowTwoOf R (K ⊔ R) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR, fun P hPH hP hRP => ?_⟩
  intro t ht
  have htH : t ∈ R ⊔ K := by rw [sup_comm]; exact hPH ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R K hRK] at htH
  obtain ⟨r, hr, k, hk, rfl⟩ := htH
  have hkP : k ∈ P := by
    have := P.mul_mem (P.inv_mem (hRP hr)) ht
    simpa using this
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp h).2.2 (P ⊓ K) inf_le_right (hP.to_inf_left)
    (le_inf (inf_le_left.trans hRP) inf_le_right)
  have hkR : k ∈ R := (hmax ⟨hkP, hk⟩).1
  exact R.mul_mem hr hkR

omit [Finite G] in
theorem inf_normalizer_le_cgsIn_of_char {X T C : Subgroup G} (hCT : C ≤ T) (hC : C ≠ ⊥)
    (hchar : (C.subgroupOf T).Characteristic) :
    X ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn X T :=
  le_iSup_of_le C (le_iSup_of_le hCT (le_iSup_of_le hC (le_iSup_of_le hchar le_rfl)))

omit [Finite G] in
theorem mem_normalizer_inf_of {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
  constructor
  · intro hh
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA h).mp hh.1,
      (Subgroup.mem_normalizer_iff.mp hB h).mp hh.2⟩
  · intro hh
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA h).mpr hh.1,
      (Subgroup.mem_normalizer_iff.mp hB h).mpr hh.2⟩

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) :
      Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem omegaOneCenterOf_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    omegaOneCenterOf T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT0
  have hZ : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  have h2 : 2 ∣ Nat.card (Subgroup.center T) := by
    obtain ⟨k, hk⟩ := (hT.to_subgroup (Subgroup.center T)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center T) := Finite.one_lt_card
    rw [hk] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2 h2
  intro hbot
  have hzmem : ((z : T) : G) ∈ omegaOneCenterOf T := by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · refine ⟨(z : T).2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have := Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩
      exact congrArg (fun w : T => (w : G)) this
    · have h3 : (z : Subgroup.center T) ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have h4 := congrArg (fun w : Subgroup.center T => ((w : T) : G)) h3
      simpa using h4
  rw [hbot, Subgroup.mem_bot] at hzmem
  have h5 : z = 1 := Subtype.ext (Subtype.ext hzmem)
  rw [h5, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem ne_bot_of_isBlock2 {X T L : Subgroup G} (hT : IsSylowTwoOf T X) (hL : IsBlock2 X L) :
    T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLs : IsShort2 L := hL.1
  intro hbot
  have hU : blockU L ≤ T :=
    ((C1.blockU_le_blockQ hLs).trans (A4.pCoreOf_le_of_subnormal 2 (IsBlock2.isSubnormal hL))).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  rw [hbot] at hU
  obtain ⟨hlt, -⟩ := hLs.2.2.2.2
  exact absurd (lt_of_lt_of_le hlt (hU.trans bot_le)) (lt_irrefl _)

theorem normalizer_inf_le_of_alt5 {X T M L : Subgroup G} (hX : CharTwo X)
    (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M) (hL : IsBlock2 X L) (h5 : IsAltType L 5) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLs : IsShort2 L := hL.1
  have hsub : IsSubnormal L X := IsBlock2.isSubnormal hL
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hL.2.1 hL.2.2
  have hOL : pCoreOf 2 X ≤ Subgroup.normalizer (L : Set G) :=
    L246C127.le_normalizer_of_isSubnormal hsub (pCoreOf_le 2 X)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 X)).mpr
        (le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
      (L246C127.le_closure_oddPPow hLs.1)
  have hOT : pCoreOf 2 X ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hT0 : T ≠ ⊥ := ne_bot_of_isBlock2 hT hL
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  have hT₁L : T₁ ⊓ L = T ⊓ L := by
    ext x
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.le_normalizer h.2⟩, h.2⟩⟩
  obtain ⟨P, hT₁P, hP⟩ := exists_isSylowTwoOf_of_le
    (le_sup_right : T₁ ≤ L ⊔ T₁) (hT.2.1.to_le inf_le_left)
  have hLN : L ⊔ T₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := hP.1.trans hLN
  have hLP : L ⊔ P = L ⊔ T₁ := le_antisymm (sup_le le_sup_left hP.1) (sup_le_sup_left hT₁P L)
  have hPsyl : IsSylowTwoOf P (L ⊔ P) := by rw [hLP]; exact hP
  obtain ⟨hQ, hUC⟩ := stmtC113c G L P hPsyl hPN hLs h5
  intro y hy
  obtain ⟨hyL, hyN⟩ := hy
  have hΩT : omegaOneCenterOf T ≤ T := fun x hx =>
    ((Subgroup.closure_le (centerOf T)).mpr (fun w hw => hw.1) hx).1
  refine hcgs (inf_normalizer_le_cgsIn_of_char hΩT
    (omegaOneCenterOf_ne_bot hT.2.1 hT0) (Setup.characteristic_omegaOneCenterOf T)
    ⟨hL.2.1 hyL, ?_⟩)
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLs).trans (C1.blockQ_le L)
  have hUcent : blockU L ≤ Subgroup.centralizer
      ((P ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun c hc =>
      (Subgroup.mem_centralizer_iff.mp hc.2 u (hUL hu)).symm
  have hset : ((blockU L ⊔ (P ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) : Set G) =
      (blockU L : Set G) * ((P ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (hUcent.trans (Subgroup.centralizer_le_normalizer _))
  have hcent : ∀ z ∈ centerOf T, y * z * y⁻¹ = z := by
    intro z hz
    have hzT : z ∈ T := hz.1
    have hzO : z ∈ pCoreOf 2 X :=
      hX ⟨hT.1 hzT, Subgroup.mem_centralizer_iff.mpr fun w hw =>
        (Subgroup.mem_centralizer_iff.mp hz.2 w (hOT hw))⟩
    have hzQ : z ∈ pCoreOf 2 (L ⊔ P) := by
      rw [hLP]
      refine le_pCoreOf_of_le_normalizer 2 (inf_le_right : pCoreOf 2 X ⊓ (L ⊔ T₁) ≤ L ⊔ T₁)
        (fun g hg => ?_) ((pCoreOf_isPGroup 2 X).to_le inf_le_left) ⟨hzO, ?_⟩
      · have hgX : g ∈ X := sup_le hL.2.1 (inf_le_left.trans hT.1) hg
        exact mem_normalizer_inf_of (le_normalizer_pCoreOf 2 X hgX) (Subgroup.le_normalizer hg)
      · exact Subgroup.mem_sup_right ⟨hzT, hOL hzO⟩
    rw [hQ] at hzQ
    have hzQ' : z ∈ ((blockU L ⊔ (P ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) :
        Set G) := hzQ
    rw [hset] at hzQ'
    obtain ⟨u, hu, c, hc, rfl⟩ := hzQ'
    have hus : ∀ s ∈ T ⊓ L, s * u = u * s := by
      intro s hs
      have h1 : s * (u * c) = (u * c) * s :=
        (Subgroup.mem_centralizer_iff.mp hz.2 s hs.1)
      have h2 : s * c = c * s := Subgroup.mem_centralizer_iff.mp hc.2 s hs.2
      calc s * u = s * (u * c) * c⁻¹ := by group
        _ = (u * c) * s * c⁻¹ := by rw [h1]
        _ = u * (c * s) * c⁻¹ := by group
        _ = u * (s * c) * c⁻¹ := by rw [h2]
        _ = u * s := by group
    have hyu : y * u * y⁻¹ = u := conj_eq_of_alt5 hLs h5 hSL hyL hyN hu hus
    have hyc : y * c = c * y := Subgroup.mem_centralizer_iff.mp hc.2 y hyL
    calc y * (u * c) * y⁻¹ = (y * u * y⁻¹) * (y * c * y⁻¹) := by group
      _ = u * c := by rw [hyu, hyc]; group
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
  have hwZ : w ∈ centerOf T := (Subgroup.closure_le _).mpr (fun x hx => hx.1) hw
  have h1 := hcent w hwZ
  calc w * y = y * w * y⁻¹ * y := by rw [h1]
    _ = y * w := by group

theorem thompsonJ_eq_of_le {S R : Subgroup G} (hJ : thompsonJ S ≤ R) (hRS : R ≤ S) :
    thompsonJ R = thompsonJ S := by
  have hSR : ∀ A, IsMaxElemAbelian S A → IsMaxElemAbelian R A := by
    intro A hA
    refine ⟨(le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ S).trans hJ, hA.2.1,
      fun B hBR hB => hA.2.2 B (hBR.trans hRS) hB⟩
  have hiff : ∀ A, IsMaxElemAbelian R A ↔ IsMaxElemAbelian S A := by
    intro A
    refine ⟨fun hA => ⟨hA.1.trans hRS, hA.2.1, fun B hBS hB => ?_⟩, hSR A⟩
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
    exact (hA₀.2.2 B hBS hB).trans (hA.2.2 A₀ (hSR A₀ hA₀).1 hA₀.2.1)
  unfold thompsonJ
  exact iSup_congr fun A => iSup_congr_Prop (hiff A) fun _ => rfl

omit [Finite G] in
theorem thompsonJ_le_self (S : Subgroup G) : thompsonJ S ≤ S :=
  iSup₂_le fun _ hA => hA.1

omit [Finite G] in
theorem thompsonJ_le_baum' (S : Subgroup G) : thompsonJ S ≤ baum S := by
  refine le_inf (thompsonJ_le_self S) fun j hj => Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hxZ : x ∈ centerOf (thompsonJ S) :=
    (Subgroup.closure_le (centerOf (thompsonJ S))).mpr (fun w hw => hw.1) hx
  exact (Subgroup.mem_centralizer_iff.mp hxZ.2 j hj).symm

omit [Finite G] in
theorem mem_normalizer_thompsonJ {Y : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((thompsonJ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have h := thompsonJ_map_mulEquiv (MulAut.conj g) Y
  rw [show (MulAut.conj g).toMonoidHom = (MulAut.conj g : G →* G) from rfl] at h
  rw [h, hg]

theorem thompsonJ_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    thompsonJ T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT0
  have h2 : 2 ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    have h1 : 1 < Nat.card T := Finite.one_lt_card
    rw [hk] at h1 ⊢
    exact dvd_pow_self 2 (by rintro rfl; simp at h1)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hE : IsElemAbelian 2 (Subgroup.zpowers (t : G)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨_, ⟨i, rfl⟩⟩ := a
      obtain ⟨_, ⟨j, rfl⟩⟩ := b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := hx
      have ht2 : (t : G) ^ 2 = 1 := by
        have := congrArg Subtype.val (pow_orderOf_eq_one t)
        rw [ht] at this
        simpa using this
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hle : Subgroup.zpowers (t : G) ≤ T := (Subgroup.zpowers_le).mpr t.2
  have hcard := hA.2.2 _ hle hE
  have htne : (t : G) ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hz : 1 < Nat.card (Subgroup.zpowers (t : G)) := by
    rw [Nat.card_zpowers, orderOf_submonoid t]
    rw [ht]
    norm_num
  intro hbot
  have hAb : A = ⊥ := by
    rw [eq_bot_iff, ← hbot]
    exact le_iSup₂_of_le A hA le_rfl
  rw [hAb, Subgroup.card_bot] at hcard
  omega

omit [Finite G] in
theorem not_le_normalizer_of_sl2Model {L S : Subgroup G} (hS : IsSylowTwoOf S L)
    (hmod : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ), Fintype.card F = 2 ^ m ∧
      0 < m ∧ ∃ α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F,
        Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L) :
    ¬ L ≤ Subgroup.normalizer (S : Set G) := by
  intro hLN
  obtain ⟨F, _, _, m, hcard, hm, α, hα, hαk⟩ := hmod
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hm (by rw [Nat.card_eq_fintype_card, hcard])
  have hSO : S ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hS.1 hLN hS.2.1
  have hsub : S.subgroupOf L ≤ CFSG.pCore 2 ↥L := by
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := hSO hx
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Subtype.ext hyx
    rw [← this]
    assumption
  have hodd : ¬ 2 ∣ (CFSG.pCore 2 ↥L).index := fun h2 =>
    hS.2.2 (h2.trans (Subgroup.index_dvd_of_le hsub))
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = (CFSG.pCore 2 ↥L).index := by
    rw [← hαk, Subgroup.index,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
  let t : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have ht2 : t ^ 2 = 1 := by
    rw [sq]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    show !![(1 : F), 1; 0, 1] * !![(1 : F), 1; 0, 1] = 1
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [one_add_one_eq_two, h2]
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [t] at this
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hdvd := orderOf_dvd_natCard t
  rw [hord, hcardSL] at hdvd
  exact hodd hdvd

theorem isMinimalParabolic_sup {L R : Subgroup G} (hR : IsPGroup 2 R)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowTwoOf (R ⊓ L) L)
    (hmod : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ), Fintype.card F = 2 ^ m ∧
      0 < m ∧ ∃ α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F,
        Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L) :
    IsMinimalParabolic R (L ⊔ R) := by
  have hnot := not_le_normalizer_of_sl2Model hS hmod
  have hset : ((L ⊔ R : Subgroup G) : Set G) = (L : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L R hRN
  set K := (L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)) ⊔ R with hK
  have hRB : R ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    intro r hr
    have hrRL : r ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_inf_of (Subgroup.le_normalizer hr) (hRN hr)
    exact mem_normalizer_inf_of (hRN hr) (Subgroup.le_normalizer hrRL)
  have hKset : (K : Set G) = ((L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :
      Subgroup G) : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ R hRB
  refine ⟨isSylowTwoOf_sup_of_inf hR hRN (by rwa [inf_comm, inf_comm L]), fun h => hnot ?_,
    K, le_sup_right, lt_of_le_of_ne (sup_le (inf_le_left.trans le_sup_left) le_sup_right) ?_,
    fun X hRX hX => ?_⟩
  · intro l hl
    exact mem_normalizer_inf_of (h (Subgroup.mem_sup_left hl)) (Subgroup.le_normalizer hl)
  · intro hKeq
    apply hnot
    intro l hl
    have hlK : l ∈ (K : Set G) := by
      rw [hKeq]
      exact Subgroup.mem_sup_left hl
    rw [hKset] at hlK
    obtain ⟨b, hb, r, hr, rfl⟩ := hlK
    have hrL : r ∈ L := by
      have := L.mul_mem (L.inv_mem hb.1) hl
      simpa using this
    exact Subgroup.mul_mem _ hb.2 (Subgroup.le_normalizer ⟨hr, hrL⟩)
  · rcases L238.dickson_block hS (le_inf (inf_le_left.trans hRX) inf_le_right) inf_le_right hmod
      with hA | hA
    · exfalso
      have hLX : L ≤ X := fun l hl => by
        have : l ∈ X ⊓ L := by rw [hA]; exact hl
        exact this.1
      exact absurd (sup_le hLX hRX) (not_le_of_gt hX)
    · intro x hx
      have hxs : x ∈ ((L ⊔ R : Subgroup G) : Set G) := hX.le hx
      rw [hset] at hxs
      obtain ⟨l, hl, r, hr, rfl⟩ := hxs
      have hlX : l ∈ X := by
        have := X.mul_mem hx (X.inv_mem (hRX hr))
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hl, hA ⟨hlX, hl⟩⟩)
        (Subgroup.mem_sup_right hr)

theorem normalizer_inf_le_of_lin2 {X T M L : Subgroup G}
    (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M) (hL : IsBlock2 X L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) (hJ : ⁅L, thompsonJ T⁆ = L) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hL.2.1 hL.2.2
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  have hJN : thompsonJ T ≤ Subgroup.normalizer (L : Set G) := by
    have h := Subgroup.normalizer_commutator_ge_right L (thompsonJ T)
    rwa [hJ] at h
  have hJT₁ : thompsonJ T ≤ T₁ := le_inf (thompsonJ_le_self T) hJN
  have hJeq : thompsonJ T₁ = thompsonJ T := thompsonJ_eq_of_le hJT₁ inf_le_left
  have hT₁2 : IsPGroup 2 T₁ := hT.2.1.to_le inf_le_left
  have hT₁N : T₁ ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hT₁L : T₁ ⊓ L = T ⊓ L := by
    ext x
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.le_normalizer h.2⟩, h.2⟩⟩
  have hmod := L238.exists_sl2_model (Or.inl ⟨n, hn, hlin⟩)
  have hmin : IsMinimalParabolic T₁ (L ⊔ T₁) :=
    isMinimalParabolic_sup hT₁2 hT₁N (by rw [hT₁L]; exact hSL) hmod
  have hLnorm : (L.subgroupOf (L ⊔ T₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT₁N)
  have hblk : IsChi0Block (L ⊔ T₁) L :=
    ⟨⟨hL.1, le_sup_left, hLnorm.isSubnormal⟩, Or.inl ⟨n, hn, hlin⟩⟩
  have hth : ⁅L, thompsonJ T₁⁆ = L := by rw [hJeq]; exact hJ
  obtain ⟨hBsyl, hBle⟩ := C56.baumann_Lin2_single hmin hblk hn hlin hth rfl hT₁N
  set Y := baum T₁ with hY
  have hYT₁ : Y ≤ T₁ := inf_le_left
  have hYN : L ⊔ Y ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer
    (hYT₁.trans hT₁N)
  have hYLsyl : IsSylowTwoOf (Y ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hBsyl le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hYN).isSubnormal
  have hYL : T ⊓ L = Y ⊓ L :=
    hYLsyl.eq_of_le (le_inf (inf_le_left.trans (hYT₁.trans inf_le_left)) inf_le_right)
      inf_le_right (hT.2.1.to_le inf_le_left)
  have hO : pCoreOf 2 (L ⊔ Y) ≤ Y := B6.pCoreOf_two_le_of_isSylowTwoOf hBsyl
  have hYeq : Y = (T ⊓ L) ⊔ pCoreOf 2 (L ⊔ Y) := by
    refine le_antisymm ?_ (sup_le (hYL ▸ inf_le_left) hO)
    rw [hYL]
    exact hBle
  have hJY : thompsonJ Y = thompsonJ T := by
    rw [thompsonJ_eq_of_le (thompsonJ_le_baum' T₁) inf_le_left, hJeq]
  intro y hy
  have hyY : y ∈ Subgroup.normalizer (Y : Set G) := by
    rw [hYeq]
    exact mem_normalizer_sup hy.2 (le_normalizer_pCoreOf 2 (L ⊔ Y) (Subgroup.mem_sup_left hy.1))
  have hyJ : y ∈ Subgroup.normalizer ((thompsonJ T : Subgroup G) : Set G) := by
    rw [← hJY]
    exact mem_normalizer_thompsonJ hyY
  exact hcgs (inf_normalizer_le_cgsIn_of_char (thompsonJ_le_self T)
    (thompsonJ_ne_bot hT.2.1 (ne_bot_of_isBlock2 hT hL)) (Setup.characteristic_thompsonJ T)
    ⟨hL.2.1 hy.1, hyJ⟩)

theorem isBorelOfBlock_of_isChi0Block {X T M L : Subgroup G}
    (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hcgs : cgsIn X T ≤ M) (hTM : T ≤ M)
    (hL : IsChi0Block X L) (hJ : ⁅L, thompsonJ T⁆ = L) (hLM : ¬ L ≤ M) :
    IsBorelOfBlock L (L ⊓ M) := by
  have hU := C129Native.isBorelOfBlockUsed_of_isChi0Block hT hTM hL hLM
  unfold IsBorelOfBlock
  unfold IsBorelOfBlockUsed at hU
  split_ifs at hU ⊢ with hc
  · exact hU
  · have h3 : ¬ IsAltType L 3 := fun h3 =>
      hc (C2Six.natCard_pCore_quotient_of_isAltType_three h3)
    have hmod : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5 := by
      rcases hL.2 with h | h3' | h5
      · exact Or.inl h
      · exact absurd h3' h3
      · exact Or.inr h5
    have hS : IsSylowTwoOf (T ⊓ L) L :=
      RankOneRecog.isSylowTwoOf_inf_of_subnormal hT hL.1.2.1 hL.1.2.2
    have hQM : pCoreOf 2 L ≤ M := hS.pCoreOf_le.trans (inf_le_left.trans hTM)
    have hNM : L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ M := by
      rcases hmod with ⟨n, hn, hlin⟩ | h5
      · exact normalizer_inf_le_of_lin2 hT hcgs hL.1 hn hlin hJ
      · exact normalizer_inf_le_of_alt5 hX hT hcgs hL.1 h5
    refine ⟨T ⊓ L, hS, le_antisymm (sup_le ?_ ?_) ?_⟩
    · refine le_inf inf_le_left ?_
      have hSA : T ⊓ L ≤ L ⊓ M := le_inf inf_le_right (inf_le_left.trans hTM)
      rcases L238.dickson_block hS hSA inf_le_left (L238.exists_sl2_model hmod) with hA | hA
      · exfalso
        apply hLM
        intro x hx
        have : x ∈ L ⊓ M := by rw [hA]; exact hx
        exact this.2
      · exact hA
    · exact le_inf (pCoreOf_le 2 L) (hS.pCoreOf_le.trans Subgroup.le_normalizer)
    · exact (le_inf inf_le_left hNM).trans le_sup_left

end CFSG.Quasithin.H13.VolI
