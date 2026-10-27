module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828E
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XUpper
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XExists
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XChief
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XNontriv
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XInputs
public import CFSG.Quasithin.Background.S1567Y
public import CFSG.Quasithin.Vol2.Ch8Sec2D3Inputs

public section

namespace CFSG.Quasithin.H13.L827X

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H13
open CFSG.LieType.BorelTits
open scoped commutatorElement

theorem mem_normalizer_sup_of {Γ : Type} [Group Γ] {A B : Subgroup Γ} {g : Γ}
    (hA : g ∈ Subgroup.normalizer (A : Set Γ)) (hB : g ∈ Subgroup.normalizer (B : Set Γ)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  have hmapA : A.map (MulAut.conj g).toMonoidHom = A := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hA a).mp ha
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · exact (hA (g⁻¹ * x * g)).mpr (by simpa [mul_assoc] using hx)
      · simp [MulAut.conj_apply, mul_assoc]
  have hmapB : B.map (MulAut.conj g).toMonoidHom = B := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hB b).mp hb
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · exact (hB (g⁻¹ * x * g)).mpr (by simpa [mul_assoc] using hx)
      · simp [MulAut.conj_apply, mul_assoc]
  have hmap : (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hmapA, hmapB]
  intro h
  constructor
  · intro hh
    have : g * h * g⁻¹ ∈ (A ⊔ B).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hh
    rwa [hmap] at this
  · intro hh
    have hm : (MulAut.conj g).toMonoidHom h ∈ (A ⊔ B).map (MulAut.conj g).toMonoidHom := by
      rw [hmap]
      simpa [MulAut.conj_apply, mul_assoc] using hh
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hm
    have h1 : g * y * g⁻¹ = g * h * g⁻¹ := hyeq
    have hyh : y = h := by simpa using h1
    rw [← hyh]
    exact hy

theorem commutator_le_of_le_centralizer {Γ : Type} [Group Γ] {U Y : Subgroup Γ}
    (h : Y ≤ Subgroup.centralizer (U : Set Γ)) : ⁅U, Y⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro u hu y hy
  have hc : u * y = y * u := (Subgroup.mem_centralizer_iff.mp (h hy)) u hu
  have : ⁅u, y⁆ = 1 := by
    rw [commutatorElement_def]
    calc u * y * u⁻¹ * y⁻¹ = y * u * u⁻¹ * y⁻¹ := by rw [hc]
      _ = 1 := by group
  rw [this]
  exact U.one_mem

theorem step827Xi_of (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (h825 : Stmt8_2_5)
    (hVc : Stmt827VCard) (hS6 : XiChiefLowerBound) : Step827Xi := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hr K hK hLUK hKq X hXi hXK hXC hXM
    hNKX hXK' H' h' k' hH' hH'XT hh' hC'
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe, hTU, -, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  set U : Subgroup G := ch82U (fsuV T I) h with hUdef
  have hrk : rk ↥U = 4 := by
    rcases hr with hr | hr
    · exact (hC5.2.2.2.1 hr).2.2.2
    · exact (hC5.2.2.2.2.1 hr).2.2.2
  have hT : quasithinIsSylowTwo T := hyp.fsu.sylow
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := CFSG.Quasithin.le_normalizer_conjClosure I T
  have hVT : fsuV T I ≤ T :=
    fsuV_le_T hyp.fsu hV (by rw [hL0]; exact sup_le hLN hTV)
  have hVp : IsPGroup 2 ↥(fsuV T I) := isPGroup_of_isElemAbelian_two hV
  have hVe : ∀ x ∈ fsuV T I, x ^ 2 = 1 := fun x hx => hV.2 _ hx
  have hUV : U ≤ fsuV T I := inf_le_left
  have hUT : U ≤ T := hUV.trans hVT
  have hTH'le : T ≤ H' := hH'.1.1
  have hTH' : QuasithinUnique.IsSylowTwoOf T H' := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH'le
  have hH'M : ¬ H' ≤ fsuM T L := hH'.2.1
  have hVH' : ¬ fsuV T I ≤ pCoreOf 2 H' := hC'.1
  have hOT : pCoreOf 2 X ≤ T := pCoreOf_le_of_quasithinIsSylowTwo hT hXi.2.1
  have hTO : T ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hXi.2.1.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X
  have hH'O : H' ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hH'XT.trans (sup_le hXN hTO)
  have hCT : CharTwo (X ⊔ T) := charTwo_of_inH' hyp.fsu.qtke hT ⟨le_sup_right, hXi.2.2.1⟩
  have hdecomp : H' = oTwoUpper H' ⊔ T :=
    (C1Pack12.oTwoUpper_sup_eq_of_sylow hTH').symm
  have hX₁X : oTwoUpper H' ⊔ pCoreOf 2 X ≤ X :=
    sup_le ((oTwoUpper_mono hH'XT).trans (S1567.oTwoUpper_sup_le hXi.2.1 hT.1))
      (pCoreOf_le 2 X)
  have hTX₁ : T ≤ Subgroup.normalizer ((oTwoUpper H' ⊔ pCoreOf 2 X : Subgroup G) : Set G) :=
    fun t ht => mem_normalizer_sup_of ((hTH'le.trans (le_normalizer_oTwoUpper H')) ht) (hTO ht)
  have hX₁lt : pCoreOf 2 X < oTwoUpper H' ⊔ pCoreOf 2 X := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    apply hH'M
    have h2 : oTwoUpper H' ≤ pCoreOf 2 X := by
      rw [heq]
      exact le_sup_left
    have hH'T : H' ≤ T := (le_of_eq hdecomp).trans (sup_le (h2.trans hOT) le_rfl)
    exact hH'T.trans (CFSG.Quasithin.le_normalizer_conjClosure L T)
  obtain ⟨v, hvV, hvX₁⟩ :=
    exists_mem_comm_not_le_pCoreOf hT hXi hTH' hH'XT hVT hTV hVH'
  obtain ⟨p, hp, hp2, hpX, -, -⟩ := hXi.exists_prime_sup_eq
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge p (bot_le : (⊥ : Subgroup G) ≤ X) IsPGroup.of_bot
  set X₁ : Subgroup G := oTwoUpper H' ⊔ pCoreOf 2 X with hX₁def
  set O : Subgroup G := pCoreOf 2 X with hOdef
  set Y₁ : Subgroup G := X₁ ⊓ P with hY₁def
  have hO2 : IsPGroup 2 ↥O := pCoreOf_isPGroup 2 X
  have hY₁p : IsPGroup p ↥Y₁ := hP.isPGroup.to_le inf_le_right
  set Λ : Subgroup G := CFSG.Quasithin.conjClosure K T ⊔ T with hΛdef
  have hKc : K ≤ CFSG.Quasithin.conjClosure K T := fun k hk =>
    Subgroup.subset_closure ⟨1, T.one_mem, k, hk, by simp⟩
  have hKΛ : K ≤ Λ := hKc.trans le_sup_left
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := le_of_mem_cComp hK
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := (Subgroup.le_normalizer).trans hNKX
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := hKX.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hconj_le : ∀ A : Subgroup G, K ≤ Subgroup.normalizer (A : Set G) →
      T ≤ Subgroup.normalizer (A : Set G) →
      CFSG.Quasithin.conjClosure K T ≤ Subgroup.normalizer (A : Set G) := by
    intro A hKA hTA
    unfold CFSG.Quasithin.conjClosure
    rw [Subgroup.closure_le]
    rintro x ⟨t, ht, z, hz, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTA ht) (hKA hz)) (Subgroup.inv_mem _ (hTA ht))
  have hΛU : Λ ≤ Subgroup.normalizer (U : Set G) := sup_le (hconj_le U hKN hTU) hTU
  have hΛO : Λ ≤ Subgroup.normalizer (O : Set G) := sup_le (hconj_le O hKO hTO) hTO
  have hΛR : Λ ≤ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_sup_of (hΛO hg) (hΛU hg)
  have hXΛ : X ≤ Λ := hXK.trans hKΛ
  have hOΛ : O ≤ Λ := (pCoreOf_le 2 X).trans hXΛ
  have hUΛ : U ≤ Λ := hUT.trans le_sup_right
  have hΛT : T ≤ Λ := le_sup_right
  have hΛ_of_R : O ⊔ U ≤ Λ := sup_le hOΛ hUΛ
  have hY₁Λ : Y₁ ≤ Λ := inf_le_left.trans ((hX₁X).trans hXΛ)
  have hUY : ⁅U, Y₁⁆ ≤ U := commutator_le_of_le_centralizer ((inf_le_left.trans hX₁X).trans hXC)
  have hX₁ne : X₁ ≠ O := hX₁lt.ne'
  have hRY : ¬ ⁅O ⊔ U, Y₁⁆ ≤ U :=
    not_commutator_R_le_U hp2 hT hXi hP hpX hX₁lt.le hX₁X hX₁ne hXC hCT
  have hRT : O ⊔ U ≤ T := sup_le hOT hUT
  have hcop : ∀ A : Subgroup G, A ≤ O ⊔ U → Y₁ ≤ Subgroup.normalizer (A : Set G) →
      ⁅⁅A, Y₁⁆, Y₁⁆ = ⁅A, Y₁⁆ := by
    intro A hA hYA
    have hA2 : IsPGroup 2 ↥A := hT.1.to_le (hA.trans hRT)
    exact coprime_commutator_commutator_eq hYA
      (IsPGroup.coprime_card_of_ne p 2 hp2 Y₁ A hY₁p hA2)
  obtain ⟨W₀, W₁, hUW₀, hW₀W₁, hW₁R, hΛW₀, hΛW₁, hchief, hW₁Y⟩ :=
    exists_chief_factor_comm hΛR hΛU (le_sup_right : U ≤ O ⊔ U) hY₁Λ hUY hRY hcop
  have hWX : ¬ ⁅W₁, X₁⁆ ≤ W₀ := fun hle =>
    hW₁Y ((Subgroup.commutator_mono le_rfl inf_le_left).trans hle)
  have h8 := hS6 G T X K U (fsuV T I) X₁ W₀ W₁ v hT hXi hCT hK hXK hNKX hXK' hXC hTU hUV hVT
    hTV hVe hX₁lt hX₁X hTX₁ hvV hvX₁ hUW₀ hW₀W₁ hW₁R hΛW₀ hΛW₁ hchief hWX
  have hH'U : H' ≤ Subgroup.normalizer (U : Set G) := by
    intro g hg
    have hXT : X ⊔ T ≤ Subgroup.normalizer (U : Set G) :=
      sup_le (hXC.trans (Subgroup.centralizer_le_normalizer _)) hTU
    exact hXT (hH'XT hg)
  have hRH' : O ⊔ U ≤ pCoreOf 2 H' := by
    refine CFSG.Quasithin.RonanD33.le_pCoreOf_of_le_normalizer (sup_le (hOT.trans hTH'le) (hUT.trans hTH'le))
      (fun g hg => mem_normalizer_sup_of (hH'O hg) (hH'U hg)) (hT.1.to_le hRT)
  have hVR : ¬ fsuV T I ≤ O ⊔ U := fun hle => hVH' (hle.trans hRH')
  have hcommV : ⁅W₁, Subgroup.zpowers v⁆ ≤ fsuV T I ⊓ (O ⊔ U) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyV : y ∈ fsuV T I := (Subgroup.zpowers_le.mpr hvV) hy
    have hxR : x ∈ O ⊔ U := hW₁R hx
    have hxT : x ∈ T := hRT hxR
    have hvΛ : v ∈ Λ := (hVT.trans hΛT) hvV
    have hyΛ : y ∈ Λ := (Subgroup.zpowers_le.mpr hvΛ) hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have h1 : x * y * x⁻¹ ∈ fsuV T I := (Subgroup.mem_normalizer_iff.mp (hTV hxT) y).mp hyV
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hyV)
    · rw [commutatorElement_def]
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      have h2 : y * x⁻¹ * y⁻¹ ∈ O ⊔ U :=
        (Subgroup.mem_normalizer_iff.mp (hΛR hyΛ) x⁻¹).mp (Subgroup.inv_mem _ hxR)
      exact Subgroup.mul_mem _ hxR h2
  have hPN : fsuV T I ⊓ (O ⊔ U) ≤ Subgroup.normalizer (W₀ : Set G) :=
    fun g hg => hΛW₀ (hΛ_of_R hg.2)
  have hUcard : Nat.card ↥U = 16 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hVp.to_le hUV)
    have hrn : rk ↥U = n := by
      unfold rk
      rw [hn, padicValNat.prime_pow]
    rw [hrk] at hrn
    rw [hn, ← hrn]
    norm_num
  have hVc' : Nat.card ↥(fsuV T I) ≤ 2 ^ 10 := by
    rcases hr with ⟨n, hn⟩ | hr'
    · have hn1 : n = 1 := hC5.2.2.1 n hn
      exact hVc G T L I hyp (Or.inl (hn1 ▸ hn))
    · exact hVc G T L I hyp (Or.inr hr')
  have h5 := mQuot_commutator_le_five hVp hUcard hVc' hUV hUW₀ hW₀W₁.le hW₁R hVR hcommV hPN
  exact absurd (h8.trans h5) (by norm_num)

end CFSG.Quasithin.H13.L827X
