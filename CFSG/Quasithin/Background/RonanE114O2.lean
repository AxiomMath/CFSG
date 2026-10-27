module

public import CFSG.Quasithin.Vol2.Ch11SecOE9A
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecE3
open CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

@[expose] def NormalTwoDichotomy {S : Type} [Group S] (X R : Subgroup S) : Prop :=
  (∃ N : Subgroup S, N ≤ R ∧ (N.subgroupOf R).Normal ∧ IsPGroup 2 N ∧ X ≤ N) ∨
    (∀ N : Subgroup S, N ≤ R → (N.subgroupOf R).Normal → IsPGroup 2 N → X ⊓ N = ⊥)

theorem NormalTwoDichotomy.map {G : Type} [Group G] {S : Type} [Group S] {X : Subgroup S}
    {θ : S →* G} (hθ : Function.Injective θ) {L : Subgroup G} (hL : θ.range = L)
    {R : Subgroup G} (hRL : R ≤ L) (hX : NormalTwoDichotomy X (R.comap θ)) :
    NormalTwoDichotomy (X.map θ) R := by
  have hRmap : (R.comap θ).map θ = R :=
    Subgroup.map_comap_eq_self (hL ▸ hRL)
  unfold NormalTwoDichotomy at hX ⊢
  rcases hX with ⟨N, hNR, hNn, hN2, hXN⟩ | hsol
  · refine Or.inl ⟨N.map θ, ?_, ?_, hN2.map θ, Subgroup.map_mono hXN⟩
    · exact hRmap ▸ Subgroup.map_mono hNR
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hRmap ▸ Subgroup.map_mono hNR)]
      rw [← hRmap]
      exact (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mp hNn)).trans
        (Subgroup.le_normalizer_map θ)
  · refine Or.inr fun N hNR hNn hN2 => ?_
    have hN'R : N.comap θ ≤ R.comap θ := Subgroup.comap_mono hNR
    have hN'n : ((N.comap θ).subgroupOf (R.comap θ)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN'R]
      intro x hx
      have hxN := (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mp hNn hx
      rw [Subgroup.mem_normalizer_iff] at hxN ⊢
      intro y
      have := hxN (θ y)
      simpa only [Subgroup.mem_comap, map_mul, map_inv] using this
    have h0 := hsol _ hN'R hN'n (hN2.comap_of_injective θ hθ)
    refine eq_bot_iff.mpr ?_
    rintro _ ⟨⟨x, hx, rfl⟩, hxN⟩
    have : x ∈ X ⊓ N.comap θ := ⟨hx, hxN⟩
    rw [h0, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _

theorem conjSub_eq_of_normal' {G : Type} [Group G] {L : Subgroup G} [L.Normal] (g : G) :
    A1b.conjSub g L = L := by
  rw [A1b.conjSub_eq_iff_mem_normalizer, Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact Subgroup.mem_top g

variable {G : Type} [Group G] [Finite G]

theorem not_isE_of_le_pCoreOf {j : ℕ} {H T A K : Subgroup G} (hAO : A ≤ pCoreOf 2 K)
    (hE : E1.IsE j H T A K) : False := by
  obtain ⟨-, -, -, hrank⟩ := hE
  have hAO' : A.subgroupOf K ≤ CFSG.Open.pCore 2 ↥K := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hAO hx
    exact (Subtype.ext hyx : y = x) ▸ hy
  have hbar2 : E1.barO2 ↥K (A.subgroupOf K) = ⊥ := by
    rw [E1.barO2, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hAO'
  have hbarR : E1.barRad ↥K (A.subgroupOf K) = ⊥ := by
    rw [E1.barRad, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hAO'.trans E3.pCore_two_le_solvableRadical
  rcases hrank with ⟨⟨p, -, -, -, -, -, h2⟩, -⟩ | ⟨hE2, -⟩
  · rw [hbar2, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  · exact E1.RootLift.not_eTwo_of_barRad_eq_bot hbarR hE2

theorem le_nParam_of_normalTwo {n : ℕ} {T L A : Subgroup G} [L.Normal] (hn : 2 ≤ n)
    (hT : IsSylowIn 2 T ⊤) (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hAT : A ≤ T) (hAL : A ≤ L) (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hcard : 2 ^ n ≤ Nat.card A)
    (hR : ∀ R : Subgroup G, R ≤ L → A ≤ R → NormalTwoDichotomy A R) :
    (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  refine le_nParam_of_forall_not_isE hn hT hO2 hAT hA hA1 fun g hgT K hK => ?_
  have hK' : E1.IsE (n - 1) ⊤ (A1b.conjSub g⁻¹ T) A (A1b.conjSub g⁻¹ K) := by
    have h := (E1.isE_conj g⁻¹).mpr hK
    rwa [Sp4.conjSub_top_eq, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one] at h
  have hAT' : A ≤ A1b.conjSub g⁻¹ T := Sp4.le_conjSub_inv hgT
  have hT'syl : IsSylowIn 2 (A1b.conjSub g⁻¹ T) ⊤ := by
    have h := (E1.isSylowIn_conj_iff (p := 2) g⁻¹ (P := T) (H := ⊤)).mpr hT
    rwa [Sp4.conjSub_top_eq] at h
  set K' := A1b.conjSub g⁻¹ K with hK'def
  obtain ⟨hAK, hcardK⟩ := E3.card_le_of_isE hT'syl hAT' hA hK'
  have hAnot : ¬ A ≤ pCoreOf 2 K' := fun h => not_isE_of_le_pCoreOf h hK'
  rcases hR (K' ⊓ L) inf_le_right (le_inf hAK hAL) with ⟨N, hNR, hNn, hN2, hAN⟩ | hsol
  ·
    refine hAnot (hAN.trans ?_)
    have h1 : N.subgroupOf K' ≤ CFSG.Open.pCore 2 ↥K' := Sp4.subgroupOf_le_pCore hNR hNn hN2
    have h2 := Subgroup.map_mono (f := K'.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le (hNR.trans inf_le_left)] at h2
  ·
    have hN0R : pCoreOf 2 K' ⊓ L ≤ K' ⊓ L :=
      inf_le_inf_right L (CFSG.LieType.BorelTits.pCoreOf_le 2 K')
    have hN0n : ((pCoreOf 2 K' ⊓ L).subgroupOf (K' ⊓ L)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN0R]
      refine (le_inf (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K')) ?_).trans
        Subgroup.inf_normalizer_le_normalizer_inf
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    have hN02 : IsPGroup 2 (pCoreOf 2 K' ⊓ L : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K').to_le inf_le_left
    have h0 := hsol _ hN0R hN0n hN02
    have h1 : A ⊓ pCoreOf 2 K' = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      have hx' : x ∈ A ⊓ (pCoreOf 2 K' ⊓ L) := ⟨hx.1, hx.2, hAL hx.1⟩
      rwa [h0] at hx'
    rw [h1, Subgroup.card_bot] at hcardK
    have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem le_nParam_of_normalTwo_model {T : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {S : Type} [Group S]
    (e : ↥(CFSG.generalizedFitting G) ≃* S) (hnab : ∃ x y : S, x * y ≠ y * x)
    {X : Subgroup S} (hXel : IsElemAbelian 2 X) (hXcard : 2 ^ n ≤ Nat.card X)
    (hdich : ∀ R : Subgroup S, X ≤ R → NormalTwoDichotomy X R) :
    (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := CFSG.generalizedFitting G with hLdef
  have hnab' : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
  have hAS := almostSimple_generalizedFitting hs hnab' hT.1 hFT
  have hTsyl : IsSylowIn 2 T ⊤ := ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
  have hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN h2 =>
    le_bot_iff.mp ((CFSG.LieType.BorelTits.le_pCore 2 hN h2).trans
      (E3.pCore_two_le_solvableRadical.trans hAS.solvableRadical_eq_bot.le))
  set θ : S →* G := L.subtype.comp e.symm.toMonoidHom with hθdef
  have hθi : Function.Injective θ := L.subtype_injective.comp e.symm.injective
  have hθr : θ.range = L := by
    rw [hθdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hX2 : IsPGroup 2 X := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hXel.2 x x.2)⟩
  obtain ⟨g, hg⟩ := E1.exists_conjSub_le_of_isSylowIn hTsyl (hX2.map θ)
  set θ' : S →* G := (MulAut.conj g).toMonoidHom.comp θ with hθ'def
  have hθ'i : Function.Injective θ' := (MulAut.conj g).injective.comp hθi
  have := hAS.normal
  have hθ'r : θ'.range = L := by
    rw [hθ'def, MonoidHom.range_comp, hθr]
    exact conjSub_eq_of_normal' g
  have hAeq : A1b.conjSub g (X.map θ) = X.map θ' := by
    rw [A1b.conjSub, Subgroup.map_map]
  rw [hAeq] at hg
  have hcard : Nat.card (X.map θ') ≥ 2 ^ n := by
    rw [Subgroup.card_map_of_injective hθ'i]
    exact hXcard
  refine le_nParam_of_normalTwo (L := L) hn hTsyl hO2 hg ?_ (E1.isElemAbelian_map' θ' hXel)
    ?_ hcard ?_
  · rw [← hθ'r]
    exact Subgroup.map_le_range _ _
  · intro h0
    rw [h0, Subgroup.card_bot] at hcard
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  · intro R hRL hAR
    exact NormalTwoDichotomy.map hθ'i hθ'r hRL (hdich (R.comap θ') fun x hx => hAR ⟨x, hx, rfl⟩)

theorem mem_conjSub_inv_iff {c x : G} {P : Subgroup G} :
    x ∈ A1b.conjSub c⁻¹ P ↔ c * x * c⁻¹ ∈ P := by
  rw [A1b.mem_conjSub_iff]
  simp

theorem conjSub_inf (g : G) (X Y : Subgroup G) :
    A1b.conjSub g (X ⊓ Y) = A1b.conjSub g X ⊓ A1b.conjSub g Y :=
  Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem conjSub_bot (g : G) : A1b.conjSub g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem normalTwo_of_BT [Fact (Nat.Prime 2)] (hBT : CFSG.LieType.BorelTits.Holds G 2)
    {U B H A : Subgroup G} (hU : IsSylowIn 2 U ⊤) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hHB : H ≤ B)
    (hpos : ∀ c : G, ∃ b ∈ B, ∃ A₁ : Subgroup G,
      (∀ O : Subgroup G, H ≤ Subgroup.normalizer (O : Set G) → A₁ ⊓ O = ⊥ ∨ A₁ ≤ O) ∧
        A1b.conjSub c⁻¹ A = A1b.conjSub b A₁) :
    ∀ R : Subgroup G, A ≤ R → NormalTwoDichotomy A R := by
  intro R hAR
  have hRn : R ≤ Subgroup.normalizer (pCoreOf 2 R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 R
  by_cases hN0 : pCoreOf 2 R = ⊥
  · refine Or.inr fun N hNR hNn hN2 => ?_
    have h := CFSG.LieType.BorelTits.le_pCoreOf 2 hNR hNn hN2
    rw [hN0, le_bot_iff] at h
    rw [h]
    exact inf_bot_eq _
  · obtain ⟨S₀, P, -, hNP, -, hUP, hSP⟩ :=
      hBT (pCoreOf 2 R) hN0 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R)
    have hRP : R ≤ P := hRn.trans hNP
    have hN0eq : pCoreOf 2 R = R ⊓ pCoreOf 2 P := by
      refine le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 R) hUP) ?_
      refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).to_le inf_le_right)
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      exact (le_inf Subgroup.le_normalizer
        (hRP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
    obtain ⟨c, hc⟩ : ∃ c : G, A1b.conjSub c U = (S₀ : Subgroup G) := by
      obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj (S := U) (T := (S₀ : Subgroup G))
        hU (isSylowIn_top S₀)
      refine ⟨c, ?_⟩
      ext x
      rw [hc, A1b.mem_conjSub_iff, B6.mem_conjSub]
    have hBM : B ≤ A1b.conjSub c⁻¹ P := by
      intro b hb
      rw [mem_conjSub_inv_iff]
      refine hSP ?_
      rw [← A1b.conjSub_eq_iff_mem_normalizer, ← hc]
      have hbU : A1b.conjSub b U = U := A1b.conjSub_eq_iff_mem_normalizer.mpr (hBU hb)
      calc A1b.conjSub (c * b * c⁻¹) (A1b.conjSub c U)
          = A1b.conjSub c (A1b.conjSub b (A1b.conjSub (c⁻¹ * c) U)) := by
            simp only [A1b.conjSub_mul, mul_assoc]
        _ = A1b.conjSub c U := by simp [hbU, A1b.conjSub_one]
    obtain ⟨b, hbB, A₁, hA₁, hcA⟩ := hpos c
    have hO : pCoreOf 2 (A1b.conjSub c⁻¹ P) = A1b.conjSub c⁻¹ (pCoreOf 2 P) :=
      CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj c⁻¹) P
    have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 (A1b.conjSub c⁻¹ P) : Set G) :=
      hHB.trans (hBM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    have hbO : A1b.conjSub b (pCoreOf 2 (A1b.conjSub c⁻¹ P)) = pCoreOf 2 (A1b.conjSub c⁻¹ P) :=
      A1b.conjSub_eq_iff_mem_normalizer.mpr
        ((hBM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) hbB)
    have hdich : A ⊓ pCoreOf 2 P = ⊥ ∨ A ≤ pCoreOf 2 P := by
      rcases hA₁ _ hHO with h0 | h0
      · left
        rw [← A1b.conjSub_inj c⁻¹, conjSub_inf, conjSub_bot, hcA, ← hO, ← hbO, ← conjSub_inf, h0,
          conjSub_bot]
      · right
        rw [← A1b.conjSub_le_conjSub_iff c⁻¹, hcA, ← hO]
        calc A1b.conjSub b A₁ ≤ A1b.conjSub b (pCoreOf 2 (A1b.conjSub c⁻¹ P)) :=
              A1b.conjSub_mono b h0
          _ = pCoreOf 2 (A1b.conjSub c⁻¹ P) := hbO
    rcases hdich with h | h
    · refine Or.inr fun N hNR hNn hN2 => ?_
      have hN : N ≤ pCoreOf 2 R := CFSG.LieType.BorelTits.le_pCoreOf 2 hNR hNn hN2
      rw [hN0eq] at hN
      refine eq_bot_iff.mpr ?_
      rw [← h]
      exact inf_le_inf_left _ (hN.trans inf_le_right)
    · refine Or.inl ⟨pCoreOf 2 R, CFSG.LieType.BorelTits.pCoreOf_le 2 R, ?_,
        CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R, ?_⟩
      · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 R)]
        exact hRn
      · rw [hN0eq]
        exact le_inf hAR h


theorem normalTwo_of_BT_bruhat [Fact (Nat.Prime 2)] (hBT : CFSG.LieType.BorelTits.Holds G 2)
    {U B H A : Subgroup G} (hU : IsSylowIn 2 U ⊤) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hHB : H ≤ B) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hbruhat : ∀ g : G, ∃ b₁ ∈ B, ∃ n : G, (∀ h ∈ H, n * h * n⁻¹ ∈ H) ∧
      ∃ b₂ ∈ B, g = b₁ * n * b₂)
    (hdich : ∀ O : Subgroup G, H ≤ Subgroup.normalizer (O : Set G) → A ⊓ O = ⊥ ∨ A ≤ O) :
    ∀ R : Subgroup G, A ≤ R → NormalTwoDichotomy A R := by
  refine normalTwo_of_BT hBT hU hBU hHB fun c => ?_
  obtain ⟨b₁, hb₁, n, hn, b₂, hb₂, hcg⟩ := hbruhat c⁻¹
  refine ⟨b₁, hb₁, A1b.conjSub n A, fun O hO => ?_, ?_⟩
  ·
    have hO' : H ≤ Subgroup.normalizer ((A1b.conjSub n⁻¹ O : Subgroup G) : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [A1b.mem_conjSub_iff, A1b.mem_conjSub_iff]
      have hh' := (Subgroup.mem_normalizer_iff.mp (hO (hn h hh)) (n * x * n⁻¹))
      have e : (n⁻¹)⁻¹ * (h * x * h⁻¹) * n⁻¹ = (n * h * n⁻¹) * (n * x * n⁻¹) * (n * h * n⁻¹)⁻¹ := by
        simp only [inv_inv, mul_inv_rev]
        group
      rw [e]
      simpa [inv_inv] using hh'
    rcases hdich _ hO' with h | h
    · left
      have := congrArg (A1b.conjSub n) h
      rw [conjSub_inf, ← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one, conjSub_bot] at this
      exact this
    · right
      have := A1b.conjSub_mono n h
      rwa [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one] at this
  · rw [hcg, A1b.conjSub_mul, A1b.conjSub_mul,
      A1b.conjSub_eq_iff_mem_normalizer.mpr (hBA hb₂)]

theorem subgroupOf_le_normalizer_of_forward {M : Type} [Group M] {Γ B Y : Subgroup M}
    (h : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) :
    B.subgroupOf Γ ≤ Subgroup.normalizer ((Y.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hb' : (b : M) ∈ B := hb
  have hbinv : (b : M)⁻¹ ∈ B := B.inv_mem hb'
  constructor
  · intro hy
    have hy' : (y : M) ∈ Y := hy
    have := h _ hb' _ hy'
    exact this
  · intro hy
    have hy' : ((b * y * b⁻¹ : ↥Γ) : M) ∈ Y := hy
    have := h _ hbinv _ hy'
    exact Subgroup.mem_subgroupOf.mpr (by simpa [mul_assoc] using this)

theorem dichotomy_subgroupOf {M : Type} [Group M] {Γ T Y : Subgroup M} (hT : T ≤ Γ) (hY : Y ≤ Γ)
    (h : ∀ O' : Subgroup M, (∀ t ∈ T, ∀ z ∈ O', t * z * t⁻¹ ∈ O') → Y ⊓ O' = ⊥ ∨ Y ≤ O') :
    ∀ O : Subgroup ↥Γ, T.subgroupOf Γ ≤ Subgroup.normalizer (O : Set ↥Γ) →
      Y.subgroupOf Γ ⊓ O = ⊥ ∨ Y.subgroupOf Γ ≤ O := by
  intro O hO
  have hO' : ∀ t ∈ T, ∀ z ∈ O.map Γ.subtype, t * z * t⁻¹ ∈ O.map Γ.subtype := by
    intro t ht z hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hmem : (⟨t, hT ht⟩ : ↥Γ) ∈ Subgroup.normalizer (O : Set ↥Γ) :=
      hO (by simpa [Subgroup.mem_subgroupOf] using ht)
    have := (Subgroup.mem_normalizer_iff.mp hmem z').mp hz'
    exact ⟨_, this, by simp⟩
  rcases h _ hO' with h0 | h0
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx1 : (x : M) ∈ Y ⊓ O.map Γ.subtype := ⟨hx.1, ⟨x, hx.2, rfl⟩⟩
    rw [h0, Subgroup.mem_bot] at hx1
    exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
  · right
    intro x hx
    obtain ⟨y, hy, hyx⟩ := h0 hx
    have : y = x := Subtype.ext hyx
    rwa [← this]

end CFSG.Quasithin.RonanE114
