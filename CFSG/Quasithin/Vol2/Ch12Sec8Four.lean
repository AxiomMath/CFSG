module

public import CFSG.Quasithin.Vol2.Ch12Sec8Basic
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mul_of_odd_orderOf {Y T : Subgroup G}
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hT : IsPGroup 2 T) {t y : G} (ht : t ∈ T)
    (hy : y ∈ Y) (hodd : Odd (orderOf (t * y))) : t ∈ Y := by
  have hpow : ∀ k : ℕ, (t ^ k)⁻¹ * (t * y) ^ k ∈ Y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : (t ^ (k + 1))⁻¹ * (t * y) ^ (k + 1) =
          t⁻¹ * ((t ^ k)⁻¹ * (t * y) ^ k) * t⁻¹⁻¹ * y := by
        rw [pow_succ, pow_succ, mul_inv_rev, inv_inv]
        simp only [mul_assoc]
      rw [e]
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTY (T.inv_mem ht)) _).mp ih) hy
  have htm : t ^ orderOf (t * y) ∈ Y := by
    have := hpow (orderOf (t * y))
    rw [pow_orderOf_eq_one, mul_one] at this
    simpa using Y.inv_mem this
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf (t * y)) (orderOf t) :=
    Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))
  exact Subgroup.zpowers_le_of_mem htm (A4.mem_zpowers_pow_of_coprime hcop)

variable {T M L : Subgroup G}

namespace Hyp1281Two

theorem mem_centralizer_of_odd (h : Hyp1281Two G T M L) {x : G}
    (hxV : x ∈ Subgroup.normalizer (VZ T M : Set G))
    (hxZ : x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  have hZ2 := h.card_omegaOneCenter
  have hxC : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    normalizer_le_centralizer_of_card_two hZ2 hxZ
  obtain ⟨z, hzZ⟩ : ∃ z : quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h.omegaOneCenter_ne_bot (by
      rw [eq_bot_iff]
      intro w hw
      have := hall ⟨w, hw⟩
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this)
  have hzV : (z : G) ∈ VZ T M := le_conjClosure _ _ z.2
  set σ : MulAut (VZ T M) := conjAct (VZ T M) ⟨x, hxV⟩ with hσ
  have hσapp : ∀ v : VZ T M, ((σ v : VZ T M) : G) = x * v * x⁻¹ := fun v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (VZ T M) (Subgroup.inclusion le_rfl ⟨x, hxV⟩) v
  have hσz : σ ⟨z, hzV⟩ = ⟨z, hzV⟩ := by
    apply Subtype.ext
    rw [hσapp]
    show x * (z : G) * x⁻¹ = z
    have := (Subgroup.mem_centralizer_iff.mp hxC) z z.2
    rw [← this, mul_inv_cancel_right]
  have hσm : σ ^ orderOf x = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨x, hxV⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ orderOf x = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have hsq : ∀ v : VZ T M, v * v = 1 := fun v =>
    Subtype.ext (by simpa [sq] using hVred.2.2.1.2 v v.2)
  have hσ1 := mulAut_eq_one_of_fix_of_odd h.rank_two hsq (z := ⟨z, hzV⟩)
    (fun h1 => hzZ (Subtype.ext (show (z : G) = 1 from congrArg (fun w : VZ T M => (w : G)) h1)))
    hσz hodd hσm
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := congrArg (fun φ : MulAut (VZ T M) => ((φ ⟨v, hv⟩ : VZ T M) : G)) hσ1
  simp only [hσapp, MulAut.one_apply] at this
  calc v * x = (x * v * x⁻¹) * x := by rw [this]
    _ = x * v := by group

theorem normalizer_VZ (h : Hyp1281Two G T M L) :
    Subgroup.normalizer (VZ T M : Set G) = M := by
  obtain ⟨hVred, hVT⟩ := h.isTwoReducedIn
  have hVne : VZ T M ≠ ⊥ := by
    intro hV
    have h4 := h.rank_two
    rw [hV, Subgroup.card_bot] at h4
    omega
  exact h.inM.1.2 _ ⟨_, hVne, h.sylow.1.to_le hVT, rfl⟩ hVred.2.1

theorem lemma_12_8_4_four (h : Hyp1281Two G T M L) {H : Subgroup G} (hH : IsHz T M L H) :
    centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) = pCoreOf 2 H := by
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := VZ T M with hVdef
  set C := centralizerMod Z H (conjClosure V H) with hCdef
  have hA := h.almostSpecialHyp hH
  have hHz := (h.isHz_iff).mp hH
  have hHN : H ≤ Subgroup.normalizer (Z : Set G) := hHz.2.1
  have hTH : T ≤ H := hHz.1.1
  have hZV : Z ≤ V := le_conjClosure _ _
  have hCH : C ≤ H := centralizerMod_le_left _ _ _
  have hHC : H ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerMod hHN Subgroup.le_normalizer (le_normalizer_conjClosure V H)
  apply le_antisymm
  ·
    have hC2 : IsPGroup 2 C := by
      refine isPGroup_two_of_odd_orderOf_eq_one fun x hx hodd => ?_
      by_contra hx1
      set Y := oTwoUpper C with hYdef
      have hCV : C ≤ Subgroup.normalizer (V : Set G) := by
        refine le_normalizer_of_conj_mem fun c hc v hv => ?_
        have h1 : c * v * c⁻¹ * v⁻¹ ∈ V := hZV (hc.2.2 v (le_conjClosure V H hv))
        have e : c * v * c⁻¹ = (c * v * c⁻¹ * v⁻¹) * v := by group
        rw [e]
        exact V.mul_mem h1 hv
      have hgen : ∀ g ∈ C, Odd (orderOf g) → g ∈ Subgroup.centralizer (V : Set G) := fun g hg ho =>
        h.mem_centralizer_of_odd (hCV hg) (centralizerMod_le_normalizer _ _ _ hg) ho
      have hgenM : ∀ g ∈ C, Odd (orderOf g) → g ∈ M := fun g hg ho => by
        rw [← h.normalizer_VZ]
        exact Subgroup.centralizer_le_normalizer _ (hgen g hg ho)
      have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
        hHC.trans (normalizer_le_normalizer_oTwoUpper C)
      have hT2 : IsPGroup 2 T := h.sylow.1
      have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hA.sylow_LT
      have hconjgen : ∀ l ∈ L, ∀ g ∈ C, Odd (orderOf g) → l * g * l⁻¹ ∈ Y := by
        intro l hl g hg ho
        have hgM := hgenM g hg ho
        have hgCV := hgen g hg ho
        have hlM : l ∈ M := h.le hl
        have hlNV : l ∈ Subgroup.normalizer (V : Set G) := by
          rw [h.normalizer_VZ]
          exact hlM
        set w := l * g * l⁻¹ * g⁻¹ with hw
        have hwL : w ∈ L := by
          have : g * l⁻¹ * g⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.mp (h.normal hgM) _).mp (L.inv_mem hl)
          have e : w = l * (g * l⁻¹ * g⁻¹) := by rw [hw]; group
          rw [e]
          exact L.mul_mem hl this
        have hwC : w ∈ Subgroup.centralizer (V : Set G) := by
          have h1 : l * g * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro v hv
            have hv' : l⁻¹ * v * l ∈ V := by
              have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlNV) v).mp hv
              simpa using this
            have hc := (Subgroup.mem_centralizer_iff.mp hgCV) _ hv'
            calc v * (l * g * l⁻¹) = l * ((l⁻¹ * v * l) * g) * l⁻¹ := by group
              _ = l * (g * (l⁻¹ * v * l)) * l⁻¹ := by rw [hc]
              _ = l * g * l⁻¹ * v := by group
          exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hgCV)
        have hwT : w ∈ T := hOT (by
          rw [← h.centralizer]
          exact ⟨Subgroup.mem_sup_left hwL, hwC⟩)
        have hgY : g ∈ Y := mem_oTwoUpper_of_odd hg ho
        have hodd' : Odd (orderOf (w * g)) := by
          have e : w * g = l * g * l⁻¹ := by rw [hw]; group
          rw [e, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
          exact ho
        have hwY : w ∈ Y := mem_of_mul_of_odd_orderOf (hTH.trans hHY) hT2 hwT hgY hodd'
        have e : l * g * l⁻¹ = w * g := by rw [hw]; group
        rw [e]
        exact Y.mul_mem hwY hgY
      have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
        refine le_normalizer_of_conj_mem fun l hl y hy => ?_
        induction hy using Subgroup.closure_induction with
        | mem g hg => exact hconjgen l hl g hg.1 hg.2
        | one => simp
        | mul a b _ _ iha ihb =>
          have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
          rw [e]
          exact Y.mul_mem iha ihb
        | inv a _ iha =>
          have e : l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ := by group
          rw [e]
          exact Y.inv_mem iha
      have hYH : Y ≤ H := (oTwoUpper_le C).trans hCH
      have hYchar : CharTwo Y :=
        CharTwo.of_normal hA.charTwo hYH (Subgroup.normal_subgroupOf_of_le_normalizer hHY)
      have hYne : Y ≠ ⊥ := by
        intro hY
        apply hx1
        have : x ∈ Y := mem_oTwoUpper_of_odd hx hodd
        rw [hY, Subgroup.mem_bot] at this
        exact this
      have hOY : pCoreOf 2 Y ≠ ⊥ := pCoreOf_ne_bot_of_charTwo hYchar hYne
      have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)) :=
        ⟨pCoreOf 2 Y, hOY, pCoreOf_isPGroup 2 Y, rfl⟩
      have hNY : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
        normalizer_le_normalizer_pCoreOf 2 Y
      obtain ⟨N, hNmax, hNle⟩ := exists_maxTwoLocal_ge hloc
      have hLTN : L ⊔ T ≤ N :=
        (sup_le (hLY.trans hNY) (hTH.trans (hHY.trans hNY))).trans hNle
      have hNM : N = M := h.unique.2 N ⟨hNmax, hLTN⟩
      exact hHz.2.2 (hNM ▸ (hHY.trans hNY).trans hNle)
    exact le_pCoreOf_of_le_normalizer 2 hCH hHC hC2
  ·
    intro q hq
    have hqH : q ∈ H := pCoreOf_le 2 H hq
    have hqN : q ∈ Subgroup.normalizer (Z : Set G) := hHN hqH
    refine ⟨hqH, hqN, fun u hu => ?_⟩
    have hcc := hA.conjClosure_le_N
    have hmemY : tmk Z ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf Z (pCoreOf 2 H)) :=
      (secImg_le_iff.1 hA.G22_one.2) ⟨u, hcc hu⟩ hu
    have hqQ : tmk Z ⟨q, hqN⟩ ∈ tildeOf Z (pCoreOf 2 H) := secMk_mem_secImg hq
    exact commutator_mem_of_secMk_commute (mem_centralizer_of_mem_omegaOneCenterOf hmemY hqQ)

end Hyp1281Two

end CFSG.Quasithin
