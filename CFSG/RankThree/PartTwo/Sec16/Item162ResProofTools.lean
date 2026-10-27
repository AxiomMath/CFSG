module

public import CFSG.RankThree.PartTwo.Sec16.Item162ResProofCent
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofA10
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec4.Steps434
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res162

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_theta_of_cover {Y La : Subgroup G}
    (hcov : La = (Y ⊓ La) ⊔ CFSG.Open.pCoreOf 2 La) (l : ↥La)
    (hl : (l : G) ∈ CFSG.Open.pCoreOf 2 Y) : l ∈ aschbacherSolvableCore 3 ↥La := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set P := CFSG.Open.pCoreOf 2 La with hPdef
  set T := O ⊓ La with hTdef
  set M := T ⊔ P with hMdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) La
  have hPLa : P ≤ La := CFSG.LieType.BorelTits.pCoreOf_le 2 La
  have hLaP : La ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 La
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := inf_le_right.trans hLaP
  have hM2 : IsPGroup 2 M := (hO2.to_le inf_le_left).to_sup_of_normal_right' hP2 hTP
  have hMLa : M ≤ La := sup_le inf_le_right hPLa
  have hKN : Y ⊓ La ≤ Subgroup.normalizer (M : Set G) :=
    Sec14.le_normalizer_sup
      (Late.le_normalizer_inf (inf_le_left.trans hYO) (inf_le_right.trans Subgroup.le_normalizer))
      (inf_le_right.trans hLaP)
  have hPN : P ≤ Subgroup.normalizer (M : Set G) := by
    intro p hp
    apply Sec14.mem_normalizer_of_map_conj_eq
    have hle : M.map (MulAut.conj p).toMonoidHom ≤ M := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (fun t ht => ?_) (fun q hq => ?_)
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have h1 : t * p⁻¹ * t⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp (hTP ht) _).mp (inv_mem hp)
        have h2 : p * (t * p⁻¹ * t⁻¹) ∈ P := mul_mem hp h1
        have e : p * t * p⁻¹ = (p * (t * p⁻¹ * t⁻¹)) * t := by group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left ht)
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_right (mul_mem (mul_mem hp hq) (inv_mem hp))
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj p).injective).ge
  have hLaN : La ≤ Subgroup.normalizer (M : Set G) := hcov.le.trans (sup_le hKN hPN)
  have hMn : (M.subgroupOf La).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMLa).mpr hLaN
  have hMp : IsPGroup 2 (M.subgroupOf La) := hM2.comap_subtype
  exact Sec4.le_aschbacherSolvableCore_of_isPGroup Nat.prime_two (by norm_num) hMn hMp
    (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ⟨hl, l.2⟩))

theorem exists_mem_inf_of_cover {Y La : Subgroup G}
    (hcov : La = (Y ⊓ La) ⊔ CFSG.Open.pCoreOf 2 La)
    (hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤
      Nat.card (↥La ⧸ aschbacherSolvableCore 3 ↥La)) :
    ∀ y ∈ Y, ∃ k ∈ Y ⊓ La, k⁻¹ * y ∈ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set P := CFSG.Open.pCoreOf 2 La with hPdef
  set K := Y ⊓ La with hKdef
  have hLaP : La ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 La
  have hPLa : P ≤ La := CFSG.LieType.BorelTits.pCoreOf_le 2 La
  set θ := aschbacherSolvableCore 3 ↥La with hθdef
  have hθ : ∀ l : ↥La, (l : G) ∈ O → l ∈ θ := mem_theta_of_cover hcov
  have hPθ : ∀ l : ↥La, (l : G) ∈ P → l ∈ θ := fun l hl =>
    Sec4.le_aschbacherSolvableCore_of_isPGroup Nat.prime_two (by norm_num) CFSG.pCore_normal
      CFSG.pCore_isPGroup ((Step163Alt.mem_pCore_two_iff l).mpr hl)
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := inf_le_right.trans hLaP
  have hmul : ∀ l ∈ La, ∃ k ∈ K, ∃ p ∈ P, l = k * p := by
    intro l hl
    have hl' : l ∈ ((K : Set G) * (P : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K P hKP, ← hcov]
      exact hl
    obtain ⟨k, hk, p, hp, rfl⟩ := Set.mem_mul.mp hl'
    exact ⟨k, hk, p, hp, rfl⟩
  have hKY : K ≤ Y := inf_le_left
  have hKLa : K ≤ La := inf_le_right
  set ρ₁ : ↥K →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hKY) with hρ₁
  set ρ₂ : ↥K →* ↥La ⧸ θ := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hKLa) with hρ₂
  have hker : ρ₁.ker ≤ ρ₂.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, hρ₁, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Step163Alt.mem_pCore_two_iff] at hk
    rw [MonoidHom.mem_ker, hρ₂, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hθ _ hk
  have hρ₂top : ρ₂.range = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ z
    obtain ⟨k, hk, p, hp, hlkp⟩ := hmul l l.2
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hρ₂, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hpl : (Subgroup.inclusion hKLa ⟨k, hk⟩)⁻¹ * l = ⟨p, hPLa hp⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [hlkp, inv_mul_cancel_left]
    rw [hpl]
    exact hPθ _ hp
  have hρ₁top : ρ₁.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Subgroup.card_le_card_group _)
    have h1 : Nat.card K = Nat.card ρ₁.range * Nat.card ρ₁.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ₁.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ₁).toEquiv]
    have h2 : Nat.card K = Nat.card ρ₂.range * Nat.card ρ₂.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ₂.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ₂).toEquiv]
    have h3 : Nat.card ρ₁.ker ≤ Nat.card ρ₂.ker := Subgroup.card_le_of_le hker
    have h4 : Nat.card ρ₂.range = Nat.card (↥La ⧸ θ) := by
      rw [hρ₂top, Subgroup.card_top]
    have hpos : 0 < Nat.card ρ₂.ker := Nat.card_pos
    have h5 : Nat.card (↥La ⧸ θ) ≤ Nat.card ρ₁.range := by
      by_contra hlt
      have := Nat.mul_lt_mul_of_lt_of_le (not_le.mp hlt) h3 hpos
      rw [← h4] at this
      omega
    exact hcard.trans h5
  intro y hy
  obtain ⟨k, hk⟩ : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hy⟩ ∈ ρ₁.range :=
    hρ₁top ▸ Subgroup.mem_top _
  exact ⟨k, k.2, (Step163Alt.mk_eq_mk_iff (Subgroup.inclusion hKY k) ⟨y, hy⟩).mp hk⟩

omit [Finite G] in
theorem eq_sup_of_forall_mem {Y La : Subgroup G}
    (h : ∀ y ∈ Y, ∃ k ∈ Y ⊓ La, k⁻¹ * y ∈ CFSG.Open.pCoreOf 2 Y) :
    Y = (Y ⊓ La) ⊔ CFSG.Open.pCoreOf 2 Y := by
  refine le_antisymm (fun y hy => ?_)
    (sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
  obtain ⟨k, hk, hko⟩ := h y hy
  have e : y = k * (k⁻¹ * y) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hko)

theorem sectionCentralizer_eq_zpowers_of_cover {A Y La : Subgroup G} {a : G}
    (hLa : La ∈ lA A a) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hcov : La = (Y ⊓ La) ⊔ CFSG.Open.pCoreOf 2 La)
    (hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤
      Nat.card (↥La ⧸ aschbacherSolvableCore 3 ↥La)) :
    Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) = (Subgroup.zpowers a : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set P := CFSG.Open.pCoreOf 2 La with hPdef
  set K := Y ⊓ La with hKdef
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hLaP : La ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 La
  have hPLa : P ≤ La := CFSG.LieType.BorelTits.pCoreOf_le 2 La
  have hLaC : La ≤ Subgroup.centralizer {a} := le_centralizer_of_mem_thetaComponentsAt hLa.1
  have hALa : A ≤ Subgroup.normalizer (La : Set G) := hLa.2.1
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    hALa.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 La)
  have hsc := hLa.2.2.1
  set θ := aschbacherSolvableCore 3 ↥La with hθdef
  have hθ : ∀ l : ↥La, (l : G) ∈ O → l ∈ θ := mem_theta_of_cover hcov
  have hPθ : ∀ l : ↥La, (l : G) ∈ P → l ∈ θ := fun l hl =>
    Sec4.le_aschbacherSolvableCore_of_isPGroup Nat.prime_two (by norm_num) CFSG.pCore_normal
      CFSG.pCore_isPGroup ((Step163Alt.mem_pCore_two_iff l).mpr hl)
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := inf_le_right.trans hLaP
  have hmul : ∀ l ∈ La, ∃ k ∈ K, ∃ p ∈ P, l = k * p := by
    intro l hl
    have hl' : l ∈ ((K : Set G) * (P : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K P hKP, ← hcov]
      exact hl
    obtain ⟨k, hk, p, hp, rfl⟩ := Set.mem_mul.mp hl'
    exact ⟨k, hk, p, hp, rfl⟩
  have hKY : K ≤ Y := inf_le_left
  have hKLa : K ≤ La := inf_le_right
  have hcover : ∀ y : ↥Y, ∃ k ∈ K, k⁻¹ * (y : G) ∈ O := fun y =>
    exists_mem_inf_of_cover hcov hcard y y.2
  ext t
  constructor
  · rintro ⟨htA, ht⟩
    have hmem : t ∈ Late.sectionCentralizer A La (θ.map La.subtype) := by
      refine ⟨htA, fun l hl => ?_⟩
      obtain ⟨k, hk, p, hp, rfl⟩ := hmul l hl
      have hkY : k ∈ Y := hKY hk
      have hkLa : k ∈ La := hKLa hk
      have h1La : t * k * t⁻¹ * k⁻¹ ∈ La :=
        La.mul_mem ((Subgroup.mem_normalizer_iff.mp (hALa htA) k).mp hkLa) (La.inv_mem hkLa)
      have h1O : t * k * t⁻¹ * k⁻¹ ∈ O := ht k hkY
      have h2P : t * p * t⁻¹ * p⁻¹ ∈ P :=
        P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAP htA) p).mp hp) (P.inv_mem hp)
      have h3P : k * (t * p * t⁻¹ * p⁻¹) * k⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hKP hk) _).mp h2P
      have e : t * (k * p) * t⁻¹ * (k * p)⁻¹ =
          (t * k * t⁻¹ * k⁻¹) * (k * (t * p * t⁻¹ * p⁻¹) * k⁻¹) := by group
      have h3La : k * (t * p * t⁻¹ * p⁻¹) * k⁻¹ ∈ La := hPLa h3P
      refine ⟨⟨_, La.mul_mem h1La h3La⟩, ?_, by rw [e]; rfl⟩
      have hθ1 : (⟨_, h1La⟩ : ↥La) ∈ θ := hθ _ h1O
      have hθ2 : (⟨_, h3La⟩ : ↥La) ∈ θ := hPθ _ h3P
      have hprod : (⟨_, La.mul_mem h1La h3La⟩ : ↥La) = ⟨_, h1La⟩ * ⟨_, h3La⟩ := rfl
      rw [hprod]
      exact θ.mul_mem hθ1 hθ2
    rw [hsc] at hmem
    exact hmem
  · intro ht
    have ht' : t ∈ Late.sectionCentralizer A La (θ.map La.subtype) := by
      rw [hsc]
      exact ht
    have htA : t ∈ A := ht'.1
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine ⟨htA, fun y hy => ?_⟩
    obtain ⟨k, hk, hko⟩ := hcover ⟨y, hy⟩
    set o := k⁻¹ * y with ho
    have hy' : y = k * o := by rw [ho, mul_inv_cancel_left]
    have htk : a ^ n * k = k * a ^ n :=
      ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp
        (hLaC (hKLa hk))).symm n)).eq
    have e : a ^ n * y * (a ^ n)⁻¹ * y⁻¹ = k * (a ^ n * o * (a ^ n)⁻¹ * o⁻¹) * k⁻¹ := by
      calc a ^ n * y * (a ^ n)⁻¹ * y⁻¹
          = (a ^ n * k) * o * (a ^ n)⁻¹ * o⁻¹ * k⁻¹ := by rw [hy']; group
        _ = (k * a ^ n) * o * (a ^ n)⁻¹ * o⁻¹ * k⁻¹ := by rw [htk]
        _ = k * (a ^ n * o * (a ^ n)⁻¹ * o⁻¹) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hYO (hKY hk)) _).mp
      (O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAO htA) o).mp hko) (O.inv_mem hko))

theorem mem_sectionCentralizer_of_meets {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {Y X : Subgroup G} {t : G} (htA : t ∈ A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) (hX : X ∈ scriptY4 A LB)
    (hXY : X ≤ Y) (hXt : X ≤ Subgroup.centralizer {t}) :
    t ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) :=
  ⟨htA, commutator_mem_of_le_centralizer (hAY htA) (hA.2 t htA) φ hXY hXt
    (Proof162.not_isSolvable_of_mem_scriptY4 hX)⟩

theorem zpowers_eq_of_mem_zpowers {A : Subgroup G} {c e : G}
    (hc : Subgroup.zpowers c ∈ omegaA A) (he : Subgroup.zpowers e ∈ omegaA A)
    (hec : e ∈ Subgroup.zpowers c) : Subgroup.zpowers e = Subgroup.zpowers c :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hec)
    (by rw [(zpowers_mem_omegaA_iff.mp hc).2.1, (zpowers_mem_omegaA_iff.mp he).2.1])

theorem meetsY4_of_alternating_ten {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (hΩ3 : (omegaA A).ncard = 3) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
    {e : G} {Le : Subgroup G} (he : Subgroup.zpowers e ∈ omegaA A) (hLe : Le ∈ lA A e)
    (hm : MeetsY4 A (lB A) Le Y) : MeetsY4 A (lB A) L Y := by
  have hD := h.toSec13Data
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B →
      B = E := fun E hE B hB hEB => (hFE ▸ hE : E ∈ partTwoF G).2.1 B hB hEB
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hO : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  have hAleY : A ≤ Y := Step163Alt.le_of_alternating_ten hmax hD.isElemAbelian hAY hO φ
  obtain ⟨y, hy, hcy⟩ := Step163Alt.omega_transitive_of_ten hD.isElemAbelian hD.card_eq hAleY φ
    hΩ3 _ he _ h.zpowers_mem_omegaA
  have hyW : y ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hy).2
  have hLy : Le.map (MulAut.conj y).toMonoidHom = L := map_conj_eq_of_zpowers h he hLe hyW hcy
  have hYy : Y.map (MulAut.conj y).toMonoidHom = Y :=
    Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (Subgroup.mem_inf.mp hy).1)
  obtain ⟨X, hX, hXLY⟩ := hm
  refine ⟨X.map (MulAut.conj y).toMonoidHom, map_conj_mem_scriptY4 hyW hX, ?_⟩
  rw [← hLy, ← hYy, ← Subgroup.map_inf _ _ _ (MulAut.conj y).injective]
  exact Subgroup.map_mono hXLY

end CFSG.RankThree.PartTwo.Sec16.Res162
