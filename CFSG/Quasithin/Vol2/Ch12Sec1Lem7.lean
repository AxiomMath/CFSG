module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec1H91

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

namespace Sec1217

variable {G : Type} [Group G]

omit [Group G] in
theorem pow_padicValNat_of_dvd {k e : ℕ} (hk : k ∣ 2 ^ e) : 2 ^ padicValNat 2 k = k := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk
  rw [padicValNat.prime_pow]

theorem conjSubgroup_eq_conjugate (V : Subgroup G) (g : G) :
    conjSubgroup V g = CFSG.conjugate V g := by
  ext x
  rw [mem_conjSubgroup_iff]
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro h
    exact ⟨g * x * g⁻¹, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy

variable [Finite G]

theorem exists_conj_of_not_wClos_le {T V : Subgroup G} (hV2 : IsPGroup 2 ↥V)
    (h : ¬ wClos V 0 T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    ∃ g : G, conjSubgroup V g ≤ T ∧ ¬ conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  apply h
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  have hVg2 : IsPGroup 2 ↥(conjSubgroup V g) := hV2.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨e, he⟩ := hVg2.exists_card_eq
  have hdvd : A.relIndex (conjSubgroup V g) ∣ 2 ^ e := by
    rw [← he]
    exact Subgroup.relIndex_dvd_card _ _
  have h1 : A.relIndex (conjSubgroup V g) = 1 := by
    rw [← pow_padicValNat_of_dvd hdvd]
    rw [mQuot] at hm
    rw [hm, pow_zero]
  have hgA : conjSubgroup V g ≤ A := Subgroup.relIndex_eq_one.mp h1
  have hA : A = conjSubgroup V g := le_antisymm hAg hgA
  subst hA
  exact le_inf hAT (hcon g hAT)

omit [Finite G] in
theorem card_conj1217 (V : Subgroup G) (g : G) : Nat.card (conjSubgroup V g) = Nat.card V :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective

omit [Finite G] in
theorem conjSubgroup_le_normalizer {X Y : Subgroup G} (h : X ≤ Subgroup.normalizer (Y : Set G))
    (g : G) : conjSubgroup X g ≤ Subgroup.normalizer (conjSubgroup Y g : Set G) := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  have h1 := Subgroup.mem_normalizer_iff.mp (h hx) (g * y * g⁻¹)
  have e : g * (x * y * x⁻¹) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
  rw [e]
  exact h1

omit [Finite G] in
theorem card_conj_inf_centralizer (X Y : Subgroup G) (g : G) :
    Nat.card ↥(conjSubgroup X g ⊓ Subgroup.centralizer (conjSubgroup Y g : Set G)) =
      Nat.card ↥(X ⊓ Subgroup.centralizer (Y : Set G)) := by
  have key : ∀ x : G, x ∈ conjSubgroup X g ⊓ Subgroup.centralizer (conjSubgroup Y g : Set G) ↔
      g * x * g⁻¹ ∈ X ⊓ Subgroup.centralizer (Y : Set G) := by
    intro x
    simp only [Subgroup.mem_inf, mem_conjSubgroup_iff, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe]
    refine and_congr Iff.rfl ⟨fun h y hy => ?_, fun h y hy => ?_⟩
    · have h1 := h (g⁻¹ * y * g) (by simpa [mul_assoc] using hy)
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * y := by group
    · have h1 := h _ hy
      calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
        _ = x * y := by group
  exact Nat.card_congr
    { toFun := fun x => ⟨g * x * g⁻¹, (key x).mp x.2⟩
      invFun := fun y => ⟨g⁻¹ * y * g, (key _).mpr (by simp [mul_assoc])⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }

omit [Finite G] in
theorem map_conj_autI {V A : Subgroup G} (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) :
    (autI hV A).map (MulAut.conj (convI hV ⟨m, hm⟩)⁻¹).toMonoidHom =
      autI hV (conjSubgroup A m) := by
  ext φ
  rw [Subgroup.mem_map, mem_autI]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨⟨a, haN⟩, haA, rfl⟩ := (mem_autI hV).1 hψ
    refine ⟨⟨m⁻¹ * a * m, (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem (Subgroup.inv_mem _ hm) haN) hm⟩, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using haA
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
  · rintro ⟨⟨x, hxN⟩, hxA, rfl⟩
    rw [mem_conjSubgroup_iff] at hxA
    refine ⟨convI hV ⟨m * x * m⁻¹, (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem hm hxN) (Subgroup.inv_mem _ hm)⟩,
      (mem_autI hV).2 ⟨_, hxA, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem gammaCheck_mono {W : Type} [CommGroup W] {k k' : ℕ} (h : k ≤ k')
    (P : Subgroup (MulAut W)) : gammaCheck k P ≤ gammaCheck k' P := by
  unfold gammaCheck
  exact iSup₂_le fun X hX => iSup_le fun hXk =>
    le_iSup₂_of_le (f := fun X (_ : X ≤ P) => ⨆ (_ : mQuot P X ≤ k'), fixV X) X hX
      (le_iSup_of_le (hXk.trans h) le_rfl)

theorem fixV_le_gammaCheck {W : Type} [CommGroup W] {k : ℕ} {P X : Subgroup (MulAut W)}
    (hX : X ≤ P) (hXk : mQuot P X ≤ k) : fixV X ≤ gammaCheck k P := by
  unfold gammaCheck
  exact le_iSup₂_of_le (f := fun X (_ : X ≤ P) => ⨆ (_ : mQuot P X ≤ k), fixV X) X hX
    (le_iSup_of_le hXk le_rfl)

end Sec1217

open Sec1217 Sec121H9 in
theorem lem1217_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1211 : Lem1211) (hH91 : LemH91)
    (h1213 : Lem1213) (h1216 : Lem1216) (hH93 : LemH93Use) (hRk : LemH9Rank4) (hFF : LemH9FF4) :
    Lem1217 := by
  intro G _ _ T L V V₁ V₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hW
  rcases hyp.rank with hn | hn
  swap
  · exact hW (h1213 G T L V V₁ V₂ n hyp hn)
  subst hn
  obtain ⟨hTL, hNV⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hV := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hcV : IsMulCommutative ↥V := hV.1
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := hNV.ge
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hH9 := h9Hyp_of_hyp121 hyp hTL hV
  obtain ⟨β, hβ, -⟩ := (hH91 G T L V V₁ V₂ 4 hyp hTL).2
  have hr : ((4 : ℕ) : ℕ∞) ≤ rParam V :=
    (((lem1212_of h1001 h331 h1211) G T L V V₁ V₂ 4 β hyp hβ).2 hV).1
  obtain ⟨g, hgT, hgC⟩ := exists_conj_of_not_wClos_le hV2 hW
  set A := conjSubgroup V g with hA
  have hAM : A ≤ Subgroup.normalizer (L : Set G) := hgT.trans hTL
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hAe : IsElemAbelian 2 A := isElemAbelian_conjSubgroup hV g
  have hA1 : autI hV A ≠ ⊥ := fun h => hgC ((autI_eq_bot_iff hV hAN).mp h)
  have hcardA : Nat.card A = Nat.card V := card_conj1217 V g
  have h1216' : ∀ h : G, V₁ ⊓ conjSubgroup V h ≠ ⊥ → ⁅V, conjSubgroup V h⁆ = ⊥ := fun h hne => by
    rw [conjSubgroup_eq_conjugate] at hne ⊢
    exact (h1216 G T L V V₁ V₂ 4 hyp).2 h hne
  have hnontriv : ∀ {B : Subgroup G}, B ≤ Subgroup.normalizer (V : Set G) →
      autI hV B ≤ autI hV L → autI hV B ≠ ⊥ →
        ∃ b ∈ B, ∃ a ∈ V₁, b * a * b⁻¹ ≠ a := by
    intro B hBN hBL hB1
    by_contra hcon
    push Not at hcon
    apply hB1
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨⟨b, hbN⟩, hbB, rfl⟩ := (mem_autI hV).1 hφ
    rw [Subgroup.mem_bot]
    refine hH9.faith _ (hBL hφ) fun w hw => IntMod.val_injective ?_
    rw [convI_apply_val]
    exact hcon b hbB _ hw
  have hcommV₁ : ∀ {B : Subgroup G}, ∀ b ∈ B, b ∈ Subgroup.normalizer (V₁ : Set G) →
      ∀ a ∈ V₁, a ∈ Subgroup.normalizer (B : Set G) → b * a * b⁻¹ * a⁻¹ ∈ V₁ ⊓ B := by
    intro B b hb hbN a ha haB
    refine ⟨V₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hbN a).mp ha) (V₁.inv_mem ha), ?_⟩
    have h1 : a * b⁻¹ * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp haB b⁻¹).mp (B.inv_mem hb)
    have e : b * a * b⁻¹ * a⁻¹ = b * (a * b⁻¹ * a⁻¹) := by group
    rw [e]
    exact B.mul_mem hb h1
  have hLnorm : ∀ {b : G} (hbN : b ∈ Subgroup.normalizer (V : Set G)),
      convI hV ⟨b, hbN⟩ ∈ autI hV L → b ∈ Subgroup.normalizer (V₁ : Set G) := by
    intro b hbN hbL
    refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 := hH9.inv₁ hbL (IntMod.mk hV ⟨a, hV₁V ha⟩)
    rw [mem_subI, mem_subI, convI_apply_val] at h1
    exact h1.mp ha
  by_cases hVA : V ≤ Subgroup.normalizer (A : Set G)
  ·
    have key : ∀ (h : G), conjSubgroup V h ≤ Subgroup.normalizer (L : Set G) →
        V ≤ Subgroup.normalizer (conjSubgroup V h : Set G) →
        autI hV (conjSubgroup V h) ≠ ⊥ →
        Nat.card V ≤ Nat.card (autI hV (conjSubgroup V h)) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (conjSubgroup V h : Set G)) → False := by
      intro h hBM hVB hB1 hFFc
      have hBN : conjSubgroup V h ≤ Subgroup.normalizer (V : Set G) := hBM.trans hMV
      have hBL := hFF _ _ _ _ _ _ hH9 (autI hV (conjSubgroup V h)) (autI_mono hV hBM)
        (isElemAbelian2_autI hV (isElemAbelian_conjSubgroup hV h) hBN) hB1
        (by rw [card_fixV_autI hV hBN]; exact hFFc)
      obtain ⟨b, hb, a, ha, hba⟩ := hnontriv hBN hBL hB1
      have hbV₁ := hLnorm (hBN hb) (hBL ((mem_autI hV).2 ⟨⟨b, hBN hb⟩, hb, rfl⟩))
      have hmem := hcommV₁ b hb hbV₁ a ha (hVB (hV₁V ha))
      have hne : V₁ ⊓ conjSubgroup V h ≠ ⊥ := by
        intro h0
        rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at hmem
        exact hba hmem
      apply hB1
      rw [autI_eq_bot_iff hV hBN, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.commutator_comm]
      exact h1216' h hne
    set A' := conjSubgroup V g⁻¹ with hA'
    have hVA' : conjSubgroup A g⁻¹ = V := by
      rw [hA, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    have hA'N : A' ≤ Subgroup.normalizer (V : Set G) := by
      have h1 := conjSubgroup_le_normalizer hVA g⁻¹
      rw [hVA'] at h1
      exact h1
    have hVA'' : V ≤ Subgroup.normalizer (A' : Set G) := by
      have h1 := conjSubgroup_le_normalizer hAN g⁻¹
      rw [hVA'] at h1
      exact h1
    have hA'M : A' ≤ Subgroup.normalizer (L : Set G) := hA'N.trans hNV.le
    have hcardA' : Nat.card A' = Nat.card V := card_conj1217 V g⁻¹
    have h1 := card_autI_mul_card_inf hV hAN
    have h2 := card_autI_mul_card_inf hV hA'N
    have hb : Nat.card ↥(A' ⊓ Subgroup.centralizer (V : Set G)) =
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
      have h3 := card_conj_inf_centralizer V A g⁻¹
      rw [hVA'] at h3
      exact h3
    have ha : Nat.card ↥(V ⊓ Subgroup.centralizer (A' : Set G)) =
        Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
      have h3 := card_conj_inf_centralizer A V g⁻¹
      rw [hVA'] at h3
      exact h3
    have hA'1 : autI hV A' ≠ ⊥ := by
      intro h0
      rw [autI_eq_bot_iff hV hA'N] at h0
      apply hA1
      rw [autI_eq_bot_iff hV hAN]
      have h3 : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = Nat.card V := by
        rw [← hb, inf_eq_left.mpr h0, hcardA']
      have h4 : V ⊓ Subgroup.centralizer (A : Set G) = V :=
        Subgroup.eq_of_le_of_card_ge inf_le_left h3.ge
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h5 : v ∈ V ⊓ Subgroup.centralizer (A : Set G) := by rw [h4]; exact hv
      exact ((Subgroup.mem_centralizer_iff.mp h5.2) x hx).symm
    rcases le_total (Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)))
        (Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) with hle | hle
    · refine key g hAM hVA hA1 ?_
      calc Nat.card V = Nat.card A := hcardA.symm
        _ = Nat.card (autI hV A) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := h1.symm
        _ ≤ Nat.card (autI hV A) * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
          Nat.mul_le_mul_left _ hle
    · refine key g⁻¹ hA'M hVA'' hA'1 ?_
      calc Nat.card V = Nat.card A' := hcardA'.symm
        _ = Nat.card (autI hV A') * Nat.card ↥(A' ⊓ Subgroup.centralizer (V : Set G)) := h2.symm
        _ = Nat.card (autI hV A') * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
          rw [hb]
        _ ≤ Nat.card (autI hV A') * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
          Nat.mul_le_mul_left _ hle
        _ = Nat.card (autI hV A') * Nat.card ↥(V ⊓ Subgroup.centralizer (A' : Set G)) := by
          rw [ha]
  ·
    have hrA := e3_4_two hVA
    rw [← hA] at hrA
    have hA2 : IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
    have hcardĀ : Nat.card (autI hV A) = 2 ^ 4 := by
      refine le_antisymm (hRk _ _ _ _ _ _ hH9 _ (autI_mono hV hAM)
        (isElemAbelian2_autI hV hAe hAN)) ?_
      rw [card_autI_eq hV hAN, relIndex_eq_two_pow hA2]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have h3 := hr.trans hrA
      exact_mod_cast h3
    obtain ⟨A₀, A₁, A₂, hAi, hconj, ⟨-, hA₀⟩, -, -, h7⟩ := hH93 _ _ _ _ _ _ hH9
    obtain ⟨mb, hmbM, hmb⟩ := hconj (autI hV A) (autI_mono hV hAM)
      (isElemAbelian2_autI hV hAe hAN) hcardĀ
    obtain ⟨⟨m, hmN⟩, hmM, rfl⟩ := (mem_autI hV).1 hmbM
    obtain ⟨As, hAsV⟩ : ∃ As : Subgroup G, As = conjSubgroup V (g * m) := ⟨_, rfl⟩
    have hAsA : As = conjSubgroup A m := by rw [hAsV, hA, conjSubgroup_conjSubgroup]
    have hAsM : As ≤ Subgroup.normalizer (L : Set G) := by
      rw [hAsA]
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have h1 := (Subgroup.normalizer (L : Set G)).mul_mem
        ((Subgroup.normalizer (L : Set G)).mul_mem (Subgroup.inv_mem _ hmM) (hAM hx)) hmM
      simpa [mul_assoc] using h1
    have hAsN : As ≤ Subgroup.normalizer (V : Set G) := hAsM.trans hMV
    have hĀs : autI hV As = A₀ ∨ autI hV As = A₁ ∨
        autI hV As = A₂ := by
      have e : autI hV As =
          (autI hV A).map (MulAut.conj (convI hV ⟨m, hmN⟩)⁻¹).toMonoidHom := by
        rw [hAsA]
        exact (map_conj_autI hV hmN).symm
      have e' : ∀ X : Subgroup (MulAut (IntMod V hV)),
          (conjAut X (convI hV ⟨m, hmN⟩)).map (MulAut.conj (convI hV ⟨m, hmN⟩)⁻¹).toMonoidHom =
            X := fun X => by
        rw [conjAut, Subgroup.map_map]
        convert Subgroup.map_id X
        ext φ w
        simp
      rcases hmb with h0 | h0 | h0
      · left; rw [e, h0, e']
      · right; left; rw [e, h0, e']
      · right; right; rw [e, h0, e']
    have hĀsmem : autI hV As ∈ ({A₀, A₁, A₂} :
        Set (Subgroup (MulAut (IntMod V hV)))) := by
      rcases hĀs with h0 | h0 | h0 <;> rw [h0] <;> simp
    have hcardĀs : Nat.card (autI hV As) = 2 ^ 4 := (hAi _ hĀsmem).2.2
    have hĀs1 : autI hV As ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hcardĀs
      norm_num at hcardĀs
    have hVAs : ¬ V ≤ Subgroup.normalizer (As : Set G) := by
      intro h
      apply hVA
      have h1 := conjSubgroup_le_normalizer h m⁻¹
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ hmN), hAsA,
        conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h1
    have hcomm : ⁅V, As⁆ ≠ ⊥ := by
      intro h0
      apply hĀs1
      rw [autI_eq_bot_iff hV hAsN, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.commutator_comm]
      exact h0
    have hw0 : wParam T V = ((0 : ℕ) : ℕ∞) := le_antisymm (iInf₂_le 0 hW) (by simp)
    have hoff : IsWOffenderAt T V (g * m) := by
      refine ⟨by rw [← hAsV]; exact hcomm, ?_⟩
      rw [← hAsV, inf_eq_left.mpr hAsN, mQuot_self, hw0]
    have hk : ((3 : ℕ) : ℕ∞) + wParam T V + 1 ≤ rParam V := by
      rw [hw0]
      refine le_trans ?_ hr
      norm_num
    have h332 := e3_32 hV hoff hk
    rw [← hAsV, inf_eq_left.mpr hAsN] at h332
    have hgam : ∀ X : Subgroup (MulAut (IntMod V hV)), X ≤ autI hV As →
        mQuot (autI hV As) X ≤ 3 → ∀ w ∈ fixV X, w.val ∈ Subgroup.normalizer (As : Set G) :=
      fun X hX hXk w hw =>
        (h332 (Subgroup.mem_map_of_mem (valHom hV) (fixV_le_gammaCheck hX hXk hw))).2
    have hV₁As : V₁ ⊓ As = ⊥ := by
      by_contra hne
      apply hcomm
      rw [hAsV] at hne ⊢
      exact h1216' (g * m) hne
    have hfixb : ∀ bb ∈ autI hV As ⊓ autI hV L, bb ≠ 1 →
        fixV (Subgroup.zpowers bb) ⊓ subI hV V₁ =
          subI hV (V₁ ⊓ Subgroup.normalizer (As : Set G)) := by
      intro bb hbb hbb1
      obtain ⟨⟨b, hbN⟩, hbAs, rfl⟩ := (mem_autI hV).1 hbb.1
      have hbV₁ := hLnorm hbN hbb.2
      apply le_antisymm
      · intro w hw
        rw [Subgroup.mem_inf] at hw
        rw [mem_subI, Subgroup.mem_inf]
        have hbb2 : (convI hV ⟨b, hbN⟩) ^ 2 = 1 := (hAi _ hĀsmem).2.1.2 _ hbb.1
        have hord : orderOf (convI hV ⟨b, hbN⟩) = 2 := orderOf_eq_prime hbb2 hbb1
        have hzle : Subgroup.zpowers (convI hV ⟨b, hbN⟩) ≤ autI hV As :=
          Subgroup.zpowers_le.mpr hbb.1
        have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers (convI hV ⟨b, hbN⟩))
          (autI hV As)
        rw [inf_eq_left.mpr hzle, Nat.card_zpowers, hord, hcardĀs] at h1
        have h8 : (Subgroup.zpowers (convI hV ⟨b, hbN⟩)).relIndex (autI hV As) = 2 ^ 3 := by
          norm_num at h1 ⊢
          omega
        have hq : mQuot (autI hV As) (Subgroup.zpowers (convI hV ⟨b, hbN⟩)) ≤ 3 := by
          rw [mQuot, h8, padicValNat.prime_pow]
        exact ⟨hw.2, hgam _ hzle hq w hw.1⟩
      · intro w hw
        rw [mem_subI, Subgroup.mem_inf] at hw
        rw [Subgroup.mem_inf]
        refine ⟨?_, hw.1⟩
        rw [H.mem_fixV_zpowers_iff]
        apply IntMod.val_injective
        rw [convI_apply_val]
        have h1 := hcommV₁ b hbAs hbV₁ w.val hw.1 hw.2
        rw [hV₁As, Subgroup.mem_bot, mul_inv_eq_one] at h1
        exact h1
    have hfin : ∀ X ∈ ({A₁, A₂} : Set (Subgroup (MulAut (IntMod V hV)))),
        autI hV As = X → False := by
      intro X hX hAsX
      obtain ⟨⟨b₁, hb₁, ht₁⟩, ⟨b₂, hb₂, hb₂1, ht₂⟩, -⟩ := h7 X hX
      rw [← hAsX] at hb₁ hb₂
      have hb₁1 : b₁ ≠ 1 := by
        rintro rfl
        have h2 := ht₁.2
        have h3 : subI hV V₁ ≤
            fixV (Subgroup.zpowers (1 : MulAut (IntMod V hV))) ⊓ subI hV V₁ :=
          fun w hw => ⟨fun x hx => by
            rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hx
            rw [hx]
            rfl, hw⟩
        rw [Subgroup.relIndex_eq_one.mpr h3] at h2
        norm_num at h2
      apply ht₂
      refine ⟨hH9.inv₁ hb₂.2, ?_⟩
      rw [hfixb b₂ hb₂ hb₂1, ← hfixb b₁ hb₁ hb₁1]
      exact ht₁.2
    rcases hĀs with h0 | h0 | h0
    ·
      apply hVAs
      intro v hv
      have h1 : IntMod.mk hV ⟨v, hv⟩ ∈ gammaCheck 3 (autI hV As) := by
        rw [h0]
        refine gammaCheck_mono (k := 2) (by norm_num) _ ?_
        rw [hA₀]
        exact Subgroup.mem_top _
      exact (h332 (Subgroup.mem_map_of_mem (valHom hV) h1)).2
    · exact hfin A₁ (Set.mem_insert _ _) h0
    · exact hfin A₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) h0

end CFSG.Quasithin.H13
