module

public import CFSG.Quasithin.H13.L32A59c
public import CFSG.Quasithin.H13.L32A58d
public import CFSG.Quasithin.Background.E5Two

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem perm3_sq_or_cube : ∀ s : Equiv.Perm (Fin 3), s ^ 2 = 1 ∨ s ^ 3 = 1 := by
  decide

theorem finRotate_three_comm : ∀ τ : Equiv.Perm (Fin 3), τ ≠ 1 → τ * τ = 1 →
    finRotate 3 * τ ≠ τ * finRotate 3 := by
  decide

namespace T53

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

theorem pCoreOf_xT_le_centralizer :
    pCoreOf 2 (xL L V₂ ⊔ T) ≤ Subgroup.centralizer (V₂ : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [← C.conjClosure_V1_X] at hv
  have hle : conjClosure (fsuV1 T V) (xL L V₂) ≤ Subgroup.centralizer ({r} : Set G) := by
    refine conjClosure_le fun x hx z hz => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxr : x⁻¹ * r * x ∈ pCoreOf 2 (xL L V₂ ⊔ T) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left (inv_mem hx))) r).mp hr
      simpa using this
    have hc : z * (x⁻¹ * r * x) = (x⁻¹ * r * x) * z :=
      Subgroup.mem_centralizer_iff.mp
        (T_le_centralizer_V1 (V := V) (pCoreOf_le_of_le C.hyp le_sup_right hxr)) z hz
    calc x * z * x⁻¹ * r = x * (z * (x⁻¹ * r * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * r * x) * z) * x⁻¹ := by rw [hc]
      _ = r * (x * z * x⁻¹) := by group
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)

theorem thompsonJ_le_pCoreOf_xT (h4 : Lemma14_7_4_two_three)
    (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) (hsolv : Group.IsSolvable ↥(hY T L V₂ Y)) :
    thompsonJ T ≤ pCoreOf 2 (xL L V₂ ⊔ T) :=
  (le_inf ((B6.thompsonJ_le T).trans le_sup_right)
    (C.thompsonJ_le_centralizer h4 hQ hsolv)).trans (C.inf_xT_le h4)

theorem thompsonJ_not_le_pCoreOf_LT (h4 : Lemma14_7_4_two_three)
    (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) (hsolv : Group.IsSolvable ↥(hY T L V₂ Y)) :
    ¬ thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := by
  intro hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he := B6.thompsonJ_eq_of_le hJ (pCoreOf_le_of_le C.hyp le_sup_right)
  have hLT : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← he]
    intro g hg
    exact CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _ (le_normalizer_pCoreOf 2 _ hg)
  have hH := C.le_normalizer_thompsonJ h4 hQ hsolv
  have hJ2 : IsPGroup 2 (thompsonJ T) := C.hyp.fsu.sylow.1.to_le (B6.thompsonJ_le T)
  have hJ1 : thompsonJ T ≠ ⊥ := by
    have : IsMulCommutative ↥V := C.isMulCommutative_V
    have S := C.set14
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
    have h1 := hA.2.2 V S.VT ⟨inferInstance, fun v hv => S.sq_V hv⟩
    rw [S.card_V] at h1
    intro hbot
    have h2 : A ≤ ⊥ := hbot ▸ B6.le_thompsonJ hA
    rw [le_bot_iff] at h2
    rw [h2, Subgroup.card_bot] at h1
    omega
  obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge
    (⟨_, hJ1, hJ2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (thompsonJ T : Set G)))
  have hL13 := C.h1332 G T L C.hyp.hyp.h13 L C.hyp.hyp.h13.faithful
  have hMeq := hL13.2.1.2.2.2 M hM (hLT.trans hle)
  apply C.not_le_M
  rw [← hMeq]
  exact ((le_sup_right.trans le_sup_left).trans hH).trans hle

theorem thompsonJ_not_le_centralizer_V (h4 : Lemma14_7_4_two_three)
    (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) (hsolv : Group.IsSolvable ↥(hY T L V₂ Y)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
  intro hJ
  apply C.thompsonJ_not_le_pCoreOf_LT h4 hQ hsolv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have S := C.set14
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.LV S.TV
  have hle : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_) S.isPGroup_cent_sup
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      normalizer_le_normalizer_centralizer _ (hLTV hg)⟩
  exact (le_inf ((B6.thompsonJ_le T).trans le_sup_right) hJ).trans hle

theorem thompsonJk_not_le_of (hJR : thompsonJ T ≤ pCoreOf 2 (xL L V₂ ⊔ T))
    (hJV : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ¬ thompsonJk 1 T ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
  intro hJk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have S := C.set14
  have hR₂T : pCoreOf 2 (xL L V₂ ⊔ T) ≤ T := pCoreOf_le_of_le C.hyp le_sup_right
  have hR₂V₂ := C.pCoreOf_xT_le_centralizer
  have hXL : xL L V₂ ≤ L := fun x hx => (oTwoRes_le _ hx).1
  obtain ⟨A, hA, hAV⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra h
    push Not at h
    exact hJV (iSup₂_le fun A hA => h A hA)
  obtain ⟨a, haA, hav⟩ := IsConcreteLE.not_le_iff_exists.mp hAV
  have haT : a ∈ T := hA.1 haA
  have haR : a ∈ pCoreOf 2 (xL L V₂ ⊔ T) := hJR (B6.le_thompsonJ hA haA)
  have haV₂ : ∀ u ∈ V₂, a * u * a⁻¹ = u := fun u hu => by
    rw [show a * u = u * a from (Subgroup.mem_centralizer_iff.mp (hR₂V₂ haR) u hu).symm]
    group
  obtain ⟨z, w, b, hz, hz1, hw, hwV, hb, hbV⟩ := S.exists_basis
  have haN : a ∈ Subgroup.normalizer (V : Set G) := S.TV haT
  have hbV' : a * b * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp haN b).mp hb
  have hcV₂ : b * (a * b * a⁻¹) ∈ V₂ := by
    rcases S.mem_V hb hbV hbV' with h | h
    · exfalso
      apply hbV
      have := (Subgroup.mem_normalizer_iff.mp (C.hV2.2.2.1 (inv_mem haT)) _).mp h
      simpa [mul_assoc] using this
    · exact h
  have hact : ∀ v ∈ V, a * v * a⁻¹ = v ∨ a * v * a⁻¹ = b * (a * b * a⁻¹) * v := by
    intro v hv
    rcases S.mem_V hb hbV hv with h | h
    · exact Or.inl (haV₂ v h)
    · right
      have hv' : v = b * (b * v) := by rw [← mul_assoc, S.mul_self_V hb, one_mul]
      calc a * v * a⁻¹ = a * (b * (b * v)) * a⁻¹ := by rw [← hv']
        _ = (a * b * a⁻¹) * (a * (b * v) * a⁻¹) := by group
        _ = (a * b * a⁻¹) * (b * v) := by rw [haV₂ _ h]
        _ = (a * b * a⁻¹) * b * v := (mul_assoc _ _ _).symm
        _ = b * (a * b * a⁻¹) * v := by rw [S.comm_V hbV' hb]
  have hc1 : b * (a * b * a⁻¹) ≠ 1 := by
    intro h1
    apply hav
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h2 : a * v * a⁻¹ = v := by
      rcases hact v hv with h | h
      · exact h
      · rw [h, h1, one_mul]
    calc v * a = (a * v * a⁻¹) * a := by rw [h2]
      _ = a * v := by group
  obtain ⟨x, hx, hxc⟩ : ∃ x ∈ xL L V₂, x * (b * (a * b * a⁻¹)) * x⁻¹ = z := by
    by_cases hcz : b * (a * b * a⁻¹) = z
    · exact ⟨1, one_mem _, by rw [hcz]; group⟩
    · have hcV₁ : b * (a * b * a⁻¹) ∉ fsuV1 T V := by
        intro h
        rcases S.eq_of_mem_V1 hz hz1 h with h' | h'
        · exact hc1 h'
        · exact hcz h'
      obtain ⟨l, hl, hlz⟩ := S.exists_L2 hz hz1 hcV₂ hcV₁ hb hbV
      exact ⟨l⁻¹, inv_mem hl, by rw [← hlz]; group⟩
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.LV (hXL hx)
  have ha'R : x * a * x⁻¹ ∈ pCoreOf 2 (xL L V₂ ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx)) a).mp
      haR
  have ha'T : x * a * x⁻¹ ∈ T := hR₂T ha'R
  have hact' : ∀ v ∈ V, (x * a * x⁻¹) * v * (x * a * x⁻¹)⁻¹ = v ∨
      (x * a * x⁻¹) * v * (x * a * x⁻¹)⁻¹ = z * v := by
    intro v hv
    have hv' : x⁻¹ * v * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) v).mp hv
      simpa using this
    have e : (x * a * x⁻¹) * v * (x * a * x⁻¹)⁻¹ = x * (a * (x⁻¹ * v * x) * a⁻¹) * x⁻¹ := by
      group
    rcases hact _ hv' with h | h
    · left
      rw [e, h]
      group
    · right
      rw [e, h, ← hxc]
      group
  have ha'V : ¬ ∀ v ∈ V, (x * a * x⁻¹) * v * (x * a * x⁻¹)⁻¹ = v := by
    intro h
    apply hav
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hxv : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
    have h1 := h _ hxv
    have h2 : a * v * a⁻¹ = v := by
      have h3 : x * (a * v * a⁻¹) * x⁻¹ = x * v * x⁻¹ := by
        rw [← h1]
        group
      exact mul_left_cancel (mul_right_cancel h3)
    calc v * a = (a * v * a⁻¹) * a := by rw [h2]
      _ = a * v := by group
  have hH1 : L₁Of L (fsuV1 T V) ⊔ T ≤ L32NSet14.nX T V := sup_le S.L1_le_X S.T_le_X
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := fun g hg => (oTwoRes_le _ hg).1
  have hH2 : L₁Of L (fsuV1 T V) ⊔ T ≤ L ⊔ T := sup_le (hL1L.trans le_sup_left) le_sup_right
  have ha'R₁ : x * a * x⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    refine S.le_pCoreOf hH1 hH2 (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right ha'T, ?_⟩)
    refine L32NSet14.mem_trivSub.mpr ⟨S.TV ha'T, S.T_V1 ha'T, fun v hv => ?_⟩
    rcases hact' v hv with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h, mul_inv_cancel_right]
      exact hz
  have hR₁T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le C.hyp le_sup_right
  have hA'R : cjSub x A ≤ pCoreOf 2 (xL L V₂ ⊔ T) :=
    cjSub_le (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx))
      ((B6.le_thompsonJ hA).trans hJR)
  have hA'T : cjSub x A ≤ T := hA'R.trans hR₂T
  have hBcard : Nat.card (cjSub x A) ≤
      2 * Nat.card ↥(pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ cjSub x A) := by
    have hne : (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).relIndex T ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card (H := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (K := T)
      rw [h0, zero_mul] at this
      exact Nat.card_pos.ne this
    have h2 := (Subgroup.relIndex_le_of_le_right hA'T hne).trans S.index2_le
    have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
      (K := cjSub x A)
    rw [← h1]
    exact Nat.mul_le_mul_right _ h2
  have hBe : IsElemAbelian 2 (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ cjSub x A) :=
    B2F.isElemAbelian_mono inf_le_right (isElemAbelian_cjSub hA.2.1)
  have ha'B : x * a * x⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ cjSub x A := by
    refine Subgroup.mem_inf.mpr ⟨ha'R₁, mem_cjSub.mpr ?_⟩
    rw [show x⁻¹ * (x * a * x⁻¹) * x = a by group]
    exact haA
  obtain ⟨l, hl, -, hlw, -⟩ := S.exists_x hz hz1 hw hwV hb hbV
  have hlN : l ∈ Subgroup.normalizer (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl)
  have hB''T : cjSub l⁻¹ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ cjSub x A) ≤ T :=
    (cjSub_le (inv_mem hlN) inf_le_left).trans hR₁T
  have hB''J : cjSub l⁻¹ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ cjSub x A) ≤ thompsonJk 1 T := by
    refine E5.le_thompsonJk hB''T (isElemAbelian_cjSub hBe) fun D hDT hD => ?_
    calc Nat.card D ≤ Nat.card A := hA.2.2 D hDT hD
      _ = Nat.card (cjSub x A) := (card_cjSub x A).symm
      _ ≤ 2 * Nat.card ↥(pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ cjSub x A) := hBcard
      _ = 2 ^ 1 * Nat.card ↥(cjSub l⁻¹ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ cjSub x A)) := by
        rw [card_cjSub, pow_one]
  have hb'' : l⁻¹ * (x * a * x⁻¹) * l ∈
      cjSub l⁻¹ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ cjSub x A) := by
    rw [mem_cjSub, inv_inv, show l * (l⁻¹ * (x * a * x⁻¹) * l) * l⁻¹ = x * a * x⁻¹ by group]
    exact ha'B
  have hcent := hR₂V₂ (hJk (hB''J hb''))
  have hfixb : (x * a * x⁻¹) * b * (x * a * x⁻¹)⁻¹ = b := by
    have h1 := Subgroup.mem_centralizer_iff.mp hcent w hw
    rw [← hlw]
    calc (x * a * x⁻¹) * (l * w * l⁻¹) * (x * a * x⁻¹)⁻¹ =
          l * ((l⁻¹ * (x * a * x⁻¹) * l) * w) * (l⁻¹ * (x * a * x⁻¹) * l)⁻¹ * l⁻¹ := by group
      _ = l * (w * (l⁻¹ * (x * a * x⁻¹) * l)) * (l⁻¹ * (x * a * x⁻¹) * l)⁻¹ * l⁻¹ := by
        rw [← h1]
      _ = l * w * l⁻¹ := by group
  apply ha'V
  intro v hv
  rcases S.mem_V hb hbV hv with h | h
  · rw [show (x * a * x⁻¹) * v = v * (x * a * x⁻¹) from
      (Subgroup.mem_centralizer_iff.mp (hR₂V₂ ha'R) v h).symm]
    group
  · have hv' : v = b * (b * v) := by rw [← mul_assoc, S.mul_self_V hb, one_mul]
    have hu := Subgroup.mem_centralizer_iff.mp (hR₂V₂ ha'R) _ h
    calc (x * a * x⁻¹) * v * (x * a * x⁻¹)⁻¹ =
          (x * a * x⁻¹) * (b * (b * v)) * (x * a * x⁻¹)⁻¹ := by rw [← hv']
      _ = ((x * a * x⁻¹) * b * (x * a * x⁻¹)⁻¹) *
          ((x * a * x⁻¹) * (b * v) * (x * a * x⁻¹)⁻¹) := by group
      _ = b * (b * v) := by
        rw [hfixb, show (x * a * x⁻¹) * (b * v) = (b * v) * (x * a * x⁻¹) from hu.symm]
        group
      _ = v := hv'.symm

theorem xL_eq_commutator_of (h4 : Lemma14_7_4_two_three)
    (hJk : ¬ thompsonJk 1 T ≤ pCoreOf 2 (xL L V₂ ⊔ T)) :
    xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJT : thompsonJk 1 T ≤ T := E5.thompsonJk_le 1 T
  have hXN : T ≤ Subgroup.normalizer (xL L V₂ : Set G) := C.T_le_normalizer_xL
  have hle : ⁅xL L V₂, thompsonJk 1 T⁆ ≤ xL L V₂ := by
    rw [Subgroup.commutator_le]
    intro x hx j hj
    have h1 : j * x⁻¹ * j⁻¹ ∈ xL L V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hXN (hJT hj)) _).mp (inv_mem hx)
    rw [commutatorElement_def, show x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) by group]
    exact mul_mem hx h1
  refine le_antisymm ?_ hle
  by_contra hno
  have hn : xL L V₂ ⊔ T ≤
      Subgroup.normalizer ((⁅xL L V₂, thompsonJk 1 T⁆ : Subgroup G) : Set G) :=
    sup_le (Subgroup.normalizer_commutator_ge_left _ _) fun t ht =>
      A4.mem_normalizer_commutator (hXN ht) (E5.le_normalizer_thompsonJk 1 T ht)
  have hK := le_pCoreOf_of_normal_of_S3 (C.quot_xT h4).1 (hle.trans le_sup_left) hn
    (by rw [C.oTwoUpper_xT]; exact hno)
  obtain ⟨φ, hφs, hφk⟩ := (C.quot_xT h4).1
  have hker : ∀ y : ↥(xL L V₂ ⊔ T), φ y = 1 ↔ (y : G) ∈ pCoreOf 2 (xL L V₂ ⊔ T) := by
    intro y
    rw [← MonoidHom.mem_ker, hφk]
    exact C2Six.mem_pCore_two_iff
  have hX2 : ¬ xL L V₂ ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
    intro h
    have : IsMulCommutative ↥V := C.isMulCommutative_V
    have hle' : conjClosure (fsuV1 T V) (xL L V₂) ≤ fsuV1 T V :=
      conjClosure_le fun x hx z hz => by
        have hxc := C.pCoreOf_xT_le_centralizer (h hx)
        rw [show x * z = z * x from (Subgroup.mem_centralizer_iff.mp hxc z (C.hV2.1 hz)).symm,
          mul_inv_cancel_right]
        exact hz
    rw [C.conjClosure_V1_X] at hle'
    have h1 := Subgroup.card_le_of_le hle'
    rw [C.hV2.2.2.2, C.set14.card_V1] at h1
    omega
  obtain ⟨x₀, hx₀, hx₀O⟩ := IsConcreteLE.not_le_iff_exists.mp hX2
  obtain ⟨j, hjJ, hjO⟩ := IsConcreteLE.not_le_iff_exists.mp hJk
  have hx₀' : x₀ ∈ xL L V₂ ⊔ T := Subgroup.mem_sup_left hx₀
  have hj' : j ∈ xL L V₂ ⊔ T := Subgroup.mem_sup_right (hJT hjJ)
  have hσ1 : φ ⟨x₀, hx₀'⟩ ≠ 1 := fun h => hx₀O ((hker _).mp h)
  have hτ1 : φ ⟨j, hj'⟩ ≠ 1 := fun h => hjO ((hker _).mp h)
  have hτ2 : φ ⟨j, hj'⟩ ^ 2 = 1 := by
    rcases perm3_sq_or_cube (φ ⟨j, hj'⟩) with h | h
    · exact h
    · exfalso
      apply hτ1
      obtain ⟨k, hk⟩ := C.hyp.fsu.sylow.1 ⟨j, hJT hjJ⟩
      have hk' : φ ⟨j, hj'⟩ ^ 2 ^ k = 1 := by
        rw [← map_pow]
        have e : (⟨j, hj'⟩ : ↥(xL L V₂ ⊔ T)) ^ 2 ^ k = 1 :=
          Subtype.ext (by simpa using congrArg Subtype.val hk)
        rw [e, map_one]
      have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one hk')
      rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one] at hd
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hconj : ∀ g' : ↥(xL L V₂ ⊔ T),
      ((g' * ⟨x₀, hx₀'⟩ * g'⁻¹ : ↥(xL L V₂ ⊔ T)) : G) ∈ xL L V₂ :=
    fun g' => (Subgroup.mem_normalizer_iff.mp (sup_le Subgroup.le_normalizer hXN g'.2) x₀).mp hx₀
  obtain ⟨x₁, hx₁X, hx₁φ⟩ : ∃ x₁ : ↥(xL L V₂ ⊔ T), (x₁ : G) ∈ xL L V₂ ∧ φ x₁ = finRotate 3 := by
    obtain ⟨g, h, hgh | hgh⟩ := perm3_gen _ hσ1
    · obtain ⟨g', rfl⟩ := hφs g
      obtain ⟨h', rfl⟩ := hφs h
      refine ⟨g' * ⟨x₀, hx₀'⟩ * g'⁻¹ * (h' * ⟨x₀, hx₀'⟩ * h'⁻¹), mul_mem (hconj g') (hconj h'),
        ?_⟩
      rw [hgh]
      simp only [map_mul, map_inv]
    · obtain ⟨g', rfl⟩ := hφs g
      refine ⟨g' * ⟨x₀, hx₀'⟩ * g'⁻¹, hconj g', ?_⟩
      rw [hgh]
      simp only [map_mul, map_inv]
  apply finRotate_three_comm _ hτ1 (by rw [← pow_two]; exact hτ2)
  have he : ((x₁ * ⟨j, hj'⟩ * x₁⁻¹ * ⟨j, hj'⟩⁻¹ : ↥(xL L V₂ ⊔ T)) : G) ∈
      pCoreOf 2 (xL L V₂ ⊔ T) := by
    have h1 := hK (Subgroup.commutator_mem_commutator hx₁X hjJ)
    rw [commutatorElement_def] at h1
    simpa using h1
  have h2 := (hker _).mpr he
  simp only [map_mul, map_inv, hx₁φ] at h2
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)

theorem xL_eq_commutator (h4 : Lemma14_7_4_two_three) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥)
    (hsolv : Group.IsSolvable ↥(hY T L V₂ Y)) : xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆ :=
  C.xL_eq_commutator_of h4 (C.thompsonJk_not_le_of (C.thompsonJ_le_pCoreOf_xT h4 hQ hsolv)
    (C.thompsonJ_not_le_centralizer_V h4 hQ hsolv))

end Ctx

end T53

end CFSG.Quasithin.H13.L32A
