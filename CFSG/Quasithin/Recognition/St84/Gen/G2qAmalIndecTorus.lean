module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecBasic

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

private theorem conj_mem_of_mem_normalizer {G : Type*} [Group G] {K : Subgroup G} {g k : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) : g * k * g⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp hg k).mp hk

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

attribute [local instance] G2qCoord.field G2qCoord.fintype

private theorem le_left_of_g2q (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L1 :=
  (hD.borelOf_inf_borelOf hH h1 h2).symm.le.trans (inf_le_left.trans (borelOf_le L1 S))

private theorem le_right_of_g2q (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L2 :=
  (hD.borelOf_inf_borelOf hH h1 h2).symm.le.trans (inf_le_right.trans (borelOf_le L2 S))

theorem G2qCoord.alpha_eq_of_inv_mul_mem {L : Subgroup G} (c : G2qCoord L S f) {x y : G}
    (hx : x ∈ L) (hy : y ∈ L) (h : x⁻¹ * y ∈ pCoreOf 2 L) : c.α ⟨x, hx⟩ = c.α ⟨y, hy⟩ := by
  have h1 : c.α (⟨x, hx⟩⁻¹ * ⟨y, hy⟩) = 1 := (c.ker _).mpr h
  rwa [map_mul, map_inv, inv_mul_eq_one] at h1

private theorem exists_pCoreOf_left_inv_mul_mem (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {s : G} (hs : s ∈ S) :
    ∃ x ∈ pCoreOf 2 L1, x⁻¹ * s ∈ pCoreOf 2 L2 := by
  have hnorm : pCoreOf 2 L2 ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    (hH.pCoreOf_le_right.trans (le_left_of_g2q hH hD h1 h2)).trans (le_normalizer_pCoreOf 2 L1)
  rw [← hD.pCoreOf_left_sup_right hH h1 h2] at hs
  obtain ⟨x, hx, b, hb, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hnorm).mp hs
  exact ⟨x, hx, by rwa [inv_mul_cancel_left]⟩

theorem G2qCoordRight.exists_pCoreOf_left_alpha_eq (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f) (r : c.F) :
    ∃ x ∈ pCoreOf 2 L1, ∃ hx : x ∈ L2, c.α ⟨x, hx⟩ = utriElt r := by
  obtain ⟨s, hs⟩ := c.surj (utriElt r)
  have hsS : (s : G) ∈ S := (c.memS s).mpr (by rw [hs]; exact utriElt_mem_utri r)
  obtain ⟨x, hx, hxs⟩ := exists_pCoreOf_left_inv_mul_mem hH hD h1 h2 hsS
  have hxL2 : x ∈ L2 := le_right_of_g2q hH hD h1 h2 (hH.pCoreOf_le_left hx)
  exact ⟨x, hx, hxL2, (c.alpha_eq_of_inv_mul_mem hxL2 s.2 hxs).trans hs⟩

theorem G2qCoordRight.natSecVec_snd_eq_zero_of_mem_inf (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f)
    {β : ↥(pCoreOf 2 L2) →* Multiplicative (Fin 2 → c.F)}
    (hβker : β.ker = c.W.subgroupOf (pCoreOf 2 L2))
    (hβeq : ∀ ℓ : ↥L2, ∀ u v : ↥(pCoreOf 2 L2), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (c.α ℓ : Matrix (Fin 2) (Fin 2) c.F).mulVec (Multiplicative.toAdd (β u)))
    {y : G} (hy1 : y ∈ pCoreOf 2 L1) (hy2 : y ∈ pCoreOf 2 L2) : natSecVec β y 1 = 0 := by
  obtain ⟨x, hx, hxL2, hxα⟩ := c.exists_pCoreOf_left_alpha_eq hH hD h1 h2 1
  have hW : ⁅x, y⁆ ∈ c.W := c.center_le
    (hD.centerOf_pCoreOf_left_le_right hH h1 h2 (hD.commutator_mem_centerOf_left hx hy1))
  have h0 := (natSecVec_eq_zero_iff hβker (c.le_pCoreOf hW)).mpr hW
  have hc : x * y * x⁻¹ ∈ pCoreOf 2 L2 :=
    conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hxL2) hy2
  rw [natSecVec_commutator hβeq ⟨x, hxL2⟩ hy2 hc, hxα] at h0
  have k := congrFun h0 0
  rw [Pi.sub_apply, utriElt_mulVec_apply_zero, one_mul] at k
  simpa using k

private theorem mem_pCoreOf_right_of_centralizes (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {h : G} (hhB : h ∈ bigB L1 L2 S)
    (hc : ∀ a ∈ pCoreOf 2 L2, h * a * h⁻¹ = a) : h ∈ pCoreOf 2 L2 := by
  have hS1 := le_left_of_g2q hH hD h1 h2
  have hS2 := le_right_of_g2q hH hD h1 h2
  have hP2 : L2 ⊔ S ⊔ borelOf L1 S = L2 ⊔ bigB L1 L2 S := by
    rw [show L2 ⊔ S = L2 from sup_eq_left.mpr hS2]
    refine le_antisymm (sup_le le_sup_left ((le_sup_left.trans le_sup_left).trans le_sup_right))
      (sup_le le_sup_left ?_)
    rw [bigB]
    exact sup_le (sup_le le_sup_right ((borelOf_le L2 S).trans le_sup_left))
      (hS2.trans le_sup_left)
  have hcore : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 :=
    pCoreOf_sup_bigB_right_of_le hH hS1 hS2
  have hhP : h ∈ L2 ⊔ S ⊔ borelOf L1 S := by
    rw [hP2]
    exact Subgroup.mem_sup_right hhB
  have hhC : h ∈ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S ⊔ borelOf L1 S) : Set G) := by
    rw [hP2, hcore, Subgroup.mem_centralizer_iff]
    intro a ha
    calc a * h = h * a * h⁻¹ * h := by rw [hc a ha]
      _ = h * a := by group
  have := hH.h2.charTwo ⟨hhP, hhC⟩
  rwa [hP2, hcore] at this

theorem G2qLocalData.exists_conj_commutator_eq_mul (hD : G2qLocalData L1 L2 S f) {h l x : G}
    (hl : l ∈ L1) (ht1 : h ∈ trivOTwoQuot L1)
    (hhQ : h ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G)) (hx : x ∈ pCoreOf 2 L1) :
    ∃ z₁ ∈ centerOf (pCoreOf 2 L1), ∃ z₂ ∈ centerOf (pCoreOf 2 L1),
      l * (h * x * h⁻¹ * x⁻¹) * l⁻¹ =
        z₁ * (h * (l * x * l⁻¹) * h⁻¹ * (l * x * l⁻¹)⁻¹) * z₂ := by
  have hk : (h * l * h⁻¹ * l⁻¹)⁻¹ ∈ pCoreOf 2 L1 := inv_mem ((mem_trivOTwoQuot.mp ht1).2 l hl)
  have hx' : l * x * l⁻¹ ∈ pCoreOf 2 L1 :=
    conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L1 hl) hx
  have hφ : h * (l * x * l⁻¹) * h⁻¹ * (l * x * l⁻¹)⁻¹ ∈ pCoreOf 2 L1 :=
    mul_mem (conj_mem_of_mem_normalizer hhQ hx') (inv_mem hx')
  refine ⟨⁅(h * l * h⁻¹ * l⁻¹)⁻¹, h * (l * x * l⁻¹) * h⁻¹ * (l * x * l⁻¹)⁻¹⁆,
    hD.commutator_mem_centerOf_left hk hφ, ⁅(h * l * h⁻¹ * l⁻¹)⁻¹, l * x * l⁻¹⁆,
    hD.commutator_mem_centerOf_left hk hx', ?_⟩
  simp only [commutatorElement_def]
  group

private theorem conj_mul_inv_mem_W_of_triv (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) {h : G} (hhQ : h ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G))
    (ht1 : h ∈ trivOTwoQuot L1) (ht2 : h ∈ trivOTwoQuot L2) {a : G} (ha : a ∈ pCoreOf 2 L2) :
    h * a * h⁻¹ * a⁻¹ ∈ c.W := by
  obtain ⟨β, -, hβker, hβeq⟩ := c.natW
  have hSL1 := le_left_of_g2q hH hD h1 h2
  have hd : ∀ b ∈ pCoreOf 2 L2, h * b * h⁻¹ * b⁻¹ ∈ pCoreOf 2 L1 ∧
      h * b * h⁻¹ * b⁻¹ ∈ pCoreOf 2 L2 := fun b hb =>
    ⟨(mem_trivOTwoQuot.mp ht1).2 b (hSL1 (hH.pCoreOf_le_right hb)),
      mul_mem (conj_mem_of_mem_normalizer hhQ hb) (inv_mem hb)⟩
  have hsnd : ∀ b ∈ pCoreOf 2 L2, natSecVec β (h * b * h⁻¹ * b⁻¹) 1 = 0 := fun b hb =>
    c.natSecVec_snd_eq_zero_of_mem_inf hH hD h1 h2 hβker hβeq (hd b hb).1 (hd b hb).2
  obtain ⟨l, hl⟩ := c.surj (ltriElt 1)
  have hlL : (l : G) ∈ L2 := l.2
  have hla : (l : G) * a * (l : G)⁻¹ ∈ pCoreOf 2 L2 :=
    conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hlL) ha
  have hl'L : h * (l : G) * h⁻¹ ∈ L2 := conj_mem_of_mem_normalizer (mem_trivOTwoQuot.mp ht2).1 hlL
  have hαl' : c.α ⟨h * (l : G) * h⁻¹, hl'L⟩ = c.α l := by
    refine c.alpha_eq_of_inv_mul_mem hl'L hlL ?_
    have := (mem_trivOTwoQuot.mp ht2).2 (l : G)⁻¹ (inv_mem hlL)
    rwa [show (h * (l : G) * h⁻¹)⁻¹ * l = h * (l : G)⁻¹ * h⁻¹ * (l : G)⁻¹⁻¹ by group]
  have hha : h * a * h⁻¹ ∈ pCoreOf 2 L2 := conj_mem_of_mem_normalizer hhQ ha
  have hc1 : (h * (l : G) * h⁻¹) * (h * a * h⁻¹) * (h * (l : G) * h⁻¹)⁻¹ ∈ pCoreOf 2 L2 :=
    conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hl'L) hha
  have hc2 : (l : G) * a⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L2 :=
    conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hlL) (inv_mem ha)
  have hv : natSecVec β (h * ((l : G) * a * (l : G)⁻¹) * h⁻¹ * ((l : G) * a * (l : G)⁻¹)⁻¹) =
      (c.α l : Matrix (Fin 2) (Fin 2) c.F) *ᵥ natSecVec β (h * a * h⁻¹ * a⁻¹) := by
    rw [show h * ((l : G) * a * (l : G)⁻¹) * h⁻¹ * ((l : G) * a * (l : G)⁻¹)⁻¹ =
        (h * (l : G) * h⁻¹) * (h * a * h⁻¹) * (h * (l : G) * h⁻¹)⁻¹ *
          ((l : G) * a⁻¹ * (l : G)⁻¹) by group,
      natSecVec_mul β hc1 hc2, natSecVec_conj hβeq ⟨_, hl'L⟩ hha hc1, hαl',
      natSecVec_conj hβeq l (inv_mem ha) hc2, natSecVec_mul β hha (inv_mem ha), Matrix.mulVec_add]
  have k := congrFun hv 1
  rw [hl, ltriElt_mulVec_apply_one, one_mul, hsnd _ hla, hsnd a ha, add_zero] at k
  have hzero : natSecVec β (h * a * h⁻¹ * a⁻¹) = 0 := by
    ext i
    fin_cases i
    · simpa using k.symm
    · simpa using hsnd a ha
  exact (natSecVec_eq_zero_iff hβker (hd a ha).2).mp hzero

private theorem commutator_conj_eq_of_triv (c : G2qCoordRight L2 S f) {h : G}
    (hhQ : h ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G))
    (hMN : ∀ a ∈ pCoreOf 2 L2, h * a * h⁻¹ * a⁻¹ ∈ c.W) {w a : G} (hw : w ∈ c.W)
    (ha : a ∈ pCoreOf 2 L2) : ⁅h * w * h⁻¹, a⁆ = h * ⁅w, a⁆ * h⁻¹ := by
  have hb : h⁻¹ * a * h ∈ pCoreOf 2 L2 := (Subgroup.mem_normalizer_iff''.mp hhQ a).mp ha
  obtain ⟨k, hkW, hka⟩ : ∃ k ∈ c.W, h⁻¹ * a * h = k * a := by
    refine ⟨h⁻¹ * a * h * a⁻¹, ?_, by group⟩
    have := inv_mem (hMN _ hb)
    rwa [show (h * (h⁻¹ * a * h) * h⁻¹ * (h⁻¹ * a * h)⁻¹)⁻¹ = h⁻¹ * a * h * a⁻¹ by group] at this
  have hZ : ⁅w, a⁆ ∈ centerOf (pCoreOf 2 L2) :=
    c.commutator_le (Subgroup.commutator_mem_commutator hw (pCoreOf_le 2 L2 ha))
  have h1 : w * k = k * w := c.commute_of_mem_W hw hkW
  have h2 : k * ⁅w, a⁆ * k⁻¹ = ⁅w, a⁆ := by
    rw [mul_comm_of_mem_centerOf hZ (c.le_pCoreOf hkW), mul_inv_cancel_right]
  have hcomm : ⁅w, k * a⁆ = ⁅w, a⁆ := by
    calc ⁅w, k * a⁆ = (w * k) * a * w⁻¹ * a⁻¹ * k⁻¹ := by rw [commutatorElement_def]; group
      _ = (k * w) * a * w⁻¹ * a⁻¹ * k⁻¹ := by rw [h1]
      _ = k * ⁅w, a⁆ * k⁻¹ := by rw [commutatorElement_def]; group
      _ = ⁅w, a⁆ := h2
  calc ⁅h * w * h⁻¹, a⁆ = h * ⁅w, h⁻¹ * a * h⁆ * h⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = h * ⁅w, a⁆ * h⁻¹ := by rw [hka, hcomm]

private theorem eq_one_of_fixed_centerOf (c : G2qCoordRight L2 S f) {h : G}
    (ht2 : h ∈ trivOTwoQuot L2)
    (hnot : ¬∀ z ∈ centerOf (pCoreOf 2 L2), h * z * h⁻¹ = z) {z : G}
    (hz : z ∈ centerOf (pCoreOf 2 L2)) (hzh : h * z * h⁻¹ = z) : z = 1 := by
  obtain ⟨β, -, hβker, hβeq⟩ := c.nat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have hLZ : L2 ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L2) : Set G) :=
    le_normalizer_centerOf_of_le_normalizer (le_normalizer_pCoreOf 2 L2)
  by_contra hz1
  refine hnot fun z' hz' => ?_
  by_cases hz'1 : z' = 1
  · rw [hz'1]
    group
  have hX : ∀ l ∈ L2, ∀ y ∈ {y : G | y ∈ centerOf (pCoreOf 2 L2) ∧ h * y * h⁻¹ = y},
      l * y * l⁻¹ ∈ {y : G | y ∈ centerOf (pCoreOf 2 L2) ∧ h * y * h⁻¹ = y} := by
    rintro l hl y ⟨hyZ, hyh⟩
    have hlyZ : l * y * l⁻¹ ∈ centerOf (pCoreOf 2 L2) := conj_mem_of_mem_normalizer (hLZ hl) hyZ
    refine ⟨hlyZ, ?_⟩
    have hk : h * l * h⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := (mem_trivOTwoQuot.mp ht2).2 l hl
    calc h * (l * y * l⁻¹) * h⁻¹ =
        (h * l * h⁻¹ * l⁻¹) * (l * (h * y * h⁻¹) * l⁻¹) * (h * l * h⁻¹ * l⁻¹)⁻¹ := by group
      _ = (h * l * h⁻¹ * l⁻¹) * (l * y * l⁻¹) * (h * l * h⁻¹ * l⁻¹)⁻¹ := by rw [hyh]
      _ = l * y * l⁻¹ := by rw [mul_comm_of_mem_centerOf hlyZ hk, mul_inv_cancel_right]
  exact (natSec_mem_of_conj_mem c.surj hβinj hβeq hLZ hX hz ⟨hz, hzh⟩ hz1 hz' hz'1).2

private theorem centralizes_of_centralizes_centerOf (c : G2qCoordRight L2 S f) {h : G} {n : ℕ}
    (hn : Odd n) (hhn : h ^ n = 1) (hhW : h ∈ Subgroup.normalizer (c.W : Set G))
    (hMN : ∀ a ∈ pCoreOf 2 L2, h * a * h⁻¹ * a⁻¹ ∈ c.W)
    (hpair : ∀ w ∈ c.W, ∀ a ∈ pCoreOf 2 L2, ⁅h * w * h⁻¹, a⁆ = h * ⁅w, a⁆ * h⁻¹)
    (hcZ : ∀ z ∈ centerOf (pCoreOf 2 L2), h * z * h⁻¹ = z) :
    ∀ a ∈ pCoreOf 2 L2, h * a * h⁻¹ = a := by
  have hcW : ∀ w ∈ c.W, h * w * h⁻¹ = w := by
    intro w hw
    have hwQ := c.le_pCoreOf hw
    have hhw : h * w * h⁻¹ ∈ c.W := conj_mem_of_mem_normalizer hhW hw
    have hy'Z : w⁻¹ * (h * w * h⁻¹) ∈ centerOf (pCoreOf 2 L2) := by
      refine mem_centerOf_of_forall_comm (mul_mem (inv_mem hwQ) (c.le_pCoreOf hhw)) fun a ha => ?_
      have e1 : ⁅h * w * h⁻¹, a⁆ = ⁅w, a⁆ := by
        rw [hpair w hw a ha, hcZ _ (c.commutator_le
          (Subgroup.commutator_mem_commutator hw (pCoreOf_le 2 L2 ha)))]
      rw [commutatorElement_def, commutatorElement_def] at e1
      have e2 : h * w * h⁻¹ * a * (h * w * h⁻¹)⁻¹ = w * a * w⁻¹ := mul_right_cancel e1
      calc a * (w⁻¹ * (h * w * h⁻¹)) = w⁻¹ * (w * a * w⁻¹) * (h * w * h⁻¹) := by group
        _ = w⁻¹ * (h * w * h⁻¹ * a * (h * w * h⁻¹)⁻¹) * (h * w * h⁻¹) := by rw [e2]
        _ = w⁻¹ * (h * w * h⁻¹) * a := by group
    have hyZ : h * w * h⁻¹ * w⁻¹ ∈ centerOf (pCoreOf 2 L2) := by
      rw [show h * w * h⁻¹ * w⁻¹ = w * (w⁻¹ * (h * w * h⁻¹)) * w⁻¹ by group]
      exact mem_centerOf_conj_of_mem_normalizer (Subgroup.le_normalizer hwQ) hy'Z
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one_of_mem_pCoreOf
      (show h * w * h⁻¹ * w⁻¹ ∈ pCoreOf 2 L2 from (Subgroup.mem_inf.mp hyZ).1)
    exact conj_eq_of_odd_of_fixed hn hhn hm (hcZ _ hyZ)
  intro a ha
  have hyW := hMN a ha
  obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one_of_mem_pCoreOf (c.le_pCoreOf hyW)
  exact conj_eq_of_odd_of_fixed hn hhn hm (hcW _ hyW)

private theorem le_normalizer_W_of_fixed (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) {h : G} {n : ℕ} (hn : Odd n) (hhn : h ^ n = 1)
    (hhQ1 : h ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hhW : h ∈ Subgroup.normalizer (c.W : Set G)) (ht1 : h ∈ trivOTwoQuot L1)
    (ht2 : h ∈ trivOTwoQuot L2) (hMN : ∀ a ∈ pCoreOf 2 L2, h * a * h⁻¹ * a⁻¹ ∈ c.W)
    (hpair : ∀ w ∈ c.W, ∀ a ∈ pCoreOf 2 L2, ⁅h * w * h⁻¹, a⁆ = h * ⁅w, a⁆ * h⁻¹)
    (hfix : ∀ z ∈ centerOf (pCoreOf 2 L2), h * z * h⁻¹ = z → z = 1) :
    L1 ≤ Subgroup.normalizer (c.W : Set G) := by
  have hSL2 := le_right_of_g2q hH hD h1 h2
  have hZ1W : centerOf (pCoreOf 2 L1) ≤ c.W :=
    (hD.centerOf_pCoreOf_left_le_right hH h1 h2).trans c.center_le
  have hWQ1 := c.W_le_pCoreOf_left hH hD h1 h2
  have hφW : ∀ x ∈ pCoreOf 2 L1, h * x * h⁻¹ * x⁻¹ ∈ c.W := by
    intro x hx
    have hy2 : h * x * h⁻¹ * x⁻¹ ∈ pCoreOf 2 L2 :=
      (mem_trivOTwoQuot.mp ht2).2 x (hSL2 (hH.pCoreOf_le_left hx))
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one_of_mem_pCoreOf hy2
    refine mem_of_conj_eq_mul_of_odd (x := x) hn hhn
      (fun k hk => conj_mem_of_mem_normalizer hhW hk)
      (fun k hk => conj_mem_of_mem_normalizer
        (c.normalizer_le_normalizer_W (Subgroup.le_normalizer (pCoreOf_le 2 L2 hy2))) hk)
      hm (hMN _ hy2) (by group)
  have hCW : ∀ w ∈ c.W, h * w * h⁻¹ = w → w = 1 := by
    intro w hw hwh
    refine hfix w (mem_centerOf_of_forall_comm (c.le_pCoreOf hw) fun a ha => ?_) hwh
    have hZ : ⁅w, a⁆ ∈ centerOf (pCoreOf 2 L2) :=
      c.commutator_le (Subgroup.commutator_mem_commutator hw (pCoreOf_le 2 L2 ha))
    have h1' : ⁅w, a⁆ = 1 := hfix _ hZ (by rw [← hpair w hw a ha, hwh])
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1').symm
  let φ : ↥c.W → ↥c.W := fun w => ⟨h * w * h⁻¹ * (w : G)⁻¹,
    mul_mem (conj_mem_of_mem_normalizer hhW w.2) (inv_mem w.2)⟩
  have hφinj : Function.Injective φ := by
    intro w₁ w₂ e
    have e' : h * (w₁ : G) * h⁻¹ * (w₁ : G)⁻¹ = h * w₂ * h⁻¹ * (w₂ : G)⁻¹ := congrArg Subtype.val e
    have hu : h * ((w₂ : G)⁻¹ * w₁) * h⁻¹ = (w₂ : G)⁻¹ * w₁ := by
      have hu' : h * ((w₂ : G)⁻¹ * w₁) * h⁻¹ * ((w₂ : G)⁻¹ * w₁)⁻¹ = 1 := by
        rw [show h * ((w₂ : G)⁻¹ * w₁) * h⁻¹ * ((w₂ : G)⁻¹ * w₁)⁻¹ =
          h * (w₂ : G)⁻¹ * h⁻¹ * (h * w₁ * h⁻¹ * (w₁ : G)⁻¹) * w₂ by group, e']
        group
      exact mul_inv_eq_one.mp hu'
    have := hCW _ (mul_mem (inv_mem w₂.2) w₁.2) hu
    exact Subtype.ext (inv_mul_eq_one.mp this).symm
  have hφsurj := Finite.injective_iff_surjective.mp hφinj
  refine le_normalizer_of_forall_conj_mem_of_mem fun l hl w hw => ?_
  obtain ⟨w', hw'⟩ := hφsurj ⟨w, hw⟩
  have hw'e : w = h * w' * h⁻¹ * (w' : G)⁻¹ := (congrArg Subtype.val hw').symm
  obtain ⟨z₁, hz₁, z₂, hz₂, e⟩ := hD.exists_conj_commutator_eq_mul hl ht1 hhQ1 (hWQ1 w'.2)
  rw [hw'e, e]
  exact mul_mem (mul_mem (hZ1W hz₁) (hφW _ (conj_mem_of_mem_normalizer
    (le_normalizer_pCoreOf 2 L1 hl) (hWQ1 w'.2)))) (hZ1W hz₂)

theorem G2qLocalData.trivOTwoQuot_inf_trivOTwoQuot_eq_bot (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1)) :
    H ⊓ trivOTwoQuot L1 ⊓ trivOTwoQuot L2 = ⊥ := by
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  have hf := c.one_le_f
  rw [eq_bot_iff]
  intro h hh
  obtain ⟨hh12, ht2⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨hhH, ht1⟩ := Subgroup.mem_inf.mp hh12
  rw [Subgroup.mem_bot]
  have hodd1 : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one
  have hn : Odd (Nat.card H) := by rw [hHcard]; exact hodd1.mul hodd1
  have hhn : h ^ Nat.card H = 1 := by
    have e := congrArg Subtype.val (pow_card_eq_one' (G := ↥H) (x := ⟨h, hhH⟩))
    rw [Subgroup.coe_pow, Subgroup.coe_one] at e
    exact e
  have hhB := hHB hhH
  have hNB := hD.bigB_le_normalizer hH h1 h2 hhB
  have hhL1 : h ∈ Subgroup.normalizer (L1 : Set G) := (Subgroup.mem_inf.mp
    (Subgroup.mem_inf.mp hNB).1).1
  have hhL2 : h ∈ Subgroup.normalizer (L2 : Set G) := (Subgroup.mem_inf.mp
    (Subgroup.mem_inf.mp hNB).1).2
  have hhQ1 := normalizer_le_normalizer_pCoreOf 2 L1 hhL1
  have hhQ2 := normalizer_le_normalizer_pCoreOf 2 L2 hhL2
  have hhW := c.normalizer_le_normalizer_W hhL2
  have hMN : ∀ a ∈ pCoreOf 2 L2, h * a * h⁻¹ * a⁻¹ ∈ c.W := fun a ha =>
    conj_mul_inv_mem_W_of_triv hH hD h1 h2 c hhQ2 ht1 ht2 ha
  have hpair : ∀ w ∈ c.W, ∀ a ∈ pCoreOf 2 L2, ⁅h * w * h⁻¹, a⁆ = h * ⁅w, a⁆ * h⁻¹ :=
    fun w hw a ha => commutator_conj_eq_of_triv c hhQ2 hMN hw ha
  by_cases hcZ : ∀ z ∈ centerOf (pCoreOf 2 L2), h * z * h⁻¹ = z
  · have hQ := mem_pCoreOf_right_of_centralizes hH hD h1 h2 hhB
      (centralizes_of_centralizes_centerOf c hn hhn hhW hMN hpair hcZ)
    have hSH : h ∈ S ⊓ H := ⟨hH.pCoreOf_le_right hQ, hhH⟩
    rwa [hSinfH, Subgroup.mem_bot] at hSH
  · exact (c.false_of_le_normalizer_W hH (le_normalizer_W_of_fixed hH hD h1 h2 c hn hhn hhQ1 hhW
      ht1 ht2 hMN hpair fun z hz hzh => eq_one_of_fixed_centerOf c ht2 hcZ hz hzh)).elim

end CFSG.Quasithin.F112R.St84

end
