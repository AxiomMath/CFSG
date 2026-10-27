module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314J

public section

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {t : G}

omit [Finite G] in
theorem mem_normalizer_commutator {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  have h1 : Subgroup.map (↑(MulAut.conj x)) A = A := hA
  have h2 : Subgroup.map (↑(MulAut.conj x)) B = B := hB
  rw [Subgroup.map_commutator, h1, h2]

omit [Finite G] in
theorem commutator_le_of_le_normalizer {V X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) : ⁅V, X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [commutatorElement_def]
  have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hX hg₂) g₁⁻¹).mp
    (V.inv_mem hg₁)
  have h2 := V.mul_mem hg₁ h1
  simpa [mul_assoc] using h2

namespace Sett

variable (e : Sett T M L t)
include e

theorem L2_le_normalizer_L : CFSG.conjugate L t ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_mem_cComp e.s.mem_cComp e.L2_mem_cComp

theorem L_le_normalizer_L2 : L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
  le_normalizer_of_mem_cComp e.L2_mem_cComp e.s.mem_cComp

theorem L_ne_L2 : L ≠ CFSG.conjugate L t := by
  intro h
  apply e.htn
  have h1 : t⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h.symm
  simpa using Subgroup.inv_mem _ h1

theorem T_le_normalizer_V : T ≤ Subgroup.normalizer (vPlus L T : Set G) :=
  le_sup_right.trans e.hX

theorem swap_conj {s : G} (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    L.map (MulAut.conj s).toMonoidHom = CFSG.conjugate L t ∧
      (CFSG.conjugate L t).map (MulAut.conj s).toMonoidHom = L := by
  have h1 : L.map (MulAut.conj s).toMonoidHom = CFSG.conjugate L t := by
    rcases map_conj_of_setup e.s e.h37 e.h38 e.hT e.ht e.htn
      (Subgroup.mem_sup_right hs) with h | h
    · exact absurd (A38.map_conj_eq_iff.mp h) hsn
    · exact h
  refine ⟨h1, ?_⟩
  have e1 : (CFSG.conjugate L t).map (MulAut.conj s).toMonoidHom =
      L.map (MulAut.conj (s * t⁻¹)).toMonoidHom := by
    unfold CFSG.conjugate
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  rcases map_conj_of_setup e.s e.h37 e.h38 e.hT e.ht e.htn
      (Subgroup.mem_sup_right (T.mul_mem hs (T.inv_mem e.ht))) with h | h
  · rw [e1]
    exact h
  · exfalso
    apply e.L_ne_L2
    have h3 : (CFSG.conjugate L t).map (MulAut.conj s).toMonoidHom =
        L.map (MulAut.conj s).toMonoidHom := by
      rw [e1, h, h1]
    exact (Subgroup.map_injective (f := (MulAut.conj s).toMonoidHom)
      (MulAut.conj s).injective h3).symm

theorem TL_le_normalizer_L2 {s : G} (hs : s ∈ T) (hsL : s ∈ Subgroup.normalizer (L : Set G)) :
    s ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
  rw [← A38.map_conj_eq_iff]
  have e1 : (CFSG.conjugate L t).map (MulAut.conj s).toMonoidHom =
      L.map (MulAut.conj (s * t⁻¹)).toMonoidHom := by
    unfold CFSG.conjugate
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  rcases map_conj_of_setup e.s e.h37 e.h38 e.hT e.ht e.htn
      (Subgroup.mem_sup_right (T.mul_mem hs (T.inv_mem e.ht))) with h | h
  · exfalso
    apply e.L_ne_L2
    have h3 : (CFSG.conjugate L t).map (MulAut.conj s).toMonoidHom =
        L.map (MulAut.conj s).toMonoidHom := by
      rw [e1, h, A38.map_conj_eq_iff.mpr hsL]
    exact (Subgroup.map_injective (f := (MulAut.conj s).toMonoidHom)
      (MulAut.conj s).injective h3).symm
  · rw [e1]
    exact h

theorem card_le_two_mul_TL :
    Nat.card T ≤ 2 * Nat.card ↥(T ⊓ Subgroup.normalizer (L : Set G)) := by
  set TL := T ⊓ Subgroup.normalizer (L : Set G) with hTL
  have hle : TL ≤ T := inf_le_left
  have hidx : (TL.subgroupOf T).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t⁻¹, T.inv_mem e.ht⟩, fun b => ?_⟩
    have hb := b.2
    by_cases hbn : (b : G) ∈ Subgroup.normalizer (L : Set G)
    · have hbTL : b ∈ TL.subgroupOf T := ⟨b.2, hbn⟩
      have hnot : b * ⟨t⁻¹, T.inv_mem e.ht⟩ ∉ TL.subgroupOf T := by
        intro h
        have h1 : (b : G) * t⁻¹ ∈ Subgroup.normalizer (L : Set G) := h.2
        have h2 : t⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hbn) h1
          simpa using this
        apply e.htn
        simpa using Subgroup.inv_mem _ h2
      exact Or.inr ⟨hbTL, hnot⟩
    · have hbn' : (b : G) ∈ T := hb
      obtain ⟨-, h2⟩ := e.swap_conj hbn' hbn
      have hmem : (b : G) * t⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
        rw [← A38.map_conj_eq_iff]
        have : L.map (MulAut.conj ((b : G) * t⁻¹)).toMonoidHom =
            (CFSG.conjugate L t).map (MulAut.conj (b : G)).toMonoidHom := by
          unfold CFSG.conjugate
          rw [Subgroup.map_map]
          congr 1
          ext x
          simp [mul_assoc]
        rw [this, h2]
      have hb2 : b * ⟨t⁻¹, T.inv_mem e.ht⟩ ∈ TL.subgroupOf T :=
        ⟨T.mul_mem hb (T.inv_mem e.ht), hmem⟩
      have hnb : b ∉ TL.subgroupOf T := fun h => hbn h.2
      exact Or.inl ⟨hb2, hnb⟩
  have h1 := Subgroup.card_mul_index (TL.subgroupOf T)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  omega

theorem L_le_N_V1 {x : G} (hx : x ∈ L) :
    x ∈ Subgroup.normalizer (⁅vPlus L T, L⁆ : Subgroup G) :=
  mem_normalizer_commutator (e.hX (Subgroup.mem_sup_left hx)) (Subgroup.le_normalizer hx)

theorem L2_le_N_V1 {x : G} (hx : x ∈ CFSG.conjugate L t) :
    x ∈ Subgroup.normalizer (⁅vPlus L T, L⁆ : Subgroup G) :=
  mem_normalizer_commutator (e.hX (e.L2_le hx)) (e.L2_le_normalizer_L hx)

theorem TL_le_N_V1 {x : G} (hx : x ∈ T ⊓ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer (⁅vPlus L T, L⁆ : Subgroup G) :=
  mem_normalizer_commutator (e.T_le_normalizer_V hx.1) hx.2

theorem L_le_N_V2 {x : G} (hx : x ∈ L) :
    x ∈ Subgroup.normalizer (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) :=
  mem_normalizer_commutator (e.hX (Subgroup.mem_sup_left hx)) (e.L_le_normalizer_L2 hx)

theorem L2_le_N_V2 {x : G} (hx : x ∈ CFSG.conjugate L t) :
    x ∈ Subgroup.normalizer (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) :=
  mem_normalizer_commutator (e.hX (e.L2_le hx)) (Subgroup.le_normalizer hx)

theorem TL_le_N_V2 {x : G} (hx : x ∈ T ⊓ Subgroup.normalizer (L : Set G)) :
    x ∈ Subgroup.normalizer (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) :=
  mem_normalizer_commutator (e.T_le_normalizer_V hx.1) (e.TL_le_normalizer_L2 hx.1 hx.2)

theorem swap_V {s : G} (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (L : Set G)) :
    (⁅vPlus L T, L⁆ : Subgroup G).map (MulAut.conj s).toMonoidHom =
        ⁅vPlus L T, CFSG.conjugate L t⁆ ∧
      (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G).map (MulAut.conj s).toMonoidHom =
        ⁅vPlus L T, L⁆ := by
  obtain ⟨h1, h2⟩ := e.swap_conj hs hsn
  have hV : (vPlus L T).map (MulAut.conj s).toMonoidHom = vPlus L T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (e.T_le_normalizer_V hs)
  rw [Subgroup.map_commutator, Subgroup.map_commutator, hV, h1, h2]
  exact ⟨rfl, rfl⟩

theorem V1_inf_V2
    (htcI : tildeComm L T L ⊓ tildeComm L T (CFSG.conjugate L t) = cvPlus L T)
    (hC : Subgroup.centralizer (mPlus L T : Set G) ⊓ vPlus L T = ⊥) :
    ⁅vPlus L T, L⁆ ⊓ ⁅vPlus L T, CFSG.conjugate L t⁆ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxV : x ∈ vPlus L T :=
    commutator_le_of_le_normalizer (le_sup_left.trans e.hX) hx.1
  have h1 : (⟨x, hxV⟩ : ↥(vPlus L T)) ∈ tildeComm L T L := Subgroup.mem_sup_left hx.1
  have h2 : (⟨x, hxV⟩ : ↥(vPlus L T)) ∈ tildeComm L T (CFSG.conjugate L t) :=
    Subgroup.mem_sup_left hx.2
  have h3 : (⟨x, hxV⟩ : ↥(vPlus L T)) ∈ cvPlus L T := htcI ▸ ⟨h1, h2⟩
  have h4 : x ∈ Subgroup.centralizer (mPlus L T : Set G) := h3
  have h5 : x ∈ (⊥ : Subgroup G) := hC ▸ ⟨h4, hxV⟩
  exact h5

theorem V_eq_sup (hV : vPlus L T = ⁅vPlus L T, mPlus L T⁆) :
    vPlus L T = ⁅vPlus L T, L⁆ ⊔ ⁅vPlus L T, CFSG.conjugate L t⁆ := by
  refine le_antisymm ?_ (sup_le (commutator_le_of_le_normalizer (le_sup_left.trans e.hX))
    (commutator_le_of_le_normalizer (fun x hx => e.hX (e.L2_le hx))))
  conv_lhs => rw [hV]
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have hx' : x ∈ ((mPlus L T : Subgroup G) : Set G) := hx
  rw [e.coe_mPlus] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have h1 : ⁅v, a⁆ ∈ ⁅vPlus L T, CFSG.conjugate L t⁆ := Subgroup.commutator_mem_commutator hv ha
  have h2 : ⁅v, b⁆ ∈ ⁅vPlus L T, L⁆ := Subgroup.commutator_mem_commutator hv hb
  have h3 : a * ⁅v, b⁆ * a⁻¹ ∈ ⁅vPlus L T, L⁆ :=
    (Subgroup.mem_normalizer_iff.mp (e.L2_le_N_V1 ha) _).mp h2
  have e1 : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h3)

theorem L2_centralizes_V1 (hI : ⁅vPlus L T, L⁆ ⊓ ⁅vPlus L T, CFSG.conjugate L t⁆ = ⊥)
    {m v : G} (hm : m ∈ CFSG.conjugate L t) (hv : v ∈ ⁅vPlus L T, L⁆) : m * v = v * m := by
  have hvV : v ∈ vPlus L T := commutator_le_of_le_normalizer (le_sup_left.trans e.hX) hv
  have h1 : ⁅v, m⁆ ∈ ⁅vPlus L T, CFSG.conjugate L t⁆ := Subgroup.commutator_mem_commutator hvV hm
  have h2 : ⁅v, m⁆ ∈ ⁅vPlus L T, L⁆ := by
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.mp (e.L2_le_N_V1 hm) v⁻¹).mp ((⁅vPlus L T, L⁆).inv_mem hv)
    have h3 := Subgroup.mul_mem _ hv (show m * v⁻¹ * m⁻¹ ∈ ⁅vPlus L T, L⁆ from this)
    simpa [mul_assoc] using h3
  have h3 : ⁅v, m⁆ ∈ (⊥ : Subgroup G) := hI ▸ ⟨h2, h1⟩
  rw [Subgroup.mem_bot, commutatorElement_def] at h3
  have h4 : v * m = m * v := by
    calc v * m = (v * m * v⁻¹ * m⁻¹) * (m * v) := by group
      _ = m * v := by rw [h3, one_mul]
  exact h4.symm

theorem L_centralizes_V2 (hI : ⁅vPlus L T, L⁆ ⊓ ⁅vPlus L T, CFSG.conjugate L t⁆ = ⊥)
    {m v : G} (hm : m ∈ L) (hv : v ∈ ⁅vPlus L T, CFSG.conjugate L t⁆) : m * v = v * m := by
  have hvV : v ∈ vPlus L T :=
    commutator_le_of_le_normalizer (fun x hx => e.hX (e.L2_le hx)) hv
  have h1 : ⁅v, m⁆ ∈ ⁅vPlus L T, L⁆ := Subgroup.commutator_mem_commutator hvV hm
  have h2 : ⁅v, m⁆ ∈ ⁅vPlus L T, CFSG.conjugate L t⁆ := by
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.mp (e.L_le_N_V2 hm) v⁻¹).mp
      ((⁅vPlus L T, CFSG.conjugate L t⁆).inv_mem hv)
    have h3 := Subgroup.mul_mem _ hv (show m * v⁻¹ * m⁻¹ ∈ ⁅vPlus L T, CFSG.conjugate L t⁆ from this)
    simpa [mul_assoc] using h3
  have h3 : ⁅v, m⁆ ∈ (⊥ : Subgroup G) := hI ▸ ⟨h1, h2⟩
  rw [Subgroup.mem_bot, commutatorElement_def] at h3
  have h4 : v * m = m * v := by
    calc v * m = (v * m * v⁻¹ * m⁻¹) * (m * v) := by group
      _ = m * v := by rw [h3, one_mul]
  exact h4.symm

theorem exists_e [IsMulCommutative ↥(vPlus L T)] (hV2 : ∀ x ∈ vPlus L T, x ^ 2 = 1)
    (hVs : vPlus L T = ⁅vPlus L T, L⁆ ⊔ ⁅vPlus L T, CFSG.conjugate L t⁆)
    (hI : ⁅vPlus L T, L⁆ ⊓ ⁅vPlus L T, CFSG.conjugate L t⁆ = ⊥)
    {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    ∃ e₀ : G, e₀ ∈ ⁅vPlus L T, L⁆ ∧ e₀ ≠ 1 ∧ e₀ ^ 2 = 1 ∧
      (∀ s ∈ T ⊓ Subgroup.normalizer (L : Set G), s * e₀ = e₀ * s) ∧
      (∀ m ∈ CFSG.conjugate L t, m * e₀ = e₀ * m) ∧
      (∀ s ∈ T, s * e₀ = e₀ * s → s ∈ Subgroup.normalizer (L : Set G)) := by
  have hVcomm : ∀ a ∈ vPlus L T, ∀ b ∈ vPlus L T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative ↥(vPlus L T)).is_comm.comm
      (⟨a, ha⟩ : ↥(vPlus L T)) ⟨b, hb⟩)
  have hV1V : ⁅vPlus L T, L⁆ ≤ vPlus L T :=
    commutator_le_of_le_normalizer (le_sup_left.trans e.hX)
  have hV2V : ⁅vPlus L T, CFSG.conjugate L t⁆ ≤ vPlus L T :=
    commutator_le_of_le_normalizer (fun x hx => e.hX (e.L2_le hx))
  have hzV : z ∈ vPlus L T := le_conjClosure _ _ hz
  have hzT : ∀ s ∈ T, s * z = z * s := fun s hs =>
    ((Subgroup.mem_centralizer_iff.mp
      (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T hs) z hz)).symm
  have hN : ⁅vPlus L T, L⁆ ≤
      Subgroup.normalizer ((⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hVcomm x (hV1V hx) y (hV2V hy)).symm
  have hzmem : z ∈ ((⁅vPlus L T, L⁆ ⊔ ⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
    rw [← hVs]
    exact hzV
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hzmem
  obtain ⟨v₁, hv₁, v₂, hv₂, hzv0⟩ := hzmem
  have hzv : v₁ * v₂ = z := hzv0
  have hv₁V := hV1V hv₁
  have hv₂V := hV2V hv₂
  obtain ⟨hs1, hs2⟩ := e.swap_V e.ht e.htn
  have hv1 : v₁ ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hzv
    have hz' : t * v₂ * t⁻¹ = v₂ := by
      have := hzT t e.ht
      rw [← hzv] at this
      exact mul_inv_eq_iff_eq_mul.mpr this
    have hmem : t * v₂ * t⁻¹ ∈ ⁅vPlus L T, L⁆ := by
      have h3 : (MulAut.conj t).toMonoidHom v₂ ∈
          (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hv₂
      rw [hs2] at h3
      simpa using h3
    have : v₂ ∈ (⊥ : Subgroup G) := hI ▸ ⟨hz' ▸ hmem, hv₂⟩
    apply hz1
    rw [← hzv]
    exact Subgroup.mem_bot.mp this
  refine ⟨v₁, hv₁, hv1, hV2 v₁ hv₁V, ?_, fun m hm => e.L2_centralizes_V1 hI hm hv₁, ?_⟩
  · intro s hs
    have hsV1 := e.TL_le_N_V1 hs
    have hsV2 := e.TL_le_N_V2 hs
    set a := s * v₁ * s⁻¹ with ha
    set b := s * v₂ * s⁻¹ with hb
    have haV1 : a ∈ ⁅vPlus L T, L⁆ := (Subgroup.mem_normalizer_iff.mp hsV1 v₁).mp hv₁
    have hbV2 : b ∈ ⁅vPlus L T, CFSG.conjugate L t⁆ :=
      (Subgroup.mem_normalizer_iff.mp hsV2 v₂).mp hv₂
    have hab : a * b = v₁ * v₂ := by
      have h1 : s * (v₁ * v₂) * s⁻¹ = a * b := by rw [ha, hb]; group
      have h2 : s * (v₁ * v₂) * s⁻¹ = v₁ * v₂ := by
        have := hzT s hs.1
        rw [← hzv] at this
        exact mul_inv_eq_iff_eq_mul.mpr this
      rw [← h1, h2]
    have h3 : v₁⁻¹ * a = v₂ * b⁻¹ := by
      calc v₁⁻¹ * a = v₁⁻¹ * (a * b) * b⁻¹ := by group
        _ = v₂ * b⁻¹ := by rw [hab]; group
    have h4 : v₁⁻¹ * a ∈ (⊥ : Subgroup G) := hI ▸ ⟨(⁅vPlus L T, L⁆).mul_mem
      ((⁅vPlus L T, L⁆).inv_mem hv₁) haV1, h3 ▸ (⁅vPlus L T, CFSG.conjugate L t⁆).mul_mem hv₂
      ((⁅vPlus L T, CFSG.conjugate L t⁆).inv_mem hbV2)⟩
    rw [Subgroup.mem_bot, inv_mul_eq_one] at h4
    rw [ha] at h4
    exact mul_inv_eq_iff_eq_mul.mp h4.symm
  · intro s hs hsc
    by_contra hsn
    obtain ⟨h1, -⟩ := e.swap_V hs hsn
    have h2 : (MulAut.conj s).toMonoidHom v₁ ∈
        (⁅vPlus L T, L⁆ : Subgroup G).map (MulAut.conj s).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hv₁
    rw [h1] at h2
    have h3 : s * v₁ * s⁻¹ = v₁ := mul_inv_eq_iff_eq_mul.mpr hsc
    have h4 : v₁ ∈ ⁅vPlus L T, CFSG.conjugate L t⁆ := by simpa [h3] using h2
    have : v₁ ∈ (⊥ : Subgroup G) := hI ▸ ⟨hv₁, h4⟩
    exact hv1 (Subgroup.mem_bot.mp this)

end Sett

end CFSG.Quasithin.H13.Ins314
