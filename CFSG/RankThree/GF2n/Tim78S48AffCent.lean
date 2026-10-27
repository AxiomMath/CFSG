module

public import CFSG.RankThree.GF2n.Tim78S48AffBasic
import CFSG.RankThree.GF2n.Tim78S48AffBor
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

open Aff

namespace Aff

theorem comm_mem_kernel {X W : Subgroup G}
    (hXW : X ≤ Subgroup.normalizer (W : Set G))
    {d : G} (hdN : d ∈ Subgroup.normalizer (X : Set G)) (hd : ∀ w ∈ W, d * w = w * d)
    {x : G} (hx : x ∈ X) : d * x * d⁻¹ * x⁻¹ ∈ X ⊓ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_inf]
  refine ⟨X.mul_mem ((Subgroup.mem_normalizer_iff.mp hdN x).mp hx) (X.inv_mem hx), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : x⁻¹ * w * x ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (hXW (X.inv_mem hx)) w).mp hw
    simpa using this
  have hw'd : d⁻¹ * (x⁻¹ * w * x) * d = x⁻¹ * w * x := by
    have := hd _ hw'
    calc d⁻¹ * (x⁻¹ * w * x) * d = d⁻¹ * ((x⁻¹ * w * x) * d) := by group
      _ = d⁻¹ * (d * (x⁻¹ * w * x)) := by rw [this]
      _ = x⁻¹ * w * x := by group
  have hwd : d * w * d⁻¹ = w := by
    have := hd w hw
    calc d * w * d⁻¹ = (w * d) * d⁻¹ := by rw [this]
      _ = w := by group
  have key : (d * x * d⁻¹ * x⁻¹) * w * (d * x * d⁻¹ * x⁻¹)⁻¹ = w := by
    calc (d * x * d⁻¹ * x⁻¹) * w * (d * x * d⁻¹ * x⁻¹)⁻¹
        = d * x * (d⁻¹ * (x⁻¹ * w * x) * d) * x⁻¹ * d⁻¹ := by group
      _ = d * x * (x⁻¹ * w * x) * x⁻¹ * d⁻¹ := by rw [hw'd]
      _ = d * w * d⁻¹ := by group
      _ = w := hwd
  exact (mul_inv_eq_iff_eq_mul.mp key).symm

end Aff

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H


theorem exists_comm_eq_T (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hrel : (T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).relIndex T =
      Nat.card B)
    {y : G} (hy : y ∈ conjSubgroup g B) (hy1 : y ≠ 1) {β : G} (hβ : β ∈ B) :
    ∃ t ∈ T, ⁅y, t⁆ = β := by
  classical
  have hTB : ∀ t ∈ T, ⁅y, t⁆ ∈ B := fun t ht => h48.comm_T y hy t ht
  let τ : T →* B :=
    { toFun := fun t => ⟨⁅y, (t : G)⁆, hTB t t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun t t' => by
        refine Subtype.ext ?_
        have hc : (t : G) * ⁅y, (t' : G)⁆ = ⁅y, (t' : G)⁆ * (t : G) :=
          H.T_comm_B t.2 (hTB t' t'.2)
        show ⁅y, (t : G) * (t' : G)⁆ = ⁅y, (t : G)⁆ * ⁅y, (t' : G)⁆
        rw [show ⁅y, (t : G) * (t' : G)⁆ =
          ⁅y, (t : G)⁆ * ((t : G) * ⁅y, (t' : G)⁆ * (t : G)⁻¹) by
            simp only [commutatorElement_def]; group, hc]
        group }
  have hker : τ.ker = (T ⊓ Subgroup.centralizer
      ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h1 : ⁅y, (t : G)⁆ = 1 := congrArg Subtype.val h
      refine ⟨t.2, ?_⟩
      have hbt : y * (t : G) = (t : G) * y := commutatorElement_eq_one_iff_mul_comm.mp h1
      have hMg : (t : G) ∈ conjSubgroup g M :=
        H.centralizer_le_conj hy hy1 (Subgroup.mem_centralizer_singleton_iff.mpr hbt.symm)
      have hnorm : (t : G) ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
        rw [H.normalizer_conj_eq g]; exact hMg
      have hBg : ∀ z ∈ conjSubgroup g B, z * (t : G) = (t : G) * z := by
        intro z hz
        have h2 : ⁅z, (t : G)⁆ ∈ conjSubgroup g B := by
          have e : ⁅z, (t : G)⁆ = z * ((t : G) * z⁻¹ * (t : G)⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (conjSubgroup g B).mul_mem hz
            ((Subgroup.mem_normalizer_iff.mp hnorm z⁻¹).mp ((conjSubgroup g B).inv_mem hz))
        have h3 : ⁅z, (t : G)⁆ ∈ B := h48.comm_T z hz t t.2
        have h4 : ⁅z, (t : G)⁆ ∈ B ⊓ conjSubgroup g B := ⟨h3, h2⟩
        rw [H.B_inf_Bg hP, Subgroup.mem_bot] at h4
        exact commutatorElement_eq_one_iff_mul_comm.mp h4
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_of_mem_sup
        (le_normalizer_of_comm fun x hx y hy => (H.commute_of_conj_le_M h48.leM y hy x hx).symm) hw
      calc b * z * (t : G) = b * (z * (t : G)) := by group
        _ = b * ((t : G) * z) := by rw [hBg z hz]
        _ = (b * (t : G)) * z := by group
        _ = ((t : G) * b) * z := by rw [H.T_comm_B t.2 hb]
        _ = (t : G) * (b * z) := by group
    · rintro ⟨-, h⟩
      refine Subtype.ext ?_
      have := Subgroup.mem_centralizer_iff.mp h y (Subgroup.mem_sup_right hy)
      exact commutatorElement_eq_one_iff_mul_comm.mpr this
  have hrange : τ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 := Subgroup.index_ker τ
    rw [hker] at h1
    have h2 : ((T ⊓ Subgroup.centralizer
        ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).subgroupOf T).index = Nat.card B := hrel
    rw [h2] at h1
    exact h1.symm
  have hmem : (⟨β, hβ⟩ : B) ∈ τ.range := by rw [hrange]; trivial
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, t.2, congrArg Subtype.val ht⟩


theorem conj_B_ne_bot (g : G) : conjSubgroup g B ≠ ⊥ := by
  intro h
  apply H.B_ne_bot
  apply Subgroup.eq_bot_of_card_eq
  have := card_conjSubgroup g B
  rw [h, Subgroup.card_bot] at this
  exact this.symm

theorem exists_conj_T_of_ne (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hrel : (T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).relIndex T =
      Nat.card B)
    {U : Subgroup G} (hU : U ∈ classIn B (B ⊔ conjSubgroup g B)) (hUB : U ≠ B) :
    ∃ t ∈ T, U = conjSubgroup t (conjSubgroup g B) := by
  obtain ⟨⟨r, rfl⟩, hUW⟩ := hU
  obtain ⟨⟨y₀, hy₀⟩, hy₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (H.conj_B_ne_bot g)
  have hy1 : y₀ ≠ 1 := fun h => hy₀1 (Subtype.ext h)
  have hrB : B ⊓ conjSubgroup r B = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hUB
  have hWel := H.W_elem h48
  have hcommW : ∀ a ∈ B ⊔ conjSubgroup g B, ∀ b ∈ B ⊔ conjSubgroup g B, a * b = b * a :=
    fun a ha b hb => comm_of_isElemAbelian hWel ha hb
  have hnorm : conjSubgroup r B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun x hx y hy => hcommW x (hUW hx) y (Subgroup.mem_sup_left hy)
  have hcard := PartTwo.Sec6.card_sup_mul_card_inf hnorm
  rw [inf_comm, hrB, Subgroup.card_bot, mul_one, card_conjSubgroup] at hcard
  have hsup : conjSubgroup r B ⊔ B = B ⊔ conjSubgroup g B := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hUW le_sup_left) ?_
    rw [H.card_W h48 hP, hcard, sq]
  have hy₀W : y₀ ∈ conjSubgroup r B ⊔ B := by rw [hsup]; exact Subgroup.mem_sup_right hy₀
  obtain ⟨u, hu, b, hb, hub⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => hcommW x (Subgroup.mem_sup_left hx) y (hUW hy)) hy₀W
  obtain ⟨t, ht, htb⟩ := H.exists_comm_eq_T h48 hP hrel hy₀ hy1 hb
  have hty : t * y₀ * t⁻¹ = u := by
    have e1 : t * y₀ * t⁻¹ = (⁅y₀, t⁆)⁻¹ * y₀ := by simp only [commutatorElement_def]; group
    have hub' : u * b = b * u := hcommW u (hUW hu) b (Subgroup.mem_sup_left hb)
    rw [e1, htb, hub]
    calc b⁻¹ * (u * b) = b⁻¹ * (b * u) := by rw [hub']
      _ = u := by group
  have hu1 : u ≠ 1 := by
    intro h
    apply hy1
    have : t * y₀ * t⁻¹ = 1 := by rw [hty, h]
    simpa using this
  refine ⟨t, ht, ?_⟩
  have hu2 : u ∈ conjSubgroup (t * g) B := by
    rw [conjSubgroup_mul, ← hty]
    exact mem_conj_iff.mpr ⟨y₀, hy₀, rfl⟩
  have := H.conj_B_eq_of_inf_ne_bot (z := r) (z' := t * g) (by
    intro hbot
    have hh : u ∈ conjSubgroup r B ⊓ conjSubgroup (t * g) B := ⟨hu, hu2⟩
    rw [hbot, Subgroup.mem_bot] at hh
    exact hu1 hh)
  rw [this, conjSubgroup_mul]


theorem conj_mem_classIn_aC (h48 : Hyp48 M B T g) {c : G} (hc : c ∈ H.aC g) :
    conjSubgroup c (conjSubgroup g B) ∈ classIn B (B ⊔ conjSubgroup g B) := by
  refine ⟨⟨c * g, (conjSubgroup_mul c g B).symm⟩, ?_⟩
  have : conjSubgroup c (conjSubgroup g B) ≤ conjSubgroup c (B ⊔ conjSubgroup g B) :=
    Subgroup.map_mono le_sup_right
  rwa [conjSubgroup_eq_self_iff.mpr (H.aC_le_normalizer_W h48 hc)] at this

theorem exists_t₀ (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hrel : (T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).relIndex T =
      Nat.card B)
    {c : G} (hc : c ∈ H.aC g) :
    ∃ t₀ ∈ T, conjSubgroup c (conjSubgroup g B) = conjSubgroup t₀ (conjSubgroup g B) := by
  have hU := H.conj_mem_classIn_aC h48 hc
  have hne : conjSubgroup c (conjSubgroup g B) ≠ B := by
    intro h
    apply H.Bg_ne hP
    have : conjSubgroup g B = conjSubgroup c⁻¹ B := by
      have h2 : conjSubgroup c⁻¹ (conjSubgroup c (conjSubgroup g B)) = conjSubgroup c⁻¹ B := by
        rw [h]
      rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h2
    rw [this]
    exact conjSubgroup_eq_self_iff.mpr (H.M_le_normalizer_B (inv_mem (H.aC_le_M hc)))
  exact H.exists_conj_T_of_ne h48 hP hrel hU hne

theorem conj_pt_eq (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hrel : (T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).relIndex T =
      Nat.card B)
    {c t₀ : G} (hc : c ∈ H.aC g) (ht₀ : t₀ ∈ T)
    (hct : conjSubgroup c (conjSubgroup g B) = conjSubgroup t₀ (conjSubgroup g B))
    {U : Subgroup G} (hU : U ∈ classIn B (B ⊔ conjSubgroup g B)) :
    conjSubgroup c U = conjSubgroup t₀ U := by
  by_cases hUB : U = B
  · subst hUB
    rw [conjSubgroup_eq_self_iff.mpr (H.M_le_normalizer_B (H.aC_le_M hc)),
      conjSubgroup_eq_self_iff.mpr (H.M_le_normalizer_B (H.Q_le_M (H.T_le_Q ht₀)))]
  obtain ⟨t, ht, rfl⟩ := H.exists_conj_T_of_ne h48 hP hrel hU hUB
  have hct' : c * t = t * c := Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) c hc.1
  have e1 : conjSubgroup c (conjSubgroup t (conjSubgroup g B)) =
      conjSubgroup t (conjSubgroup t₀ (conjSubgroup g B)) := by
    rw [← conjSubgroup_mul, hct', conjSubgroup_mul, hct]
  have hm : ⁅t₀⁻¹, t⁻¹⁆ ∈ B :=
    H.commutator_mem (H.T_le_Q (T.inv_mem ht₀)) (H.T_le_Q (T.inv_mem ht))
  have hBS : B ≤ Subgroup.normalizer (conjSubgroup g B : Set G) :=
    le_normalizer_of_comm fun x hx y hy => H.commute_of_conj_le_M h48.leM x hx y hy
  have e2 : conjSubgroup t₀ (conjSubgroup t (conjSubgroup g B)) =
      conjSubgroup t (conjSubgroup t₀ (conjSubgroup g B)) := by
    have this : t₀ * t = (t * t₀) * ⁅t₀⁻¹, t⁻¹⁆ := by simp only [commutatorElement_def]; group
    have h1 : conjSubgroup t₀ (conjSubgroup t (conjSubgroup g B)) =
        conjSubgroup (t₀ * t) (conjSubgroup g B) := (conjSubgroup_mul t₀ t _).symm
    have h2 : conjSubgroup t (conjSubgroup t₀ (conjSubgroup g B)) =
        conjSubgroup (t * t₀) (conjSubgroup g B) := (conjSubgroup_mul t t₀ _).symm
    rw [h1, h2, this, conjSubgroup_mul (t * t₀) ⁅t₀⁻¹, t⁻¹⁆ (conjSubgroup g B),
      conjSubgroup_eq_self_iff.mpr (hBS hm)]
  rw [e1, ← e2]

theorem conj_fix_B {c t₀ : G} (hc : c ∈ P) (ht₀ : t₀ ∈ T) :
    ∀ b ∈ B, (t₀⁻¹ * c) * b * (t₀⁻¹ * c)⁻¹ = b := by
  intro b hb
  have h1 : c * b = b * c := (H.center_Q hb (H.P_le_Q hc)).symm
  have h2 : t₀⁻¹ * b = b * t₀⁻¹ := H.T_comm_B (T.inv_mem ht₀) hb
  calc (t₀⁻¹ * c) * b * (t₀⁻¹ * c)⁻¹ = t₀⁻¹ * (c * b) * c⁻¹ * t₀ := by group
    _ = t₀⁻¹ * (b * c) * c⁻¹ * t₀ := by rw [h1]
    _ = (t₀⁻¹ * b) * t₀ := by group
    _ = (b * t₀⁻¹) * t₀ := by rw [h2]
    _ = b := by group

theorem aC_conj_cent (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hrel : (T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)).relIndex T =
      Nat.card B)
    (hpart : ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
      ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U)
    {c t₀ : G} (hc : c ∈ H.aC g) (ht₀ : t₀ ∈ T)
    (hct : conjSubgroup c (conjSubgroup g B) = conjSubgroup t₀ (conjSubgroup g B)) :
    ∀ y ∈ conjSubgroup g B, (t₀⁻¹ * c) * y * (t₀⁻¹ * c)⁻¹ = y := by
  have hpt : ∀ U ∈ classIn B (B ⊔ conjSubgroup g B), conjSubgroup (t₀⁻¹ * c) U = U := by
    intro U hU
    rw [conjSubgroup_mul, H.conj_pt_eq h48 hP hrel hc ht₀ hct hU, ← conjSubgroup_mul,
      inv_mul_cancel, conjSubgroup_one]
  have hB := H.conj_fix_B hc.1 ht₀
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]; group
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp H.B_ne_bot
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hw : b * y ∈ B ⊔ conjSubgroup g B :=
    (B ⊔ conjSubgroup g B).mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hy)
  have hw1 : b * y ≠ 1 := by
    intro h
    apply hb1'
    have hbB : b = y⁻¹ := eq_inv_of_mul_eq_one_left h
    have : b ∈ B ⊓ conjSubgroup g B := ⟨hb, by rw [hbB]; exact (conjSubgroup g B).inv_mem hy⟩
    rw [H.B_inf_Bg hP] at this
    exact Subgroup.mem_bot.mp this
  obtain ⟨U, ⟨hUcls, hwU⟩, -⟩ := hpart _ hw hw1
  have hBg : conjSubgroup (t₀⁻¹ * c) (conjSubgroup g B) = conjSubgroup g B :=
    hpt _ ⟨⟨g, rfl⟩, le_sup_right⟩
  have hy' : (t₀⁻¹ * c) * y * (t₀⁻¹ * c)⁻¹ ∈ conjSubgroup g B := by
    rw [← hBg]; exact mem_conj_iff.mpr ⟨y, hy, rfl⟩
  have hU' : (t₀⁻¹ * c) * (b * y) * (t₀⁻¹ * c)⁻¹ ∈ U := by
    rw [← hpt U hUcls]; exact mem_conj_iff.mpr ⟨_, hwU, rfl⟩
  have e : (t₀⁻¹ * c) * (b * y) * (t₀⁻¹ * c)⁻¹ = b * ((t₀⁻¹ * c) * y * (t₀⁻¹ * c)⁻¹) := by
    calc (t₀⁻¹ * c) * (b * y) * (t₀⁻¹ * c)⁻¹
        = ((t₀⁻¹ * c) * b * (t₀⁻¹ * c)⁻¹) * ((t₀⁻¹ * c) * y * (t₀⁻¹ * c)⁻¹) := by group
      _ = _ := by rw [hB b hb]
  rw [e] at hU'
  have hq : y⁻¹ * ((t₀⁻¹ * c) * y * (t₀⁻¹ * c)⁻¹) ∈ U := by
    have := U.mul_mem (U.inv_mem hwU) hU'
    simpa [mul_assoc] using this
  have hq2 : y⁻¹ * ((t₀⁻¹ * c) * y * (t₀⁻¹ * c)⁻¹) ∈ conjSubgroup g B :=
    (conjSubgroup g B).mul_mem ((conjSubgroup g B).inv_mem hy) hy'
  have hUne : U ⊓ conjSubgroup g B = ⊥ := by
    by_contra hne
    obtain ⟨⟨r, rfl⟩, -⟩ := hUcls
    have hU2 : conjSubgroup r B = conjSubgroup g B := H.conj_B_eq_of_inf_ne_bot hne
    rw [hU2] at hwU
    have hbBg : b ∈ conjSubgroup g B := by
      have := (conjSubgroup g B).mul_mem hwU ((conjSubgroup g B).inv_mem hy)
      simpa using this
    have : b ∈ B ⊓ conjSubgroup g B := ⟨hb, hbBg⟩
    rw [H.B_inf_Bg hP] at this
    exact hb1' (Subgroup.mem_bot.mp this)
  have : y⁻¹ * ((t₀⁻¹ * c) * y * (t₀⁻¹ * c)⁻¹) ∈ U ⊓ conjSubgroup g B := ⟨hq, hq2⟩
  rw [hUne, Subgroup.mem_bot] at this
  exact (inv_mul_eq_one.mp this).symm


theorem aC_le_normalizer_K (h48 : Hyp48 M B T g)
    (htrans : ∀ U ∈ classIn B (B ⊔ conjSubgroup g B),
      ∃ h ∈ T ⊔ conjSubgroup g T, U = conjSubgroup h B) :
    H.aC g ≤ Subgroup.normalizer (kernel48 B T g : Set G) := fun c hc =>
  mem_normalizer_inf (H.aC_le_normalizer_X h48 htrans hc)
    (mem_normalizer_centralizer (H.aC_le_normalizer_W h48 hc))

theorem aC_cent (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) (h1 : Phase1 B T g) :
    ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c := by
  obtain ⟨n, hn, hnat, hpart, htrans, hKel, hKform, hWA, hA, hcomm, hrel, K₁, hK₁X, hK₁B,
    hK₁Bg, hK₁cyc, hK₁card, hK₁A, hK₁fpf, hK₁pts⟩ := h1
  intro c hc y hy
  obtain ⟨t₀, ht₀, hct⟩ := H.exists_t₀ h48 hP hrel hc
  have hcent' := H.aC_conj_cent h48 hP hrel hpart hc ht₀ hct
  have hfixB := H.conj_fix_B hc.1 ht₀
  have key : ∀ w ∈ B ⊔ conjSubgroup g B, t₀ * w = w * t₀ := by
    by_contra hnc
    have hcX := H.aC_le_normalizer_X h48 htrans hc
    have hcK := H.aC_le_normalizer_K h48 htrans hc
    have hcW := H.aC_le_normalizer_W h48 hc
    have hn2 : 2 ≤ n := by
      have h4 := H.q4
      rw [hn] at h4
      by_contra hlt
      interval_cases n <;> simp at h4
    have hAK : T ⊓ conjSubgroup g T ≤
        (T ⊔ conjSubgroup g T) ⊓
          Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
      rw [hKform]; exact le_sup_right
    set E : Subgroup G :=
      (T ⊔ conjSubgroup g T) ⊓ Subgroup.centralizer ((T ⊓ conjSubgroup g T : Subgroup G) : Set G)
      with hE
    have hKE : (T ⊔ conjSubgroup g T) ⊓
        Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) ≤ E := by
      intro k hk
      refine ⟨hk.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact comm_of_isElemAbelian hKel (hAK ha) hk
    have hK₁E : K₁ ≤ E := fun x hx => ⟨hK₁X hx, hK₁A hx⟩
    have hc'W : ∀ w ∈ B ⊔ conjSubgroup g B, (t₀⁻¹ * c) * w * (t₀⁻¹ * c)⁻¹ = w := by
      intro w hw
      obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_of_mem_sup
        (le_normalizer_of_comm fun x hx y hy =>
          (H.commute_of_conj_le_M h48.leM y hy x hx).symm) hw
      calc (t₀⁻¹ * c) * (b * z) * (t₀⁻¹ * c)⁻¹
          = ((t₀⁻¹ * c) * b * (t₀⁻¹ * c)⁻¹) * ((t₀⁻¹ * c) * z * (t₀⁻¹ * c)⁻¹) := by group
        _ = b * z := by rw [hfixB b hb, hcent' z hz]
    have hd : ∀ w ∈ B ⊔ conjSubgroup g B, (t₀⁻¹ * c)⁻¹ * w = w * (t₀⁻¹ * c)⁻¹ := by
      intro w hw
      have := hc'W w hw
      calc (t₀⁻¹ * c)⁻¹ * w = (t₀⁻¹ * c)⁻¹ * (((t₀⁻¹ * c) * w * (t₀⁻¹ * c)⁻¹)) := by rw [this]
        _ = w * (t₀⁻¹ * c)⁻¹ := by group
    have hc'N : (t₀⁻¹ * c)⁻¹ ∈ Subgroup.normalizer ((T ⊔ conjSubgroup g T : Subgroup G) : Set G) :=
      inv_mem (mul_mem (inv_mem (Subgroup.le_normalizer (Subgroup.mem_sup_left ht₀))) hcX)
    have ht₀E : ∀ x ∈ K₁, t₀ * x * t₀⁻¹ ∈ E := by
      intro x hx
      have hk₀ := comm_mem_kernel (H.X_le_normalizer_W h48) hc'N hd (hK₁X hx)
      have e : t₀ * x * t₀⁻¹ = (c * ((t₀⁻¹ * c)⁻¹ * x * (t₀⁻¹ * c)⁻¹⁻¹ * x⁻¹) * c⁻¹) *
          (c * x * c⁻¹) := by group
      rw [e]
      refine E.mul_mem (hKE ?_) ⟨(Subgroup.mem_normalizer_iff.mp hcX x).mp (hK₁X hx), ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hcK _).mp hk₀
      · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
        have hca : c * a = a * c := (Subgroup.mem_centralizer_iff.mp
          (H.T_le_centralizer_P ha.1) c hc.1)
        have hxa : x * a = a * x := (Subgroup.mem_centralizer_iff.mp (hK₁A hx) a ha).symm
        calc a * (c * x * c⁻¹) = (a * c) * x * c⁻¹ := by group
          _ = (c * a) * x * c⁻¹ := by rw [hca]
          _ = c * (a * x) * c⁻¹ := by group
          _ = c * (x * a) * c⁻¹ := by rw [hxa]
          _ = (c * x * c⁻¹) * (c * a * c⁻¹) := by group
          _ = (c * x * c⁻¹) * (a * c * c⁻¹) := by rw [hca]
          _ = (c * x * c⁻¹) * a := by group
    have hTE : T ≤ E :=
      torus_conj_generates (n := n) hn2 hnat le_sup_left H.B_ne_bot
        le_sup_left (fun t ht b hb => H.T_comm_B ht hb)
        hK₁X hK₁B (by rw [hK₁card, hn]) hK₁fpf inf_le_left hKE hK₁E ht₀ hnc ht₀E
    apply hA
    rw [eq_bot_iff]
    intro a ha
    have haC : a ∈ Q ⊓ Subgroup.centralizer (T : Set G) :=
      ⟨H.T_le_Q ha.1, Subgroup.mem_centralizer_iff.mpr fun t ht =>
        ((Subgroup.mem_centralizer_iff.mp (hTE ht).2 a ha).symm)⟩
    rw [H.inf_centralizer_T_eq_P] at haC
    have haB : a ∈ B := by
      have : a ∈ P ⊓ T := ⟨haC, ha.1⟩
      rwa [H.P_inf_T] at this
    have : a ∈ (B ⊔ conjSubgroup g B) ⊓ (T ⊓ conjSubgroup g T) :=
      ⟨Subgroup.mem_sup_left haB, ha⟩
    rw [hWA] at this
    exact this
  have hy' := hcent' y hy
  have hty : t₀ * y * t₀⁻¹ = y := by
    have := key y (Subgroup.mem_sup_right hy)
    calc t₀ * y * t₀⁻¹ = (y * t₀) * t₀⁻¹ := by rw [this]
      _ = y := by group
  have : c * y * c⁻¹ = y := by
    calc c * y * c⁻¹ = t₀ * ((t₀⁻¹ * c) * y * (t₀⁻¹ * c)⁻¹) * t₀⁻¹ := by group
      _ = t₀ * y * t₀⁻¹ := by rw [hy']
      _ = y := hty
  exact (mul_inv_eq_iff_eq_mul.mp this)


end Hyp4

end CFSG.RankThree.GF2n.Tim78
