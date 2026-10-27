module

public import CFSG.RankThree.GF2n.Tim78S48Defs
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.RankThree.GF2n.Tim78P210Basic
public import CFSG.RankThree.GF2n.Tim78S45Aux

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

theorem side_centralizer {D E S : Subgroup G} (hDE : D ⊓ E = ⊥)
    (hcomm : ∀ a ∈ D, ∀ b ∈ E, a * b = b * a)
    (hSD : ∀ t ∈ S, ∀ a ∈ D, t * a = a * t)
    (hSE : ∀ b ∈ E, ∀ t ∈ S, ⁅b, t⁆ ∈ D)
    (hcent : ∀ b ∈ E, b ≠ 1 → ∀ c : G, c * b = b * c → c ∈ Subgroup.normalizer (E : Set G))
    {t : G} (ht : t ∈ S) (hnc : ¬ ∀ b ∈ E, t * b = b * t) :
    ∀ w ∈ D ⊔ E, t * w = w * t → w ∈ D := by
  intro w hw htw
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => (hcomm y hy x hx).symm) hw
  have hta := hSD t ht a ha
  have htb : t * b = b * t := by
    have h1 : a * (t * b) = a * (b * t) := by
      calc a * (t * b) = t * (a * b) := by rw [← mul_assoc, ← hta, mul_assoc]
        _ = a * b * t := htw
        _ = a * (b * t) := by rw [mul_assoc]
    exact mul_left_cancel h1
  by_cases hb1 : b = 1
  · rw [hb1, mul_one]
    exact ha
  exfalso
  apply hnc
  have htE : t ∈ Subgroup.normalizer (E : Set G) := hcent b hb hb1 t htb
  intro c hc
  have h1 : ⁅c, t⁆ ∈ D := hSE c hc t ht
  have h2 : ⁅c, t⁆ ∈ E := by
    have e : ⁅c, t⁆ = c * (t * c⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact E.mul_mem hc ((Subgroup.mem_normalizer_iff.mp htE c⁻¹).mp (E.inv_mem hc))
  have h3 : ⁅c, t⁆ ∈ D ⊓ E := ⟨h1, h2⟩
  rw [hDE, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3.symm

theorem le_normalizer_sup_of_comm {D E S : Subgroup G} [Finite G]
    (hcomm : ∀ a ∈ D, ∀ b ∈ E, a * b = b * a)
    (hSD : ∀ t ∈ S, ∀ a ∈ D, t * a = a * t) (hSE : ∀ b ∈ E, ∀ t ∈ S, ⁅b, t⁆ ∈ D) :
    S ≤ Subgroup.normalizer ((D ⊔ E : Subgroup G) : Set G) := by
  intro t ht
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => (hcomm y hy x hx).symm) hw
  have h1 : t * a * t⁻¹ = a := by rw [hSD t ht a ha, mul_inv_cancel_right]
  have h2 : t * b * t⁻¹ = (⁅b, t⁆)⁻¹ * b := by
    simp only [commutatorElement_def]; group
  have e : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
  rw [e, h1, h2]
  exact (D ⊔ E).mul_mem (Subgroup.mem_sup_left ha) ((D ⊔ E).mul_mem
    ((D ⊔ E).inv_mem (Subgroup.mem_sup_left (hSE b hb t ht))) (Subgroup.mem_sup_right hb))

theorem le_normalizer_kernelGen {S S' K : Subgroup G} [Finite G]
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hS'K : S' ≤ Subgroup.normalizer (K : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ Subgroup.normalizer (((S ⊓ K) ⊔ (S' ⊓ K) : Subgroup G) : Set G) := by
  intro s hs
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hS'S : S' ⊓ K ≤ Subgroup.normalizer ((S ⊓ K : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_inf (hKS hy.2) (hS'K hy.1)
  obtain ⟨a, ha, y, hy, rfl⟩ := exists_mul_of_mem_sup hS'S hx
  have e : s * (a * y) * s⁻¹ = (s * a * s⁻¹) * (⁅s, y⁆ * y) := by
    simp only [commutatorElement_def]; group
  have h1 : s * a * s⁻¹ ∈ S ⊓ K := (Subgroup.mem_normalizer_iff.mp
    (mem_normalizer_inf (Subgroup.le_normalizer hs) (hSK hs)) a).mp ha
  have h2 : ⁅s, y⁆ ∈ S ⊓ K := by
    refine ⟨?_, ?_⟩
    · have : ⁅s, y⁆ = s * (y * s⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact S.mul_mem hs ((Subgroup.mem_normalizer_iff.mp (hKS hy.2) s⁻¹).mp (S.inv_mem hs))
    · have : ⁅s, y⁆ = (s * y * s⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
      rw [this]
      exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSK hs) y).mp hy.2) (K.inv_mem hy.2)
  rw [e]
  exact ((S ⊓ K) ⊔ (S' ⊓ K)).mul_mem (Subgroup.mem_sup_left h1)
    (((S ⊓ K) ⊔ (S' ⊓ K)).mul_mem (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right hy))

theorem cw_conj {D S W K : Subgroup G} {x u : G}
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hDW : D ≤ W) (hside : ∀ s ∈ S, s ∉ K → ∀ w ∈ W, s * w = w * s → w ∈ D)
    (hcen : ∀ s ∈ S, ∀ w ∈ D, s * w = w * s) (hu : u ∈ conjSubgroup x S) (huK : u ∉ K) :
    ∀ w, w ∈ conjSubgroup x D ↔ w ∈ W ∧ u * w = w * u := by
  have hs : x⁻¹ * u * x ∈ S := mem_conjSubgroup.mp hu
  have hsK : x⁻¹ * u * x ∉ K := fun h => huK (by
    have := (Subgroup.mem_normalizer_iff.mp hxK _).mp h
    rwa [show x * (x⁻¹ * u * x) * x⁻¹ = u by group] at this)
  have hWx : ∀ w, x⁻¹ * w * x ∈ W ↔ w ∈ W := fun w => by
    have h := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxW) w
    rw [inv_inv] at h
    exact h.symm
  intro w
  rw [mem_conjSubgroup]
  constructor
  · intro hw
    refine ⟨(hWx w).mp (hDW hw), ?_⟩
    have := hcen _ hs _ hw
    calc u * w = x * ((x⁻¹ * u * x) * (x⁻¹ * w * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * w * x) * (x⁻¹ * u * x)) * x⁻¹ := by rw [this]
      _ = w * u := by group
  · rintro ⟨hwW, hw⟩
    refine hside _ hs hsK _ ((hWx w).mpr hwW) ?_
    calc x⁻¹ * u * x * (x⁻¹ * w * x) = x⁻¹ * (u * w) * x := by group
      _ = x⁻¹ * (w * u) * x := by rw [hw]
      _ = x⁻¹ * w * x * (x⁻¹ * u * x) := by group

theorem closure_step [Finite G] {W K D₁ D₂ : Subgroup G} {u v : G}
    (hvW : v ∈ Subgroup.normalizer (W : Set G)) (hκ : ⁅u, v⁆ ∈ K)
    (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
    (hD₁ : ∀ w, w ∈ D₁ ↔ w ∈ W ∧ u * w = w * u) (hD₂ : ∀ w, w ∈ D₂ ↔ w ∈ W ∧ v * w = w * v)
    (hD₁2 : IsPGroup 2 D₁) (hD₁1 : D₁ ≠ ⊥) (hv2 : ∃ k : ℕ, v ^ 2 ^ k = 1)
    (hTI : D₁ ⊓ D₂ ≠ ⊥ → D₁ = D₂) : D₁ = D₂ := by
  have hvD : v ∈ Subgroup.normalizer (D₁ : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨hwW, huw⟩ := (hD₁ w).mp hw
    refine (hD₁ _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hvW w).mp hwW, ?_⟩
    have hvw : v * w * v⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hvW w).mp hwW
    have h1 := hKW _ hκ _ hvw
    have e1 : u * (v * w * v⁻¹) * u⁻¹ = v * w * v⁻¹ := by
      have hκv : u * v * u⁻¹ = ⁅u, v⁆ * v := by simp only [commutatorElement_def]; group
      have hw' : u * w * u⁻¹ = w := by rw [huw]; group
      calc u * (v * w * v⁻¹) * u⁻¹ = (u * v * u⁻¹) * (u * w * u⁻¹) * (u * v * u⁻¹)⁻¹ := by group
        _ = (⁅u, v⁆ * v) * w * (⁅u, v⁆ * v)⁻¹ := by rw [hκv, hw']
        _ = ⁅u, v⁆ * (v * w * v⁻¹) * ⁅u, v⁆⁻¹ := by group
        _ = v * w * v⁻¹ := by rw [h1]; group
    calc u * (v * w * v⁻¹) = (u * (v * w * v⁻¹) * u⁻¹) * u := by group
      _ = (v * w * v⁻¹) * u := by rw [e1]
  obtain ⟨z, hz, hz1, hvz⟩ := exists_ne_one_commute' hD₁2 hD₁1 hv2 hvD
  apply hTI
  intro hbot
  have hz2 : z ∈ D₂ := (hD₂ z).mpr ⟨((hD₁ z).mp hz).1, hvz⟩
  have : z ∈ D₁ ⊓ D₂ := ⟨hz, hz2⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hz1 this

abbrev kernelGen48 (B T : Subgroup G) (g : G) : Subgroup G :=
  (T ⊓ kernel48 B T g) ⊔ (conjSubgroup g T ⊓ kernel48 B T g)

@[expose] def IsSide48 (B T : Subgroup G) (g : G) (D S : Subgroup G) : Prop :=
  (D = B ∧ S = T) ∨ (D = conjSubgroup g B ∧ S = conjSubgroup g T)

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

omit [Finite G] in
theorem Bg_ne (hP : ¬ conjSubgroup g B ≤ P) : conjSubgroup g B ≠ B :=
  fun h => hP (by rw [h]; exact H.B_le_P)

theorem B_inf_Bg (hP : ¬ conjSubgroup g B ≤ P) : B ⊓ conjSubgroup g B = ⊥ :=
  inf_conjSubgroup_eq_bot_of_isTI H.ti (H.Bg_ne hP)

theorem W_elem (h48 : Hyp48 M B T g) : Assembly.IsElemAbelian 2 (B ⊔ conjSubgroup g B) :=
  IsElemAbelian.sup_of_commute H.elemAb (isElemAbelian_conjSubgroup H.elemAb g)
    (H.commute_of_conj_le_M h48.leM)

theorem card_W (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    Nat.card (B ⊔ conjSubgroup g B : Subgroup G) = Nat.card B ^ 2 := by
  have hN : B ≤ Subgroup.normalizer (conjSubgroup g B : Set G) :=
    le_normalizer_of_comm fun x hx y hy => H.commute_of_conj_le_M h48.leM x hx y hy
  have h := PartTwo.Sec6.card_sup_mul_card_inf hN
  rw [H.B_inf_Bg hP, Subgroup.card_bot, mul_one, card_conjSubgroup] at h
  rw [h, sq]

omit [Finite G] in
theorem T_comm_B {t : G} (ht : t ∈ T) {a : G} (ha : a ∈ B) : t * a = a * t :=
  (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) a (H.B_le_P ha)).symm

omit [Finite G] in
theorem Tg_comm_Bg {t : G} (ht : t ∈ conjSubgroup g T) {a : G} (ha : a ∈ conjSubgroup g B) :
    t * a = a * t := by
  rw [mem_conjSubgroup] at ht ha
  have := H.T_comm_B ht ha
  calc t * a = g * ((g⁻¹ * t * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * a * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [this]
    _ = a * t := by group

theorem T_le_normalizer_W (h48 : Hyp48 M B T g) :
    T ≤ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
  le_normalizer_sup_of_comm (fun a ha b hb => H.commute_of_conj_le_M h48.leM a ha b hb)
    (fun _ ht _ ha => H.T_comm_B ht ha) fun b hb t ht => h48.comm_T b hb t ht

theorem Tg_le_normalizer_W (h48 : Hyp48 M B T g) :
    conjSubgroup g T ≤ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  rw [sup_comm]
  exact le_normalizer_sup_of_comm
    (fun a ha b hb => (H.commute_of_conj_le_M h48.leM b hb a ha).symm)
    (fun _ ht _ ha => H.Tg_comm_Bg ht ha) fun b hb t ht => h48.comm_Tg b hb t ht

theorem X_le_normalizer_W (h48 : Hyp48 M B T g) :
    T ⊔ conjSubgroup g T ≤ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
  sup_le (H.T_le_normalizer_W h48) (H.Tg_le_normalizer_W h48)

omit [Finite G] in
theorem kernel_le_M : kernel48 B T g ≤ M := by
  intro k hk
  rw [← H.normalizer_B]
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
    (SetLike.coe_subset_coe.mpr (le_sup_left : B ≤ B ⊔ conjSubgroup g B)) hk.2)

omit [Finite G] in
theorem kernel_le_Mg : kernel48 B T g ≤ conjSubgroup g M := by
  intro k hk
  rw [← H.normalizer_conj_eq]
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
    (SetLike.coe_subset_coe.mpr (le_sup_right : conjSubgroup g B ≤ B ⊔ conjSubgroup g B)) hk.2)

theorem X_le_normalizer_kernel (h48 : Hyp48 M B T g) :
    T ⊔ conjSubgroup g T ≤ Subgroup.normalizer (kernel48 B T g : Set G) := fun x hx =>
  mem_normalizer_inf (Subgroup.le_normalizer hx)
    (mem_normalizer_centralizer (H.X_le_normalizer_W h48 hx))

theorem kernel_le_normalizer_T : kernel48 B T g ≤ Subgroup.normalizer (T : Set G) :=
  fun _ hk => H.M_le_normalizer_T (H.kernel_le_M hk)

theorem kernel_le_normalizer_Tg : kernel48 B T g ≤ Subgroup.normalizer (conjSubgroup g T : Set G) :=
  fun _ hk => mem_normalizer_conj_of_mem_conj H.M_le_normalizer_T (H.kernel_le_Mg hk)

theorem T_side (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) {t : G} (ht : t ∈ T)
    (hnc : ¬ ∀ b ∈ conjSubgroup g B, t * b = b * t) :
    ∀ w ∈ B ⊔ conjSubgroup g B, t * w = w * t → w ∈ B :=
  side_centralizer (H.B_inf_Bg hP) (H.commute_of_conj_le_M h48.leM)
    (fun _ ht _ ha => H.T_comm_B ht ha) (fun b hb t ht => h48.comm_T b hb t ht)
    (fun b hb hb1 c hc => by
      have := H.centralizer_le_conj hb hb1 (Subgroup.mem_centralizer_singleton_iff.mpr hc)
      rwa [← H.normalizer_conj_eq] at this) ht hnc

theorem Tg_side (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) {t : G}
    (ht : t ∈ conjSubgroup g T) (hnc : ¬ ∀ b ∈ B, t * b = b * t) :
    ∀ w ∈ B ⊔ conjSubgroup g B, t * w = w * t → w ∈ conjSubgroup g B := by
  rw [sup_comm]
  exact side_centralizer (by rw [inf_comm]; exact H.B_inf_Bg hP)
    (fun a ha b hb => (H.commute_of_conj_le_M h48.leM b hb a ha).symm)
    (fun _ ht _ ha => H.Tg_comm_Bg ht ha) (fun b hb t ht => h48.comm_Tg b hb t ht)
    (fun b hb hb1 c hc => by
      have := H.centralizer_le_conj (g := 1) (by rwa [conjSubgroup_one]) hb1
        (Subgroup.mem_centralizer_singleton_iff.mpr hc)
      rw [conjSubgroup_one] at this
      exact H.M_le_normalizer_B this) ht hnc

theorem T_mem_kernel_iff (h48 : Hyp48 M B T g) {t : G} (htT : t ∈ T)
    (htX : t ∈ T ⊔ conjSubgroup g T) :
    t ∈ kernel48 B T g ↔ ∀ b ∈ conjSubgroup g B, t * b = b * t := by
  constructor
  · intro hk b hb
    exact (Subgroup.mem_centralizer_iff.mp hk.2 b (Subgroup.mem_sup_right hb)).symm
  · intro h
    refine ⟨htX, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
      (le_normalizer_of_comm fun x hx y hy => (H.commute_of_conj_le_M h48.leM y hy x hx).symm) hw
    calc a * b * t = a * (b * t) := by rw [mul_assoc]
      _ = a * (t * b) := by rw [h b hb]
      _ = (a * t) * b := by rw [mul_assoc]
      _ = (t * a) * b := by rw [H.T_comm_B htT ha]
      _ = t * (a * b) := by rw [mul_assoc]

theorem Tg_mem_kernel_iff (h48 : Hyp48 M B T g) {t : G} (htT : t ∈ conjSubgroup g T)
    (htX : t ∈ T ⊔ conjSubgroup g T) :
    t ∈ kernel48 B T g ↔ ∀ b ∈ B, t * b = b * t := by
  constructor
  · intro hk b hb
    exact (Subgroup.mem_centralizer_iff.mp hk.2 b (Subgroup.mem_sup_left hb)).symm
  · intro h
    refine ⟨htX, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
      (le_normalizer_of_comm fun x hx y hy => (H.commute_of_conj_le_M h48.leM y hy x hx).symm) hw
    calc a * b * t = a * (b * t) := by rw [mul_assoc]
      _ = a * (t * b) := by rw [H.Tg_comm_Bg htT hb]
      _ = (a * t) * b := by rw [mul_assoc]
      _ = (t * a) * b := by rw [h a ha]
      _ = t * (a * b) := by rw [mul_assoc]

theorem kernelGen_le_kernel : kernelGen48 B T g ≤ kernel48 B T g :=
  sup_le inf_le_right inf_le_right

theorem kernelGen_le_X : kernelGen48 B T g ≤ T ⊔ conjSubgroup g T :=
  H.kernelGen_le_kernel.trans inf_le_left

theorem X_le_normalizer_kernelGen (h48 : Hyp48 M B T g) :
    T ⊔ conjSubgroup g T ≤ Subgroup.normalizer (kernelGen48 B T g : Set G) := by
  have hT : T ≤ Subgroup.normalizer (kernel48 B T g : Set G) := fun x hx =>
    H.X_le_normalizer_kernel h48 (Subgroup.mem_sup_left hx)
  have hTg : conjSubgroup g T ≤ Subgroup.normalizer (kernel48 B T g : Set G) := fun x hx =>
    H.X_le_normalizer_kernel h48 (Subgroup.mem_sup_right hx)
  refine sup_le (le_normalizer_kernelGen hT hTg H.kernel_le_normalizer_T) ?_
  rw [show kernelGen48 B T g = (conjSubgroup g T ⊓ kernel48 B T g) ⊔ (T ⊓ kernel48 B T g) from
    sup_comm _ _]
  exact le_normalizer_kernelGen hTg hT H.kernel_le_normalizer_Tg

theorem normal_kernelGen (h48 : Hyp48 M B T g) :
    ((kernelGen48 B T g).subgroupOf (T ⊔ conjSubgroup g T)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer H.kernelGen_le_X).mpr
    (H.X_le_normalizer_kernelGen h48)

theorem side_le {D S : Subgroup G} (hs : IsSide48 B T g D S) :
    D ≤ B ⊔ conjSubgroup g B ∧ S ≤ T ⊔ conjSubgroup g T := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨le_sup_left, le_sup_left⟩
  · exact ⟨le_sup_right, le_sup_right⟩

theorem side_centralizer' (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) {D S : Subgroup G}
    (hs : IsSide48 B T g D S) :
    (∀ s ∈ S, s ∉ kernel48 B T g → ∀ w ∈ B ⊔ conjSubgroup g B, s * w = w * s → w ∈ D) ∧
      (∀ s ∈ S, ∀ w ∈ D, s * w = w * s) := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨fun s hs hsK w hw hsw => H.T_side h48 hP hs (fun h => hsK
      ((H.T_mem_kernel_iff h48 hs (Subgroup.mem_sup_left hs)).mpr h)) w hw hsw,
      fun s hs w hw => H.T_comm_B hs hw⟩
  · exact ⟨fun s hs hsK w hw hsw => H.Tg_side h48 hP hs (fun h => hsK
      ((H.Tg_mem_kernel_iff h48 hs (Subgroup.mem_sup_right hs)).mpr h)) w hw hsw,
      fun s hs w hw => H.Tg_comm_Bg hs hw⟩

omit H in
theorem side_conj {D S : Subgroup G} (hs : IsSide48 B T g D S) (x : G) :
    ∃ z : G, conjSubgroup x D = conjSubgroup z B ∧ conjSubgroup x S = conjSubgroup z T := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨x, rfl, rfl⟩
  · exact ⟨x * g, (conjSubgroup_mul x g B).symm, (conjSubgroup_mul x g T).symm⟩

theorem conj_B_eq_of_inf_ne_bot {z z' : G} (h : conjSubgroup z B ⊓ conjSubgroup z' B ≠ ⊥) :
    conjSubgroup z B = conjSubgroup z' B := by
  have hTI := isTI_conjSubgroup H.ti z'
  have hne : conjSubgroup z' B ⊓ conjSubgroup (z * z'⁻¹) (conjSubgroup z' B) ≠ ⊥ := by
    rw [← conjSubgroup_mul, show z * z'⁻¹ * z' = z by group, inf_comm]
    exact h
  have := conjSubgroup_eq_of_isTI hTI hne
  rwa [← conjSubgroup_mul, show z * z'⁻¹ * z' = z by group] at this

theorem conj_T_eq_of_conj_B_eq {z z' : G} (h : conjSubgroup z B = conjSubgroup z' B) :
    conjSubgroup z T = conjSubgroup z' T := by
  have hm : z'⁻¹ * z ∈ M := by
    rw [← H.normalizer_B, ← conjSubgroup_eq_self_iff, conjSubgroup_mul, h, ← conjSubgroup_mul,
      inv_mul_cancel, conjSubgroup_one]
  have e : conjSubgroup z T = conjSubgroup z' (conjSubgroup (z'⁻¹ * z) T) := by
    rw [← conjSubgroup_mul, mul_inv_cancel_left]
  rw [e, conjSubgroup_eq_self_iff.mpr (H.M_le_normalizer_T hm)]

theorem side_TI {D D' S S' : Subgroup G} (hs : IsSide48 B T g D S) (hs' : IsSide48 B T g D' S')
    (x y : G) (h : conjSubgroup x D ⊓ conjSubgroup y D' ≠ ⊥) :
    conjSubgroup x D = conjSubgroup y D' := by
  obtain ⟨z, hz, -⟩ := side_conj hs x
  obtain ⟨z', hz', -⟩ := side_conj hs' y
  rw [hz, hz'] at h ⊢
  exact H.conj_B_eq_of_inf_ne_bot h

theorem side_eq {D D' S S' : Subgroup G} (hs : IsSide48 B T g D S) (hs' : IsSide48 B T g D' S')
    (x y : G) (h : conjSubgroup x D = conjSubgroup y D') :
    conjSubgroup x S = conjSubgroup y S' := by
  obtain ⟨z, hz, hzS⟩ := side_conj hs x
  obtain ⟨z', hz', hzS'⟩ := side_conj hs' y
  rw [hz, hz'] at h
  rw [hzS, hzS']
  exact H.conj_T_eq_of_conj_B_eq h

theorem side_pGroup {D S : Subgroup G} (hs : IsSide48 B T g D S) :
    IsPGroup 2 D ∧ IsPGroup 2 S ∧ D ≠ ⊥ := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨H.isPGroup_B, H.isPGroup_Q.to_le H.T_le_Q, H.B_ne_bot⟩
  · refine ⟨H.isPGroup_B.map _, (H.isPGroup_Q.to_le H.T_le_Q).map _, fun h => H.B_ne_bot ?_⟩
    apply Subgroup.eq_bot_of_card_eq
    have := card_conjSubgroup g B
    rw [h, Subgroup.card_bot] at this
    exact this.symm

theorem conj_side_inf_kernel_le (h48 : Hyp48 M B T g) {D S : Subgroup G}
    (hs : IsSide48 B T g D S) {x u : G} (hx : x ∈ T ⊔ conjSubgroup g T)
    (hu : u ∈ conjSubgroup x S) (huK : u ∈ kernel48 B T g) : u ∈ kernelGen48 B T g := by
  have hs' : x⁻¹ * u * x ∈ S := mem_conjSubgroup.mp hu
  have hK : x⁻¹ * u * x ∈ kernel48 B T g := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _
      (H.X_le_normalizer_kernel h48 hx)) u).mp huK
    rwa [inv_inv] at this
  have hK0 : x⁻¹ * u * x ∈ kernelGen48 B T g := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Subgroup.mem_sup_left ⟨hs', hK⟩
    · exact Subgroup.mem_sup_right ⟨hs', hK⟩
  have := (Subgroup.mem_normalizer_iff.mp (H.X_le_normalizer_kernelGen h48 hx) _).mp hK0
  rwa [show x * (x⁻¹ * u * x) * x⁻¹ = u by group] at this

theorem closure48 (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) {D D' S S' : Subgroup G}
    (hs : IsSide48 B T g D S) (hs' : IsSide48 B T g D' S') {x y u v : G}
    (hx : x ∈ T ⊔ conjSubgroup g T) (hy : y ∈ T ⊔ conjSubgroup g T)
    (hu : u ∈ conjSubgroup x S) (hv : v ∈ conjSubgroup y S') (huK : u ∉ kernel48 B T g)
    (hvK : v ∉ kernel48 B T g) (hκ : ⁅u, v⁆ ∈ kernel48 B T g) :
    conjSubgroup x D = conjSubgroup y D' ∧ conjSubgroup x S = conjSubgroup y S' := by
  obtain ⟨hc1, hc2⟩ := H.side_centralizer' h48 hP hs
  obtain ⟨hc1', hc2'⟩ := H.side_centralizer' h48 hP hs'
  obtain ⟨hDW, hSX⟩ := H.side_le hs
  obtain ⟨hD'W, hS'X⟩ := H.side_le hs'
  have hvX : v ∈ T ⊔ conjSubgroup g T := by
    have h1 : y⁻¹ * v * y ∈ T ⊔ conjSubgroup g T := hS'X (mem_conjSubgroup.mp hv)
    have := (T ⊔ conjSubgroup g T).mul_mem ((T ⊔ conjSubgroup g T).mul_mem hy h1)
      ((T ⊔ conjSubgroup g T).inv_mem hy)
    rwa [show y * (y⁻¹ * v * y) * y⁻¹ = v by group] at this
  have hcu := cw_conj (H.X_le_normalizer_W h48 hx) (H.X_le_normalizer_kernel h48 hx) hDW hc1 hc2
    hu huK
  have hcv := cw_conj (H.X_le_normalizer_W h48 hy) (H.X_le_normalizer_kernel h48 hy) hD'W hc1' hc2'
    hv hvK
  obtain ⟨hD2, -, hD1⟩ := H.side_pGroup hs
  obtain ⟨-, hS'2, -⟩ := H.side_pGroup hs'
  have hv2 : ∃ k : ℕ, v ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := (hS'2.map (MulAut.conj y).toMonoidHom : IsPGroup 2 (conjSubgroup y S'))
      ⟨v, hv⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hDx : conjSubgroup x D ≠ ⊥ := fun h => hD1 (by
    apply Subgroup.eq_bot_of_card_eq
    have := card_conjSubgroup x D
    rw [h, Subgroup.card_bot] at this
    exact this.symm)
  have hDe := closure_step (H.X_le_normalizer_W h48 hvX) hκ
    (fun k hk w hw => (Subgroup.mem_centralizer_iff.mp hk.2 w hw).symm) hcu hcv
    (hD2.map (MulAut.conj x).toMonoidHom) hDx hv2 (H.side_TI hs hs' x y)
  exact ⟨hDe, H.side_eq hs hs' x y hDe⟩

theorem comm_side_kernel_mem (h48 : Hyp48 M B T g) {D S : Subgroup G} (hs : IsSide48 B T g D S)
    {t k : G} (ht : t ∈ S) (hk : k ∈ kernel48 B T g) : ⁅t, k⁆ ∈ S ⊓ kernel48 B T g := by
  obtain ⟨-, hSX⟩ := H.side_le hs
  have hKS : kernel48 B T g ≤ Subgroup.normalizer (S : Set G) := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact H.kernel_le_normalizer_T
    · exact H.kernel_le_normalizer_Tg
  refine ⟨?_, ?_⟩
  · have e : ⁅t, k⁆ = t * (k * t⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact S.mul_mem ht ((Subgroup.mem_normalizer_iff.mp (hKS hk) t⁻¹).mp (S.inv_mem ht)
      |> fun h => by simpa [mul_assoc] using h)
  · have e : ⁅t, k⁆ = (t * k * t⁻¹) * k⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (kernel48 B T g).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (H.X_le_normalizer_kernel h48 (hSX ht)) k).mp hk) ((kernel48 B T g).inv_mem hk)

theorem side_inf_kernel_le {D S : Subgroup G} (hs : IsSide48 B T g D S) :
    S ⊓ kernel48 B T g ≤ kernelGen48 B T g := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_sup_left
  · exact le_sup_right

section Cert43


theorem W_le_X : B ⊔ conjSubgroup g B ≤ T ⊔ conjSubgroup g T :=
  sup_le_sup H.B_le_T (Subgroup.map_mono H.B_le_T)

theorem W_le_kernel (h48 : Hyp48 M B T g) : B ⊔ conjSubgroup g B ≤ kernel48 B T g :=
  le_inf H.W_le_X fun w hw => Subgroup.mem_centralizer_iff.mpr fun w' hw' =>
    comm_of_isElemAbelian (H.W_elem h48) hw' hw

theorem side_le_kernelGen (h48 : Hyp48 M B T g) {D S : Subgroup G}
    (hs : IsSide48 B T g D S) : D ≤ kernelGen48 B T g := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (le_inf H.B_le_T (le_sup_left.trans (H.W_le_kernel h48))).trans le_sup_left
  · exact (le_inf (Subgroup.map_mono H.B_le_T)
      (le_sup_right.trans (H.W_le_kernel h48))).trans le_sup_right

theorem side_comm {D S : Subgroup G} (hs : IsSide48 B T g D S) :
    (∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ D) ∧ ∀ s ∈ S, s * s ∈ D := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨fun s hs s' hs' => H.commutator_mem (H.T_le_Q hs) (H.T_le_Q hs'), fun s hs => by
      rw [← sq]; exact H.sq_mem (H.T_le_Q hs)⟩
  · refine ⟨fun s hs s' hs' => ?_, fun s hs => ?_⟩
    · rw [mem_conjSubgroup] at hs hs' ⊢
      rw [show g⁻¹ * ⁅s, s'⁆ * g = ⁅g⁻¹ * s * g, g⁻¹ * s' * g⁆ by
        simp only [commutatorElement_def]; group]
      exact H.commutator_mem (H.T_le_Q hs) (H.T_le_Q hs')
    · rw [mem_conjSubgroup] at hs ⊢
      rw [show g⁻¹ * (s * s) * g = (g⁻¹ * s * g) ^ 2 by rw [sq]; group]
      exact H.sq_mem (H.T_le_Q hs)

end Cert43

end Hyp4

end CFSG.RankThree.GF2n.Tim78
