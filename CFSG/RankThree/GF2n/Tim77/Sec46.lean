module

public import CFSG.RankThree.GF2n.Tim77.Sec35
public import CFSG.RankThree.GF2n.Tim77.Sec41Gen
public import CFSG.RankThree.GF2n.Tim77.Sec44
public import CFSG.RankThree.GF2n.Tim77.Sec46U3
public import CFSG.RankThree.GF2n.Tim77.Assembly
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped commutatorElement

section QZ

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem sec46_comm_A (h : Sec3Ctx A Abar S₀ B) {b a : G} (hb : b ∈ B) (ha : a ∈ A) :
    b * a = a * b :=
  (Subgroup.mem_centralizer_iff.mp (h.b_le_centralizer hb) a ha).symm

theorem sec46_conj_fix (h : Sec3Ctx A Abar S₀ B) {b a : G} (hb : b ∈ B) (ha : a ∈ A) :
    b * a * b⁻¹ = a := by
  rw [sec46_comm_A h hb ha]
  group

theorem sec46_conj_swap {g b y : G} (hgb : g * b = b * g) :
    g * (b * y * b⁻¹) * g⁻¹ = b * (g * y * g⁻¹) * b⁻¹ := by
  have h1 : g * b * g⁻¹ = b := by rw [hgb]; group
  calc g * (b * y * b⁻¹) * g⁻¹ = (g * b * g⁻¹) * (g * y * g⁻¹) * (g * b * g⁻¹)⁻¹ := by group
    _ = b * (g * y * g⁻¹) * b⁻¹ := by rw [h1]

theorem sec46_conj_kak (h : Sec3Ctx A Abar S₀ B) {b k a : G} (hb : b ∈ B) (ha : a ∈ A) :
    b * (k * a * k⁻¹) * b⁻¹ = (b * k * b⁻¹) * a * (b * k * b⁻¹)⁻¹ := by
  have hfix := sec46_conj_fix h hb ha
  calc b * (k * a * k⁻¹) * b⁻¹ = (b * k * b⁻¹) * (b * a * b⁻¹) * (b * k * b⁻¹)⁻¹ := by group
    _ = (b * k * b⁻¹) * a * (b * k * b⁻¹)⁻¹ := by rw [hfix]

theorem sec46_Q_eq_closure (A Abar B : Subgroup G) :
    Sec45Q A Abar B = Subgroup.closure {x | x ∈ Section3.A0 A Abar ∨
      ∃ b ∈ B, ∃ y ∈ Section3.Abar0 A Abar, x = b * y * b⁻¹} := by
  unfold Sec45Q
  apply le_antisymm
  · refine sup_le (fun x hx => Subgroup.subset_closure (Or.inl hx)) ?_
    refine iSup₂_le fun b hb x hx => Subgroup.subset_closure
      (Or.inr ⟨b, hb, b⁻¹ * x * b, mem_conjSubgroup.mp hx, by group⟩)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | ⟨b, hb, y, hy, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · refine Subgroup.mem_sup_right ?_
      refine Subgroup.mem_iSup_of_mem b (Subgroup.mem_iSup_of_mem hb (mem_conjSubgroup.mpr ?_))
      rw [show b⁻¹ * (b * y * b⁻¹) * b = y by group]
      exact hy

theorem sec46_A0_le_Q (A Abar B : Subgroup G) : Section3.A0 A Abar ≤ Sec45Q A Abar B :=
  le_sup_left

theorem sec46_conj_mem_Q {b y : G} (hb : b ∈ B) (hy : y ∈ Section3.Abar0 A Abar) :
    b * y * b⁻¹ ∈ Sec45Q A Abar B := by
  unfold Sec45Q
  refine Subgroup.mem_sup_right ?_
  refine Subgroup.mem_iSup_of_mem b (Subgroup.mem_iSup_of_mem hb (mem_conjSubgroup.mpr ?_))
  rw [show b⁻¹ * (b * y * b⁻¹) * b = y by group]
  exact hy

theorem sec46_Abar0_le_Q (A Abar B : Subgroup G) (hB1 : (1 : G) ∈ B) :
    Section3.Abar0 A Abar ≤ Sec45Q A Abar B := fun y hy => by
  have := sec46_conj_mem_Q (A := A) (Abar := Abar) hB1 hy
  simpa using this

theorem sec46_A0_comm (h : Sec3Ctx A Abar S₀ B) {b a y : G} (hb : b ∈ B)
    (ha : a ∈ Section3.A0 A Abar) (hy : y ∈ Section3.Abar0 A Abar) :
    a * (b * y * b⁻¹) = (b * y * b⁻¹) * a := by
  have hA : a ∈ A := h.setup.L_le ha
  have e : a = b * a * b⁻¹ := (sec46_conj_fix h hb hA).symm
  have hcomm := h.setup.comm_L_Lb ha hy
  calc a * (b * y * b⁻¹) = (b * a * b⁻¹) * (b * y * b⁻¹) := by rw [← e]
    _ = b * (a * y) * b⁻¹ := by group
    _ = b * (y * a) * b⁻¹ := by rw [hcomm]
    _ = (b * y * b⁻¹) * (b * a * b⁻¹) := by group
    _ = (b * y * b⁻¹) * a := by rw [← e]

theorem sec46_comm_conj (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {b₁ b₂ y z : G} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hy : y ∈ Section3.Abar0 A Abar)
    (hz : z ∈ Section3.Abar0 A Abar) :
    (b₁ * y * b₁⁻¹) * (b₂ * z * b₂⁻¹) = (b₂ * z * b₂⁻¹) * (b₁ * y * b₁⁻¹) := by
  have hc : b₁⁻¹ * b₂ ∈ B := B.mul_mem (B.inv_mem hb₁) hb₂
  have key : y * ((b₁⁻¹ * b₂) * z * (b₁⁻¹ * b₂)⁻¹) =
      ((b₁⁻¹ * b₂) * z * (b₁⁻¹ * b₂)⁻¹) * y := by
    by_cases hc1 : b₁⁻¹ * b₂ = 1
    · rw [hc1]
      simp only [one_mul, inv_one, mul_one]
      exact IsElemAbelian.comm h.setup.elem_Ab (h.setup.Lb_le hy) (h.setup.Lb_le hz)
    · exact sec32a_K2 h (hS _ hc hc1) y hy _ (sec41g_mem_conj hz)
  calc (b₁ * y * b₁⁻¹) * (b₂ * z * b₂⁻¹)
      = b₁ * (y * ((b₁⁻¹ * b₂) * z * (b₁⁻¹ * b₂)⁻¹)) * b₁⁻¹ := by group
    _ = b₁ * (((b₁⁻¹ * b₂) * z * (b₁⁻¹ * b₂)⁻¹) * y) * b₁⁻¹ := by rw [key]
    _ = (b₂ * z * b₂⁻¹) * (b₁ * y * b₁⁻¹) := by group

theorem sec46_Q_elemAbelian (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) :
    IsElemAbelian 2 (Sec45Q A Abar B) := by
  rw [sec46_Q_eq_closure]
  refine sec41_isElemAbelian_closure ?_ ?_
  · rintro x (hx | ⟨b₁, hb₁, y, hy, rfl⟩) x' (hx' | ⟨b₂, hb₂, z, hz, rfl⟩)
    · exact IsElemAbelian.comm h.hyp.elemAbelian (h.setup.L_le hx) (h.setup.L_le hx')
    · exact sec46_A0_comm h hb₂ hx hz
    · exact (sec46_A0_comm h hb₁ hx' hy).symm
    · exact sec46_comm_conj h hS hb₁ hb₂ hy hz
  · rintro x (hx | ⟨b, hb, y, hy, rfl⟩)
    · exact h.setup.sq_A (h.setup.L_le hx)
    · have hyy : y * y = 1 := h.setup.sq_Ab (h.setup.Lb_le hy)
      calc b * y * b⁻¹ * (b * y * b⁻¹) = b * (y * y) * b⁻¹ := by group
        _ = 1 := by rw [hyy]; group

theorem sec46_A_le_Z (A Abar B : Subgroup G) : A ≤ Sec45Z A Abar B := le_sup_left

theorem sec46_conj_le_Z {b : G} (hb : b ∈ B) : conjSubgroup b Abar ≤ Sec45Z A Abar B := by
  unfold Sec45Z
  exact le_sup_of_le_right (le_iSup₂ (f := fun b (_ : b ∈ B) => conjSubgroup b Abar) b hb)

theorem sec46_Abar_le_Z (A Abar B : Subgroup G) (hB1 : (1 : G) ∈ B) :
    Abar ≤ Sec45Z A Abar B := by
  have := sec46_conj_le_Z (A := A) (Abar := Abar) (B := B) hB1
  rwa [conjSubgroup_one] at this

theorem sec46_Q_le_Z (h : Sec3Ctx A Abar S₀ B) : Sec45Q A Abar B ≤ Sec45Z A Abar B := by
  unfold Sec45Q Sec45Z
  exact sup_le_sup h.setup.L_le (iSup₂_mono fun b _ => conjSubgroup_mono h.setup.Lb_le)

theorem sec46_k_mem_Z {k : G} (hk : k ∈ A ⊔ Abar) (hB1 : (1 : G) ∈ B) :
    k ∈ Sec45Z A Abar B :=
  (sup_le (sec46_A_le_Z A Abar B) (sec46_Abar_le_Z A Abar B hB1)) hk

theorem sec46_conj_mem_Z (h : Sec3Ctx A Abar S₀ B) {b x : G} (hb : b ∈ B)
    (hx : x ∈ Sec45Z A Abar B) : b * x * b⁻¹ ∈ Sec45Z A Abar B := by
  have hle : Sec45Z A Abar B ≤ (Sec45Z A Abar B).comap (MulAut.conj b).toMonoidHom := by
    refine (sup_le ?_ (iSup₂_le fun b' hb' x' hx' => ?_) : Sec45Z A Abar B ≤ _)
    · intro a ha
      show b * a * b⁻¹ ∈ Sec45Z A Abar B
      rw [sec46_conj_fix h hb ha]
      exact sec46_A_le_Z A Abar B ha
    · show b * x' * b⁻¹ ∈ Sec45Z A Abar B
      have : b * x' * b⁻¹ ∈ conjSubgroup (b * b') Abar := by
        rw [mem_conjSubgroup] at hx' ⊢
        rw [show (b * b')⁻¹ * (b * x' * b⁻¹) * (b * b') = b'⁻¹ * x' * b' by group]
        exact hx'
      exact sec46_conj_le_Z (B.mul_mem hb hb') this
  exact hle hx

theorem sec46_mem_normalizer_Q {g : G}
    (h₁ : ∀ a ∈ Section3.A0 A Abar, g * a * g⁻¹ ∈ Sec45Q A Abar B)
    (h₂ : ∀ b ∈ B, ∀ y ∈ Section3.Abar0 A Abar, g * (b * y * b⁻¹) * g⁻¹ ∈ Sec45Q A Abar B) :
    g ∈ normalizer (Sec45Q A Abar B : Set G) := by
  refine sa_mem_normalizer_of_forall fun n hn => ?_
  have hcl : Subgroup.closure {x | x ∈ Section3.A0 A Abar ∨
      ∃ b ∈ B, ∃ y ∈ Section3.Abar0 A Abar, x = b * y * b⁻¹} ≤
      (Sec45Q A Abar B).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | ⟨b, hb, y, hy, rfl⟩)
    · exact h₁ x hx
    · exact h₂ b hb y hy
  rw [← sec46_Q_eq_closure] at hcl
  exact hcl hn

theorem sec46_A_le_normalizer_Q (h : Sec3Ctx A Abar S₀ B) :
    A ≤ normalizer (Sec45Q A Abar B : Set G) := by
  intro g hg
  refine sec46_mem_normalizer_Q ?_ ?_
  · intro a ha
    have hA : a ∈ A := h.setup.L_le ha
    have e : g * a * g⁻¹ = a := by
      rw [IsElemAbelian.comm h.hyp.elemAbelian hg hA]
      group
    rw [e]
    exact sec46_A0_le_Q A Abar B ha
  · intro b hb y hy
    have hgb : g * b = b * g := (sec46_comm_A h hb hg).symm
    rw [sec46_conj_swap hgb]
    have hc := h.setup.commutator_mem_L hg hy
    have hcA : g * y * g⁻¹ * y⁻¹ ∈ A := h.setup.L_le hc
    have e : b * (g * y * g⁻¹) * b⁻¹ =
        (b * (g * y * g⁻¹ * y⁻¹) * b⁻¹) * (b * y * b⁻¹) := by group
    rw [e, sec46_conj_fix h hb hcA]
    exact Subgroup.mul_mem _ (sec46_A0_le_Q A Abar B hc) (sec46_conj_mem_Q hb hy)

theorem sec46_conj_N_le_Q (h : Sec3Ctx A Abar S₀ B) {b' c : G} (hb' : b' ∈ B) (hc : c ∈ B) :
    ∀ n ∈ Section3.N A Abar c, b' * n * b'⁻¹ ∈ Sec45Q A Abar B := by
  have hle : Section3.N A Abar c ≤ (Sec45Q A Abar B).comap (MulAut.conj b').toMonoidHom := by
    unfold Section3.N
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      show b' * a * b'⁻¹ ∈ Sec45Q A Abar B
      rw [sec46_conj_fix h hb' (h.setup.L_le ha)]
      exact sec46_A0_le_Q A Abar B ha
    · intro y hy
      exact sec46_conj_mem_Q hb' hy
    · intro z hz
      obtain ⟨y, hy, rfl⟩ : ∃ y ∈ Section3.Abar0 A Abar, z = c * y * c⁻¹ :=
        ⟨c⁻¹ * z * c, mem_conjSubgroup.mp hz, by group⟩
      show b' * (c * y * c⁻¹) * b'⁻¹ ∈ Sec45Q A Abar B
      have := sec46_conj_mem_Q (A := A) (Abar := Abar) (B := B) (B.mul_mem hb' hc) hy
      rwa [show b' * c * y * (b' * c)⁻¹ = b' * (c * y * c⁻¹) * b'⁻¹ by group] at this
  intro n hn
  exact hle hn

theorem sec46_conj_Abar_le_normalizer_Q (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {b' : G} (hb' : b' ∈ B) :
    conjSubgroup b' Abar ≤ normalizer (Sec45Q A Abar B : Set G) := by
  intro g hg
  obtain ⟨v, hv, rfl⟩ : ∃ v ∈ Abar, g = b' * v * b'⁻¹ :=
    ⟨b'⁻¹ * g * b', mem_conjSubgroup.mp hg, by group⟩
  refine sec46_mem_normalizer_Q ?_ ?_
  · intro a ha
    have hA : a ∈ A := h.setup.L_le ha
    have hc := h.setup.commutator_mem_Lb hv ha
    have h1 : b'⁻¹ * a * b' = a := by simpa using sec46_conj_fix h (B.inv_mem hb') hA
    have h2 : b' * a * b'⁻¹ = a := sec46_conj_fix h hb' hA
    have e : b' * v * b'⁻¹ * a * (b' * v * b'⁻¹)⁻¹ =
        (b' * (v * a * v⁻¹ * a⁻¹) * b'⁻¹) * a := by
      calc b' * v * b'⁻¹ * a * (b' * v * b'⁻¹)⁻¹
          = b' * v * (b'⁻¹ * a * b') * v⁻¹ * b'⁻¹ := by group
        _ = b' * v * a * v⁻¹ * b'⁻¹ := by rw [h1]
        _ = (b' * (v * a * v⁻¹ * a⁻¹) * b'⁻¹) * (b' * a * b'⁻¹) := by group
        _ = (b' * (v * a * v⁻¹ * a⁻¹) * b'⁻¹) * a := by rw [h2]
    rw [e]
    exact Subgroup.mul_mem _ (sec46_conj_mem_Q hb' hc) (sec46_A0_le_Q A Abar B ha)
  · intro b hb y hy
    have hcB : b'⁻¹ * b ∈ B := B.mul_mem (B.inv_mem hb') hb
    have e : b' * v * b'⁻¹ * (b * y * b⁻¹) * (b' * v * b'⁻¹)⁻¹ =
        b' * (v * ((b'⁻¹ * b) * y * (b'⁻¹ * b)⁻¹) * v⁻¹) * b'⁻¹ := by group
    rw [e]
    by_cases hc1 : b'⁻¹ * b = 1
    · have hcy : (b'⁻¹ * b) * y * (b'⁻¹ * b)⁻¹ = y := by rw [hc1]; group
      have hvy : v * y * v⁻¹ = y := by
        rw [IsElemAbelian.comm h.setup.elem_Ab hv (h.setup.Lb_le hy)]
        group
      rw [hcy, hvy]
      exact sec46_conj_mem_Q hb' hy
    · obtain ⟨-, hYN, -⟩ := tim77Sec32a_holds G A Abar S₀ B (b'⁻¹ * b) h (hS _ hcB hc1)
      have hvY : v ∈ Section3.Y A Abar (b'⁻¹ * b) := sa_Abar_le_Y hv
      have hw : (b'⁻¹ * b) * y * (b'⁻¹ * b)⁻¹ ∈ Section3.N A Abar (b'⁻¹ * b) :=
        sa_conj_Abar0_le_N (sec41g_mem_conj hy)
      have hn : v * ((b'⁻¹ * b) * y * (b'⁻¹ * b)⁻¹) * v⁻¹ ∈ Section3.N A Abar (b'⁻¹ * b) :=
        (Subgroup.mem_normalizer_iff.mp (hYN v hvY) _).mp hw
      exact sec46_conj_N_le_Q h hb' hcB _ hn

theorem sec46_Z_le_normalizer_Q (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) :
    Sec45Z A Abar B ≤ normalizer (Sec45Q A Abar B : Set G) := by
  unfold Sec45Z
  exact sup_le (sec46_A_le_normalizer_Q h)
    (iSup₂_le fun b hb => sec46_conj_Abar_le_normalizer_Q h hS hb)

end QZ

section Data

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem sec46_hAN (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) :
    ∀ y ∈ Sec45Z A Abar B, conjSubgroup y (Section3.A0 A Abar) ≤ Sec45Q A Abar B :=
  fun _ hy => sec41_conj_le (sec46_Z_le_normalizer_Q h hS hy) (sec46_A0_le_Q A Abar B)

theorem sec46_hNc (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) :
    ∀ x ∈ Sec45Q A Abar B, ∀ w ∈ Sec45Q A Abar B, x * w = w * x :=
  fun _ hx _ hw => IsElemAbelian.comm (sec46_Q_elemAbelian h hS) hx hw

theorem sec46_D_le_Z {t : G}
    (ht : t ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)) : t ∈ Sec45Z A Abar B := by
  obtain ⟨y, hy, a, ha, -, rfl⟩ := sec41g_mem_D.mp ht
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy (sec46_A_le_Z A Abar B ha))
    (Subgroup.inv_mem _ hy)

theorem sec46_D_sq (h : Sec3Ctx A Abar S₀ B) {t : G}
    (ht : t ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)) : t * t = 1 := by
  obtain ⟨y, -, a, ha, -, rfl⟩ := sec41g_mem_D.mp ht
  exact sec41g_conj_sq (sec41g_invol h.hyp.elemAbelian ha)

theorem sec46_D_not_mem_Q (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {t : G}
    (ht : t ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)) : t ∉ Sec45Q A Abar B := by
  obtain ⟨y, hy, a, ha, haA₀, rfl⟩ := sec41g_mem_D.mp ht
  intro hQ
  have hy' : y⁻¹ ∈ normalizer (Sec45Q A Abar B : Set G) :=
    Subgroup.inv_mem _ (sec46_Z_le_normalizer_Q h hS hy)
  have haQ : a ∈ Sec45Q A Abar B := by
    have := (Subgroup.mem_normalizer_iff.mp hy' (y * a * y⁻¹)).mp hQ
    rwa [show y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ = a by group] at this
  obtain ⟨x₀, hx₀, hx₀1⟩ := sec32a_exists_mem_ne_one h.setup.Lb_ne_bot
  have hcomm : a * x₀ = x₀ * a :=
    sec46_hNc h hS a haQ x₀ (sec46_Abar0_le_Q A Abar B B.one_mem hx₀)
  have hN : a ∈ normalizer (Abar : Set G) :=
    mem_normalizer_of_commute_of_isTI h.setup.ti_Ab (h.setup.Lb_le hx₀) hx₀1 hcomm
  exact haA₀ (h.setup.mem_L.mpr ⟨ha, hN⟩)

theorem sec46_conj_A_mem (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) {x' a : G}
    (hx' : x' ∈ Sec45Z A Abar B) (ha : a ∈ A) :
    x' * a * x'⁻¹ ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) ∨
      x' * a * x'⁻¹ ∈ Sec45Q A Abar B := by
  by_cases haA₀ : a ∈ Section3.A0 A Abar
  · exact Or.inr (sec46_hAN h hS x' hx' (sec41g_mem_conj haA₀))
  · exact Or.inl (sec41g_mem_D.mpr ⟨x', hx', a, ha, haA₀, rfl⟩)

theorem sec46_conj_Abar_eq (h : Sec3Ctx A Abar S₀ B) {b k : G} (hb : b ∈ B)
    (hk : Abar = conjSubgroup k A) : conjSubgroup b Abar = conjSubgroup (b * k * b⁻¹) A := by
  have h1 : conjSubgroup b⁻¹ A = A :=
    conjSubgroup_eq_of_mem_centralizer (h.b_le_centralizer (B.inv_mem hb))
  rw [hk, ← conjSubgroup_mul b k A, conjSubgroup_mul (b * k) b⁻¹ A, h1]

theorem sec46_gen (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) :
    ∀ y : ↥(Sec45Z A Abar B), y ∈ Subgroup.closure
      ({t : ↥(Sec45Z A Abar B) |
          (t : G) ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)} ∪
        (((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B) : Subgroup ↥(Sec45Z A Abar B)) :
          Set ↥(Sec45Z A Abar B))) := by
  intro y
  set Cl := Subgroup.closure
      ({t : ↥(Sec45Z A Abar B) |
          (t : G) ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)} ∪
        (((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B) : Subgroup ↥(Sec45Z A Abar B)) :
          Set ↥(Sec45Z A Abar B))) with hCl
  have hmem : ∀ x : G, ∀ hx : x ∈ Sec45Z A Abar B,
      (x ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) ∨ x ∈ Sec45Q A Abar B) →
      (⟨x, hx⟩ : ↥(Sec45Z A Abar B)) ∈ Cl := by
    intro x hx hxDQ
    rcases hxDQ with hD | hQ
    · exact Subgroup.subset_closure (Or.inl hD)
    · exact Subgroup.subset_closure (Or.inr (Subgroup.mem_subgroupOf.mpr hQ))
  have hP : Sec45Z A Abar B ≤ Cl.map (Sec45Z A Abar B).subtype := by
    refine (sup_le ?_ (iSup₂_le fun b hb x hx => ?_) : Sec45Z A Abar B ≤ _)
    · intro a ha
      have h1 := sec46_conj_A_mem h hS (x' := 1) (Subgroup.one_mem _) ha
      simp only [one_mul, inv_one, mul_one] at h1
      exact ⟨⟨a, sec46_A_le_Z A Abar B ha⟩, hmem a _ h1, rfl⟩
    · obtain ⟨k, hk, hAk, -⟩ := sa_exists_k h
      have hx'Z : b * k * b⁻¹ ∈ Sec45Z A Abar B :=
        sec46_conj_mem_Z h hb (sec46_k_mem_Z hk B.one_mem)
      have hxmem : x ∈ conjSubgroup (b * k * b⁻¹) A := sec46_conj_Abar_eq h hb hAk ▸ hx
      obtain ⟨a, ha, hxa⟩ : ∃ a ∈ A, x = (b * k * b⁻¹) * a * (b * k * b⁻¹)⁻¹ :=
        ⟨_, mem_conjSubgroup.mp hxmem, by group⟩
      have hxZ : x ∈ Sec45Z A Abar B := sec46_conj_le_Z hb hx
      refine ⟨⟨x, hxZ⟩, hmem x hxZ ?_, rfl⟩
      rw [hxa]
      exact sec46_conj_A_mem h hS hx'Z ha
  obtain ⟨w, hw, hwy⟩ := hP y.2
  have hwy' : w = y := Subtype.ext hwy
  rw [← hwy']
  exact hw

theorem sec46_sec42Data (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    (hsingle : ∃ d₀ ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar),
      ∀ d ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar),
        ∃ g ∈ Sec45Z A Abar B, d = g * d₀ * g⁻¹)
    (hO2 : ∀ z ∈ pCore 2 ↥(Sec45Z A Abar B), ∀ g : ↥(Sec45Z A Abar B),
      ⁅z, g⁆ ∈ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) :
    Sec42Data ↥(Sec45Z A Abar B) ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))
      {t | (t : G) ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)} := by
  have hAN := sec46_hAN h hS
  have hNc := sec46_hNc h hS
  refine
    { sq := fun n hn => Subtype.ext (by
        simpa using (sec46_Q_elemAbelian h hS).2 (n : G) (Subgroup.mem_subgroupOf.mp hn))
      disj := fun t ht htN => sec46_D_not_mem_Q h hS ht (Subgroup.mem_subgroupOf.mp htN)
      invol := ?_
      ord := ?_
      conjD := ?_
      gen := sec46_gen h hS
      cent := ?_
      single := ?_
      O2 := hO2 }
  · intro t ht
    apply Subtype.ext
    have h2 := sec46_D_sq h ht
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [sq]
    exact h2
  · intro t ht t' ht'
    have e : orderOf (t * t') = orderOf ((t : G) * (t' : G)) := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    rw [e]
    rcases sec41g_order h hAN hNc ht ht' with h2 | hodd
    · exact Or.inl (dvd_of_eq h2)
    · exact Or.inr hodd
  · intro g t ht
    have := sec41g_D_conj g.2 ht
    simpa using this
  · intro t ht x hx y hy hxt hyt
    have hxt' : (x : G) * (t : G) = (t : G) * (x : G) := congrArg Subtype.val hxt.eq
    have hyt' : (y : G) * (t : G) = (t : G) * (y : G) := congrArg Subtype.val hyt.eq
    exact Subtype.ext (sec41g_comm_gen h hAN hNc ht hx hxt' hy hyt')
  · obtain ⟨d₀, hd₀, hcl⟩ := hsingle
    refine ⟨⟨d₀, sec46_D_le_Z hd₀⟩, hd₀, fun d hd => ?_⟩
    obtain ⟨y, hy, hdy⟩ := hcl d hd
    exact ⟨⟨y, hy⟩, Subtype.ext hdy⟩

def sec46K (N N₀ : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ normalizer (N : Set G) ∧ ∀ n ∈ N₀, ⁅n, y⁆ ∈ N}
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁N, hy₁⟩ ⟨hy₂N, hy₂⟩
    refine ⟨(normalizer (N : Set G)).mul_mem hy₁N hy₂N, fun n hn => ?_⟩
    have e : ⁅n, y₁ * y₂⁆ = ⁅n, y₁⁆ * (y₁ * ⁅n, y₂⁆ * y₁⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem (hy₁ n hn) ((Subgroup.mem_normalizer_iff.mp hy₁N _).mp (hy₂ n hn))
  one_mem' := by
    refine ⟨(normalizer (N : Set G)).one_mem, fun n _ => ?_⟩
    have e : ⁅n, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
    rw [e]; exact N.one_mem
  inv_mem' := by
    rintro y ⟨hyN, hy⟩
    refine ⟨(normalizer (N : Set G)).inv_mem hyN, fun n hn => ?_⟩
    have e : ⁅n, y⁻¹⁆ = y⁻¹ * (⁅n, y⁆)⁻¹ * (y⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp ((normalizer (N : Set G)).inv_mem hyN) _).mp
      (N.inv_mem (hy n hn))

theorem sec46_O2 (h : Sec3Ctx A Abar S₀ B)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b) :
    ∀ z ∈ pCore 2 ↥(Sec45Z A Abar B), ∀ g : ↥(Sec45Z A Abar B),
      ⁅z, g⁆ ∈ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B) := by
  have hsyl : ∃ P : Sylow 2 G, (P : Subgroup G) ≤ normalizer (A : Set G) :=
    (sylow_le_normalizer_iff A).2 h.hyp.sylow
  have hZN := sec46_Z_le_normalizer_Q h hS
  have hN₀A : (pCore 2 ↥(Sec45Z A Abar B)).map (Sec45Z A Abar B).subtype ≤
      normalizer (A : Set G) :=
    sec32b_le_normalizer h.setup h.hyp.rootTypeInCentralizer hsyl
      (sec46_A_le_Z A Abar B) (sec46_Abar_le_Z A Abar B B.one_mem) (sec46_Q_le_Z h)
      (sec46_A0_le_Q A Abar B) (fun y hy => hZN hy) (sec46_Q_elemAbelian h hS)
  have hN₀n : ∀ y ∈ Sec45Z A Abar B, ∀ n ∈ (pCore 2 ↥(Sec45Z A Abar B)).map
      (Sec45Z A Abar B).subtype, y * n * y⁻¹ ∈ (pCore 2 ↥(Sec45Z A Abar B)).map
      (Sec45Z A Abar B).subtype := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_map_subtype _ (pCore 2 ↥(Sec45Z A Abar B)) hy) n).mp hn
  have hconjN : ∀ y ∈ Sec45Z A Abar B, (pCore 2 ↥(Sec45Z A Abar B)).map
      (Sec45Z A Abar B).subtype ≤ normalizer (conjSubgroup y A : Set G) := by
    intro y hy n hn
    rw [sec32b_mem_normalizer_conj]
    apply hN₀A
    have := hN₀n y⁻¹ ((Sec45Z A Abar B).inv_mem hy) n hn
    simpa using this
  obtain ⟨k, hk, hAk, -⟩ := sa_exists_k h
  have hkZ := sec46_k_mem_Z hk (B.one_mem : (1 : G) ∈ B)
  have hAbn : (pCore 2 ↥(Sec45Z A Abar B)).map (Sec45Z A Abar B).subtype ≤
      normalizer (Abar : Set G) := by
    intro n hn
    have := hconjN k hkZ hn
    rwa [← hAk] at this
  have hAK : A ≤ sec46K (Sec45Q A Abar B) ((pCore 2 ↥(Sec45Z A Abar B)).map
      (Sec45Z A Abar B).subtype) := by
    intro a ha
    refine ⟨sec46_A_le_normalizer_Q h ha, fun n hn => ?_⟩
    have hnA : n ∈ normalizer (A : Set G) := hN₀A hn
    have h1 : ⁅n, a⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp hnA a).mp ha) (A.inv_mem ha)
    have h2 : ⁅n, a⁆ ∈ (pCore 2 ↥(Sec45Z A Abar B)).map (Sec45Z A Abar B).subtype := by
      have h1' := hN₀n a (sec46_A_le_Z A Abar B ha) n⁻¹ (Subgroup.inv_mem _ hn)
      have e : ⁅n, a⁆ = n * (a * n⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hn h1'
    have h3 : ⁅n, a⁆ ∈ Section3.A0 A Abar := by
      rw [h.a0_eq]
      exact Subgroup.mem_inf.mpr ⟨h1, hAbn h2⟩
    exact sec46_A0_le_Q A Abar B h3
  have hBK : ∀ b ∈ B, conjSubgroup b Abar ≤ sec46K (Sec45Q A Abar B)
      ((pCore 2 ↥(Sec45Z A Abar B)).map (Sec45Z A Abar B).subtype) := by
    intro b hb u hu
    refine ⟨sec46_conj_Abar_le_normalizer_Q h hS hb hu, fun n hn => ?_⟩
    have hbAb : (pCore 2 ↥(Sec45Z A Abar B)).map (Sec45Z A Abar B).subtype ≤
        normalizer (conjSubgroup b Abar : Set G) := by
      rw [sec46_conj_Abar_eq h hb hAk]
      exact hconjN _ (sec46_conj_mem_Z h hb hkZ)
    have h1 : ⁅n, u⁆ ∈ conjSubgroup b Abar := by
      rw [commutatorElement_def]
      exact (conjSubgroup b Abar).mul_mem ((Subgroup.mem_normalizer_iff.mp (hbAb hn) u).mp hu)
        ((conjSubgroup b Abar).inv_mem hu)
    have h2 : ⁅n, u⁆ ∈ (pCore 2 ↥(Sec45Z A Abar B)).map (Sec45Z A Abar B).subtype := by
      have h1' := hN₀n u (sec46_conj_le_Z hb hu) n⁻¹ (Subgroup.inv_mem _ hn)
      have e : ⁅n, u⁆ = n * (u * n⁻¹ * u⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hn h1'
    have h3 : ⁅n, u⁆ ∈ normalizer (A : Set G) := hN₀A h2
    have hbN : b ∈ normalizer (A : Set G) := h.s0_le_normalizer (h.b_le_s0 hb)
    have h4 : b⁻¹ * ⁅n, u⁆ * b ∈ Section3.Abar0 A Abar := by
      rw [h.abar0_eq]
      refine Subgroup.mem_inf.mpr ⟨mem_conjSubgroup.mp h1, ?_⟩
      exact (normalizer (A : Set G)).mul_mem
        ((normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem hbN) h3) hbN
    have := sec46_conj_mem_Q hb h4
    rwa [show b * (b⁻¹ * ⁅n, u⁆ * b) * b⁻¹ = ⁅n, u⁆ by group] at this
  have hZK : Sec45Z A Abar B ≤ sec46K (Sec45Q A Abar B) ((pCore 2 ↥(Sec45Z A Abar B)).map
      (Sec45Z A Abar B).subtype) :=
    (sup_le hAK (iSup₂_le fun b hb => hBK b hb) : Sec45Z A Abar B ≤ _)
  intro z hz g
  have hzN₀ : (z : G) ∈ (pCore 2 ↥(Sec45Z A Abar B)).map (Sec45Z A Abar B).subtype :=
    Subgroup.mem_map_of_mem _ hz
  have := (hZK g.2).2 _ hzN₀
  rw [Subgroup.mem_subgroupOf]
  simpa [commutatorElement_def] using this

theorem sec46_single
    (h : Sec3Ctx A Abar S₀ B) :
    ∃ d₀ ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar),
      ∀ d ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar),
        ∃ g ∈ Sec45Z A Abar B, d = g * d₀ * g⁻¹ := by
  obtain ⟨a₀, ha₀A, ha₀N⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h.setup.L_le h.setup.ne)
  refine ⟨a₀, sec41g_mem_D.mpr ⟨1, Subgroup.one_mem _, a₀, ha₀A, ha₀N, by simp⟩,
    fun d hd => ?_⟩
  obtain ⟨y, hy, a, ha, haA₀, rfl⟩ := sec41g_mem_D.mp hd
  obtain ⟨g, hgmem, hg⟩ := Prop24Setup.tim77_2_4_five h.setup
    CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput ha haA₀ ha₀A ha₀N
  have hgZ : g ∈ Sec45Z A Abar B := sec46_k_mem_Z (Subgroup.mem_inf.mp hgmem).1 B.one_mem
  refine ⟨y * g⁻¹, Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hgZ), ?_⟩
  rw [← hg]
  group

theorem sec46_not_solvable {b : G}
    (hY : ¬ Group.IsSolvable ↥(A ⊔ Abar ⊔ conjSubgroup b Abar)) (hb : b ∈ B) :
    ¬ Group.IsSolvable ↥(Sec45Z A Abar B) := by
  intro hZ
  have hle : A ⊔ Abar ⊔ conjSubgroup b Abar ≤ Sec45Z A Abar B :=
    sup_le (sup_le (sec46_A_le_Z A Abar B) (sec46_Abar_le_Z A Abar B B.one_mem))
      (sec46_conj_le_Z hb)
  exact hY (solvable_of_solvable_injective (Subgroup.inclusion_injective hle))

end Data

section U3

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem sec46_relIndex_A (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2) :
    (Section3.A0 A Abar).relIndex A = 2 := by
  have hqAb : (Section3.Abar0 A Abar).relIndex Abar = 2 := by
    unfold Section3.q at hq
    exact hq
  rw [← h.setup.relIndex_Lb]
  exact hqAb

theorem sec46_rootType_B (h : Sec3Ctx A Abar S₀ B) :
    IsRootTypeIn 2 (centralizer (B : Set G)) A := by
  obtain ⟨c, hc⟩ := h.nota.conj
  have hA_le : conjSubgroup c⁻¹ (conjSubgroup c A) ≤
      centralizer (conjSubgroup c A : Set G) := by
    rw [conjSubgroup_inv_conj_cancel]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact sec46_comm_A h (by rw [hc]; exact hb) ha
  have := (elementaryAbelianTIRootCentralizerHypothesis_conj_t77 h.hyp c).rootTypeInCentralizer
    c⁻¹ hA_le
  rw [conjSubgroup_inv_conj_cancel, ← hc] at this
  exact this

theorem sec46_B_ti (h : Sec3Ctx A Abar S₀ B) : IsTI B := by
  obtain ⟨c, hc⟩ := h.nota.conj
  rw [hc]
  exact isTI_conjSubgroup h.hyp.ti c

theorem sec46_dich (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {k a β b : G} (hkZ : k ∈ Sec45Z A Abar B) (ha : a ∈ A) (haA₀ : a ∉ Section3.A0 A Abar)
    (hβ : β = k * a * k⁻¹) (hb : b ∈ B) :
    β * (b * β * b⁻¹) = (b * β * b⁻¹) * β ∨
      ∃ y ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar),
        a * y = y * a ∧ y * β * y⁻¹ = b * β * b⁻¹ := by
  by_cases hnc : β * (b * β * b⁻¹) = (b * β * b⁻¹) * β
  · exact Or.inl hnc
  right
  have hAN := sec46_hAN h hS
  have hNc := sec46_hNc h hS
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hnc
    simp
  have hbb : b * b = 1 := sa_sq_of_mem_B h hb
  have haZ : a ∈ Sec45Z A Abar B := sec46_A_le_Z A Abar B ha
  have hx'Z : b * k * b⁻¹ ∈ Sec45Z A Abar B := sec46_conj_mem_Z h hb hkZ
  have hβ_mem : β ∈ conjSubgroup k A := by rw [hβ]; exact sec41g_mem_conj ha
  have hβ_not : β ∉ conjSubgroup k (Section3.A0 A Abar) := by
    rw [hβ]; exact sec41g_not_mem_conj haA₀
  have hβb : b * β * b⁻¹ = (b * k * b⁻¹) * a * (b * k * b⁻¹)⁻¹ := by
    rw [hβ]; exact sec46_conj_kak h hb ha
  have hβb_mem : b * β * b⁻¹ ∈ conjSubgroup (b * k * b⁻¹) A := by
    rw [hβb]; exact sec41g_mem_conj ha
  have hβb_not : b * β * b⁻¹ ∉ conjSubgroup (b * k * b⁻¹) (Section3.A0 A Abar) := by
    rw [hβb]; exact sec41g_not_mem_conj haA₀
  have hnc' : ¬ ∀ x ∈ conjSubgroup k A, ∀ w ∈ conjSubgroup (b * k * b⁻¹) A, x * w = w * x :=
    fun hall => hnc (hall β hβ_mem _ hβb_mem)
  have S1 := sec41g_prop24 h hAN hNc hkZ hx'Z hnc'
  have hodd : Odd (orderOf (β * (b * β * b⁻¹))) :=
    S1.odd_orderOf_mul hβ_mem hβ_not hβb_mem hβb_not
  have hββ : β * β = 1 := by
    rw [hβ]; exact sec41g_conj_sq (sec41g_invol h.hyp.elemAbelian ha)
  have hγγ : (b * β * b⁻¹) * (b * β * b⁻¹) = 1 := sec41g_conj_sq hββ
  have hφφ : MulAut.conj b * MulAut.conj b = 1 := by rw [← map_mul, hbb, map_one]
  obtain ⟨ρ, hρcl, hρρ, hρβρ, hρb, g, hgcl, hρg⟩ :=
    dih_fixed_reflection (R := G) hββ hγγ hodd (MulAut.conj b) hφφ (MulAut.conj_apply b β)
  rw [MulAut.conj_apply] at hρb
  have hβZ : β ∈ Sec45Z A Abar B := by
    rw [hβ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkZ haZ) (Subgroup.inv_mem _ hkZ)
  have hβbZ : b * β * b⁻¹ ∈ Sec45Z A Abar B := sec46_conj_mem_Z h hb hβZ
  have hclZ : Subgroup.closure ({β, b * β * b⁻¹} : Set G) ≤ Sec45Z A Abar B := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hβZ, hβbZ⟩
  have hgkZ : g * k ∈ Sec45Z A Abar B := Subgroup.mul_mem _ (hclZ hgcl) hkZ
  have hρeq : ρ = (g * k) * a * (g * k)⁻¹ := by rw [hρg, hβ]; group
  have hρT : ρ ∈ conjSubgroup (g * k) A := by rw [hρeq]; exact sec41g_mem_conj ha
  have hρT₀ : ρ ∉ conjSubgroup (g * k) (Section3.A0 A Abar) := by
    rw [hρeq]; exact sec41g_not_mem_conj haA₀
  have hρD : ρ ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨g * k, hgkZ, a, ha, haA₀, hρeq⟩
  refine ⟨ρ, hρD, ?_, ?_⟩
  ·
    by_contra hnoc
    have hnc2 : ¬ ∀ x ∈ A, ∀ w ∈ conjSubgroup (g * k) A, x * w = w * x :=
      fun hall => hnoc (hall a ha ρ hρT)
    have S2 : Prop24Setup A (conjSubgroup (g * k) A) (Section3.A0 A Abar)
        (conjSubgroup (g * k) (Section3.A0 A Abar))
        (Section3.A0 A Abar ⊔ conjSubgroup (g * k) (Section3.A0 A Abar)) := by
      have := sec41g_prop24 h hAN hNc (Subgroup.one_mem _) hgkZ
        (by rw [conjSubgroup_one]; exact hnc2)
      rwa [conjSubgroup_one, conjSubgroup_one] at this
    have hidx : (conjSubgroup (g * k) (Section3.A0 A Abar)).relIndex
        (conjSubgroup (g * k) A) = 2 := by
      rw [relIndex_conjSubgroup_t77]
      exact sec46_relIndex_A h hq
    have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun a' ha' =>
      Subgroup.mem_centralizer_singleton_iff.mpr (sec46_comm_A h hb ha').symm
    have hρC : ρ ∈ Subgroup.centralizer ({b} : Set G) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc ρ * b = (b * ρ * b⁻¹) * b := by rw [hρb]
        _ = b * ρ := by group
    have hT₀C : conjSubgroup (g * k) (Section3.A0 A Abar) ≤
        Subgroup.centralizer ({b} : Set G) := by
      intro t₀ ht₀
      obtain ⟨n, hn, e⟩ := S2.symm.exists_commutator_eq hρT hρT₀ ht₀
      have hnC : n ∈ Subgroup.centralizer ({b} : Set G) := hAC (h.setup.L_le hn)
      rw [← e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC hnC)
        (Subgroup.inv_mem _ hρC)) (Subgroup.inv_mem _ hnC)
    have hTC : conjSubgroup (g * k) A ≤ Subgroup.centralizer ({b} : Set G) := by
      intro t ht
      by_cases htT₀ : t ∈ conjSubgroup (g * k) (Section3.A0 A Abar)
      · exact hT₀C htT₀
      · have h1 := hT₀C (sa_mul_mem_of_index_two hidx hρT ht hρT₀ htT₀)
        have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hρC) h1
        rwa [inv_mul_cancel_left] at h2
    have hBTI := sec46_B_ti h
    obtain ⟨c, hc⟩ := h.nota.conj
    have hTN : conjSubgroup (g * k) A ≤ normalizer (conjSubgroup c A : Set G) := by
      intro t ht
      rw [← hc]
      exact mem_normalizer_of_commute_of_isTI hBTI hb hb1
        (Subgroup.mem_centralizer_singleton_iff.mp (hTC ht))
    have hTB := sec32b_commute_of_normalizes h.hyp.elemAbelian h.hyp.ti (g * k) c hTN
    have hX : A ⊔ conjSubgroup (g * k) A ≤ centralizer (B : Set G) := by
      refine sup_le (fun a' ha' => ?_) (fun t ht => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro b' hb'
        exact sec46_comm_A h hb' ha'
      · rw [Subgroup.mem_centralizer_iff]
        intro b' hb'
        exact (hTB t ht b' (by rw [← hc]; exact hb')).symm
    obtain ⟨x', hx'mem, hx'eq⟩ := S2.exists_conj_eq
    have hne : normalizerIn A (conjSubgroup x' A) ≠ ⊥ := by
      rw [← hx'eq]
      unfold normalizerIn
      rw [← S2.hL]
      exact h.a0_ne_bot
    have hall := (sec46_rootType_B h).2.2.2 x' (hX hx'mem) hne
    rw [← hx'eq] at hall
    exact hnoc (hall a ha ρ hρT)
  · rw [inv_eq_of_mul_eq_one_right hρρ]
    exact hρβρ

theorem sec46_closure_top (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {L : Type} [Group L] (φ : ↥(Sec45Z A Abar B) →* L) (hφs : Function.Surjective φ)
    (hφQ : ∀ x : ↥(Sec45Z A Abar B), (x : G) ∈ Sec45Q A Abar B → φ x = 1)
    {k a β : G} (hk : Abar = conjSubgroup k A) (hkZ : k ∈ Sec45Z A Abar B) (haA : a ∈ A)
    (haN : a ∉ Section3.A0 A Abar) (hβ : β = k * a * k⁻¹)
    (haZ : a ∈ Sec45Z A Abar B) (hβbZ : ∀ b ∈ B, b * β * b⁻¹ ∈ Sec45Z A Abar B) :
    Subgroup.closure {x : L | x = φ ⟨a, haZ⟩ ∨
      ∃ b, ∃ hb : b ∈ B, x = φ ⟨b * β * b⁻¹, hβbZ b hb⟩} = ⊤ := by
  have hAN := sec46_hAN h hS
  have hqA := sec46_relIndex_A h hq
  set Cl := Subgroup.closure {x : L | x = φ ⟨a, haZ⟩ ∨
      ∃ b, ∃ hb : b ∈ B, x = φ ⟨b * β * b⁻¹, hβbZ b hb⟩} with hCl
  have hu : φ ⟨a, haZ⟩ ∈ Cl := Subgroup.subset_closure (Or.inl rfl)
  have hβb : ∀ (b : G) (hb : b ∈ B), φ ⟨b * β * b⁻¹, hβbZ b hb⟩ ∈ Cl := fun b hb =>
    Subgroup.subset_closure (Or.inr ⟨b, hb, rfl⟩)
  have hP : Sec45Z A Abar B ≤ (Cl.comap φ).map (Sec45Z A Abar B).subtype := by
    refine (sup_le ?_ (iSup₂_le fun b hb x hx => ?_) : Sec45Z A Abar B ≤ _)
    · intro a' ha'
      refine ⟨⟨a', sec46_A_le_Z A Abar B ha'⟩, ?_, rfl⟩
      show φ ⟨a', sec46_A_le_Z A Abar B ha'⟩ ∈ Cl
      by_cases ha'N : a' ∈ Section3.A0 A Abar
      · rw [hφQ _ (sec46_A0_le_Q A Abar B ha'N)]
        exact Cl.one_mem
      · have hmul : a' * a ∈ Section3.A0 A Abar :=
          sa_mul_mem_of_index_two hqA ha' haA ha'N haN
        have h1 : φ ⟨a', sec46_A_le_Z A Abar B ha'⟩ * φ ⟨a, haZ⟩ = 1 := by
          rw [← map_mul]
          exact hφQ _ (sec46_A0_le_Q A Abar B hmul)
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Cl.inv_mem hu
    · have hxZ : x ∈ Sec45Z A Abar B := sec46_conj_le_Z hb hx
      refine ⟨⟨x, hxZ⟩, ?_, rfl⟩
      show φ ⟨x, hxZ⟩ ∈ Cl
      have hx'Z : b * k * b⁻¹ ∈ Sec45Z A Abar B := sec46_conj_mem_Z h hb hkZ
      have hxmem : x ∈ conjSubgroup (b * k * b⁻¹) A := sec46_conj_Abar_eq h hb hk ▸ hx
      obtain ⟨a₂, ha₂, hxa⟩ : ∃ a₂ ∈ A, x = (b * k * b⁻¹) * a₂ * (b * k * b⁻¹)⁻¹ :=
        ⟨_, mem_conjSubgroup.mp hxmem, by group⟩
      by_cases ha₂N : a₂ ∈ Section3.A0 A Abar
      · rw [hφQ _ (by
          show x ∈ Sec45Q A Abar B
          rw [hxa]
          exact hAN _ hx'Z (sec41g_mem_conj ha₂N))]
        exact Cl.one_mem
      · have hmul : a₂ * a ∈ Section3.A0 A Abar :=
          sa_mul_mem_of_index_two hqA ha₂ haA ha₂N haN
        have h1 : φ ⟨x, hxZ⟩ * φ ⟨b * β * b⁻¹, hβbZ b hb⟩ = 1 := by
          rw [← map_mul]
          refine hφQ _ ?_
          show x * (b * β * b⁻¹) ∈ Sec45Q A Abar B
          have e : x * (b * β * b⁻¹) = (b * k * b⁻¹) * (a₂ * a) * (b * k * b⁻¹)⁻¹ := by
            rw [hxa, hβ, sec46_conj_kak h hb haA]
            group
          rw [e]
          exact hAN _ hx'Z (sec41g_mem_conj hmul)
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Cl.inv_mem (hβb b hb)
  rw [eq_top_iff]
  intro l _
  obtain ⟨y, rfl⟩ := hφs l
  obtain ⟨w, hw, hwy⟩ := hP y.2
  have hwy' : w = y := Subtype.ext hwy
  rw [← hwy']
  exact hw

theorem sec46_orderOf_two {W : Type} [Group W] [Finite W] {N₀ : Subgroup W} [N₀.Normal]
    {D₀ : Set W} (hdat : Sec42Data W N₀ D₀)
    (hB : CFSG.BenderSuzuki.IsBenderGroup ((W ⧸ N₀) ⧸ Subgroup.center (W ⧸ N₀))) {t : W}
    (ht : t ∈ D₀) :
    orderOf (QuotientGroup.mk' (Subgroup.center (W ⧸ N₀)) (QuotientGroup.mk' N₀ t)) = 2 := by
  have hnot : QuotientGroup.mk' N₀ t ∉ Subgroup.center (W ⧸ N₀) :=
    (qp_setup hdat).not_mem_of_isBenderGroup (F := Subgroup.center (W ⧸ N₀)) le_rfl hB
      ⟨t, ht, rfl⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← map_pow, hdat.invol t ht, map_one, map_one]
  · intro h1
    exact hnot ((QuotientGroup.eq_one_iff _).mp h1)

theorem sec46_u3_aux (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    {L : Type} [Group L] [Finite L] (φ : ↥(Sec45Z A Abar B) →* L)
    (hφs : Function.Surjective φ)
    (hφQ : ∀ x : ↥(Sec45Z A Abar B), (x : G) ∈ Sec45Q A Abar B → φ x = 1)
    (hφE : ∀ x : ↥(Sec45Z A Abar B),
      (x : G) ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) → orderOf (φ x) = 2)
    {m : ℕ} (hm : 2 ≤ m) (e : L ≃* CFSG.Theory.Comparator.PSU3Model m) : False := by
  obtain ⟨k, hk, hAk, -⟩ := sa_exists_k h
  have hkZ := sec46_k_mem_Z hk (B.one_mem : (1 : G) ∈ B)
  obtain ⟨a, haA, haN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h.setup.L_le h.setup.ne)
  have haZ : a ∈ Sec45Z A Abar B := sec46_A_le_Z A Abar B haA
  obtain ⟨β, hβ⟩ : ∃ β : G, β = k * a * k⁻¹ := ⟨_, rfl⟩
  have hβZ : β ∈ Sec45Z A Abar B := by
    rw [hβ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkZ haZ) (Subgroup.inv_mem _ hkZ)
  have hβbZ : ∀ b ∈ B, b * β * b⁻¹ ∈ Sec45Z A Abar B := fun b hb =>
    sec46_conj_mem_Z h hb hβZ
  have haE : a ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨1, Subgroup.one_mem _, a, haA, haN, by simp⟩
  have hβE : β ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    sec41g_mem_D.mpr ⟨k, hkZ, a, haA, haN, hβ⟩
  have hβbE : ∀ b ∈ B, b * β * b⁻¹ ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar) :=
    fun b hb => sec41g_mem_D.mpr ⟨b * k * b⁻¹, sec46_conj_mem_Z h hb hkZ, a, haA, haN,
      by rw [hβ]; exact sec46_conj_kak h hb haA⟩
  have hub : orderOf (φ ⟨a, haZ⟩) = 2 := hφE _ haE
  have hvb : orderOf (φ ⟨β, hβZ⟩) = 2 := hφE _ hβE
  have hgen := sec46_closure_top h hq hS φ hφs hφQ hAk hkZ haA haN hβ haZ hβbZ
  have hmem : ∀ x ∈ {x : L | x = φ ⟨a, haZ⟩ ∨
      ∃ b, ∃ hb : b ∈ B, x = φ ⟨b * β * b⁻¹, hβbZ b hb⟩},
      x ∈ invComm (φ ⟨a, haZ⟩) ⊔ invComm (φ ⟨β, hβZ⟩) := by
    rintro x (rfl | ⟨b, hb, rfl⟩)
    · exact Subgroup.mem_sup_left (mem_invComm hub (Commute.refl _))
    · rcases sec46_dich h hq hS hkZ haA haN hβ hb with hcomm | ⟨y, hyE, hay, hyβ⟩
      · refine Subgroup.mem_sup_right (mem_invComm (hφE _ (hβbE b hb)) ?_)
        have hc : Commute (⟨b * β * b⁻¹, hβbZ b hb⟩ : ↥(Sec45Z A Abar B)) ⟨β, hβZ⟩ :=
          Subtype.ext hcomm.symm
        exact hc.map φ
      · have hyZ := sec46_D_le_Z hyE
        have hy2 : φ ⟨y, hyZ⟩ ∈ invComm (φ ⟨a, haZ⟩) := by
          refine mem_invComm (hφE _ hyE) ?_
          have hc : Commute (⟨y, hyZ⟩ : ↥(Sec45Z A Abar B)) ⟨a, haZ⟩ := Subtype.ext hay.symm
          exact hc.map φ
        have hv : φ ⟨β, hβZ⟩ ∈ invComm (φ ⟨β, hβZ⟩) := mem_invComm hvb (Commute.refl _)
        have e1 : (⟨b * β * b⁻¹, hβbZ b hb⟩ : ↥(Sec45Z A Abar B)) =
            ⟨y, hyZ⟩ * ⟨β, hβZ⟩ * ⟨y, hyZ⟩⁻¹ := Subtype.ext hyβ.symm
        rw [e1, map_mul, map_mul, map_inv]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hy2)
          (Subgroup.mem_sup_right hv)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hy2))
  have hle : (⊤ : Subgroup L) ≤ invComm (φ ⟨a, haZ⟩) ⊔ invComm (φ ⟨β, hβZ⟩) := by
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr hmem
  exact u3_two_roots_ne_top hm e hub hvb (top_le_iff.mp hle)

theorem sec46_no_u3 (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b)
    [((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal]
    (hdat : Sec42Data ↥(Sec45Z A Abar B) ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))
      {t | (t : G) ∈ sec41g_D (Sec45Z A Abar B) A (Section3.A0 A Abar)})
    {m : ℕ} (hm : 2 ≤ m)
    (e : ((↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ⧸
      Subgroup.center (↥(Sec45Z A Abar B) ⧸
        (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) ≃*
          CFSG.Theory.Comparator.PSU3Model m) : False := by
  have hB := CFSG.BenderSuzuki.IsBenderGroup.isPSU3 m hm e
  refine sec46_u3_aux h hq hS ((QuotientGroup.mk' (Subgroup.center _)).comp
    (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)))) ?_ ?_ ?_ hm e
  · exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  · intro x hx
    have h1 : QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hx)
    show QuotientGroup.mk' (Subgroup.center _)
      (QuotientGroup.mk' ((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) x) = 1
    rw [h1, map_one]
  · intro x hx
    exact sec46_orderOf_two hdat hB hx

end U3

section Main

theorem sec46w_of :
    ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
      Section3.q A Abar = 2 →
        IsElemAbelian 2 (Sec45Q A Abar B) ∧ Sec45Q A Abar B ≤ Sec45Z A Abar B ∧
        Sec45Z A Abar B ≤ normalizer (Sec45Q A Abar B : Set G) ∧
        ∀ [((Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)).Normal],
          CFSG.solvableRadical (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) =
            Subgroup.center (↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ∧
          ((∃ m : ℕ, IsPSL2Model ((↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ⧸
              Subgroup.center (↥(Sec45Z A Abar B) ⧸
                (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) m) ∨
           (∃ a : ℕ, IsSzModel ((↥(Sec45Z A Abar B) ⧸ (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) ⧸
              Subgroup.center (↥(Sec45Z A Abar B) ⧸
                (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B))) a)) := by
  intro G _ _ A Abar S₀ B h hq
  have hS : ∀ b ∈ B, b ≠ 1 → Section3.IsSChoice A Abar S₀ B b := by
    intro b hb hb1
    obtain ⟨x, hxA, hx1, hxo⟩ := sec44w_holds G A Abar S₀ B h hq b hb hb1
    exact ⟨b, hb, hb1, Or.inl ⟨⟨x, hxA, hx1, hxo⟩, rfl⟩⟩
  refine ⟨sec46_Q_elemAbelian h hS, sec46_Q_le_Z h, sec46_Z_le_normalizer_Q h hS, ?_⟩
  intro hNn
  have hdat := sec46_sec42Data h hS (sec46_single h) (sec46_O2 h hS)
  obtain ⟨b, hb, -, hbns⟩ := sec45_of sec43_of sec44w_holds tim77Sec35_holds h hq
  have hns : ¬ Group.IsSolvable (↥(Sec45Z A Abar B) ⧸
      (Sec45Q A Abar B).subgroupOf (Sec45Z A Abar B)) :=
    sec44w_not_solvable_quot (fun x hx y hy => Subtype.ext (sec46_hNc h hS _
      (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)))
      (sec46_not_solvable hbns hb)
  obtain ⟨hrad, hB⟩ := qp_main hdat hns
  refine ⟨hrad, ?_⟩
  cases hB with
  | isPSL2 n hn e => exact Or.inl ⟨n, ⟨e⟩⟩
  | isSuzuki n hn e =>
    exact Or.inr ⟨n, ⟨e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz n))⟩⟩
  | isPSU3 n hn e => exact (sec46_no_u3 h hq hS hdat hn e).elim

end Main

end CFSG.RankThree.GF2n.Tim77
