module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Key
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.K8b

open S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem inf_eq_bot_of_card_two {Zp W : Subgroup G} (h : Nat.card Zp = 2) (hz : ¬ Zp ≤ W) :
    Zp ⊓ W = ⊥ := by
  rw [eq_bot_iff]
  intro z hz'
  by_contra hne
  have hne' : z ≠ 1 := fun h' => hne (Subgroup.mem_bot.mpr h')
  apply hz
  intro z' hz''
  by_cases h1 : z' = 1
  · rw [h1]; exact W.one_mem
  · have := card_two_eq h hz'.1 hz'' hne' h1
    rw [← this]
    exact hz'.2

omit [Finite G] in
theorem normalizer_of_comm {L N : Subgroup G} (hLN : L ≤ N)
    (hc : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ L) : N ≤ Subgroup.normalizer (L : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have key : ∀ w ∈ N, ∀ v ∈ L, w * v * w⁻¹ ∈ L := by
    intro w hw v hv
    have e : w * v * w⁻¹ = (w * v * w⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact L.mul_mem (hc w hw v (hLN hv)) hv
  refine ⟨fun hv => key w hw v hv, fun hv => ?_⟩
  have := key w⁻¹ (N.inv_mem hw) _ hv
  rwa [inv_inv, show w⁻¹ * (w * v * w⁻¹) * w = v by group] at this

theorem claim8b_II (hS : Sit H M S) (hb7 : 7 ≤ bMin H M)
    (hT : ClaimT H M) (h7 : Claim7s H M) (h8a : Claim8a H M)
    (hNT : S35.II.NoTrivialAct H M) (hsec7 : S35.II.WbSec7 H M) :
    Claim8b H M := by
  have hsec : ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β) :=
    fun β hβ => hsec7 hb7 β hβ
  intro β α' hp ht hidx
  obtain ⟨A, B, hA, hB, hAB, h1, h2, h3⟩ := h8a β α' hp ht
  have hβ := hp.vδ
  have hα' := hp.vδ'
  obtain ⟨l₀, hl₀, hl₀Q⟩ : ∃ l ∈ nbrs β, ¬ Zv l ≤ Qv α' := by
    by_contra hcon
    push Not at hcon
    exact hp.not_le (iSup₂_le fun l hl => hcon l hl)
  have hZp : Nat.card (Zv α') = 2 := hS.cardZ5 α' hα'
  have hstabβ : Vn α' ≤ stab β := (Std.PD_Vn_le_stab hS hp).2
  have hZα'_le : Zv α' ≤ Vn α' := Std.Zv_le_Vn_S5 hS hα'
  have hVβs : Vn β ≤ stab α' := (Std.PD_Vn_le_stab hS hp).1
  have hl₀S3 : vtype l₀ = true := Std.vtype_nbr_S5 hβ hl₀
  have hβl₀ : β ∈ nbrs l₀ := Std.mem_nbrs_symm.mp hl₀
  have hVW : Vn β ≤ Wb β := Std.Vn_le_Wb_self hS hβ
  have hWlW : Wl l₀ ≤ Wb β := by
    refine Std.Wl_le fun ρ hρ => ?_
    by_cases hρβ : ρ = β
    · rw [hρβ]; exact hVW
    · exact Std.Vn_le_Wb (Std.dist_eq_two_iff.mpr ⟨l₀, hl₀, hρ, hρβ⟩)
  by_contra hneg
  have hcase : (Zv α' ⊓ Wb β = ⊥ ∧ (Wb β ⊓ stab α' ⊓ Wb β).relIndex (Wb β) ≤ 2) ∨
      Wb β ≤ Wb β ⊓ stab α' := by
    by_cases hz : Zv α' ≤ Wb β
    · right
      have hne1 : (Wb β ⊓ stab α').relIndex (Wb β) ≠ 2 := fun h => hneg ⟨hz, h⟩
      have hne0 := relIndex_ne_zero' (Wb β ⊓ stab α') (Wb β)
      have : (Wb β ⊓ stab α').relIndex (Wb β) = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp this
    · left
      refine ⟨inf_eq_bot_of_card_two hZp hz, ?_⟩
      rw [Subgroup.inf_relIndex_right]
      exact hidx
  have hVB : ⁅Vn β, B⁆ ≤ Vn β := by
    rw [Subgroup.commutator_le]
    intro v hv b hb
    have h4 : b * v⁻¹ * b⁻¹ ∈ Vn β := (Subgroup.mem_normalizer_iff.mp
      (Std.Vn_normal β (hstabβ (hB hb))) v⁻¹).mp ((Vn β).inv_mem hv)
    have e : ⁅v, b⁆ = v * (b * v⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (Vn β).mul_mem hv h4
  have hmain : ∀ x ∈ B, ∀ y ∈ Wb β ⊓ stab α', x * y * x⁻¹ * y⁻¹ ∈ Zv α' ⊔ ⁅Vn β, B⁆ := by
    intro x hx y hy
    have : ⁅x, y⁆ ∈ ⁅Wb β ⊓ stab α', B⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx hy
    rw [commutatorElement_def] at this
    exact h2 this
  by_cases hBQ : ∃ x ∈ B, x ∉ Qv β
  ·
    obtain ⟨x, hxB, hxQ⟩ := hBQ
    have hxs : x ∈ stab β := hstabβ (hB hxB)
    have hWL : Wb β ≤ Subgroup.normalizer (Vn β : Set G) :=
      normalizer_of_comm (hsec β hβ).le (hsec β hβ).comm
    have hle := secIdx_le_two (L := Vn β) (W := Wb β) (Zp := Zv α') (Y := Wb β ⊓ stab α')
      (x := x) hWL (Std.Vn_normal β hxs) (Std.Wb_normal β hxs) hVW
      (fun z hz => Std.Vn_normal β (hstabβ (hZα'_le hz))) hZp
      (fun y hy _ => (sup_le_sup_left hVB _) (hmain x hxB y hy)) hcase
    have h7' := h7 β α' hp x (hB hxB) hxQ (hsec β hβ)
    have hnt : secIdx (Subgroup.zpowers x) (Vn β) (Wb β) ≠ 1 := by
      intro h1
      apply hxQ
      have hfix : Wb β ≤ fixSecIn (Subgroup.zpowers x) (Vn β) (Wb β) := by
        unfold secIdx at h1
        exact Subgroup.relIndex_eq_one.mp h1
      exact hNT β hβ x hxs fun u hu =>
        ((mem_fixSecIn_zpowers_iff hWL ((hsec β hβ).normL hxs)).mp (hfix hu)).2
    have hne0 : secIdx (Subgroup.zpowers x) (Vn β) (Wb β) ≠ 0 := relIndex_ne_zero' _ _
    omega
  · push Not at hBQ
    have hBQ' : ∃ x ∈ B, x ∉ Qv l₀ := by
      by_contra hcon
      push Not at hcon
      apply h3 l₀ hl₀ hl₀Q
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((Subgroup.mem_centralizer_iff.mp
        (Zv_le_centerOf_Qv hS.glob.amalg l₀ hz).2) b (hcon b hb)).symm
    obtain ⟨x, hxB, hxQl⟩ := hBQ'
    have hxQβ := hBQ x hxB
    have hxs : x ∈ stab l₀ := Std.Qv_le_stab hS hl₀ hxQβ
    have hZl₀n : stab l₀ ≤ Subgroup.normalizer (Zv l₀ : Set G) :=
      stab_le_normalizer_Zv hS.glob.amalg l₀
    have hZβl : Zv β ≤ Zv l₀ := Std.Zv_le_Zv_of_nbr hS hβ hl₀
    have hVWl : Vn β ≤ Wl l₀ := Std.Vn_le_Wl hβl₀
    have hZlW : Zv l₀ ≤ Wl l₀ := (Std.Zv_le_Vn hl₀).trans hVWl
    have hWln : Wl l₀ ≤ Subgroup.normalizer (Zv l₀ : Set G) := by
      intro w hw
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Std.Wl_comm hS l₀ z (hZlW hz) w hw
    have hdist : dist α' l₀ ≤ bMin H M + 1 := by
      have h1 := dist_triangle_of_adj hβl₀ α'
      have h2 : dist l₀ β = 1 := dist_eq_one_iff_adj.mpr hβl₀
      have h3 := hp.dist_eq
      rw [dist_comm α' l₀]
      omega
    have hZpL : Zv α' ≤ Subgroup.normalizer (Zv l₀ : Set G) := fun z hz =>
      hZl₀n (Std.Zv_le_stab_dist_S5 hS hα' hdist hz)
    have hcomm : ⁅Vn β, B⁆ ≤ Zv β := by
      rw [← Std.comm_Vn_Qv hS hβ]
      exact Subgroup.commutator_mono le_rfl (fun b hb => hBQ b hb)
    have hle := secIdx_le_two (L := Zv l₀) (W := Wl l₀) (Zp := Zv α') (Y := Wb β ⊓ stab α')
      (x := x) hWln (hZl₀n hxs) (Std.Wl_normal l₀ hxs) hZlW hZpL hZp
      (fun y hy _ => sup_le_sup_left (hcomm.trans hZβl) _ (hmain x hxB y hy)) (by
        rcases hcase with ⟨hZW, hidx'⟩ | hWY
        · left
          refine ⟨le_bot_iff.mp ((inf_le_inf_left _ hWlW).trans hZW.le), ?_⟩
          rw [Subgroup.inf_relIndex_right]
          rw [Subgroup.inf_relIndex_right] at hidx'
          exact (Subgroup.relIndex_le_of_le_right hWlW (relIndex_ne_zero' _ _)).trans hidx'
        · exact Or.inr (hWlW.trans hWY))
    have hT' := hT l₀ hl₀S3 x hxs hxQl
    omega

theorem claim7s_II (hS : Sit H M S) (h : S35.II.NoTransvII H M) : Claim7s H M := by
  intro β α' hp x hx hxQ hsec
  exact h β hp.vδ hsec x ((Std.PD_Vn_le_stab hS hp).2 hx) hxQ

end S35.K8b

end F53.Stellmacher

end CFSG.Quasithin
