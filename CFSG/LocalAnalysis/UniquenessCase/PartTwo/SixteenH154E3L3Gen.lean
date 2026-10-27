module

public import CFSG.Quasithin.Background.B4L3Coord
import CFSG.Quasithin.EmptyFaithful.F918C13
import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_isPSL_of_coord {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : L3Coord L I Z) : IsPSL 3 2 1 ↥L := by
  obtain ⟨D⟩ := h
  exact isPSL_three_two_iff.mpr
    ⟨(MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).symm⟩

private theorem s16h_e3_l3_conj_gen {L : Subgroup (MulAut W)} (e : ↥L ≃* L3.Γ) {γ : MulAut W}
    (hγL : γ ∈ L) (hginvol : L3.IsInvol (e ⟨γ, hγL⟩)) (t : L3.Γ) (ht : L3.IsInvol t) :
    ∃ g : MulAut W, g ∈ L ∧ ((e.symm t : ↥L) : MulAut W) = g * γ * g⁻¹ := by
  obtain ⟨y, hy⟩ := L3.conj_invol hginvol ht
  refine ⟨((e.symm y : ↥L) : MulAut W), (e.symm y).2, ?_⟩
  have h1 : e.symm (y * e ⟨γ, hγL⟩ * y⁻¹) = e.symm t := by rw [hy]
  have h2 : (e.symm y * (⟨γ, hγL⟩ : ↥L) * (e.symm y)⁻¹ : ↥L) = e.symm t := by
    rw [← h1]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  have h3 := congrArg (fun z : ↥L => (z : MulAut W)) h2
  simpa using h3.symm

theorem s16h_e3_l3_rk_le_three_mul_commSub {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L)
    {X M : Subgroup W}
    (hXinv : ∀ l ∈ L, ∀ x ∈ X, l x ∈ X) (hMinv : ∀ l ∈ L, ∀ m ∈ M, l m ∈ M)
    (hX : commSub X L ⊔ M = X) {γ : MulAut W} (hγL : γ ∈ L) (hγ2 : γ ^ 2 = 1) (hγ1 : γ ≠ 1) :
    rk ↥X + 2 * rk ↥M ≤ 3 * rk ↥(commSub X (Subgroup.zpowers γ) ⊔ M) := by
  obtain ⟨e⟩ := isPSL_three_two_iff.mp hL
  have hgL2 : (⟨γ, hγL⟩ : ↥L) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hγ2
  have hgL1 : (⟨γ, hγL⟩ : ↥L) ≠ 1 := by
    intro h
    exact hγ1 (congrArg Subtype.val h)
  have hginvol : L3.IsInvol (e ⟨γ, hγL⟩) := by
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← pow_two, hgL2, map_one]
    · intro h
      exact hgL1 (e.injective (by rw [h, map_one]))
  obtain ⟨g₁, hg₁L, ha₁⟩ := s16h_e3_l3_conj_gen e hγL hginvol L3.x12 L3.x12_invol
  obtain ⟨g₂, hg₂L, ha₂⟩ := s16h_e3_l3_conj_gen e hγL hginvol L3.x23 L3.x23_invol
  obtain ⟨g₃, hg₃L, ha₃⟩ := s16h_e3_l3_conj_gen e hγL hginvol L3.x31 L3.x31_invol
  set B : Subgroup W := commSub X (Subgroup.zpowers γ) ⊔ M with hBeq
  let A₁ : Subgroup W := B.map g₁.toMonoidHom
  let A₂ : Subgroup W := B.map g₂.toMonoidHom
  let A₃ : Subgroup W := B.map g₃.toMonoidHom
  have hzp : Subgroup.zpowers γ ≤ L := Subgroup.zpowers_le.mpr hγL
  have hMX : M ≤ X := by rw [← hX]; exact le_sup_right
  have hBX : B ≤ X := by
    rw [hBeq]
    exact sup_le (commSub_le_of_invariant (fun x hx w hw => hXinv x (hzp hx) w hw)) hMX
  have hMA₁ : M ≤ A₁ := by
    intro m hm
    dsimp only [A₁]
    refine Subgroup.mem_map.mpr ⟨g₁⁻¹ m, ?_, ?_⟩
    · rw [hBeq]
      exact Subgroup.mem_sup_right (hMinv g₁⁻¹ (L.inv_mem hg₁L) m hm)
    · simpa using mulAut_apply_inv_apply g₁ m
  have hMA₂ : M ≤ A₂ := by
    intro m hm
    dsimp only [A₂]
    refine Subgroup.mem_map.mpr ⟨g₂⁻¹ m, ?_, ?_⟩
    · rw [hBeq]
      exact Subgroup.mem_sup_right (hMinv g₂⁻¹ (L.inv_mem hg₂L) m hm)
    · simpa using mulAut_apply_inv_apply g₂ m
  have hMA₃ : M ≤ A₃ := by
    intro m hm
    dsimp only [A₃]
    refine Subgroup.mem_map.mpr ⟨g₃⁻¹ m, ?_, ?_⟩
    · rw [hBeq]
      exact Subgroup.mem_sup_right (hMinv g₃⁻¹ (L.inv_mem hg₃L) m hm)
    · simpa using mulAut_apply_inv_apply g₃ m
  have hA₁X : A₁ ≤ X := by
    intro z hz
    dsimp only [A₁] at hz
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
    exact hXinv g₁ hg₁L b (hBX hb)
  have hA₂X : A₂ ≤ X := by
    intro z hz
    dsimp only [A₂] at hz
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
    exact hXinv g₂ hg₂L b (hBX hb)
  have hA₃X : A₃ ≤ X := by
    intro z hz
    dsimp only [A₃] at hz
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
    exact hXinv g₃ hg₃L b (hBX hb)
  have hMN : M ≤ A₁ ⊔ A₂ ⊔ A₃ := hMA₁.trans (le_sup_left.trans le_sup_left)
  let S : Subgroup ↥L :=
    { carrier := {l : ↥L | ∀ x ∈ X, (l : MulAut W) x * x⁻¹ ∈ A₁ ⊔ A₂ ⊔ A₃}
      one_mem' := by
        intro x _
        simp
      mul_mem' := by
        intro a b ha hb x hx
        have hbx : (b : MulAut W) x ∈ X := hXinv b b.2 x hx
        have h1 := ha ((b : MulAut W) x) hbx
        have h2 := hb x hx
        have hkey : (↑(a * b) : MulAut W) x * x⁻¹ =
            ((a : MulAut W) ((b : MulAut W) x) * ((b : MulAut W) x)⁻¹) *
              ((b : MulAut W) x * x⁻¹) := by
          show (a : MulAut W) ((b : MulAut W) x) * x⁻¹ = _
          group
        rw [hkey]
        exact Subgroup.mul_mem _ h1 h2
      inv_mem' := by
        intro a ha x hx
        have hy : (↑a⁻¹ : MulAut W) x ∈ X :=
          hXinv (↑a⁻¹ : MulAut W) (by simpa using L.inv_mem a.2) x hx
        have h1 := ha ((↑a⁻¹ : MulAut W) x) hy
        have hkey : (↑a⁻¹ : MulAut W) x * x⁻¹ =
            ((a : MulAut W) ((↑a⁻¹ : MulAut W) x) * ((↑a⁻¹ : MulAut W) x)⁻¹)⁻¹ := by
          have h2 : (a : MulAut W) ((↑a⁻¹ : MulAut W) x) = x :=
            mulAut_apply_inv_apply (a : MulAut W) x
          rw [h2]
          group
        rw [hkey]
        exact Subgroup.inv_mem _ h1 }
  have hS1 : e.symm L3.x12 ∈ S := by
    intro x hx
    have hy : g₁⁻¹ x ∈ X := hXinv g₁⁻¹ (L.inv_mem hg₁L) x hx
    have hval : ((e.symm L3.x12 : ↥L) : MulAut W) x * x⁻¹ =
        g₁ (γ (g₁⁻¹ x) * (g₁⁻¹ x)⁻¹) := by
      rw [ha₁]
      simp only [MulAut.mul_apply]
      have h2 : g₁ (g₁⁻¹ x) = x := mulAut_apply_inv_apply g₁ x
      calc g₁ (γ (g₁⁻¹ x)) * x⁻¹
          = g₁ (γ (g₁⁻¹ x)) * (g₁ (g₁⁻¹ x))⁻¹ := by rw [h2]
        _ = g₁ (γ (g₁⁻¹ x) * (g₁⁻¹ x)⁻¹) := by rw [map_mul, map_inv]
    rw [hval]
    have hgen : γ (g₁⁻¹ x) * (g₁⁻¹ x)⁻¹ ∈ commSub X (Subgroup.zpowers γ) :=
      Subgroup.subset_closure ⟨γ, Subgroup.mem_zpowers γ, g₁⁻¹ x, hy, rfl⟩
    have hBmem : γ (g₁⁻¹ x) * (g₁⁻¹ x)⁻¹ ∈ B := by
      rw [hBeq]; exact Subgroup.mem_sup_left hgen
    have hAmem : g₁ (γ (g₁⁻¹ x) * (g₁⁻¹ x)⁻¹) ∈ A₁ := by
      show g₁ (γ (g₁⁻¹ x) * (g₁⁻¹ x)⁻¹) ∈ B.map g₁.toMonoidHom
      exact Subgroup.mem_map.mpr ⟨_, hBmem, rfl⟩
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hAmem)
  have hS2 : e.symm L3.x23 ∈ S := by
    intro x hx
    have hy : g₂⁻¹ x ∈ X := hXinv g₂⁻¹ (L.inv_mem hg₂L) x hx
    have hval : ((e.symm L3.x23 : ↥L) : MulAut W) x * x⁻¹ =
        g₂ (γ (g₂⁻¹ x) * (g₂⁻¹ x)⁻¹) := by
      rw [ha₂]
      simp only [MulAut.mul_apply]
      have h2 : g₂ (g₂⁻¹ x) = x := mulAut_apply_inv_apply g₂ x
      calc g₂ (γ (g₂⁻¹ x)) * x⁻¹
          = g₂ (γ (g₂⁻¹ x)) * (g₂ (g₂⁻¹ x))⁻¹ := by rw [h2]
        _ = g₂ (γ (g₂⁻¹ x) * (g₂⁻¹ x)⁻¹) := by rw [map_mul, map_inv]
    rw [hval]
    have hgen : γ (g₂⁻¹ x) * (g₂⁻¹ x)⁻¹ ∈ commSub X (Subgroup.zpowers γ) :=
      Subgroup.subset_closure ⟨γ, Subgroup.mem_zpowers γ, g₂⁻¹ x, hy, rfl⟩
    have hBmem : γ (g₂⁻¹ x) * (g₂⁻¹ x)⁻¹ ∈ B := by
      rw [hBeq]; exact Subgroup.mem_sup_left hgen
    have hAmem : g₂ (γ (g₂⁻¹ x) * (g₂⁻¹ x)⁻¹) ∈ A₂ := by
      show g₂ (γ (g₂⁻¹ x) * (g₂⁻¹ x)⁻¹) ∈ B.map g₂.toMonoidHom
      exact Subgroup.mem_map.mpr ⟨_, hBmem, rfl⟩
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hAmem)
  have hS3 : e.symm L3.x31 ∈ S := by
    intro x hx
    have hy : g₃⁻¹ x ∈ X := hXinv g₃⁻¹ (L.inv_mem hg₃L) x hx
    have hval : ((e.symm L3.x31 : ↥L) : MulAut W) x * x⁻¹ =
        g₃ (γ (g₃⁻¹ x) * (g₃⁻¹ x)⁻¹) := by
      rw [ha₃]
      simp only [MulAut.mul_apply]
      have h2 : g₃ (g₃⁻¹ x) = x := mulAut_apply_inv_apply g₃ x
      calc g₃ (γ (g₃⁻¹ x)) * x⁻¹
          = g₃ (γ (g₃⁻¹ x)) * (g₃ (g₃⁻¹ x))⁻¹ := by rw [h2]
        _ = g₃ (γ (g₃⁻¹ x) * (g₃⁻¹ x)⁻¹) := by rw [map_mul, map_inv]
    rw [hval]
    have hgen : γ (g₃⁻¹ x) * (g₃⁻¹ x)⁻¹ ∈ commSub X (Subgroup.zpowers γ) :=
      Subgroup.subset_closure ⟨γ, Subgroup.mem_zpowers γ, g₃⁻¹ x, hy, rfl⟩
    have hBmem : γ (g₃⁻¹ x) * (g₃⁻¹ x)⁻¹ ∈ B := by
      rw [hBeq]; exact Subgroup.mem_sup_left hgen
    have hAmem : g₃ (γ (g₃⁻¹ x) * (g₃⁻¹ x)⁻¹) ∈ A₃ := by
      show g₃ (γ (g₃⁻¹ x) * (g₃⁻¹ x)⁻¹) ∈ B.map g₃.toMonoidHom
      exact Subgroup.mem_map.mpr ⟨_, hBmem, rfl⟩
    exact Subgroup.mem_sup_right hAmem
  have hmap : S.map e.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← L3.closure_gens, Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨e.symm L3.x12, hS1, by simp⟩
    · exact ⟨e.symm L3.x23, hS2, by simp⟩
    · exact ⟨e.symm L3.x31, hS3, by simp⟩
  have hStop : S = ⊤ := by
    rw [eq_top_iff]
    intro l _
    have hel : e l ∈ S.map e.toMonoidHom := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨s, hs, hse⟩ := hel
    have hsl : s = l := e.injective hse
    rwa [hsl] at hs
  have hcommN : commSub X L ≤ A₁ ⊔ A₂ ⊔ A₃ := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hlL, x, hxX, rfl⟩
    have hlS : (⟨l, hlL⟩ : ↥L) ∈ S := by rw [hStop]; exact Subgroup.mem_top _
    exact hlS x hxX
  have hNX : A₁ ⊔ A₂ ⊔ A₃ ≤ X := sup_le (sup_le hA₁X hA₂X) hA₃X
  have hXN : X ≤ A₁ ⊔ A₂ ⊔ A₃ := by
    rw [← hX]
    exact sup_le hcommN hMN
  have hN_eq : A₁ ⊔ A₂ ⊔ A₃ = X := le_antisymm hNX hXN
  have hrk₁ : rk ↥A₁ = rk ↥B := by
    dsimp only [A₁]
    unfold rk
    rw [Subgroup.card_map_of_injective g₁.injective]
  have hrk₂ : rk ↥A₂ = rk ↥B := by
    dsimp only [A₂]
    unfold rk
    rw [Subgroup.card_map_of_injective g₂.injective]
  have hrk₃ : rk ↥A₃ = rk ↥B := by
    dsimp only [A₃]
    unfold rk
    rw [Subgroup.card_map_of_injective g₃.injective]
  have h1 := rk_sup_add_rk_inf A₁ A₂
  have h2 : rk ↥M ≤ rk ↥(A₁ ⊓ A₂) := rk_mono (le_inf hMA₁ hMA₂)
  have h3 := rk_sup_add_rk_inf (A₁ ⊔ A₂) A₃
  have h4 : rk ↥M ≤ rk ↥((A₁ ⊔ A₂) ⊓ A₃) :=
    rk_mono (le_inf (hMA₁.trans le_sup_left) hMA₃)
  have hgoal : rk ↥(A₁ ⊔ A₂ ⊔ A₃) + 2 * rk ↥M ≤ 3 * rk ↥B := by omega
  have hXrk : rk ↥X = rk ↥(A₁ ⊔ A₂ ⊔ A₃) := by rw [hN_eq]
  rw [hXrk]
  exact hgoal

theorem s16h_e3_l3_rk_le_three_mul_commSub_of_eq {L : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {X : Subgroup W}
    (hXinv : ∀ l ∈ L, ∀ x ∈ X, l x ∈ X) (hX : commSub X L = X) {γ : MulAut W} (hγL : γ ∈ L)
    (hγ2 : γ ^ 2 = 1) (hγ1 : γ ≠ 1) :
    rk ↥X ≤ 3 * rk ↥(commSub X (Subgroup.zpowers γ)) := by
  have hMinv : ∀ l ∈ L, ∀ m ∈ (⊥ : Subgroup W), l m ∈ (⊥ : Subgroup W) := by
    intro l _ m hm
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm, map_one]
  have hX' : commSub X L ⊔ (⊥ : Subgroup W) = X := by rw [hX, sup_bot_eq]
  have h := s16h_e3_l3_rk_le_three_mul_commSub hL hXinv hMinv hX' hγL hγ2 hγ1
  rw [rk_bot, sup_bot_eq] at h
  omega

theorem s16h_e3_l3_rk_add_three_le (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {X Y : Subgroup W} (hXinv : ∀ l ∈ L, ∀ x ∈ X, l x ∈ X)
    (hYinv : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) (hYX : Y ≤ X)
    (hnt : ∃ l ∈ L, ∃ x ∈ X, l x * x⁻¹ ∉ Y) :
    rk ↥Y + 3 ≤ rk ↥X := by
  by_contra hcon
  rw [not_le] at hcon
  haveI : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hL).2
  have hL24 : 24 < Nat.card ↥L := by
    rw [card_eq_168_of_isPSL_three_two hL]
    norm_num
  have hsec : Nat.card (↥X ⧸ Y.subgroupOf X) ≤ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf X)
    have h2 : Nat.card ↥(Y.subgroupOf X) = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
    rw [h2, card_eq_two_pow hW X, card_eq_two_pow hW Y] at h1
    have h3 : rk ↥X ≤ rk ↥Y + 2 := by omega
    have h4 : 2 ^ rk ↥X ≤ 4 * 2 ^ rk ↥Y := by
      calc 2 ^ rk ↥X ≤ 2 ^ (rk ↥Y + 2) := Nat.pow_le_pow_right (by norm_num) h3
        _ = 4 * 2 ^ rk ↥Y := by rw [pow_add]; ring
    rw [h1] at h4
    exact Nat.le_of_mul_le_mul_right h4 (Nat.pow_pos (by norm_num))
  obtain ⟨l, hlL, x, hxX, hlx⟩ := hnt
  exact hlx (commutator_mem_of_sec_small hL24 hXinv hYinv hsec l hlL x hxX)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
