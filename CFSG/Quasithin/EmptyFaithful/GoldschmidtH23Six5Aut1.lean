module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5AutDefs

public section

namespace CFSG.Quasithin

namespace SixData151b

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

private theorem iff_of_forall_mem {H : Subgroup W} {g : MulAut W} (h : ∀ w ∈ H, g w ∈ H) :
    ∀ w : W, w ∈ H ↔ g w ∈ H := by
  intro w
  refine ⟨h w, fun hw => ?_⟩
  have hinj : Function.Injective (fun x : H => (⟨g x, h x x.2⟩ : H)) := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hinj ⟨g w, hw⟩
  have hx' : g x = g w := congrArg Subtype.val hx
  rw [← g.injective hx']
  exact x.2

omit [Finite W] in
private theorem eq_of_mul_eq_of_inf_eq_bot {U V : Subgroup W} (hUV : U ⊓ V = ⊥) {u u' v v' : W}
    (hu : u ∈ U) (hu' : u' ∈ U) (hv : v ∈ V) (hv' : v' ∈ V) (h : u * v = u' * v') :
    u = u' ∧ v = v' := by
  have h1 : u'⁻¹ * u = v' * v⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * v) * v⁻¹ := by group
      _ = u'⁻¹ * (u' * v') * v⁻¹ := by rw [h]
      _ = v' * v⁻¹ := by group
  have hmem : u'⁻¹ * u ∈ U ⊓ V :=
    ⟨U.mul_mem (U.inv_mem hu') hu, h1 ▸ V.mul_mem hv' (V.inv_mem hv)⟩
  rw [hUV, Subgroup.mem_bot] at hmem
  have hu2 : u = u' := by
    have := congrArg (u' * ·) hmem
    simpa using this
  refine ⟨hu2, ?_⟩
  rw [hu2] at h
  exact mul_left_cancel h

private theorem W₂_eq_commSub_a₂ (hW : ∀ w : W, w ^ 2 = 1) :
    S.W₂ = commSub (⊤ : Subgroup W) (Subgroup.zpowers S.a₂) := by
  have h := S.swap.W₁_eq_commSub_a₁ (Or.inr rfl) hW
  rwa [swap_W₁, swap_a₁] at h

private theorem stab₁_of_conj (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W}
    (h : g * S.a₁ * g⁻¹ ∈ Subgroup.zpowers S.a₁) : S.Stab₁ g := by
  refine iff_of_forall_mem fun w hw => ?_
  rw [S.W₁_eq_commSub_a₁ (Or.inr rfl) hW] at hw ⊢
  exact commSub_top_stable151b (conj_mem_zpowers151b h) w hw

private theorem stab₂_of_conj (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W}
    (h : g * S.a₂ * g⁻¹ ∈ Subgroup.zpowers S.a₂) : S.Stab₂ g := by
  refine iff_of_forall_mem fun w hw => ?_
  rw [S.W₂_eq_commSub_a₂ hW] at hw ⊢
  exact commSub_top_stable151b (conj_mem_zpowers151b h) w hw

private theorem swap_of_typeII (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W} (h : S.TypeII g) :
    S.Swap₁₂ g := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [S.W₁_eq_commSub_a₁ (Or.inr rfl) hW] at hw
    rw [S.W₂_eq_commSub_a₂ hW]
    exact commSub_top_map151b (conj_mem_zpowers151b h.1) w hw
  · rw [S.W₂_eq_commSub_a₂ hW] at hw
    rw [S.W₁_eq_commSub_a₁ (Or.inr rfl) hW]
    exact commSub_top_map151b (conj_mem_zpowers151b h.2) w hw

theorem stab_or_swap (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W}
    (hg : ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) :
    (S.Stab₁ g ∧ S.Stab₂ g) ∨ S.Swap₁₂ g := by
  rcases S.typeI_or_typeII (Or.inr rfl) hW hg with hI | hII
  · exact Or.inl ⟨S.stab₁_of_conj hW hI.1, S.stab₂_of_conj hW hI.2⟩
  · exact Or.inr (S.swap_of_typeII hW hII)

theorem swap_of_conj (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W}
    (hg : ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂)
    (h₁ : ∀ a ∈ S.A₁, g * a * g⁻¹ ∈ S.A₂) : S.Swap₁₂ g :=
  S.swap_of_typeII hW (S.typeII_of_swap (Or.inr rfl) hW hg h₁)

theorem stab_of_mem_A₀ {x : MulAut W} (hx : x ∈ S.A₁ ⊔ S.A₂) : S.Stab₁ x ∧ S.Stab₂ x := by
  obtain ⟨s11, s22, s12, s21⟩ := six_module151b S.comm S.winf
  have h₁ : S.A₁ ⊔ S.A₂ ≤ stabSub S.W₁ := by
    refine sup_le (fun a ha => mem_stabSub.mpr fun u => (iff_of_forall_mem (s11 a ha) u).symm)
      fun b hb => centSub_le_stabSub S.W₁ (mem_centSub.mpr fun u hu => s21 b hb u hu)
  have h₂ : S.A₁ ⊔ S.A₂ ≤ stabSub S.W₂ := by
    refine sup_le (fun a ha => centSub_le_stabSub S.W₂ (mem_centSub.mpr fun u hu => s12 a ha u hu))
      fun b hb => mem_stabSub.mpr fun u => (iff_of_forall_mem (s22 b hb) u).symm
  exact ⟨fun u => (mem_stabSub.mp (h₁ hx) u).symm, fun u => (mem_stabSub.mp (h₂ hx) u).symm⟩

theorem not_stab₁_of_swap (hcard : Nat.card W = 256) {g : MulAut W} (h : S.Swap₁₂ g) :
    ¬ S.Stab₁ g := by
  intro hs
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ S.W₁, w ≠ 1 := by
    by_contra hcon
    have hbot : S.W₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
      by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h1 := Subgroup.card_eq_one.mpr hbot
    have h16 := S.card_W₁ hcard
    omega
  have h3 : g w ∈ S.W₁ ⊓ S.W₂ := ⟨(hs w).1 hw, h.1 w hw⟩
  rw [S.winf, Subgroup.mem_bot] at h3
  exact hw1 (g.injective (h3.trans (map_one g).symm))

theorem stab_mul_of_swap {f g : MulAut W} (hf : S.Swap₁₂ f) (hg : S.Swap₁₂ g) :
    S.Stab₁ (f * g) ∧ S.Stab₂ (f * g) := by
  refine ⟨iff_of_forall_mem fun w hw => ?_, iff_of_forall_mem fun w hw => ?_⟩
  · exact hf.2 _ (hg.1 w hw)
  · exact hf.1 _ (hg.2 w hw)

set_option linter.unusedSectionVars false in
theorem a₂_fix_W₁ {w : W} (hw : w ∈ S.W₁) : S.a₂ w = w :=
  (six_module151b S.comm S.winf).2.2.2 S.a₂ S.a₂_mem w hw

theorem mem_zpowers_a₂_conj (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {g : MulAut W} (hg : ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂)
    (hs : S.Stab₁ g ∧ S.Stab₂ g) : g * S.a₂ * g⁻¹ ∈ Subgroup.zpowers S.a₂ := by
  rcases S.typeI_or_typeII (Or.inr rfl) hW hg with hI | hII
  · exact hI.2
  · exact absurd hs.1 (S.not_stab₁_of_swap hcard (S.swap_of_typeII hW hII))

set_option linter.unusedSectionVars false in
theorem fixV_eq_sup {P : Subgroup (MulAut W)} (hP : ∀ g ∈ P, S.Stab₁ g ∧ S.Stab₂ g) :
    fixV P = (S.W₁ ⊓ fixV P) ⊔ (S.W₂ ⊓ fixV P) := by
  refine le_antisymm (fun w hw => ?_) (sup_le inf_le_right inf_le_right)
  have hw' : w ∈ S.W₁ ⊔ S.W₂ := by rw [S.wsup]; exact Subgroup.mem_top w
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hw'
  have hfix : ∀ g ∈ P, g u = u ∧ g v = v := by
    intro g hg
    have h3 : g u * g v = u * v := by rw [← map_mul]; exact mem_fixV.mp hw g hg
    exact eq_of_mul_eq_of_inf_eq_bot S.winf (((hP g hg).1 u).1 hu) hu (((hP g hg).2 v).1 hv) hv h3
  exact Subgroup.mul_mem_sup ⟨hu, mem_fixV.mpr fun g hg => (hfix g hg).1⟩
    ⟨hv, mem_fixV.mpr fun g hg => (hfix g hg).2⟩

end SixData151b

end CFSG.Quasithin
