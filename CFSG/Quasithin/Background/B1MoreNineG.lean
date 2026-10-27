module

public import CFSG.Quasithin.Background.B1MoreNineF

public section

namespace CFSG.Quasithin

open CFSG.Open B19Aux

variable {V : Type*} [CommGroup V]

section Xk

variable [Finite V] {X : Subgroup (MulAut V)}

theorem Xk_fix_commV (hV : ∀ v : V, v ^ 2 = 1) {Y Z : Subgroup (MulAut V)} (hY : Y ∈ Xk X 1)
    (hZ : Z ∈ Xk X 1) (hne : Y ≠ Z) : ∀ y ∈ Y, ∀ w ∈ commV Z, y w = w := by
  have hcomm : ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y := fun y hy z hz =>
    Xk_commute hV (Or.inl rfl) Y hY Z hZ y hy z hz
  have hdisj : Disjoint (commV Y) (commV Z) :=
    (D2_12_2 hV (X := X) (Or.inl rfl)).2.pairwiseDisjoint (i := ⟨Y, hY⟩) (j := ⟨Z, hZ⟩)
      (fun h => hne (congrArg Subtype.val h))
  have hinf : commV Y ⊓ commV Z = ⊥ := disjoint_iff.1 hdisj
  intro y hy w hw
  have hinv : ∀ c ∈ commSub (⊤ : Subgroup V) Z, y c ∈ commSub (⊤ : Subgroup V) Z :=
    B1.commSub_invariant_of_commute (M := (⊤ : Subgroup V))
      (fun z hz b hb => (hcomm b hb z hz).symm) (fun _ _ _ _ => Subgroup.mem_top _) y hy
  rw [commV_eq_commSub] at hw
  have h1 : y w * w⁻¹ ∈ commV Y := Subgroup.subset_closure ⟨y, hy, w, rfl⟩
  have h2 : y w * w⁻¹ ∈ commV Z := by
    rw [commV_eq_commSub]
    exact (commSub ⊤ Z).mul_mem (hinv w hw) ((commSub ⊤ Z).inv_mem hw)
  have h3 : y w * w⁻¹ ∈ commV Y ⊓ commV Z := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h3
  exact h3

end Xk

namespace B19Loc

variable [Finite V] {G A A' : Subgroup (MulAut V)}

theorem A_centralizes_FA' (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) (P' : B19Loc G A')
    (hne : FAsub G A ≠ FAsub G A') : ∀ a ∈ A, ∀ y ∈ FAsub G A', a * y = y * a := by
  have hY := P.FA_mem_Xk hV
  have hY' := P'.FA_mem_Xk hV
  have hVfix : ∀ w ∈ commV (FAsub G A'), w ∈ fixV (FAsub G A) := fun w hw y hy =>
    Xk_fix_commV hV hY hY' hne y hy w hw
  intro a ha
  have haW : ∀ w ∈ commV (FAsub G A'), a w = w := fun w hw => P.A_trivial_fixV hV w (hVfix w hw) a ha
  have hconj : conjBy a (FAsub G A') ∈ Xk G 1 := conjBy_mem_Xk (P.A_le ha) hY'
  have hact : ∀ y ∈ FAsub G A', ∀ w ∈ commV (FAsub G A'), (a * y * a⁻¹) w = y w := by
    intro y hy w hw
    have hyw : y w ∈ commV (FAsub G A') := by
      rw [commV_eq_commSub] at hw ⊢
      exact commSub_inv_H (FAsub G A') ⊤ y hy w hw
    have h1 : a⁻¹ w = w := by
      have := haW w hw
      calc a⁻¹ w = a⁻¹ (a w) := by rw [this]
        _ = w := by simp
    simp only [MulAut.mul_apply]
    rw [h1, haW _ hyw]
  have heq : conjBy a (FAsub G A') = FAsub G A' := by
    by_contra hne'
    have hcentral : ∀ y'' ∈ conjBy a (FAsub G A'), ∀ w ∈ commV (FAsub G A'), y'' w = w :=
      Xk_fix_commV hV hconj hY' hne'
    have htriv : ∀ y ∈ FAsub G A', y = 1 := by
      intro y hy
      refine Xk_faithful hV hY' hy fun w hw => ?_
      rw [← hact y hy w hw]
      exact hcentral _ (mem_conjBy_of_mem hy) w hw
    have hcard := P'.local_structure hV
    obtain ⟨-, hc3, -⟩ := hcard
    have : Nat.card ↥(FAsub G A') = 1 := by
      rw [Subgroup.card_eq_one]
      exact (Subgroup.eq_bot_iff_forall _).2 htriv
    omega
  intro y hy
  have hmem : a * y * a⁻¹ ∈ FAsub G A' := by
    have : a * y * a⁻¹ ∈ conjBy a (FAsub G A') := mem_conjBy_of_mem hy
    rwa [heq] at this
  have h2 : a * y * a⁻¹ = y := by
    have h3 : (a * y * a⁻¹) * y⁻¹ = 1 := by
      refine Xk_faithful hV hY' ((FAsub G A').mul_mem hmem ((FAsub G A').inv_mem hy)) ?_
      intro w hw
      have hyinv : y⁻¹ ∈ FAsub G A' := (FAsub G A').inv_mem hy
      have hw' : y⁻¹ w ∈ commV (FAsub G A') := by
        rw [commV_eq_commSub] at hw ⊢
        exact commSub_inv_H (FAsub G A') ⊤ y⁻¹ hyinv w hw
      show (a * y * a⁻¹) (y⁻¹ w) = w
      rw [hact y hy _ hw']
      simp
    exact mul_inv_eq_one.1 h3
  calc a * y = (a * y * a⁻¹) * a := by group
    _ = y * a := by rw [h2]

theorem A_comm_A' (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) (P' : B19Loc G A')
    (hne : FAsub G A ≠ FAsub G A') : ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a := by
  intro a ha a' ha'
  have hY := P.FA_mem_Xk hV
  have hY' := P'.FA_mem_Xk hV
  have hVY : ∀ w ∈ commV (FAsub G A), w ∈ fixV (FAsub G A') := fun w hw y hy =>
    Xk_fix_commV hV hY' hY hne.symm y hy w hw
  have ha'cent : ∀ y ∈ FAsub G A, a' * y = y * a' :=
    P'.A_centralizes_FA' hV P hne.symm a' ha'
  obtain ⟨-, -, -, hWcomm, -⟩ := P.local_structure hV
  have haW : ∀ w ∈ commV (FAsub G A), a w ∈ commV (FAsub G A) := by
    intro w hw
    rw [← hWcomm] at hw ⊢
    exact P.W_inv_A ha w hw
  have hsup := P.commV_FA_sup_fixV hV
  ext v
  have hv : v ∈ commV (FAsub G A) ⊔ fixV (FAsub G A) := by rw [hsup]; trivial
  obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
  have hx' : a' x = x := P'.A_trivial_fixV hV x (hVY x hx) a' ha'
  have hax' : a' (a x) = a x := P'.A_trivial_fixV hV _ (hVY _ (haW x hx)) a' ha'
  have hz1 : a z = z := P.A_trivial_fixV hV z hz a ha
  have hz2 : a' z ∈ fixV (FAsub G A) := by
    intro y hy
    have := congrArg (fun t : MulAut V => t z) (ha'cent y hy)
    simp only [MulAut.mul_apply] at this
    exact this.symm.trans (congrArg a' (hz y hy))
  have hz3 : a (a' z) = a' z := P.A_trivial_fixV hV _ hz2 a ha
  show a (a' (x * z)) = a' (a (x * z))
  rw [map_mul, map_mul, map_mul, map_mul, hx', hax', hz1, hz3]

theorem GY_comm (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) (P' : B19Loc G A')
    (hne : FAsub G A ≠ FAsub G A') : ∀ g ∈ FAsub G A ⊔ A, ∀ g' ∈ FAsub G A' ⊔ A', g * g' = g' * g := by
  intro g hg g' hg'
  obtain ⟨f, hf, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer (A_normalizes_FA G A)).1 hg
  obtain ⟨f', hf', a', ha', rfl⟩ := (mem_sup_iff_of_le_normalizer (A_normalizes_FA G A')).1 hg'
  have h1 : Commute f f' :=
    Xk_commute hV (Or.inl rfl) _ (P.FA_mem_Xk hV) _ (P'.FA_mem_Xk hV) f hf f' hf'
  have h2 : Commute f a' := (P'.A_centralizes_FA' hV P hne.symm a' ha' f hf).symm
  have h3 : Commute a f' := P.A_centralizes_FA' hV P' hne a ha f' hf'
  have h4 : Commute a a' := P.A_comm_A' hV P' hne a ha a' ha'
  exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq

end B19Loc

end CFSG.Quasithin
