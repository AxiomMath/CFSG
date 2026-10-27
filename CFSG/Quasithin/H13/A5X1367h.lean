module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.H13.A5X1367f

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin

section Cards

variable {A : Type} [CommGroup A] [Finite A]

theorem card_mul_le_of_disjoint {E C W : Subgroup A} (hEC : E ⊓ C = ⊥) (hEW : E ≤ W)
    (hCW : C ≤ W) : Nat.card ↥E * Nat.card ↥C ≤ Nat.card ↥W := by
  let f : ↥E × ↥C → ↥W := fun p => ⟨(p.1 : A) * p.2, W.mul_mem (hEW p.1.2) (hCW p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨e, c⟩ ⟨e', c'⟩ h
    have h1 : (e : A) * c = e' * c' := congrArg Subtype.val h
    have h2 : (e' : A)⁻¹ * e = c' * (c : A)⁻¹ := by
      calc (e' : A)⁻¹ * e = (e' : A)⁻¹ * (e * c) * (c : A)⁻¹ := by group
        _ = (e' : A)⁻¹ * (e' * c') * (c : A)⁻¹ := by rw [h1]
        _ = c' * (c : A)⁻¹ := by group
    have hm : (e' : A)⁻¹ * e ∈ E ⊓ C :=
      ⟨E.mul_mem (E.inv_mem e'.2) e.2, h2 ▸ C.mul_mem c'.2 (C.inv_mem c.2)⟩
    rw [hEC, Subgroup.mem_bot, inv_mul_eq_one] at hm
    have hee : e = e' := Subtype.ext hm.symm
    subst hee
    have hcc : (c : A) = c' := mul_left_cancel h1
    rw [Subtype.ext hcc]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem card_mul_eq_of_decomp {E C W : Subgroup A} (hEC : E ⊓ C = ⊥) (hEW : E ≤ W)
    (hCW : C ≤ W) (hdec : ∀ w ∈ W, ∃ e ∈ E, ∃ c ∈ C, w = e * c) :
    Nat.card ↥E * Nat.card ↥C = Nat.card ↥W := by
  refine le_antisymm (card_mul_le_of_disjoint hEC hEW hCW) ?_
  let f : ↥E × ↥C → ↥W := fun p => ⟨(p.1 : A) * p.2, W.mul_mem (hEW p.1.2) (hCW p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨e, he, c, hc, rfl⟩ := hdec w hw
    exact ⟨⟨⟨e, he⟩, ⟨c, hc⟩⟩, rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

end Cards

section DS3

variable {U : Type} [CommGroup U] [Finite U]

omit [Finite U] in
theorem phi_commV_le {J Gi Gj : Subgroup (MulAut U)} {Wi Wj : Subgroup U} (hGiJ : Gi ≤ J)
    (hGjJ : Gj ≤ J) (hc : ∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a)
    (hinvi : ∀ g ∈ J, ∀ w ∈ Wi, g w ∈ Wi) (hinvj : ∀ g ∈ J, ∀ w ∈ Wj, g w ∈ Wj)
    (hGi : commV Gi ≤ Wi) (hGj : commV Gj ≤ Wj) {y : MulAut U} (hy : y ∈ Gi) :
    ∀ a ∈ commV Gj, threePhi y a ∈ Wi ⊓ Wj := by
  have hle : commV Gj ≤ (Wi ⊓ Wj).comap (threePhi y) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨g, hg, u, rfl⟩
    refine ⟨?_, ?_⟩
    ·
      have hgy : y * g = g * y := hc y hy g hg
      have e : threePhi y (g u * u⁻¹) = g (y u * u⁻¹) * (y u * u⁻¹)⁻¹ := by
        have h1 : y (g u) = g (y u) := by
          have := congrArg (fun f : MulAut U => f u) hgy
          simpa [MulAut.mul_apply] using this
        rw [threePhi_apply, map_mul, map_inv, h1, map_mul, map_inv]
        simp only [mul_inv_rev, inv_inv, mul_assoc, mul_comm, mul_left_comm]
      have hx : y u * u⁻¹ ∈ Wi := hGi (Subgroup.subset_closure ⟨y, hy, u, rfl⟩)
      show threePhi y (g u * u⁻¹) ∈ Wi
      rw [e]
      exact Wi.mul_mem (hinvi g (hGjJ hg) _ hx) (Wi.inv_mem hx)
    · have hx : g u * u⁻¹ ∈ Wj := hGj (Subgroup.subset_closure ⟨g, hg, u, rfl⟩)
      show threePhi y (g u * u⁻¹) ∈ Wj
      rw [threePhi_apply]
      exact Wj.mul_mem (hinvj y (hGiJ hy) _ hx) (Wj.inv_mem hx)
  exact fun a ha => hle ha

theorem ds3_structure (hU2 : ∀ u : U, u * u = 1) {J Gi Gj : Subgroup (MulAut U)}
    {Wi Wj : Subgroup U} (hsup : Gi ⊔ Gj = J) (hc : ∀ a ∈ Gi, ∀ b ∈ Gj, a * b = b * a)
    (hWsup : Wi ⊔ Wj = ⊤) (hWinf : Wi ⊓ Wj = fixV J)
    (hinvi : ∀ g ∈ J, ∀ w ∈ Wi, g w ∈ Wi) (hinvj : ∀ g ∈ J, ∀ w ∈ Wj, g w ∈ Wj)
    (hWi : Wi = commV Gi ⊔ fixV J) (hWj : Wj = commV Gj ⊔ fixV J)
    (hcardi : Nat.card ↥Wi = 4 * Nat.card ↥(fixV J))
    {y : MulAut U} (hy : y ∈ Gi) (hy3 : orderOf y = 3) :
    (threePhi y).range ≤ Wi ∧ Nat.card ↥(threePhi y).range = 4 ∧ (threePhi y).ker = Wj := by
  have hGiJ : Gi ≤ J := hsup ▸ le_sup_left
  have hGjJ : Gj ≤ J := hsup ▸ le_sup_right
  have hyJ : y ∈ J := hGiJ hy
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hCi : fixV J ≤ Wi := hWinf ▸ inf_le_left
  have hCj : fixV J ≤ Wj := hWinf ▸ inf_le_right
  have hGi : commV Gi ≤ Wi := hWi ▸ le_sup_left
  have hGj : commV Gj ≤ Wj := hWj ▸ le_sup_left
  have hyC : ∀ c ∈ fixV J, y c = c := fun c hc => hc y hyJ
  have hyWj : ∀ w ∈ Wj, y w = w := by
    refine three_trivial_of_comm hU2 hy3' (fun w hw => ?_) hyC
    have hw' : w ∈ commV Gj ⊔ fixV J := hWj ▸ hw
    obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp hw'
    rw [map_mul, show threePhi y c = 1 from by rw [threePhi_apply, hyC c hc', mul_inv_cancel],
      mul_one, ← hWinf]
    exact phi_commV_le hGiJ hGjJ hc hinvi hinvj hGi hGj hy a ha
  have hCker : fixV J ≤ (threePhi y).ker := fun c hc => mem_ker_threePhi.mpr (hyC c hc)
  have hWjker : Wj ≤ (threePhi y).ker := fun w hw => mem_ker_threePhi.mpr (hyWj w hw)
  have hEW : (threePhi y).range ≤ Wi := by
    rintro _ ⟨u, rfl⟩
    have hu : u ∈ Wi ⊔ Wj := by rw [hWsup]; exact Subgroup.mem_top u
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, show threePhi y b = 1 from (MonoidHom.mem_ker).mp (hWjker hb), mul_one,
      threePhi_apply]
    exact Wi.mul_mem (hinvi y hyJ a ha) (Wi.inv_mem ha)
  have hEC : (threePhi y).range ⊓ fixV J = ⊥ :=
    eq_bot_iff.mpr fun x hx => by
      have : x ∈ (threePhi y).range ⊓ (threePhi y).ker := ⟨hx.1, hCker hx.2⟩
      rwa [three_range_inf_ker hU2 hy3'] at this
  have hy1 : ∃ u, y u ≠ u := by
    by_contra hcon
    push Not at hcon
    have : y = 1 := MulEquiv.ext hcon
    rw [this, orderOf_one] at hy3
    omega
  have hcard : Nat.card ↥(threePhi y).range = 4 := by
    refine le_antisymm ?_ (four_le_card_three_range hU2 hy3' hy1)
    have h1 := card_mul_le_of_disjoint hEC hEW hCi
    rw [hcardi] at h1
    have hpos : 0 < Nat.card ↥(fixV J) := Nat.card_pos
    exact Nat.le_of_mul_le_mul_right h1 hpos
  refine ⟨hEW, hcard, le_antisymm ?_ hWjker⟩
  set K := Wi ⊓ (threePhi y).ker with hK
  have hKdec : ∀ w ∈ Wi, ∃ e ∈ (threePhi y).range, ∃ c ∈ K, w = e * c := by
    intro w hw
    obtain ⟨h1, h2⟩ := three_decomp hU2 hy3' w
    refine ⟨_, ⟨y w, rfl⟩, w * y w * y (y w), ⟨?_, h2⟩, h1.symm⟩
    exact Wi.mul_mem (Wi.mul_mem hw (hinvi y hyJ w hw)) (hinvi y hyJ _ (hinvi y hyJ w hw))
  have hEK : (threePhi y).range ⊓ K = ⊥ :=
    eq_bot_iff.mpr fun x hx => by
      have : x ∈ (threePhi y).range ⊓ (threePhi y).ker := ⟨hx.1, hx.2.2⟩
      rwa [three_range_inf_ker hU2 hy3'] at this
  have hcardK := card_mul_eq_of_decomp hEK hEW inf_le_left hKdec
  rw [hcard, hcardi] at hcardK
  have hCK : fixV J ≤ K := le_inf hCi hCker
  have hKC : K = fixV J :=
    (Subgroup.eq_of_le_of_card_ge hCK (by omega)).symm
  intro u hu
  have hu' : u ∈ Wi ⊔ Wj := by rw [hWsup]; exact Subgroup.mem_top u
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu'
  have hak : a ∈ (threePhi y).ker := by
    rw [mem_ker_threePhi] at hu ⊢
    rw [map_mul, hyWj b hb] at hu
    exact mul_right_cancel hu
  have haC : a ∈ fixV J := hKC ▸ (⟨ha, hak⟩ : a ∈ K)
  exact Wj.mul_mem (hCj haC) hb

end DS3

end CFSG.Quasithin.H13.A5
