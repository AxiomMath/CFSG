module

public import CFSG.Quasithin.Background.G116IIIA5
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isCompl_conjSub_of_irr [Finite V] {Γ H : Subgroup (GLV V)}
    (hN : ∀ γ ∈ Γ, ∀ n ∈ H, γ * n * γ⁻¹ ∈ H) {I : Submodule (ZMod 2) V} (hI : IsIrr H I)
    {x : GLV V} (hx : x ∈ Γ) (hxI : conjSub x I ≠ I)
    (hdim : 2 * Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) V) :
    IsCompl I (conjSub x I) := by
  rcases hI.conj_eq_or_inf_eq_bot hN hx with h | h
  · exact absurd h hxI
  · have hinf : I ⊓ conjSub x I = ⊥ := by rw [inf_comm]; exact h
    have hsup : I ⊔ conjSub x I = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq I (conjSub x I)
      rw [hinf, finrank_bot, finrank_conjSub] at h1
      omega
    exact IsCompl.of_eq hinf hsup

theorem commSpace_map_conj_top (K : Subgroup (GLV V)) (g : GLV V) :
    commSpace (K.map (MulAut.conj g).toMonoidHom) ⊤ = conjSub g (commSpace K ⊤) := by
  unfold commSpace conjSub
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨k', hk', u, -, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
    refine ⟨k (g⁻¹ u) - g⁻¹ u, ⟨k, hk, g⁻¹ u, trivial, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]
  · rintro ⟨w', ⟨k, hk, u, -, rfl⟩, rfl⟩
    refine ⟨g * k * g⁻¹, ⟨k, hk, ?_⟩, g u, trivial, ?_⟩
    · simp [MulAut.conj_apply]
    · simp

theorem commSpanOf_eq_commSpace_top [Finite V] (L : Subgroup (GLV V)) :
    commSpanOf L = commSpace L ⊤ := by
  unfold commSpanOf commSpace
  congr 1
  ext w
  simp

theorem conj_map_trivial_on {L : Subgroup (GLV V)} {x : GLV V} (hx2 : x * x = 1)
    {I : Submodule (ZMod 2) V} (hfix : conjSub x I = fixedSpace L) :
    ∀ b ∈ L.map (MulAut.conj x).toMonoidHom, ∀ v ∈ I, b v = v := by
  intro b hb v hv
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hb
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h1 : x v ∈ fixedSpace L := by
    rw [← hfix]
    exact apply_mem_conjSub hv
  have h2 : l (x v) = x v := h1 l hl
  have h3 : x (x v) = v := by
    have := congrArg (fun m : GLV V => m v) hx2
    simpa using this
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxinv]
  calc (x * l * x) v = x (l (x v)) := rfl
    _ = x (x v) := by rw [h2]
    _ = v := h3

theorem eq_one_of_fixes_isCompl {I J : Submodule (ZMod 2) V} (h : IsCompl I J) {g : GLV V}
    (hI : ∀ v ∈ I, g v = v) (hJ : ∀ v ∈ J, g v = v) : g = 1 := by
  ext v
  have hv : v ∈ I ⊔ J := by rw [h.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hI a ha, hJ b hb]
  simp

theorem mul_comm_of_isCompl_fixes {I J : Submodule (ZMod 2) V} (h : IsCompl I J) {a b : GLV V}
    (haI : ∀ v ∈ I, a v ∈ I) (hbJ : ∀ v ∈ J, b v ∈ J)
    (haJ : ∀ v ∈ J, a v = v) (hbI : ∀ v ∈ I, b v = v) : a * b = b * a := by
  ext v
  have hv : v ∈ I ⊔ J := by rw [h.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  show a (b (u + w)) = b (a (u + w))
  simp only [map_add]
  rw [hbI u hu, haJ w hw, hbI _ (haI u hu), haJ _ (hbJ w hw)]

theorem inf_map_conj_eq_bot_of_isCompl {L : Subgroup (GLV V)} {x : GLV V}
    {I J : Submodule (ZMod 2) V} (h : IsCompl I J) (hL : ∀ a ∈ L, ∀ v ∈ J, a v = v)
    (hLx : ∀ b ∈ L.map (MulAut.conj x).toMonoidHom, ∀ v ∈ I, b v = v) :
    L ⊓ L.map (MulAut.conj x).toMonoidHom = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  exact eq_one_of_fixes_isCompl h (hLx g hg.2) (hL g hg.1)

theorem apply_mem_commSpace_top_of_commute {L : Subgroup (GLV V)} {c : GLV V}
    (hc : ∀ l ∈ L, c * l = l * c) {w : V} (hw : w ∈ commSpace L ⊤) : c w ∈ commSpace L ⊤ := by
  have hcent : c ∈ Subgroup.centralizer (L : Set (GLV V)) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => (hc l hl).symm
  have hinv : Invariant (Subgroup.centralizer (L : Set (GLV V))) (commSpace L ⊤) := by
    refine invariant_commSpace (fun k' hk' k hk => ?_) (invariant_top _)
    have := Subgroup.mem_centralizer_iff.1 hk' k hk
    rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  exact hinv c hcent w hw

theorem eq_one_of_commute_L_Lx {L : Subgroup (GLV V)} {x : GLV V} {I : Submodule (ZMod 2) V}
    (hA5 : IsA5Module L I) (hIL : I = commSpace L ⊤) (hinv : Invariant L I)
    (hcompl : IsCompl I (conjSub x I)) {c : GLV V}
    (hcL : ∀ l ∈ L, c * l = l * c)
    (hcLx : ∀ b ∈ L.map (MulAut.conj x).toMonoidHom, c * b = b * c) : c = 1 := by
  have key : ∀ d : GLV V, (∀ l ∈ L, d * l = l * d) → ∀ v ∈ I, d v = v := by
    intro d hd
    refine hA5.fixes_of_commute hinv (fun v hv => ?_) (fun l hl v _ => ?_)
    · rw [hIL] at hv ⊢
      exact apply_mem_commSpace_top_of_commute hd hv
    · exact congrArg (fun m : GLV V => m v) (hd l hl)
  have hcI := key c hcL
  have hc' : ∀ l ∈ L, (x⁻¹ * c * x) * l = l * (x⁻¹ * c * x) := by
    intro l hl
    have hb := hcLx (x * l * x⁻¹) ⟨l, hl, by simp [MulAut.conj_apply]⟩
    calc x⁻¹ * c * x * l = x⁻¹ * (c * (x * l * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * l * x⁻¹) * c) * x := by rw [hb]
      _ = l * (x⁻¹ * c * x) := by group
  have hc'I := key _ hc'
  refine eq_one_of_fixes_isCompl hcompl hcI (fun w hw => ?_)
  obtain ⟨v, hv, rfl⟩ := hw
  have h1 := hc'I v hv
  have hxx : x * (x⁻¹ * c * x) = c * x := by group
  calc c ((x : V →ₗ[ZMod 2] V) v) = (c * x) v := rfl
    _ = (x * (x⁻¹ * c * x)) v := by rw [hxx]
    _ = x ((x⁻¹ * c * x) v) := rfl
    _ = x v := by rw [h1]

end G11

end CFSG.Quasithin
