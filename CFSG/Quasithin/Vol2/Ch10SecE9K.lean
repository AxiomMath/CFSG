module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LG
public import CFSG.Quasithin.Vol2.Ch10SecBXi

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem mkO2_eq_iff (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {x x' : G}
    (hx : x ∈ XOf T L Ψ A) (hx' : x' ∈ XOf T L Ψ A) :
    mkO2 (XOf T L Ψ A) x hx = mkO2 (XOf T L Ψ A) x' hx' ↔
      Ψ ⟨x, XOf_le_fsuL0 h hD hx⟩ * (Ψ ⟨x', XOf_le_fsuL0 h hD hx'⟩)⁻¹ ∈ E.prod E := by
  have hXL0 := XOf_le_fsuL0 h hD
  have e : Ψ ⟨x, hXL0 hx⟩ * (Ψ ⟨x', hXL0 hx'⟩)⁻¹ =
      Ψ ⟨x * x'⁻¹, hXL0 ((XOf T L Ψ A).mul_mem hx ((XOf T L Ψ A).inv_mem hx'))⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [mk_eq_mk_iff, pCoreOf_XOf h hD, e]
  constructor
  · rintro ⟨-, hm⟩
    obtain ⟨hl, hΨ⟩ := mem_preIn.mp hm
    exact hΨ
  · intro hm
    exact ⟨(XOf T L Ψ A).mul_mem hx ((XOf T L Ψ A).inv_mem hx'), mem_preIn.mpr ⟨_, hm⟩⟩

omit [Finite G] in
theorem conjQuot_mul_apply {H : Subgroup G} {a b : G} (ha : H.map (MulAut.conj a).toMonoidHom = H)
    (hb : H.map (MulAut.conj b).toMonoidHom = H)
    (hab : H.map (MulAut.conj (a * b)).toMonoidHom = H) (q : ↥H ⧸ CFSG.pCore 2 ↥H) :
    C10P34.conjQuot H H (a * b) hab q = C10P34.conjQuot H H a ha (C10P34.conjQuot H H b hb q) := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hbk : b * k * b⁻¹ ∈ H := by
    have := Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hk
    rw [hb] at this; exact this
  have habk : a * (b * k * b⁻¹) * a⁻¹ ∈ H := by
    have := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hbk
    rw [ha] at this; exact this
  have habk' : a * b * k * (a * b)⁻¹ ∈ H := by
    have e : a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
    rw [e]; exact habk
  rw [C10P34.conjQuot_mk hab hk habk', C10P34.conjQuot_mk hb hk hbk,
    C10P34.conjQuot_mk ha hbk habk]
  exact congrArg _ (Subtype.ext (show a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ by group))

omit [Finite G] in
theorem conjQuot_congr {H : Subgroup G} {g g' : G} (hg : H.map (MulAut.conj g).toMonoidHom = H)
    (hg' : H.map (MulAut.conj g').toMonoidHom = H) (e : g = g') :
    C10P34.conjQuot H H g hg = C10P34.conjQuot H H g' hg' := by
  subst e; rfl

omit [Finite G] in
theorem map_conj_inv_eq {H : Subgroup G} {g : G} (hg : H.map (MulAut.conj g).toMonoidHom = H) :
    H.map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [A38.map_conj_eq_iff] at hg ⊢
  exact Subgroup.inv_mem _ hg

omit [Finite G] in
theorem conjQuot_conj {H : Subgroup G} {y s : G} (hy : H.map (MulAut.conj y).toMonoidHom = H)
    (hs : H.map (MulAut.conj s).toMonoidHom = H)
    (hys : H.map (MulAut.conj (y * s * y⁻¹)).toMonoidHom = H) :
    C10P34.conjQuot H H y hy * C10P34.conjQuot H H s hs * (C10P34.conjQuot H H y hy)⁻¹ =
      C10P34.conjQuot H H (y * s * y⁻¹) hys := by
  have hyi := map_conj_inv_eq hy
  have hinv : (C10P34.conjQuot H H y hy)⁻¹ = C10P34.conjQuot H H y⁻¹ hyi := by
    rw [inv_eq_iff_mul_eq_one]
    ext q
    have h1 : H.map (MulAut.conj (y * y⁻¹)).toMonoidHom = H :=
      A38.map_conj_eq_iff.mpr (by rw [mul_inv_cancel]; exact Subgroup.one_mem _)
    rw [MulAut.mul_apply, ← conjQuot_mul_apply hy hyi h1, MulAut.one_apply]
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hk' : y * y⁻¹ * k * (y * y⁻¹)⁻¹ ∈ H := by simpa using hk
    rw [C10P34.conjQuot_mk h1 hk hk']
    exact congrArg _ (Subtype.ext (show y * y⁻¹ * k * (y * y⁻¹)⁻¹ = k by group))
  rw [hinv]
  ext q
  have hsy : H.map (MulAut.conj (s * y⁻¹)).toMonoidHom = H := by
    rw [A38.map_conj_eq_iff] at hs hyi ⊢
    exact Subgroup.mul_mem _ hs hyi
  have hys' : H.map (MulAut.conj (y * (s * y⁻¹))).toMonoidHom = H := by
    rw [← mul_assoc]; exact hys
  rw [MulAut.mul_apply, MulAut.mul_apply, ← conjQuot_mul_apply hs hyi hsy,
    ← conjQuot_mul_apply hy hsy hys', conjQuot_congr hys' hys (by group)]

omit [Finite G] in
theorem mem_of_inv_act (hD : ParData A K E) {d k : L32.Γ}
    (hd : ∀ k ∈ K, d * k * d⁻¹ * k ∈ E) (hk : k ∈ K) (h : d * k * d⁻¹ * k⁻¹ ∈ E) : k ∈ E := by
  have h1 : (d * k * d⁻¹ * k⁻¹)⁻¹ * (d * k * d⁻¹ * k) ∈ E := E.mul_mem (E.inv_mem h) (hd k hk)
  have e1 : (d * k * d⁻¹ * k⁻¹)⁻¹ * (d * k * d⁻¹ * k) = k * k := by group
  rw [e1] at h1
  have h2 := hD.cube k hk
  have e2 : k = k * k * k * (k * k)⁻¹ := by group
  rw [e2]
  exact E.mul_mem h2 (E.inv_mem h1)

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
