module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Conj

public section

namespace CFSG.Quasithin.H11

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

@[expose] def mapAut (A : Subgroup (MulAut V)) : Subgroup (MulAut V') :=
  A.map (MulAut.congr e).toMonoidHom

theorem congr_apply' (f : MulAut V) (v' : V') : (MulAut.congr e f) v' = e (f (e.symm v')) := rfl

theorem congr_symm_apply' (x : MulAut V') (v : V) :
    ((MulAut.congr e).symm x) v = e.symm (x (e v)) := rfl

theorem mem_mapAut {A : Subgroup (MulAut V)} {x : MulAut V'} :
    x ∈ mapAut e A ↔ (MulAut.congr e).symm x ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (MulAut.congr e).symm ((MulAut.congr e).toMonoidHom y) = y :=
      MulEquiv.symm_apply_apply _ y
    rw [this]
    exact hy
  · intro hx
    exact ⟨_, hx, MulEquiv.apply_symm_apply _ x⟩

theorem fixV_mapAut (A : Subgroup (MulAut V)) :
    fixV (mapAut e A) = (fixV A).map e.toMonoidHom := by
  ext v'
  constructor
  · intro hv
    refine ⟨e.symm v', ?_, e.apply_symm_apply v'⟩
    intro x hx
    have h1 := hv ((MulAut.congr e) x) ((mem_mapAut e).mpr (by
      rw [MulEquiv.symm_apply_apply]; exact hx))
    rw [congr_apply'] at h1
    apply e.injective
    simpa using h1
  · rintro ⟨v, hv, rfl⟩ x hx
    have hx' := (mem_mapAut e).mp hx
    have h2 : ((MulAut.congr e).symm x) v = v := hv _ hx'
    rw [congr_symm_apply'] at h2
    have h3 := congrArg e h2
    simp only [MulEquiv.apply_symm_apply] at h3
    exact h3

theorem rkIdx_fixV_mapAut (A : Subgroup (MulAut V)) :
    rkIdx (fixV (mapAut e A)) = rkIdx (fixV A) := by
  rw [fixV_mapAut]
  unfold rkIdx
  exact congrArg (padicValNat 2) (Subgroup.index_map_equiv (fixV A) e)

theorem rk_mapAut (A : Subgroup (MulAut V)) : rk (mapAut e A) = rk A := by
  unfold rk mapAut
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]

theorem isElemAbelian2_mapAut {A : Subgroup (MulAut V)} (hel : IsElemAbelian2 A) :
    IsElemAbelian2 (mapAut e A) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [mem_mapAut] at hx hy
    have := hel.1 _ hx _ hy
    apply (MulAut.congr e).symm.injective
    rw [map_mul, map_mul]
    exact this
  · rw [mem_mapAut] at hx
    have := hel.2 _ hx
    apply (MulAut.congr e).symm.injective
    rw [map_pow, map_one]
    exact this

theorem mapAut_ne_bot {A : Subgroup (MulAut V)} (hA : A ≠ ⊥) : mapAut e A ≠ ⊥ := by
  intro h0
  apply hA
  rw [Subgroup.eq_bot_iff_forall] at h0 ⊢
  intro x hx
  have := h0 ((MulAut.congr e) x) ((mem_mapAut e).mpr (by rwa [MulEquiv.symm_apply_apply]))
  exact (MulAut.congr e).injective (by rw [map_one]; exact this)

theorem mapAut_mono {A B : Subgroup (MulAut V)} (h : A ≤ B) : mapAut e A ≤ mapAut e B :=
  Subgroup.map_mono h

theorem mapAut_zpowers (t : MulAut V) :
    mapAut e (Subgroup.zpowers t) = Subgroup.zpowers ((MulAut.congr e) t) := by
  unfold mapAut
  rw [MonoidHom.map_zpowers]
  rfl

theorem H11Concl_of_equiv [Finite V] [Finite V'] {a : ℕ} {L A : Subgroup (MulAut V)}
    (h : H11Concl a (mapAut e L) (mapAut e A)) : H11Concl a L A := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [rk_mapAut, rkIdx_fixV_mapAut] at h1 h2 h3
  refine ⟨h1, ?_, fun hAL => h3 (mapAut_mono e hAL)⟩
  rcases h2 with h2 | ⟨ha, t', ht', hrk⟩
  · exact Or.inl h2
  · refine Or.inr ⟨ha, (MulAut.congr e).symm t', (mem_mapAut e).mp ht', ?_⟩
    rw [← hrk, ← rkIdx_fixV_mapAut e, mapAut_zpowers, MulEquiv.apply_symm_apply]

end CFSG.Quasithin.H11
