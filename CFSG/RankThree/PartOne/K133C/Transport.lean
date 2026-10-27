module

public import CFSG.RankThree.PartOne.K133.Moving
public import CFSG.RankThree.PartOne.N143X.Weights

public section

namespace CFSG.RankThree.PartOne.K133C

open CFSG CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.N143X

theorem GoodAction.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    {Ē : Subgroup (MulAut X)} {Ē' : Subgroup (MulAut Y)}
    (hĒ : ∀ φ : MulAut X, φ ∈ Ē ↔ MulAut.congr e φ ∈ Ē') (h : GoodAction p Y Ē') :
    GoodAction p X Ē := by
  rcases h with ⟨S, hS1, hS2, hSst⟩ | ⟨P, hPĒ, hPc, S, hS2, hSst, φ, hφP, s, hsS, hφs⟩
  · left
    refine ⟨S.map e.symm.toMonoidHom, ?_, hS2.map _, ?_⟩
    · intro hbot
      apply hS1
      rw [eq_bot_iff]
      intro s hs
      have h1 : e.symm s ∈ Subgroup.map e.symm.toMonoidHom S := Subgroup.mem_map_of_mem _ hs
      rw [hbot, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact (MulEquiv.map_eq_one_iff e.symm).1 h1
    · intro φ hφ s hs
      obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
      refine Subgroup.mem_map.2 ⟨MulAut.congr e φ s', hSst _ ((hĒ φ).1 hφ) s' hs', ?_⟩
      simp [MulAut.congr_apply]
  · right
    refine ⟨P.map (MulAut.congr e).symm.toMonoidHom, ?_, ?_, S.map e.symm.toMonoidHom, hS2.map _, ?_, ?_⟩
    · rintro _ ⟨φ', hφ', rfl⟩
      show (MulAut.congr e).symm φ' ∈ Ē
      rw [hĒ, MulEquiv.apply_symm_apply]
      exact hPĒ hφ'
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hPc]
    · rintro _ ⟨φ', hφ', rfl⟩ _ ⟨s', hs', rfl⟩
      refine ⟨φ' s', hSst φ' hφ' s' hs', ?_⟩
      simp
    · refine ⟨(MulAut.congr e).symm φ, Subgroup.mem_map_of_mem _ hφP, e.symm s,
        Subgroup.mem_map_of_mem _ hsS, ?_⟩
      intro heq
      apply hφs
      have h1 : e.symm (φ s) = e.symm s := by simpa using heq
      exact e.symm.injective h1

theorem Good.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ} (h : Good p Y) :
    Good p X := by
  intro Ē hE hc
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := MulEquiv.injective _
  refine GoodAction.of_mulEquiv e (Ē' := Ē.map (MulAut.congr e).toMonoidHom) (fun φ => ?_) (h _ ?_ ?_)
  · rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  · exact isElementaryAbelian_of_equiv (Ē.equivMapOfInjective _ hinj) hE
  · rw [Subgroup.card_map_of_injective hinj, hc]

@[expose] def autStab {T : Type} [Group T] (S : Subgroup T) : Subgroup (MulAut T) where
  carrier := {φ | ∀ s, φ s ∈ S ↔ s ∈ S}
  one_mem' := fun s => Iff.rfl
  mul_mem' := fun {a b} ha hb s => by
    rw [MulAut.mul_apply, ha, hb]
  inv_mem' := fun {a} ha s => by
    have := ha (a⁻¹ s)
    rw [show a (a⁻¹ s) = s from by simp] at this
    exact this.symm

theorem mem_autStab_of_forward {T : Type} [Group T] (S : Subgroup T) {φ : MulAut T}
    (h1 : ∀ s ∈ S, φ s ∈ S) (h2 : ∀ s ∈ S, φ⁻¹ s ∈ S) : φ ∈ autStab S := fun s =>
  ⟨fun hs => by simpa using h2 _ hs, h1 s⟩

theorem conj_map_aut {T : Type*} [Group T] (φ : MulAut T) (t : T) :
    MulAut.conj (φ t) = φ * MulAut.conj t * φ⁻¹ := by
  ext u
  simp [MulAut.conj_apply, MulAut.mul_apply]

end CFSG.RankThree.PartOne.K133C
