module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Defs
import TauCeti.Algebra.Group.Subgroup.Map

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup

variable {P P' : Type*} [Group P] [Group P']

theorem quadY_map (f : P →* P') {G B : Subgroup P} {a : P}
    (hf : ∀ x ∈ G, f x * f a = f a * f x → x * a = a * x) :
    (quadY G B a).map f = quadY (G.map f) (B.map f) (f a) := by
  simp only [quadY, Subgroup.map_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun hxa => ?_
    rw [Subgroup.map_map_conj]
    refine le_iSup_of_le (f x) (le_iSup_of_le (Subgroup.mem_map_of_mem f hx) ?_)
    refine le_iSup_of_le (by simpa [map_mul] using congrArg f hxa) le_rfl
  · refine iSup_le fun y => iSup_le fun hy => iSup_le fun hya => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← Subgroup.map_map_conj]
    exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le (hf x hx hya) le_rfl))

theorem ParrottGen.map {f : P →* P'} (hf : Function.Injective f) {I : Subgroup P} {t u : P}
    (h : ParrottGen I t u) : ParrottGen (I.map f) (f t) (f u) := by
  obtain ⟨τ, hτI, hodd, hconj, hgen⟩ := h
  refine ⟨f τ, Subgroup.mem_map_of_mem f hτI, ?_, ?_, ?_⟩
  · rwa [orderOf_injective f hf]
  · have h : f (t * τ * t⁻¹) = f (τ⁻¹) := by rw [hconj]
    simpa [map_mul, map_inv] using h
  · calc I.map f ≤ (closure ({t, u, τ} : Set P)).map f := Subgroup.map_mono hgen
      _ = closure ({f t, f u, f τ} : Set P') := by
        rw [MonoidHom.map_closure]
        simp [Set.image_insert_eq]

theorem L2CaseII.map {f : P →* P'} (hf : Function.Injective f) {I : Subgroup P} {t β : P}
    (h : L2CaseII I t β) : L2CaseII (I.map f) (f t) (f β) := by
  obtain ⟨hgen, hle⟩ := h
  have ht : ∀ x, f x * f t = f t * f x → x * t = t * x :=
    fun x hx => hf (by simpa [map_mul] using hx)
  have hβ : ∀ x, f x * f β = f β * f x → x * β = β * x :=
    fun x hx => hf (by simpa [map_mul] using hx)
  have hclosure : (closure ({t, β} : Set P)).map f = closure ({f t, f β} : Set P') := by
    rw [MonoidHom.map_closure]
    simp [Set.image_insert_eq]
  have hsup : ((closure ({t, β} : Set P)) ⊔ I).map f =
      closure ({f t, f β} : Set P') ⊔ I.map f := by
    rw [Subgroup.map_sup, hclosure]
  have hq_t := quadY_map (G := closure ({t, β} : Set P) ⊔ I)
    (B := closure ({t, β} : Set P)) (a := t) f (fun x _ hx => ht x hx)
  have hq_β := quadY_map (G := closure ({t, β} : Set P) ⊔ I)
    (B := closure ({t, β} : Set P)) (a := β) f (fun x _ hx => hβ x hx)
  refine ⟨ParrottGen.map hf hgen, ?_⟩
  have hmap := Subgroup.map_mono (f := f) hle
  rw [Subgroup.map_sup, hq_t, hq_β, hsup, hclosure] at hmap
  exact hmap

theorem L2CaseIII.map {f : P →* P'} (hf : Function.Injective f) {I : Subgroup P} {t β : P}
    (h : L2CaseIII I t β) : L2CaseIII (I.map f) (f t) (f β) := by
  obtain ⟨p, U, hp, hp2, hUI, hUne, hUcomm, hUpow, hUnorm, hUcent, hhyp⟩ := h
  have hβ : ∀ x, f x * f β = f β * f x → x * β = β * x :=
    fun x hx => hf (by simpa [map_mul] using hx)
  have hclosure : (closure ({t, β} : Set P)).map f = closure ({f t, f β} : Set P') := by
    rw [MonoidHom.map_closure]
    simp [Set.image_insert_eq]
  have hsup : ((closure ({t, β} : Set P)) ⊔ I).map f =
      closure ({f t, f β} : Set P') ⊔ I.map f := by
    rw [Subgroup.map_sup, hclosure]
  have hq_β := quadY_map (G := closure ({t, β} : Set P) ⊔ I)
    (B := closure ({t, β} : Set P)) (a := β) f (fun x _ hx => hβ x hx)
  refine ⟨p, U.map f, hp, hp2, Subgroup.map_mono hUI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hUne ((Subgroup.map_eq_bot_iff_of_injective U hf).mp hbot)
  · intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
    simpa [map_mul] using congrArg f (hUcomm x0 hx0 y0 hy0)
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hUpow x0 hx0, map_one]
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [map_mul, map_inv] using Subgroup.mem_map_of_mem f (hUnorm x0 hx0)
  · intro z hz
    obtain ⟨hzU, hzC⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨x, hxU, rfl⟩ := Subgroup.mem_map.mp hzU
    have hxC : x * β = β * x := by
      apply hf
      have h := Subgroup.mem_centralizer_singleton_iff.mp hzC
      simpa [map_mul] using h
    have hxY : x ∈ quadY (closure ({t, β} : Set P) ⊔ I)
        (closure ({t, β} : Set P)) β :=
      hUcent (Subgroup.mem_inf.mpr
        ⟨hxU, Subgroup.mem_centralizer_singleton_iff.mpr hxC⟩)
    have hmem : f x ∈ (quadY (closure ({t, β} : Set P) ⊔ I)
        (closure ({t, β} : Set P)) β).map f := Subgroup.mem_map_of_mem f hxY
    rw [hq_β, hsup, hclosure] at hmem
    exact hmem
  · intro K hKU hrel
    let H : Subgroup P := K.comap f ⊓ U
    have hHU : H ≤ U := inf_le_right
    have hHmap : H.map f = K := by
      show (K.comap f ⊓ U).map f = K
      rw [Subgroup.map_inf (K.comap f) U f hf,
        Subgroup.map_comap_eq_self (hKU.trans (Subgroup.map_le_range (f := f) U))]
      exact inf_eq_left.mpr hKU
    have hrelH : H.relIndex U = p := by
      rw [← Subgroup.relIndex_map_map_of_injective H U hf, hHmap]
      exact hrel
    obtain ⟨s, hsI, hsU, hnotcent, hneq⟩ := hhyp H hHU hrelH
    have hKmap : K.map (MulAut.conj (f s)).toMonoidHom =
        (H.map (MulAut.conj s).toMonoidHom).map f := by
      rw [← hHmap, ← Subgroup.map_map_conj]
    refine ⟨f s, Subgroup.mem_map_of_mem f hsI, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
      simpa [map_mul, map_inv] using Subgroup.mem_map_of_mem f (hsU x0 hx0)
    · intro hle
      apply hnotcent
      intro y hy
      obtain ⟨hyU, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyC' : f y ∈ centralizer ({f β} : Set P') := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
        simpa [map_mul] using congrArg f hyC
      have hy' : f y ∈ U.map f ⊓ centralizer ({f β} : Set P') :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem f hyU, hyC'⟩
      have hmem := hle hy'
      rw [hKmap, Subgroup.mem_map_iff_mem hf] at hmem
      exact hmem
    · intro heq
      have heq2 : ((H.map (MulAut.conj s).toMonoidHom).map
          (MulAut.conj β).toMonoidHom).map f =
          (H.map (MulAut.conj s).toMonoidHom).map f := by
        calc ((H.map (MulAut.conj s).toMonoidHom).map
              (MulAut.conj β).toMonoidHom).map f
            = ((H.map (MulAut.conj s).toMonoidHom).map f).map
                (MulAut.conj (f β)).toMonoidHom := Subgroup.map_map_conj _ f β
          _ = (K.map (MulAut.conj (f s)).toMonoidHom).map
                (MulAut.conj (f β)).toMonoidHom := by rw [← hKmap]
          _ = K.map (MulAut.conj (f s)).toMonoidHom := heq
          _ = (H.map (MulAut.conj s).toMonoidHom).map f := hKmap
      exact hneq (Subgroup.map_injective hf heq2)

theorem L2OuterFacts.map {I : Subgroup P} (h : L2OuterFacts I) (e : P ≃* P') :
    L2OuterFacts (I.map e.toMonoidHom) := by
  intro t' β' ht' hβ' ht'sq ht'ne hβ'sq hcomm
  let t := e.symm t'
  let β := e.symm β'
  have ht : e t = t' := by simp [t]
  have hβ : e β = β' := by simp [β]
  have htI : t ∈ I := (Subgroup.mem_map_equiv (f := e) (K := I) (x := t')).mp ht'
  have hβI : β ∉ I := by
    intro hmem
    apply hβ'
    rw [← hβ]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hmem
  have htsq : t * t = 1 := by
    apply e.injective
    rw [map_mul, ht, ht'sq, map_one]
  have htne : t ≠ 1 := by
    intro h1
    exact ht'ne (by rw [← ht, h1, map_one])
  have hβsq : β * β = 1 := by
    apply e.injective
    rw [map_mul, hβ, hβ'sq, map_one]
  have hcommt : t * β = β * t := by
    apply e.injective
    rw [map_mul, map_mul, ht, hβ, hcomm]
  rcases h t β htI hβI htsq htne hβsq hcommt with h2 | h3
  · exact Or.inl (by
      simpa [ht, hβ] using L2CaseII.map (f := e.toMonoidHom) e.injective h2)
  · exact Or.inr (by
      simpa [ht, hβ] using L2CaseIII.map (f := e.toMonoidHom) e.injective h3)

theorem L2InnerFacts.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (h : L2InnerFacts X)
    (e : X ≃* X') : L2InnerFacts X' := by
  refine ⟨?_, ?_⟩
  · intro t' u' ht'sq ht'ne hu'sq hu'ne hcomm' hne'
    let t := e.symm t'
    let u := e.symm u'
    have ht : e t = t' := by simp [t]
    have hu : e u = u' := by simp [u]
    have htsq : t * t = 1 := by
      apply e.injective
      rw [map_mul, ht, ht'sq, map_one]
    have htne : t ≠ 1 := by
      intro h1
      exact ht'ne (by rw [← ht, h1, map_one])
    have husq : u * u = 1 := by
      apply e.injective
      rw [map_mul, hu, hu'sq, map_one]
    have hune : u ≠ 1 := by
      intro h1
      exact hu'ne (by rw [← hu, h1, map_one])
    have hcomm : t * u = u * t := by
      apply e.injective
      rw [map_mul, map_mul, ht, hu, hcomm']
    have hne : t ≠ u := by
      intro h
      exact hne' (by rw [← ht, ← hu, h])
    have hmap := ParrottGen.map (f := e.toMonoidHom) e.injective
      (h.gen t u htsq htne husq hune hcomm hne)
    rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
    simpa [ht, hu] using hmap
  · intro t' u' ht'sq ht'ne hu'sq hu'ne hcomm' hne'
    let t := e.symm t'
    let u := e.symm u'
    have ht : e t = t' := by simp [t]
    have hu : e u = u' := by simp [u]
    have htsq : t * t = 1 := by
      apply e.injective
      rw [map_mul, ht, ht'sq, map_one]
    have htne : t ≠ 1 := by
      intro h1
      exact ht'ne (by rw [← ht, h1, map_one])
    have husq : u * u = 1 := by
      apply e.injective
      rw [map_mul, hu, hu'sq, map_one]
    have hune : u ≠ 1 := by
      intro h1
      exact hu'ne (by rw [← hu, h1, map_one])
    have hcomm : t * u = u * t := by
      apply e.injective
      rw [map_mul, map_mul, ht, hu, hcomm']
    have hne : t ≠ u := by
      intro h
      exact hne' (by rw [← ht, ← hu, h])
    have hcent := h.cent t u htsq htne husq hune hcomm hne
    have hmaptop : (centralizer {t} ⊔ centralizer {u}).map e.toMonoidHom = ⊤ := by
      rw [hcent, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    have hle : (centralizer {t} ⊔ centralizer {u}).map e.toMonoidHom =
        (centralizer {t}).map e.toMonoidHom ⊔ (centralizer {u}).map e.toMonoidHom :=
      Subgroup.map_sup _ _ _
    have ht_le : (centralizer {t}).map e.toMonoidHom ≤ centralizer {t'} := by
      have h := Subgroup.map_centralizer_le_centralizer_image ({t} : Set X) e.toMonoidHom
      simpa [ht] using h
    have hu_le : (centralizer {u}).map e.toMonoidHom ≤ centralizer {u'} := by
      have h := Subgroup.map_centralizer_le_centralizer_image ({u} : Set X) e.toMonoidHom
      simpa [hu] using h
    have htop : (⊤ : Subgroup X') ≤ centralizer {t'} ⊔ centralizer {u'} := by
      rw [← hmaptop, hle]
      exact sup_le_sup ht_le hu_le
    exact top_le_iff.mp htop

theorem L2AutFacts.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (h : L2AutFacts X)
    (e : X ≃* X') : L2AutFacts X' := by
  let E : MulAut X ≃* MulAut X' := MulAut.congr e
  have hE : ∀ x : X, E (MulAut.conj x) = MulAut.conj (e x) := by
    intro x
    ext y
    simp [E, MulAut.congr_apply, MulAut.conj_apply]
  refine ⟨?_, ?_⟩
  · intro W' hW'exp hW'card
    let W : Subgroup (MulAut X) := W'.map E.symm.toMonoidHom
    have hWexp : ∀ w ∈ W, w * w = 1 := by
      intro w hw
      obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
      rw [← map_mul, hW'exp w' hw', map_one]
    have hWcard : Nat.card W = 4 := by
      rw [show W = W'.map E.symm.toMonoidHom from rfl,
        Subgroup.card_map_of_injective E.symm.injective, hW'card]
    obtain ⟨w, hwW, hwne, hwrange⟩ := h.foote W hWexp hWcard
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hwrange
    refine ⟨E w, ?_, ?_, ?_⟩
    · simpa using (Subgroup.mem_map_equiv (f := E.symm) (K := W') (x := w)).mp hwW
    · intro h1
      apply hwne
      simpa using congrArg E.symm h1
    · refine ⟨e x, ?_⟩
      rw [← hE x, hx]
  · have hrange : (MulAut.conj : X →* MulAut X).range.map E.toMonoidHom =
        (MulAut.conj : X' →* MulAut X').range := by
      rw [MonoidHom.map_range]
      have hcomp : E.toMonoidHom.comp (MulAut.conj : X →* MulAut X) =
          (MulAut.conj : X' →* MulAut X').comp e.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        exact hE x
      have htop : e.toMonoidHom.range = ⊤ := by
        simpa using MulEquiv.range_eq_top e
      rw [hcomp, MonoidHom.range_comp, htop, Subgroup.map_top]
    have houter := L2OuterFacts.map h.outer E
    rwa [hrange] at houter

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
