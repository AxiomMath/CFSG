module

public import CFSG.Quasithin.EmptyFaithful.SzN15Vocab
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.SzN15

variable {V : Type} [CommGroup V]

section Nat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {X : Subgroup (MulAut V)} {U Z : Subgroup V} {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
  {π : ↥Γ →* ↥X}

theorem natAct_one' (x : Multiplicative (ι → K)) : natAct Γ 1 x = x := by
  simp [natAct]

theorem natAct_mul' (g h : ↥Γ) (x : Multiplicative (ι → K)) :
    natAct Γ (g * h) x = natAct Γ g (natAct Γ h x) := by
  simp [natAct, Matrix.mulVec_mulVec]

theorem natAct_inv' (g : ↥Γ) (x : Multiplicative (ι → K)) : natAct Γ g⁻¹ (natAct Γ g x) = x := by
  rw [← natAct_mul', inv_mul_cancel, natAct_one']

theorem natAct_mul_elt (g : ↥Γ) (x y : Multiplicative (ι → K)) :
    natAct Γ g (x * y) = natAct Γ g x * natAct Γ g y := by
  simp [natAct, Matrix.mulVec_add]

theorem natAct_inv_elt (g : ↥Γ) (x : Multiplicative (ι → K)) :
    natAct Γ g x⁻¹ = (natAct Γ g x)⁻¹ := by
  simp [natAct, Matrix.mulVec_neg]

@[expose] def fixM (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (T : Subgroup ↥Γ) :
    Set (Multiplicative (ι → K)) :=
  {m | ∀ t ∈ T, natAct Γ t m = m}

@[expose] def Qt (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (T : Subgroup ↥Γ) : Subgroup ↥Γ where
  carrier := {γ | ∀ m, m ∈ fixM Γ T ↔ natAct Γ γ m ∈ fixM Γ T}
  one_mem' := fun m => by simp [natAct_one']
  mul_mem' := fun {x y} hx hy m => by
    rw [hy m, hx (natAct Γ y m), natAct_mul']
  inv_mem' := fun {x} hx m => by
    rw [hx (natAct Γ x⁻¹ m), ← natAct_mul', mul_inv_cancel, natAct_one']

theorem mem_Qt {T : Subgroup ↥Γ} {γ : ↥Γ} :
    γ ∈ Qt Γ T ↔ ∀ m, m ∈ fixM Γ T ↔ natAct Γ γ m ∈ fixM Γ T := Iff.rfl

structure NatReal (X : Subgroup (MulAut V)) (U Z : Subgroup V)
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (π : ↥Γ →* ↥X) : Prop where
  surj : Function.Surjective π
  U_inv : ∀ x : ↥X, ∀ u ∈ U, (x : MulAut V) u ∈ U
  Z_inv : ∀ x : ↥X, ∀ z ∈ Z, (x : MulAut V) z ∈ Z
  exists_β : ∃ β : ↥U →* Multiplicative (ι → K), Function.Surjective β ∧
    (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
    ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥X) : MulAut V) u ∈ U),
      β ⟨((π γ : ↥X) : MulAut V) u, hu⟩ = natAct Γ γ (β u)

theorem NatReal.of_realizesVia (h : (FFModel.nat Γ).RealizesVia X U Z π) :
    NatReal X U Z Γ π := by
  obtain ⟨hsurj, -, -, hUinv, hZinv, -, -, β, hβs, hβk, hβe⟩ := h
  refine ⟨hsurj, fun x u hu => hUinv x u hu, fun x z hz => hZinv x z hz, ?_⟩
  let q : ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec →*
      Multiplicative (ι → K) :=
    QuotientGroup.lift _ ((FFModel.nat Γ).sec.subtype) (by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have h0 : (x.1 : (FFModel.nat Γ).Amb) ∈ (⊥ : Subgroup (Multiplicative (ι → K))) := hx
      exact Subgroup.mem_bot.1 h0)
  have hq : ∀ m : ↥(FFModel.nat Γ).sec, q (QuotientGroup.mk m) = m.1 := fun m => rfl
  have hqinj : ∀ c, q c = 1 → c = 1 := by
    intro c hc
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective c
    rw [hq] at hc
    have : m = 1 := Subtype.ext hc
    rw [this]; rfl
  have hqsurj : Function.Surjective q := by
    intro x
    exact ⟨QuotientGroup.mk ⟨x, Subgroup.mem_top x⟩, rfl⟩
  refine ⟨q.comp β, hqsurj.comp hβs, fun u => ?_, fun γ u hu => ?_⟩
  · rw [MonoidHom.comp_apply, ← hβk u]
    exact ⟨hqinj _, fun h => by rw [h, map_one]⟩
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hm' : (FFModel.nat Γ).act γ m.1 ∈ (FFModel.nat Γ).sec :=
      Subgroup.mem_top _
    have h1 := hβe γ u m hu hm' hm.symm
    have h2 := congrArg q h1
    have h3 : q (β u) = m.1 := by rw [← hm, hq]
    exact h2.trans (by rw [hq]; exact (congrArg (natAct Γ γ) h3).symm)


theorem NatReal.setStab_iff (R : NatReal X U Z Γ π) {S : Subgroup (MulAut V)} {T : Subgroup ↥Γ}
    (hT : ∀ s : MulAut V, s ∈ S ↔ ∃ t ∈ T, ((π t : ↥X) : MulAut V) = s) (γ : ↥Γ) :
    ((π γ : ↥X) : MulAut V) ∈ setStab (fixMod S U Z) ↔ γ ∈ Qt Γ T := by
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  have h3 : ∀ (t : ↥Γ) (u : ↥U) (hsu : ((π t : ↥X) : MulAut V) u ∈ U)
      (hm : ((π t : ↥X) : MulAut V) u * (u : V)⁻¹ ∈ U),
      β ⟨((π t : ↥X) : MulAut V) u * (u : V)⁻¹, hm⟩ = natAct Γ t (β u) * (β u)⁻¹ := by
    intro t u hsu hm
    have : (⟨((π t : ↥X) : MulAut V) u * (u : V)⁻¹, hm⟩ : ↥U) =
        ⟨((π t : ↥X) : MulAut V) u, hsu⟩ * u⁻¹ := rfl
    rw [this, map_mul, map_inv, hβe t u hsu]
  have key : ∀ u : ↥U, (u : V) ∈ fixMod S U Z ↔ β u ∈ fixM Γ T := by
    intro u
    constructor
    · rintro ⟨-, hu⟩ t ht
      have hs : ((π t : ↥X) : MulAut V) ∈ S := (hT _).2 ⟨t, ht, rfl⟩
      have h1 := hu _ hs
      have hsu : ((π t : ↥X) : MulAut V) u ∈ U := R.U_inv _ u u.2
      have hm : ((π t : ↥X) : MulAut V) u * (u : V)⁻¹ ∈ U := U.mul_mem hsu (U.inv_mem u.2)
      have h2 : β ⟨((π t : ↥X) : MulAut V) u * (u : V)⁻¹, hm⟩ = 1 := (hβk _).2 h1
      rw [h3 t u hsu hm] at h2
      exact mul_inv_eq_one.1 h2
    · intro hu
      refine ⟨u.2, fun s hs => ?_⟩
      obtain ⟨t, ht, rfl⟩ := (hT s).1 hs
      have hsu : ((π t : ↥X) : MulAut V) u ∈ U := R.U_inv _ u u.2
      have hm : ((π t : ↥X) : MulAut V) u * (u : V)⁻¹ ∈ U := U.mul_mem hsu (U.inv_mem u.2)
      have h4 := hu t ht
      have : β ⟨((π t : ↥X) : MulAut V) u * (u : V)⁻¹, hm⟩ = 1 := by
        rw [h3 t u hsu hm, h4]; simp
      exact (hβk _).1 this
  rw [mem_Qt, mem_setStab]
  constructor
  · intro h m
    obtain ⟨u, rfl⟩ := hβs m
    have hxu := R.U_inv (π γ) u u.2
    rw [← key u, h (u : V), key ⟨_, hxu⟩, hβe γ u hxu]
  · intro h u
    by_cases huU : u ∈ U
    · have hxu := R.U_inv (π γ) u huU
      rw [key ⟨u, huU⟩, key ⟨_, hxu⟩, hβe γ ⟨u, huU⟩ hxu]
      exact h _
    · have h6 : ¬ (u ∈ fixMod S U Z) := fun hh => huU hh.1
      have h7 : ¬ ((π γ : ↥X) : MulAut V) u ∈ fixMod S U Z := by
        intro hh
        apply huU
        have := R.U_inv (π γ⁻¹) _ hh.1
        simpa [map_inv] using this
      simp [h6, h7]

theorem NatReal.comap_eq (R : NatReal X U Z Γ π) {S : Subgroup (MulAut V)} {T : Subgroup ↥Γ}
    (hT : ∀ s : MulAut V, s ∈ S ↔ ∃ t ∈ T, ((π t : ↥X) : MulAut V) = s) :
    ((setStab (fixMod S U Z)).comap X.subtype).comap π = Qt Γ T := by
  ext γ
  rw [Subgroup.mem_comap, Subgroup.mem_comap]
  exact R.setStab_iff hT γ

end Nat

theorem covBy_top_of_comap {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (Q : Subgroup H) (h : Q.comap f ⋖ ⊤) : Q ⋖ ⊤ := by
  refine ⟨?_, fun T hQT hT => ?_⟩
  · refine lt_top_iff_ne_top.2 fun hQ => ?_
    have := h.1
    rw [hQ, Subgroup.comap_top] at this
    exact lt_irrefl _ this
  · have h1 : Q.comap f < T.comap f := (Subgroup.comap_lt_comap_of_surjective hf).2 hQT
    have h2 : T.comap f < ⊤ := by
      have := (Subgroup.comap_lt_comap_of_surjective hf (f := f) (K := T) (L := ⊤)).2 hT
      rwa [Subgroup.comap_top] at this
    exact h.2 h1 h2


section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}

theorem natAct_inv'' (g : ↥Γ) (x : Multiplicative (ι → K)) : natAct Γ g (natAct Γ g⁻¹ x) = x := by
  rw [← natAct_mul', mul_inv_cancel, natAct_one']

theorem mem_fixM_conj (T : Subgroup ↥Γ) (g : ↥Γ) (m : Multiplicative (ι → K)) :
    m ∈ fixM Γ (T.map (MulAut.conj g).toMonoidHom) ↔ natAct Γ g⁻¹ m ∈ fixM Γ T := by
  constructor
  · intro h t ht
    have h1 := h (g * t * g⁻¹) ⟨t, ht, by simp⟩
    rw [natAct_mul', natAct_mul'] at h1
    have h2 := congrArg (natAct Γ g⁻¹) h1
    rwa [natAct_inv'] at h2
  · intro h s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have h1 := h t ht
    have h2 : natAct Γ (g * t * g⁻¹) m = m := by
      rw [natAct_mul', natAct_mul', h1, natAct_inv'']
    simpa using h2

theorem Qt_conj (T : Subgroup ↥Γ) (g : ↥Γ) :
    Qt Γ (T.map (MulAut.conj g).toMonoidHom) = (Qt Γ T).map (MulAut.conj g).toMonoidHom := by
  ext γ
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  rw [mem_Qt, mem_Qt]
  constructor
  · intro h m'
    have h1 := h (natAct Γ g m')
    rw [mem_fixM_conj, mem_fixM_conj, natAct_inv'] at h1
    rw [h1, natAct_mul', natAct_mul']
  · intro h m
    have h1 := h (natAct Γ g⁻¹ m)
    rw [mem_fixM_conj, mem_fixM_conj]
    rw [h1, natAct_mul', natAct_mul', natAct_inv'']

theorem covBy_top_Qt_conj (T : Subgroup ↥Γ) (g : ↥Γ) (h : Qt Γ T ⋖ ⊤) :
    Qt Γ (T.map (MulAut.conj g).toMonoidHom) ⋖ ⊤ := by
  rw [Qt_conj]
  have key : ∀ x y : Subgroup ↥Γ, x.map (MulAut.conj g).toMonoidHom ⋖ y.map (MulAut.conj g).toMonoidHom
      ↔ x ⋖ y := fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup (MulAut.conj g))
  rw [← Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective, key]
  exact h

end Conj

end CFSG.Quasithin.SzN15
