module

public import CFSG.Quasithin.EmptyFaithful.SzN28X0Form

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace F8Form

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ A : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
  {x : GLV V} (c : F8Form B Γ A I I' x)

include c in
theorem swap : F8Form B Γ A I' I x where
  data :=
    { A_le := c.data.A_le
      A_normal := c.data.A_normal
      A_min := c.data.A_min
      card_A := c.data.card_A
      x_mem := c.data.x_mem
      x_sq := c.data.x_sq
      compl := c.data.compl.symm
      I'_eq := by
        ext w
        rw [Submodule.mem_map]
        constructor
        · intro hw
          exact ⟨x w, (c.data.mem_I'_iff (x w)).2 (by rw [c.data.xx_apply]; exact hw),
            c.data.xx_apply w⟩
        · rintro ⟨j, hj, rfl⟩
          exact (c.data.mem_I'_iff j).1 hj
      rank4 := c.data.rank4'
      A_inv_I := c.data.A_inv_I'
      faithful_I := c.data.faithful_I'
      outer := c.data.outer }
  alt := c.alt
  nondeg := c.nondeg
  isom := c.isom
  iso_I := c.iso_I'

include c in
theorem eq_t_of_cyc {e₀ f₀ : V} (he : e₀ ∈ I) (hf : f₀ ∈ I') (hf0 : f₀ ≠ 0) (hB0 : B e₀ f₀ = 0)
    {t y : GLV V} (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀) (hy : y ∈ A)
    (hcyc : ∀ i ∈ I, ∃ a : ZMod 2, y i = i + a • e₀)
    (hj₀ : ∃ j₀ ∈ I', y j₀ - j₀ = f₀) : y = t := by
  have hyΓ : y ∈ Γ := c.data.A_le hy
  have hyI' : ∀ j ∈ I', y j ∈ I' := c.data.A_inv_I' y hy
  have z4 : ∀ p q r : ZMod 2, p + r = q → p - q = r := by decide
  have key : ∀ i ∈ I, ∀ a : ZMod 2, y i = i + a • e₀ → ∀ j, B i (y j - j) = a * B e₀ (y j) := by
    intro i hi a hya j
    have h1 := c.isom y hyΓ i j
    rw [hya] at h1
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [map_sub]
    exact z4 _ _ _ h1
  obtain ⟨j₀, hj₀I, hj₀⟩ := hj₀
  have hb1 : B e₀ (y j₀) = 1 := by
    by_contra hne
    have key2 : ∀ r : ZMod 2, r ≠ 1 → r = 0 := by decide
    have h0 : B e₀ (y j₀) = 0 := key2 _ hne
    apply hf0
    apply c.pair_I' hf
    intro i hi
    obtain ⟨a, ha⟩ := hcyc i hi
    have := key i hi a ha j₀
    rw [hj₀, h0, mul_zero] at this
    exact this
  have hyi : ∀ i ∈ I, y i = i + B i f₀ • e₀ := by
    intro i hi
    obtain ⟨a, ha⟩ := hcyc i hi
    have := key i hi a ha j₀
    rw [hj₀, hb1, mul_one] at this
    rw [ha, this]
  have hyj : ∀ j ∈ I', y j = j + B e₀ j • f₀ := by
    intro j hj
    obtain ⟨d, hd⟩ : ∃ d, d = y j - j := ⟨_, rfl⟩
    have hdI' : d ∈ I' := by rw [hd]; exact I'.sub_mem (hyI' j hj) hj
    obtain ⟨r, hr⟩ : ∃ r, r = B e₀ (y j) := ⟨_, rfl⟩
    have h1 : d = r • f₀ := by
      have := c.pair_I' (I'.sub_mem hdI' (I'.smul_mem r hf)) (fun i hi => by
        have h2 := key i hi (B i f₀) (hyi i hi) j
        rw [← hd, ← hr] at h2
        rw [map_sub, h2, map_smul, smul_eq_mul, mul_comm, sub_self])
      exact sub_eq_zero.1 this
    have h2 : r = B e₀ j := by
      have e1 : y j = j + d := by rw [hd]; abel
      have e2 : B e₀ (y j) = B e₀ j + B e₀ d := by rw [e1, map_add]
      rw [h1, map_smul, smul_eq_mul, hB0, mul_zero, add_zero] at e2
      rw [hr]
      exact e2
    rw [h2] at h1
    calc y j = j + d := by rw [hd]; abel
      _ = j + B e₀ j • f₀ := by rw [h1]
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ I ⊔ I' := by rw [c.data.compl.sup_eq_top]; trivial
  obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hyi i hi, hyj j hj, ht (i + j)]
  have e1 : B (i + j) f₀ = B i f₀ := by
    rw [map_add, LinearMap.add_apply, c.iso_I' j hj f₀ hf, add_zero]
  have e2 : B (i + j) e₀ = B e₀ j := by
    rw [map_add, LinearMap.add_apply, c.iso_I i hi e₀ he, zero_add, c.symm j e₀]
  rw [e1, e2]
  abel

include c in
theorem finrank_eq_eight [Finite V] : Module.finrank (ZMod 2) V = 8 := by
  have := Submodule.finrank_add_eq_of_isCompl c.data.compl
  rw [c.data.rank4, c.data.rank4'] at this
  omega

include c in
theorem eq_t_of_finrank_ker [Finite V] {e₀ f₀ : V} (he : e₀ ∈ I) (hf : f₀ ∈ I') (he0 : e₀ ≠ 0)
    (hf0 : f₀ ≠ 0) (hB0 : B e₀ f₀ = 0) {t y : GLV V}
    (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀) (hy : y ∈ A) (hv : ∃ v, y v - v = e₀ + f₀)
    (hk : 5 ≤ Module.finrank (ZMod 2)
      (LinearMap.ker ((y : V →ₗ[ZMod 2] V) - LinearMap.id))) : y = t := by
  let T : V →ₗ[ZMod 2] V := (y : V →ₗ[ZMod 2] V) - LinearMap.id
  have hT : ∀ v, T v = y v - v := fun v => by simp [T]
  have hyI : ∀ i ∈ I, y i ∈ I := c.data.A_inv_I y hy
  have hyI' : ∀ j ∈ I', y j ∈ I' := c.data.A_inv_I' y hy
  obtain ⟨v, hv⟩ := hv
  have hvs : v ∈ I ⊔ I' := by rw [c.data.compl.sup_eq_top]; trivial
  obtain ⟨i₀, hi₀, j₀, hj₀, rfl⟩ := Submodule.mem_sup.1 hvs
  have hdec : (y i₀ - i₀) + (y j₀ - j₀) = e₀ + f₀ := by
    rw [← hv, map_add]
    abel
  obtain ⟨h1, h2⟩ := c.data.eq_of_add_eq (I.sub_mem (hyI i₀ hi₀) hi₀) he
    (I'.sub_mem (hyI' j₀ hj₀) hj₀) hf hdec
  let N₁ : Submodule (ZMod 2) V := I.map T
  let N₁' : Submodule (ZMod 2) V := I'.map T
  have hN₁I : N₁ ≤ I := by
    rintro _ ⟨i, hi, rfl⟩
    rw [hT]
    exact I.sub_mem (hyI i hi) hi
  have hN₁I' : N₁' ≤ I' := by
    rintro _ ⟨j, hj, rfl⟩
    rw [hT]
    exact I'.sub_mem (hyI' j hj) hj
  have hdisj : N₁ ⊓ N₁' = ⊥ :=
    le_bot_iff.1 ((inf_le_inf hN₁I hN₁I').trans (le_of_eq c.data.compl.inf_eq_bot))
  have he1 : e₀ ∈ N₁ := ⟨i₀, hi₀, by rw [hT]; exact h1⟩
  have hf1 : f₀ ∈ N₁' := ⟨j₀, hj₀, by rw [hT]; exact h2⟩
  have hV8 := c.finrank_eq_eight
  have hk' : 5 ≤ Module.finrank (ZMod 2) (LinearMap.ker T) := hk
  have hrange : Module.finrank (ZMod 2) (LinearMap.range T) ≤ 3 := by
    have := LinearMap.finrank_range_add_finrank_ker T
    omega
  have hsup : N₁ ⊔ N₁' ≤ LinearMap.range T := by
    refine sup_le ?_ ?_
    · rintro _ ⟨i, -, rfl⟩
      exact LinearMap.mem_range_self T i
    · rintro _ ⟨i, -, rfl⟩
      exact LinearMap.mem_range_self T i
  have hsum : Module.finrank (ZMod 2) N₁ + Module.finrank (ZMod 2) N₁' ≤ 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq N₁ N₁'
    rw [hdisj, finrank_bot] at h
    have := Submodule.finrank_mono hsup
    omega
  have hpos1 : 0 < Module.finrank (ZMod 2) N₁ :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨e₀, he1⟩, fun h => he0 (congrArg Subtype.val h)⟩
  have hpos2 : 0 < Module.finrank (ZMod 2) N₁' :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨f₀, hf1⟩, fun h => hf0 (congrArg Subtype.val h)⟩
  by_cases hc1 : Module.finrank (ZMod 2) N₁ = 1
  · refine c.eq_t_of_cyc he hf hf0 hB0 ht hy ?_ ⟨j₀, hj₀, h2⟩
    intro i hi
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e₀, he1⟩ : N₁)
      (fun h => he0 (congrArg Subtype.val h))).1 hc1 ⟨T i, Submodule.mem_map_of_mem hi⟩
    refine ⟨a, ?_⟩
    have h3 : a • e₀ = T i := congrArg Subtype.val ha
    rw [h3, hT]
    abel
  · have hc2 : Module.finrank (ZMod 2) N₁' = 1 := by omega
    have hB0' : B f₀ e₀ = 0 := by rw [c.symm]; exact hB0
    have ht' : ∀ v, t v = v + B v e₀ • f₀ + B v f₀ • e₀ := fun v => by
      rw [ht v]
      abel
    refine c.swap.eq_t_of_cyc hf he he0 hB0' ht' hy ?_ ⟨i₀, hi₀, h1⟩
    intro j hj
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨f₀, hf1⟩ : N₁')
      (fun h => hf0 (congrArg Subtype.val h))).1 hc2 ⟨T j, Submodule.mem_map_of_mem hj⟩
    refine ⟨a, ?_⟩
    have h3 : a • f₀ = T j := congrArg Subtype.val ha
    rw [h3, hT]
    abel

include c in
theorem finrank_ker_le_four [Finite V] {e₀ f₀ : V} (he : e₀ ∈ I) (hf : f₀ ∈ I') (he0 : e₀ ≠ 0)
    (hf0 : f₀ ≠ 0) (hB0 : B e₀ f₀ = 0) {t y : GLV V}
    (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀) (hyΓ : y ∈ Γ) (hyt : y ≠ t)
    (hv : ∃ v, y v - v = e₀ + f₀) :
    Module.finrank (ZMod 2) (LinearMap.ker ((y : V →ₗ[ZMod 2] V) - LinearMap.id)) ≤ 4 := by
  by_cases hyA : y ∈ A
  · by_contra hk
    exact hyt (c.eq_t_of_finrank_ker he hf he0 hf0 hB0 ht hyA hv (by omega))
  · let K : Submodule (ZMod 2) V := LinearMap.ker ((y : V →ₗ[ZMod 2] V) - LinearMap.id)
    have hdisj : K ⊓ I' = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hvK, hvI'⟩
      have hfix : y v = v := by
        have : y v - v = 0 := by simpa [K] using hvK
        exact sub_eq_zero.1 this
      have h1 : y v ∈ I := c.data.outer_I' hyΓ hyA hvI'
      rw [hfix] at h1
      have h2 : v ∈ I ⊓ I' := ⟨h1, hvI'⟩
      rw [c.data.compl.inf_eq_bot] at h2
      exact h2
    have h := Submodule.finrank_sup_add_finrank_inf_eq K I'
    rw [hdisj, finrank_bot, c.data.rank4'] at h
    have h3 := Submodule.finrank_le (K ⊔ I')
    have hV8 := c.finrank_eq_eight
    show Module.finrank (ZMod 2) K ≤ 4
    omega

end F8Form

end CFSG.Quasithin.SzN28
